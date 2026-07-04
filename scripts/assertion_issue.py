#!/usr/bin/env python3
"""Validate or apply assertions submitted as a GitHub issue.

Usage (issue body passed via the ISSUE_BODY env var, safe for untrusted text):

  python scripts/assertion_issue.py validate   # dry-run all guard checks
  python scripts/assertion_issue.py apply      # save to assertions.json

`apply` additionally reads ISSUE_NUMBER and ISSUE_AUTHOR to record provenance
in the saved notes. Prints a markdown comment for the issue on stdout.
Exit code: validate -> 0 iff every assertion passes; apply -> 0 iff at least
one assertion was applied.

Two supported body formats:

1. The issue form (.github/ISSUE_TEMPLATE/assertion.yml), single assertion:

     ### Statement
     P8 => ~P32
     ### Verdict
     true
     ### Note
     reference / justification

2. The website's batch format, any number of assertions:

     statement: P8 => ~P32
     verdict: true
     note: reference / justification

     statement: ~P1 => P21
     verdict: false
     note: ...

Assertions in a batch are checked sequentially, each against the data plus
the earlier ones in the same issue.
"""

import io
import os
import re
import sys
from contextlib import redirect_stdout
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import implications
from implications import CommandError


def parse_form(body):
    """The rendered issue-form format -> one (statement, verdict, note)."""
    fields = {}
    current = None
    for line in body.splitlines():
        m = re.match(r"###\s+(.+)", line)
        if m:
            current = m.group(1).strip().lower()
            fields[current] = []
        elif current is not None:
            fields[current].append(line)

    def get(key):
        text = "\n".join(fields.get(key, [])).strip()
        return "" if text == "_No response_" else text

    return [(get("statement"), get("verdict").strip().lower(), get("note"))]


def parse_batch(body):
    """statement:/verdict:/note: line groups -> list of (statement, verdict, note)."""
    items, cur = [], {}
    for line in body.splitlines():
        m = re.match(r"\s*(statement|verdict|note)\s*:\s*(.*)", line, re.I)
        if not m:
            continue
        key, value = m.group(1).lower(), m.group(2).strip()
        if key == "statement" and cur.get("statement"):
            items.append(cur)
            cur = {}
        cur[key] = value
    if cur.get("statement"):
        items.append(cur)
    return [(c.get("statement", ""), c.get("verdict", "").lower(),
             c.get("note", "")) for c in items]


def pretty(statement, props):
    """Statement with property names linked to pi-base, falling back to raw."""
    try:
        (ua, va), (ub, vb) = implications.parse_statement(statement, props)
    except CommandError:
        return f"`{statement or '?'}`"

    def lit(uid, value):
        return (("" if value else "¬")
                + f"[{props[uid]}](https://topology.pi-base.org/properties/{uid})")

    return f"{lit(ua, va)} ⇒ {lit(ub, vb)} (`{statement}`)"


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else ""
    if mode not in ("validate", "apply"):
        sys.exit("usage: assertion_issue.py validate|apply")
    body = os.environ.get("ISSUE_BODY", "")

    if re.search(r"^###\s+Statement", body, re.M):
        items = parse_form(body)
    else:
        items = parse_batch(body)
    if not items:
        print("❌ Could not find any assertion in this issue. Use the "
              "assertion form or the website's Submit button.")
        sys.exit(1)

    data = implications.load_data()
    assertions = implications.load_assertions()
    engine = implications.Engine(assertions, data)
    if engine.problems:
        print("❌ The repository data is currently inconsistent; "
              "cannot process assertions:\n```\n"
              + "\n".join(engine.problems) + "\n```")
        sys.exit(1)

    results, ok = [], 0
    for statement, verdict, note in items:
        label = f"{pretty(statement, engine.props)} is `{verdict or '?'}`"
        if verdict not in ("true", "false"):
            results.append(f"❌ {label} — missing or invalid verdict")
            continue
        if mode == "apply":
            issue = os.environ.get("ISSUE_NUMBER", "?")
            author = os.environ.get("ISSUE_AUTHOR", "?")
            note = f"{note} (#{issue}, by @{author})"
        try:
            with redirect_stdout(io.StringIO()):
                assertions = implications.do_assert(
                    engine, statement, verdict, note, save=(mode == "apply"))
            engine = implications.Engine(assertions, data)
            ok += 1
            results.append(f"✅ {label} — passes all consistency checks"
                           + (" (applied)" if mode == "apply" else ""))
        except CommandError as e:
            results.append(f"❌ {label} — {e}")

    plural = "assertion" if len(items) == 1 else f"{len(items)} assertions"
    if mode == "validate":
        print(f"Checked {plural} against the current data "
              f"(theorems, spaces, and accepted assertions):\n")
        print("\n".join(f"- {r}" for r in results))
        if ok == len(items):
            print("\nA maintainer can accept by adding the `approved` label.")
        else:
            print(f"\n{len(items) - ok} of {len(items)} rejected — please "
                  f"edit the issue to fix or remove the rejected ones.")
        sys.exit(0 if ok == len(items) else 1)
    else:
        print(f"Processed {plural}:\n")
        print("\n".join(f"- {r}" for r in results))
        if ok:
            print(f"\nSaved {ok} assertion{'s' if ok != 1 else ''} to "
                  f"`assertions.json` — the website will update in a couple "
                  f"of minutes.")
        sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
