#!/usr/bin/env python3
"""Validate or apply an assertion submitted as a GitHub issue.

Usage (issue body passed via the ISSUE_BODY env var, safe for untrusted text):

  python scripts/assertion_issue.py validate   # dry-run all guard checks
  python scripts/assertion_issue.py apply      # save to assertions.json

`apply` additionally reads ISSUE_NUMBER and ISSUE_AUTHOR to record provenance
in the saved note. Prints a markdown comment for the issue on stdout; exits
non-zero if the assertion is rejected.

The expected body is the rendered issue form (.github/ISSUE_TEMPLATE/assertion.yml):

  ### Statement
  P8 => ~P32
  ### Verdict
  true
  ### Note
  reference / justification
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


def parse_issue(body):
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

    return get("statement"), get("verdict").strip().lower(), get("note")


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else ""
    if mode not in ("validate", "apply"):
        sys.exit("usage: assertion_issue.py validate|apply")
    body = os.environ.get("ISSUE_BODY", "")

    statement, verdict, note = parse_issue(body)
    if verdict not in ("true", "false"):
        print(f"❌ Could not read a `true`/`false` verdict from this issue "
              f"(got {verdict!r}). Please use the assertion form.")
        sys.exit(1)
    if mode == "apply":
        issue = os.environ.get("ISSUE_NUMBER", "?")
        author = os.environ.get("ISSUE_AUTHOR", "?")
        note = f"{note} (#{issue}, by @{author})"

    engine = implications.Engine(implications.load_assertions())
    if engine.problems:
        print("❌ The repository data is currently inconsistent; "
              "cannot process assertions:\n```\n"
              + "\n".join(engine.problems) + "\n```")
        sys.exit(1)

    log = io.StringIO()
    try:
        with redirect_stdout(log):
            implications.do_assert(engine, statement, verdict, note,
                                   save=(mode == "apply"))
    except CommandError as e:
        print(f"❌ **Rejected**: {e}\n\n```\n{log.getvalue()}```")
        sys.exit(1)

    if mode == "validate":
        print(f"✅ **`{statement}` is `{verdict}`** passes all consistency "
              f"checks against the current data.\n\n```\n{log.getvalue()}```\n"
              f"A maintainer can accept it by adding the `approved` label.")
    else:
        print(f"✅ Accepted **`{statement}` is `{verdict}`** — saved to "
              f"`assertions.json`.\n\n```\n{log.getvalue()}```\n"
              f"The website will update in a couple of minutes.")


if __name__ == "__main__":
    main()
