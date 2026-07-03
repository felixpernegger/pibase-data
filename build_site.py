#!/usr/bin/env python3
"""Build the static website (for GitHub Pages) into _site/.

Runs the deduction engine over the repo data + assertions.json and emits:
  _site/index.html   (from site_template.html, repo name substituted)
  _site/data.json    (stats, accepted assertions, full open list)

The static site lets visitors browse the open list and submit true/false
verdicts as pre-filled GitHub issues; accepted ones land in assertions.json
via the assertion workflows and the site rebuilds automatically.
"""

import json
import os
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path

import implications

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "_site"


def repo_slug():
    slug = os.environ.get("GITHUB_REPOSITORY")
    if slug:
        return slug
    url = subprocess.run(["git", "remote", "get-url", "origin"], cwd=ROOT,
                         capture_output=True, text=True).stdout.strip()
    m = re.search(r"github\.com[:/]+([^/]+/[^/.]+)", url)
    if not m:
        raise SystemExit("cannot determine GitHub repo (set GITHUB_REPOSITORY)")
    return m.group(1)


def main():
    slug = repo_slug()
    print(f"building site for {slug} ...")
    engine = implications.Engine(implications.load_assertions())
    if engine.problems:
        for p in engine.problems:
            print(f"ERROR: {p}")
        raise SystemExit("data is inconsistent; refusing to build")

    counts, unknown = engine.classify()

    def lit(uid, value):
        return {"uid": uid, "value": value, "name": engine.props[uid]}

    pairs = []
    for a, b in unknown:
        ua, va = engine.prover.unlit(a)
        ub, vb = engine.prover.unlit(b)
        pairs.append({"if": lit(ua, va), "then": lit(ub, vb)})

    assertions = [
        {"if": lit(x["if"]["property"], x["if"]["value"]),
         "then": lit(x["then"]["property"], x["then"]["value"]),
         "holds": x["holds"], "note": x.get("note", ""), "date": x["date"]}
        for x in engine.assertions]

    # everything the in-browser engine needs to apply assertions locally:
    # clauses over literals (2*i for prop_ids[i]=true, 2*i+1 for false) and the
    # deduced trait assignment of every space (+ virtual counterexamples from
    # accepted false assertions) as '1'/'0'/'?' strings aligned with prop_ids.
    def model(val):
        return "".join("?" if v is None else ("1" if v else "0") for v in val)

    data = {
        "repo": slug,
        "generated": datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC"),
        "counts": counts,
        "spaces": len(engine.space_vals),
        "assertions": assertions,
        "pairs": pairs,
        "prop_ids": engine.prover.prop_ids,
        "clauses": [list(c) for c in engine.prover.clauses],
        "models": [model(v) for v in engine.space_vals.values()]
                  + [model(v) for _, v in engine.virtual_vals],
    }

    OUT.mkdir(exist_ok=True)
    (OUT / "data.json").write_text(json.dumps(data), encoding="utf-8")
    html = (ROOT / "site_template.html").read_text(encoding="utf-8")
    html = html.replace("__REPO__", slug)
    (OUT / "index.html").write_text(html, encoding="utf-8")
    (OUT / "engine.js").write_text((ROOT / "site_engine.js").read_text(encoding="utf-8"),
                                   encoding="utf-8")
    print(f"wrote _site/index.html and _site/data.json "
          f"({counts['unknown']} open, {len(assertions)} accepted assertions)")


if __name__ == "__main__":
    main()
