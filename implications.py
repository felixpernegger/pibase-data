#!/usr/bin/env python3
"""Terminal tool for querying and asserting pi-base implications.

Run without arguments for an interactive session, or give a single command:

  ./implications.py                       interactive mode ('help' for commands)
  ./implications.py status "P8 => P32"    one-shot command

Statements are written as "A => B" where A and B are property literals:
`P48`, `P000048`, or negated `~P48`. Your own knowledge is stored in
assertions.json next to this script:

  - asserting a statement TRUE adds it to the deduction engine as an extra
    theorem (so it propagates and can settle further statements);
  - asserting a statement FALSE records a "virtual counterexample" (the
    deductive closure of A and not-B), which can refute further statements.

Commands:
  status  "A => B"              show what pi-base (+ your assertions) knows
  assert  "A => B" true|false   record your knowledge (checked for consistency)
  list                          show saved assertions
  remove  N                     delete assertion #N
  unknown                       regenerate unknown_pairs.csv with assertions
  random                        show a random unknown implication
  find    TEXT                  look up property uids by name
"""

import argparse
import json
import random
import re
import shlex
import sys
from datetime import date
from pathlib import Path

import deduce

ROOT = Path(__file__).resolve().parent
STORE = ROOT / "assertions.json"

LIT_RE = re.compile(r"^\s*([~!]?)\s*P0*(\d+)\s*$")


class CommandError(Exception):
    """User-facing command failure; message is printed, session continues."""


def load_data():
    return (deduce.parse_properties(), deduce.parse_theorems(),
            deduce.parse_spaces())


def load_assertions():
    return json.loads(STORE.read_text(encoding="utf-8")) if STORE.exists() else []


def save_assertions(assertions):
    STORE.write_text(json.dumps(assertions, indent=2, ensure_ascii=False) + "\n",
                     encoding="utf-8")


def parse_statement(text, props):
    parts = re.split(r"=>|->|⇒", text)
    if len(parts) != 2:
        raise CommandError(
            f"cannot parse {text!r}: expected 'A => B' (e.g. '~P48 => P16')")
    lits = []
    for part in parts:
        m = LIT_RE.match(part)
        if not m:
            raise CommandError(
                f"cannot parse literal {part.strip()!r}: use e.g. P48 or ~P000048")
        uid = f"P{int(m.group(2)):06d}"
        if uid not in props:
            raise CommandError(f"unknown property {uid}")
        lits.append((uid, m.group(1) == ""))
    return tuple(lits)


def fmt_lit(props, uid, value):
    return f"{'' if value else '~'}{uid} ({props[uid]})"


def fmt_statement(props, stmt):
    (ua, va), (ub, vb) = stmt
    return f"{fmt_lit(props, ua, va)}  =>  {fmt_lit(props, ub, vb)}"


def assertion_statement(a):
    return ((a["if"]["property"], a["if"]["value"]),
            (a["then"]["property"], a["then"]["value"]))


class Engine:
    """Pi-base theorems and spaces, extended with user assertions."""

    def __init__(self, assertions, data=None):
        self.data = data if data is not None else load_data()
        self.props, theorems, spaces = self.data
        self.assertions = assertions
        self.problems = []

        self.base_prover = deduce.Prover(sorted(self.props), theorems)
        extra = [(f"assertion #{i}", [assertion_statement(a)[0]],
                  assertion_statement(a)[1])
                 for i, a in enumerate(assertions) if a["holds"]]
        self.prover = deduce.Prover(sorted(self.props), theorems + extra)

        self.space_vals = {}
        for sid in sorted(spaces):
            lits = [self.prover.lit(u, v) for u, v in spaces[sid]]
            val, contradiction = self.prover.propagate(lits)
            if contradiction:
                self.problems.append(f"space {sid} becomes contradictory")
            else:
                self.space_vals[sid] = val

        # virtual counterexamples from false assertions: closure of {A, ~B}
        self.virtual_vals = []  # (label, val)
        for i, a in enumerate(assertions):
            if a["holds"]:
                continue
            (ua, va), (ub, vb) = assertion_statement(a)
            lits = [self.prover.lit(ua, va), self.prover.lit(ub, vb) ^ 1]
            val, contradiction = self.prover.propagate(lits)
            if contradiction:
                self.problems.append(
                    f"false-assertion #{i} "
                    f"({fmt_statement(self.props, assertion_statement(a))}) "
                    f"is contradicted: the engine proves the implication")
            else:
                self.virtual_vals.append((f"assertion #{i}", val))

        self._classified = None

    def classify(self):
        """(counts, unknown literal pairs), computed once and cached."""
        if self.problems:
            raise CommandError(
                "fix the reported problems (remove offending assertions) first")
        if self._classified is None:
            assignments = (list(self.space_vals.values())
                           + [v for _, v in self.virtual_vals])
            spaces_with = deduce.literal_bitsets(self.prover, assignments)
            self._classified = deduce.classify_pairs(self.prover, spaces_with)
        return self._classified

    def status(self, stmt):
        """-> (kind, detail): kind in {'provable', 'refuted', 'unknown'}."""
        (ua, va), (ub, vb) = stmt
        a = self.prover.lit(ua, va)
        b = self.prover.lit(ub, vb)

        for sid, val in self.space_vals.items():
            if val[a >> 1] == ((a & 1) == 0) and val[b >> 1] == ((b & 1) != 0):
                return "refuted", f"counterexample {sid}"
        for label, val in self.virtual_vals:
            if val[a >> 1] == ((a & 1) == 0) and val[b >> 1] == ((b & 1) != 0):
                return "refuted", f"your false-{label}"

        _, contradiction = self.prover.propagate([a, b ^ 1])
        if contradiction:
            _, base = self.base_prover.propagate([a, b ^ 1])
            return "provable", ("by pi-base theorems alone" if base
                                else "using your true-assertions")
        return "unknown", (f"no proof, no counterexample among "
                           f"{len(self.space_vals)} spaces"
                           + (f" + {len(self.virtual_vals)} virtual"
                              if self.virtual_vals else ""))


def report_problems(engine, prefix="warning"):
    for p in engine.problems:
        print(f"{prefix}: {p}")


# ---------------------------------------------------------------- commands

def do_status(engine, statement_text):
    stmt = parse_statement(statement_text, engine.props)
    kind, detail = engine.status(stmt)
    print(f"{fmt_statement(engine.props, stmt)}\n  {kind.upper()}: {detail}")


def do_assert(engine, statement_text, verdict, note):
    """Save an assertion. Returns the new assertions list (caller rebuilds)."""
    holds = {"true": True, "false": False}[verdict]
    stmt = parse_statement(statement_text, engine.props)
    (ua, va), (ub, vb) = stmt

    # duplicate / conflict against saved assertions (modulo contrapositive)
    contrapositive = ((ub, not vb), (ua, not va))
    for i, a in enumerate(engine.assertions):
        if assertion_statement(a) in (stmt, contrapositive):
            if a["holds"] == holds:
                raise CommandError(f"already asserted as #{i}, nothing to do")
            raise CommandError(
                f"conflicts with your assertion #{i} "
                f"({fmt_statement(engine.props, assertion_statement(a))} "
                f"is {str(a['holds']).lower()}); remove it first")

    kind, detail = engine.status(stmt)
    print(f"{fmt_statement(engine.props, stmt)}\n"
          f"  current status: {kind.upper()} ({detail})")
    if holds and kind == "provable":
        raise CommandError("already provable, not saving")
    if holds and kind == "refuted":
        raise CommandError(
            "REFUSED: you assert it holds, but it is refuted — resolve first")
    if not holds and kind == "refuted":
        raise CommandError("already refuted, not saving")
    if not holds and kind == "provable":
        raise CommandError(
            "REFUSED: you assert it fails, but the engine proves it — resolve first")

    entry = {"if": {"property": ua, "value": va},
             "then": {"property": ub, "value": vb},
             "holds": holds, "note": note, "date": date.today().isoformat()}
    trial = Engine(engine.assertions + [entry], engine.data)
    new_problems = [p for p in trial.problems if p not in engine.problems]
    if new_problems:
        raise CommandError("\n".join(
            f"REFUSED, this assertion is inconsistent with the data: {p}"
            for p in new_problems))

    assertions = engine.assertions + [entry]
    save_assertions(assertions)
    print(f"saved as assertion #{len(assertions) - 1} "
          f"({'holds' if holds else 'fails'}) in {STORE.name}")
    return assertions


def do_list(engine):
    if not engine.assertions:
        print(f"no assertions saved ({STORE.name} empty or missing)")
        return
    for i, a in enumerate(engine.assertions):
        note = f"  # {a['note']}" if a.get("note") else ""
        print(f"[{i}] {'holds' if a['holds'] else 'fails'}: "
              f"{fmt_statement(engine.props, assertion_statement(a))} "
              f"({a['date']}){note}")


def do_remove(engine, index):
    """Delete assertion #index. Returns the new assertions list."""
    assertions = list(engine.assertions)
    if not 0 <= index < len(assertions):
        raise CommandError(f"no assertion #{index} (have {len(assertions)})")
    a = assertions.pop(index)
    save_assertions(assertions)
    print(f"removed: {'holds' if a['holds'] else 'fails'}: "
          f"{fmt_statement(engine.props, assertion_statement(a))}")
    return assertions


def do_unknown(engine):
    counts, unknown = engine.classify()

    print(f"candidate statements: {counts['total']}")
    print(f"  refuted (spaces + your counterexamples): {counts['refuted']}")
    print(f"  provable (theorems + your assertions)  : {counts['provable']}")
    print(f"  UNKNOWN                                : {counts['unknown']}")
    if engine.assertions:
        _, _, spaces = engine.data
        base_with = deduce.literal_bitsets(
            engine.base_prover,
            list(deduce.close_spaces(engine.base_prover, spaces).values()))
        base_counts, _ = deduce.classify_pairs(engine.base_prover, base_with)
        print(f"  (your {len(engine.assertions)} assertions settle "
              f"{base_counts['unknown'] - counts['unknown']} statements)")

    out = ROOT / "unknown_pairs.csv"
    deduce.write_unknown_csv(out, engine.prover, engine.props, unknown)
    print(f"wrote {counts['unknown']} rows to {out}")


def short_statement(stmt):
    return " => ".join(f"{'' if v else '~'}P{int(u[1:])}" for u, v in stmt)


def do_random(engine, interactive=False):
    """Show a random unknown implication; returns it as a statement tuple."""
    _, unknown = engine.classify()
    if not unknown:
        print("no unknown implications left!")
        return None
    a, b = random.choice(unknown)
    ua, va = engine.prover.unlit(a)
    ub, vb = engine.prover.unlit(b)
    stmt = ((ua, va), (ub, vb))
    hint = ("reply 'true' or 'false' (+ optional note) to save, "
            "or 'random' for another" if interactive
            else f"settle it with: assert {short_statement(stmt)} true|false")
    print(f"{fmt_statement(engine.props, stmt)}\n  UNKNOWN — {hint}")
    return stmt


def do_find(engine, text):
    needle = text.lower()
    hits = [(uid, name) for uid, name in sorted(engine.props.items())
            if needle in name.lower()]
    for uid, name in hits:
        print(f"{uid}  {name}")
    if not hits:
        print(f"no property name contains {text!r}")


# ---------------------------------------------------------------- interactive

REPL_HELP = """\
commands:
  status A => B                what is known about the implication
  assert A => B true|false [note ...]
                               record your knowledge (note may be free text)
  list                         show saved assertions
  remove N                     delete assertion #N
  unknown                      regenerate unknown_pairs.csv
  random                       show a random unknown implication;
                               then just 'true [note ...]' or 'false [note ...]'
                               saves your verdict for it
  find TEXT                    look up property uids by name
  help                         this message
  exit                         quit (also: quit, q, Ctrl-D)

literals: P48, P000048, negated ~P48; arrow: => or ->"""


def note_from(tokens):
    """Note text from trailing tokens: plain text, '--note text', or '--text'."""
    if tokens and tokens[0] == "--note":
        tokens = tokens[1:]
    elif tokens and tokens[0].startswith("--"):
        tokens = [tokens[0][2:]] + tokens[1:]
    return " ".join(t for t in tokens if t)


def repl():
    try:
        import readline  # noqa: F401  (line editing + history for input())
    except ImportError:
        pass

    print("loading pi-base data ...")
    data = load_data()
    engine = Engine(load_assertions(), data)
    report_problems(engine)
    props, theorems, spaces = data
    print(f"pi-base implications tool: {len(props)} properties, "
          f"{len(theorems)} theorems, {len(spaces)} spaces, "
          f"{len(engine.assertions)} saved assertions")
    print("type 'help' for commands, 'exit' to quit")

    pending = None  # statement shown by the last 'random'
    while True:
        try:
            line = input("pibase> ").strip()
        except EOFError:
            print()
            return
        except KeyboardInterrupt:
            print()
            continue
        if not line:
            continue
        try:
            tokens = shlex.split(line)
        except ValueError as e:
            print(f"parse error: {e}")
            continue
        cmd, args = tokens[0].lower(), tokens[1:]

        try:
            if cmd in ("exit", "quit", "q"):
                return
            elif cmd == "help":
                print(REPL_HELP)
            elif cmd == "status":
                do_status(engine, " ".join(args))
            elif cmd == "assert":
                vi = next((i for i, t in enumerate(args)
                           if t.lower() in ("true", "false")), None)
                if vi is None or vi == 0:
                    raise CommandError(
                        "usage: assert A => B true|false [note ...]")
                assertions = do_assert(engine, " ".join(args[:vi]),
                                       args[vi].lower(),
                                       note_from(args[vi + 1:]))
                engine = Engine(assertions, data)
                report_problems(engine)
                do_unknown(engine)
            elif cmd == "list":
                do_list(engine)
            elif cmd == "remove":
                if len(args) != 1 or not args[0].lstrip("-").isdigit():
                    raise CommandError("usage: remove N")
                assertions = do_remove(engine, int(args[0]))
                engine = Engine(assertions, data)
                report_problems(engine)
            elif cmd == "unknown":
                do_unknown(engine)
            elif cmd == "random":
                pending = do_random(engine, interactive=True)
            elif cmd in ("true", "false"):
                if pending is None:
                    raise CommandError(
                        "no pending implication — show one with 'random' first")
                assertions = do_assert(engine, short_statement(pending),
                                       cmd, note_from(args))
                engine = Engine(assertions, data)
                report_problems(engine)
                pending = None
                do_unknown(engine)
            elif cmd == "find":
                if not args:
                    raise CommandError("usage: find TEXT")
                do_find(engine, " ".join(args))
            else:
                print(f"unknown command {cmd!r} — type 'help'")
        except CommandError as e:
            print(e)


# ---------------------------------------------------------------- one-shot CLI

def run_cli(argv):
    p = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="command", required=True)

    s = sub.add_parser("status", help="show what is known about 'A => B'")
    s.add_argument("statement", help="e.g. 'P48 => ~P16'")

    s = sub.add_parser("assert", help="record that 'A => B' is true or false")
    s.add_argument("statement", help="e.g. 'P48 => ~P16'")
    s.add_argument("verdict", choices=["true", "false"])
    s.add_argument("--note", default="", help="reference / justification")

    sub.add_parser("list", help="show saved assertions")

    s = sub.add_parser("remove", help="delete assertion #N")
    s.add_argument("index", type=int)

    sub.add_parser("unknown", help="regenerate unknown_pairs.csv")

    sub.add_parser("random", help="show a random unknown implication")

    s = sub.add_parser("find", help="look up property uids by name")
    s.add_argument("text")

    args = p.parse_args(argv)
    engine = Engine(load_assertions())
    report_problems(engine)
    try:
        if args.command == "status":
            do_status(engine, args.statement)
        elif args.command == "assert":
            assertions = do_assert(engine, args.statement, args.verdict,
                                   args.note)
            do_unknown(Engine(assertions, engine.data))
        elif args.command == "list":
            do_list(engine)
        elif args.command == "remove":
            do_remove(engine, args.index)
        elif args.command == "unknown":
            do_unknown(engine)
        elif args.command == "random":
            do_random(engine)
        elif args.command == "find":
            do_find(engine, args.text)
    except CommandError as e:
        sys.exit(str(e))


def main():
    if len(sys.argv) > 1:
        run_cli(sys.argv[1:])
    else:
        repl()


if __name__ == "__main__":
    main()
