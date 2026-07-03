#!/usr/bin/env python3
"""Local recreation of the pi-base deduction engine (pi-base/web Prover.ts).

Parses this repo's properties/spaces/theorems, closes all space traits under
the theorems (forward application + contrapositives, i.e. unit propagation on
Horn-style clauses over literals), then enumerates every implication statement
between property literals (+/-P => +/-Q) that is neither provable by the
engine (asserting {A, not B} yields a contradiction, matching proveTheorem
semantics) nor refuted by a counterexample space (a space known to satisfy
A and not B). Contrapositive duplicates are collapsed and P000164 is excluded.

Output: unknown_pairs.csv at the repo root + a summary on stdout.
"""

import csv
import sys
from collections import deque
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent
EXCLUDED = {"P000164"}


def frontmatter(path):
    text = path.read_text(encoding="utf-8")
    if not text.startswith("---"):
        raise ValueError(f"no frontmatter in {path}")
    end = text.index("\n---", 3)
    return yaml.safe_load(text[3:end])


# ---------------------------------------------------------------- parsing

def parse_properties():
    props = {}
    for path in sorted((ROOT / "properties").glob("P*.md")):
        fm = frontmatter(path)
        props[fm["uid"]] = fm["name"]
    return props


def parse_atom(node):
    """A single {Pxxxxxx: bool} mapping -> (uid, bool)."""
    if not isinstance(node, dict) or len(node) != 1:
        raise ValueError(f"unexpected atom shape: {node!r}")
    (uid, value), = node.items()
    uid = uid.strip()
    if not isinstance(value, bool):
        raise ValueError(f"non-boolean atom value: {node!r}")
    return uid, value


def parse_formula(node):
    """Antecedent formula -> list of (uid, bool). Only atoms and flat ands exist."""
    if isinstance(node, dict) and "and" in node:
        if len(node) != 1:
            raise ValueError(f"unexpected formula shape: {node!r}")
        return [parse_atom(sub) for sub in node["and"]]
    return [parse_atom(node)]


def parse_theorems():
    theorems = []
    for path in sorted((ROOT / "theorems").glob("T*.md")):
        fm = frontmatter(path)
        theorems.append((fm["uid"], parse_formula(fm["if"]), parse_atom(fm["then"])))
    return theorems


def parse_spaces():
    spaces = {}
    for space_dir in sorted((ROOT / "spaces").glob("S*")):
        traits = []
        for path in sorted((space_dir / "properties").glob("P*.md")):
            fm = frontmatter(path)
            traits.append((fm["property"], bool(fm["value"])))
        spaces[space_dir.name] = traits
    return spaces


# ---------------------------------------------------------------- engine

class Prover:
    """Unit propagation over clauses (l1 & ... & lk => l0), contrapositives included.

    Literal encoding: 2*prop_index for (P, true), 2*prop_index+1 for (P, false).
    Negation is lit ^ 1.
    """

    def __init__(self, prop_ids, theorems):
        self.prop_ids = prop_ids
        self.index = {uid: i for i, uid in enumerate(prop_ids)}
        self.n = len(prop_ids)
        # clause = tuple of literals meaning "at least one holds":
        # (a1 & ... & ak => c) == (~a1 | ... | ~ak | c)
        self.clauses = []
        self.by_prop = [[] for _ in range(self.n)]
        for _, antecedent, consequent in theorems:
            clause = tuple(self.lit(uid, not v) for uid, v in antecedent)
            clause += (self.lit(*consequent),)
            ci = len(self.clauses)
            self.clauses.append(clause)
            for lit in clause:
                self.by_prop[lit >> 1].append(ci)

    def lit(self, uid, value):
        return self.index[uid] * 2 + (0 if value else 1)

    def unlit(self, lit):
        return self.prop_ids[lit >> 1], (lit & 1) == 0

    def propagate(self, literals, val=None, queue=None):
        """Assign the given literals and run to fixpoint.

        val: optional preexisting assignment (list of None/True/False per
        property) already at fixpoint; it is mutated in place.
        Returns (val, contradiction: bool).
        """
        if val is None:
            val = [None] * self.n
        if queue is None:
            queue = deque()

        def assign(lit):
            p, v = lit >> 1, (lit & 1) == 0
            if val[p] is None:
                val[p] = v
                queue.append(p)
                return True
            return val[p] == v

        for lit in literals:
            if not assign(lit):
                return val, True

        while queue:
            p = queue.popleft()
            for ci in self.by_prop[p]:
                unknown = None
                satisfied = False
                for lit in self.clauses[ci]:
                    v = val[lit >> 1]
                    if v is None:
                        if unknown is not None:
                            break  # >=2 unknowns: nothing to do
                        unknown = lit
                    elif v == ((lit & 1) == 0):
                        satisfied = True
                        break
                else:
                    if unknown is None:
                        return val, True  # every literal false
                    if not assign(unknown):
                        return val, True
        return val, False


# ---------------------------------------------------------------- pipeline

def close_spaces(prover, spaces):
    """Deduce the full trait assignment of each space. Raises on contradiction."""
    vals = {}
    for sid in sorted(spaces):
        lits = [prover.lit(u, v) for u, v in spaces[sid]]
        val, contradiction = prover.propagate(lits)
        if contradiction:
            raise ValueError(f"space {sid} closure is contradictory")
        vals[sid] = val
    return vals


def literal_bitsets(prover, assignments):
    """For each literal, a bitmask over `assignments` of where it holds."""
    with_lit = [0] * (2 * prover.n)
    for si, val in enumerate(assignments):
        for p in range(prover.n):
            if val[p] is not None:
                with_lit[2 * p + (0 if val[p] else 1)] |= 1 << si
    return with_lit


def single_literal_closures(prover):
    """closure[lit] = frozenset of implied literals, or None if lit is unsatisfiable."""
    closure = []
    for lit in range(2 * prover.n):
        val, contradiction = prover.propagate([lit])
        closure.append(None if contradiction else frozenset(
            2 * p + (0 if val[p] else 1) for p in range(prover.n)
            if val[p] is not None))
    return closure


def classify_pairs(prover, spaces_with, excluded=EXCLUDED):
    """Classify every canonical literal pair (a => b).

    Returns (counts, unknown) where unknown is a list of (a, b) literal pairs
    that are neither provable ({a, ~b} propagates to a contradiction) nor
    refuted (some assignment in spaces_with satisfies a and ~b).
    """
    closure = single_literal_closures(prover)
    excluded_idx = {prover.index[uid] for uid in excluded if uid in prover.index}
    candidates = [l for l in range(2 * prover.n) if (l >> 1) not in excluded_idx]

    def canonical(a, b):
        # One representative per contrapositive class {(a,b), (~b,~a)},
        # never the both-negated form: ~P => ~Q is reported as Q => P.
        alt = (b ^ 1, a ^ 1)
        if a & 1 and b & 1:
            return alt
        if not (a & 1 or b & 1):
            return (a, b)
        return min((a, b), alt)

    counts = {"total": 0, "refuted": 0, "provable": 0, "unknown": 0}
    unknown = []
    for a in candidates:
        base = closure[a]
        for b in candidates:
            if (a >> 1) == (b >> 1):
                continue
            if (a, b) != canonical(a, b):
                continue
            counts["total"] += 1
            if spaces_with[a] & spaces_with[b ^ 1]:
                counts["refuted"] += 1
                continue
            if base is None or b in base or (closure[b ^ 1] is not None
                                             and (a ^ 1) in closure[b ^ 1]):
                counts["provable"] += 1
                continue
            _, contradiction = prover.propagate([a, b ^ 1])
            if contradiction:
                counts["provable"] += 1
            else:
                counts["unknown"] += 1
                unknown.append((a, b))
    return counts, unknown


def write_unknown_csv(path, prover, props, unknown):
    with path.open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["antecedent_uid", "antecedent_value", "antecedent_name",
                    "consequent_uid", "consequent_value", "consequent_name"])
        for a, b in unknown:
            ua, va = prover.unlit(a)
            ub, vb = prover.unlit(b)
            w.writerow([ua, str(va).lower(), props[ua],
                        ub, str(vb).lower(), props[ub]])


# ---------------------------------------------------------------- main

def main():
    props = parse_properties()
    theorems = parse_theorems()
    spaces = parse_spaces()
    prop_ids = sorted(props)
    prover = Prover(prop_ids, theorems)
    print(f"parsed: {len(props)} properties, {len(theorems)} theorems, "
          f"{len(spaces)} spaces, "
          f"{sum(len(t) for t in spaces.values())} asserted traits")

    # --- self-check: the engine must prove every theorem in the database
    unproved = []
    for uid, antecedent, consequent in theorems:
        lits = [prover.lit(u, v) for u, v in antecedent]
        lits.append(prover.lit(*consequent) ^ 1)
        _, contradiction = prover.propagate(lits)
        if not contradiction:
            unproved.append(uid)
    if unproved:
        print(f"SELF-CHECK FAILED: engine cannot re-prove {unproved}")
        sys.exit(1)
    print("self-check: all theorems re-proved by the engine")

    # --- close every space's traits under the theorems
    try:
        space_val = close_spaces(prover, spaces)
    except ValueError as e:
        print(f"ANOMALY: {e}")
        sys.exit(1)
    deduced = sum(sum(v is not None for v in val) for val in space_val.values())
    print(f"space closures: no contradictions; {deduced} known traits after "
          f"deduction (from {sum(len(t) for t in spaces.values())} asserted)")

    for lit, cl in enumerate(single_literal_closures(prover)):
        if cl is None:
            uid, v = prover.unlit(lit)
            print(f"note: literal {uid}={v} is unsatisfiable by theorems alone "
                  f"(implies everything vacuously)")

    spaces_with = literal_bitsets(prover, list(space_val.values()))
    counts, unknown = classify_pairs(prover, spaces_with)

    print(f"\ncandidate statements (canonical, distinct properties, "
          f"P000164 excluded): {counts['total']}")
    print(f"  refuted by a counterexample space : {counts['refuted']}")
    print(f"  provable by the deduction engine  : {counts['provable']}")
    print(f"  UNKNOWN                           : {counts['unknown']}")

    out = ROOT / "unknown_pairs.csv"
    write_unknown_csv(out, prover, props, unknown)
    print(f"wrote {counts['unknown']} rows to {out}")


if __name__ == "__main__":
    main()
