// In-browser port of the pi-base deduction engine (mirrors deduce.py).
// Literals: 2*i for prop_ids[i]=true, 2*i+1 for prop_ids[i]=false; negation is lit^1.
// Models are strings over '1'/'0'/'?' aligned with prop_ids.
const PiEngine = (() => {
  function makeIndex(clauses, np) {
    const byProp = Array.from({ length: np }, () => []);
    clauses.forEach((clause, ci) => {
      const seen = new Set();
      for (const lit of clause) {
        const p = lit >> 1;
        if (!seen.has(p)) { seen.add(p); byProp[p].push(ci); }
      }
    });
    return byProp;
  }

  // Unit propagation to fixpoint. Returns {val, contradiction}.
  function propagate(clauses, byProp, np, literals) {
    const val = new Array(np).fill(null);
    const queue = [];
    function assign(lit) {
      const p = lit >> 1, v = (lit & 1) === 0;
      if (val[p] === null) { val[p] = v; queue.push(p); return true; }
      return val[p] === v;
    }
    for (const lit of literals) {
      if (!assign(lit)) return { val, contradiction: true };
    }
    while (queue.length) {
      const p = queue.shift();
      for (const ci of byProp[p]) {
        const clause = clauses[ci];
        let unknown = null, satisfied = false, twoUnknown = false;
        for (const lit of clause) {
          const v = val[lit >> 1];
          if (v === null) {
            if (unknown !== null) { twoUnknown = true; break; }
            unknown = lit;
          } else if (v === ((lit & 1) === 0)) {
            satisfied = true;
            break;
          }
        }
        if (satisfied || twoUnknown) continue;
        if (unknown === null) return { val, contradiction: true };
        if (!assign(unknown)) return { val, contradiction: true };
      }
    }
    return { val, contradiction: false };
  }

  // Like propagate, but tracks which clause forced each assignment so a
  // contradiction can be explained. Returns {val, contradiction, used} where
  // used is the list of clause indices involved in the contradiction.
  function propagateProof(clauses, byProp, np, literals) {
    const val = new Array(np).fill(null);
    const reason = new Array(np).fill(-1); // forcing clause index; -1 = given
    const queue = [];
    let conflict = null; // {clause: index|-1, prop: index|-1}

    function assign(lit, ci) {
      const p = lit >> 1, v = (lit & 1) === 0;
      if (val[p] === null) { val[p] = v; reason[p] = ci; queue.push(p); return true; }
      if (val[p] === v) return true;
      conflict = { clause: ci, prop: p };
      return false;
    }

    function result(contradiction) {
      const used = new Set();
      if (contradiction && conflict) {
        const stack = [];
        if (conflict.clause >= 0) {
          used.add(conflict.clause);
          for (const lit of clauses[conflict.clause]) stack.push(lit >> 1);
        }
        if (conflict.prop >= 0) stack.push(conflict.prop);
        const seen = new Set();
        while (stack.length) {
          const p = stack.pop();
          if (seen.has(p)) continue;
          seen.add(p);
          const r = reason[p];
          if (r >= 0) {
            used.add(r);
            for (const lit of clauses[r]) stack.push(lit >> 1);
          }
        }
      }
      return { val, contradiction, used: [...used] };
    }

    for (const lit of literals) {
      if (!assign(lit, -1)) return result(true);
    }
    while (queue.length) {
      const p = queue.shift();
      for (const ci of byProp[p]) {
        const clause = clauses[ci];
        let unknown = null, satisfied = false, twoUnknown = false;
        for (const lit of clause) {
          const v = val[lit >> 1];
          if (v === null) {
            if (unknown !== null) { twoUnknown = true; break; }
            unknown = lit;
          } else if (v === ((lit & 1) === 0)) {
            satisfied = true;
            break;
          }
        }
        if (satisfied || twoUnknown) continue;
        if (unknown === null) { conflict = { clause: ci, prop: -1 }; return result(true); }
        if (!assign(unknown, ci)) return result(true);
      }
    }
    return result(false);
  }

  // Does the literal hold in the model string?
  function holdsIn(model, lit) {
    return model.charCodeAt(lit >> 1) === ((lit & 1) === 0 ? 49 /*'1'*/ : 48 /*'0'*/);
  }

  // Is there a model where all the literals hold? (counterexample check:
  // pass the hypotheses plus the negated conclusion)
  function hasModel(models, lits) {
    for (const m of models) {
      let all = true;
      for (const lit of lits) {
        if (!holdsIn(m, lit)) { all = false; break; }
      }
      if (all) return true;
    }
    return false;
  }

  function valToModel(val) {
    let s = '';
    for (const v of val) s += v === null ? '?' : (v ? '1' : '0');
    return s;
  }

  function modelToLits(model) {
    const lits = [];
    for (let p = 0; p < model.length; p++) {
      const c = model.charCodeAt(p);
      if (c === 49) lits.push(2 * p);          // '1' -> prop true
      else if (c === 48) lits.push(2 * p + 1); // '0' -> prop false
    }
    return lits;
  }

  // Re-close every model under an extended clause set (sound: unit-propagation
  // closure is a unique fixpoint, so closing an already-closed model under more
  // clauses equals closing its original traits under them). Returns null if
  // some model becomes contradictory.
  function recloseModels(models, clauses, byProp, np) {
    const out = [];
    for (const m of models) {
      const pr = propagate(clauses, byProp, np, modelToLits(m));
      if (pr.contradiction) return null;
      out.push(valToModel(pr.val));
    }
    return out;
  }

  // Canonical statement of a clause (array of literals): the displayed form
  // with the fewest negations — conclusion = smallest positive literal if the
  // clause has one, else smallest literal; hypotheses = the rest, negated.
  function canonicalStatement(clause) {
    const pos = clause.filter(l => !(l & 1));
    const concl = pos.length ? Math.min(...pos) : Math.min(...clause);
    const hyps = clause.filter(l => l !== concl).map(l => l ^ 1).sort((a, b) => a - b);
    return { hyps, concl };
  }

  // Rejection-sample a random open two-hypothesis statement A ∧ B ⇒ C:
  // canonical form, not refuted by a model, not provable, hypotheses
  // independent (neither A⇒B nor B⇒A provable), properties from propsOk.
  function drawOpenTriple(clauses, byProp, np, models, propsOk, maxTries) {
    for (let t = 0; t < (maxTries || 2000); t++) {
      const picked = [];
      while (picked.length < 3) {
        const p = propsOk[Math.floor(Math.random() * propsOk.length)];
        if (!picked.includes(p)) picked.push(p);
      }
      const clause = picked.map(p => 2 * p + (Math.random() < 0.5 ? 1 : 0));
      const { hyps, concl } = canonicalStatement(clause);
      const seed = hyps.concat([concl ^ 1]);
      if (hasModel(models, seed)) continue;                       // refuted
      if (propagate(clauses, byProp, np, seed).contradiction) continue; // provable
      const [A, B] = hyps;
      if (propagate(clauses, byProp, np, [A, B ^ 1]).contradiction) continue;
      if (propagate(clauses, byProp, np, [B, A ^ 1]).contradiction) continue;
      return { hyps, concl };
    }
    return null;
  }

  // For every open pair, how many open pairs (incl. itself) a true resp.
  // false resolution would settle. pairLits: [[aLit, bLit], ...].
  //
  // false resolution adds only the virtual model closure({A,~B}) — it settles
  // exactly the open pairs (X,Y) with X and ~Y holding in that closure.
  //
  // true resolution adds the clause (~A | B). Since each pair's closure C is
  // a fixpoint of the old clauses, propagation under old+new clauses differs
  // only if the new clause unit-fires on C (A in C with B unknown, or ~B in C
  // with A unknown) — extend C by the forced literal under the old clauses
  // (the new clause is satisfied afterwards) and check for contradiction.
  // The same argument re-closes the space models cheaply. ifTrue = -1 marks
  // "asserting true would contradict a known space" (guards would reject it).
  function computeScores(clauses, np, models, pairLits) {
    const byProp = makeIndex(clauses, np);
    const n = pairLits.length;
    const clos = new Array(n);
    for (let i = 0; i < n; i++) {
      const [a, b] = pairLits[i];
      clos[i] = valToModel(propagate(clauses, byProp, np, [a, b ^ 1]).val);
    }

    const ifFalse = new Array(n).fill(0);
    for (let j = 0; j < n; j++) {
      const m = clos[j];
      let c = 0;
      for (let i = 0; i < n; i++) {
        const [x, y] = pairLits[i];
        if (holdsIn(m, x) && holdsIn(m, y ^ 1)) c++;
      }
      ifFalse[j] = c;
    }

    const ifTrue = new Array(n).fill(0);
    for (let j = 0; j < n; j++) {
      const [A, B] = pairLits[j];
      const clausesJ = clauses.concat([[A ^ 1, B]]);
      const byPropJ = makeIndex(clausesJ, np);
      const changed = [];
      let impossible = false;
      for (const m of models) {
        if (holdsIn(m, A ^ 1) || holdsIn(m, B)) continue;          // satisfied
        const aKnown = m.charCodeAt(A >> 1) !== 63 /* '?' */;
        const bKnown = m.charCodeAt(B >> 1) !== 63;
        if (!aKnown && !bKnown) continue;                          // no unit
        const forced = aKnown ? B : (A ^ 1);
        const pr = propagate(clausesJ, byPropJ, np, modelToLits(m).concat([forced]));
        if (pr.contradiction) { impossible = true; break; }
        changed.push(valToModel(pr.val));
      }
      if (impossible) { ifTrue[j] = -1; continue; }

      let score = 0;
      for (let i = 0; i < n; i++) {
        const [x, y] = pairLits[i];
        let settled = false;
        for (const m of changed) {
          if (holdsIn(m, x) && holdsIn(m, y ^ 1)) { settled = true; break; }
        }
        if (!settled) {
          const Ci = clos[i];
          const hasA = holdsIn(Ci, A), hasNB = holdsIn(Ci, B ^ 1);
          if (hasA && hasNB) settled = true;
          else if (hasA && Ci.charCodeAt(B >> 1) === 63) {
            settled = propagate(clauses, byProp, np,
                                modelToLits(Ci).concat([B])).contradiction;
          } else if (hasNB && Ci.charCodeAt(A >> 1) === 63) {
            settled = propagate(clauses, byProp, np,
                                modelToLits(Ci).concat([A ^ 1])).contradiction;
          }
        }
        if (settled) score++;
      }
      ifTrue[j] = score;
    }
    return { ifTrue, ifFalse };
  }

  return { makeIndex, propagate, propagateProof, holdsIn, hasModel, valToModel,
           modelToLits, recloseModels, computeScores, canonicalStatement,
           drawOpenTriple };
})();
if (typeof module !== 'undefined') module.exports = PiEngine;
