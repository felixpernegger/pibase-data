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

  // Does the literal hold in the model string?
  function holdsIn(model, lit) {
    return model.charCodeAt(lit >> 1) === ((lit & 1) === 0 ? 49 /*'1'*/ : 48 /*'0'*/);
  }

  // Is there a model where both literals hold? (counterexample check: pass a, ~b)
  function hasModel(models, litA, litB) {
    for (const m of models) {
      if (holdsIn(m, litA) && holdsIn(m, litB)) return true;
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

  return { makeIndex, propagate, holdsIn, hasModel, valToModel, modelToLits, recloseModels };
})();
if (typeof module !== 'undefined') module.exports = PiEngine;
