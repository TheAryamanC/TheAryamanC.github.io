/* SAT formula structure */
(function (global) {
  'use strict';

  let nextClauseId = 0;

  class Clause {
    constructor(lits, opts) {
      opts = opts || {};
      this.lits = lits.slice();
      this.learnt = !!opts.learnt;
      this.activity = 0;
      this.lbd = opts.lbd !== undefined ? opts.lbd : this.lits.length;
      this.deleted = false;
      this.id = opts.id !== undefined ? opts.id : nextClauseId++;
    }
    size() {
      return this.lits.length;
    }
  }

  class Formula {
    /**
     * @param {number} numVars
     * @param {number[][]} clauseLitsArray
     */
    constructor(numVars, clauseLitsArray) {
      this.numVars = numVars || 0;
      this.clauses = [];
      this.occPos = [[]]; // occPos[v] = clause indices where +v appears
      this.occNeg = [[]]; // occNeg[v] = clause indices where -v appears
      this._growOccTo(this.numVars);
      (clauseLitsArray || []).forEach((lits) => this.addClause(lits, {}));
    }

    _growOccTo(v) {
      while (this.occPos.length <= v) this.occPos.push([]);
      while (this.occNeg.length <= v) this.occNeg.push([]);
    }

    addClause(lits, opts) {
      const idx = this.clauses.length;
      const c = new Clause(lits, opts);
      this.clauses.push(c);
      const seenVars = new Set();
      for (const lit of lits) {
        const v = Math.abs(lit);
        if (v > this.numVars) {
          this.numVars = v;
        }
        this._growOccTo(v);
        if (seenVars.has(v)) continue; // ignore duplicate literals of same var for occurrence bookkeeping edge case
        seenVars.add(v);
      }
      for (const lit of lits) {
        const v = Math.abs(lit);
        if (lit > 0) this.occPos[v].push(idx);
        else this.occNeg[v].push(idx);
      }
      return idx;
    }

    /**
     * Evaluate a clause against a partial assignment.
     * assign[v] is 0 (unassigned), 1 (true) or -1 (false).
     * Returns {sat, conflict, unit, unassignedLit, unassignedCount}.
     */
    clauseStatus(c, assign) {
      let unassignedLit = null;
      let unassignedCount = 0;
      const lits = c.lits;
      for (let i = 0; i < lits.length; i++) {
        const lit = lits[i];
        const v = lit < 0 ? -lit : lit;
        const val = assign[v];
        if (val === 0) {
          unassignedCount++;
          unassignedLit = lit;
        } else if ((lit > 0 && val === 1) || (lit < 0 && val === -1)) {
          return { sat: true, conflict: false, unit: false, unassignedLit: null, unassignedCount };
        }
      }
      if (unassignedCount === 0) {
        return { sat: false, conflict: true, unit: false, unassignedLit: null, unassignedCount: 0 };
      }
      if (unassignedCount === 1) {
        return { sat: false, conflict: false, unit: true, unassignedLit, unassignedCount: 1 };
      }
      return { sat: false, conflict: false, unit: false, unassignedLit: null, unassignedCount };
    }
  }

  /** Bipartite Variable-Clause Graph (incidence graph) of the *original* formula. */
  function buildVCG(formula) {
    const nodes = [];
    const edges = [];
    for (let v = 1; v <= formula.numVars; v++) {
      nodes.push({ id: 'v' + v, label: 'x' + v, type: 'var', v });
    }
    formula.clauses.forEach((c, i) => {
      if (c.learnt) return; // structural graph reflects the input problem
      nodes.push({ id: 'c' + i, label: 'C' + (i + 1), type: 'clause', size: c.size() });
    });
    formula.clauses.forEach((c, i) => {
      if (c.learnt) return;
      const seen = new Set();
      c.lits.forEach((lit) => {
        const v = Math.abs(lit);
        if (seen.has(v)) return;
        seen.add(v);
        edges.push({ source: 'v' + v, target: 'c' + i, positive: lit > 0 });
      });
    });
    return { nodes, edges };
  }

  /** Variable Interaction Graph: edge between two vars that co-occur in a clause, weighted by count. */
  function buildVIG(formula) {
    const nodes = [];
    for (let v = 1; v <= formula.numVars; v++) {
      nodes.push({ id: 'v' + v, label: 'x' + v, type: 'var', v });
    }
    const weight = new Map();
    formula.clauses.forEach((c) => {
      if (c.learnt) return;
      const vars = Array.from(new Set(c.lits.map((l) => Math.abs(l))));
      for (let i = 0; i < vars.length; i++) {
        for (let j = i + 1; j < vars.length; j++) {
          const a = Math.min(vars[i], vars[j]);
          const b = Math.max(vars[i], vars[j]);
          const k = a + '_' + b;
          weight.set(k, (weight.get(k) || 0) + 1);
        }
      }
    });
    const edges = [];
    weight.forEach((w, k) => {
      const parts = k.split('_');
      edges.push({ source: 'v' + parts[0], target: 'v' + parts[1], weight: w });
    });
    return { nodes, edges };
  }

  const ns = { Clause, Formula, buildVCG, buildVIG };

  global.SAT = global.SAT || {};
  Object.assign(global.SAT, ns);

  if (typeof module !== 'undefined' && module.exports) {
    module.exports = ns;
  }
})(typeof window !== 'undefined' ? window : globalThis);
