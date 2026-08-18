/* DPLL/CDCL solver written to be stepped through */
(function (global) {
  'use strict';

  const U = global.SAT; // utils.js must load before this file

  const DEFAULT_OPTIONS = {
    mode: 'cdcl', // 'dpll' | 'cdcl'
    heuristic: 'vsids', // 'vsids' | 'jw' | 'dlis' | 'random' | 'fixed'
    polarity: 'phase-saving', // 'phase-saving' | 'true' | 'false' | 'random'
    restart: 'luby', // 'none' | 'fixed' | 'luby' | 'glucose'
    restartInterval: 100,
    lubyUnit: 32,
    glucoseWindow: 30,
    glucoseK: 0.8,
    clauseDeletion: 'lbd', // 'none' | 'activity' | 'size' | 'lbd'
    reduceInterval: 20,
    vsidsDecay: 0.95,
    vsidsBump: 1,
    clauseActivityDecay: 0.999,
    pureLiteralElim: false,
    seed: 1,
    maxSteps: 300000,
  };

  class Solver {
    constructor(formula, options) {
      this.formula = formula;
      this.numVars = formula.numVars;
      this.options = Object.assign({}, DEFAULT_OPTIONS, options || {});

      this.assign = new Int8Array(this.numVars + 1);
      this.level = new Int32Array(this.numVars + 1).fill(-1);
      this.reason = new Array(this.numVars + 1).fill(null);
      this.trail = [];
      this.trailLim = []; // CDCL: trailLim[d] = trail length at start of level d+1
      this.decisionLevel = 0;
      this.qHead = 0;
      this.decisionStack = []; // DPLL only: [{lit, trailIndexBefore, flipped}]

      this.activity = new Float64Array(this.numVars + 1); // VSIDS
      this.savedPhase = new Int8Array(this.numVars + 1); // phase saving: 0/1/-1

      this.rng = U.mulberry32(this.options.seed >>> 0);

      this.stats = {
        decisions: 0,
        propagations: 0,
        conflicts: 0,
        restarts: 0,
        learned: 0,
        deleted: 0,
        maxDecisionLevel: 0,
      };

      this.lubyIndex = 0;
      this.conflictsSinceRestart = 0;
      this.conflictsSinceReduce = 0;
      this.lbdAllSum = 0;
      this.lbdAllCount = 0;
      this.lbdRecent = [];

      this.result = null; // null | 'SAT' | 'UNSAT' | 'LIMIT'
      this.startTime = Date.now();

      this._gen = this._run();
      this._done = false;
    }

    // ---- public stepping API -------------------------------------------------

    /** Advance the solver by exactly one event. Returns {done, value}. */
    step() {
      if (this._done) return { done: true, value: null };
      const r = this._gen.next();
      if (r.done) this._done = true;
      return r;
    }

    isDone() {
      return this._done;
    }

    // ---- assignment / trail bookkeeping ---------------------------------------

    assignLiteral(lit, reasonIdx) {
      const v = lit < 0 ? -lit : lit;
      this.assign[v] = lit > 0 ? 1 : -1;
      this.level[v] = this.decisionLevel;
      this.reason[v] = reasonIdx === undefined ? null : reasonIdx;
      this.trail.push(lit);
    }

    undoToTrailIndex(idx) {
      for (let i = this.trail.length - 1; i >= idx; i--) {
        const lit = this.trail[i];
        const v = lit < 0 ? -lit : lit;
        if (this.options.polarity === 'phase-saving') this.savedPhase[v] = lit > 0 ? 1 : -1;
        this.assign[v] = 0;
        this.level[v] = -1;
        this.reason[v] = null;
      }
      this.trail.length = idx;
      this.qHead = idx;
    }

    backjump(level) {
      const cut = level === 0 ? (this.trailLim.length ? this.trailLim[0] : this.trail.length) : this.trailLim[level];
      this.undoToTrailIndex(cut);
      this.trailLim.length = level;
      this.decisionLevel = level;
    }

    allClausesSatisfied() {
      const clauses = this.formula.clauses;
      for (let i = 0; i < clauses.length; i++) {
        const c = clauses[i];
        if (c.deleted) continue;
        if (!this.formula.clauseStatus(c, this.assign).sat) return false;
      }
      return true;
    }

    verifyAssignment() {
      const clauses = this.formula.clauses;
      for (let i = 0; i < clauses.length; i++) {
        const c = clauses[i];
        if (c.learnt) continue;
        if (!this.formula.clauseStatus(c, this.assign).sat) return false;
      }
      return true;
    }

    // ---- unit propagation ------------------------------------------------------

    *_propagate() {
      while (this.qHead < this.trail.length) {
        const lit = this.trail[this.qHead++];
        const v = lit < 0 ? -lit : lit;
        // lit just became true, so -lit is now false: clauses containing -lit
        // may have become unit or fully falsified.
        const watch = lit > 0 ? this.formula.occNeg[v] : this.formula.occPos[v];
        for (let k = 0; k < watch.length; k++) {
          const cIdx = watch[k];
          const c = this.formula.clauses[cIdx];
          if (c.deleted) continue;
          const st = this.formula.clauseStatus(c, this.assign);
          if (st.conflict) return cIdx;
          if (st.unit && this.assign[st.unassignedLit < 0 ? -st.unassignedLit : st.unassignedLit] === 0) {
            this.assignLiteral(st.unassignedLit, cIdx);
            this.stats.propagations++;
            yield { type: 'propagate', lit: st.unassignedLit, reason: cIdx, level: this.decisionLevel };
          }
        }
      }
      return null;
    }

    // ---- level-0 preprocessing: initial units + optional pure literals -------

    *_initialPreprocess() {
      // Empty clauses (⊥) can't be reached by occurrence-list propagation since
      // they have no literal to trigger a scan — catch them explicitly.
      for (let i = 0; i < this.formula.clauses.length; i++) {
        if (this.formula.clauses[i].size() === 0) return i;
      }
      for (let i = 0; i < this.formula.clauses.length; i++) {
        const c = this.formula.clauses[i];
        if (c.size() !== 1) continue;
        const lit = c.lits[0];
        const v = lit < 0 ? -lit : lit;
        if (this.assign[v] === 0) {
          this.assignLiteral(lit, i);
          this.stats.propagations++;
          yield { type: 'propagate', lit, reason: i, level: 0, initial: true };
        } else {
          const consistent = (lit > 0 && this.assign[v] === 1) || (lit < 0 && this.assign[v] === -1);
          if (!consistent) return i;
        }
      }
      let conflict = yield* this._propagate();
      if (conflict !== null) return conflict;

      if (this.options.pureLiteralElim) {
        let changed = true;
        while (changed) {
          changed = false;
          const appearsPos = new Uint8Array(this.numVars + 1);
          const appearsNeg = new Uint8Array(this.numVars + 1);
          for (const c of this.formula.clauses) {
            if (c.deleted) continue;
            const st = this.formula.clauseStatus(c, this.assign);
            if (st.sat) continue;
            for (const lit of c.lits) {
              const v = lit < 0 ? -lit : lit;
              if (this.assign[v] !== 0) continue;
              if (lit > 0) appearsPos[v] = 1;
              else appearsNeg[v] = 1;
            }
          }
          for (let v = 1; v <= this.numVars; v++) {
            if (this.assign[v] !== 0) continue;
            if (appearsPos[v] && !appearsNeg[v]) {
              this.assignLiteral(v, null);
              yield { type: 'pure_literal', lit: v, level: 0 };
              changed = true;
            } else if (!appearsPos[v] && appearsNeg[v]) {
              this.assignLiteral(-v, null);
              yield { type: 'pure_literal', lit: -v, level: 0 };
              changed = true;
            }
          }
          if (changed) {
            conflict = yield* this._propagate();
            if (conflict !== null) return conflict;
          }
        }
      }
      return null;
    }

    // ---- conflict analysis (1UIP) ----------------------------------------------

    analyzeConflict(conflictIdx) {
      const seen = new Uint8Array(this.numVars + 1);
      let counter = 0;
      const learnt = [];
      const involvedVars = [];
      const involvedClauses = [conflictIdx];
      let p; // literal currently being resolved out; undefined on first pass
      let idx = this.trail.length - 1;
      let clauseLits = this.formula.clauses[conflictIdx].lits;
      const currentLevel = this.decisionLevel;

      do {
        for (let i = 0; i < clauseLits.length; i++) {
          const lit = clauseLits[i];
          if (p !== undefined && (lit < 0 ? -lit : lit) === (p < 0 ? -p : p)) continue;
          const v = lit < 0 ? -lit : lit;
          if (!seen[v] && this.level[v] > 0) {
            seen[v] = 1;
            involvedVars.push(v);
            if (this.level[v] === currentLevel) counter++;
            else learnt.push(lit);
          }
        }
        do {
          idx--;
        } while (idx >= 0 && !seen[this.trail[idx] < 0 ? -this.trail[idx] : this.trail[idx]]);
        if (idx < 0) break; // defensive; should not happen on a well-formed trail
        p = this.trail[idx];
        const v = p < 0 ? -p : p;
        seen[v] = 0;
        counter--;
        if (counter > 0) {
          const r = this.reason[v];
          if (r === null || r === undefined) break; // defensive
          involvedClauses.push(r);
          clauseLits = this.formula.clauses[r].lits;
        }
      } while (counter > 0);

      learnt.unshift(-p);

      let backjumpLevel = 0;
      const levelsSet = new Set();
      for (let i = 0; i < learnt.length; i++) {
        const v = learnt[i] < 0 ? -learnt[i] : learnt[i];
        levelsSet.add(this.level[v]);
        if (i > 0) backjumpLevel = Math.max(backjumpLevel, this.level[v]);
      }
      const lbd = levelsSet.size || 1;

      return { learntClause: learnt, backjumpLevel, lbd, involvedVars, involvedClauses };
    }

    // ---- DPLL chronological backtracking --------------------------------------

    dpllBacktrack() {
      while (this.decisionStack.length > 0) {
        const top = this.decisionStack[this.decisionStack.length - 1];
        if (!top.flipped) {
          this.undoToTrailIndex(top.trailIndexBefore);
          top.flipped = true;
          const newLit = -top.lit;
          top.lit = newLit;
          this.decisionLevel = this.decisionStack.length;
          this.assignLiteral(newLit, null);
          return { exhausted: false, flippedTo: newLit, level: this.decisionLevel };
        }
        this.undoToTrailIndex(top.trailIndexBefore);
        this.decisionStack.pop();
        this.decisionLevel = this.decisionStack.length;
      }
      return { exhausted: true };
    }

    // ---- decision heuristics ----------------------------------------------------

    pickDecisionLiteral() {
      switch (this.options.heuristic) {
        case 'jw':
          return this._pickJW();
        case 'dlis':
          return this._pickDLIS();
        case 'random':
          return this._pickRandom();
        case 'fixed':
          return this._pickFixed();
        case 'vsids':
        default:
          return this._pickVSIDS();
      }
    }

    _applyPolarity(v) {
      let posTrue;
      switch (this.options.polarity) {
        case 'true':
          posTrue = true;
          break;
        case 'false':
          posTrue = false;
          break;
        case 'random':
          posTrue = this.rng() < 0.5;
          break;
        case 'phase-saving':
        default:
          posTrue = this.savedPhase[v] !== -1;
          break;
      }
      return posTrue ? v : -v;
    }

    _pickVSIDS() {
      let best = -1;
      let bestScore = -1;
      for (let v = 1; v <= this.numVars; v++) {
        if (this.assign[v] !== 0) continue;
        const s = this.activity[v];
        if (best === -1 || s > bestScore) {
          bestScore = s;
          best = v;
        }
      }
      if (best === -1) return null;
      return this._applyPolarity(best);
    }

    _computeJWScores() {
      const pos = new Float64Array(this.numVars + 1);
      const neg = new Float64Array(this.numVars + 1);
      for (const c of this.formula.clauses) {
        if (c.deleted) continue;
        const st = this.formula.clauseStatus(c, this.assign);
        if (st.sat) continue;
        const w = Math.pow(2, -c.size());
        for (const lit of c.lits) {
          const v = lit < 0 ? -lit : lit;
          if (this.assign[v] !== 0) continue;
          if (lit > 0) pos[v] += w;
          else neg[v] += w;
        }
      }
      return { pos, neg };
    }

    _pickJW() {
      const { pos, neg } = this._computeJWScores();
      let best = -1;
      let bestScore = -1;
      let bestPos = true;
      for (let v = 1; v <= this.numVars; v++) {
        if (this.assign[v] !== 0) continue;
        const combined = pos[v] + neg[v];
        if (best === -1 || combined > bestScore) {
          bestScore = combined;
          best = v;
          bestPos = pos[v] >= neg[v];
        }
      }
      if (best === -1) return null;
      return bestPos ? best : -best;
    }

    _computeDLISCounts() {
      const pos = new Int32Array(this.numVars + 1);
      const neg = new Int32Array(this.numVars + 1);
      for (const c of this.formula.clauses) {
        if (c.deleted) continue;
        const st = this.formula.clauseStatus(c, this.assign);
        if (st.sat) continue;
        for (const lit of c.lits) {
          const v = lit < 0 ? -lit : lit;
          if (this.assign[v] !== 0) continue;
          if (lit > 0) pos[v]++;
          else neg[v]++;
        }
      }
      return { pos, neg };
    }

    _pickDLIS() {
      const { pos, neg } = this._computeDLISCounts();
      let bestLit = null;
      let bestCount = -1;
      for (let v = 1; v <= this.numVars; v++) {
        if (this.assign[v] !== 0) continue;
        if (pos[v] > bestCount) {
          bestCount = pos[v];
          bestLit = v;
        }
        if (neg[v] > bestCount) {
          bestCount = neg[v];
          bestLit = -v;
        }
      }
      return bestLit;
    }

    _pickRandom() {
      const unassigned = [];
      for (let v = 1; v <= this.numVars; v++) if (this.assign[v] === 0) unassigned.push(v);
      if (!unassigned.length) return null;
      const v = unassigned[Math.floor(this.rng() * unassigned.length)];
      return this._applyPolarity(v);
    }

    _pickFixed() {
      for (let v = 1; v <= this.numVars; v++) {
        if (this.assign[v] === 0) return this._applyPolarity(v);
      }
      return null;
    }

    getHeuristicScores() {
      switch (this.options.heuristic) {
        case 'vsids': {
          const items = [];
          for (let v = 1; v <= this.numVars; v++) if (this.assign[v] === 0) items.push({ v, score: this.activity[v] });
          items.sort((a, b) => b.score - a.score);
          return { type: 'vsids', items };
        }
        case 'jw': {
          const { pos, neg } = this._computeJWScores();
          const items = [];
          for (let v = 1; v <= this.numVars; v++)
            if (this.assign[v] === 0) items.push({ v, score: pos[v] + neg[v], pos: pos[v], neg: neg[v] });
          items.sort((a, b) => b.score - a.score);
          return { type: 'jw', items };
        }
        case 'dlis': {
          const { pos, neg } = this._computeDLISCounts();
          const items = [];
          for (let v = 1; v <= this.numVars; v++)
            if (this.assign[v] === 0) items.push({ v, score: Math.max(pos[v], neg[v]), pos: pos[v], neg: neg[v] });
          items.sort((a, b) => b.score - a.score);
          return { type: 'jw', items };
        }
        default:
          return { type: this.options.heuristic, items: [] };
      }
    }

    // ---- activity bumping / decay -----------------------------------------------

    bumpVarActivity(vars) {
      if (this.options.heuristic !== 'vsids') return;
      const bump = this.options.vsidsBump;
      for (let i = 0; i < vars.length; i++) this.activity[vars[i]] += bump;
    }

    bumpClauseActivity(clauseIdxs) {
      const bump = this.options.vsidsBump;
      for (let i = 0; i < clauseIdxs.length; i++) {
        const c = this.formula.clauses[clauseIdxs[i]];
        if (c && c.learnt) c.activity += bump;
      }
    }

    decayActivities() {
      if (this.options.heuristic === 'vsids') {
        for (let v = 1; v <= this.numVars; v++) this.activity[v] *= this.options.vsidsDecay;
      }
      const clauses = this.formula.clauses;
      for (let i = 0; i < clauses.length; i++) {
        if (clauses[i].learnt) clauses[i].activity *= this.options.clauseActivityDecay;
      }
    }

    // ---- restarts -----------------------------------------------------------------

    recordLBD(lbd) {
      this.lbdAllSum += lbd;
      this.lbdAllCount++;
      this.lbdRecent.push(lbd);
      if (this.lbdRecent.length > this.options.glucoseWindow) this.lbdRecent.shift();
    }

    shouldRestart() {
      switch (this.options.restart) {
        case 'fixed':
          return this.conflictsSinceRestart >= this.options.restartInterval;
        case 'luby':
          return this.conflictsSinceRestart >= this.options.lubyUnit * U.luby(this.lubyIndex + 1);
        case 'glucose': {
          if (this.lbdRecent.length < this.options.glucoseWindow || this.lbdAllCount === 0) return false;
          const globalAvg = this.lbdAllSum / this.lbdAllCount;
          const recentAvg = U.average(this.lbdRecent);
          return recentAvg * this.options.glucoseK > globalAvg;
        }
        default:
          return false;
      }
    }

    // ---- learned clause database reduction -----------------------------------------

    shouldReduceDB() {
      return this.conflictsSinceReduce >= this.options.reduceInterval;
    }

    reduceClauseDB() {
      this.conflictsSinceReduce = 0;
      const locked = new Set();
      for (let v = 1; v <= this.numVars; v++) {
        if (this.assign[v] !== 0 && this.reason[v] !== null && this.reason[v] !== undefined) locked.add(this.reason[v]);
      }
      const candidates = [];
      this.formula.clauses.forEach((c, i) => {
        if (!c.learnt || c.deleted) return;
        if (locked.has(i)) return;
        if (this.options.clauseDeletion === 'lbd' && c.lbd <= 2) return; // protect glue clauses
        candidates.push(i);
      });
      const metric = (i) => {
        const c = this.formula.clauses[i];
        if (this.options.clauseDeletion === 'activity') return c.activity;
        if (this.options.clauseDeletion === 'size') return -c.size();
        if (this.options.clauseDeletion === 'lbd') return -c.lbd;
        return 0;
      };
      candidates.sort((a, b) => metric(b) - metric(a)); // best (keep) first, worst (drop) last
      const removeCount = Math.floor(candidates.length / 2);
      const toRemove = candidates.slice(candidates.length - removeCount);
      toRemove.forEach((i) => {
        this.formula.clauses[i].deleted = true;
      });
      this.stats.deleted += toRemove.length;
      return toRemove.length;
    }

    // ---- main loop -----------------------------------------------------------------

    *_run() {
      const initConflict = yield* this._initialPreprocess();
      if (initConflict !== null) {
        this.result = 'UNSAT';
        yield { type: 'unsat', clause: initConflict };
        return 'UNSAT';
      }
      if (this.allClausesSatisfied()) {
        this.result = 'SAT';
        yield { type: 'sat' };
        return 'SAT';
      }

      let guard = 0;
      while (true) {
        guard++;
        if (guard > this.options.maxSteps) {
          this.result = 'LIMIT';
          yield { type: 'limit_reached', steps: guard };
          return 'LIMIT';
        }

        const conflictIdx = yield* this._propagate();

        if (conflictIdx !== null) {
          this.stats.conflicts++;
          yield { type: 'conflict', clause: conflictIdx, level: this.decisionLevel };

          if (this.options.mode === 'dpll') {
            const res = this.dpllBacktrack();
            yield Object.assign({ type: 'backtrack' }, res);
            if (res.exhausted) {
              this.result = 'UNSAT';
              yield { type: 'unsat' };
              return 'UNSAT';
            }
          } else {
            if (this.decisionLevel === 0) {
              this.result = 'UNSAT';
              yield { type: 'unsat' };
              return 'UNSAT';
            }
            const ana = this.analyzeConflict(conflictIdx);
            const learntIdx = this.formula.addClause(ana.learntClause, { learnt: true, lbd: ana.lbd });
            this.stats.learned++;
            this.recordLBD(ana.lbd);
            this.decayActivities();
            this.bumpVarActivity(ana.involvedVars);
            this.bumpClauseActivity(ana.involvedClauses);
            yield {
              type: 'learn',
              clauseIdx: learntIdx,
              clause: ana.learntClause.slice(),
              lbd: ana.lbd,
              backjumpLevel: ana.backjumpLevel,
            };
            this.backjump(ana.backjumpLevel);
            yield { type: 'backjump', level: ana.backjumpLevel };
            this.assignLiteral(ana.learntClause[0], learntIdx);
            this.stats.propagations++;
            yield { type: 'propagate', lit: ana.learntClause[0], reason: learntIdx, level: this.decisionLevel, asserting: true };
            this.conflictsSinceRestart++;
            this.conflictsSinceReduce++;
          }
          continue;
        }

        if (this.allClausesSatisfied()) {
          this.result = 'SAT';
          yield { type: 'sat' };
          return 'SAT';
        }

        if (this.options.mode === 'cdcl' && this.options.restart !== 'none' && this.shouldRestart()) {
          yield { type: 'restart', level: this.decisionLevel };
          this.backjump(0);
          this.stats.restarts++;
          this.conflictsSinceRestart = 0;
          this.lubyIndex++;
          continue;
        }

        if (this.options.mode === 'cdcl' && this.options.clauseDeletion !== 'none' && this.shouldReduceDB()) {
          const removed = this.reduceClauseDB();
          if (removed > 0) {
            yield { type: 'reduceDB', removed };
            continue;
          }
        }

        const lit = this.pickDecisionLiteral();
        if (lit === null) {
          this.result = 'SAT';
          yield { type: 'sat' };
          return 'SAT';
        }
        if (this.options.mode === 'cdcl') {
          this.trailLim.push(this.trail.length);
          this.decisionLevel = this.trailLim.length;
        } else {
          this.decisionStack.push({ lit, trailIndexBefore: this.trail.length, flipped: false });
          this.decisionLevel = this.decisionStack.length;
        }
        this.assignLiteral(lit, null);
        this.stats.decisions++;
        this.stats.maxDecisionLevel = Math.max(this.stats.maxDecisionLevel, this.decisionLevel);
        yield { type: 'decision', lit, level: this.decisionLevel };
      }
    }
  }

  const ns = { Solver, DEFAULT_OPTIONS };

  global.SAT = global.SAT || {};
  Object.assign(global.SAT, ns);

  if (typeof module !== 'undefined' && module.exports) {
    module.exports = ns;
  }
})(typeof window !== 'undefined' ? window : globalThis);
