/* dimacs.js — parses DIMACS CNF text into a plain {numVars, clauses} shape */
(function (global) {
  'use strict';

  const MAX_LINES = 1000;

  /**
   * @param {string} text raw textarea contents
   * @returns {{ok:boolean, numVars?:number, clauses?:number[][], errors:string[], warnings:string[], lineCount:number}}
   */
  function parseDimacs(text) {
    const rawLines = (text || '').split(/\r\n|\r|\n/);
    const errors = [];
    const warnings = [];
    const lineCount = rawLines.length;

    if (lineCount > MAX_LINES) {
      errors.push(
        'Input is too long'
      );
      return { ok: false, errors, warnings, lineCount };
    }

    let declaredVars = 0;
    let declaredClauses = null;
    let sawProblemLine = false;
    let maxVarSeen = 0;
    const clauses = [];
    let cur = [];
    let curStartLine = null;

    for (let i = 0; i < rawLines.length; i++) {
      const lineNo = i + 1;
      const line = rawLines[i].trim();
      if (line.length === 0) continue;
      if (line[0] === 'c' || line[0] === 'C') continue; // comment line
      if (line[0] === 'p' || line[0] === 'P') {
        const parts = line.split(/\s+/);
        if (parts.length < 4 || parts[1].toLowerCase() !== 'cnf') {
          errors.push('Incorrectly written problem statement line');
          continue;
        }
        declaredVars = parseInt(parts[2], 10) || 0;
        declaredClauses = parseInt(parts[3], 10);
        sawProblemLine = true;
        continue;
      }

      const tokens = line.split(/\s+/).filter(Boolean);
      for (const tok of tokens) {
        const n = parseInt(tok, 10);
        if (Number.isNaN(n) || String(n) !== tok.replace(/^\+/, '')) {
          errors.push('Not valid literal');
          continue;
        }
        if (curStartLine === null) curStartLine = lineNo;
        if (n === 0) {
          clauses.push(cur);
          cur = [];
          curStartLine = null;
        } else {
          maxVarSeen = Math.max(maxVarSeen, Math.abs(n));
          cur.push(n);
        }
      }
    }

    if (cur.length > 0) {
      clauses.push(cur);
    }

    const numVars = Math.max(declaredVars, maxVarSeen);

    if (clauses.length === 0) {
      return { ok: false, errors, warnings, lineCount };
    }

    return { ok: true, numVars, clauses, errors, warnings, lineCount };
  }

  /** Convert assignment back into DIMACS model line, e.g. "v 1 -2 3 0" */
  function formatModelLine(assign, numVars) {
    const lits = [];
    for (let v = 1; v <= numVars; v++) {
      const val = assign[v];
      lits.push(val >= 0 ? v : -v); // don't-care variables default to true
    }
    return lits.join(' ') + ' 0';
  }

  /** Serialize a Formula's original (non-learnt) clauses back to DIMACS text. */
  function toDimacs(formula) {
    const orig = formula.clauses.filter((c) => !c.learnt);
    let out = 'p cnf ' + formula.numVars + ' ' + orig.length + '\n';
    orig.forEach((c) => {
      out += c.lits.join(' ');
    });
    return out;
  }

  const ns = { parseDimacs, formatModelLine, toDimacs, MAX_LINES };

  global.SAT = global.SAT || {};
  Object.assign(global.SAT, ns);

  if (typeof module !== 'undefined' && module.exports) {
    module.exports = ns;
  }
})(typeof window !== 'undefined' ? window : globalThis);
