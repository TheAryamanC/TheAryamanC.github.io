/* helpers */
(function (global) {
  'use strict';

  /**
   * Deterministic PRNG (mulberry32). Given the same seed it always produces
   * the same sequence, which matters for a teaching tool: "random" heuristics
   * should still be reproducible when a student re-runs with the same seed.
   * @param {number} seed
   * @returns {() => number} function returning a float in [0, 1)
   */
  function mulberry32(seed) {
    let a = seed >>> 0;
    return function () {
      a |= 0;
      a = (a + 0x6d2b79f5) | 0;
      let t = Math.imul(a ^ (a >>> 15), 1 | a);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }

  /**
   * Standard iterative Luby sequence: 1,1,2,1,1,2,4,1,1,2,1,1,2,4,8,...
   * Used to size restart intervals. Returns the i-th term (1-indexed).
   * @param {number} i
   */
  function luby(i) {
    // Find the finite subsequence that contains index i, and its size.
    let size = 1;
    let seq = 0;
    while (size < i + 1) {
      seq++;
      size = 2 * size + 1;
    }
    while (size - 1 !== i) {
      size = Math.floor((size - 1) / 2);
      seq--;
      i = i % size;
    }
    return Math.pow(2, seq);
  }

  function clamp(x, lo, hi) {
    return Math.max(lo, Math.min(hi, x));
  }

  function average(arr) {
    if (!arr.length) return 0;
    let s = 0;
    for (let i = 0; i < arr.length; i++) s += arr[i];
    return s / arr.length;
  }

  /** Format a signed literal for display, e.g. 5 -> "x5", -5 -> "¬x5" */
  function fmtLit(lit) {
    return (lit < 0 ? '\u00ac' : '') + 'x' + Math.abs(lit);
  }

  const ns = { mulberry32, luby, clamp, average, fmtLit };

  global.SAT = global.SAT || {};
  Object.assign(global.SAT, ns);

  if (typeof module !== 'undefined' && module.exports) {
    module.exports = ns;
  }
})(typeof window !== 'undefined' ? window : globalThis);
