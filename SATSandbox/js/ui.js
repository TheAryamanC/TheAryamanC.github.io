(function () {
  'use strict';

  const SAT = window.SAT;

  const state = {
    parsed: null,
    solver: null,
    needsReinit: true,
    mode: 'cdcl',
    lastEvent: null,
    running: false,
    pauseRequested: false,
    mounts: { structural: null, implication: null },
    currentGraphKind: 'vcg',
    clauseDbSort: { field: 'id', dir: 'asc' },
    clauseDbFilter: 'all',
    clauseDbShowDeleted: false,
  };
  let runToken = 0;

  const $ = (id) => document.getElementById(id);

  // ---- hints (make the sandbox self-explanatory) ------------------------------

  const HEURISTIC_HINTS = {
    vsids: 'Variable State Independent Decaying Sum \u2014 scores rise when a variable appears in a recent conflict, and quietly decay over time. The classic CDCL heuristic.',
    jw: 'Jeroslow\u2013Wang \u2014 favours variables that appear in many short, still-unsatisfied clauses, weighted 2\u207B\u02E2\u1D62\u1DBB\u1DE6.',
    dlis: 'Dynamic Largest Individual Sum \u2014 picks the single literal appearing in the most currently-unsatisfied clauses, deciding variable and polarity together.',
    random: 'Uniformly random variable and polarity, driven by the seed below \u2014 so a "random" run is still reproducible.',
    fixed: 'Always the lowest-indexed unassigned variable. A naive baseline \u2014 useful for seeing what the smarter heuristics are improving on.',
  };
  const RESTART_HINTS = {
    none: 'Never restart. The trail only ever shrinks via backjumping after a conflict.',
    fixed: 'Restart every fixed number of conflicts (set in Advanced settings).',
    luby: 'Restart on the Luby sequence (1,1,2,1,1,2,4,\u2026) \u00d7 a unit \u2014 short restarts early, longer ones later. A strong general-purpose default.',
    glucose: 'Restart when the recent average LBD of learned clauses is notably worse than the long-run average \u2014 a sign the search has wandered somewhere unproductive.',
  };
  const DELETION_HINTS = {
    none: 'Keep every learned clause forever. Simple, but the database only grows.',
    activity: 'Periodically drop the least recently "useful" learned clauses \u2014 the same idea as VSIDS, applied to clauses.',
    size: 'Periodically drop the largest learned clauses \u2014 shorter clauses constrain the search more per byte.',
    lbd: 'Periodically drop learned clauses with a high LBD. Clauses with LBD \u2264 2 ("glue clauses") are always protected.',
  };

  function updateHints() {
    // $('heuristicHint').textContent = HEURISTIC_HINTS[$('heuristicSelect').value] || '';
    // $('restartHint').textContent = RESTART_HINTS[$('restartSelect').value] || '';
    // $('deletionHint').textContent = DELETION_HINTS[$('deletionSelect').value] || '';
  }

  // ---- input parsing ------------------------------------------------------------

  function parseCurrentInput() {
    const text = $('dimacsInput').value;
    const lineCount = text.split(/\r\n|\r|\n/).length;
    const counter = $('lineCounter');
    counter.textContent = lineCount + ' / 1000 lines';
    counter.classList.toggle('over-limit', lineCount > 1000);

    const parsed = SAT.parseDimacs(text);
    const statusEl = $('parseStatus');
    if (!parsed.ok) {
      statusEl.textContent = parsed.errors[0] || 'Could not parse input';
      statusEl.className = 'parse-status parse-error';
    } else {
      let msg = parsed.numVars + ' variable' + (parsed.numVars === 1 ? '' : 's') + ', ' + parsed.clauses.length + ' clause' + (parsed.clauses.length === 1 ? '' : 's');
      if (parsed.warnings.length) msg += ' \u2014 ' + parsed.warnings.length + ' warning' + (parsed.warnings.length === 1 ? '' : 's') + ': ' + parsed.warnings[0];
      statusEl.textContent = msg;
      statusEl.className = 'parse-status ' + (parsed.warnings.length ? 'parse-warning' : 'parse-ok');
    }
    state.parsed = parsed;
    state.needsReinit = true;
    dropStaleSolver();
    updateActionAvailability();
    return parsed;
  }

  function updateActionAvailability() {
    const ok = !!(state.parsed && state.parsed.ok);
    ['btnGenVCG', 'btnGenVIG', 'btnStep', 'btnRun'].forEach((id) => {
      $(id).disabled = !ok;
    });
  }

  function dropStaleSolver() {
    if (state.running) return; // never yank the solver out from under a live run
    state.solver = null;
    state.lastEvent = null;
    renderAll();
    updateStatus(null);
    renderResult(null);
  }

  // ---- structural graphs (VCG / VIG) -----------------------------------------------

  function renderStructuralLegend(kind) {
    const el = $('structuralGraphLegend');
    if (kind === 'vcg') {
      el.innerHTML =
        '<span class="legend-item"><span class="legend-swatch legend-var"></span>variable</span>' +
        '<span class="legend-item"><span class="legend-swatch legend-clause"></span>clause</span>' +
        '<span class="legend-item"><span class="legend-line legend-line-solid"></span>positive literal</span>' +
        '<span class="legend-item"><span class="legend-line legend-line-dashed"></span>negative literal</span>';
    } else {
      el.innerHTML =
        '<span class="legend-item"><span class="legend-swatch legend-var"></span>variable</span>' +
        '<span class="legend-item"><span class="legend-line legend-line-solid"></span>co-occurs in a clause</span>';
    }
  }

  function showStructuralGraph(kind) {
    if (!state.parsed || !state.parsed.ok) return;
    const formula = new SAT.Formula(state.parsed.numVars, state.parsed.clauses);
    $('structuralGraphPanel').hidden = false;
    document.querySelectorAll('.graph-tab').forEach((b) => b.classList.toggle('active', b.dataset.graph === kind));
    const host = $('structuralGraphHost');
    const w = Math.max(560, Math.min(1100, host.clientWidth || 900));
    const result = kind === 'vcg' ? SAT.renderVCG(host, formula, { width: w, height: 480 }) : SAT.renderVIG(host, formula, { width: w, height: 480 });
    state.mounts.structural = result.mount;
    $('structuralGraphMeta').textContent =
      result.nodeCount + ' node(s), ' + result.edgeCount + ' edge(s)';
    renderStructuralLegend(kind);
    state.currentGraphKind = kind;
  }

  function renderImplicationLegend() {
    $('implicationLegend').innerHTML =
      '<span class="legend-item"><span class="legend-swatch legend-decision"></span>decision</span>' +
      '<span class="legend-item"><span class="legend-swatch legend-propagated"></span>propagated</span>' +
      '<span class="legend-item"><span class="legend-swatch legend-conflict"></span>conflict (\u22a5)</span>' +
      '<span class="legend-item">colour = assigned true / false</span>';
  }

  // ---- solver options from the form --------------------------------------------

  function readSolverOptions() {
    return {
      mode: state.mode,
      heuristic: $('heuristicSelect').value,
      polarity: $('polaritySelect').value,
      restart: $('restartSelect').value,
      clauseDeletion: $('deletionSelect').value,
      pureLiteralElim: $('pureLiteralCheckbox').checked,
      seed: parseInt($('seedInput').value, 10) || 1,
      restartInterval: parseInt($('restartIntervalInput').value, 10) || 100,
      lubyUnit: parseInt($('lubyUnitInput').value, 10) || 32,
      glucoseWindow: parseInt($('glucoseWindowInput').value, 10) || 30,
      glucoseK: parseFloat($('glucoseKInput').value) || 0.8,
      reduceInterval: parseInt($('reduceIntervalInput').value, 10) || 20,
      vsidsDecay: parseFloat($('vsidsDecayInput').value) || 0.95,
      maxSteps: parseInt($('maxStepsInput').value, 10) || 300000,
    };
  }

  // NOTE: index.html has no #vsidsDpllNote element — guarded.
  function updateVsidsDpllNote() {
    const el = $('vsidsDpllNote');
    if (!el) return;
    el.hidden = !(state.mode === 'dpll' && $('heuristicSelect').value === 'vsids');
  }

  // NOTE: index.html has no #dpllModeNote element — guarded.
  function updateModeDependentControls() {
    const isDpll = state.mode === 'dpll';
    $('restartSelect').disabled = isDpll;
    $('deletionSelect').disabled = isDpll;
    const note = $('dpllModeNote');
    if (note) note.hidden = !isDpll;
    updateVsidsDpllNote();
  }

  // ---- solver lifecycle -----------------------------------------------------------

  function initSolver() {
    const parsed = state.parsed && state.parsed.ok ? state.parsed : parseCurrentInput();
    if (!parsed.ok) return null;
    const formula = new SAT.Formula(parsed.numVars, parsed.clauses);
    const options = readSolverOptions();
    const solver = new SAT.Solver(formula, options);
    state.solver = solver;
    state.needsReinit = false;
    state.lastEvent = null;
    $('btnPause').hidden = true;
    $('btnRun').hidden = false;
    renderAll();
    updateStatus(solver);
    renderResult(solver);
    $('lastEventText').textContent = '';
    return solver;
  }

  function describeEvent(ev) {
    if (!ev) return '';
    const L = SAT.fmtLit;
    switch (ev.type) {
      case 'propagate':
        return (ev.asserting ? 'Assert (from the just-learned clause): ' : 'Propagate: ') + L(ev.lit) + ' via C' + (ev.reason + 1) + ' \u2014 level ' + ev.level;
      case 'pure_literal':
        return 'Pure literal: ' + L(ev.lit) + ' appears with only one polarity in the remaining formula, so it can be fixed for free.';
      case 'decision':
        return 'Decision: ' + L(ev.lit) + ' \u2014 opens level ' + ev.level;
      case 'conflict':
        return 'Conflict in C' + (ev.clause + 1) + ' at level ' + ev.level;
      case 'backtrack':
        return ev.exhausted ? 'Both branches exhausted at this level \u2014 backtracking further.' : 'Chronological backtrack: flip to ' + L(ev.flippedTo) + ' \u2014 level ' + ev.level;
      case 'learn':
        return 'Learned C' + (ev.clauseIdx + 1) + ' (size ' + ev.clause.length + ', LBD ' + ev.lbd + '): (' + ev.clause.map(L).join(' \u2228 ') + ')';
      case 'backjump':
        return 'Backjump to level ' + ev.level;
      case 'restart':
        return 'Restart \u2014 trail cleared back to level 0 (learned clauses are kept)';
      case 'reduceDB':
        return 'Clause DB reduced: ' + ev.removed + ' learned clause(s) dropped';
      case 'sat':
        return 'SAT \u2014 every clause is satisfied.';
      case 'unsat':
        return 'UNSAT \u2014 derived a contradiction at level 0.';
      case 'limit_reached':
        return 'Step safety cap reached (' + ev.steps + ' actions) \u2014 this instance may just be hard. Raise the cap in Advanced settings to keep searching.';
      default:
        return '';
    }
  }

  // NOTE: index.html has no #statusDot / #statusText elements — guarded.
  function updateStatus(solver, note) {
    const dot = $('statusDot');
    const text = $('statusText');
    if (dot) dot.className = 'status-dot';
    if (!solver) {
      if (text) text.textContent = 'Not started';
      return;
    }
    if (solver.result === 'SAT') {
      if (dot) dot.classList.add('status-sat');
      if (text) text.textContent = note || 'SAT';
    } else if (solver.result === 'UNSAT') {
      if (dot) dot.classList.add('status-unsat');
      if (text) text.textContent = note || 'UNSAT';
    } else if (solver.result === 'LIMIT') {
      if (dot) dot.classList.add('status-limit');
      if (text) text.textContent = note || 'Step limit reached';
    } else {
      if (dot) dot.classList.add('status-running');
      if (text) text.textContent = note || 'Ready \u2014 level ' + solver.decisionLevel;
    }
  }

  function renderResult(solver) {
    const el = $('resultOutput');
    el.classList.remove('result-sat', 'result-unsat', 'result-waiting', 'result-limit');
    if (!solver || solver.result === null) {
      // el.textContent = 'Configure the solver and press Step or Run.';
      el.classList.add('result-waiting');
      return;
    }
    if (solver.result === 'SAT') {
      const verified = solver.verifyAssignment();
      const model = SAT.formatModelLine(solver.assign, solver.numVars);
      el.textContent = 'SAT\n' + model;
      el.classList.add('result-sat');
    } else if (solver.result === 'UNSAT') {
      el.textContent = 'UNSAT';
      el.classList.add('result-unsat');
    } else if (solver.result === 'LIMIT') {
      el.textContent = 'Step limit reached before a verdict.\nThis instance may be genuinely hard \u2014 try CDCL with Luby restarts, or raise the safety cap in Advanced settings.';
      el.classList.add('result-limit');
    } else {
      el.textContent = 'Still searching\u2026 (' + solver.stats.decisions + ' decisions, ' + solver.stats.conflicts + ' conflicts so far)';
      el.classList.add('result-waiting');
    }
  }

  // ---- panel renderers --------------------------------------------------------------

  function renderTrail(solver) {
    const host = $('trailHost');
    if (!solver || solver.trail.length === 0) {
      // host.innerHTML = '<p class="empty-note">Empty \u2014 no literals assigned yet.</p>';
      return;
    }
    let html = '<table class="trail-table"><thead><tr><th>#</th><th>Literal</th><th>Level</th><th>Antecedent</th></tr></thead><tbody>';
    for (let i = solver.trail.length - 1; i >= 0; i--) {
      const lit = solver.trail[i];
      const v = lit < 0 ? -lit : lit;
      const lvl = solver.level[v];
      const r = solver.reason[v];
      const isDecision = r === null || r === undefined;
      const ante = isDecision ? '<span class="tag tag-decision">decision</span>' : 'C' + (r + 1);
      html +=
        '<tr class="' + (lit > 0 ? 'val-true' : 'val-false') + '"><td>' + (i + 1) + '</td><td class="mono">' + SAT.fmtLit(lit) + '</td><td>' + lvl + '</td><td>' + ante + '</td></tr>';
    }
    html += '</tbody></table>';
    host.innerHTML = html;
  }

  function clauseDbTh(label, field) {
    const active = state.clauseDbSort.field === field;
    const arrow = active ? (state.clauseDbSort.dir === 'asc' ? ' \u2191' : ' \u2193') : '';
    return '<th class="sortable" data-sort-field="' + field + '">' + label + arrow + '</th>';
  }

  function renderClauseDB(solver) {
    const host = $('clauseDbHost');
    if (!solver) {
      // host.innerHTML = '<p class="empty-note">Start the solver to populate the clause database.</p>';
      return;
    }
    let rows = solver.formula.clauses.map((c, i) => ({ i, c }));
    if (!state.clauseDbShowDeleted) rows = rows.filter((r) => !r.c.deleted);
    if (state.clauseDbFilter === 'original') rows = rows.filter((r) => !r.c.learnt);
    if (state.clauseDbFilter === 'learnt') rows = rows.filter((r) => r.c.learnt);

    const field = state.clauseDbSort.field;
    const dir = state.clauseDbSort.dir === 'asc' ? 1 : -1;
    rows.sort((a, b) => {
      const va = field === 'size' ? a.c.size() : field === 'lbd' ? a.c.lbd : field === 'activity' ? a.c.activity : a.i;
      const vb = field === 'size' ? b.c.size() : field === 'lbd' ? b.c.lbd : field === 'activity' ? b.c.activity : b.i;
      return (va - vb) * dir;
    });

    const total = rows.length;
    const shown = rows.slice(0, rows.length);

    const toolbar =
      '<div class="clausedb-toolbar">' +
      '<div class="segmented segmented-sm" id="clauseFilterSeg">' +
      '<button type="button" data-filter="all" class="segmented-btn ' + (state.clauseDbFilter === 'all' ? 'active' : '') + '">All</button>' +
      '<button type="button" data-filter="original" class="segmented-btn ' + (state.clauseDbFilter === 'original' ? 'active' : '') + '">Original</button>' +
      '<button type="button" data-filter="learnt" class="segmented-btn ' + (state.clauseDbFilter === 'learnt' ? 'active' : '') + '">Learnt</button>' +
      '</div>' +
      '<label class="checkbox-label sm"><input type="checkbox" id="clauseShowDeleted" ' + (state.clauseDbShowDeleted ? 'checked' : '') + '> show deleted</label>' +
      '<span class="clausedb-count">' + total + ' clause(s)' + '</span>' +
      '</div>';

    let table =
      '<table class="clausedb-table"><thead><tr>' +
      clauseDbTh('#', 'id') +
      '<th>Literals</th><th>Type</th>' +
      clauseDbTh('Size', 'size') +
      clauseDbTh('LBD', 'lbd') +
      clauseDbTh('Activity', 'activity') +
      '<th>Status</th></tr></thead><tbody>';
    shown.forEach(({ i, c }) => {
      table +=
        '<tr class="' + (c.deleted ? 'row-deleted' : '') + ' ' + (c.learnt ? 'row-learnt' : 'row-original') + '">' +
        '<td>C' + (i + 1) + '</td>' +
        '<td class="mono clause-lits">(' + c.lits.map(SAT.fmtLit).join(' \u2228 ') + ')</td>' +
        '<td>' + (c.learnt ? '<span class="tag tag-learnt">learnt</span>' : '<span class="tag tag-original">original</span>') + '</td>' +
        '<td>' + c.size() + '</td>' +
        '<td>' + c.lbd + '</td>' +
        '<td>' + c.activity.toFixed(2) + '</td>' +
        '<td>' + (c.deleted ? 'deleted' : 'active') + '</td>' +
        '</tr>';
    });
    table += '</tbody></table>';

    host.innerHTML = toolbar + '<div class="clausedb-scroll">' + table + '</div>';

    host.querySelectorAll('.sortable').forEach((th) => {
      th.addEventListener('click', () => {
        const f = th.dataset.sortField;
        if (state.clauseDbSort.field === f) state.clauseDbSort.dir = state.clauseDbSort.dir === 'asc' ? 'desc' : 'asc';
        else state.clauseDbSort = { field: f, dir: 'asc' };
        renderClauseDB(state.solver);
      });
    });
    host.querySelectorAll('#clauseFilterSeg .segmented-btn').forEach((b) => {
      b.addEventListener('click', () => {
        state.clauseDbFilter = b.dataset.filter;
        renderClauseDB(state.solver);
      });
    });
    const cb = host.querySelector('#clauseShowDeleted');
    if (cb) cb.addEventListener('change', () => {
      state.clauseDbShowDeleted = cb.checked;
      renderClauseDB(state.solver);
    });
  }

  function renderHotVariables(solver) {
    const host = $('hotVarsHost');
    if (!solver) {
      //host.innerHTML = '<p class="empty-note">Start the solver to see live heuristic scores.</p>';
      return;
    }
    const data = solver.getHeuristicScores();
    if (data.type === 'random' || data.type === 'fixed' || !data.items.length) {
      const msg =
        data.type === 'random'
          ? 'Random heuristic \u2014 no scores are tracked; every unassigned variable is equally likely.'
          : data.type === 'fixed'
          ? 'Fixed order \u2014 variables are chosen by index, no scoring involved.'
          : 'No unassigned variables left.';
      host.innerHTML = '<p class="empty-note">' + msg + '</p>';
      return;
    }
    const top = data.items.slice(0, 12);
    let max = 1e-9;
    top.forEach((t) => (max = Math.max(max, t.score)));
    let html = '<div class="hotvar-list">';
    top.forEach((t) => {
      const pct = Math.max(4, Math.round((t.score / max) * 100));
      html +=
        '<div class="hotvar-row"><span class="hotvar-label mono">x' + t.v + '</span>' +
        '<span class="hotvar-bar-track"><span class="hotvar-bar" style="width:' + pct + '%"></span></span>' +
        '<span class="hotvar-score mono">' + t.score.toFixed(2) + '</span></div>';
    });
    html += '</div>';
    host.innerHTML = html;
  }

  function renderStats(solver) {
    const host = $('statsHost');
    if (!solver) {
      // host.innerHTML = '<p class="empty-note">No run yet.</p>';
      return;
    }
    const s = solver.stats;
    const elapsed = ((Date.now() - solver.startTime) / 1000).toFixed(2);
    const items = [
      ['Result', solver.result || 'in progress'],
      ['Decisions', s.decisions],
      ['Propagations', s.propagations],
      ['Conflicts', s.conflicts],
      ['Learned clauses', s.learned],
      ['Deleted clauses', s.deleted],
      ['Restarts', s.restarts],
      ['Current level', solver.decisionLevel],
      ['Max level reached', s.maxDecisionLevel],
      ['Elapsed', elapsed + 's'],
    ];
    host.innerHTML =
      '<div class="stats-grid">' +
      items.map(([k, v]) => '<div class="stat-cell"><span class="stat-label">' + k + '</span><span class="stat-value mono">' + v + '</span></div>').join('') +
      '</div>';
  }

  function renderImplication(solver, lastEvent) {
    const host = $('implicationHost');
    if (!solver || solver.trail.length === 0) {
      // host.innerHTML = '<div class="graph-empty">No literals assigned yet \u2014 press Step to begin.</div>';
      state.mounts.implication = null;
      return;
    }
    const result = SAT.renderImplicationGraph(host, solver, lastEvent);
    state.mounts.implication = result && result.mount ? result.mount : null;
  }

  function renderAll() {
    renderTrail(state.solver);
    renderClauseDB(state.solver);
    renderHotVariables(state.solver);
    renderStats(state.solver);
    renderImplication(state.solver, state.lastEvent);
  }

  // ---- step / run / pause / reset ---------------------------------------------------

  function doStep() {
    if (!state.parsed || !state.parsed.ok) {
      parseCurrentInput();
      if (!state.parsed.ok) return;
    }
    if (!state.solver || state.needsReinit) initSolver();
    if (!state.solver || state.solver.isDone()) return;
    const r = state.solver.step();
    state.lastEvent = r.value;
    $('lastEventText').textContent = describeEvent(state.lastEvent);
    renderAll();
    updateStatus(state.solver);
    renderResult(state.solver);
  }

  // NOTE: index.html has no #exampleSelect element — guarded.
  function setRunningControlsUI(running) {
    $('btnRun').hidden = running;
    $('btnPause').hidden = !running;
    $('btnStep').disabled = running;
    $('btnReset').disabled = running;
    document.querySelectorAll('.config-panel select, .config-panel input, .config-panel button').forEach((el) => (el.disabled = running));
    $('dimacsInput').disabled = running;
    const exSel = $('exampleSelect');
    if (exSel) exSel.disabled = running;
    if (!running) updateModeDependentControls();
  }

  async function runLoop() {
    if (!state.parsed || !state.parsed.ok) {
      parseCurrentInput();
      if (!state.parsed.ok) return;
    }
    if (!state.solver || state.needsReinit) initSolver();
    if (!state.solver || state.solver.isDone()) return;

    const myToken = ++runToken;
    state.pauseRequested = false;
    state.running = true;
    setRunningControlsUI(true);

    const batchSize = 250;
    const wallCapMs = 15000;
    const t0 = performance.now();
    let autoPaused = false;

    while (true) {
      for (let i = 0; i < batchSize; i++) {
        if (state.solver.isDone()) break;
        const r = state.solver.step();
        state.lastEvent = r.value;
      }
      $('lastEventText').textContent = describeEvent(state.lastEvent);
      renderStats(state.solver);
      updateStatus(state.solver, 'Running\u2026 ' + state.solver.stats.decisions + ' decisions, ' + state.solver.stats.conflicts + ' conflicts so far');
      if (state.solver.isDone()) break;
      if (state.pauseRequested) break;
      if (performance.now() - t0 > wallCapMs) {
        autoPaused = true;
        break;
      }
      await new Promise((res) => setTimeout(res, 0));
      if (myToken !== runToken) return; // superseded by reset/new input mid-flight
    }

    state.running = false;
    setRunningControlsUI(false);
    renderAll();
    renderResult(state.solver);
    if (state.solver.isDone()) {
      updateStatus(state.solver);
    } else if (autoPaused) {
      updateStatus(state.solver, 'Paused automatically after 15s \u2014 press Run to keep searching.');
    } else {
      updateStatus(state.solver, 'Paused \u2014 press Run to continue.');
    }
  }

  function doReset() {
    if (state.running) return;
    runToken++; // invalidate any in-flight loop just in case
    state.solver = null;
    state.lastEvent = null;
    if (state.parsed && state.parsed.ok) initSolver();
    else {
      renderAll();
      updateStatus(null);
      renderResult(null);
    }
    $('lastEventText').textContent = '';
  }

  // ---- wiring -------------------------------------------------------------------------

  // NOTE: index.html has no #btnDownloadCnf element — guarded.
  function wireInputPanel() {
    $('dimacsInput').addEventListener('input', parseCurrentInput);
    $('btnGenVCG').addEventListener('click', () => showStructuralGraph('vcg'));
    $('btnGenVIG').addEventListener('click', () => showStructuralGraph('vig'));
    document.querySelectorAll('.graph-tab').forEach((b) => b.addEventListener('click', () => showStructuralGraph(b.dataset.graph)));
    const dl = $('btnDownloadCnf');
    if (dl) {
      dl.addEventListener('click', () => {
        const text = $('dimacsInput').value;
        const blob = new Blob([text], { type: 'text/plain' });
        const url = URL.createObjectURL(blob);
        const a = document.createElement('a');
        a.href = url;
        a.download = 'formula.cnf';
        document.body.appendChild(a);
        a.click();
        document.body.removeChild(a);
        URL.revokeObjectURL(url);
      });
    }
  }

  function wireConfigPanel() {
    document.querySelectorAll('#modeSegmented .segmented-btn').forEach((btn) => {
      btn.addEventListener('click', () => {
        if (state.running) return;
        document.querySelectorAll('#modeSegmented .segmented-btn').forEach((b) => b.classList.remove('active'));
        btn.classList.add('active');
        state.mode = btn.dataset.value;
        state.needsReinit = true;
        dropStaleSolver();
        updateModeDependentControls();
      });
    });
    $('heuristicSelect').addEventListener('change', updateVsidsDpllNote);
    $('restartSelect').addEventListener('change', () => updateHints());
    $('deletionSelect').addEventListener('change', () => updateHints());
    document.querySelector('.config-panel').addEventListener('change', () => {
      state.needsReinit = true;
      dropStaleSolver();
      updateHints();
    });
    document.querySelector('.config-panel').addEventListener('input', (e) => {
      if (e.target.type === 'number') {
        state.needsReinit = true;
        dropStaleSolver();
      }
    });
  }

  function wireExecutePanel() {
    $('btnStep').addEventListener('click', doStep);
    $('btnRun').addEventListener('click', runLoop);
    $('btnPause').addEventListener('click', () => {
      state.pauseRequested = true;
    });
    $('btnReset').addEventListener('click', doReset);
  }

  function wireZoomControls() {
    document.addEventListener('click', (e) => {
      const btn = e.target.closest('.zoom-btn');
      if (!btn) return;
      const target = btn.dataset.zoomTarget || 'structural';
      const mount = state.mounts[target];
      if (!mount) return;
      const action = btn.dataset.zoom;
      if (action === 'in') mount.zoomBy(1.25);
      else if (action === 'out') mount.zoomBy(0.8);
      else mount.resetView();
    });
  }

  function wireKeyboardShortcut() {
    document.addEventListener('keydown', (e) => {
      if (e.code !== 'Space') return;
      const tag = (document.activeElement && document.activeElement.tagName) || '';
      if (tag === 'TEXTAREA' || tag === 'INPUT' || tag === 'SELECT' || tag === 'BUTTON') return;
      if (state.running) return;
      e.preventDefault();
      doStep();
    });
  }

  // Receive DIMACS content posted from the book's DemoSAT click handler.
  function wirePostMessage() {
    window.addEventListener('message', (e) => {
      if (typeof e.data !== 'string' || state.running) return;
      $('dimacsInput').value = e.data;
      parseCurrentInput();
      $('dimacsInput').scrollTop = 0;
      $('dimacsInput').focus();
    });
    // Signal to the opener that the sandbox is ready to receive content.
    if (window.opener) window.opener.postMessage('ready', '*');
  }

  function init() {
    wireInputPanel();
    wireConfigPanel();
    wireExecutePanel();
    wireZoomControls();
    wireKeyboardShortcut();
    wirePostMessage();
    updateHints();
    updateModeDependentControls();
    renderImplicationLegend();
    renderAll();
    updateStatus(null);
    renderResult(null);
  }

  init();
})();