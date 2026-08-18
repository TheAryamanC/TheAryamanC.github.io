/**
 * graphRender.js — hand-rolled SVG rendering for the three graphs the
 * sandbox shows: the VCG and VIG (structural, force-directed) and the
 * implication graph (dynamic, laid out in columns by decision level).
 * No external graphing library — this keeps the whole site a handful of
 * static files that work straight off GitHub Pages.
 */
(function (global) {
  'use strict';

  const SVGNS = 'http://www.w3.org/2000/svg';
  const U = global.SAT;

  function svgEl(name, attrs) {
    const el = document.createElementNS(SVGNS, name);
    if (attrs) {
      for (const k in attrs) {
        if (attrs[k] !== undefined && attrs[k] !== null) el.setAttribute(k, attrs[k]);
      }
    }
    return el;
  }

  // ---- force-directed layout (Fruchterman–Reingold style) --------------------

  function forceLayout(nodes, edges, opts) {
    opts = opts || {};
    const width = opts.width || 900;
    const height = opts.height || 560;
    const iterations = opts.iterations || Math.min(300, Math.max(60, Math.round(18000 / Math.max(1, nodes.length))));
    const k = (Math.sqrt((width * height) / Math.max(1, nodes.length))) * (opts.kScale || 1.1);
    const rng = U.mulberry32(opts.seed || 7);

    const pos = {};
    nodes.forEach((n, i) => {
      const angle = (i / nodes.length) * Math.PI * 2;
      const r = Math.min(width, height) * 0.36;
      pos[n.id] = {
        x: width / 2 + Math.cos(angle) * r + (rng() - 0.5) * 12,
        y: height / 2 + Math.sin(angle) * r + (rng() - 0.5) * 12,
      };
    });

    const disp = {};
    for (let iter = 0; iter < iterations; iter++) {
      nodes.forEach((n) => (disp[n.id] = { x: 0, y: 0 }));

      for (let i = 0; i < nodes.length; i++) {
        for (let j = i + 1; j < nodes.length; j++) {
          const a = nodes[i].id;
          const b = nodes[j].id;
          let dx = pos[a].x - pos[b].x;
          let dy = pos[a].y - pos[b].y;
          let dist = Math.sqrt(dx * dx + dy * dy) || 0.01;
          const force = (k * k) / dist;
          dx /= dist;
          dy /= dist;
          disp[a].x += dx * force;
          disp[a].y += dy * force;
          disp[b].x -= dx * force;
          disp[b].y -= dy * force;
        }
      }

      edges.forEach((e) => {
        const a = pos[e.source];
        const b = pos[e.target];
        if (!a || !b) return;
        let dx = a.x - b.x;
        let dy = a.y - b.y;
        let dist = Math.sqrt(dx * dx + dy * dy) || 0.01;
        const force = (dist * dist) / k;
        dx /= dist;
        dy /= dist;
        disp[e.source].x -= dx * force;
        disp[e.source].y -= dy * force;
        disp[e.target].x += dx * force;
        disp[e.target].y += dy * force;
      });

      const temp = width * 0.08 * (1 - iter / iterations);
      nodes.forEach((n) => {
        const d = disp[n.id];
        const dist = Math.sqrt(d.x * d.x + d.y * d.y) || 0.01;
        const lim = Math.min(dist, Math.max(temp, 0.5));
        pos[n.id].x = U.clamp(pos[n.id].x + (d.x / dist) * lim, 24, width - 24);
        pos[n.id].y = U.clamp(pos[n.id].y + (d.y / dist) * lim, 24, height - 24);
      });
    }
    return pos;
  }

  // ---- shared pannable / zoomable SVG mount -----------------------------------

  function mountZoomableSVG(container, width, height) {
    container.innerHTML = '';
    const svg = svgEl('svg', {
      viewBox: '0 0 ' + width + ' ' + height,
      class: 'graph-svg',
      preserveAspectRatio: 'xMidYMid meet',
    });
    svg.style.touchAction = 'none';

    const defs = svgEl('defs');
    const gid = 'grid-' + Math.random().toString(36).slice(2, 9);
    const pattern = svgEl('pattern', { id: gid, width: 22, height: 22, patternUnits: 'userSpaceOnUse' });
    pattern.appendChild(svgEl('path', { d: 'M 22 0 L 0 0 0 22', class: 'grid-line' }));
    defs.appendChild(pattern);

    const mid = 'arrow-' + Math.random().toString(36).slice(2, 9);
    const marker = svgEl('marker', {
      id: mid,
      viewBox: '0 0 10 10',
      refX: 8.5,
      refY: 5,
      markerWidth: 6.5,
      markerHeight: 6.5,
      orient: 'auto-start-reverse',
    });
    marker.appendChild(svgEl('path', { d: 'M0,0 L10,5 L0,10 z', class: 'arrow-head' }));
    defs.appendChild(marker);
    svg.appendChild(defs);

    const bg = svgEl('rect', { x: 0, y: 0, width, height, fill: 'url(#' + gid + ')', class: 'graph-bg' });
    svg.appendChild(bg);

    const content = svgEl('g', { class: 'graph-content' });
    svg.appendChild(content);
    container.appendChild(svg);

    let tx = 0;
    let ty = 0;
    let scale = 1;
    function apply() {
      content.setAttribute('transform', 'translate(' + tx + ',' + ty + ') scale(' + scale + ')');
    }

    let dragging = false;
    let lastX = 0;
    let lastY = 0;
    svg.addEventListener('pointerdown', (e) => {
      dragging = true;
      lastX = e.clientX;
      lastY = e.clientY;
      svg.setPointerCapture(e.pointerId);
      svg.classList.add('dragging');
    });
    svg.addEventListener('pointermove', (e) => {
      if (!dragging) return;
      const rect = svg.getBoundingClientRect();
      const sx = width / rect.width;
      const sy = height / rect.height;
      tx += (e.clientX - lastX) * sx;
      ty += (e.clientY - lastY) * sy;
      lastX = e.clientX;
      lastY = e.clientY;
      apply();
    });
    function endDrag() {
      dragging = false;
      svg.classList.remove('dragging');
    }
    svg.addEventListener('pointerup', endDrag);
    svg.addEventListener('pointercancel', endDrag);
    svg.addEventListener('pointerleave', endDrag);
    svg.addEventListener(
      'wheel',
      (e) => {
        e.preventDefault();
        const rect = svg.getBoundingClientRect();
        const mx = (e.clientX - rect.left) * (width / rect.width);
        const my = (e.clientY - rect.top) * (height / rect.height);
        const factor = e.deltaY > 0 ? 0.88 : 1.13;
        const newScale = U.clamp(scale * factor, 0.15, 4.5);
        tx = mx - (mx - tx) * (newScale / scale);
        ty = my - (my - ty) * (newScale / scale);
        scale = newScale;
        apply();
      },
      { passive: false }
    );

    function resetView() {
      tx = 0;
      ty = 0;
      scale = 1;
      apply();
    }
    function zoomBy(factor) {
      const cx = width / 2;
      const cy = height / 2;
      const newScale = U.clamp(scale * factor, 0.15, 4.5);
      tx = cx - (cx - tx) * (newScale / scale);
      ty = cy - (cy - ty) * (newScale / scale);
      scale = newScale;
      apply();
    }

    return { svg, content, resetView, zoomBy, markerId: mid };
  }

  function drawEdge(content, a, b, opts) {
    opts = opts || {};
    const line = svgEl('line', { x1: a.x, y1: a.y, x2: b.x, y2: b.y });
    line.setAttribute('class', 'edge ' + (opts.className || ''));
    if (opts.dashed) line.setAttribute('stroke-dasharray', '5 4');
    if (opts.width) line.setAttribute('stroke-width', opts.width);
    if (opts.marker) line.setAttribute('marker-end', 'url(#' + opts.marker + ')');
    content.appendChild(line);
    return line;
  }

  // ---- VCG / VIG (structural graphs of the input formula) --------------------

  function renderStructuralGraph(container, kind, formula, opts) {
    opts = opts || {};
    const width = opts.width || 900;
    const height = opts.height || 560;
    const data = kind === 'vcg' ? U.buildVCG(formula) : U.buildVIG(formula);
    const large = data.nodes.length > 350;

    const pos = forceLayout(data.nodes, data.edges, { width, height, seed: opts.seed || 7 });
    const mount = mountZoomableSVG(container, width, height);
    const { content, markerId } = mount;

    data.edges.forEach((e) => {
      const a = pos[e.source];
      const b = pos[e.target];
      if (!a || !b) return;
      if (kind === 'vcg') {
        drawEdge(content, a, b, {
          className: e.positive ? 'edge-pos' : 'edge-neg',
          dashed: !e.positive,
        });
      } else {
        const w = Math.min(5.5, 1 + (e.weight || 1) * 0.55);
        drawEdge(content, a, b, { className: 'edge-vig', width: w });
      }
    });

    data.nodes.forEach((n) => {
      const p = pos[n.id];
      if (!p) return;
      const g = svgEl('g', { class: 'node node-' + n.type, transform: 'translate(' + p.x + ',' + p.y + ')' });
      if (n.type === 'var') {
        g.appendChild(svgEl('circle', { r: 13, class: 'node-shape node-var-shape' }));
      } else {
        const s = 12;
        g.appendChild(svgEl('rect', { x: -s, y: -s, width: s * 2, height: s * 2, rx: 2, class: 'node-shape node-clause-shape' }));
      }
      const label = svgEl('text', { class: 'node-label', 'text-anchor': 'middle', dy: '0.32em' });
      label.textContent = n.label;
      g.appendChild(label);
      content.appendChild(g);
    });

    void markerId;
    return { mount, nodeCount: data.nodes.length, edgeCount: data.edges.length, large };
  }

  function renderVCG(container, formula, opts) {
    return renderStructuralGraph(container, 'vcg', formula, opts);
  }
  function renderVIG(container, formula, opts) {
    return renderStructuralGraph(container, 'vig', formula, opts);
  }

  // ---- implication graph (dynamic, per solver step) ---------------------------

  function buildImplicationGraphData(solver, lastEvent) {
    const nodes = [];
    const nodeByVar = {};
    const byLevel = {};
    solver.trail.forEach((lit) => {
      const v = lit < 0 ? -lit : lit;
      const lvl = solver.level[v];
      const r = solver.reason[v];
      const isDecision = r === null || r === undefined;
      const n = { id: 'n' + v, v, lit, level: lvl, isDecision, reason: r };
      nodes.push(n);
      nodeByVar[v] = n;
      (byLevel[lvl] = byLevel[lvl] || []).push(n);
    });

    const edges = [];
    solver.trail.forEach((lit) => {
      const v = lit < 0 ? -lit : lit;
      const r = solver.reason[v];
      if (r === null || r === undefined) return;
      const clause = solver.formula.clauses[r];
      if (!clause) return;
      clause.lits.forEach((l) => {
        const ov = l < 0 ? -l : l;
        if (ov === v) return;
        if (nodeByVar[ov]) edges.push({ source: 'n' + ov, target: 'n' + v });
      });
    });

    let conflictNode = null;
    let conflictEdges = [];
    if (lastEvent && lastEvent.type === 'conflict' && solver.formula.clauses[lastEvent.clause]) {
      const c = solver.formula.clauses[lastEvent.clause];
      conflictNode = { id: 'CONFLICT', level: solver.decisionLevel };
      c.lits.forEach((l) => {
        const ov = l < 0 ? -l : l;
        if (nodeByVar[ov]) conflictEdges.push({ source: 'n' + ov, target: 'CONFLICT' });
      });
    }

    return { nodes, edges, byLevel, conflictNode, conflictEdges, nodeByVar };
  }

  function layoutImplicationGraph(data) {
    const colWidth = 148;
    const rowHeight = 54;
    const marginX = 60;
    const marginY = 46;
    const levels = Object.keys(data.byLevel)
      .map(Number)
      .sort((a, b) => a - b);
    const pos = {};
    let maxRows = 1;
    levels.forEach((lvl) => {
      const list = data.byLevel[lvl];
      list.forEach((n, i) => {
        pos[n.id] = { x: marginX + lvl * colWidth, y: marginY + i * rowHeight };
      });
      maxRows = Math.max(maxRows, list.length);
    });
    const maxLevel = levels.length ? Math.max.apply(null, levels) : 0;
    if (data.conflictNode) {
      const lvl = data.conflictNode.level;
      const list = data.byLevel[lvl] || [];
      pos[data.conflictNode.id] = {
        x: marginX + (lvl + 0.85) * colWidth,
        y: marginY + Math.max(0, list.length - 1) * rowHeight * 0.5 + rowHeight * 0.5,
      };
    }
    const width = marginX * 2 + (maxLevel + 1.7) * colWidth;
    const height = marginY * 2 + Math.max(maxRows, 1) * rowHeight;
    return { pos, width: Math.max(width, 360), height: Math.max(height, 260), levels };
  }

  function renderImplicationGraph(container, solver, lastEvent) {
    const data = buildImplicationGraphData(solver, lastEvent);
    if (data.nodes.length === 0) {
      container.innerHTML = '<div class="graph-empty">No literals assigned yet — press Step to begin.</div>';
      return { empty: true };
    }
    const layout = layoutImplicationGraph(data);
    const mount = mountZoomableSVG(container, layout.width, layout.height);
    const { content, markerId } = mount;

    // Column headers
    layout.levels.forEach((lvl) => {
      const x = 60 + lvl * 148;
      const t = svgEl('text', { x, y: 20, class: 'level-header' });
      t.textContent = lvl === 0 ? 'LEVEL 0 (forced)' : 'LEVEL ' + lvl;
      content.appendChild(t);
    });

    data.edges.forEach((e) => {
      const a = layout.pos[e.source];
      const b = layout.pos[e.target];
      if (!a || !b) return;
      drawEdge(content, a, b, { className: 'edge-implication', marker: markerId });
    });
    data.conflictEdges.forEach((e) => {
      const a = layout.pos[e.source];
      const b = layout.pos[e.target];
      if (!a || !b) return;
      drawEdge(content, a, b, { className: 'edge-conflict', marker: markerId });
    });

    data.nodes.forEach((n) => {
      const p = layout.pos[n.id];
      if (!p) return;
      const isTrue = n.lit > 0;
      const isCurrent = lastEvent && lastEvent.lit !== undefined && Math.abs(lastEvent.lit) === n.v;
      const cls = ['node', 'node-impl', n.isDecision ? 'node-decision' : 'node-propagated', isTrue ? 'val-true' : 'val-false'];
      if (isCurrent) cls.push('node-current');
      const g = svgEl('g', { class: cls.join(' '), transform: 'translate(' + p.x + ',' + p.y + ')' });
      if (n.isDecision) {
        g.appendChild(svgEl('rect', { x: -14, y: -14, width: 28, height: 28, class: 'node-shape node-decision-shape', transform: 'rotate(45)' }));
      } else {
        g.appendChild(svgEl('circle', { r: 15, class: 'node-shape node-impl-shape' }));
      }
      const label = svgEl('text', { class: 'node-label', 'text-anchor': 'middle', dy: '0.32em' });
      label.textContent = (n.lit < 0 ? '\u00ac' : '') + 'x' + n.v;
      g.appendChild(label);
      const sub = svgEl('text', { class: 'node-sublabel', 'text-anchor': 'middle', y: 26 });
      sub.textContent = n.isDecision ? 'decision' : 'C' + (n.reason + 1);
      g.appendChild(sub);
      content.appendChild(g);
    });

    if (data.conflictNode) {
      const p = layout.pos[data.conflictNode.id];
      const g = svgEl('g', { class: 'node node-conflict', transform: 'translate(' + p.x + ',' + p.y + ')' });
      g.appendChild(svgEl('circle', { r: 17, class: 'node-shape node-conflict-shape' }));
      const label = svgEl('text', { class: 'node-label node-conflict-label', 'text-anchor': 'middle', dy: '0.32em' });
      label.textContent = '\u22a5';
      g.appendChild(label);
      content.appendChild(g);
    }

    return { mount, nodeCount: data.nodes.length };
  }

  const ns = { forceLayout, mountZoomableSVG, renderVCG, renderVIG, renderImplicationGraph, buildImplicationGraphData };

  global.SAT = global.SAT || {};
  Object.assign(global.SAT, ns);

  if (typeof module !== 'undefined' && module.exports) {
    module.exports = ns;
  }
})(typeof window !== 'undefined' ? window : globalThis);
