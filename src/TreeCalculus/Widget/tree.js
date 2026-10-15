// Copyright (c) 2026 Aron Adler. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.

import * as React from 'react';
import { useRpcSession } from '@leanprover/infoview';

const h = React.createElement;
const redexColour = '#f5a000';
const previewColour = 'var(--vscode-textLink-foreground, #3794ff)';
const errorColour = 'var(--vscode-errorForeground, #f48771)';
const neutral = 'var(--vscode-editor-foreground, #eeeeee)';
const border = 'var(--vscode-widget-border, #7776)';
const runLimit = 1000;
const nodeLimit = 20000;
const playDelay = 400;

// A leaf occupies one horizontal slot; parents sit between their outer children.
// Keep this iterative so long stems do not exhaust the JavaScript call stack.
export function layoutTree(tree, redexRules) {
  const nodes = [];
  const pending = [{ tree, parent: -1, depth: 0, childIndex: 0 }];
  let leaves = 0;
  let depth = 0;
  while (pending.length) {
    const item = pending.pop();
    const id = nodes.length;
    const node = { ...item, id, rule: redexRules[id] || null, children: [], size: 1, x: 0, y: item.depth * 44 };
    nodes.push(node);
    if (item.parent >= 0) nodes[item.parent].children.push(id);
    depth = Math.max(depth, item.depth);
    if (item.tree.length === 0) node.x = leaves++ * 38;
    for (let i = item.tree.length - 1; i >= 0; i--)
      pending.push({ tree: item.tree[i], parent: id, depth: item.depth + 1, childIndex: i });
  }
  for (let i = nodes.length - 1; i >= 0; i--) {
    const n = nodes[i];
    if (n.children.length) {
      n.x = (nodes[n.children[0]].x + nodes[n.children.at(-1)].x) / 2;
      n.size += n.children.reduce((sum, id) => sum + nodes[id].size, 0);
    }
  }
  return { nodes, width: Math.max(24, (leaves - 1) * 38 + 24), height: depth * 44 + 24 };
}

function pathOf(nodes, node) {
  const path = [];
  while (node.parent >= 0) {
    path.push(node.childIndex);
    node = nodes[node.parent];
  }
  return path.reverse();
}
const pathLabel = path => ['root', ...path.map(i => i + 1)].join('.');

function idAtPath(nodes, path) {
  let id = 0;
  for (const i of path) id = nodes[id]?.children[i];
  return id ?? null;
}

// Flat tokens share the diagram's preorder node IDs. Keeping every token lets
// every graph node have an expression counterpart, including in large terms.
export function expressionTokens(nodes) {
  const stack = [0];
  const tokens = [];
  while (stack.length) {
    const item = stack.pop();
    if (typeof item !== 'number') { tokens.push(item); continue; }
    const node = nodes[item];
    tokens.push({ text: '△', nodeId: item });
    for (let i = node.children.length - 1; i >= 0; i--) {
      const child = node.children[i];
      if (nodes[child].children.length) {
        stack.push({ text: ')', nodeId: child }, child, { text: '(', nodeId: child },
          { text: ' ⬝ ', nodeId: item });
      } else stack.push(child, { text: ' ⬝ ', nodeId: item });
    }
  }
  return tokens;
}

// Stepping state lives outside the component, one session per term: the
// infoview remounts the message under the cursor whenever the cursor moves,
// and "Messages" and "All Messages" can show the same term at once. Every view
// of a term renders the same session, and only the session drives playback.
// The infoview loads a separate instance of this module for each panel that
// mounts while the module is still loading, so sessions hang off the window
// rather than module scope. Bump the key's version if the session shape changes.
const sessions = globalThis[Symbol.for('boom.treeCalculus.sessions.v1')] ??= new Map();

function useSession(key, initial, rs) {
  let session = sessions.get(key);
  if (!session) {
    session = { history: [initial()], playing: false, busy: false, error: null, timer: null,
      listeners: new Set() };
    sessions.set(key, session);
  }
  // Any live view's RPC session can serve requests; the latest one is used.
  session.rs = rs;
  const [, rerender] = React.useReducer(n => n + 1, 0);
  React.useEffect(() => {
    session.listeners.add(rerender);
    return () => { session.listeners.delete(rerender); };
  }, [session]);
  return session;
}

function update(session, patch) {
  Object.assign(session, patch);
  session.listeners.forEach(listener => listener());
}

// Results are dropped if the history changed while the request was in flight.
async function request(session, method, params, entry) {
  const from = session.history.at(-1);
  update(session, { busy: true, error: null });
  try {
    const next = entry(await session.rs.call(method, { tree: from.tree, ...params }), from);
    if (next && session.history.at(-1) === from) update(session, { history: [...session.history, next] });
  } catch (e) {
    update(session, { error: e?.message ?? String(e), playing: false });
  } finally {
    update(session, { busy: false });
  }
}

const step = (session, path) => request(session, 'Term.stepRpc', { path }, (r, from) =>
  ({ tree: r.tree, redexRules: r.redexRules, path: r.path, rule: r.rule, steps: from.steps + 1 }));

const run = session => request(session, 'Term.runRpc', { maxSteps: runLimit, maxNodes: nodeLimit },
  (r, from) => r.steps && { tree: r.tree, redexRules: r.redexRules, ran: r.steps, steps: from.steps + r.steps });

// Playback stops at normal form, at the node limit, or when no view is left.
function play(session) {
  clearTimeout(session.timer);
  if (!session.playing) return;
  const { redexRules } = session.history.at(-1);
  if (!redexRules.some(Boolean) || redexRules.length > nodeLimit || !session.listeners.size) {
    update(session, { playing: false });
    return;
  }
  session.timer = setTimeout(async () => { await step(session, null); play(session); }, playDelay);
}

function setPlaying(session, playing) {
  update(session, { playing });
  play(session);
}

function rewind(session, length) {
  clearTimeout(session.timer);
  update(session, { playing: false, error: null, history: session.history.slice(0, length) });
}

const shape = n => ['leaf', 'stem', 'fork'][n.children.length] ?? `${n.children.length} arguments`;

const popover = { position: 'absolute', zIndex: 2, padding: '6px 9px', fontSize: 12, lineHeight: 1.45,
  borderRadius: 6, color: neutral, fontWeight: 'normal', textAlign: 'left',
  background: 'var(--vscode-editorHoverWidget-background, #252526)',
  border: '1px solid var(--vscode-editorHoverWidget-border, #454545)', boxShadow: '0 2px 8px #0006' };

// Native titles are slow to appear and easy to miss, so buttons get their own.
// CSS anchor positioning centres a tip under its control and, via
// anchor-center, slides it back inside the widget when it would overflow.
function Tip({ text, width, children }) {
  const [open, setOpen] = React.useState(false);
  const anchor = `--boom-tip-${React.useId().replace(/[^\w-]/g, '')}`;
  return h('span', { style: { display: 'inline-flex', anchorName: anchor },
    onPointerEnter: () => setOpen(true), onPointerLeave: () => setOpen(false),
    onFocus: () => setOpen(true), onBlur: () => setOpen(false) },
    children,
    open && h('span', { role: 'tooltip', style: { ...popover, positionAnchor: anchor,
      positionArea: 'bottom span-all', justifySelf: 'anchor-center', margin: '6px 4px 0',
      width: width ?? 'max-content', maxWidth: 260, pointerEvents: 'none' } }, text));
}

// Signals that the view is changing by itself. It holds still for anyone who
// prefers reduced motion.
const spinnerCss = '@keyframes boom-tree-spin { to { transform: rotate(360deg) } }'
  + '@media (prefers-reduced-motion: reduce) { .boom-tree-spin { animation: none !important } }';
const spinner = h(React.Fragment, null, h('style', null, spinnerCss),
  h('span', { className: 'boom-tree-spin', 'aria-hidden': true, style: { display: 'inline-block',
    width: 8, height: 8, marginRight: 6, verticalAlign: -1, borderRadius: '50%',
    border: '2px solid currentColor', borderRightColor: 'transparent',
    animation: 'boom-tree-spin 0.8s linear infinite' } }));

// Disabled buttons swallow pointer events in some browsers; let them reach the tooltip.
function Button({ label, tip, onClick, disabled, children, style }) {
  return h(Tip, { text: tip },
    h('button', { type: 'button', 'aria-label': label, disabled, onClick,
      style: { cursor: 'pointer', color: 'inherit', opacity: disabled ? 0.35 : 1,
        pointerEvents: disabled ? 'none' : undefined,
        background: 'var(--vscode-editor-background, #111111)', border: `1px solid ${border}`,
        borderRadius: 4, padding: '2px 8px', minWidth: 26, font: 'inherit', fontSize: 12, ...style } },
      children));
}

function Help() {
  const line = text => h('div', { style: { marginTop: 4 } }, text);
  return h(Tip, { width: 270, text: h(React.Fragment, null,
    h('div', null, h('span', { style: { color: redexColour } }, '●'),
      ' A rewrite rule fires here. Click it to apply the rule.'),
    line('Every step is computed in Lean by Term.rewriteAt?, which is proved sound.'),
    line('Stepping is a preview: the Lean term is unchanged.'),
    line('Hover the tree or expression to link the two.')) },
    h('span', { tabIndex: 0, role: 'button', 'aria-label': 'Help',
      style: { cursor: 'help', opacity: 0.6, fontSize: 14 } }, 'ⓘ'));
}

export default function TreeWidget({ tree, label, redexRules }) {
  const rs = useRpcSession();
  const key = React.useMemo(() => `${label}\u0000${JSON.stringify(tree)}`, [tree, label]);
  // history[0] is the term itself; later entries record the step that made them.
  const session = useSession(key, () => ({ tree, redexRules, steps: 0 }), rs);
  const { history, playing, busy, error } = session;
  const current = history.at(-1);
  const layout = React.useMemo(() => layoutTree(current.tree, current.redexRules), [current]);
  const { nodes } = layout;
  const tokens = React.useMemo(() => expressionTokens(nodes), [nodes]);
  const host = React.useRef(null);
  const expression = React.useRef(null);
  const drag = React.useRef(null);
  const [width, setWidth] = React.useState(480);
  const [camera, setCamera] = React.useState(null);
  const [hovered, setHovered] = React.useState(null);
  React.useEffect(() => {
    const observer = new ResizeObserver(entries => setWidth(Math.max(160, entries[0].contentRect.width)));
    observer.observe(host.current);
    return () => observer.disconnect();
  }, []);
  React.useEffect(() => { setCamera(null); setHovered(null); }, [key]);
  React.useEffect(() => setHovered(null), [current]);

  const previewing = history.length > 1;
  const redexCount = nodes.filter(n => n.rule).length;
  const changed = current.path ? idAtPath(nodes, current.path) : null;

  const height = Math.max(210, Math.min(520, layout.height + 56));
  const fitScale = Math.min(1, (width - 48) / layout.width, (height - 48) / layout.height);
  const fit = { scale: fitScale, x: (width - (layout.width - 24) * fitScale) / 2,
    y: (height - (layout.height - 24) * fitScale) / 2 };
  const view = camera || fit;
  const highlighted = hovered === null ? null : nodes[hovered];
  const colour = n => n.rule ? redexColour : neutral;
  const inHighlight = id => highlighted && id >= highlighted.id && id < highlighted.id + highlighted.size;
  const opacity = n => !highlighted || inHighlight(n.id) ? 1 : 0.22;

  // When a graph node is hovered, reveal its triangle in the expression's
  // scroll area. Scroll only this local area, never the enclosing infoview.
  function hoverGraph(id) {
    setHovered(id);
    const area = expression.current;
    const token = area?.querySelector(`[data-tree-triangle="${id}"]`);
    if (token) {
      const a = area.getBoundingClientRect(), b = token.getBoundingClientRect();
      if (b.top < a.top) area.scrollTop += b.top - a.top;
      else if (b.bottom > a.bottom) area.scrollTop += b.bottom - a.bottom;
    }
  }
  const tokenId = e => {
    const span = e.target.closest('[data-tree-expr-node]');
    return span ? Number(span.dataset.treeExprNode) : null;
  };
  const activate = id => {
    if (busy || !nodes[id]?.rule) return;
    setPlaying(session, false);
    step(session, pathOf(nodes, nodes[id]));
  };

  function zoom(factor, cx = width / 2, cy = height / 2) {
    const scale = Math.max(0.02, Math.min(6, view.scale * factor));
    const ratio = scale / view.scale;
    setCamera({ scale, x: cx - (cx - view.x) * ratio, y: cy - (cy - view.y) * ratio });
  }

  const describe = n => [pathLabel(pathOf(nodes, n)), shape(n), `${n.size} nodes`].join(' · ');
  const remaining = redexCount ? `${redexCount} ${redexCount === 1 ? 'redex' : 'redexes'}` : 'normal form';
  const status = [
    previewing ? `step ${current.steps}` : 'Original',
    previewing && (current.ran ? `ran ${current.ran}` : `rule ${current.rule} at ${pathLabel(current.path)}`),
    remaining,
    current.ran && redexCount && 'hit step limit',
  ].filter(Boolean).join(' · ');
  const normal = 'Already in normal form';

  return h('section', { ref: host, style: { position: 'relative', color: neutral, margin: '8px 0', borderRadius: 8,
    border: previewing ? `1px solid ${previewColour}` : `1px solid ${border}`,
    boxShadow: previewing ? `0 0 0 1px ${previewColour}` : undefined } },
    h('div', { style: { display: 'flex', alignItems: 'baseline', gap: 10, padding: '9px 12px' } },
      h('code', { style: { flex: 1, overflowWrap: 'anywhere', lineHeight: 1.5, fontSize: 12 } }, label),
      h('span', { style: { opacity: 0.6, fontSize: 12, whiteSpace: 'nowrap' } }, `${nodes.length} nodes`),
      h(Help)),
    // Controls sit above the canvas so a growing tree never moves them, and
    // the status is a single line so a long status never reflows them either.
    h('div', { style: { padding: '7px 12px', fontSize: 12, borderTop: `1px solid ${previewing ? previewColour : border}`,
      borderBottom: `1px solid ${previewing ? previewColour : border}`,
      background: previewing ? 'color-mix(in srgb, var(--vscode-textLink-foreground, #3794ff) 12%, transparent)' : undefined } },
      h('div', { style: { display: 'flex', flexWrap: 'wrap', gap: 6 } },
        h(Button, { label: 'Reset', disabled: !previewing, onClick: () => rewind(session, 1),
          tip: previewing ? 'Discard all steps and show the original term' : 'Showing the original term',
          style: previewing ? { borderColor: previewColour, color: previewColour } : undefined }, '↺ Reset'),
        h(Button, { label: 'Undo', disabled: !previewing || busy, onClick: () => rewind(session, history.length - 1),
          tip: current.ran ? `Undo the previous run (${current.ran} steps)` : 'Undo the previous step' }, '↶ Undo'),
        h('span', { style: { width: 6 } }),
        h(Button, { label: 'Step', disabled: !redexCount || busy || playing, onClick: () => step(session, null),
          tip: redexCount ? 'Rewrite the leftmost-outermost redex' : normal }, 'Step'),
        h(Button, { label: playing ? 'Pause' : 'Play', disabled: !redexCount && !playing,
          onClick: () => setPlaying(session, !playing),
          tip: playing ? 'Pause' : redexCount ? 'Keep stepping automatically' : normal,
          style: playing ? { background: previewColour, borderColor: previewColour,
            color: 'var(--vscode-editor-background, #111111)' } : undefined },
          playing ? '⏸︎' : '▶︎'),
        h(Button, { label: 'Run', disabled: !redexCount || busy || playing, onClick: () => run(session),
          tip: redexCount ? `Run up to ${runLimit} steps at once, stopping early at normal form. `
            + 'Press again to keep going.' : normal }, '⏭︎')),
      h('div', { title: error ?? status, style: { marginTop: 6, whiteSpace: 'nowrap', overflow: 'hidden',
        textOverflow: 'ellipsis', color: error ? errorColour : previewing || playing ? previewColour : undefined,
        opacity: error || previewing || playing ? 1 : 0.7 } },
        error ?? h(React.Fragment, null, playing && spinner,
          (playing || previewing) && h('strong', null, playing ? 'Playing · ' : 'Preview · '), status))),
    // Overlays share the canvas's grid cell rather than being positioned, so
    // the widget stays the containing block that tooltips are kept inside.
    h('div', { style: { display: 'grid' } },
      h('svg', { width: '100%', height, viewBox: `0 0 ${width} ${height}`,
        role: 'img', 'aria-label': `Tree of ${label}, ${nodes.length} nodes. Children are ordered left to right.`,
        style: { gridArea: '1 / 1', display: 'block', background: 'var(--vscode-editor-background, #111111)', touchAction: 'none',
          cursor: highlighted?.rule && !busy ? 'pointer' : 'grab', userSelect: 'none' },
        onPointerDown: e => {
          if (e.button !== 0) return;
          drag.current = { x: e.clientX, y: e.clientY, view, moved: false };
          e.currentTarget.setPointerCapture(e.pointerId);
        },
        onPointerMove: e => {
          const d = drag.current;
          if (!d) return;
          const dx = e.clientX - d.x, dy = e.clientY - d.y;
          if (Math.abs(dx) + Math.abs(dy) > 3) d.moved = true;
          if (d.moved) setCamera({ ...d.view, x: d.view.x + dx, y: d.view.y + dy });
        },
        onPointerUp: e => {
          const d = drag.current;
          drag.current = null;
          e.currentTarget.releasePointerCapture(e.pointerId);
          if (d && !d.moved) {
            // Pointer capture retargets pointerup, so hit-test in tree coordinates.
            const rect = e.currentTarget.getBoundingClientRect();
            const x = ((e.clientX - rect.left) * width / rect.width - view.x) / view.scale;
            const y = ((e.clientY - rect.top) - view.y) / view.scale;
            const hit = nodes.find(n => Math.hypot(n.x - x, n.y - y) < 14);
            if (hit) activate(hit.id);
          }
        },
        onPointerCancel: () => { drag.current = null; } },
        h('g', { transform: `translate(${view.x} ${view.y}) scale(${view.scale})` },
          ...nodes.slice(1).map(n => h('line', { key: `e${n.id}`, x1: nodes[n.parent].x,
            y1: nodes[n.parent].y, x2: n.x, y2: n.y, stroke: neutral, strokeWidth: 3,
            opacity: opacity(n), strokeLinecap: 'round' })),
          ...nodes.map(n => h('g', { key: n.id, 'data-tree-node': n.id, 'data-redex-rule': n.rule || '',
            onPointerEnter: () => { if (!drag.current) hoverGraph(n.id); },
            onPointerLeave: () => setHovered(null) },
            n.id === changed && h('circle', { cx: n.x, cy: n.y, r: 15,
              fill: 'none', stroke: previewColour, strokeWidth: 2, strokeDasharray: '3 3' }),
            n.id === hovered && h('circle', { cx: n.x, cy: n.y, r: 12,
              fill: 'none', stroke: colour(n), strokeWidth: 2 }),
            h('circle', { cx: n.x, cy: n.y, r: 9, fill: colour(n), opacity: opacity(n) }))))),
      h('div', { style: { gridArea: '1 / 1', justifySelf: 'end', alignSelf: 'start', margin: 8,
        display: 'flex', gap: 4 } },
        h(Button, { label: 'Zoom out', tip: 'Zoom out', onClick: () => zoom(1 / 1.3) }, '−'),
        h(Button, { label: 'Zoom in', tip: 'Zoom in', onClick: () => zoom(1.3) }, '+'),
        h(Button, { label: 'Fit', tip: 'Fit the tree to the view',
          onClick: () => setCamera(null) }, 'Fit')),
      highlighted && h('div', { style: { gridArea: '1 / 1', justifySelf: 'start', alignSelf: 'end',
        margin: '0 10px 8px', fontSize: 12,
        pointerEvents: 'none', opacity: 0.85 } },
        describe(highlighted),
        highlighted.rule && h('span', { style: { color: redexColour } },
          ` · rule ${highlighted.rule} · click to rewrite`))),
    h('code', { ref: expression, 'aria-label': 'Expanded Tree Calculus expression',
      style: { display: 'block', overflowWrap: 'anywhere', whiteSpace: 'pre-wrap', fontSize: 12,
        maxHeight: 180, overflowY: 'auto', padding: '8px 12px 10px', lineHeight: 1.8,
        borderTop: `1px solid ${border}` },
      onPointerMove: e => setHovered(tokenId(e)), onPointerLeave: () => setHovered(null),
      onClick: e => { const id = tokenId(e); if (id !== null) activate(id); } },
      ...tokens.map((token, i) => {
        const node = nodes[token.nodeId];
        const triangle = token.text === '△';
        return h('span', { key: i, 'data-tree-expr-node': token.nodeId,
          'data-tree-triangle': triangle ? token.nodeId : undefined,
          tabIndex: triangle && node.rule ? 0 : undefined,
          role: triangle && node.rule ? 'button' : undefined,
          'aria-label': triangle && node.rule ? `Apply rule ${node.rule} at ${pathLabel(pathOf(nodes, node))}` : undefined,
          onFocus: () => setHovered(token.nodeId), onBlur: () => setHovered(null),
          onKeyDown: e => {
            if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); activate(token.nodeId); }
          },
          style: { cursor: node.rule ? 'pointer' : 'default', color: colour(node),
            background: inHighlight(token.nodeId) ? 'var(--vscode-editor-selectionBackground, #617baf66)' : undefined,
            textDecoration: token.nodeId === hovered && triangle ? 'underline' : undefined,
            textUnderlineOffset: 3 } }, token.text);
      })));
}
