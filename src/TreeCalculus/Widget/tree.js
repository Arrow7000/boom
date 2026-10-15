import * as React from 'react';

const h = React.createElement;
const palette = ['#f5a000', '#00cf35', '#00b8ec', '#c178fa', '#ff758f', '#58c9bd'];
const branchColour = index => palette[index] ?? `hsl(${(index * 137.508) % 360} 75% 60%)`;

// A leaf occupies one horizontal slot; parents sit between their outer children.
// Keep this iterative so long stems do not exhaust the JavaScript call stack.
export function layoutTree(tree, redexRules = []) {
  const nodes = [];
  const pending = [{ tree, parent: -1, depth: 0, colourIndex: -1, childIndex: 0 }];
  let leaves = 0;
  let depth = 0;
  while (pending.length) {
    const item = pending.pop();
    const id = nodes.length;
    const node = { ...item, id, rule: redexRules[id] || null,
      children: [], size: 1, x: 0, y: item.depth * 44 };
    nodes.push(node);
    if (item.parent >= 0) nodes[item.parent].children.push(id);
    depth = Math.max(depth, item.depth);
    if (item.tree.length === 0) node.x = leaves++ * 38;
    for (let i = item.tree.length - 1; i >= 0; i--) {
      pending.push({ tree: item.tree[i], parent: id, depth: item.depth + 1,
        // A split starts new colours on its outgoing branches. A stem keeps
        // its incoming colour, including a neutral stem above the first split.
        colourIndex: item.tree.length > 1 ? item.colourIndex + 1 + i : item.colourIndex,
        childIndex: i });
    }
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
    path.push(node.childIndex + 1);
    node = nodes[node.parent];
  }
  return path.length ? 'root.' + path.reverse().join('.') : 'root';
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

export default function TreeWidget({ tree, label, redexRules }) {
  const layout = React.useMemo(() => layoutTree(tree, redexRules), [tree, redexRules]);
  const { nodes } = layout;
  const tokens = React.useMemo(() => expressionTokens(nodes), [nodes]);
  const host = React.useRef(null);
  const expression = React.useRef(null);
  const drag = React.useRef(null);
  const [width, setWidth] = React.useState(480);
  const [camera, setCamera] = React.useState(null);
  const [selected, setSelected] = React.useState(0);
  const [hovered, setHovered] = React.useState(null);
  const [colourMode, setColourMode] = React.useState('redexes');
  React.useEffect(() => {
    const observer = new ResizeObserver(entries => setWidth(Math.max(160, entries[0].contentRect.width)));
    observer.observe(host.current);
    return () => observer.disconnect();
  }, []);
  React.useEffect(() => { setCamera(null); setSelected(0); setHovered(null); }, [tree]);

  const height = Math.max(210, Math.min(520, layout.height + 56));
  const fitScale = Math.min(1, (width - 48) / layout.width, (height - 48) / layout.height);
  const fit = { scale: fitScale, x: (width - (layout.width - 24) * fitScale) / 2,
    y: (height - (layout.height - 24) * fitScale) / 2 };
  const view = camera || fit;
  const focus = nodes[selected] || nodes[0];
  const highlighted = hovered === null ? null : nodes[hovered];
  const neutral = 'var(--vscode-editor-foreground, #eeeeee)';
  const colour = n => colourMode === 'redexes' ? (n.rule ? '#f5a000' : neutral)
    : colourMode === 'branches' && n.colourIndex >= 0 ? branchColour(n.colourIndex) : neutral;
  const redexCount = nodes.filter(n => n.rule).length;
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

  function zoom(factor, cx = width / 2, cy = height / 2) {
    const scale = Math.max(0.02, Math.min(6, view.scale * factor));
    const ratio = scale / view.scale;
    setCamera({ scale, x: cx - (cx - view.x) * ratio, y: cy - (cy - view.y) * ratio });
  }
  const buttonStyle = { cursor: 'pointer', color: 'inherit', background: 'transparent',
    border: '1px solid var(--vscode-widget-border, #7776)', borderRadius: 4, padding: '3px 9px' };
  const button = (text, title, onClick) => h('button', { type: 'button', title,
    'aria-label': title, style: buttonStyle, onClick }, text);
  const shape = n => n.children.length === 0 ? 'leaf' : n.children.length === 1 ? 'stem'
    : n.children.length === 2 ? 'fork' : `${n.children.length} arguments`;
  const ruleDescription = n => n.rule
    ? `rule ${n.rule}${n.children.length > 3 ? ` at first 3 arguments; ${n.children.length - 3} trailing arguments retained` : ''}`
    : 'no rewrite at this node';

  return h('section', { ref: host, style: { color: 'var(--vscode-editor-foreground, #eeeeee)',
    border: '1px solid var(--vscode-widget-border, #7776)', borderRadius: 8, overflow: 'hidden', margin: '8px 0' } },
    h('div', { style: { display: 'flex', alignItems: 'center', flexWrap: 'wrap', gap: 6, padding: '9px 12px' } },
      h('strong', { style: { marginRight: 'auto' } }, 'Tree Calculus'),
      h('span', { style: { opacity: 0.7, fontSize: 12, marginRight: 8 } }, `${nodes.length} nodes`),
      button('−', 'Zoom out', () => zoom(1 / 1.3)),
      button('+', 'Zoom in', () => zoom(1.3)),
      button('Fit', 'Fit tree to view', () => setCamera(null))),
    h('code', { style: { display: 'block', padding: '12px 12px 10px', lineHeight: 1.5,
      overflowWrap: 'anywhere', fontSize: 12 } }, label),
    h('div', { style: { display: 'flex', flexWrap: 'wrap', alignItems: 'center', gap: 8, padding: '9px 12px' } },
      h('label', null, 'Colours ', h('select', { 'aria-label': 'Colour mode', value: colourMode,
        onChange: e => setColourMode(e.target.value),
        style: { color: 'inherit', background: 'var(--vscode-dropdown-background, #333333)',
          border: '1px solid var(--vscode-widget-border, #7776)', borderRadius: 4, padding: '3px 6px' } },
        h('option', { value: 'redexes' }, 'Redexes'),
        h('option', { value: 'branches' }, 'Branches'),
        h('option', { value: 'none' }, 'None'))),
      h('span', { style: { opacity: 0.75, fontSize: 12 } }, `${redexCount} local rewrite ${redexCount === 1 ? 'site' : 'sites'}`)),
    h('div', { style: { padding: '0 12px 9px', fontSize: 12, opacity: 0.8 } },
      colourMode === 'redexes'
        ? 'Orange: a rewrite can fire here. Neutral nodes may still contain redexes below them.'
        : colourMode === 'branches' ? 'Colours change where branches split; straight stems keep their colour.'
        : 'Hover either view to highlight matching subtrees.'),
    h('svg', { width: '100%', height, viewBox: `0 0 ${width} ${height}`,
      role: 'img', 'aria-label': `Tree of ${label}, ${nodes.length} nodes. Children are ordered left to right.`,
      style: { display: 'block', background: 'var(--vscode-editor-background, #111111)',
        touchAction: 'none', cursor: 'grab', userSelect: 'none' },
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
        if (d && !d.moved) {
          // Pointer capture retargets pointerup, so hit-test in tree coordinates.
          const rect = e.currentTarget.getBoundingClientRect();
          const x = ((e.clientX - rect.left) * width / rect.width - view.x) / view.scale;
          const y = ((e.clientY - rect.top) - view.y) / view.scale;
          const hit = nodes.find(n => Math.hypot(n.x - x, n.y - y) < 14);
          if (hit) setSelected(hit.id);
        }
        drag.current = null;
        e.currentTarget.releasePointerCapture(e.pointerId);
      },
      onPointerCancel: () => { drag.current = null; } },
      h('g', { transform: `translate(${view.x} ${view.y}) scale(${view.scale})` },
        ...nodes.slice(1).map(n => h('line', { key: `e${n.id}`, x1: nodes[n.parent].x,
          y1: nodes[n.parent].y, x2: n.x, y2: n.y,
          stroke: colourMode === 'branches' ? colour(n) : neutral, strokeWidth: 3,
          opacity: opacity(n), strokeLinecap: 'round' })),
        ...nodes.map(n => h('g', { key: n.id, 'data-tree-node': n.id, 'data-redex-rule': n.rule || '',
          onPointerEnter: () => { if (!drag.current) hoverGraph(n.id); },
          onPointerLeave: () => setHovered(null) },
          h('title', null, `${pathOf(nodes, n)} · ${shape(n)} · ${n.size} nodes · ${ruleDescription(n)}`),
          n.id === selected && h('circle', { cx: n.x, cy: n.y, r: 14,
            fill: 'none', stroke: colour(n), strokeWidth: 1.5, opacity: 0.6 }),
          n.id === hovered && h('circle', { cx: n.x, cy: n.y, r: 12,
            fill: 'none', stroke: colour(n), strokeWidth: 2 }),
          h('circle', { cx: n.x, cy: n.y, r: 9, fill: colour(n), opacity: opacity(n) }))))),
    h('div', { style: { padding: '9px 12px', fontSize: 12, borderTop: '1px solid var(--vscode-widget-border, #7776)' } },
      h('div', { style: { marginBottom: 5 } }, `${pathOf(nodes, focus)} · ${shape(focus)} · ${focus.size} nodes in subtree · ${ruleDescription(focus)}`),
      h('div', { style: { marginBottom: 5, opacity: 0.8 } }, 'Expression · hover either view to highlight the same subtree'),
      h('code', { ref: expression, 'aria-label': 'Expanded Tree Calculus expression',
        style: { display: 'block', overflowWrap: 'anywhere', whiteSpace: 'pre-wrap',
          maxHeight: 180, overflowY: 'auto', padding: '6px 2px', lineHeight: 1.8 },
        onPointerMove: e => setHovered(tokenId(e)), onPointerLeave: () => setHovered(null),
        onClick: e => { const id = tokenId(e); if (id !== null) setSelected(id); } },
        ...tokens.map((token, i) => h('span', { key: i, 'data-tree-expr-node': token.nodeId,
          'data-tree-triangle': token.text === '△' ? token.nodeId : undefined,
          'data-highlighted': inHighlight(token.nodeId) ? 'true' : 'false',
          title: `${pathOf(nodes, nodes[token.nodeId])} · ${shape(nodes[token.nodeId])} · ${ruleDescription(nodes[token.nodeId])}`,
          tabIndex: token.text === '△' ? 0 : undefined,
          role: token.text === '△' ? 'button' : undefined,
          'aria-label': token.text === '△' ? `Inspect ${pathOf(nodes, nodes[token.nodeId])}` : undefined,
          onFocus: () => setHovered(token.nodeId), onBlur: () => setHovered(null),
          onKeyDown: e => {
            if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); setSelected(token.nodeId); }
          },
          style: { cursor: 'pointer', color: colour(nodes[token.nodeId]),
            background: inHighlight(token.nodeId) ? 'var(--vscode-editor-selectionBackground, #617baf66)' : undefined,
            textDecoration: token.nodeId === hovered && token.text === '△' ? 'underline' : undefined,
            textUnderlineOffset: 3 } }, token.text))),
      h('div', { style: { opacity: 0.65, marginTop: 8 } },
        'Drag to pan · + / − to zoom · click a node or triangle to inspect · children run left to right')));
}
