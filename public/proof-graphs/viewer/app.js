"use strict";

const svgNS = "http://www.w3.org/2000/svg";
const bySelector = (selector) => document.querySelector(selector);
const stage = bySelector("#stage");
const diagram = bySelector("#diagram");
const world = bySelector("#world");
const edgeLayer = bySelector("#edges");
const nodeLayer = bySelector("#nodes");
const labelWorld = bySelector("#label-world");
const inspector = bySelector("#inspector");
const inspectorBody = bySelector("#inspector-body");
const portraitLayout = window.matchMedia("(orientation: portrait) and (max-width: 1024px)");

const referenceRelations = new Set(["applies", "summarizes", "unfolds",
  "mentions_in_statement", "references_in_proof", "references_in_body"]);
const relationLabels = {
  premise_of: "Premise",
  produces: "Result",
  concludes: "Concludes the theorem",
  supports: "Result used as a premise",
  applies: "Applied Lean result",
  summarizes: "Lean source summarized",
  unfolds: "Definition unfolded",
  mentions_in_statement: "Statement reference",
  references_in_proof: "Proof-term reference",
  references_in_body: "Definition reference",
  about: "Concept",
};
const labelWidthRatio = 1.50;
const labelHeightRatio = 1.16;
const nodeGap = 25;
const linkedNodeGap = 46;
const arrowHeadSize = 8;
const minZoom = .19;
const maxZoom = 3.3;
const touchPoints = new Map();

let proof;
let evidence;
let annotations;
let concepts;
let roots;
let views;
let layout;
let selected = null;
let mode = "steps";
let downwardFlow = new URLSearchParams(location.search).get("layout") === "downward";
let gesture = null;
let pinch = null;
let camera = { x: 0, y: 0, scale: 1, fitted: true, overview: true };
let frame = 0;

function svg(tag, attributes = {}) {
  const element = document.createElementNS(svgNS, tag);
  for (const [name, value] of Object.entries(attributes)) element.setAttribute(name, value);
  return element;
}

function html(tag, text, className) {
  const element = document.createElement(tag);
  if (text) element.textContent = text;
  if (className) element.className = className;
  return element;
}

function drawMath(element, formula, display = false) {
  if (!formula) return;
  if (window.katex) {
    window.katex.render(formula, element, {
      throwOnError: false, trust: false, strict: "ignore", displayMode: display,
    });
  } else {
    element.textContent = formula;
  }
}

function titleFor(id) {
  const item = evidence.get(id);
  return annotations[id]?.title || item?.title || item?.name || id;
}

function shortLabel(id) {
  return [titleFor(id), annotations[id]?.compact_latex];
}

function sourceUrl(value) {
  if (typeof value !== "string") return null;
  try {
    const url = new URL(value);
    return ["http:", "https:"].includes(url.protocol) ? url.href : null;
  } catch {
    return null;
  }
}

function hash(value) {
  let n = 2166136261;
  for (const c of value) n = Math.imul(n ^ c.codePointAt(0), 16777619);
  return n >>> 0;
}

function noise(seed, index) {
  return ((Math.imul(seed ^ Math.imul(index + 97, 2654435761), 2246822519) >>> 0) % 4096) / 4096 - .5;
}

function anchorNodes(layout, portrait, fold = false, center = false) {
  const { nodes, nodeMap, neighbors, edges } = layout;
  const incoming = new Map(nodes.map((node) => [node.id, []]));
  for (const edge of edges) incoming.get(edge.target).push(edge.source);
  const seen = new Set();
  const crossLimit = Math.max(480, Math.sqrt(nodes.length) * 158);
  let nextComponent = 0;

  for (const first of nodes) {
    if (seen.has(first.id)) continue;
    const component = [first.id];
    seen.add(first.id);
    for (const id of component) {
      for (const next of neighbors.get(id)) {
        if (seen.has(next)) continue;
        seen.add(next);
        component.push(next);
      }
    }
    const anchors = component.filter((id) => nodeMap.get(id).isRoot);
    const queue = anchors.length ? anchors : [component[0]];
    const ranks = new Map(queue.map((id) => [id, 0]));
    for (const id of queue) {
      for (const previous of incoming.get(id)) {
        if (ranks.has(previous)) continue;
        ranks.set(previous, ranks.get(id) + 1);
        queue.push(previous);
      }
    }
    // For cycles or links pointing away from a root, use the undirected distance.
    for (const id of queue) {
      for (const next of neighbors.get(id)) {
        if (ranks.has(next)) continue;
        ranks.set(next, ranks.get(id) + 1);
        queue.push(next);
      }
    }
    const layers = new Map();
    for (const id of queue) {
      const rank = ranks.get(id);
      if (!layers.has(rank)) layers.set(rank, []);
      layers.get(rank).push(nodeMap.get(id));
    }
    if (fold && layers.size > 4) {
      nextComponent = foldLayers([...layers.values()], portrait, nextComponent);
      continue;
    }

    const alongRadius = (node) => portrait ? node.ry : node.rx;
    const crossRadius = (node) => portrait ? node.rx : node.ry;
    let along = 0;
    let crossExtent = 0;
    const offsets = new Map();
    const ranksInOrder = [...layers.keys()].sort((a, b) => a - b);
    if (center && anchors.length && ranksInOrder.length > 2) {
      const rootRank = ranksInOrder.shift();
      ranksInOrder.splice(Math.floor(ranksInOrder.length / 2), 0, rootRank);
    }
    for (const rank of ranksInOrder) {
      const layer = layers.get(rank);
      const preferred = (node) => {
        const reference = [...neighbors.get(node.id)].filter((id) => offsets.has(id));
        return reference.length ? reference.reduce((sum, id) => sum + offsets.get(id), 0) / reference.length : 0;
      };
      const ordered = layer.map((node) => ({ node, preference: preferred(node) }));
      ordered.sort((a,b) => a.preference-b.preference);
      let row = [];
      let span = 0;
      const placeRow = () => {
        if (!row.length) return;
        const half = Math.max(...row.map(alongRadius));
        along += half;
        let cross = -span / 2;
        const stagger = row.length === 1 && rank ? (rank % 2 ? 1 : -1) * 24 : 0;
        for (const node of row) {
          const offset = cross + crossRadius(node) + stagger;
          offsets.set(node.id, offset);
          const column = nextComponent + offset;
          node.x = node.ax = portrait ? column : -along;
          node.y = node.ay = portrait ? -along : column;
          cross = offset - stagger + crossRadius(node) + nodeGap * 1.7;
          crossExtent = Math.max(crossExtent, Math.abs(offset) + crossRadius(node));
          node.vx = node.vy = 0;
        }
        along += half + linkedNodeGap + 16;
        row = [];
        span = 0;
      };
      for (const { node } of ordered) {
        const width = 2 * crossRadius(node);
        if (row.length && span + width + nodeGap * 1.7 > crossLimit) placeRow();
        span += width + (row.length ? nodeGap * 1.7 : 0);
        row.push(node);
      }
      placeRow();
    }
    for (const id of component) {
      const node = nodeMap.get(id);
      if (portrait) node.x = node.ax += crossExtent;
      else node.y = node.ay += crossExtent;
    }
    nextComponent += crossExtent * 2 + 95;
  }
}

function placeNode(node, x, y) {
  node.x = node.ax = x;
  node.y = node.ay = y;
  node.vx = node.vy = 0;
}

function foldLayers(layers, portrait, crossStart) {
  const along = (node) => portrait ? node.ry : node.rx;
  const cross = (node) => portrait ? node.rx : node.ry;
  const stretch = Math.ceil(Math.sqrt(layers.length * (portrait ? 1.65 : 1.1)));
  const bandCount = Math.ceil(layers.length / stretch);
  const bandWidths = Array(bandCount).fill(0);
  const rowHeights = Array(stretch).fill(0);
  const cells = layers.map((nodes, i) => {
    const band = Math.floor(i / stretch);
    const offset = i % stretch;
    const row = band % 2 ? stretch - 1 - offset : offset;
    const width = nodes.reduce((sum, node) => sum + 2 * cross(node) + nodeGap, -nodeGap);
    bandWidths[band] = Math.max(bandWidths[band], width);
    rowHeights[row] = Math.max(rowHeights[row], ...nodes.map((node) => 2 * along(node)));
    return { band, row, nodes, width };
  });
  const position = (sizes, offset) => sizes.map((size) => {
    const middle = offset + size / 2;
    offset += size + linkedNodeGap + 12;
    return middle;
  });
  const bands = position(bandWidths, crossStart);
  const rows = position(rowHeights, 0);
  for (const { band, row, nodes, width } of cells) {
    let offset = bands[band] - width / 2;
    for (const node of nodes) {
      const column = offset + cross(node);
      placeNode(node, portrait ? column : -rows[row], portrait ? -rows[row] : column);
      offset += 2 * cross(node) + nodeGap;
    }
  }
  return bands.at(-1) + bandWidths.at(-1) / 2 + 95;
}

function centerBranches(layout, portrait) {
  const { nodes, nodeMap, neighbors, edges } = layout;
  const central = nodes.filter((node) => node.isRoot);
  if (!central.length) return false;
  const incoming = new Map(nodes.map((node) => [node.id, new Set()]));
  for (const { source, target } of edges) incoming.get(target).add(source);
  const severalRoots = central.length > 1;
  const seeds = severalRoots ? central : [...incoming.get(central[0].id)].map((id) => nodeMap.get(id));
  if (seeds.length < 2) return false;
  if (nodes.length > 100) {
    // Keep large reference graphs packed in layers so long cross-links stay routable.
    anchorNodes(layout, portrait, false, true);
    return true;
  }

  const branches = seeds.map(() => new Map());
  const queue = seeds.map((node, branch) => ({ node, branch, rank: severalRoots ? 0 : 1 }));
  const seen = new Set([...central, ...seeds].map(({ id }) => id));
  const visit = ({ node, rank, branch }, links) => {
    for (const id of links.get(node.id)) {
      if (seen.has(id)) continue;
      seen.add(id);
      queue.push({ node: nodeMap.get(id), rank: rank + 1, branch });
    }
  };
  for (const entry of queue) visit(entry, incoming);
  for (const entry of queue) visit(entry, neighbors);
  for (const { node, branch, rank } of queue) {
    const rows = branches[branch];
    if (!rows.has(rank)) rows.set(rank, []);
    rows.get(rank).push(node);
  }

  const firstAngle = portrait ? -Math.PI / 2 : Math.PI;
  const step = 2 * Math.PI / seeds.length;
  const centerRadius = severalRoots ? 0 : Math.max(central[0].rx, central[0].ry);
  const seedDiameter = Math.max(...seeds.map((node) => 2 * Math.max(node.rx, node.ry)));
  const seedRadius = (seedDiameter + nodeGap) / (2 * Math.sin(step / 2));
  const startRadius = severalRoots ? Math.max(seedRadius, seedDiameter * .45)
    : Math.max(seedRadius, centerRadius + seedDiameter / 2 + linkedNodeGap);
  const laneWidth = Math.max(300, Math.sqrt(queue.length / seeds.length) * 104);
  if (!severalRoots) placeNode(central[0], 0, 0);

  for (const [branch, rows] of branches.entries()) {
    const angle = firstAngle + branch * step;
    const ux = Math.cos(angle);
    const uy = Math.sin(angle);
    const along = (node) => projectedRadius(node, ux, uy);
    const cross = (node) => projectedRadius(node, -uy, ux);
    let radius = startRadius - along(seeds[branch]);
    const preferred = new Map();
    let ranks = [...rows].sort(([a], [b]) => a - b).map(([, row]) => row);
    if (seeds.length === 2 && ranks.length > 4) {
      const [head, ...rest] = ranks;
      const chain = rest.flat();
      const width = Math.ceil(Math.sqrt(chain.length * (portrait ? .9 : 1.5)));
      ranks = [head];
      for (let i = 0; i < chain.length; i += width) ranks.push(chain.slice(i, i + width));
    }
    const packed = ranks.length < rows.size;
    for (const [rowIndex, row] of ranks.entries()) {
      const byParent = (node) => {
        const offsets = [...neighbors.get(node.id)].filter((id) => preferred.has(id));
        return offsets.reduce((sum, id) => sum + preferred.get(id), 0) / (offsets.length || 1);
      };
      if (packed) {
        if (rowIndex % 2) row.reverse();
      } else {
        row.sort((a, b) => byParent(a) - byParent(b));
      }
      let first = 0;
      while (first < row.length) {
        let end = first + 1;
        let width = 2 * cross(row[first]);
        while (end < row.length && (packed || width + 2 * cross(row[end]) + nodeGap <= laneWidth)) {
          width += 2 * cross(row[end++]) + nodeGap;
        }
        const lane = row.slice(first, end);
        const half = Math.max(...lane.map(along));
        radius += half;
        let lateral = -width / 2;
        for (const node of lane) {
          const offset = lateral + cross(node);
          placeNode(node, radius * ux - offset * uy, radius * uy + offset * ux);
          preferred.set(node.id, offset);
          lateral += 2 * cross(node) + nodeGap;
        }
        radius += half + linkedNodeGap + 12;
        first = end;
      }
    }
  }
  const loose = nodes.filter(({ id }) => !seen.has(id));
  if (loose.length) {
    anchorNodes({ ...layout, nodes: loose, edges: edges.filter(({ source }) => !seen.has(source)) }, portrait);
    const offset = Math.max(...nodes.filter(({ id }) => seen.has(id)).map((node) => node.x + node.rx)) -
      Math.min(...loose.map((node) => node.x - node.rx)) + 95;
    for (const node of loose) placeNode(node, node.x + offset, node.y);
  }
  return true;
}

function ellipsePath(rx, ry, seed, offset = 0) {
  const points = Array.from({ length: 24 }, (_, i) => {
    const angle = i * Math.PI / 12;
    const wobble = noise(seed, i) * 3.3;
    return [
      Math.cos(angle) * (rx + wobble + offset) + noise(seed, i + 60) * .8,
      Math.sin(angle) * (ry + wobble + offset) + noise(seed, i + 140) * .8,
    ];
  });
  const midpoint = (a, b) => [(a[0] + b[0]) / 2, (a[1] + b[1]) / 2];
  const format = (p) => `${p[0].toFixed(1)} ${p[1].toFixed(1)}`;
  const start = midpoint(points.at(-1), points[0]);
  return `M${format(start)} ` + points.map((point, i) =>
    `Q${format(point)} ${format(midpoint(point, points[(i + 1) % points.length]))}`
  ).join(" ") + " Z";
}

function createNode(item, sizeRole) {
  const isRoot = roots.has(item.id);
  const [title, formula] = shortLabel(item.id);
  const rx = isRoot ? 93 : sizeRole === "block" ? 72 :
    item.kind === "inference" ? 64 : item.role === "assumption" ? 59 : 57;
  const ry = Math.ceil(rx * (isRoot ? .75 : .70));
  const group = svg("g", {
    class: `graph-node${isRoot ? " is-root" : ""}${item.kind === "declaration" && !isRoot ? " is-reference" : ""}`,
    "data-node": item.id, role: "button", tabindex: "0",
    "aria-label": title, "aria-pressed": "false",
  });
  const outline = svg("path", { class: "node-outline" });
  const echo = svg("path", { class: "node-echo" });
  // Keep the math in HTML so it doesn't depend on SVG foreignObject compositing.
  const label = html("div", null, `node-label${isRoot ? " is-root" : ""}`);
  const stack = html("div", null, "node-label-stack");
  const titleElement = html("span", title, "node-title");
  const math = formula ? html("span", null, "node-formula") : null;
  stack.append(titleElement);
  if (math) {
    drawMath(math, formula);
    stack.append(math);
  }
  label.append(stack);
  group.append(outline, echo);
  group.addEventListener("keydown", (event) => {
    if (event.key === "Enter" || event.key === " ") {
      event.preventDefault();
      selectNode(item.id);
    }
  });
  nodeLayer.append(group);
  labelWorld.append(label);
  return {
    id: item.id, item, isRoot, rx, ry, baseRx: rx, baseRy: ry, ax: 0, ay: 0,
    x: 0, y: 0, vx: 0, vy: 0, group, pinned: false,
    outline, echo, label, stack, titleElement, math,
  };
}

function createEdge(link, nodes) {
  const group = svg("g", { class: referenceRelations.has(link.relation) ? "edge is-reference" : "edge",
    "data-source": link.source, "data-target": link.target });
  const paths = ["edge-highlight", "edge-highlight-tip", "edge-echo", "edge-line", "edge-tip"].map(
    (kind) => svg("path", { class: kind }),
  );
  group.append(...paths);
  edgeLayer.append(group);
  return { ...link, a: nodes.get(link.source), b: nodes.get(link.target), group, paths,
    bend: noise(hash(JSON.stringify([link.source, link.target, link.relation])), 1) * 40 };
}

function createLayout() {
  cancelAnimationFrame(frame);
  gesture = null;
  pinch = null;
  touchPoints.clear();
  diagram.classList.remove("is-dragging");
  const projection = views[mode];
  const portrait = downwardFlow || portraitLayout.matches;
  nodeLayer.replaceChildren();
  edgeLayer.replaceChildren();
  labelWorld.replaceChildren();
  const nodes = projection.nodes.map((id) => createNode(evidence.get(id), projection.size_roles?.[id]));
  const nodeMap = new Map(nodes.map((node) => [node.id, node]));
  const edges = projection.edges.filter((edge) => edge.source !== edge.target)
    .map((edge) => createEdge(edge, nodeMap));
  const neighbors = new Map(nodes.map((node) => [node.id, new Set()]));
  for (const edge of edges) {
    neighbors.get(edge.source).add(edge.target);
    neighbors.get(edge.target).add(edge.source);
  }
  layout = { nodes, nodeMap, edges, neighbors, collapsed: projection.collapsed_into || {}, portrait };
  fitLabels(nodes);
  if (downwardFlow || !centerBranches(layout, portrait)) anchorNodes(layout, portrait, !downwardFlow);
  if (nodes.length <= 100) {
    for (let i = 0; i < 42; i++) forceStep(.75);
    separateNodes(24);
  }
  for (const node of nodes) node.vx = node.vy = 0;
  paintNodes();
  bySelector("#graph-count").textContent = `${nodes.length} nodes · ${edges.length} arrows`;
  const currentLayout = layout;
  if (document.fonts?.status === "loading") {
    document.fonts.ready.then(() => {
      if (layout !== currentLayout) return;
      fitLabels(nodes);
      separateNodes(40);
      paintNodes();
      if (camera.fitted) fitGraph(camera.overview);
    });
  }
}

function setLabelBounds(node) {
  // The rectangle's corners sit inside the ellipse, away from the ink outline.
  const width = Math.floor(node.rx * labelWidthRatio);
  const height = Math.floor(node.ry * labelHeightRatio);
  node.label.style.width = `${width}px`;
  node.label.style.height = `${height}px`;
  return { width: width - 3, height: height - 3 };
}

function fitNodeLabel(node) {
  const { titleElement: title, stack, math } = node;
  node.rx = node.baseRx;
  node.ry = node.baseRy;
  const minTitleSize = 13;
  const maxTitleSize = node.isRoot ? 23 : 19;
  for (let attempt = 0; attempt < 6; attempt++) {
    const { width, height } = setLabelBounds(node);
    if (math) {
      math.hidden = false;
      math.style.fontSize = "12px";
      if (math.offsetWidth > width) {
        math.style.fontSize = `${Math.max(8, 12 * (width - 1) / math.offsetWidth)}px`;
      }
      const fittedRadius = Math.ceil((math.offsetWidth + 4) / labelWidthRatio);
      if (math.offsetWidth > width && fittedRadius <= node.baseRx * 1.22) {
        node.rx = fittedRadius;
        continue;
      }
      math.hidden = math.offsetWidth > width;
    }
    title.style.fontSize = `${minTitleSize}px`;
    if (stack.offsetHeight > height) {
      node.ry = Math.ceil((stack.offsetHeight + 6) / labelHeightRatio);
      continue;
    }
    let low = minTitleSize;
    let high = maxTitleSize;
    for (let i = 0; i < 7; i++) {
      const candidate = (low + high) / 2;
      title.style.fontSize = `${candidate}px`;
      if (stack.offsetHeight <= height) low = candidate;
      else high = candidate;
    }
    title.style.fontSize = `${low}px`;
    break;
  }
  setLabelBounds(node);
  const seed = hash(node.id);
  node.outline.setAttribute("d", ellipsePath(node.rx, node.ry, seed));
  node.echo.setAttribute("d", ellipsePath(node.rx, node.ry, seed ^ 0x5041, -1.7));
}

function fitLabels(nodes) {
  stage.classList.add("is-fitting-labels");
  for (const node of nodes) fitNodeLabel(node);
  stage.classList.remove("is-fitting-labels");
}

function projectedRadius(node, ux, uy) {
  return Math.hypot(node.rx * ux, node.ry * uy);
}

function separateNodes(iterations) {
  const { nodes, neighbors } = layout;
  for (let pass = 0; pass < iterations; pass++) {
    let moved = false;
    for (let i = 0; i < nodes.length; i++) {
      const a = nodes[i];
      for (let j = i + 1; j < nodes.length; j++) {
        const b = nodes[j];
        const gap = neighbors.get(a.id).has(b.id) ? linkedNodeGap : nodeGap;
        const dx = b.x - a.x;
        const dy = b.y - a.y;
        const distance = Math.hypot(dx, dy);
        if (distance > Math.max(a.rx, a.ry) + Math.max(b.rx, b.ry) + gap) continue;
        const ux = distance ? dx / distance : 1;
        const uy = distance ? dy / distance : 0;
        const overlap = projectedRadius(a, ux, uy) + projectedRadius(b, ux, uy) + gap - distance;
        if (overlap < .1) continue;
        const weightA = a.pinned ? 0 : a.isRoot ? .36 : 1;
        const weightB = b.pinned ? 0 : b.isRoot ? .36 : 1;
        if (!weightA && !weightB) continue;
        const push = overlap / (weightA + weightB);
        a.x -= ux * push * weightA;
        a.y -= uy * push * weightA;
        b.x += ux * push * weightB;
        b.y += uy * push * weightB;
        moved = true;
      }
    }
    if (!moved) break;
  }
}

function forceStep(strength) {
  if (!layout) return;
  const { nodes, edges } = layout;
  for (let i = 0; i < nodes.length; i++) {
    const a = nodes[i];
    for (let j = i + 1; j < nodes.length; j++) {
      const b = nodes[j];
      const dx = b.x - a.x || .01;
      const dy = b.y - a.y || .01;
      const distance = Math.hypot(dx, dy);
      const theta = Math.atan2(dy, dx);
      const minimum = ellipseRadius(a, theta) + ellipseRadius(b, theta) + nodeGap;
      const push = (Math.max(0, minimum - distance) * .18 + 690 / Math.max(distance, 38) ** 2) * strength;
      a.vx -= dx * push / distance;
      a.vy -= dy * push / distance;
      b.vx += dx * push / distance;
      b.vy += dy * push / distance;
    }
  }
  for (const { a, b } of edges) {
    const dx = b.x - a.x;
    const dy = b.y - a.y;
    const distance = Math.hypot(dx, dy) || 1;
    const rest = projectedRadius(a, dx / distance, dy / distance) +
      projectedRadius(b, dx / distance, dy / distance) + linkedNodeGap + 9;
    const pull = (distance - rest) * .012 * strength;
    a.vx += dx * pull / distance;
    a.vy += dy * pull / distance;
    b.vx -= dx * pull / distance;
    b.vy -= dy * pull / distance;
  }
  for (const n of nodes) {
    if (n.pinned) { n.vx = n.vy = 0; continue; }
    const pull = n.isRoot ? .25 : .16;
    n.vx = (n.vx + (n.ax - n.x) * pull * strength) * .78;
    n.vy = (n.vy + (n.ay - n.y) * pull * strength) * .78;
    n.x += n.vx;
    n.y += n.vy;
  }
}

function ellipseRadius(node, angle) {
  return 1 / Math.hypot(Math.cos(angle) / node.rx, Math.sin(angle) / node.ry);
}

function pointOutsideNode(node, angle) {
  const distance = ellipseRadius(node, angle) + 4;
  return [node.x + Math.cos(angle) * distance, node.y + Math.sin(angle) * distance];
}

function segmentClear([x, y], [endX, endY], obstacles) {
  const minX = Math.min(x, endX);
  const maxX = Math.max(x, endX);
  const minY = Math.min(y, endY);
  const maxY = Math.max(y, endY);
  return obstacles.every(({ cx, cy, rx, ry }) => {
    if (maxX < cx - rx || minX > cx + rx || maxY < cy - ry || minY > cy + ry) return true;
    // In scaled coordinates, the ellipse is a unit circle.
    const px = (x - cx) / rx;
    const py = (y - cy) / ry;
    const dx = (endX - x) / rx;
    const dy = (endY - y) / ry;
    const closest = Math.max(0, Math.min(1, -(px * dx + py * dy) / (dx * dx + dy * dy || 1)));
    return (px + closest * dx) ** 2 + (py + closest * dy) ** 2 >= 1;
  });
}

function obstacleIndex(nodes) {
  const cell = 144;
  const grid = new Map();
  const boxes = nodes.map(({ id, x, y, rx, ry }) => ({ id, cx: x, cy: y, rx: rx + 16, ry: ry + 16 }));
  const range = (left, top, right, bottom) =>
    [left, top, right, bottom].map((coordinate) => Math.floor(coordinate / cell));
  for (const box of boxes) {
    const [left, top, right, bottom] = range(box.cx - box.rx, box.cy - box.ry, box.cx + box.rx, box.cy + box.ry);
    for (let x = left; x <= right; x++) {
      for (let y = top; y <= bottom; y++) {
        const key = `${x},${y}`;
        if (!grid.has(key)) grid.set(key, []);
        grid.get(key).push(box);
      }
    }
  }
  return {
    query(x, y, u, v, margin = 0) {
      const [left, top, right, bottom] = range(Math.min(x, u)-margin, Math.min(y, v)-margin,
        Math.max(x, u)+margin, Math.max(y, v)+margin);
      if ((right-left+1)*(bottom-top+1) > boxes.length * 2) return boxes;
      const nearby = new Set();
      for (let column = left; column <= right; column++) {
        for (let row = top; row <= bottom; row++) {
          for (const box of grid.get(`${column},${row}`) || []) nearby.add(box);
        }
      }
      return nearby;
    },
    boxes,
  };
}

function routeEdge(a, b, obstacles, clear) {
  const start = [a.x, a.y];
  const end = [b.x, b.y];
  const terminals = [a, b].map(({ x, y, rx, ry }) => ({ cx: x, cy: y, rx: rx + 8, ry: ry + 8 }));
  const corners = Array.from(obstacles, ({ cx, cy, rx, ry }) => [
    [cx - rx, cy - ry], [cx + rx, cy - ry], [cx - rx, cy + ry], [cx + rx, cy + ry],
  ]).flat().filter((point) => segmentClear(point, point, terminals) && clear(point, point));
  const points = [start, end, ...corners];
  const distance = ([x, y], [u, v]) => Math.hypot(x - u, y - v);
  const estimate = points.map((point) => distance(point, end));
  const costs = points.map(() => Infinity);
  const previous = [];
  const open = new Set([0]);
  const seen = new Set();
  costs[0] = 0;

  // Find the shortest route through the visible corners of the padded obstacles.
  while (open.size) {
    let current = open.values().next().value;
    for (const i of open) {
      if (costs[i] + estimate[i] < costs[current] + estimate[current]) current = i;
    }
    if (current === 1) {
      const route = [];
      for (let i = current; i !== undefined; i = previous[i]) route.push(points[i]);
      return route.reverse();
    }
    open.delete(current);
    seen.add(current);
    for (let i = 1; i < points.length; i++) {
      if (seen.has(i)) continue;
      const cost = costs[current] + distance(points[current], points[i]);
      if (cost >= costs[i] || !clear(points[current], points[i])) continue;
      costs[i] = cost;
      previous[i] = current;
      open.add(i);
    }
  }
  return null;
}

function roundedRoute(points, offset = 0) {
  const coords = ([x, y]) => `${x} ${y + offset}`;
  const shorten = ([x, y], [u, v]) => {
    const distance = Math.hypot(u - x, v - y) || 1;
    // A quadratic cuts in by at most a quarter of this trim.
    const fraction = Math.min(.35, 32 / distance);
    return [x + (u - x) * fraction, y + (v - y) * fraction];
  };
  let path = `M${coords(points[0])}`;
  for (let i = 1; i < points.length - 1; i++) {
    const corner = points[i];
    path += ` L${coords(shorten(corner, points[i - 1]))} Q${coords(corner)} ${coords(shorten(corner, points[i + 1]))}`;
  }
  return `${path} L${coords(points.at(-1))}`;
}

function bezierSamples([start, first, second, end]) {
  return Array.from({ length: 17 }, (_, i) => {
    const t = i / 16;
    const u = 1 - t;
    return start.map((value, axis) => u ** 3 * value + 3 * u ** 2 * t * first[axis] +
      3 * u * t ** 2 * second[axis] + t ** 3 * end[axis]);
  });
}

function smoothRoute({ a, b, bend }, spatial) {
  const dx = b.x - a.x;
  const dy = b.y - a.y;
  const span = Math.hypot(dx, dy) || 1;
  const side = Math.sign(bend) || 1;
  const curvature = Math.min(span / 4, Math.max(10, Math.abs(bend)));
  for (const extra of [curvature, -curvature, curvature * 2, -curvature * 2, 0]) {
    const x = -dy * extra * side / span;
    const y = dx * extra * side / span;
    const sourceAngle = Math.atan2(dy / 3 + y, dx / 3 + x);
    const targetAngle = Math.atan2(-dy / 3 + y, -dx / 3 + x);
    const start = pointOutsideNode(a, sourceAngle);
    const end = pointOutsideNode(b, targetAngle);
    const handle = Math.hypot(end[0] - start[0], end[1] - start[1]) / 3;
    const curve = [
      start, [start[0] + Math.cos(sourceAngle) * handle, start[1] + Math.sin(sourceAngle) * handle],
      [end[0] + Math.cos(targetAngle) * handle, end[1] + Math.sin(targetAngle) * handle], end,
    ];
    const samples = bezierSamples(curve);
    const xs = curve.map(([x]) => x);
    const ys = curve.map(([, y]) => y);
    const obstacles = Array.from(spatial.query(Math.min(...xs), Math.min(...ys), Math.max(...xs), Math.max(...ys)))
      .filter((node) => node.id !== a.id && node.id !== b.id);
    for (const { x: cx, y: cy, rx, ry } of [a, b]) obstacles.push({ cx, cy, rx, ry });
    if (samples.slice(1).every((point, i) => segmentClear(samples[i], point, obstacles))) {
      return { curve, samples };
    }
  }
  return null;
}

function bezierPath([start, first, second, end], offset = 0) {
  const coords = ([x, y]) => `${x} ${y + offset}`;
  return `M${coords(start)} C${coords(first)} ${coords(second)} ${coords(end)}`;
}

function paintEdge(edge, spatial) {
  const { a, b, paths } = edge;
  edge.routePoints = null;
  edge.arrow = null;
  const clear = (start, end) => segmentClear(start, end,
    Array.from(spatial.query(...start, ...end)).filter((n) => n.id !== a.id && n.id !== b.id));
  const smooth = smoothRoute(edge, spatial);
  if (smooth) {
    const { curve, samples } = smooth;
    const [x, y] = curve.at(-1);
    const [u, v] = curve.at(-2);
    edge.routePoints = samples;
    paintEdgePaths(edge, bezierPath(curve), bezierPath(curve, .8), x, y, Math.atan2(y - v, x - u));
    return;
  }
  const nearby = (margin) => Array.from(spatial.query(a.x, a.y, b.x, b.y, margin))
    .filter((n) => n.id !== a.id && n.id !== b.id);
  const blockers = nearby(0).filter((n) => !segmentClear([a.x,a.y], [b.x,b.y], [n]));
  const points = routeEdge(a, b, blockers, clear) ||
    routeEdge(a, b, nearby(190), clear) ||
    routeEdge(a, b, spatial.boxes.filter((n) => n.id !== a.id && n.id !== b.id), clear);
  if (!points) {
    // During a drag, a node may close the gap at an endpoint.
    for (const path of paths) path.setAttribute("d", "");
    return;
  }
  const angleTo = ([x, y], [u, v]) => Math.atan2(v - y, u - x);
  const sourceAngle = angleTo(points[0], points[1]);
  const targetAngle = angleTo(points.at(-1), points.at(-2));
  points[0] = pointOutsideNode(a, sourceAngle);
  points[points.length - 1] = pointOutsideNode(b, targetAngle);
  edge.routePoints = points;
  const [x, y] = points.at(-1);
  paintEdgePaths(edge, roundedRoute(points), roundedRoute(points, .8), x, y, targetAngle + Math.PI);
}

function paintEdgePaths(edge, path, echo, x, y, angle) {
  const [highlight, , trace, line] = edge.paths;
  highlight.setAttribute("d", path);
  trace.setAttribute("d", echo);
  line.setAttribute("d", path);
  edge.arrow = { x, y, angle: angle * 180 / Math.PI };
  paintArrowhead(edge);
}

function paintArrowhead({ arrow, paths }) {
  if (!arrow) return;
  const { x, y, angle } = arrow;
  // Share one ink size at the current zoom. Limit world-space reach on dense graphs.
  const size = Math.min(arrowHeadSize / camera.scale, 22);
  for (const tip of [paths[1], paths[4]]) {
    tip.setAttribute("d", "M-.88 .48 Q-.48 .20 0 0 L-.86 -.49");
    tip.setAttribute("transform", `translate(${x} ${y}) rotate(${angle}) scale(${size})`);
  }
}

function paintNodes() {
  for (const node of layout.nodes) {
    node.group.setAttribute("transform", `translate(${node.x},${node.y})`);
    node.label.style.transform = `translate(${node.x}px, ${node.y}px) translate(-50%, -50%)`;
  }
  const index = obstacleIndex(layout.nodes);
  for (const edge of layout.edges) paintEdge(edge, index);
}

function settle(iterations = 42) {
  cancelAnimationFrame(frame);
  if (window.matchMedia("(prefers-reduced-motion: reduce)").matches) {
    separateNodes(40);
    paintNodes();
    return;
  }
  const tick = () => {
    forceStep(.48);
    separateNodes(iterations <= 1 && !gesture?.node ? 40 : 6);
    paintNodes();
    if (--iterations > 0 || gesture?.node) frame = requestAnimationFrame(tick);
  };
  frame = requestAnimationFrame(tick);
}

function paintCamera() {
  world.setAttribute("transform", `translate(${camera.x},${camera.y}) scale(${camera.scale})`);
  labelWorld.style.transform = `translate(${camera.x}px, ${camera.y}px) scale(${camera.scale})`;
  for (const edge of layout.edges) paintArrowhead(edge);
}

function fitGraph(initial = false) {
  if (!layout) return;
  const box = stage.getBoundingClientRect();
  const route = layout.edges.flatMap((edge) => edge.routePoints || []);
  const left = Math.min(...layout.nodes.map((n) => n.x - n.rx), ...route.map(([x]) => x));
  const right = Math.max(...layout.nodes.map((n) => n.x + n.rx), ...route.map(([x]) => x));
  const top = Math.min(...layout.nodes.map((n) => n.y - n.ry), ...route.map(([, y]) => y));
  const bottom = Math.max(...layout.nodes.map((n) => n.y + n.ry), ...route.map(([, y]) => y));
  const narrow = box.width < 600;
  const margin = narrow ? 18 : 55;
  const leftMargin = narrow && layout.portrait ? 62 : margin;
  const scale = Math.min(1.32, (box.width - leftMargin - margin) / (right - left),
    (box.height - 72) / (bottom - top));
  camera.scale = Math.max(.001, scale);
  camera.x = (box.width + leftMargin - margin) / 2 - (left + right) / 2 * camera.scale;
  camera.y = (box.height - 15) / 2 - (top + bottom) / 2 * camera.scale;
  camera.fitted = true;
  camera.overview = initial;
  paintCamera();
}

function zoom(factor, x = stage.clientWidth / 2, y = stage.clientHeight / 2) {
  zoomAbout(camera.scale * factor, (x - camera.x) / camera.scale, (y - camera.y) / camera.scale, x, y);
}

function zoomAbout(scale, worldX, worldY, x, y) {
  camera.scale = Math.max(Math.min(minZoom, camera.scale), Math.min(maxZoom, scale));
  camera.x = x - worldX * camera.scale;
  camera.y = y - worldY * camera.scale;
  camera.fitted = false;
  paintCamera();
}

function reveal(id) {
  if (!camera.fitted) return;
  const node = layout.nodeMap.get(id);
  if (!node) return;
  const x = camera.x + node.x * camera.scale;
  const y = camera.y + node.y * camera.scale;
  const width = stage.clientWidth;
  const height = stage.clientHeight;
  if (x < 55 || x > width - 55 || y < 40 || y > height - 55) {
    camera.x = width / 2 - node.x * camera.scale;
    camera.y = height / 2 - node.y * camera.scale;
    paintCamera();
  }
}

function updateHighlights() {
  const neighbors = new Set([selected]);
  for (const edge of layout.edges) {
    const incoming = Boolean(selected && edge.target === selected);
    const outgoing = Boolean(selected && edge.source === selected);
    edge.group.classList.toggle("is-incoming", incoming);
    edge.group.classList.toggle("is-outgoing", outgoing);
    edge.group.classList.toggle("is-muted", Boolean(selected && !incoming && !outgoing));
    if (incoming || outgoing) {
      neighbors.add(edge.source);
      neighbors.add(edge.target);
      edgeLayer.append(edge.group);
    }
  }
  for (const node of layout.nodes) {
    const muted = Boolean(selected && !neighbors.has(node.id));
    node.group.classList.toggle("is-selected", node.id === selected);
    node.group.classList.toggle("is-muted", muted);
    node.label.classList.toggle("is-muted", muted);
    node.group.setAttribute("aria-pressed", String(node.id === selected));
  }
}

function connectionList(edges, direction) {
  const incoming = direction === "incoming";
  const accent = incoming ? "var(--blue)" : "var(--yellow)";
  const title = html("h3", `${incoming ? "Incoming" : "Outgoing"} · ${edges.length}`);
  const mark = html("span", null, "direction-mark");
  mark.style.setProperty("--direction", accent);
  title.prepend(mark);
  inspectorBody.append(title);
  if (!edges.length) {
    inspectorBody.append(html("p", "None in this view.", "small"));
    return;
  }
  const list = html("ul", null, "connections");
  list.style.setProperty("--direction", accent);
  for (const edge of edges) {
    const id = incoming ? edge.source : edge.target;
    const entry = html("li");
    const button = html("button", titleFor(id));
    button.type = "button";
    button.append(html("small", relationLabels[edge.relation] || edge.relation.replaceAll("_", " "), "connection-rel"));
    button.addEventListener("click", () => selectNode(id));
    entry.append(button);
    list.append(entry);
  }
  inspectorBody.append(list);
}

function renderInspector(id) {
  const item = evidence.get(id);
  const annotation = annotations[id] || {};
  const label = item.kind === "fact" ? item.role : item.kind === "inference" ? "Proof step" :
    roots.has(id) ? "Theorem" : item.type || item.kind;
  bySelector("#node-kind").textContent = label[0].toUpperCase() + label.slice(1);
  inspectorBody.replaceChildren(html("h2", titleFor(id)));
  const formula = shortLabel(id)[1];
  if (formula) {
    const panel = html("div", null, "formula-panel");
    drawMath(panel, formula, true);
    inspectorBody.append(panel);
  }
  if (annotation.summary) {
    for (const paragraph of annotation.summary.split(/\n\s*\n/)) {
      inspectorBody.append(html("p", paragraph));
    }
  }
  if (item.statement && item.statement !== annotation.summary) {
    inspectorBody.append(html("p", item.statement));
  }
  if (annotation.why_here) {
    inspectorBody.append(html("h3", "Role in the proof"), html("p", annotation.why_here));
  }
  if (annotation.statement_latex) {
    const statement = html("details");
    statement.append(html("summary", "Full statement"));
    const panel = html("div", null, "formula-panel");
    drawMath(panel, annotation.statement_latex, true);
    statement.append(panel);
    inspectorBody.append(statement);
  }

  connectionList(layout.edges.filter((edge) => edge.target === id), "incoming");
  connectionList(layout.edges.filter((edge) => edge.source === id), "outgoing");

  const related = (annotation.concepts || []).map((key) => concepts.get(key)).filter(Boolean);
  if (related.length) {
    inspectorBody.append(html("h3", "Concepts"));
    const list = html("ul", null, "concept-list");
    for (const concept of related) {
      const entry = html("li", concept.title);
      if (concept.summary) entry.title = concept.summary;
      list.append(entry);
    }
    inspectorBody.append(list);
  }
  inspectorBody.append(html("h3", "Lean evidence"));
  if (item.name) inspectorBody.append(html("code", item.name));
  const nearbyEvidence = new Set([id]);
  for (const [other, representative] of Object.entries(layout.collapsed)) {
    if (representative === id) nearbyEvidence.add(other);
  }
  const refs = new Set(proof.edges
    .filter((edge) => nearbyEvidence.has(edge.source) && referenceRelations.has(edge.relation))
    .map((edge) => edge.target));
  if (refs.size) {
    const list = html("ul", null, "concept-list");
    for (const target of refs) {
      const declaration = evidence.get(target);
      const url = sourceUrl(declaration?.evidence?.url);
      const li = html("li", url ? null : titleFor(target));
      if (url) {
        const link = html("a", titleFor(target));
        link.href = url;
        link.target = "_blank";
        link.rel = "noopener";
        li.append(link);
      }
      list.append(li);
    }
    inspectorBody.append(list);
  }
  const url = sourceUrl(item.evidence?.url);
  if (url) {
    const link = html("a", "Open Lean source", "source-anchor");
    link.href = url;
    link.target = "_blank";
    link.rel = "noopener";
    inspectorBody.append(link);
  }
  if (item.lean) {
    const details = html("details");
    details.append(html("summary", "Lean excerpt"), html("pre", item.lean));
    inspectorBody.append(details);
  }
  inspectorBody.scrollTop = 0;
}

function selectNode(id) {
  if (!layout.nodeMap.has(id)) return;
  selected = id;
  inspector.hidden = false;
  updateHighlights();
  renderInspector(id);
  requestAnimationFrame(() => reveal(id));
}

function clearSelection(restoreFocus = false) {
  const previous = selected;
  if (!previous) return;
  selected = null;
  inspector.hidden = true;
  updateHighlights();
  if (restoreFocus) layout.nodeMap.get(previous)?.group.focus({ preventScroll: true });
}

function pointerPosition(event) {
  const box = diagram.getBoundingClientRect();
  return { x: event.clientX - box.left, y: event.clientY - box.top };
}

function singlePointer(pointerId, { x, y }, node = null, moved = false) {
  return { x, y, pointerId, node, moved, cameraX: camera.x, cameraY: camera.y,
    nodeX: node?.x, nodeY: node?.y };
}

function pinchPosition() {
  const [a, b] = touchPoints.values();
  return {
    x: (a.x + b.x) / 2,
    y: (a.y + b.y) / 2,
    distance: Math.max(1, Math.hypot(a.x - b.x, a.y - b.y)),
  };
}

diagram.addEventListener("pointerdown", (event) => {
  if (!layout || event.button !== 0) return;
  const touch = event.pointerType === "touch";
  if (touchPoints.size === 2 || (gesture && !(touch && touchPoints.size === 1))) return;
  const point = pointerPosition(event);
  diagram.setPointerCapture(event.pointerId);
  if (touch) {
    touchPoints.set(event.pointerId, point);
    if (touchPoints.size === 2) {
      finishGesture(true);
      const { x, y, distance } = pinchPosition();
      pinch = { distance, scale: camera.scale, worldX: (x - camera.x) / camera.scale,
        worldY: (y - camera.y) / camera.scale };
      diagram.classList.add("is-dragging");
      return;
    }
  }
  const id = event.target.closest("[data-node]")?.dataset.node;
  gesture = singlePointer(event.pointerId, point, layout.nodeMap.get(id));
});

diagram.addEventListener("pointermove", (event) => {
  const trackedTouch = touchPoints.has(event.pointerId);
  if (!trackedTouch && gesture?.pointerId !== event.pointerId) return;
  const point = pointerPosition(event);
  if (trackedTouch) {
    touchPoints.set(event.pointerId, point);
    if (pinch) {
      const { x, y, distance } = pinchPosition();
      zoomAbout(pinch.scale * distance / pinch.distance, pinch.worldX, pinch.worldY, x, y);
      return;
    }
  }
  const dx = point.x - gesture.x;
  const dy = point.y - gesture.y;
  if (!gesture.moved && Math.hypot(dx, dy) < 4) return;
  if (!gesture.moved) {
    gesture.moved = true;
    diagram.classList.add("is-dragging");
    if (gesture.node) settle();
  }
  if (gesture.node) {
    const n = gesture.node;
    n.pinned = true;
    n.x = gesture.nodeX + dx / camera.scale;
    n.y = gesture.nodeY + dy / camera.scale;
    separateNodes(8);
    paintNodes();
  } else {
    camera.x = gesture.cameraX + dx;
    camera.y = gesture.cameraY + dy;
    camera.fitted = false;
    paintCamera();
  }
});

function finishGesture(cancelled) {
  const { node, moved } = gesture;
  gesture = null;
  diagram.classList.remove("is-dragging");
  if (node && moved) {
    node.pinned = false;
    node.ax = node.x;
    node.ay = node.y;
    settle();
  } else if (!cancelled && !moved) {
    if (node) selectNode(node.id);
    else clearSelection();
  }
}

function endGesture(event, cancelled) {
  if (touchPoints.delete(event.pointerId) && pinch) {
    pinch = null;
    const [[pointerId, point]] = touchPoints;
    gesture = singlePointer(pointerId, point, null, true);
    return;
  }
  if (gesture?.pointerId === event.pointerId) finishGesture(cancelled);
}

diagram.addEventListener("pointerup", (event) => endGesture(event, false));
diagram.addEventListener("pointercancel", (event) => endGesture(event, true));
diagram.addEventListener("lostpointercapture", (event) => {
  if (event.target === diagram) endGesture(event, true);
});
diagram.addEventListener("wheel", (event) => {
  if (!layout) return;
  event.preventDefault();
  const { x, y } = pointerPosition(event);
  zoom(Math.exp(-Math.max(-140, Math.min(140, event.deltaY)) * .0018), x, y);
}, { passive: false });

bySelector("#zoom-in").addEventListener("click", () => { if (layout) zoom(1.23); });
bySelector("#zoom-out").addEventListener("click", () => { if (layout) zoom(1 / 1.23); });
bySelector("#fit").addEventListener("click", () => fitGraph());
bySelector("#close-inspector").addEventListener("click", () => clearSelection(true));

const settings = bySelector("#settings");
const viewSettings = bySelector("#view-settings");
const settingsButton = bySelector("#settings-button");
function showSettings(open) {
  settings.hidden = !open;
  settingsButton.setAttribute("aria-expanded", String(open));
}
settingsButton.addEventListener("click", () => showSettings(settings.hidden));
document.addEventListener("pointerdown", (event) => {
  if (!settings.hidden && !settings.contains(event.target) && !settingsButton.contains(event.target)) {
    showSettings(false);
  }
});
document.addEventListener("keydown", (event) => {
  if (event.key !== "Escape") return;
  if (!settings.hidden) { showSettings(false); settingsButton.focus(); }
  else if (selected) clearSelection(true);
});
bySelector("#formula-toggle").addEventListener("change", (event) => {
  stage.classList.toggle("hide-formulas", !event.target.checked);
});
const flowToggle = bySelector("#downward-flow");
flowToggle.checked = downwardFlow;
flowToggle.addEventListener("change", () => {
  downwardFlow = flowToggle.checked;
  const url = new URL(location.href);
  if (downwardFlow) url.searchParams.set("layout", "downward");
  else url.searchParams.delete("layout");
  history.replaceState(history.state, "", url);
  if (!layout) return;
  createLayout();
  updateHighlights();
  fitGraph(true);
  if (selected) reveal(selected);
});
bySelector("#reset-layout").addEventListener("click", () => {
  if (!proof) return;
  createLayout();
  updateHighlights();
  fitGraph(true);
});
viewSettings.addEventListener("change", (event) => {
  if (!proof || !views[event.target.value]) return;
  mode = event.target.value;
  createLayout();
  if (selected && Object.hasOwn(layout.collapsed, selected)) selected = layout.collapsed[selected];
  if (selected && !layout.nodeMap.has(selected)) clearSelection();
  if (selected) renderInspector(selected);
  updateHighlights();
  fitGraph(true);
});

portraitLayout.addEventListener("change", () => {
  if (!layout) return;
  createLayout();
  updateHighlights();
  fitGraph(true);
  if (selected) reveal(selected);
});

new ResizeObserver(() => {
  if (!layout || !camera.fitted) return;
  fitGraph(camera.overview);
  if (selected) reveal(selected);
}).observe(stage);

function acceptGraph(document) {
  if (document?.schema_version !== 1 || !Array.isArray(document.nodes) || !Array.isArray(document.edges)) {
    throw new Error("Choose a version 1 proof graph JSON file.");
  }
  const concepts = document.concepts || [];
  const records = new Map([...document.nodes, ...concepts, ...(document.groups || [])]
    .map((node) => [node.id, node]));
  const available = document.views || (document.view ? { projection: document.view } :
    { references: { label: "Lean references", nodes: document.nodes.map((node) => node.id), edges: document.edges } });
  const supported = Object.create(null);
  for (const [name, view] of Object.entries(available)) {
    if (!Array.isArray(view.nodes) || !Array.isArray(view.edges) || !view.nodes.length) {
      throw new Error("A graph view is empty or malformed.");
    }
    const present = new Set(view.nodes);
    if (present.size !== view.nodes.length || view.nodes.some((id) => !records.has(id)) ||
        view.edges.some((edge) => !present.has(edge.source) || !present.has(edge.target) ||
          typeof edge.relation !== "string")) {
      throw new Error("A graph view refers to an unknown or duplicate node.");
    }
    supported[name] = view;
  }
  const rootIds = document.roots || [document.root];
  if (!Object.keys(supported).length || !rootIds.length || rootIds.some((id) => !records.has(id))) {
    throw new Error("The graph needs at least one root and one view.");
  }
  return { records, supported, rootIds, concepts };
}

async function showGraph(data) {
  const { records, supported, rootIds, concepts: graphConcepts } = acceptGraph(data);
  await document.fonts?.load('700 19px "Notebook Hand"').catch(() => {});
  proof = data;
  evidence = records;
  views = supported;
  annotations = Object.assign(Object.create(null), data.annotations);
  concepts = new Map(graphConcepts.map((concept) => [concept.id, concept]));
  roots = new Set(rootIds);
  mode = views[data.default_view] ? data.default_view : Object.keys(views)[0];
  selected = null;
  inspector.hidden = true;
  viewSettings.replaceChildren(html("legend", "Show"));
  for (const [id, view] of Object.entries(views)) {
    const input = html("input");
    input.type = "radio";
    input.name = "detail";
    input.value = id;
    input.checked = id === mode;
    const label = html("label");
    label.append(input, ` ${view.label || id}`);
    viewSettings.append(label);
  }
  const name = data.title || data.source?.title || (rootIds.length === 1 ? titleFor(rootIds[0]) : "Proof graph");
  bySelector("#graph-title").textContent = name;
  document.title = name === "Proof graph" ? name : `${name} · Proof graph`;
  const link = bySelector("#graph-source");
  const url = sourceUrl(data.source?.url) || sourceUrl(evidence.get(rootIds[0]).evidence?.url);
  link.hidden = !url;
  if (url) link.href = url;
  createLayout();
  fitGraph(true);
  bySelector("#canvas-notice").hidden = true;
}

function showLoadError(error) {
  const notice = bySelector("#canvas-notice");
  notice.textContent = error.message;
  notice.hidden = false;
}

bySelector("#open-graph").addEventListener("change", async ({ target }) => {
  const file = target.files[0];
  target.value = "";
  if (!file) return;
  try {
    await showGraph(JSON.parse(await file.text()));
    showSettings(false);
  } catch (error) {
    showLoadError(error);
  }
});

async function start() {
  try {
    const response = await fetch("proof.json");
    if (!response.ok) throw new Error("The default proof graph could not be loaded. You can open a JSON file in Graph settings.");
    await showGraph(await response.json());
  } catch (error) {
    showLoadError(error);
  }
}

start();
