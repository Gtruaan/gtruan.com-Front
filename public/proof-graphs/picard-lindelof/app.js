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
const useProofRanks = diagram.hasAttribute("data-proof-ranks");

const proofRelations = new Set(["premise_of", "produces", "concludes"]);
const referenceRelations = new Set(["applies", "summarizes", "unfolds"]);
const relationLabels = {
  premise_of: "Premise",
  produces: "Result",
  concludes: "Concludes the theorem",
  supports: "Result used as a premise",
  applies: "Applied Lean result",
  summarizes: "Lean source summarized",
  unfolds: "Definition unfolded",
};
const overviewLabels = {
  "step:curve-space": ["Complete curve space", "\\mathcal X\\text{ complete}"],
  "step:picard-self-map": ["Picard operator", "T:\\mathcal X\\to\\mathcal X"],
  "step:factorial-bound": ["Factorial estimate", "q_n=\\dfrac{(KR)^n}{n!}"],
  "step:contracting-iterate": ["Contracting iterate", "q_n<1"],
  "step:fixed-curve": ["Fixed point", "T\\alpha=\\alpha"],
  "step:integral-equation": ["Integral equation", "g(t)=x+\\int_{t_0}^{t} f(s,g(s))\\,ds"],
  "step:ode-solution": ["Differentiate the integral", "g'_I(t)=f(t,g(t))"],
  "step:trajectory-comparison": ["Grönwall estimate", "d(f(t),g(t))\\le\\delta e^{K(t-a)}"],
  "step:one-sided-principle": ["One-sided uniqueness", "d(f(t),g(t))=0"],
  "step:split-interval": ["Split at the initial time", "[a,b]=[a,t_0]\\cup[t_0,b]"],
  "step:forward-agreement": ["Forward agreement", "f=g\\text{ on }[t_0,b]"],
  "step:backward-agreement": ["Backward agreement", "f=g\\text{ on }[a,t_0]"],
  "step:agreement-on-interval": ["Join the two halves", "f=g\\text{ on }[a,b]"],
  "fact:state-space": ["Complete state space", "t_0\\in I"],
  "fact:existence-hypotheses": ["Field and interval bounds", "L\\,R\\le a-r"],
  "fact:uniqueness-hypotheses": ["Uniqueness hypotheses", "t_0\\in(a,b)"],
  "fact:same-initial-value": ["Common initial value", "f(t_0)=g(t_0)"],
};
const anchors = {
  "step:curve-space": [-520, -118],
  "step:picard-self-map": [-500, 45],
  "step:factorial-bound": [-540, 216],
  "step:contracting-iterate": [-375, 262],
  "step:fixed-curve": [-278, 153],
  "step:integral-equation": [-352, -14],
  "step:ode-solution": [-273, -177],
  "fact:state-space": [-467, -266],
  "fact:existence-hypotheses": [-648, 70],
  "step:trajectory-comparison": [250, 268],
  "step:one-sided-principle": [403, 205],
  "step:split-interval": [567, -4],
  "step:forward-agreement": [398, -117],
  "step:backward-agreement": [408, 48],
  "step:agreement-on-interval": [260, -196],
  "fact:uniqueness-hypotheses": [629, -147],
  "fact:same-initial-value": [576, 149],
};
const prominent = new Set(["step:fixed-curve", "step:trajectory-comparison", "step:picard-self-map"]);
const labelWidthRatio = 1.50;
const labelHeightRatio = 1.16;
const nodeGap = 25;
const linkedNodeGap = 46;
const minZoom = .19;
const maxZoom = 3.3;
const touchPoints = new Map();

let proof;
let evidence;
let annotations;
let concepts;
let roots;
let flow;
let layout;
let selected = null;
let mode = bySelector('input[name="detail"]:checked').value;
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
  return annotations[id]?.title || item?.name || id;
}

function shortLabel(id) {
  if (useProofRanks) return [titleFor(id), annotations[id]?.compact_latex];
  const rootIndex = roots.indexOf(id);
  if (rootIndex === 0) {
    return ["Existence of a solution", "\\begin{gathered}\\exists\\,g:\\ g(t_0)=x,\\\\g'_I(t)=f(t,g(t))\\end{gathered}"];
  }
  if (rootIndex === 1) return ["Uniqueness of solutions", "f=g\\text{ on }[a,b]"];
  return overviewLabels[id] || [titleFor(id), annotations[id]?.compact_latex];
}

function hash(value) {
  let n = 2166136261;
  for (const c of value) n = Math.imul(n ^ c.codePointAt(0), 16777619);
  return n >>> 0;
}

function noise(seed, index) {
  return ((Math.imul(seed ^ Math.imul(index + 97, 2654435761), 2246822519) >>> 0) % 4096) / 4096 - .5;
}

function buildProjection(detail) {
  const producer = new Map();
  for (const edge of flow) {
    if (edge.relation === "produces") producer.set(edge.target, edge.source);
  }
  const idFor = (id) => detail === "overview" ? producer.get(id) || id : id;
  const nodes = [...evidence.values()].filter((node) => {
    if (roots.includes(node.id)) return true;
    if (node.kind === "declaration") return detail === "references";
    return detail !== "overview" || node.kind === "inference" || node.role === "assumption";
  });
  const mapped = new Map();
  const addLink = (source, target, relation, via) => {
    if (source === target) return;
    const key = JSON.stringify([source, target, relation]);
    if (!mapped.has(key)) mapped.set(key, { source, target, relation, via: [] });
    if (via) mapped.get(key).via.push(via);
  };
  for (const edge of flow) {
    const source = idFor(edge.source);
    const relation = edge.relation === "premise_of" && source !== edge.source ? "supports" : edge.relation;
    addLink(source, idFor(edge.target), relation, source !== edge.source ? edge.source : null);
  }
  if (detail === "references") {
    for (const edge of proof.edges) {
      // Show the cited declaration flowing into the step, with its original relation preserved.
      if (referenceRelations.has(edge.relation)) addLink(edge.target, edge.source, edge.relation);
    }
  }
  return { nodes, links: [...mapped.values()], producer };
}

function positionFor(node, projection) {
  const rootIndex = roots.indexOf(node.id);
  if (rootIndex >= 0) return [rootIndex === 0 ? -107 : 104, -82];
  if (anchors[node.id]) return anchors[node.id];
  const source = projection.producer.get(node.id);
  if (source && anchors[source]) {
    const [x, y] = anchors[source];
    const consumer = flow.find((edge) => edge.source === node.id && anchors[edge.target]);
    const target = consumer && anchors[consumer.target];
    return target ? [(x + target[0]) / 2 + 8, (y + target[1]) / 2 + 20] : [x * .83, y - 58];
  }
  const adjacent = projection.links.find((link) => link.source === node.id && anchors[link.target]);
  if (adjacent) {
    const [x, y] = anchors[adjacent.target];
    return [x * 1.16, y * 1.12 + (y > 0 ? 60 : -60)];
  }
  const angle = hash(node.id) % 360 * Math.PI / 180;
  return [Math.cos(angle) * 640, Math.sin(angle) * 325];
}

function rankPositions({ nodes, links }) {
  const consumers = new Map(nodes.map((node) => [node.id, []]));
  for (const { source, target } of links) consumers.get(source).push(target);
  const rootRanks = roots.map((root) => {
    const ranks = new Map([[root, 0]]);
    function rank(id) {
      if (ranks.has(id)) return ranks.get(id);
      const next = consumers.get(id).map(rank);
      const depth = next.length ? 1 + Math.max(...next) : -Infinity;
      ranks.set(id, depth);
      return depth;
    }
    for (const { id } of nodes) rank(id);
    return ranks;
  });

  const lanes = new Map();
  const shared = new Set();
  for (const { id } of nodes) {
    const distances = rootRanks.map((ranks) => ranks.get(id));
    const depth = Math.max(...distances);
    const branch = distances.filter(Number.isFinite).length > 1 ? -1 : distances.indexOf(depth);
    if (branch === -1) shared.add(id);
    const column = [branch, Number.isFinite(depth) ? depth : 0];
    const key = column.join("/");
    if (!lanes.has(key)) lanes.set(key, { column, members: [] });
    lanes.get(key).members.push(id);
  }

  const positions = new Map();
  const sharedLane = [];
  const twoBranches = roots.length === 2;
  for (const { column: [branch, depth], members } of lanes.values()) {
    if (branch === -1) {
      sharedLane.push(...members);
      continue;
    }
    const branchDirection = branch ? 1 : -1;
    const x = twoBranches ? branchDirection * (116 + depth * 80) : -depth * 121;
    const stagger = depth % 2 ? 32 : -32;
    const y = twoBranches ? Math.sin(depth * 1.08) * 160 + stagger : stagger;
    members.forEach((id, i) => positions.set(id, [x, y + (i - (members.length - 1) / 2) * 151]));
  }
  if (sharedLane.length) {
    const outside = Math.min(...Array.from(positions.values(), ([, y]) => y)) - 140;
    sharedLane.forEach((id, i) => positions.set(id, [(i - (sharedLane.length - 1) / 2) * 151, outside]));
  }
  return { positions, shared };
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

function createNode(item, projection, portrait) {
  const isRoot = roots.includes(item.id);
  const [x, y] = projection.positions?.get(item.id) || positionFor(item, projection);
  const [ax, ay] = portrait ? [y * .82, x] : [x, y];
  const [title, formula] = shortLabel(item.id);
  const rx = isRoot ? 93 : prominent.has(item.id) ? 72 :
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
    id: item.id, item, isRoot, rx, ry, baseRx: rx, baseRy: ry, ax, ay,
    x: ax, y: ay, vx: 0, vy: 0, group, pinned: false,
    outline, echo, label, stack, titleElement, math,
  };
}

function createEdge(link, nodes) {
  const group = svg("g", { class: referenceRelations.has(link.relation) ? "edge is-reference" : "edge" });
  const paths = ["edge-highlight", "edge-highlight-tip", "edge-echo", "edge-line", "edge-tip"].map(
    (kind) => svg("path", { class: kind }),
  );
  group.append(...paths);
  edgeLayer.append(group);
  return { ...link, a: nodes.get(link.source), b: nodes.get(link.target), group, paths,
    bend: noise(hash(link.source + link.target), 1) * 40 };
}

function createLayout() {
  cancelAnimationFrame(frame);
  gesture = null;
  pinch = null;
  touchPoints.clear();
  diagram.classList.remove("is-dragging");
  const projection = buildProjection(mode);
  if (useProofRanks) Object.assign(projection, rankPositions(projection));
  const portrait = portraitLayout.matches;
  nodeLayer.replaceChildren();
  edgeLayer.replaceChildren();
  labelWorld.replaceChildren();
  const nodes = projection.nodes.map((n) => createNode(n, projection, portrait));
  const nodeMap = new Map(nodes.map((node) => [node.id, node]));
  const edges = projection.links.map((link) => {
    const edge = createEdge(link, nodeMap);
    edge.avoidNodes = projection.shared?.has(link.source) && link.relation === "premise_of" &&
      edge.a.item.role === "assumption";
    return edge;
  });
  const neighbors = new Map(nodes.map((node) => [node.id, new Set()]));
  for (const edge of edges) {
    neighbors.get(edge.source).add(edge.target);
    neighbors.get(edge.target).add(edge.source);
  }
  layout = { nodes, nodeMap, edges, neighbors, producer: projection.producer, portrait };
  fitLabels(nodes);
  for (let i = 0; i < 160; i++) forceStep(.36 + .64 * (1 - i / 160));
  separateNodes(40);
  for (const node of nodes) node.vx = node.vy = 0;
  paintNodes();
  bySelector("#graph-count").textContent = `${nodes.length} nodes · ${edges.length} arrows`;
  const currentLayout = layout;
  document.fonts?.ready.then(() => {
    if (layout !== currentLayout) return;
    fitLabels(nodes);
    separateNodes(40);
    paintNodes();
    if (camera.fitted) fitGraph(camera.overview);
  });
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
      math.style.fontSize = "12px";
      if (math.offsetWidth > width) {
        math.style.fontSize = `${Math.max(9, 12 * (width - 1) / math.offsetWidth)}px`;
      }
      if (math.offsetWidth > width) {
        node.rx = Math.ceil((math.offsetWidth + 6) / labelWidthRatio);
        continue;
      }
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
        if (distance > a.rx + b.rx + gap) continue;
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
    const pull = roots.includes(n.id) ? .18 : .10;
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

function routeEdge({ a, b }, nodes) {
  const obstacles = nodes.filter((node) => node !== a && node !== b)
    .map(({ x, y, rx, ry }) => ({ cx: x, cy: y, rx: rx + 17, ry: ry + 17 }));
  const start = [a.x, a.y];
  const end = [b.x, b.y];
  if (segmentClear(start, end, obstacles)) return [start, end];

  const corners = obstacles.flatMap(({ cx, cy, rx, ry }) => [
    [cx - rx, cy - ry], [cx + rx, cy - ry], [cx - rx, cy + ry], [cx + rx, cy + ry],
  ]);
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
      if (cost >= costs[i] || !segmentClear(points[current], points[i], obstacles)) continue;
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
    const fraction = Math.min(.35, 8 / distance);
    return [x + (u - x) * fraction, y + (v - y) * fraction];
  };
  let path = `M${coords(points[0])}`;
  for (let i = 1; i < points.length - 1; i++) {
    const corner = points[i];
    path += ` L${coords(shorten(corner, points[i - 1]))} Q${coords(corner)} ${coords(shorten(corner, points[i + 1]))}`;
  }
  return `${path} L${coords(points.at(-1))}`;
}

function paintRoutedEdge(edge, nodes) {
  const points = routeEdge(edge, nodes);
  if (!points) return false;
  const angleTo = ([x, y], [u, v]) => Math.atan2(v - y, u - x);
  const sourceAngle = angleTo(points[0], points[1]);
  const targetAngle = angleTo(points.at(-1), points.at(-2));
  points[0] = pointOutsideNode(edge.a, sourceAngle);
  points[points.length - 1] = pointOutsideNode(edge.b, targetAngle);
  const [x, y] = points.at(-1);
  const [u, v] = points.at(-2);
  paintEdgePaths(edge.paths, roundedRoute(points), roundedRoute(points, .8),
    x, y, targetAngle + Math.PI, Math.hypot(x - u, y - v));
  return true;
}

function paintEdge(edge) {
  const { a, b, paths, avoidNodes } = edge;
  const angle = Math.atan2(b.y - a.y, b.x - a.x);
  const span = Math.hypot(b.x - a.x, b.y - a.y);
  const gap = span - ellipseRadius(a, angle) - ellipseRadius(b, angle + Math.PI) - 8;
  if (gap < 3) {
    for (const path of paths) path.setAttribute("d", "");
    return;
  }
  if (avoidNodes && paintRoutedEdge(edge, layout.nodes)) return;
  const maxBend = gap * .33;
  const bend = Math.max(-maxBend, Math.min(maxBend, edge.bend));
  const drift = Math.min(.23, Math.max(-.23, bend / span));
  const [x0, y0] = pointOutsideNode(a, angle + drift);
  const [x1, y1] = pointOutsideNode(b, angle + Math.PI - drift);
  const ox = -Math.sin(angle) * bend;
  const oy = Math.cos(angle) * bend;
  const cx = (x0 + x1) / 2 + ox;
  const cy = (y0 + y1) / 2 + oy;
  const path = `M${x0} ${y0} Q${cx} ${cy} ${x1} ${y1}`;
  const echo = `M${x0} ${y0 + 1.1} Q${cx + 1.5} ${cy - 1.9} ${x1} ${y1 + .8}`;
  const tipAngle = Math.atan2(y1 - cy, x1 - cx);
  paintEdgePaths(paths, path, echo, x1, y1, tipAngle, Math.hypot(x1 - x0, y1 - y0));
}

function paintEdgePaths(paths, path, echo, x1, y1, tipAngle, space) {
  const wing = (side, length) => [
    x1 - Math.cos(tipAngle + side) * length, y1 - Math.sin(tipAngle + side) * length,
  ];
  const headSize = Math.min(10.2, space * .36);
  const [lx, ly] = wing(-.49, headSize);
  const [rx, ry] = wing(.52, headSize * .93);
  const head = `M${lx} ${ly} Q${(lx + x1) / 2} ${(ly + y1) / 2 - .45} ${x1} ${y1} L${rx} ${ry}`;
  [path, head, echo, path, head].forEach((value, i) => paths[i].setAttribute("d", value));
}

function paintNodes() {
  for (const node of layout.nodes) {
    node.group.setAttribute("transform", `translate(${node.x},${node.y})`);
    node.label.style.transform = `translate(${node.x}px, ${node.y}px) translate(-50%, -50%)`;
  }
  for (const edge of layout.edges) paintEdge(edge);
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
}

function fitGraph(initial = false) {
  if (!layout) return;
  const box = stage.getBoundingClientRect();
  const left = Math.min(...layout.nodes.map((n) => n.x - n.rx));
  const right = Math.max(...layout.nodes.map((n) => n.x + n.rx));
  const top = Math.min(...layout.nodes.map((n) => n.y - n.ry));
  const bottom = Math.max(...layout.nodes.map((n) => n.y + n.ry));
  const narrow = box.width < 600;
  const margin = narrow ? 18 : 55;
  const scale = Math.min(1.32, (box.width - 2 * margin) / (right - left),
    (box.height - 72) / (bottom - top));
  camera.scale = Math.max(initial && narrow && !layout.portrait ? .64 : minZoom, scale);
  camera.x = box.width / 2 - (left + right) / 2 * camera.scale;
  camera.y = (box.height - 15) / 2 - (top + bottom) / 2 * camera.scale;
  camera.fitted = true;
  camera.overview = initial;
  paintCamera();
}

function zoom(factor, x = stage.clientWidth / 2, y = stage.clientHeight / 2) {
  zoomAbout(camera.scale * factor, (x - camera.x) / camera.scale, (y - camera.y) / camera.scale, x, y);
}

function zoomAbout(scale, worldX, worldY, x, y) {
  camera.scale = Math.max(minZoom, Math.min(maxZoom, scale));
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
    button.append(html("small", relationLabels[edge.relation], "connection-rel"));
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
    roots.includes(id) ? "Theorem" : item.type;
  bySelector("#node-kind").textContent = label[0].toUpperCase() + label.slice(1);
  inspectorBody.replaceChildren(html("h2", titleFor(id)));
  const formula = shortLabel(id)[1];
  if (formula) {
    const panel = html("div", null, "formula-panel");
    drawMath(panel, formula, true);
    inspectorBody.append(panel);
  }
  if (annotation.summary) inspectorBody.append(html("p", annotation.summary));
  if (item.statement && item.statement !== annotation.summary) {
    inspectorBody.append(html("p", item.statement));
  }
  if (annotation.why_here) {
    inspectorBody.append(html("h3", "Role in the proof"), html("p", annotation.why_here));
  }
  if (mode === "overview" && item.kind === "inference") {
    const result = flow.find((edge) => edge.source === id && edge.relation === "produces");
    const fact = result && evidence.get(result.target);
    if (fact?.statement) inspectorBody.append(html("h3", "Result"), html("p", fact.statement));
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
  const refs = proof.edges.filter((edge) => edge.source === id && referenceRelations.has(edge.relation));
  if (refs.length) {
    const list = html("ul", null, "concept-list");
    for (const edge of refs) {
      const declaration = evidence.get(edge.target);
      const link = html("a", titleFor(declaration.id));
      link.href = declaration.evidence.url;
      link.target = "_blank";
      link.rel = "noopener";
      const li = html("li");
      li.append(link);
      list.append(li);
    }
    inspectorBody.append(list);
  }
  if (item.evidence?.url) {
    const link = html("a", "Open source in Mathlib", "source-anchor");
    link.href = item.evidence.url;
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
bySelector("#reset-layout").addEventListener("click", () => {
  if (!proof) return;
  createLayout();
  updateHighlights();
  fitGraph(true);
});
for (const input of settings.querySelectorAll('input[name="detail"]')) {
  input.addEventListener("change", () => {
    if (!proof) return;
    mode = input.value;
    createLayout();
    if (selected && !layout.nodeMap.has(selected)) clearSelection();
    if (selected) renderInspector(selected);
    updateHighlights();
    fitGraph(true);
  });
}

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

async function start() {
  const notice = bySelector("#canvas-notice");
  try {
    const response = await fetch("proof.json");
    if (!response.ok) throw new Error("The proof data could not be loaded.");
    proof = await response.json();
    evidence = new Map(proof.nodes.map((node) => [node.id, node]));
    annotations = proof.annotations;
    concepts = new Map(proof.concepts.map((concept) => [concept.id, concept]));
    roots = proof.roots;
    flow = proof.edges.filter((edge) => proofRelations.has(edge.relation));
    await document.fonts?.load('700 19px "Notebook Hand"').catch(() => {});
    createLayout();
    fitGraph(true);
    notice.hidden = true;
  } catch (error) {
    notice.textContent = "The proof graph could not be loaded.";
    console.error(error);
  }
}

start();
