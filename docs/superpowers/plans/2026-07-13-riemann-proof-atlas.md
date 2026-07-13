# Riemann Proof Atlas Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the current embedded visualization fragment with a standalone, responsive, accessible proof atlas that clearly separates verified Lean results, active PNT-route gaps, and distant RH goals.

**Architecture:** One self-contained HTML document owns the semantic fallback, concept data, SVG relationship map, responsive styles, and hash-based interaction. A small Node.js checker validates offline independence, required concept coverage, status labels, semantic controls, and the absence of known overclaims before browser-based visual verification.

**Tech Stack:** HTML5, CSS, inline SVG, vanilla JavaScript, Node.js built-in modules, browser screenshot and interaction tooling.

## Global Constraints

- Final artifact: `/Users/luicy/.codex/visualizations/2026/05/23/019e55d5-94a4-7802-b7f0-8df5066f27b1/riemann-proof-atlas.html`.
- The artifact must work directly through `file://` without a server, framework, build tool, external JavaScript library, font download, or network resource.
- The compact view contains six core concepts and expands to the full network on demand.
- Every concept page contains plain-language intuition, a representative formula, Lean evidence, downstream impact, and an overclaim warning when applicable.
- Status values are exactly `proved`, `route`, and `frontier`; color is never the only status signal.
- PNT and RH must not be represented as proved by this project.
- The zero-free-region node may be marked proved only after the current theorem and its axioms boundary are checked.
- The layout must remain readable without horizontal scrolling at widths from 320 px upward.
- Native keyboard order, visible focus, semantic controls, and `prefers-reduced-motion` support are required.

---

### Task 1: Add an Executable Artifact Contract

**Files:**
- Create: `scripts/check_riemann_proof_atlas.mjs`
- Inspect: `formal-theorem-inventory.md`
- Inspect: `docs/zero-free-region-chain.md`
- Test target: `/Users/luicy/.codex/visualizations/2026/05/23/019e55d5-94a4-7802-b7f0-8df5066f27b1/riemann-proof-atlas.html`

**Interfaces:**
- Consumes: one HTML path from `process.argv[2]`.
- Produces: exit code `0` with `proof atlas contract: PASS`, or exit code `1` with one line per violated contract.

- [ ] **Step 1: Write the failing checker**

Create a Node script using only built-in modules. It must check the document shell, offline independence, all required concept identifiers, all three status labels, semantic node buttons, reduced-motion CSS, mobile CSS, hash routing, and prohibited project claims.

```js
import fs from "node:fs";
import path from "node:path";

const target = process.argv[2];
if (!target) {
  console.error("usage: node scripts/check_riemann_proof_atlas.mjs <html-path>");
  process.exit(2);
}

const html = fs.readFileSync(path.resolve(target), "utf8");
const required = [
  "<!doctype html>",
  "<html lang=\"zh-CN\">",
  "id=\"atlas-map\"",
  "id=\"concept-view\"",
  "data-action=\"toggle-network\"",
  "prefers-reduced-motion",
  "@media (max-width: 720px)",
  "location.hash",
  "status: \"proved\"",
  "status: \"route\"",
  "status: \"frontier\"",
  ...[
    "zeta", "zeta-tools", "three-four-one", "zero-free", "perron",
    "explicit-formula", "psi-error", "pnt", "pnt-error", "existing-pnt",
    "zero-density", "rh-error", "rh"
  ].map((id) => `id: \"${id}\"`)
];

const errors = required
  .filter((needle) => !html.toLowerCase().includes(needle.toLowerCase()))
  .map((needle) => `missing: ${needle}`);

for (const pattern of [/https?:\/\//i, /<script[^>]+src=/i, /<link[^>]+href=/i]) {
  if (pattern.test(html)) errors.push(`external resource: ${pattern}`);
}

for (const claim of ["本项目已经证明素数定理", "本项目已经证明黎曼猜想"]) {
  if (html.includes(claim)) errors.push(`prohibited claim: ${claim}`);
}

if (!/<button[^>]+class="[^"]*map-node/i.test(html)) {
  errors.push("map nodes are not semantic buttons");
}

if (errors.length) {
  console.error(errors.join("\n"));
  process.exit(1);
}

console.log("proof atlas contract: PASS");
```

- [ ] **Step 2: Run the checker against the current fragment**

Run:

```bash
node scripts/check_riemann_proof_atlas.mjs /Users/luicy/.codex/visualizations/2026/05/23/019e55d5-94a4-7802-b7f0-8df5066f27b1/riemann-proof-atlas.html
```

Expected: exit code `1`, including missing `<!doctype html>`, missing `atlas-map`, and missing concept data identifiers.

- [ ] **Step 3: Audit the status copy before implementation**

Run:

```bash
rg -n "classical_zero_free_region|Perron|explicit formula|Prime Number Theorem|Riemann" formal-theorem-inventory.md docs/zero-free-region-chain.md README.md
rg -n "sorry|admit|axiom" RiemannPNT.lean ZeroFreeRegion PrimeNumberTheorem
```

Expected: enough source evidence to classify each concept as `proved`, `route`, or `frontier`. Any ambiguous result is classified conservatively as `route` in the visualization.

- [ ] **Step 4: Commit the checker**

```bash
git add scripts/check_riemann_proof_atlas.mjs
git commit -m "test: define proof atlas artifact contract"
```

---

### Task 2: Build the Standalone Atlas and Content Model

**Files:**
- Modify: `/Users/luicy/.codex/visualizations/2026/05/23/019e55d5-94a4-7802-b7f0-8df5066f27b1/riemann-proof-atlas.html`
- Test: `scripts/check_riemann_proof_atlas.mjs`

**Interfaces:**
- Consumes: audited concept statuses from Task 1.
- Produces: `CONCEPTS`, an immutable array of concept objects; a readable no-JavaScript overview; and the `#atlas-map`, `#selection-drawer`, and `#concept-view` surfaces.

- [ ] **Step 1: Replace the fragment with a complete document shell**

The document begins with this structure and contains no external resource tags:

```html
<!doctype html>
<html lang="zh-CN">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Riemann Proof Atlas</title>
  <style>
    :root {
      color-scheme: light;
      --paper: #e8edf2;
      --paper-strong: #f5f7f8;
      --ink: #182536;
      --ink-soft: #536476;
      --navy: #233f5d;
      --verified: #2c7a68;
      --route: #a56a32;
      --frontier: #994d54;
      --rule: #9aa8b7;
      --focus: #166c9b;
    }
    * { box-sizing: border-box; }
    body { margin: 0; background: var(--paper); color: var(--ink); font-family: system-ui, sans-serif; }
    button, a { font: inherit; }
    button:focus-visible, a:focus-visible { outline: 3px solid var(--focus); outline-offset: 3px; }
    [hidden] { display: none !important; }
    .skip-link { position: absolute; left: 12px; top: -80px; }
    .skip-link:focus { top: 12px; }
  </style>
</head>
<body>
  <a class="skip-link" href="#atlas-map">跳到证明星图</a>
  <header class="site-header">
    <p>LEAN 4 · ANALYTIC NUMBER THEORY</p>
    <h1 id="atlas-title">The Riemann Proof Atlas</h1>
    <p>一张区分已证明组件、待连接路线与远期目标的研究地图。</p>
  </header>
  <main>
    <section id="overview-view" aria-labelledby="atlas-title">
      <aside class="map-legend" aria-label="证明状态图例">
        <h2>如何阅读地图</h2>
        <p><span aria-hidden="true">●</span> 已证明：当前项目中有可审计 Lean 证明</p>
        <p><span aria-hidden="true">◆</span> 正在连接：路线接口或尚未闭合的证明链</p>
        <p><span aria-hidden="true">○</span> 研究前沿：不能当作当前项目结论</p>
      </aside>
      <div id="atlas-map" aria-label="证明依赖关系图"></div>
      <section id="selection-drawer" aria-live="polite">
        <p>当前选择</p>
        <h2>经典零自由区域</h2>
        <p>把 zeta 零点从 Re(s)=1 附近推开一段可定量的距离。</p>
        <button type="button" data-action="open-concept" data-concept-id="zero-free">进入概念页</button>
      </section>
    </section>
    <article id="concept-view" hidden aria-live="polite"></article>
    <noscript>本页面的核心路线：zeta 工具 → 零自由区域 → Perron/显式公式 → PNT；RH 是更远的目标。</noscript>
  </main>
  <script>document.documentElement.classList.add("js");</script>
</body>
</html>
```

- [ ] **Step 2: Add the complete concept schema and audited content**

Each concept object uses the same property names:

```js
const CONCEPTS = Object.freeze([
  {
    id: "zero-free",
    title: "经典零自由区域",
    english: "Classical zero-free region",
    status: "proved",
    core: true,
    summary: "把 zeta 零点从 Re(s)=1 附近推开一段可定量的距离。",
    formula: "Re(s) ≥ 1 − c / log |Im(s)|  ⟹  ζ(s) ≠ 0",
    intuition: "零点越靠右，素数计数误差越大；先排除最危险的右边缘。",
    leanEvidence: [
      "对数导数 Dirichlet 级数实部公式",
      "de la Vallée Poussin 3-4-1 非负组合",
      "高处 c / log |t| 零自由区域"
    ],
    impact: "为 Perron 路径移动和经典 PNT 误差路线提供解析输入。",
    warning: "这不是 RH；它只控制 Re(s)=1 附近的一条区域。",
    dependsOn: ["zeta-tools", "three-four-one"],
    compact: { x: 68, y: 20 },
    expanded: { x: 67, y: 18 }
  }
]);
```

Add one object for every identifier asserted by the checker. Every object must explicitly include all properties shown above. Use these audited status assignments unless Task 1 finds stronger source evidence:

```js
const STATUS_BY_ID = Object.freeze({
  zeta: "proved",
  "zeta-tools": "proved",
  "three-four-one": "proved",
  "zero-free": "proved",
  perron: "route",
  "explicit-formula": "route",
  "psi-error": "route",
  pnt: "route",
  "pnt-error": "frontier",
  "existing-pnt": "frontier",
  "zero-density": "frontier",
  "rh-error": "frontier",
  rh: "frontier"
});
```

The `existing-pnt` entry must say that other Lean projects have formalized PNT and that this does not make it a result of the current repository. The `pnt` and `rh` warnings must explicitly state that this project has not proved them.

- [ ] **Step 3: Implement the visual system and responsive geometry**

Define named tokens for paper, ink, structural navy, verified green, route amber, frontier red, border, and focus. Desktop uses a radial map; widths at or below `720px` use a vertical dependency list.

Required responsive rule:

```css
@media (max-width: 720px) {
  .atlas-layout { grid-template-columns: 1fr; }
  .map-legend { display: flex; flex-wrap: wrap; border-right: 0; }
  .map-stage { min-height: auto; display: grid; gap: 12px; }
  .connector-layer, .orbit { display: none; }
  .map-node { position: relative; inset: auto !important; transform: none; width: 100%; }
  .map-node[hidden] { display: none; }
}

@media (prefers-reduced-motion: reduce) {
  *, *::before, *::after { scroll-behavior: auto !important; transition: none !important; animation: none !important; }
}
```

- [ ] **Step 4: Run the artifact checker**

Run the Task 1 command.

Expected: exit code `0` and `proof atlas contract: PASS`.

- [ ] **Step 5: Inspect direct-file rendering**

Open the artifact with its `file://` URL. Expected: the scientific-map theme, six visible core nodes, readable fallback copy, no missing fonts or resources, and no browser console network errors.

---

### Task 3: Implement Map, Concept, and History Interaction

**Files:**
- Modify: `/Users/luicy/.codex/visualizations/2026/05/23/019e55d5-94a4-7802-b7f0-8df5066f27b1/riemann-proof-atlas.html`
- Test: `scripts/check_riemann_proof_atlas.mjs`

**Interfaces:**
- Consumes: `CONCEPTS` and semantic surfaces from Task 2.
- Produces: `renderMap(expanded)`, `selectConcept(id)`, `showConcept(id)`, `showOverview()`, and `routeFromHash()`.

- [ ] **Step 1: Add deterministic rendering helpers**

```js
const byId = new Map(CONCEPTS.map((concept) => [concept.id, concept]));
let expanded = false;
let selectedId = "zero-free";

function visibleConcepts() {
  return CONCEPTS.filter((concept) => expanded || concept.core);
}

function statusLabel(status) {
  return { proved: "已证明", route: "正在连接", frontier: "研究前沿" }[status];
}

function conceptOrFallback(id) {
  return byId.get(id) ?? byId.get("zero-free");
}
```

- [ ] **Step 2: Render semantic node buttons and connectors**

`renderMap(expanded)` clears and rebuilds the connector layer and node layer from `visibleConcepts()`. Each node is a native button with `class="map-node"`, a visible status label, `aria-pressed`, and a `data-concept-id` attribute. Connector arrows are SVG paths derived from `dependsOn`; their relationships are repeated as text in concept pages.

- [ ] **Step 3: Implement selection and concept rendering**

```js
function selectConcept(id) {
  const concept = conceptOrFallback(id);
  selectedId = concept.id;
  renderDrawer(concept);
  document.querySelectorAll(".map-node").forEach((node) => {
    node.setAttribute("aria-pressed", String(node.dataset.conceptId === selectedId));
  });
}

function showConcept(id) {
  const concept = conceptOrFallback(id);
  renderConceptPage(concept);
  document.querySelector("#overview-view").hidden = true;
  document.querySelector("#concept-view").hidden = false;
  document.querySelector("#concept-view h1")?.focus();
}

function showOverview() {
  document.querySelector("#concept-view").hidden = true;
  document.querySelector("#overview-view").hidden = false;
  renderMap(expanded);
  selectConcept(selectedId);
}
```

The concept renderer omits empty optional sections and creates previous/next navigation from the array order.

- [ ] **Step 4: Implement hash history and unknown-route fallback**

```js
function routeFromHash() {
  const match = location.hash.match(/^#concept\/([a-z0-9-]+)$/);
  if (match && byId.has(match[1])) {
    showConcept(match[1]);
    return;
  }
  if (location.hash && location.hash !== "#overview") {
    history.replaceState(null, "", "#overview");
  }
  showOverview();
}

window.addEventListener("hashchange", routeFromHash);
routeFromHash();
```

The expand control updates `expanded`, `aria-expanded`, and its visible label, then rerenders without changing the hash.

- [ ] **Step 5: Run the checker and interaction smoke test**

Run the checker, then verify:

1. compact map has six visible nodes;
2. expand reveals every concept;
3. selecting a node updates the drawer;
4. opening a concept changes the hash;
5. back/forward returns between map and concept;
6. `#concept/not-real` returns to `#overview`;
7. Enter and Space activate focused node buttons.

Expected: all checks pass without console errors.

---

### Task 4: Visual, Responsive, and Claim-Boundary Verification

**Files:**
- Modify if defects are found: `/Users/luicy/.codex/visualizations/2026/05/23/019e55d5-94a4-7802-b7f0-8df5066f27b1/riemann-proof-atlas.html`
- Test: `scripts/check_riemann_proof_atlas.mjs`

**Interfaces:**
- Consumes: completed standalone artifact.
- Produces: verified screenshots and a final artifact that passes automated and visual checks.

- [ ] **Step 1: Capture desktop screenshots**

Open the `file://` artifact and capture the overview and one concept page at `1440x900` and `1024x768`.

Expected: no overlap, clipped node labels, internal horizontal scroll, blank SVG paths, or oversized typography. The next section remains visible without requiring a full viewport-height hero.

- [ ] **Step 2: Capture mobile screenshots**

Capture the compact route, expanded route, and one concept page at `390x844` and `320x700`.

Expected: nodes become a vertical route, all text fits, controls wrap cleanly, and no content extends past the viewport width.

- [ ] **Step 3: Verify keyboard and reduced-motion behavior**

Tab through map controls, activate one node and the expand control with the keyboard, and emulate `prefers-reduced-motion: reduce`.

Expected: visible focus at every step, logical focus order, and no animated transitions under reduced motion.

- [ ] **Step 4: Re-run source and claim audits**

```bash
node scripts/check_riemann_proof_atlas.mjs /Users/luicy/.codex/visualizations/2026/05/23/019e55d5-94a4-7802-b7f0-8df5066f27b1/riemann-proof-atlas.html
rg -n "本项目已经证明素数定理|本项目已经证明黎曼猜想" /Users/luicy/.codex/visualizations/2026/05/23/019e55d5-94a4-7802-b7f0-8df5066f27b1/riemann-proof-atlas.html
git status --short
```

Expected: checker passes; prohibited-claim search returns no matches; Git status shows only intentional checker/plan changes plus the user's pre-existing unrelated changes.

- [ ] **Step 5: Commit repository-owned verification files**

```bash
git add scripts/check_riemann_proof_atlas.mjs docs/superpowers/plans/2026-07-13-riemann-proof-atlas.md
git commit -m "test: verify standalone Riemann proof atlas"
```

Do not stage or commit pre-existing Lean or documentation changes.
