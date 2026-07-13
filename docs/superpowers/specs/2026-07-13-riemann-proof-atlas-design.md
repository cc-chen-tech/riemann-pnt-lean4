# Riemann Proof Atlas Design

## Purpose

Build a standalone interactive HTML visualization that explains the relationship between the project's verified Lean results, the classical PNT route, and the much more distant Riemann Hypothesis goal. The page should feel like a scientific proof atlas rather than a generic dashboard.

The primary audience is a reader who understands the project goal but does not yet understand how zero-free regions, Perron formulas, PNT error terms, and RH relate. The page's main job is to make distance and dependency visible without overstating what the Lean repository proves.

## Deliverable

Replace the existing visualization with one self-contained HTML file:

`/Users/luicy/.codex/visualizations/2026/05/23/019e55d5-94a4-7802-b7f0-8df5066f27b1/riemann-proof-atlas.html`

It must open directly with a `file://` URL and must not depend on Codex theme variables, a local server, a build tool, or external JavaScript libraries.

## Visual Direction

The selected direction is "Proof Atlas": a precise scientific map with a light gray-blue field, navy structural marks, and restrained status colors.

- Background and structure: cool gray-blue paper and fine cartographic rules.
- Primary structure: deep navy.
- Verified Lean results: muted green.
- Active route gaps: amber.
- Distant research frontier or overclaim boundary: restrained dark red.
- Typography: a serif display face for mathematical concepts, a neutral sans-serif for Chinese explanation, and monospace for theorem/status metadata.
- Corners, shadows, and animation remain restrained. The map, not decoration, is the signature element.

Color never acts as the only status signal. Every status also has a text label and node marker.

## Information Architecture

### Overview map

The initial view shows six core concepts:

1. Riemann zeta function as the central object.
2. Zeta and logarithmic-derivative tools.
3. Classical zero-free region.
4. Perron and contour bridge.
5. Prime Number Theorem.
6. Riemann Hypothesis.

Node distance from the center communicates increasing dependency depth and mathematical distance. Directed connectors communicate logical dependency. A visible legend distinguishes:

- proved in the current Lean project;
- route component or active gap;
- distant frontier or claim boundary.

An "expand full network" control reveals the remaining concepts, including the 3-4-1 method, explicit formula, psi error estimates, PNT with remainder, existing Lean PNT routes, zero-density estimates, and RH error equivalences.

### Selected-concept drawer

Selecting a map node updates a compact explanation band below the map. It shows:

- concept name and status;
- one plain-language explanation;
- why the concept matters;
- an action to open the full concept page.

This band is part of the page layout, not a floating modal.

### Concept pages

Every concept uses the same four-part explanation structure:

1. Plain-language intuition.
2. Exact mathematical shape or representative formula.
3. What is genuinely proved or available in Lean.
4. What it unlocks next and what it must not be confused with.

Each page keeps a breadcrumb back to the atlas, previous/next concept navigation, and an action to locate the concept on the map.

## Content Model

All node content lives in one JavaScript data structure. Each entry contains:

- stable identifier;
- Chinese title and optional English label;
- status (`proved`, `route`, or `frontier`);
- overview summary;
- representative formula;
- plain-language explanation;
- Lean evidence;
- next dependency or impact;
- overclaim warning;
- map coordinates for the compact and expanded layouts;
- dependency identifiers.

The map and concept pages are rendered from this structure. Concept text is not duplicated across hand-written HTML sections.

## Interaction

- The compact map is the default.
- The network can be expanded and collapsed without changing pages.
- Clicking or pressing Enter/Space on a node selects it.
- A separate action opens the full concept page.
- Browser back/forward navigation works through URL hashes.
- Reloading preserves the current concept or overview state.
- Returning to the overview restores the selected node and expansion state when possible.
- Motion is limited to short connector/node transitions and is disabled under `prefers-reduced-motion`.

## Responsive Behavior

At desktop widths, the visualization uses a spatial atlas with a side legend and lower explanation band.

At narrow widths, it becomes a vertical dependency route. It does not shrink the radial map until labels overlap. The same content, statuses, and navigation remain available. Text and controls must fit at 320 px without horizontal scrolling.

## Accessibility

- Use semantic headings, navigation, buttons, and sections.
- Preserve native keyboard order and visible focus indicators.
- Provide text labels in addition to status colors.
- Every connector relationship is also available in text on the selected concept page.
- Respect reduced-motion settings.
- Keep Chinese body text at a readable size and contrast.

## Claim Boundary

The visualization must separate source-level Lean theorems from route interfaces, targets, and broader mathematical context.

It must not imply that the project proves PNT or RH unless the current source and an axioms audit support that claim. The classical zero-free-region node may be marked proved only if its current theorem remains verified without `sorry`, `admit`, or project-added axioms. Existing PNT work in Lean and Isabelle must be presented as related work, not as this project's result.

## Failure Handling

- Unknown or malformed URL hashes return to the overview.
- Missing optional concept fields are omitted without leaving empty headings.
- JavaScript-disabled browsers retain a readable overview and explanation of the core route.
- The visualization contains no required network resources, so offline and `file://` use remain functional.

## Verification

Before delivery:

1. Open the final file directly through `file://`.
2. Capture and inspect desktop screenshots at approximately 1440 x 900 and 1024 x 768.
3. Capture and inspect mobile screenshots at approximately 390 x 844 and 320 x 700.
4. Exercise compact/expanded map controls and every concept route.
5. Test browser back/forward and reload behavior.
6. Test keyboard-only selection and navigation.
7. Check for overlap, clipping, horizontal scrolling, blank content, and unreadable contrast.
8. Cross-check all proved/route/frontier labels against the current repository theorem inventory.

## Out of Scope

- Editing Lean proofs or theorem statements.
- Live synchronization with Git or theorem inventory files.
- A server, framework, package manager, or deployment pipeline.
- A claim that the current project proves PNT or RH.
