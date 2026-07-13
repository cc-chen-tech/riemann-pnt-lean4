# Task 1 Review Remediation Report

## Retrieval Note

The requested worktree directory had been removed before this remediation. The existing `rescue/proof-atlas-redesign` branch was checked out again at `7b480fce45de457aa56525c56aafe96d0d0853d3`; neither the original Task 1 brief nor the prior report was tracked on that branch. This report records the recovered evidence and corrections without changing Lean, the plan, or the deployed HTML artifact.

## Corrected Status Rationale

| Concept | Required status | Rationale |
| --- | --- | --- |
| `zeta`, `zeta-tools`, `three-four-one` | `proved` | Audited local Lean components. |
| `zero-free` | `route` in this worktree | The main-checkout axiom audit cannot be applied because the worktree's defining `PhragmenLindelofZeta.lean` blob differs. Restore `proved` only after a matching-source audit. |
| `perron`, `explicit-formula`, `psi-error`, `pnt` | `route` | `pnt` is the endpoint of the active classical chain, not a current proof. |
| `pnt-error`, `existing-pnt`, `zero-density`, `rh-error`, `rh` | `frontier` | `existing-pnt` is an external comparison, not a current-project result; `rh-error` requires RH-scale remote input. |

`pnt` and `rh` are rejected as `proved`. The checker now requires a nonempty `leanEvidence` array for every concept. Static checking only confirms that `@media (max-width: 360px)` exists. Actual 320px readability remains a Task 4 browser acceptance test and cannot be proved by text matching.

## Axiom-Audit Scope Check

Exact Git-object evidence:

```text
worktree branch: rescue/proof-atlas-redesign @ 7b480fce45de457aa56525c56aafe96d0d0853d3
main checkout: main @ 32e40f3f9f3412b39365ef42414b285611030e48

ZeroFreeRegion.lean
  worktree/main: 7c8dede0f8ccbfbda5b8be90b55702861c471003 (match)
ZeroFreeRegion/PhragmenLindelofZeta.lean
  worktree:      2c602a0d3b1249a5350f2d661fde9686c98e328a
  main audit:    018cfdc8eaf5c34b5fb859d0d5aa67d1101c1aa0 (different)
```

The successful audit was run in the main checkout with:

```bash
printf '%s\n' 'import ZeroFreeRegion.PhragmenLindelofZeta' \
  '#print axioms ZeroFreeRegion.classical_zero_free_region_proved' | lake env lean /dev/stdin
```

Result:

```text
'ZeroFreeRegion.classical_zero_free_region_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This is valid evidence for the main source blob only. It is not evidence that the differing worktree theorem has the same axiom boundary, so this report does not claim the audit applies there.

## Checker Regressions

Focused fixtures were generated under `$(node -p 'require("node:os").tmpdir()')/riemann-proof-atlas-checker-fixtures` and run with the one-target CLI. Results:

```text
runtime-fetch.html       exit=1  runtime resource: fetch
runtime-xhr.html         exit=1  runtime resource: XMLHttpRequest; XMLHttpRequest.open
runtime-websocket.html   exit=1  runtime resource: WebSocket
runtime-eventsource.html exit=1  runtime resource: EventSource
runtime-script-src.html  exit=1  runtime resource: dynamic src/href assignment
runtime-link-href.html   exit=1  runtime resource: dynamic src/href assignment
runtime-import.html      exit=1  runtime resource: dynamic import
http-literal.html        exit=1  external resource: http(s) or protocol-relative literal
protocol-relative.html   exit=1  external resource: http(s) or protocol-relative literal
comment-spoof.html       exit=1  missing id="atlas-map" and zero static fallback nodes
invalid-status.html      exit=1  concept pnt must use status route, found proved
empty-evidence.html      exit=1  concept zeta has empty leanEvidence array
few-fallback.html        exit=1  expected at least six static #atlas-map fallback buttons, found 5
hash-anchor-allowed.html exit=0  proof atlas contract: PASS
comment-url-ignored.html exit=0  proof atlas contract: PASS
valid-noncanonical.html exit=0  proof atlas contract: PASS
```

The pre-fix checker incorrectly returned `exit=0` for the runtime-fetch, empty-evidence, and one-static-fallback fixtures. The noncanonical valid fixture proves the structural checker still has a one-target CLI and does not require a deployment comparison for every target. When the target path is exactly `docs/assets/riemann-proof-atlas.html`, the checker requires the deployed absolute artifact to exist and compares the two buffers byte-for-byte; checking the old external artifact directly does not take that comparison path.

Commands rerun after the fix:

```bash
node --check scripts/check_riemann_proof_atlas.mjs
node scripts/check_riemann_proof_atlas.mjs /Users/luicy/.codex/visualizations/2026/05/23/019e55d5-94a4-7802-b7f0-8df5066f27b1/riemann-proof-atlas.html
```

Results: `node --check` exited `0`; the old artifact exited `1` as expected, with missing standalone-document/map/concept/routing requirements and no canonical-comparison error.

Canonical deployment probe (the temporary source was removed immediately after the check):

```bash
mkdir -p docs/assets
cp "$fixture_dir/valid-noncanonical.html" docs/assets/riemann-proof-atlas.html
node scripts/check_riemann_proof_atlas.mjs docs/assets/riemann-proof-atlas.html
rm docs/assets/riemann-proof-atlas.html
rmdir docs/assets
```

Result: `exit=1` with exactly `deployed artifact differs from canonical source: /Users/luicy/.codex/visualizations/2026/05/23/019e55d5-94a4-7802-b7f0-8df5066f27b1/riemann-proof-atlas.html`. This exercises the canonical comparison without modifying the external artifact.

## Self-Review

- Runtime detection is applied after HTML, JavaScript, and CSS comments are stripped; comment-only URL text does not create a false RED.
- Static fallback counting is scoped to `#atlas-map`, excludes script/style bodies, requires real `button.map-node[data-concept-id]` markup, and accepts progressive JavaScript enhancement only after that fallback exists.
- Deployment byte comparison is conditional on the canonical repository source path, so checking the legacy external artifact remains a normal contract RED.
- No Lean file, plan, or external HTML artifact was modified.

## Post-Commit Verification

Exact command sequence:

```bash
node --check scripts/check_riemann_proof_atlas.mjs
fixture_dir="$(node -p 'require("node:os").tmpdir()')/riemann-proof-atlas-checker-fixtures"
for fixture in runtime-fetch.html runtime-xhr.html runtime-websocket.html runtime-eventsource.html runtime-script-src.html runtime-link-href.html runtime-import.html http-literal.html protocol-relative.html comment-spoof.html invalid-status.html empty-evidence.html few-fallback.html; do
  node scripts/check_riemann_proof_atlas.mjs "$fixture_dir/$fixture"
done
for fixture in hash-anchor-allowed.html comment-url-ignored.html valid-noncanonical.html; do
  node scripts/check_riemann_proof_atlas.mjs "$fixture_dir/$fixture"
done
node scripts/check_riemann_proof_atlas.mjs /Users/luicy/.codex/visualizations/2026/05/23/019e55d5-94a4-7802-b7f0-8df5066f27b1/riemann-proof-atlas.html
```

Results: syntax check `0`; all 13 required RED fixtures `1`; hash-anchor, comment-only URL, and valid noncanonical fixtures `0`; legacy external artifact `1` with `missing: <!doctype html>`. The temporary canonical-source probe remained `1` with the expected byte-mismatch message.

## Final Task 1 Status Correction (2026-07-14)

The earlier `zero-free | route` row and the associated concern that zero-free must remain `route` are superseded by the exact-branch audit below. The checker now requires `zero-free` to be `proved`.

| Concept | Required status | Rationale |
| --- | --- | --- |
| `zeta`, `zeta-tools`, `three-four-one`, `zero-free` | `proved` | The exact local Lean sources and the branch-specific zero-free theorem audit are accepted. |
| `perron`, `explicit-formula`, `psi-error`, `pnt` | `route` | These remain route-level components of the active chain. |
| `pnt-error`, `existing-pnt`, `zero-density`, `rh-error`, `rh` | `frontier` | These remain frontier or external-comparison targets. |

### Exact-Branch Axiom Audit

The worktree's `ZeroFreeRegion/PhragmenLindelofZeta.lean` was compiled into:

```text
.superpowers/sdd/lean-audit/ZeroFreeRegion/PhragmenLindelofZeta.olean
```

Dependency oleans were used only where their imported source blobs matched. The controller then ran `.superpowers/sdd/AuditZeroFree.lean` with this isolated branch olean first in `LEAN_PATH`; the command exited `0` and printed:

```text
'ZeroFreeRegion.classical_zero_free_region_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This is exact-branch evidence. The theorem depends only on Lean's standard axioms shown above; the previous main-checkout source-mismatch concern does not apply to this audit and is withdrawn.

### Final Focused Checker Evidence

Using the existing `valid-noncanonical.html` fixture and a temporary copy with only the zero-free status changed:

```text
node --check scripts/check_riemann_proof_atlas.mjs       exit=0
zero-free=proved fixture                                 exit=0  proof atlas contract: PASS
zero-free=route fixture                                  exit=1  concept zero-free must use status proved, found route
old external artifact                                    exit=1  missing standalone atlas requirements
```

The old external artifact remains intentionally RED because it is not the canonical standalone atlas source. No remaining status concern requires `zero-free` to stay `route`.

## Final Task 1 Checker Findings (2026-07-14)

The checker was extended without changing the exact-branch `zero-free: proved` mapping or the existing structural, claim, fallback, deployment, and external-resource checks. Temporary fixtures were generated under `$(node -p 'require("node:os").tmpdir()')/riemann-proof-atlas-checker-fixtures`; no fixture files were added to the repository.

Post-edit command results:

```text
node --check scripts/check_riemann_proof_atlas.mjs       exit=0
git diff --check                                          exit=0
```

Focused RED fixtures:

```text
runtime-worker.html                exit=1 runtime resource: Worker
runtime-importscripts.html         exit=1 runtime resource: importScripts
runtime-sendbeacon.html            exit=1 runtime resource: navigator.sendBeacon
runtime-constructed-url.html       exit=1 runtime resource: new URL
div-network-toggle.html            exit=1 missing: button[data-action="toggle-network"]
unrelated-focus.html               exit=1 missing: visible focus for button or map-node controls;missing: visible focus for network toggle
valid-bound-focus.html             exit=0 proof atlas contract: PASS
```

Full runtime denylist matrix:

```text
runtime-sharedworker.html          exit=1 runtime resource: SharedWorker
runtime-serviceworker.html         exit=1 runtime resource: serviceWorker.register
runtime-dynamic-import.html        exit=1 runtime resource: dynamic import
runtime-fetch.html                 exit=1 runtime resource: fetch
runtime-xhr.html                   exit=1 runtime resource: XMLHttpRequest
runtime-websocket.html             exit=1 external resource: http(s) or protocol-relative literal;runtime resource: WebSocket
runtime-eventsource.html           exit=1 runtime resource: EventSource
runtime-object-url.html            exit=1 runtime resource: URL.createObjectURL
runtime-constructed-element.html   exit=1 runtime resource: constructed resource element
runtime-image.html                 exit=1 runtime resource: constructed Image
runtime-audio.html                 exit=1 runtime resource: constructed Audio
css-url.html                       exit=1 external resource: CSS url(/asset.png)
```

The old deployed artifact remained RED as expected:

```text
old-artifact.html                   exit=1 missing: <!doctype html>;missing: <html lang="zh-CN">;missing: id="atlas-map";missing: id="concept-view";missing: @media (max-width: 720px);missing: @media (max-width: 360px);missing: hash routing;missing: hashchange listener;missing: location.hash;missing: network expansion;missing: concept rendering;missing: button[data-action="toggle-network"];missing: visible focus for button or map-node controls;missing: visible focus for network toggle;expected at least six static #atlas-map fallback buttons, found 0;missing: CONCEPTS array
```

The prior invalid fixture set also remained RED. The existing `hash-anchor-allowed.html`, `comment-url-ignored.html`, and `valid-noncanonical.html` temporary fixtures predate the exact-branch `zero-free: proved` mapping and the newly required bound focus rules, so they are not valid post-edit acceptance fixtures; `valid-bound-focus.html` is the replacement positive fixture and passed.

## Final Concrete Checker Bypass Closure (2026-07-14)

Only `scripts/check_riemann_proof_atlas.mjs` and this evidence append were changed. The required `zero-free: proved` status mapping was preserved.

Temporary one-target fixtures were added under `/var/folders/0r/01j0z8210zb8d0p10wllg6tc0000gn/T/riemann-proof-atlas-checker-fixtures`; none were added to the repository. Before the checker edit, the following requested bypass fixtures each returned `exit=0`: `onclick-fetch.html`, `static-module-import.html`, `input-src.html`, `svg-image-href.html`, `concepts-string-spoof.html`, `concepts-template-spoof.html`, `duplicate-zeta-fallback.html`, `core-set-mismatch.html`, and `rgba-alpha-zero-focus.html`.

Post-edit verification command sequence:

```bash
node --check scripts/check_riemann_proof_atlas.mjs
fixture_dir=/var/folders/0r/01j0z8210zb8d0p10wllg6tc0000gn/T/riemann-proof-atlas-checker-fixtures
for fixture in onclick-fetch.html static-module-import.html static-export-from.html input-src.html svg-image-href.html resource-attributes.html concepts-string-spoof.html concepts-template-spoof.html duplicate-zeta-fallback.html core-set-mismatch.html rgba-alpha-zero-focus.html; do
  node scripts/check_riemann_proof_atlas.mjs "$fixture_dir/$fixture"
done
for fixture in internal-hash-allowed.html valid-core-focus.html; do
  node scripts/check_riemann_proof_atlas.mjs "$fixture_dir/$fixture"
done
node scripts/check_riemann_proof_atlas.mjs /Users/luicy/.codex/visualizations/2026/05/23/019e55d5-94a4-7802-b7f0-8df5066f27b1/riemann-proof-atlas.html
git diff --check
```

Results:

```text
node --check                              exit=0
onclick-fetch.html                        exit=1 runtime resource: fetch
static-module-import.html                 exit=1 runtime resource: static ES module import/export
static-export-from.html                   exit=1 runtime resource: static ES module import/export
input-src.html                            exit=1 external resource: <input> src=/atlas.png
svg-image-href.html                       exit=1 external resource: <image> href=/atlas.svg; external resource: <use> href=/atlas-symbol
resource-attributes.html                  exit=1 external resource: <object> data=/atlas.bin; external resource: <video> poster=/poster.png; external resource: <form> action=/submit; external resource: <button> formaction=/next; external resource: <object> data=/atlas.bin; external resource: <video> poster=/poster.png
concepts-string-spoof.html                exit=1 missing: CONCEPTS array
concepts-template-spoof.html              exit=1 missing: CONCEPTS array
duplicate-zeta-fallback.html              exit=1 static #atlas-map fallback buttons must not duplicate data-concept-id values; static #atlas-map fallback IDs must exactly match core:true concept IDs
core-set-mismatch.html                    exit=1 static #atlas-map fallback IDs must exactly match core:true concept IDs
rgba-alpha-zero-focus.html                exit=1 missing: visible focus for button or map-node controls; missing: visible focus for network toggle
internal-hash-allowed.html                exit=0 proof atlas contract: PASS
valid-core-focus.html                     exit=0 proof atlas contract: PASS
old-artifact.html                         exit=1 expected standalone-atlas requirements missing
git diff --check                          exit=0
```

The static attribute scan accepts only `<a href="#...">` hash navigation. It rejects the resource-bearing `src`, `href`, `data`, `poster`, `action`, and `formaction` attributes for every other markup element, with quoted and unquoted values covered by the fixtures. Inline event-handler bodies are scanned with script bodies; static ES-module `import` and `export ... from` declarations are rejected; `CONCEPTS` is located only in script code after strings and template literals are masked. Static fallback nodes are now de-duplicated and required to equal the six `core:true` concept IDs. Visible focus requires a nonzero width, a `solid`, `dashed`, or `double` style, and a non-transparent color, including alpha-zero functional and hex colors.

## Final One-Line Class Fixes (2026-07-14)

The visible-outline validator now requires a literal, statically nontransparent color and rejects indirect color expressions including `var(...)`, `currentColor`, `color-mix(...)`, `calc(...)`, `env(...)`, `attr(...)`, and CSS-wide inheritance keywords. The required `zero-free: proved` mapping and all prior checks remain unchanged.

Focused evidence from temporary fixtures:

```text
indirect-focus-var-alpha-zero.html  exit=1  missing: visible focus for button or map-node controls;missing: visible focus for network toggle
indirect-focus-current-color.html   exit=1  same focus failures
indirect-focus-color-mix.html       exit=1  same focus failures
indirect-focus-calc.html            exit=1  same focus failures
indirect-focus-env.html             exit=1  same focus failures
indirect-focus-inherit.html         exit=1  same focus failures
valid-core-focus.html               exit=0  proof atlas contract: PASS (`#166c9b`)
old deployed artifact                exit=1  standalone-atlas requirements remain missing
```

Verification: `node --check scripts/check_riemann_proof_atlas.mjs` exited `0`; `git diff --check` exited `0`. Only the checker and this report were changed for this fix; the pre-existing plan worktree modification was left untouched.
