# Gate input supplier + detector extraction corollaries: FORMALIZED

Status: **DONE** (merge-test-amplification worktree).  All new declarations
0 `sorry`; axiom audits print only `[propext, Classical.choice, Quot.sound]`.

## `PrimeNumberTheorem/WindowedDetectorConclusion.lean` — detector extraction

| declaration | statement |
|---|---|
| `windowedDetector_contradicts_noTopLayerZero` | L3 capstone (round 42): the accounted-sum decomposition `{seed} ∪ top ∪ complementary` with the explicit-formula identity, error bound, three exponent budgets and the seed signal excess implies `False` |
| `windowedDetector_topLayerMass_exceeds` | **extraction corollary**: under the same hypotheses (minus `hMassA`), the top layer's frequency-weighted mass `Σ m(ρ)/\|γ−Im ρ\|` must *exceed* the budget `MassA` — pure contrapositive of the capstone |

## `PrimeNumberTheorem/WindowedMellinL3.lean` — packet count

| declaration | statement |
|---|---|
| `topLayerPacket_card_le_of_mass` | **count extraction**: `MassA < Σ_{ρ∈top} m(ρ)/\|γ−Im ρ\|`, the `η`-separation of the detection point and the global multiplicity cap `globalZeroMultiplicity ≤ Cg (T0+H)(1+log(T0+H+6))` force `q ≤ top.card` whenever `(q : ℝ) ≤ MassA·η/(Cg(T0+H)(1+log(T0+H+6)))` |

Together with the L1 mass bound this converts the capstone contradiction
into the gate's growing packet `q T = ⌊T^h'⌋` per node.

## `PrimeNumberTheorem/ExceptionalZeroAmplificationGateInputSupplier.lean` — gate assembly

| declaration | statement |
|---|---|
| `GateAssemblyInput β δ σ H depth` | the single remaining obligation bundle: layer growth data (`hroots`/`hbranch`/`hdisjoint`), per-window packet data (`windows`/`cluster`/`windowStart` with start separation, per-window lower bound, ambient membership, layer-card cover `hbranch_le`), and the exponent budget data (`h'`, `hq`, `hqexp`) |
| `assemblyCertificate` | the `IterativeLocalBranchCertificate` from the packet data: `depth+1` layers, `branchCount = #windows`, `localContribution = 1` |
| `zeroDensityZerosFinset_card_le_zeroDensityCount` | the ambient count bound: distinct-zero cardinality ≤ multiplicity-counted `zeroDensityCount` (via `analyticOrderNatAt_riemannZeta_pos_of_zero`) |
| `amplificationGateInputs_hlower` | gate input 5 from `disjointWindowFamilyLowerCount_eventually_le_zeroDensity` (already-proved bridge) |
| `amplificationGateInputs_hgap` | gate input 6 from `AmplificationGateExponentBudget.tendsto_qPower_sub_carlsonMajorant_atTop` (round 36) |
| `amplificationGateInputs_of_assembly` | the full `AmplificationGateInputs` bundle from a `GateAssemblyInput` |
| **`no_nontrivial_zero_re_gt_two_thirds_of_assembly`** | **terminal interface**: if `GateAssemblyInput` is supplied for every feasible tuple, then `∀ ρ, IsNontrivialZero ρ → ρ.re ≤ 2/3` |

## Remaining obligations (unchanged substance, now with a single interface)

1. Discharge `GateAssemblyInput` per feasible tuple from the L1–L3 detector:
   the per-window capstone instantiation (`windowedDetector_topLayerMass_exceeds`
   + `topLayerPacket_card_le_of_mass` → packet per window; separated windows →
   `hbranch`/`hdisjoint`/`hbranch_le`/`hadjacent`/`hlocal`/`hinside`), with
   `hq`/`hqexp` from the power-growth budget.
2. The seed-signal witness per window: vk-edge oscillation conclusion
   (`VKEdgeConditionalPackage.halfIsolatedEnvelopeBridge`) → the capstone's
   `hsignal` form (windowed response vs seed coefficient term).
3. `hexplicit`/`herr` (truncated explicit formula + contour remainder) on the
   user's cubic-line worktree (`actual-cubic-two-height-l2-tail`).

When 1–3 land, the axiom audit of the full route is at zero.
