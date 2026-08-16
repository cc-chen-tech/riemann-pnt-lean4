# L3 capstone (`windowedDetector_contradicts_noTopLayerZero`): FORMALIZED

Status: **DONE** (merge-test-amplification worktree,
`PrimeNumberTheorem/WindowedDetectorConclusion.lean`).  0 `sorry`; axiom audit
(`Test/WindowedDetectorConclusionAxiomAudit.lean`) prints only
`[propext, Classical.choice, Quot.sound]`.

## The theorem

```text
windowedDetector_contradicts_noTopLayerZero
  {lam gap β h T0 H γ} {seed : ℂ} {top complementary : Finset ℂ} {Err} {MassA MassB} {KA Ce}
  (hlam : 1 < lam) (hh : 0 < h) (hT0 : 0 < T0) (hH : 0 < H)
  (hβ : 0 < β) (hgap : 0 < gap) (hhsmall : h ≤ Real.log 2) (hCe : 0 ≤ Ce)
  (hdisj1 : seed ∉ top) (hdisj2 : seed ∉ complementary) (hdisj : Disjoint top complementary)
  (hseed : IsNontrivialZero seed) (hseed_re : seed.re = β) (hz_seed) (hγavoid_seed)
  (hzero_top/hre_top/hz_top/hγavoid_top/hhigh_top)          -- top-layer data
  (hzero_comp/hre_comp : ρ.re ≤ β − gap/hz_comp/hγavoid_comp/hhigh_comp)
  (hMassA : Σ_{ρ∈top} m(ρ)/|γ−Im ρ| ≤ MassA)                 -- round-41 kernel form
  (hMassB : Σ_{ρ∈complementary} m(ρ)/|γ−Im ρ| ≤ MassB)
  (hErrCont : Continuous Err)
  (hexplicit : ∀ᶠ x, centeredSecondDifferencePsi x h
      = Σ_{ρ∈{seed}∪top∪complementary} cubicZeroResidueSecondDifference ρ x h / h² + Err x)
  (hErrBound : ∀ᶠ x, ‖Err x‖ ≤ Ce·x^(1−1/20))
  (hbudgetA : ∀ᶠ X, max 4 (36/(h·(T0/2))²)·4·X^(λβ)/T0·MassA < X^(λβ)/(16β(T0+H)))
  (hbudgetB : ∀ᶠ X, max 4 (36/(h·(T0/2))²)·4·X^(λ(β−gap))/T0·MassB < X^(λβ)/(16β(T0+H)))
  (hbudgetErr : ∀ᶠ X, Ce·(20/19)·X^(λ(1−1/20)) < X^(λβ)/(16β(T0+H)))
  (hsignal : ∀ᶠ X, ‖coeff(seed)·I(seed)‖ + 3·X^(λβ)/(16β(T0+H)) < ‖windowedResponse X lam h γ‖)
  : False
```

## Proof structure

1. `hident` = round-42 restatement of
   `windowedMellinResponse_eq_sum_add_error` with the explicit constant form:
   `‖wr − Σ coeff·I‖ ≤ Ce·(20/19)·X^(λ(1−1/20))`.
2. The kernel-form coefficient bounds (round 41)
   `topLayerCoeffResponseSum_le` / `complementaryCoeffResponseSum_le`
   are bridged to `integralFactor` form via
   `integral_cpow_eq_integralFactor` under `sum_congr`.
3. The truncated sum splits `{seed} ∪ top ∪ complementary` with
   `Finset.sum_union` under the lattice-`Disjoint` hypotheses via
   `Finset.disjoint_singleton_left` / `Finset.disjoint_left`.
4. `hcontra`: under `1 < X`, identity bound + the three budgets + the seed
   signal excess force `‖seed‖ + 3u < ‖wr‖ ≤ ‖seed‖ + 3u` (the two budget
   units `top + complementary + err < 3u` from `hA + hB + hE'`), `nlinarith`.
5. Closure: the six eventuals are combined with `Filter.Eventually.and`
   (the `filter_upwards`/False-goal `mp_mem` path is avoided) plus
   `Filter.eventually_gt_atTop (1 : ℝ)`, then
   `Filter.Eventually.exists` + `rcases` instantiate `hcontra`.

## Remarks for the gate assembly (next step)

- The capstone is the analytic end of the L1–L3 line; its conclusion is
  `False` from the accounted-sum decomposition.  The gate inputs
  `hbranch`/`hbranch_le`/`hlower`/`hdisjoint` are derived by instantiating
  it with `top` = the top-layer packet, `complementary` = the lower layers,
  `MassA`/`MassB` = the L1/L3 frequency-weighted mass bounds, and
  `hbudgetA/B/Err` = `AmplificationGateExponentBudget`-style power
  comparisons (dischargeable for any `β ∈ (2/3,1)`, `gap > 0`).
- `hsignal` is supplied by the vk-edge witness
  (`VKEdgeConditionalPackage.halfIsolatedEnvelopeBridge`); the bridge from
  its oscillation conclusion to the capstone's `hsignal` form is the next
  assembly step.
- `hexplicit`/`herr` remain on the user's cubic-line worktree
  (`actual-cubic-two-height-l2-tail`); the local re-derivation
  `ZeroDensityLayerBudgetCubicKernelLocal` matches its declaration names,
  so the merge supersedes the local copy.
