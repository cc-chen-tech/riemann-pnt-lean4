# L1 DetectionPointChoice: PROMOTION COMPLETE (axiom → theorem)

Status: **DONE** (2026-08-16, merge-test-amplification worktree).

`PrimeNumberTheorem/HalfIsolatedZeroDichotomy/DetectionPointChoice.lean`
now contains **zero `sorry`** and the six target declarations audit clean
(`#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`):

| declaration | role | status |
|---|---|---|
| `exists_point_avoiding_small_intervals` | Appendix A covering/avoidance lemma | theorem, clean |
| `exists_windowedZeroMultiplicity_le` | Appendix B windowed count (T0-form) | theorem, clean |
| `exists_windowedZeroMultiplicity_le_uniform` | Appendix B, uniform `[a, b]`-form | theorem, clean |
| `ringMass_le_windowedCount` | ring mass ≤ windowed count | theorem, clean |
| `dyadic_distance_sum_le` | high-region dyadic split | theorem, clean |
| `exists_good_detection_point` | **L1 main assembly** | theorem, clean |

Audit file: `Test/DetectionPointChoiceAxiomAudit.lean`
(run `lake env lean Test/DetectionPointChoiceAxiomAudit.lean`).

## What the L1 theorem now states

```lean
theorem exists_good_detection_point
    (T0 H : ℝ) (complementary : Finset ℂ)
    (hT0 : 16 ≤ T0) (hH1 : 1 ≤ H) (hHleT0 : H ≤ T0)
    (hzero : ∀ ρ ∈ complementary, RiemannHypothesis.IsNontrivialZero ρ)
    (him_pos : ∀ ρ ∈ complementary, 0 < ρ.im)
    (him_le : ∀ ρ ∈ complementary, ρ.im ≤ T0 + H) :
    ∃ C γ : ℝ, 0 ≤ C ∧ T0 ≤ γ ∧ γ ≤ T0 + H ∧
      frequencyWeightedMass complementary γ ≤
        C * (1 + Real.log (T0 + H + 6)) ^ 2 * (T0 + H) / (T0 * H)
```

with `frequencyWeightedMass S γ = ∑ ρ ∈ S, m(ρ) / (‖ρ‖ · |γ - Im ρ|)`,
where `m(ρ) = analyticOrderNatAt riemannZeta ρ`.

## Design changes made during the promotion (vs. the old skeleton)

1. **No boundary slab.**  The high region now uses the *strict* cut
   `T0/2 < Im ρ` (low region `Im ρ ≤ T0/2`), so ring members enter
   `positiveNontrivialZerosBetween a b` through the strict left endpoint
   with `a = max(T0/2, γ - 2^(k+1) η)`, `b = γ + 2^(k+1) η`.  This
   removes the `globalZeroMultiplicity` slab term entirely (and with it
   the `T1²` blow-up in the constant cleaning).
2. **Base-2 dyadic weight.**  The pointwise bound uses
   `(1/2)^⌊log₂(|γ-Im ρ|/η)⌋`, whose level sets are exactly the dyadic
   rings `2^k η ≤ |γ - Im ρ| < 2^(k+1) η`; the partition is
   `Finset.sum_fiberwise_of_maps_to` over `k < K := ⌈log₂(T1/η)⌉ + 2`,
   with `2^(k+1) η ≤ 8 T1` from `2^⌈x⌉ ≤ 2^(x+1)`, so
   `log(b+6) ≤ log(9(T1+6)) ≤ (1 + log 9)(1 + log(T1+6))` inside
   `ringMass_le_windowedCount`.
3. **Closed-form constants, no cleaning sorry.**  The dyadic lemma
   returns the explicit constant
   `Cw (1 + log 9) (4 K + 6/η)`, and the main assembly returns
   `2 Cdy + 2 Crec` with `Crec` from
   `exists_globalReciprocalZeroMultiplicity_le_log_sq` (low region).
   The theorem's log factor is `(1 + log(T0+H+6))²` (it previously said
   `log(T0+H)`); consumers must use this shape.

## Remaining roadmap (unchanged)

- L2 windowed Mellin response: kernel modules
  (`cubicZeroResidueSecondDifference`, `cubicKernelMultiplier`) live on
  the `actual-cubic-two-height-l2-tail` line; the L2 draft
  (`WindowedMellinL2Draft.lean`) is shape-only until those modules are
  merged back or re-derived here.
- L3 threshold, gate instantiation (`hbranch`/`hgap`), and the final
  `no_nontrivial_zero_re_gt_two_thirds` exclusion.
- Partial milestone available meanwhile: β > 14/17 via single-layer
  forcing (`single-layer-forcing-beta-14-17.md`).
