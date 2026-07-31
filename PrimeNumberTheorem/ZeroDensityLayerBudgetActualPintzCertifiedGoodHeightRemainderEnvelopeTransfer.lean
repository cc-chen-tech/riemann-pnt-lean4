import PrimeNumberTheorem.ZeroDensityLayerBudgetActualPintzCertifiedGoodHeightOptimization
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightNaturalRemainderDecay
import PrimeNumberTheorem.ZeroDensityLayerBudgetVariableBoundaryZeroFreeEnvelopeTransfer

/-!
# Finite-switching remainder and zero-free-envelope transfer

The certified Pintz optimizer may switch between good-height selectors as the
scale changes.  This module proves that a finite pointwise switch preserves the
actual target-normalized remainder certificate.  It then applies the same
optimizer witness to the visible-positive-zero envelope.

No concrete zero-free function, signed main witness, unconditional Omega
statement, or RH claim is introduced here.
-/

namespace PrimeNumberTheorem

open Filter Topology
open scoped BigOperators

/-- A height schedule that pointwise selects one member of a finite family
inherits the actual natural-point remainder certificate of that family. -/
theorem
    actualSelectedHeightNaturalPointRemainderCertificate_of_finite_switching
    {ι : Type*} [Fintype ι] {beta : ℝ}
    (H : ℝ → ℝ) (candidate : ι → ℝ → ℝ)
    (hwitness : ∀ x, ∃ i, H x = candidate i x)
    (hcertificate :
      ∀ i, ActualSelectedHeightNaturalPointRemainderCertificate beta
        (candidate i)) :
    ActualSelectedHeightNaturalPointRemainderCertificate beta H := by
  classical
  refine ⟨?_⟩
  unfold NaturalPointTargetAmplitudeNegligible
  have hsum :
      Tendsto
        (fun m : ℕ =>
          ∑ i : ι,
            |actualPNTExplicitFormulaRelativeRemainder
              (candidate i) (m : ℝ)| /
              targetZeroPowerAmplitude beta (m : ℝ))
        atTop (nhds 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finset_sum Finset.univ fun i _ =>
        (hcertificate i).negligible
  have hamplitude :
      ∀ᶠ m : ℕ in atTop,
        0 < targetZeroPowerAmplitude beta (m : ℝ) :=
    eventually_naturalPoint_pos_of_eventually_pos
      (targetZeroPowerAmplitude_eventually_pos beta)
  refine squeeze_zero' ?_ ?_ hsum
  · filter_upwards [hamplitude] with m hm
    exact div_nonneg (abs_nonneg _) hm.le
  · filter_upwards [hamplitude] with m hm
    rcases hwitness (m : ℝ) with ⟨i, hi⟩
    have hremainder :
        actualPNTExplicitFormulaRelativeRemainder H (m : ℝ) =
          actualPNTExplicitFormulaRelativeRemainder (candidate i) (m : ℝ) := by
      unfold actualPNTExplicitFormulaRelativeRemainder
      rw [hi]
    rw [hremainder]
    exact Finset.single_le_sum
      (fun j _ => div_nonneg (abs_nonneg
        (actualPNTExplicitFormulaRelativeRemainder
          (candidate j) (m : ℝ))) hm.le)
      (Finset.mem_univ i)

/-- The regularized Stack119 candidate is eventually the existing selected
uniform good height and hence retains its actual remainder certificate. -/
theorem actualPintzCandidateHeight_actualNaturalRemainderCertificate
    {beta alpha : ℝ} (hbeta : 0 < beta)
    (halpha : 0 < alpha) (halphaOne : alpha ≤ 1)
    (hmargin : 1 - beta < alpha)
    (selection : UniformNaturalPointGoodHeightSelection) :
    ActualSelectedHeightNaturalPointRemainderCertificate beta
      (actualPintzCandidateHeight alpha selection) := by
  have hselected :=
    selectedUniformGoodHeight_actualNaturalRemainderCertificate
      hbeta halpha halphaOne hmargin selection
  refine ⟨?_⟩
  have hpower : Tendsto (fun x : ℝ => x ^ alpha) atTop atTop :=
    tendsto_rpow_atTop halpha
  have hlargeReal : ∀ᶠ x : ℝ in atTop, 9 ≤ x ^ alpha :=
    (tendsto_atTop.1 hpower) 9
  have hlargeNat : ∀ᶠ m : ℕ in atTop, 9 ≤ (m : ℝ) ^ alpha :=
    tendsto_natCast_atTop_atTop.eventually hlargeReal
  apply hselected.negligible.congr'
  filter_upwards [hlargeNat] with m hm
  unfold actualPNTExplicitFormulaRelativeRemainder
  simp [actualPintzCandidateHeight, hm]

/-- The exact pointwise certified optimizer has the actual natural-point
remainder certificate, despite switching selectors with the scale. -/
theorem actualPintzCertifiedOptimalHeight_actualNaturalRemainderCertificate
    {ι : Type*} [Fintype ι]
    (cost : ℝ → ℝ → ℝ) {beta alpha : ℝ}
    (hbeta : 0 < beta) (halpha : 0 < alpha)
    (halphaOne : alpha ≤ 1) (hmargin : 1 - beta < alpha)
    (family : ActualPintzGoodHeightCandidateFamily ι) :
    ActualSelectedHeightNaturalPointRemainderCertificate beta
      (actualPintzCertifiedOptimalHeight cost alpha halpha family) :=
  actualSelectedHeightNaturalPointRemainderCertificate_of_finite_switching
    (actualPintzCertifiedOptimalHeight cost alpha halpha family)
    (fun i => actualPintzCandidateHeight alpha (family.selector i))
    (actualPintzCertifiedOptimalHeight_eq_candidate
      cost alpha halpha family)
    (fun i =>
      actualPintzCandidateHeight_actualNaturalRemainderCertificate
        hbeta halpha halphaOne hmargin (family.selector i))

/-- A common visible-positive-zero envelope for every certified candidate is
inherited by the exact pointwise optimizer. -/
theorem actualPintzCertifiedOptimalHeight_isNaturalPositiveZeroFreeEnvelope
    {ι : Type*} [Fintype ι]
    (cost : ℝ → ℝ → ℝ) {alpha : ℝ} (halpha : 0 < alpha)
    (family : ActualPintzGoodHeightCandidateFamily ι)
    (gap : ℕ → ℝ)
    (henvelope :
      ∀ i, IsNaturalPositiveZeroFreeEnvelope
        (actualPintzCandidateHeight alpha (family.selector i)) gap) :
    IsNaturalPositiveZeroFreeEnvelope
      (actualPintzCertifiedOptimalHeight cost alpha halpha family) gap := by
  intro m rho hrho
  rcases actualPintzCertifiedOptimalHeight_eq_candidate
      cost alpha halpha family (m : ℝ) with ⟨i, hi⟩
  apply henvelope i m rho
  rw [hi] at hrho
  exact hrho

end PrimeNumberTheorem
