import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightGoodHeightChoice
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTRealOrdinateDecay

/-!
# Actual natural-point remainder at the selected good height

This module converts the existing `TruncatedPNTErrorCertificate` into a bound
for the actual multiplicity-aware explicit-formula approximation.  At depth
zero the finite trivial-zero sum vanishes; the only difference between the
truncated contour formula and `explicitFormulaApproxWithMultiplicity` is the
closed logarithmic trivial-zero term.

The resulting upper bound is a fully explicit function of the selected height.
Its target-amplitude decay is retained as a separate, auditable analytic
statement.
-/

namespace PrimeNumberTheorem

open Complex Filter Topology
open scoped BigOperators

/-- A depth-zero truncated contour certificate bounds the actual
multiplicity-aware explicit-formula approximation error after adding only the
closed logarithmic trivial-zero term. -/
theorem
    TruncatedPNTErrorCertificate.norm_explicitFormulaApproxWithMultiplicity_sub_le
    {x T : ℝ} (certificate : TruncatedPNTErrorCertificate x T)
    (htrivial : certificate.trivialContribution = 0) :
    ‖explicitFormulaApproxWithMultiplicity x T -
        (chebyshevPsi0 x : ℂ)‖ ≤
      certificate.remainderBound +
        ‖(1 / 2 : ℂ) * (Real.log (1 - x ^ (-2 : ℝ)) : ℂ)‖ := by
  let formulaError : ℂ :=
    certificate.trivialContribution +
      ((x : ℂ) - deriv riemannZeta 0 / riemannZeta 0 +
        ∑ rho ∈ nontrivialZerosFinset T,
          pntFiniteZeroContribution x rho) -
      (chebyshevPsi0 x : ℂ)
  let logTerm : ℂ :=
    (1 / 2 : ℂ) * (Real.log (1 - x ^ (-2 : ℝ)) : ℂ)
  have hsum :=
    sum_pntFiniteZeroContribution_eq_neg_finiteNontrivialZeroSumWithMultiplicity
      x T
  have hidentity :
      explicitFormulaApproxWithMultiplicity x T -
          (chebyshevPsi0 x : ℂ) =
        formulaError - logTerm := by
    dsimp [formulaError, logTerm]
    rw [htrivial, zero_add, hsum]
    unfold explicitFormulaApproxWithMultiplicity
    ring
  rw [hidentity]
  calc
    ‖formulaError - logTerm‖ ≤ ‖formulaError‖ + ‖logTerm‖ :=
      norm_sub_le _ _
    _ ≤ certificate.remainderBound + ‖logTerm‖ := by
      gcongr
      exact certificate.formula_bound

/-- Relative real-part form of the actual approximation-error bound. -/
theorem
    TruncatedPNTErrorCertificate.abs_actualPNTExplicitFormulaRelativeRemainder_le
    {x T : ℝ} (certificate : TruncatedPNTErrorCertificate x T)
    (htrivial : certificate.trivialContribution = 0)
    (hx : 0 < x) :
    |(((chebyshevPsi0 x : ℂ) -
        explicitFormulaApproxWithMultiplicity x T) / (x : ℂ)).re| ≤
      (certificate.remainderBound +
        ‖(1 / 2 : ℂ) * (Real.log (1 - x ^ (-2 : ℝ)) : ℂ)‖) / x := by
  calc
    |(((chebyshevPsi0 x : ℂ) -
        explicitFormulaApproxWithMultiplicity x T) / (x : ℂ)).re| ≤
        ‖((chebyshevPsi0 x : ℂ) -
          explicitFormulaApproxWithMultiplicity x T) / (x : ℂ)‖ :=
      abs_re_le_norm _
    _ =
        ‖explicitFormulaApproxWithMultiplicity x T -
          (chebyshevPsi0 x : ℂ)‖ / x := by
      rw [norm_div, norm_sub_rev, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hx]
    _ ≤
        (certificate.remainderBound +
          ‖(1 / 2 : ℂ) *
            (Real.log (1 - x ^ (-2 : ℝ)) : ℂ)‖) / x := by
      exact div_le_div_of_nonneg_right
        (certificate.norm_explicitFormulaApproxWithMultiplicity_sub_le
          htrivial) hx.le

/-- Fully explicit natural-point upper bound for the actual selected-height
relative approximation remainder. -/
noncomputable def selectedUniformGoodHeightNaturalRemainderUpperBound
    (alpha : ℝ) (selection : UniformNaturalPointGoodHeightSelection)
    (m : ℕ) : ℝ :=
  (cofinalPNTFormulaRemainderBound selection.constant
      ((m : ℝ) ^ alpha - 1)
      (selectedUniformGoodHeight alpha selection (m : ℝ)) m 0 +
    ‖(1 / 2 : ℂ) *
      (Real.log (1 - (m : ℝ) ^ (-2 : ℝ)) : ℂ)‖) / (m : ℝ)

/-- The selected-height actual explicit-formula remainder is eventually
bounded by the explicit depth-zero natural-point majorant. -/
theorem eventually_abs_selectedUniformGoodHeight_actualRemainder_le
    {alpha : ℝ} (halpha : 0 < alpha)
    (selection : UniformNaturalPointGoodHeightSelection) :
    ∀ᶠ m : ℕ in atTop,
      |actualPNTExplicitFormulaRelativeRemainder
        (selectedUniformGoodHeight alpha selection) (m : ℝ)| ≤
      selectedUniformGoodHeightNaturalRemainderUpperBound
        alpha selection m := by
  have hpower :
      Tendsto (fun x : ℝ => x ^ alpha) atTop atTop :=
    tendsto_rpow_atTop halpha
  have hlargeReal : ∀ᶠ x : ℝ in atTop, 9 ≤ x ^ alpha :=
    (tendsto_atTop.1 hpower) 9
  have hlargeNat : ∀ᶠ m : ℕ in atTop, 9 ≤ (m : ℝ) ^ alpha :=
    tendsto_natCast_atTop_atTop.eventually hlargeReal
  filter_upwards [hlargeNat, eventually_ge_atTop (3 : ℕ)] with
      m hlarge hm
  have hbase : 8 ≤ (m : ℝ) ^ alpha - 1 := by linarith
  rcases
      selectedUniformGoodHeight_truncatedCertificate
        selection m 0 hm hbase with
    ⟨certificate, htrivial, hremainder⟩
  have hmpos : 0 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) hm)
  have hbound :=
    certificate.abs_actualPNTExplicitFormulaRelativeRemainder_le
      (htrivial.trans (cofinalTrivialZeroContribution_zero m))
      hmpos
  unfold actualPNTExplicitFormulaRelativeRemainder
  rw [hremainder] at hbound
  simpa [selectedUniformGoodHeightNaturalRemainderUpperBound] using hbound

/-- Eventual domination by a natural-point target-negligible majorant
transfers target negligibility to the dominated remainder. -/
theorem NaturalPointTargetAmplitudeNegligible.of_eventually_abs_le
    {amplitude majorant remainder : ℕ → ℝ}
    (hamplitude : ∀ᶠ m in atTop, 0 < amplitude m)
    (hmajorant :
      NaturalPointTargetAmplitudeNegligible amplitude majorant)
    (hbound : ∀ᶠ m in atTop, |remainder m| ≤ majorant m) :
    NaturalPointTargetAmplitudeNegligible amplitude remainder := by
  unfold NaturalPointTargetAmplitudeNegligible at hmajorant ⊢
  refine squeeze_zero' ?_ ?_ hmajorant
  · filter_upwards [hamplitude] with m hm
    exact div_nonneg (abs_nonneg _) hm.le
  · filter_upwards [hamplitude, hbound] with m hm hboundM
    exact div_le_div_of_nonneg_right
      (hboundM.trans (le_abs_self (majorant m))) hm.le

/-- The remaining explicit analytic obligation: the displayed selected-height
majorant is negligible on the target-zero scale. -/
structure SelectedUniformGoodHeightNaturalRemainderMajorantCertificate
    (beta alpha : ℝ)
    (selection : UniformNaturalPointGoodHeightSelection) : Prop where
  negligible :
    NaturalPointTargetAmplitudeNegligible
      (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
      (selectedUniformGoodHeightNaturalRemainderUpperBound alpha selection)

/-- A target-negligible explicit majorant constructs the natural-point actual
remainder certificate expected by the lower transfer. -/
theorem
    SelectedUniformGoodHeightNaturalRemainderMajorantCertificate.actualRemainderCertificate
    {beta alpha : ℝ} (halpha : 0 < alpha)
    {selection : UniformNaturalPointGoodHeightSelection}
    (certificate :
      SelectedUniformGoodHeightNaturalRemainderMajorantCertificate
        beta alpha selection) :
    ActualSelectedHeightNaturalPointRemainderCertificate beta
      (selectedUniformGoodHeight alpha selection) where
  negligible :=
    NaturalPointTargetAmplitudeNegligible.of_eventually_abs_le
      (eventually_naturalPoint_pos_of_eventually_pos
        (targetZeroPowerAmplitude_eventually_pos beta))
      certificate.negligible
      (eventually_abs_selectedUniformGoodHeight_actualRemainder_le
        halpha selection)

end PrimeNumberTheorem
