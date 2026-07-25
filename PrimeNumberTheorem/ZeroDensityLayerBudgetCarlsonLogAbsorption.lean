import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonTargetRegion
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Absorbing Carlson's logarithmic factor

Carlson's concrete density theorem contains `(log T)^4`.  The strict negative
power margin obtained in the admissible target region absorbs this factor.
This file proves the required real-asymptotic statement and specializes it to
the Carlson target-layer exponent.
-/

namespace PrimeNumberTheorem

open Filter

/-- A negative real power tends to zero at positive infinity. -/
theorem tendsto_rpow_neg_atTop_nhds_zero
    {r : ℝ} (hr : r < 0) :
    Filter.Tendsto (fun x : ℝ => x ^ r)
      Filter.atTop (nhds 0) := by
  have hpositive : 0 < -r := neg_pos.mpr hr
  have hbase :
      Filter.Tendsto (fun x : ℝ => x ^ (-r))
        Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop hpositive
  have hinverse :
      Filter.Tendsto (fun x : ℝ => (x ^ (-r))⁻¹)
        Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hbase
  refine hinverse.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  simpa using (Real.rpow_neg hx (-r)).symm

/-- Any strictly negative power margin absorbs the fixed fourth power of the
logarithm. -/
theorem tendsto_rpow_mul_log_four_atTop_nhds_zero
    {exponent epsilon : ℝ}
    (hepsilon : 0 < epsilon)
    (hmargin : exponent + epsilon < 0) :
    Filter.Tendsto
      (fun x : ℝ => x ^ exponent * (Real.log x) ^ (4 : ℕ))
      Filter.atTop (nhds 0) := by
  have hlogRpow :
      (fun x : ℝ => (Real.log x) ^ (4 : ℝ))
        =o[Filter.atTop] (fun x => x ^ epsilon) :=
    isLittleO_log_rpow_rpow_atTop 4 hepsilon
  have hlog :
      (fun x : ℝ => (Real.log x) ^ (4 : ℕ))
        =o[Filter.atTop] (fun x => x ^ epsilon) := by
    refine hlogRpow.congr' ?_ Filter.EventuallyEq.rfl
    exact Filter.Eventually.of_forall fun x => by
      exact Real.rpow_natCast (Real.log x) 4
  have hraw :
      (fun x : ℝ => (Real.log x) ^ (4 : ℕ) * x ^ exponent)
        =o[Filter.atTop]
      (fun x => x ^ epsilon * x ^ exponent) :=
    hlog.mul_isBigO
      (Asymptotics.isBigO_refl (fun x : ℝ => x ^ exponent)
        Filter.atTop)
  have htarget :
      (fun x : ℝ => x ^ exponent * (Real.log x) ^ (4 : ℕ))
        =o[Filter.atTop]
      (fun x => x ^ (exponent + epsilon)) := by
    refine hraw.congr' ?_ ?_
    · exact Filter.Eventually.of_forall fun x => by ring
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [Real.rpow_add hx]
      ring
  exact htarget.tendsto_zero_of_tendsto
    (tendsto_rpow_neg_atTop_nhds_zero hmargin)

/-- The actual Carlson logarithmic target majorant at polynomial height. -/
noncomputable def carlsonTargetNormalizedLogMajorant
    (beta sigma alpha : ℝ) (x : ℝ) : ℝ :=
  x ^ targetAmplitudePintzCarlsonExponent beta sigma
      (carlsonClassicalPolynomialDensityExponent alpha sigma) *
    (Real.log x) ^ (4 : ℕ)

/-- A strict Carlson exponent margin makes the full normalized majorant,
including `(log x)^4`, tend to zero. -/
theorem tendsto_carlsonTargetNormalizedLogMajorant
    {beta sigma alpha epsilon : ℝ}
    (hepsilon : 0 < epsilon)
    (hmargin :
      targetAmplitudePintzCarlsonExponent beta sigma
          (carlsonClassicalPolynomialDensityExponent alpha sigma) +
        epsilon < 0) :
    Filter.Tendsto
      (carlsonTargetNormalizedLogMajorant beta sigma alpha)
      Filter.atTop (nhds 0) := by
  exact tendsto_rpow_mul_log_four_atTop_nhds_zero hepsilon hmargin

/-- Every target real part in Carlson's admissible region admits a polynomial
height for which the complete power-times-logarithm majorant tends to zero. -/
theorem exists_carlsonPolynomialHeight_normalizedLogMajorant_tendsto_zero
    {beta sigma : ℝ} (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (hbeta :
      carlsonClassicalTargetThreshold sigma < beta) :
    ∃ alpha : ℝ,
      1 - beta < alpha ∧
      Filter.Tendsto
        (carlsonTargetNormalizedLogMajorant beta sigma alpha)
        Filter.atTop (nhds 0) := by
  obtain ⟨alpha, epsilon, hepsilon, hcontour, hmargin⟩ :=
    exists_carlsonPolynomialHeight_targetAmplitude_strictMargin
      hsigma hsigmaOne hbeta
  exact ⟨alpha, hcontour,
    tendsto_carlsonTargetNormalizedLogMajorant hepsilon hmargin⟩

end PrimeNumberTheorem
