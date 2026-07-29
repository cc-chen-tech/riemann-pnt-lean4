import PrimeNumberTheorem.VKEdgeZeroClusterRemainderL2

open Complex MeasureTheory Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# Explicit local L2 control of the closed explicit-formula terms

After deleting the almost-everywhere-zero midpoint jump, the actual cluster
remainder consists of a complementary zero sum, a finite-height
approximation error, and closed elementary terms.  This module gives the
closed terms an explicit exponentially decaying local second-moment bound.
-/

/-- A fixed explicit upper bound for the closed terms on logarithmic
coordinates `y >= 1`. -/
noncomputable def zeroPackageClosedTermsUniformBound : ℝ :=
  Real.log (2 * Real.pi) +
    (1 / 2 : ℝ) * Real.exp (-2) / (1 - Real.exp (-2))

/-- The closed terms with real-exponent normalization. -/
noncomputable def normalizedZeroPackageClosedTerms
    (beta y : ℝ) : ℂ :=
  (Real.exp (-beta * y) : ℂ) *
    ZeroForcedOscillation.zeroPackageClosedTerms y

/-- Local second moment of the normalized closed terms. -/
noncomputable def normalizedZeroPackageClosedTermsSecondMoment
    (beta a L : ℝ) : ℝ :=
  ∫ y in a..(a + L),
    ‖normalizedZeroPackageClosedTerms beta y‖ ^ 2

/-- The normalized complementary-zero contribution. -/
noncomputable def normalizedFiniteZeroClusterComplementContribution
    (S : Finset ℂ) (T beta y : ℝ) : ℂ :=
  (Real.exp (-beta * y) : ℂ) *
    finiteZeroClusterComplementContribution S (Real.exp y) T

/-- The normalized finite-height explicit-formula approximation error. -/
noncomputable def normalizedFiniteZeroClusterApproximationError
    (T beta y : ℝ) : ℂ :=
  (Real.exp (-beta * y) : ℂ) *
    (explicitFormulaApproxWithMultiplicity (Real.exp y) T -
      (chebyshevPsi0 (Real.exp y) : ℂ))

/-- The explicit uniform closed-term bound is strictly positive. -/
theorem zero_lt_zeroPackageClosedTermsUniformBound :
    0 < zeroPackageClosedTermsUniformBound := by
  have hpi : 1 < 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hlog : 0 < Real.log (2 * Real.pi) :=
    Real.log_pos hpi
  have hqpos : 0 < Real.exp (-2) := Real.exp_pos _
  have hqlt : Real.exp (-2) < 1 :=
    Real.exp_lt_one_iff.mpr (by norm_num)
  have htail :
      0 < (1 / 2 : ℝ) * Real.exp (-2) / (1 - Real.exp (-2)) := by
    exact div_pos (mul_pos (by norm_num) hqpos) (sub_pos.mpr hqlt)
  unfold zeroPackageClosedTermsUniformBound
  linarith

/-- Uniform pointwise bound for the elementary closed terms on `y >= 1`. -/
theorem norm_zeroPackageClosedTerms_le_uniformBound
    {y : ℝ} (hy : 1 ≤ y) :
    ‖ZeroForcedOscillation.zeroPackageClosedTerms y‖ ≤
      zeroPackageClosedTermsUniformBound := by
  have hypos : 0 < y := zero_lt_one.trans_le hy
  have hbase :=
    ZeroForcedOscillation.norm_zeroPackageClosedTerms_le_log_two_pi_add_exp_neg_div
      hypos
  have hqle : Real.exp (-2 * y) ≤ Real.exp (-2) := by
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hqylt : Real.exp (-2 * y) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith)
  have hq1lt : Real.exp (-2) < 1 :=
    Real.exp_lt_one_iff.mpr (by norm_num)
  have hratio :
      Real.exp (-2 * y) / (1 - Real.exp (-2 * y)) ≤
        Real.exp (-2) / (1 - Real.exp (-2)) := by
    rw [div_le_div_iff₀ (sub_pos.mpr hqylt) (sub_pos.mpr hq1lt)]
    nlinarith
  calc
    ‖ZeroForcedOscillation.zeroPackageClosedTerms y‖ ≤
        Real.log (2 * Real.pi) +
          (1 / 2 : ℝ) * Real.exp (-2 * y) /
            (1 - Real.exp (-2 * y)) := hbase
    _ = Real.log (2 * Real.pi) +
          (1 / 2 : ℝ) *
            (Real.exp (-2 * y) / (1 - Real.exp (-2 * y))) := by
      ring
    _ ≤ Real.log (2 * Real.pi) +
          (1 / 2 : ℝ) *
            (Real.exp (-2) / (1 - Real.exp (-2))) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hratio (by norm_num))
    _ = Real.log (2 * Real.pi) +
          (1 / 2 : ℝ) * Real.exp (-2) /
            (1 - Real.exp (-2)) := by
      ring
    _ = zeroPackageClosedTermsUniformBound := rfl

/-- The normalized closed terms decay uniformly from the left endpoint of a
positive logarithmic interval. -/
theorem norm_normalizedZeroPackageClosedTerms_le_uniformBound
    {beta a y : ℝ}
    (hbeta : 0 ≤ beta) (ha : 1 ≤ a) (hay : a ≤ y) :
    ‖normalizedZeroPackageClosedTerms beta y‖ ≤
      Real.exp (-beta * a) * zeroPackageClosedTermsUniformBound := by
  have hy : 1 ≤ y := ha.trans hay
  have hclosed := norm_zeroPackageClosedTerms_le_uniformBound hy
  have hexp : Real.exp (-beta * y) ≤ Real.exp (-beta * a) := by
    exact Real.exp_le_exp.mpr (by nlinarith)
  unfold normalizedZeroPackageClosedTerms
  rw [norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-beta * y) *
          ‖ZeroForcedOscillation.zeroPackageClosedTerms y‖ ≤
        Real.exp (-beta * y) * zeroPackageClosedTermsUniformBound :=
      mul_le_mul_of_nonneg_left hclosed (Real.exp_pos _).le
    _ ≤ Real.exp (-beta * a) * zeroPackageClosedTermsUniformBound :=
      mul_le_mul_of_nonneg_right hexp
        zero_lt_zeroPackageClosedTermsUniformBound.le

private theorem continuousOn_normalizedZeroPackageClosedTerms
    {beta a b : ℝ} (ha : 1 ≤ a) :
    ContinuousOn (normalizedZeroPackageClosedTerms beta) (Icc a b) := by
  intro y hy
  have hypos : 0 < y := zero_lt_one.trans_le (ha.trans hy.1)
  have harg : 1 - Real.exp (-2 * y) ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr
      (Real.exp_lt_one_iff.mpr (by nlinarith)))
  unfold normalizedZeroPackageClosedTerms
  simp_rw [ZeroForcedOscillation.zeroPackageClosedTerms_eq_log_two_pi_add_log_term]
  have hlinearBeta :
      ContinuousAt (fun z : ℝ => -beta * z) y :=
    continuousAt_const.mul continuousAt_id
  have hlinearTwo :
      ContinuousAt (fun z : ℝ => -2 * z) y :=
    continuousAt_const.mul continuousAt_id
  have hexpBeta :
      ContinuousAt (fun z : ℝ => Real.exp (-beta * z)) y :=
    Real.continuous_exp.continuousAt.comp hlinearBeta
  have hinner :
      ContinuousAt (fun z : ℝ => 1 - Real.exp (-2 * z)) y :=
    continuousAt_const.sub
      (Real.continuous_exp.continuousAt.comp hlinearTwo)
  have hlog :
      ContinuousAt (fun z : ℝ => Real.log (1 - Real.exp (-2 * z))) y :=
    hinner.log harg
  have hcastExp :
      ContinuousAt (fun z : ℝ => (Real.exp (-beta * z) : ℂ)) y :=
    Complex.continuous_ofReal.continuousAt.comp hexpBeta
  have hcastLog :
      ContinuousAt
        (fun z : ℝ => (Real.log (1 - Real.exp (-2 * z)) : ℂ)) y :=
    Complex.continuous_ofReal.continuousAt.comp hlog
  exact
    (hcastExp.mul
      (continuousAt_const.add (continuousAt_const.mul hcastLog))).continuousWithinAt

/-- Explicit local second-moment bound for the normalized closed terms. -/
theorem normalizedZeroPackageClosedTermsSecondMoment_le
    {beta a L : ℝ}
    (hbeta : 0 ≤ beta) (ha : 1 ≤ a) (hL : 0 ≤ L) :
    normalizedZeroPackageClosedTermsSecondMoment beta a L ≤
      L * (Real.exp (-beta * a) *
        zeroPackageClosedTermsUniformBound) ^ 2 := by
  have hab : a ≤ a + L := by linarith
  have hleft :
      IntervalIntegrable
        (fun y => ‖normalizedZeroPackageClosedTerms beta y‖ ^ 2)
        volume a (a + L) := by
    exact
      ((continuousOn_normalizedZeroPackageClosedTerms
        (beta := beta) (b := a + L) ha).norm.pow 2).intervalIntegrable_of_Icc
        hab
  have hright :
      IntervalIntegrable
        (fun _ : ℝ =>
          (Real.exp (-beta * a) *
            zeroPackageClosedTermsUniformBound) ^ 2)
        volume a (a + L) :=
    intervalIntegrable_const
  have hpoint :
      ∀ y ∈ Icc a (a + L),
        ‖normalizedZeroPackageClosedTerms beta y‖ ^ 2 ≤
          (Real.exp (-beta * a) *
            zeroPackageClosedTermsUniformBound) ^ 2 := by
    intro y hy
    have hnorm :=
      norm_normalizedZeroPackageClosedTerms_le_uniformBound
        hbeta ha hy.1
    nlinarith [norm_nonneg (normalizedZeroPackageClosedTerms beta y),
      Real.exp_pos (-beta * a),
      zero_lt_zeroPackageClosedTermsUniformBound]
  have hmono :=
    intervalIntegral.integral_mono_on hab hleft hright hpoint
  simpa [normalizedZeroPackageClosedTermsSecondMoment] using hmono

/-- Exact decomposition of the normalized no-jump remainder into the only
three remaining analytic components. -/
theorem normalizedFiniteZeroClusterPsiRemainderWithoutJump_eq_components
    (S : Finset ℂ) (T beta y : ℝ) :
    normalizedFiniteZeroClusterPsiRemainderWithoutJump S T beta y =
      normalizedFiniteZeroClusterComplementContribution S T beta y +
        normalizedFiniteZeroClusterApproximationError T beta y +
        normalizedZeroPackageClosedTerms beta y := by
  unfold normalizedFiniteZeroClusterPsiRemainderWithoutJump
  unfold finiteZeroClusterPsiExplicitFormulaRemainderWithoutJump
  unfold normalizedFiniteZeroClusterComplementContribution
  unfold normalizedFiniteZeroClusterApproximationError
  unfold normalizedZeroPackageClosedTerms
  ring

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
