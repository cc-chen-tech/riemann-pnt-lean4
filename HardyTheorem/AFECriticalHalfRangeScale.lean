import HardyTheorem.AFECriticalHalfRangeLogBound

/-!
# Explicit broad Gaussian scale for the half-range AFE estimate

We set `Delta = 4 * U^(19/20)`.  This is long enough for a square-root zeta
polynomial multiplied by every mollifier of length at most `U^(9/20)`.
-/

namespace HardyTheorem
namespace AFE

/-- Elementary square-root scale conditions used by the parameter-ready
critical AFE theorem. -/
theorem criticalHalfRange_sqrt_scale_bounds
    {U : ℝ} (hTwoPi : 2 * Real.pi ≤ U) (hFour : 4 ≤ U) :
    1 ≤ Real.sqrt (U / (2 * Real.pi)) ∧
      2 * Real.sqrt (U / (2 * Real.pi)) ≤ U := by
  have hdenPos : 0 < 2 * Real.pi := by positivity
  have hdenOne : 1 ≤ 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hratioOne : 1 ≤ U / (2 * Real.pi) := by
    apply (le_div_iff₀ hdenPos).2
    simpa only [one_mul] using hTwoPi
  have hsqrtOne : 1 ≤ Real.sqrt (U / (2 * Real.pi)) := by
    simpa using Real.sqrt_le_sqrt hratioOne
  have hUpos : 0 < U := by linarith
  have hratioU : U / (2 * Real.pi) ≤ U :=
    div_le_self hUpos.le hdenOne
  have hsqrtRatio :
      Real.sqrt (U / (2 * Real.pi)) ≤ Real.sqrt U :=
    Real.sqrt_le_sqrt hratioU
  have hsqrtU0 : 0 ≤ Real.sqrt U := Real.sqrt_nonneg U
  have hsqrtU2 : 2 ≤ Real.sqrt U := by
    rw [Real.le_sqrt (by norm_num)]
    all_goals nlinarith
  have hsqrtUSq : (Real.sqrt U) ^ 2 = U := Real.sq_sqrt hUpos.le
  have hsqrtUHalf : Real.sqrt U ≤ U / 2 := by
    have hprod : 0 ≤ Real.sqrt U * (Real.sqrt U - 2) :=
      mul_nonneg hsqrtU0 (sub_nonneg.mpr hsqrtU2)
    nlinarith
  exact ⟨hsqrtOne, by linarith⟩

/-- The broad scale `4*U^(19/20)` dominates the product of the canonical
square-root cutoff and a mollifier of length at most `U^(9/20)`. -/
theorem four_mul_sqrt_scale_mul_length_le_halfRangeDelta
    {U : ℝ} {X : ℕ} (hU : 1 ≤ U)
    (hX : (X : ℝ) ≤ U ^ (9 / 20 : ℝ)) :
    4 * Real.sqrt (U / (2 * Real.pi)) * (X : ℝ) ≤
      4 * U ^ (19 / 20 : ℝ) := by
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have hdenOne : 1 ≤ 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hratioU : U / (2 * Real.pi) ≤ U :=
    div_le_self hUpos.le hdenOne
  have hsqrt : Real.sqrt (U / (2 * Real.pi)) ≤ U ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt hratioU
  calc
    4 * Real.sqrt (U / (2 * Real.pi)) * (X : ℝ) ≤
        4 * U ^ (1 / 2 : ℝ) * U ^ (9 / 20 : ℝ) := by
      gcongr
    _ = 4 * U ^ (19 / 20 : ℝ) := by
      calc
        4 * U ^ (1 / 2 : ℝ) * U ^ (9 / 20 : ℝ) =
            4 * (U ^ (1 / 2 : ℝ) * U ^ (9 / 20 : ℝ)) := by ring
        _ = 4 * U ^ ((1 / 2 : ℝ) + 9 / 20) := by
          rw [Real.rpow_add hUpos]
        _ = 4 * U ^ (19 / 20 : ℝ) := by norm_num

/-- The complete conditional critical-line estimate at the explicit broad
Gaussian width `Delta = 4*U^(19/20)`. -/
theorem setIntegral_gaussian_normSq_criticalAfeProduct_le_halfRange_scale
    (hAFE : zeta_critical_afe_target) :
    ∃ R > (0 : ℝ), ∀ {X : ℕ} {L U : ℝ},
      1 < L → L ≤ U → 2 ≤ X →
      (X : ℝ) ≤ L ^ (9 / 20 : ℝ) →
      2 * Real.pi ≤ U → 4 ≤ U →
      ∀ w : ℝ,
      (∫ t : ℝ in Set.Icc L U,
        Real.exp (-((t - w) ^ 2) /
            (4 * U ^ (19 / 20 : ℝ)) ^ 2) *
          Complex.normSq
            (riemannZeta ((1 / 2 : ℂ) + Complex.I * t) *
              selbergMoebiusMollifier X
                ((1 / 2 : ℂ) + Complex.I * t))) ≤
        3 * Real.sqrt
          (Real.pi / (1 / (4 * U ^ (19 / 20 : ℝ)) ^ 2)) *
          (256 * MathlibAux.gaussianBucketSchurConstant *
              (1 + Real.log U) ^ 6 + 4 * R ^ 2) := by
  obtain ⟨R, hR, hwindow⟩ :=
    setIntegral_gaussian_normSq_criticalAfeProduct_le_halfRange_log hAFE
  refine ⟨R, hR, ?_⟩
  intro X L U hL hLU hX hXscale hTwoPi hFour w
  have hU : 1 ≤ U := hL.le.trans hLU
  have hXU : (X : ℝ) ≤ U ^ (9 / 20 : ℝ) := by
    exact hXscale.trans
      (Real.rpow_le_rpow (zero_lt_one.trans hL).le hLU (by norm_num))
  obtain ⟨hUsqrt, hsqrtU⟩ :=
    criticalHalfRange_sqrt_scale_bounds hTwoPi hFour
  exact hwindow hL hLU hX hXscale hUsqrt hsqrtU
    (four_mul_sqrt_scale_mul_length_le_halfRangeDelta hU hXU) w

end AFE
end HardyTheorem
