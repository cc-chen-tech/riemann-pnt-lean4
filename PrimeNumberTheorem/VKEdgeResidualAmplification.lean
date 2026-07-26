import MathlibAux.ResidualSecondMoment
import PrimeNumberTheorem.VKEdgePiOverTwoSweptL2

open Complex Filter MeasureTheory Set Topology

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- The normalized real contribution of a conjugate zero pair. -/
def cosineZeroPair (m gamma phase y : ℝ) : ℝ :=
  -2 * m * Real.cos (gamma * y - phase)

/-- Exact second moment of a conjugate zero pair on an oriented interval. -/
theorem intervalIntegral_cosineZeroPair_sq
    {m gamma phase a b : ℝ} (hgamma : gamma ≠ 0) :
    (∫ y in a..b, cosineZeroPair m gamma phase y ^ 2) =
      2 * m ^ 2 * (b - a) +
        m ^ 2 / gamma *
          (Real.sin (2 * gamma * b - 2 * phase) -
            Real.sin (2 * gamma * a - 2 * phase)) := by
  let primitive : ℝ → ℝ := fun y =>
    2 * m ^ 2 * y +
      m ^ 2 / gamma * Real.sin (2 * gamma * y - 2 * phase)
  have hderiv (y : ℝ) :
      HasDerivAt primitive (cosineZeroPair m gamma phase y ^ 2) y := by
    have hlinear :
        HasDerivAt (fun x : ℝ => 2 * gamma * x - 2 * phase)
          (2 * gamma) y := by
      convert ((hasDerivAt_id y).const_mul (2 * gamma)).sub_const
        (2 * phase) using 1 <;> ring
    have hsin :
        HasDerivAt
          (fun x : ℝ =>
            m ^ 2 / gamma *
              Real.sin (2 * gamma * x - 2 * phase))
          (m ^ 2 / gamma *
            (Real.cos (2 * gamma * y - 2 * phase) *
              (2 * gamma))) y :=
      hlinear.sin.const_mul (m ^ 2 / gamma)
    have hmain :
        HasDerivAt (fun x : ℝ => 2 * m ^ 2 * x)
          (2 * m ^ 2) y := by
      convert (hasDerivAt_id y).const_mul (2 * m ^ 2) using 1 <;> ring
    convert hmain.add hsin using 1
    · rw [show 2 * gamma * y - 2 * phase =
          2 * (gamma * y - phase) by ring,
        Real.cos_two_mul]
      unfold cosineZeroPair
      field_simp [hgamma]
      ring
  have hint :
      IntervalIntegrable
        (fun y => cosineZeroPair m gamma phase y ^ 2)
        volume a b := by
    apply Continuous.intervalIntegrable
    unfold cosineZeroPair
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _hy => hderiv y) hint]
  dsimp [primitive]
  ring

/-- The target pair has mean-square density `2m²`, up to an explicit
endpoint error. -/
theorem integral_Icc_cosineZeroPair_sq_le
    {m gamma phase a b : ℝ}
    (hab : a ≤ b) (hgamma : gamma ≠ 0) :
    (∫ y in Icc a b, cosineZeroPair m gamma phase y ^ 2) ≤
      2 * m ^ 2 * (b - a) + 2 * m ^ 2 / |gamma| := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab,
    intervalIntegral_cosineZeroPair_sq hgamma]
  let delta :=
    Real.sin (2 * gamma * b - 2 * phase) -
      Real.sin (2 * gamma * a - 2 * phase)
  have hdelta : |delta| ≤ 2 := by
    dsimp [delta]
    calc
      |Real.sin (2 * gamma * b - 2 * phase) -
          Real.sin (2 * gamma * a - 2 * phase)| ≤
          |Real.sin (2 * gamma * b - 2 * phase)| +
            |Real.sin (2 * gamma * a - 2 * phase)| :=
        abs_sub _ _
      _ ≤ 1 + 1 :=
        add_le_add (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
      _ = 2 := by norm_num
  have hgammaAbs : 0 < |gamma| := abs_pos.mpr hgamma
  have habs :
      |m ^ 2 / gamma * delta| =
        m ^ 2 / |gamma| * |delta| := by
    rw [abs_mul, abs_div, abs_pow, sq_abs]
  have hterm :
      m ^ 2 / gamma * delta ≤ 2 * m ^ 2 / |gamma| := by
    calc
      m ^ 2 / gamma * delta ≤ |m ^ 2 / gamma * delta| :=
        le_abs_self _
      _ = m ^ 2 / |gamma| * |delta| := habs
      _ ≤ m ^ 2 / |gamma| * 2 :=
        mul_le_mul_of_nonneg_left hdelta
          (div_nonneg (sq_nonneg m) hgammaAbs.le)
      _ = 2 * m ^ 2 / |gamma| := by ring
  dsimp [delta] at hterm
  linarith

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
