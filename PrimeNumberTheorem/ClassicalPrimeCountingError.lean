import PrimeNumberTheorem.ClassicalPNTError

open Filter Topology

namespace PrimeNumberTheorem

/-- The prime-power correction is absorbed into the de la Vallee Poussin
scale, transferring the proved `psi` remainder to Chebyshev's `theta`. -/
theorem exists_eventually_abs_chebyshevTheta_sub_id_le_exp_neg_sqrt_log :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
      |Chebyshev.theta x - x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  rcases exists_abs_chebyshevPsi_sub_id_le_exp_neg_sqrt_log with
    ⟨c, C, X, hc, hC, hpsi⟩
  let a : ℝ := c / 2
  have ha : 0 < a := div_pos hc (by norm_num)
  have hsqrtLogTop :
      Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have hu : ∀ᶠ x : ℝ in atTop, 4 * a ≤ Real.sqrt (Real.log x) :=
    tendsto_atTop.1 hsqrtLogTop (4 * a)
  refine ⟨a, C + 8, ha, add_nonneg hC (by norm_num), ?_⟩
  filter_upwards [eventually_ge_atTop X,
      eventually_ge_atTop (Real.exp 1), hu] with x hxX hxexp hux
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxexp
  have hx0 : 0 ≤ x := hxpos.le
  have hx1 : 1 ≤ x := by
    have hone_exp : (1 : ℝ) ≤ Real.exp 1 := by
      rw [Real.one_le_exp_iff]
      norm_num
    exact hone_exp.trans hxexp
  have hlog1 : 1 ≤ Real.log x :=
    (Real.le_log_iff_exp_le hxpos).2 hxexp
  have hlog0 : 0 ≤ Real.log x := hlog1.trans' zero_le_one
  have hu0 : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
  have huSq : (Real.sqrt (Real.log x)) ^ 2 = Real.log x :=
    Real.sq_sqrt hlog0
  let scale : ℝ := x * Real.exp (-a * Real.sqrt (Real.log x))
  have hscale0 : 0 ≤ scale := by
    dsimp [scale]
    positivity
  have hexpWeak :
      Real.exp (-c * Real.sqrt (Real.log x)) ≤
        Real.exp (-a * Real.sqrt (Real.log x)) := by
    apply Real.exp_le_exp.mpr
    dsimp [a]
    nlinarith [mul_nonneg hc.le hu0]
  have hpsiWeak : |chebyshevPsi x - x| ≤ C * scale := by
    calc
      |chebyshevPsi x - x| ≤
          C * x * Real.exp (-c * Real.sqrt (Real.log x)) := hpsi x hxX
      _ ≤ C * x * Real.exp (-a * Real.sqrt (Real.log x)) := by
        exact mul_le_mul_of_nonneg_left hexpWeak (mul_nonneg hC hx0)
      _ = C * scale := by simp [scale, mul_assoc]
  have hlogPow :
      Real.log x ≤ x ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) :=
    Real.log_le_rpow_div hx0 (by norm_num)
  have hdiffPow :
      2 * Real.sqrt x * Real.log x ≤ 8 * x ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    calc
      2 * x ^ (1 / 2 : ℝ) * Real.log x ≤
          2 * x ^ (1 / 2 : ℝ) *
            (x ^ (1 / 4 : ℝ) / (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogPow (by positivity)
      _ = 8 * x ^ (3 / 4 : ℝ) := by
        rw [show (3 / 4 : ℝ) = (1 / 2 : ℝ) + 1 / 4 by ring,
          Real.rpow_add hxpos]
        ring
  have hrpowScale : x ^ (3 / 4 : ℝ) ≤ scale := by
    have hmul := mul_le_mul_of_nonneg_right hux hu0
    have hexponent :
        Real.log x * (3 / 4 : ℝ) ≤
          Real.log x + (-a * Real.sqrt (Real.log x)) := by
      nlinarith [huSq]
    calc
      x ^ (3 / 4 : ℝ) =
          Real.exp (Real.log x * (3 / 4 : ℝ)) := by
        rw [Real.rpow_def_of_pos hxpos]
      _ ≤ Real.exp (Real.log x + (-a * Real.sqrt (Real.log x))) :=
        Real.exp_le_exp.mpr hexponent
      _ = scale := by
        dsimp [scale]
        rw [Real.exp_add, Real.exp_log hxpos]
  have hdiffScale :
      |chebyshevPsi x - Chebyshev.theta x| ≤ 8 * scale := by
    have hdiff := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx1
    have hdiff' :
        |chebyshevPsi x - Chebyshev.theta x| ≤
          2 * Real.sqrt x * Real.log x := by
      simpa [chebyshevPsi_eq_mathlib] using hdiff
    exact hdiff'.trans (hdiffPow.trans
      (mul_le_mul_of_nonneg_left hrpowScale (by norm_num)))
  have hdecomp :
      Chebyshev.theta x - x =
        (chebyshevPsi x - x) + -(chebyshevPsi x - Chebyshev.theta x) := by
    ring
  calc
    |Chebyshev.theta x - x| =
        |(chebyshevPsi x - x) +
          -(chebyshevPsi x - Chebyshev.theta x)| := by rw [hdecomp]
    _ ≤ |chebyshevPsi x - x| +
        |-(chebyshevPsi x - Chebyshev.theta x)| := abs_add_le _ _
    _ ≤ C * scale + 8 * scale := by
      simpa only [abs_neg] using add_le_add hpsiWeak hdiffScale
    _ = (C + 8) * x * Real.exp (-a * Real.sqrt (Real.log x)) := by
      dsimp [scale]
      ring

end PrimeNumberTheorem
