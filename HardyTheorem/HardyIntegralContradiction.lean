import HardyTheorem.HardyIntegralUpperBound

open Complex Filter MeasureTheory Set Topology

namespace HardyTheorem

/-- Hardy's integral upper and lower bounds rule out a bounded real zero set
for the Hardy Z-function. -/
theorem hardyZ_zero_set_not_isBounded :
    ¬ Bornology.IsBounded {t : ℝ | hardyZ t = 0} := by
  intro hbounded
  obtain ⟨c, Tlower, hc, _hTlower, hlower⟩ :=
    exists_integral_norm_riemannZeta_critical_line_ge_mul
  obtain ⟨C, Tupper, _hC, _hTupper, hupper⟩ :=
    exists_abs_integral_hardyZ_le_rpow_three_quarters
  have heq :=
    eventually_abs_integral_hardyZ_eq_integral_norm_zeta_of_bounded_zeros
      hbounded
  have hgrowth :
      Tendsto (fun T : ℝ => c * T ^ (1 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).const_mul_atTop hc
  have hdominates :
      ∀ᶠ T : ℝ in atTop, C < c * T ^ (1 / 4 : ℝ) :=
    hgrowth.eventually_gt_atTop C
  obtain ⟨Teq, hEq_after⟩ := eventually_atTop.1 heq
  obtain ⟨Tdom, hdom_after⟩ := eventually_atTop.1 hdominates
  let T := max Teq (max Tlower (max Tupper (max 1 Tdom)))
  have hTeq : Teq ≤ T := le_max_left _ _
  have hrest : max Tlower (max Tupper (max 1 Tdom)) ≤ T :=
    le_max_right _ _
  have hTl : Tlower ≤ T := (le_max_left _ _).trans hrest
  have hrest' : max Tupper (max 1 Tdom) ≤ T :=
    (le_max_right _ _).trans hrest
  have hTu : Tupper ≤ T := (le_max_left _ _).trans hrest'
  have hrest'' : max 1 Tdom ≤ T := (le_max_right _ _).trans hrest'
  have hT1 : 1 ≤ T := (le_max_left _ _).trans hrest''
  have hTdom : Tdom ≤ T := (le_max_right _ _).trans hrest''
  have hEq := hEq_after T hTeq
  have hdom := hdom_after T hTdom
  have hTpos : 0 < T := zero_lt_one.trans_le hT1
  have hpowpos : 0 < T ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hTpos _
  have hstrict : C * T ^ (3 / 4 : ℝ) < c * T := by
    calc
      C * T ^ (3 / 4 : ℝ) <
          (c * T ^ (1 / 4 : ℝ)) * T ^ (3 / 4 : ℝ) :=
        mul_lt_mul_of_pos_right hdom hpowpos
      _ = c * T := by
        rw [mul_assoc, ← Real.rpow_add hTpos]
        norm_num
  have hcycle : c * T < c * T := calc
    c * T ≤ ∫ t in T..(2 * T),
        ‖riemannZeta ((1 / 2 : ℂ) + I * t)‖ := hlower T hTl
    _ = |∫ t in T..(2 * T), hardyZ t| := hEq.symm
    _ ≤ C * T ^ (3 / 4 : ℝ) := hupper T hTu
    _ < c * T := hstrict
  exact (lt_irrefl (c * T)) hcycle

/-- Critical-line zeta zeros have unbounded absolute height. -/
theorem hardy_zeros_abs_unbounded_target_proved :
    hardy_zeros_abs_unbounded_target := by
  rw [hardy_zeros_abs_unbounded_target_iff_hardyZ_abs_unbounded]
  by_contra hnot
  push Not at hnot
  obtain ⟨T, hT⟩ := hnot
  apply hardyZ_zero_set_not_isBounded
  refine (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).2 ⟨T, ?_⟩
  intro t ht
  have habs : |t| ≤ T := by
    by_contra hnotle
    exact hT t (lt_of_not_ge hnotle).le ht
  simpa [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs] using habs

/-- Hardy's theorem in its stronger unbounded positive-height form. -/
theorem hardy_zeros_unbounded_target_proved :
    hardy_zeros_unbounded_target :=
  hardy_zeros_unbounded_iff_abs_unbounded.mpr
    hardy_zeros_abs_unbounded_target_proved

/-- The classical statement that zeta has infinitely many critical-line zeros. -/
theorem hardy_theorem_target_proved : hardy_theorem_target :=
  hardy_theorem_target_of_unbounded hardy_zeros_unbounded_target_proved

end HardyTheorem
