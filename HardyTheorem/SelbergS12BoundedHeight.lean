import HardyTheorem.SelbergS12NearOne

open Complex Set

namespace HardyTheorem

/-!
# Selberg S12: bounded-height annulus

Away from `t = 0`, the quotient `(1 / ζ(1+it)) / t` is continuous.  Its norm
is therefore bounded on every compact annulus `r ≤ |t| ≤ T`.
-/

theorem exists_norm_inv_riemannZeta_oneLine_le_mul_abs_on_annulus
    {r T : ℝ} (hr : 0 < r) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ t : ℝ, r ≤ |t| → |t| ≤ T →
        ‖(riemannZeta ((1 : ℂ) + I * t))⁻¹‖ ≤ M * |t| := by
  let K : Set ℝ := Metric.closedBall 0 T \ Metric.ball 0 r
  let f : ℝ → ℂ := fun t =>
    (riemannZeta ((1 : ℂ) + I * t))⁻¹ / (t : ℂ)
  have hK : IsCompact K :=
    (isCompact_closedBall (0 : ℝ) T).diff Metric.isOpen_ball
  have hf : ContinuousOn f K := by
    intro t ht
    have htT : |t| ≤ T := by
      have h := ht.1
      simpa [K, Metric.mem_closedBall, Real.dist_eq] using h
    have htr : r ≤ |t| := by
      have h := ht.2
      simp only [Metric.mem_ball, Real.dist_eq, sub_zero, Real.norm_eq_abs] at h
      exact le_of_not_gt h
    have ht0 : t ≠ 0 := by
      intro hzero
      subst t
      norm_num at htr
      linarith
    let z : ℝ → ℂ := fun u => (1 : ℂ) + I * u
    have hzpath : ContinuousAt z t := by
      fun_prop
    have hz1 : z t ≠ 1 := by
      intro heq
      have him := congrArg Complex.im heq
      simp [z] at him
      exact ht0 him
    have hzcont : ContinuousAt (fun u : ℝ => riemannZeta (z u)) t :=
      (differentiableAt_riemannZeta hz1).continuousAt.comp hzpath
    have hznonzero : riemannZeta (z t) ≠ 0 := by
      apply riemannZeta_ne_zero_of_one_le_re
      simp [z]
    have hnum : ContinuousAt (fun u : ℝ => (riemannZeta (z u))⁻¹) t :=
      hzcont.inv₀ hznonzero
    have hden : ContinuousAt (fun u : ℝ => (u : ℂ)) t :=
      Complex.continuous_ofReal.continuousAt
    change ContinuousWithinAt
      ((fun u : ℝ => (riemannZeta ((1 : ℂ) + I * u))⁻¹) /
        (fun u : ℝ => (u : ℂ))) K t
    simpa [z] using
      (hnum.div hden (Complex.ofReal_ne_zero.mpr ht0)).continuousWithinAt
  rcases hK.exists_bound_of_continuousOn hf with ⟨M, hM⟩
  let M' : ℝ := max 0 M
  have hM' : 0 ≤ M' := le_max_left _ _
  refine ⟨M', hM', ?_⟩
  intro t htr htT
  have ht0 : t ≠ 0 := by
    intro hzero
    subst t
    norm_num at htr
    linarith
  have htK : t ∈ K := by
    constructor
    · simpa [K, Metric.mem_closedBall, Real.dist_eq] using htT
    · simp only [Metric.mem_ball, Real.dist_eq, sub_zero, Real.norm_eq_abs]
      exact not_lt.mpr htr
  have hfM : ‖f t‖ ≤ M' := (hM t htK).trans (le_max_right _ _)
  have heq : (riemannZeta ((1 : ℂ) + I * t))⁻¹ = f t * (t : ℂ) := by
    dsimp [f]
    field_simp [Complex.ofReal_ne_zero.mpr ht0]
  calc
    ‖(riemannZeta ((1 : ℂ) + I * t))⁻¹‖ = ‖f t * (t : ℂ)‖ := by rw [heq]
    _ = ‖f t‖ * |t| := by simp [norm_mul]
    _ ≤ M' * |t| := mul_le_mul_of_nonneg_right hfM (abs_nonneg _)

end HardyTheorem
