import HardyTheorem.SelbergS12ZetaInverse

open Complex Set

namespace HardyTheorem

/-!
# Selberg S12: the reciprocal-zeta bound on a bounded strip

The analytic pole unit removes the apparent singularity at `s = 1`.  Its inverse is continuous
and nonzero on every bounded rectangle `1 ≤ re s ≤ 2`; compactness then supplies a uniform
constant.  Multiplying back by `s - 1` gives the required two-dimensional linear vanishing.
-/

noncomputable def selbergS12StripPoint (epsilon t : ℝ) : ℂ :=
  ((1 + epsilon : ℝ) : ℂ) + I * t

@[simp] theorem selbergS12StripPoint_re (epsilon t : ℝ) :
    (selbergS12StripPoint epsilon t).re = 1 + epsilon := by
  simp [selbergS12StripPoint]

@[simp] theorem selbergS12StripPoint_im (epsilon t : ℝ) :
    (selbergS12StripPoint epsilon t).im = t := by
  simp [selbergS12StripPoint]

theorem riemannZetaPoleUnitAtOne_ne_zero_of_one_le_re
    {s : ℂ} (hs : 1 ≤ s.re) :
    ZeroFreeRegion.riemannZetaPoleUnitAtOne s ≠ 0 := by
  by_cases hs1 : s = 1
  · subst s
    rw [ZeroFreeRegion.riemannZetaPoleUnitAtOne_one]
    exact one_ne_zero
  · have hs0 : s ≠ 0 := by
      intro h
      subst s
      norm_num at hs
    rw [ZeroFreeRegion.riemannZetaPoleUnitAtOne_eq_sub_one_mul_riemannZeta hs0 hs1]
    exact mul_ne_zero (sub_ne_zero.mpr hs1)
      (riemannZeta_ne_zero_of_one_le_re hs)

theorem inv_riemannZeta_eq_sub_one_mul_inv_poleUnit
    {s : ℂ} (hsre : 1 ≤ s.re) (hs1 : s ≠ 1) :
    (riemannZeta s)⁻¹ =
      (s - 1) * (ZeroFreeRegion.riemannZetaPoleUnitAtOne s)⁻¹ := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hsre
  have hzeta : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hsre
  have hunit :=
    ZeroFreeRegion.riemannZetaPoleUnitAtOne_eq_sub_one_mul_riemannZeta hs0 hs1
  rw [hunit]
  field_simp

theorem exists_norm_inv_riemannZeta_strip_le_mul_offset_on_bounded_height
    (T : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ epsilon t : ℝ,
        0 ≤ epsilon → epsilon ≤ 1 → |t| ≤ T → 0 < epsilon + |t| →
        ‖(riemannZeta (selbergS12StripPoint epsilon t))⁻¹‖ ≤
          A * (epsilon + |t|) := by
  let K : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (-T) T
  let point : ℝ × ℝ → ℂ := fun p => selbergS12StripPoint p.1 p.2
  let f : ℝ × ℝ → ℂ := fun p =>
    (ZeroFreeRegion.riemannZetaPoleUnitAtOne (point p))⁻¹
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hf : ContinuousOn f K := by
    intro p hp
    have hpre : 1 ≤ (point p).re := by
      dsimp [point]
      simp only [selbergS12StripPoint_re]
      linarith [hp.1.1]
    have hpos : 0 < (point p).re := zero_lt_one.trans_le hpre
    have hanalytic : AnalyticAt ℂ ZeroFreeRegion.riemannZetaPoleUnitAtOne (point p) :=
      ZeroFreeRegion.analyticOnNhd_riemannZetaPoleUnitAtOne_re_gt
        (θ := 0) le_rfl (point p) hpos
    have hpoint : ContinuousAt point p := by
      dsimp [point, selbergS12StripPoint]
      fun_prop
    exact (hanalytic.inv
      (riemannZetaPoleUnitAtOne_ne_zero_of_one_le_re hpre)).continuousAt.comp
        hpoint |>.continuousWithinAt
  rcases hK.exists_bound_of_continuousOn hf with ⟨M, hM⟩
  let A : ℝ := max 0 M
  have hA : 0 ≤ A := le_max_left _ _
  refine ⟨A, hA, ?_⟩
  intro epsilon t heps0 heps1 htT hoffset
  have htIcc : t ∈ Icc (-T) T := (abs_le.mp htT)
  have hpK : (epsilon, t) ∈ K := ⟨⟨heps0, heps1⟩, htIcc⟩
  have hfbound : ‖f (epsilon, t)‖ ≤ A :=
    (hM (epsilon, t) hpK).trans (le_max_right _ _)
  let s : ℂ := selbergS12StripPoint epsilon t
  have hsre : 1 ≤ s.re := by
    dsimp [s]
    simp only [selbergS12StripPoint_re]
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    dsimp [s] at hre him
    simp only [selbergS12StripPoint_re, one_re] at hre
    simp only [selbergS12StripPoint_im, one_im] at him
    have : epsilon = 0 := by linarith
    subst epsilon
    simp at hoffset
    exact hoffset him
  have heq := inv_riemannZeta_eq_sub_one_mul_inv_poleUnit hsre hs1
  have hdist : ‖s - 1‖ ≤ epsilon + |t| := by
    calc
      ‖s - 1‖ ≤ |(s - 1).re| + |(s - 1).im| :=
        Complex.norm_le_abs_re_add_abs_im (s - 1)
      _ = epsilon + |t| := by
        dsimp [s]
        simp [selbergS12StripPoint, abs_of_nonneg heps0]
  have hfinv :
      ‖(ZeroFreeRegion.riemannZetaPoleUnitAtOne s)⁻¹‖ ≤ A := by
    simpa [f, point, s] using hfbound
  calc
    ‖(riemannZeta s)⁻¹‖ =
        ‖(s - 1) * (ZeroFreeRegion.riemannZetaPoleUnitAtOne s)⁻¹‖ := by
      rw [heq]
    _ = ‖s - 1‖ * ‖(ZeroFreeRegion.riemannZetaPoleUnitAtOne s)⁻¹‖ := norm_mul _ _
    _ ≤ (epsilon + |t|) * A :=
      mul_le_mul hdist hfinv (norm_nonneg _) (by positivity)
    _ = A * (epsilon + |t|) := by ring

end HardyTheorem
