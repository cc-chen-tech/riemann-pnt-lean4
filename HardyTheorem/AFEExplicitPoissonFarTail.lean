import HardyTheorem.AFEExplicitPoissonUniformIntegral
import HardyTheorem.AFEWeightedPoissonVelocityBounds
import MathlibAux.DyadicHarmonic

/-! The distant positive and negative Poisson modes, with exact frequency cutoff. -/

open Set MeasureTheory
open scoped BigOperators

namespace HardyTheorem.AFE

noncomputable def explicitPoissonFarConstant (C₁ C₂ sigma : ℝ) : ℝ :=
  4 * C₂ + 4 * C₁ ^ 2 + 8 * sigma * C₁ + 6 * C₁ + 4 * sigma + 5

noncomputable def explicitPoissonMode (sigma x N t : ℝ) (k : ℤ) : ℂ :=
  ∫ u in (x - 1)..(N + 1), explicitComplexMellinAmplitude sigma x N u *
    Complex.exp (Complex.I * weightedPoissonPhase t k u)

private theorem uniformBound_le_far
    {C₁ C₂ sigma a t g : ℝ} (hs : 0 < sigma) (ha : 1 ≤ a)
    (ht : 0 ≤ t) (hg : 0 < g) (hC₁ : 0 ≤ C₁) (hfar : t ≤ a * g) :
    (1 / g ^ 2) * (2 * (2 * C₂ + 2 * C₁ ^ 2) * a ^ (-sigma) +
        (8 * sigma * C₁ + sigma) * a ^ (-sigma - 1)) +
      (6 * C₁ * t / g ^ 3) * (a ^ (-sigma - 1) / (sigma + 1)) +
      ((3 * sigma + 2) * t / g ^ 3) * (a ^ (-sigma - 2) / (sigma + 2)) +
      (3 * t ^ 2 / g ^ 4) * (a ^ (-sigma - 3) / (sigma + 3)) ≤
      explicitPoissonFarConstant C₁ C₂ sigma * a ^ (-sigma) / g ^ 2 := by
  have ha0 : 0 < a := by linarith
  let r := t / (a * g)
  have hr0 : 0 ≤ r := div_nonneg ht (by positivity)
  have hr1 : r ≤ 1 := (div_le_one (by positivity)).mpr hfar
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  have hb₁ : 1 / a ≤ 1 := (div_le_one ha0).mpr ha
  have hb₂ : r / (sigma + 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith)
  have hb₃ : r / (a * (sigma + 2)) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by nlinarith)
  have hb₄ : r ^ 2 / (a * (sigma + 3)) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by nlinarith)
  have hsum : 2 * (2 * C₂ + 2 * C₁ ^ 2) +
      (8 * sigma * C₁ + sigma) * (1 / a) +
      6 * C₁ * (r / (sigma + 1)) +
      (3 * sigma + 2) * (r / (a * (sigma + 2))) +
      3 * (r ^ 2 / (a * (sigma + 3))) ≤
      2 * (2 * C₂ + 2 * C₁ ^ 2) + (8 * sigma * C₁ + sigma) +
        6 * C₁ + (3 * sigma + 2) + 3 := by
    have h₁ := mul_le_mul_of_nonneg_left hb₁
      (show 0 ≤ 8 * sigma * C₁ + sigma by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hb₂ (show 0 ≤ 6 * C₁ by positivity)
    have h₃ := mul_le_mul_of_nonneg_left hb₃ (show 0 ≤ 3 * sigma + 2 by positivity)
    have h₄ := mul_le_mul_of_nonneg_left hb₄ (show (0 : ℝ) ≤ 3 by norm_num)
    linarith
  have hp₁ : a ^ (-sigma - 1) = a ^ (-sigma) / a := by
    simpa using Real.rpow_sub_natCast ha0.ne' (-sigma) 1
  have hp₂ : a ^ (-sigma - 2) = a ^ (-sigma) / a ^ 2 := by
    simpa using Real.rpow_sub_natCast ha0.ne' (-sigma) 2
  have hp₃ : a ^ (-sigma - 3) = a ^ (-sigma) / a ^ 3 := by
    simpa using Real.rpow_sub_natCast ha0.ne' (-sigma) 3
  calc
    _ = (a ^ (-sigma) / g ^ 2) *
        (2 * (2 * C₂ + 2 * C₁ ^ 2) + (8 * sigma * C₁ + sigma) * (1 / a) +
          6 * C₁ * (r / (sigma + 1)) +
          (3 * sigma + 2) * (r / (a * (sigma + 2))) +
          3 * (r ^ 2 / (a * (sigma + 3)))) := by
      rw [hp₁, hp₂, hp₃]
      dsimp only [r]
      field_simp [ha0.ne', hg.ne', show sigma + 1 ≠ 0 by linarith,
        show sigma + 2 ≠ 0 by linarith, show sigma + 3 ≠ 0 by linarith]
    _ ≤ (a ^ (-sigma) / g ^ 2) *
        (2 * (2 * C₂ + 2 * C₁ ^ 2) + (8 * sigma * C₁ + sigma) +
          6 * C₁ + (3 * sigma + 2) + 3) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by unfold explicitPoissonFarConstant; ring

private theorem norm_explicitPoissonMode_le_farGap
    {C₁ C₂ sigma x N t g : ℝ} {k : ℤ}
    (hs : 0 < sigma) (hx : 2 ≤ x) (hxN : x ≤ N) (ht : 0 ≤ t) (hg : 0 < g)
    (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hC₂ : ∀ z : ℝ, |deriv (deriv Real.smoothTransition) z| ≤ C₂)
    (hfar : t ≤ (x - 1) * g)
    (hgap : ∀ u ∈ Icc (x - 1) (N + 1), g ≤ |weightedPoissonVelocity t k u|) :
    ‖explicitPoissonMode sigma x N t k‖ ≤
      explicitPoissonFarConstant C₁ C₂ sigma * (x - 1) ^ (-sigma) / g ^ 2 :=
  (norm_explicitPoissonIntegral_le_uniform hs (by linarith) hxN ht hg
    hC₁0 hC₂0 hC₁ hC₂ hgap).trans
    (uniformBound_le_far hs (by linarith) ht hg hC₁0 hfar)

/-- The far condition keeps both signs away from every stationary point. -/
theorem norm_explicitPoissonMode_pair_le_far
    {C₁ C₂ sigma x N t : ℝ} {m : ℕ}
    (hs : 0 < sigma) (hx : 2 ≤ x) (hxN : x ≤ N) (ht : 0 ≤ t)
    (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hC₂ : ∀ z : ℝ, |deriv (deriv Real.smoothTransition) z| ≤ C₂)
    (hm : 1 ≤ m) (hfar : t / (x - 1) ≤ Real.pi * m) :
    ‖explicitPoissonMode sigma x N t (m : ℤ)‖ +
      ‖explicitPoissonMode sigma x N t (-(m : ℤ))‖ ≤
        2 * explicitPoissonFarConstant C₁ C₂ sigma * (x - 1) ^ (-sigma) /
          (Real.pi * m) ^ 2 := by
  have ha : 0 < x - 1 := by linarith
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hg : 0 < Real.pi * m := mul_pos Real.pi_pos hm0
  have hfar' : t ≤ (x - 1) * (Real.pi * m) := by
    simpa only [mul_comm] using (div_le_iff₀ ha).mp hfar
  have hpos : ∀ u ∈ Icc (x - 1) (N + 1),
      Real.pi * m ≤ |weightedPoissonVelocity t (m : ℤ) u| := by
    intro u hu
    have h := frequency_le_abs_weightedPoissonVelocity_of_nonneg_frequency
      ht (ha.trans_le hu.1) (Int.natCast_nonneg m)
    simp only [Int.cast_natCast] at h
    linarith
  have hneg : ∀ u ∈ Icc (x - 1) (N + 1),
      Real.pi * m ≤ |weightedPoissonVelocity t (-(m : ℤ)) u| := by
    intro u hu
    have h := right_endpoint_gap_le_abs_weightedPoissonVelocity_neg_nat
      ha ht hu (show t / (x - 1) ≤ 2 * Real.pi * m by linarith)
    linarith
  have hp := norm_explicitPoissonMode_le_farGap
    hs hx hxN ht hg hC₁0 hC₂0 hC₁ hC₂ hfar' hpos
  have hn := norm_explicitPoissonMode_le_farGap
    hs hx hxN ht hg hC₁0 hC₂0 hC₁ hC₂ hfar' hneg
  refine (add_le_add hp hn).trans_eq ?_
  ring

/-- Every finite far-frequency subset has the same cutoff-uniform bound. -/
theorem sum_norm_explicitPoissonMode_pair_le_far
    {C₁ C₂ sigma x N t : ℝ} (S : Finset ℕ)
    (hs : 0 < sigma) (hx : 2 ≤ x) (hxN : x ≤ N) (ht : 0 ≤ t)
    (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hC₂ : ∀ z : ℝ, |deriv (deriv Real.smoothTransition) z| ≤ C₂)
    (hfar : ∀ m ∈ S, 1 ≤ m ∧ t / (x - 1) ≤ Real.pi * m) :
    (∑ m ∈ S, (‖explicitPoissonMode sigma x N t (m : ℤ)‖ +
      ‖explicitPoissonMode sigma x N t (-(m : ℤ))‖)) ≤
        4 * explicitPoissonFarConstant C₁ C₂ sigma * (x - 1) ^ (-sigma) / Real.pi ^ 2 := by
  have ha : 0 < x - 1 := by linarith
  have hC : 0 ≤ explicitPoissonFarConstant C₁ C₂ sigma := by
    unfold explicitPoissonFarConstant
    positivity
  have hsubset : S ⊆ Finset.Icc 1 (S.sup id) := by
    intro m hm
    exact Finset.mem_Icc.mpr ⟨(hfar m hm).1, Finset.le_sup (f := id) hm⟩
  have hsum : (∑ m ∈ S, ((m : ℝ) ^ 2)⁻¹) ≤ 2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsubset (by intros; positivity)).trans
      (MathlibAux.sum_inv_sq_Icc_one_le_two (S.sup id))
  calc
    _ ≤ ∑ m ∈ S, 2 * explicitPoissonFarConstant C₁ C₂ sigma *
        (x - 1) ^ (-sigma) / (Real.pi * m) ^ 2 := by
      apply Finset.sum_le_sum
      intro m hm
      exact norm_explicitPoissonMode_pair_le_far hs hx hxN ht
        hC₁0 hC₂0 hC₁ hC₂ (hfar m hm).1 (hfar m hm).2
    _ = (2 * explicitPoissonFarConstant C₁ C₂ sigma *
        (x - 1) ^ (-sigma) / Real.pi ^ 2) * ∑ m ∈ S, ((m : ℝ) ^ 2)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      rw [mul_pow, div_mul_eq_div_div, div_eq_mul_inv]
    _ ≤ (2 * explicitPoissonFarConstant C₁ C₂ sigma *
        (x - 1) ^ (-sigma) / Real.pi ^ 2) * 2 :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

end HardyTheorem.AFE
