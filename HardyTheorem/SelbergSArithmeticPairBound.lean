import HardyTheorem.SelbergS13GroupedAbsolute

open Complex Nat Finset
open scoped BigOperators

namespace HardyTheorem

/-! # Selberg's grouped arithmetic estimate (S19) -/

noncomputable def selbergGroupedPairScale
    (E : ℝ) (rho X : ℕ) (theta : ℝ) : ℝ :=
  E ^ 2 * ((X : ℝ) ^ theta) *
      (∏ p ∈ rho.primeFactors, (1 + (p : ℝ)⁻¹)) /
    Real.log (X : ℝ)

theorem selbergGroupedLocalMajorant_mul_zero_eq
    {E : ℝ} {rho X d e : ℕ} {theta : ℝ}
    (hd : 0 < d) (he : 0 < e)
    (hX : Real.exp 1 ≤ (X : ℝ)) :
    selbergGroupedLocalMajorant E rho X theta d *
        selbergGroupedLocalMajorant E rho X 0 e =
      selbergGroupedPairScale E rho X theta *
        (|selbergSqrtZetaCoeff d * selbergSqrtZetaCoeff e| /
          ((d * e : ℕ) : ℝ)) := by
  have hlog : 0 ≤ Real.log (X : ℝ) := by
    exact Real.log_nonneg
      ((Real.one_le_exp zero_le_one).trans hX)
  have hP : 0 ≤ ∏ p ∈ rho.primeFactors,
      (1 + (p : ℝ)⁻¹) := by positivity
  have hsL := Real.mul_self_sqrt hlog
  have hsP := Real.mul_self_sqrt hP
  have hlogpos : 0 < Real.log (X : ℝ) :=
    Real.log_pos ((Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hX)
  unfold selbergGroupedLocalMajorant selbergGroupedPairScale
  rw [Real.rpow_zero, abs_mul, Nat.cast_mul]
  field_simp [show (d : ℝ) ≠ 0 by exact_mod_cast hd.ne',
    show (e : ℝ) ≠ 0 by exact_mod_cast he.ne', hlogpos.ne']
  simp only [one_div, pow_two]
  rw [hsL, hsP]
  ring

private theorem selbergGroupedLocalMajorant_nonneg
    {E : ℝ} {rho X d : ℕ} {theta : ℝ}
    (hE : 0 ≤ E) (hX : Real.exp 1 ≤ (X : ℝ)) :
    0 ≤ selbergGroupedLocalMajorant E rho X theta d := by
  have hlogpos : 0 < Real.log (X : ℝ) :=
    Real.log_pos ((Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hX)
  unfold selbergGroupedLocalMajorant
  positivity

private theorem norm_selbergArithmeticPairSum_le_scale_mul_mass
    {E : ℝ} (hE : 0 ≤ E)
    (hlocal : ∀ (rho : ℕ) [NeZero rho] (theta : ℝ) (X : ℕ)
        (d : selbergSmoothOuterIndex rho X),
        0 ≤ theta → Real.exp 1 ≤ (X : ℝ) →
        ‖selbergSmoothOuterFactor X theta d.1 *
            selbergS12WeightedCoprimeSumReal rho theta
              ((X : ℝ) / (d.1 : ℝ))‖ ≤
          selbergGroupedLocalMajorant E rho X theta d.1)
    {rho X : ℕ} [NeZero rho] {theta : ℝ}
    (htheta : 0 ≤ theta) (hX : Real.exp 1 ≤ (X : ℝ)) :
    ‖selbergArithmeticPairSum rho X theta‖ ≤
      selbergGroupedPairScale E rho X theta *
        selbergS13BoundedSmoothPairMass rho X := by
  have hXtwo : 2 ≤ X := by
    have htwoexp : (2 : ℝ) < Real.exp 1 := by
      nlinarith [Real.exp_one_gt_d9]
    have htwoX : 2 < X := by
      exact_mod_cast htwoexp.trans_le hX
    omega
  rw [selbergArithmeticPairSum_eq_grouped theta hXtwo]
  unfold selbergArithmeticGroupedSum
  let G : ℝ → selbergSmoothOuterIndex rho X → ℂ := fun eta d =>
    selbergSmoothOuterFactor X eta d.1 *
      selbergS12WeightedCoprimeSumReal rho eta
        ((X : ℝ) / (d.1 : ℝ))
  calc
    ‖∑ d : selbergSmoothOuterIndex rho X,
        ∑ e : selbergSmoothOuterIndex rho X,
          if rho ∣ d.1 * e.1 then G theta d * G 0 e else 0‖ ≤
      ∑ d : selbergSmoothOuterIndex rho X,
        ‖∑ e : selbergSmoothOuterIndex rho X,
          if rho ∣ d.1 * e.1 then G theta d * G 0 e else 0‖ :=
      norm_sum_le Finset.univ _
    _ ≤ ∑ d : selbergSmoothOuterIndex rho X,
        ∑ e : selbergSmoothOuterIndex rho X,
          ‖if rho ∣ d.1 * e.1 then G theta d * G 0 e else 0‖ := by
      apply Finset.sum_le_sum
      intro d _hd
      exact norm_sum_le Finset.univ _
    _ ≤ ∑ d : selbergSmoothOuterIndex rho X,
        ∑ e : selbergSmoothOuterIndex rho X,
          if rho ∣ d.1 * e.1 then
            selbergGroupedLocalMajorant E rho X theta d.1 *
              selbergGroupedLocalMajorant E rho X 0 e.1
          else 0 := by
      apply Finset.sum_le_sum
      intro d _hd
      apply Finset.sum_le_sum
      intro e _he
      by_cases hdiv : rho ∣ d.1 * e.1
      · simp only [if_pos hdiv, norm_mul]
        exact mul_le_mul
          (hlocal rho theta X d htheta hX)
          (hlocal rho 0 X e (le_rfl) hX)
          (norm_nonneg _)
          (selbergGroupedLocalMajorant_nonneg hE hX)
      · simp [hdiv]
    _ = selbergGroupedPairScale E rho X theta *
        selbergS13BoundedSmoothPairMass rho X := by
      rw [selbergS13BoundedSmoothPairMass_eq_outer_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _hd
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hdiv : rho ∣ d.1 * e.1
      · rw [if_pos hdiv, if_pos hdiv]
        exact selbergGroupedLocalMajorant_mul_zero_eq
          (Nat.zero_lt_of_lt (Finset.mem_Icc.mp d.2.1).1)
          (Nat.zero_lt_of_lt (Finset.mem_Icc.mp e.2.1).1) hX
      · rw [if_neg hdiv, if_neg hdiv, mul_zero]

/-- S19: the exact grouped arithmetic sum has the uniform
`X^theta / (rho log X) * P(rho)^2` bound. -/
theorem exists_norm_selbergArithmeticPairSum_le :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (rho : ℕ) [NeZero rho] (theta : ℝ) (X : ℕ),
        0 ≤ theta → Real.exp 1 ≤ (X : ℝ) →
        ‖selbergArithmeticPairSum rho X theta‖ ≤
          C * ((X : ℝ) ^ theta) / Real.log (X : ℝ) *
            (rho : ℝ)⁻¹ *
            (∏ p ∈ rho.primeFactors, (1 + (p : ℝ)⁻¹)) ^ 2 := by
  rcases exists_norm_selbergGroupedLocalFactor_le with ⟨E, hE, hlocal⟩
  let C : ℝ := 2 * E ^ 2
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro rho _ theta X htheta hX
  have hscaleNonneg : 0 ≤ selbergGroupedPairScale E rho X theta := by
    have hlogpos : 0 < Real.log (X : ℝ) :=
      Real.log_pos ((Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hX)
    unfold selbergGroupedPairScale
    positivity
  calc
    ‖selbergArithmeticPairSum rho X theta‖ ≤
        selbergGroupedPairScale E rho X theta *
          selbergS13BoundedSmoothPairMass rho X :=
      norm_selbergArithmeticPairSum_le_scale_mul_mass hE hlocal htheta hX
    _ ≤ selbergGroupedPairScale E rho X theta *
        (2 * (rho : ℝ)⁻¹ *
          ∏ p ∈ rho.primeFactors, (1 + (p : ℝ)⁻¹)) :=
      mul_le_mul_of_nonneg_left
        (selbergS13BoundedSmoothPairMass_le_two_mul_plus rho X)
        hscaleNonneg
    _ = C * ((X : ℝ) ^ theta) / Real.log (X : ℝ) *
        (rho : ℝ)⁻¹ *
        (∏ p ∈ rho.primeFactors, (1 + (p : ℝ)⁻¹)) ^ 2 := by
      unfold selbergGroupedPairScale
      dsimp [C]
      ring

end HardyTheorem
