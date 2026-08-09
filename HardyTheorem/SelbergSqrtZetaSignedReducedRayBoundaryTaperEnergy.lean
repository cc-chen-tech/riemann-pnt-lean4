import HardyTheorem.SelbergSqrtZetaSignedReducedRayBoundaryEnergy

open scoped BigOperators

namespace HardyTheorem

/-!
# Logarithmic decay of the Selberg boundary taper energy

The linear logarithmic taper has much less weighted square mass than the
support-count bound sees.  Pointwise, `log y ≤ 2 * sqrt y` for `1 ≤ y`;
with `y = X / r`, this makes every weighted summand at most
`4 * X / log(X)^2`.
-/

private theorem harmonic_real_nonneg (X : ℕ) :
    0 ≤ (harmonic X : ℝ) := by
  rw [show (harmonic X : ℝ) =
      ∑ r ∈ Finset.Icc 1 X, (r : ℝ)⁻¹ by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast]]
  apply Finset.sum_nonneg
  intro r _hr
  positivity

private theorem sq_log_le_four_mul_of_one_le
    {y : ℝ} (hy : 1 ≤ y) :
    (Real.log y) ^ 2 ≤ 4 * y := by
  have hyPos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hsqrtPos : 0 < Real.sqrt y := Real.sqrt_pos.2 hyPos
  have hlogNonneg : 0 ≤ Real.log y := Real.log_nonneg hy
  have hlogSqrt :
      Real.log (Real.sqrt y) ≤ Real.sqrt y - 1 :=
    Real.log_le_sub_one_of_pos hsqrtPos
  have hlogLe : Real.log y ≤ 2 * Real.sqrt y := by
    rw [Real.log_sqrt hyPos.le] at hlogSqrt
    linarith
  have hsq :
      (Real.log y) ^ 2 ≤ (2 * Real.sqrt y) ^ 2 :=
    (sq_le_sq₀ hlogNonneg (by positivity)).2 hlogLe
  rw [mul_pow, Real.sq_sqrt hyPos.le] at hsq
  norm_num at hsq ⊢
  exact hsq

private theorem mul_sq_selbergMoebiusWeight_le_four_mul_div_log_sq
    {X r : ℕ} (hX : 2 ≤ X) (hr1 : 1 ≤ r) (hrX : r ≤ X) :
    (r : ℝ) * (selbergMoebiusWeight X r) ^ 2 ≤
      4 * (X : ℝ) / (Real.log X) ^ 2 := by
  have hXPos : (0 : ℝ) < X := by positivity
  have hrPos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hratioOne : (1 : ℝ) ≤ (X : ℝ) / (r : ℝ) := by
    apply (le_div_iff₀ hrPos).2
    simpa only [one_mul] using
      (show (r : ℝ) ≤ (X : ℝ) by exact_mod_cast hrX)
  have hlogXPos : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hweight :
      selbergMoebiusWeight X r =
        Real.log ((X : ℝ) / (r : ℝ)) / Real.log (X : ℝ) := by
    rw [selbergMoebiusWeight, Real.log_div hXPos.ne' hrPos.ne']
    field_simp
  have hlogSq :
      (Real.log ((X : ℝ) / (r : ℝ))) ^ 2 ≤
        4 * ((X : ℝ) / (r : ℝ)) :=
    sq_log_le_four_mul_of_one_le hratioOne
  have hnum :
      (r : ℝ) * (Real.log ((X : ℝ) / (r : ℝ))) ^ 2 ≤
        4 * (X : ℝ) := by
    calc
      (r : ℝ) * (Real.log ((X : ℝ) / (r : ℝ))) ^ 2 ≤
          (r : ℝ) * (4 * ((X : ℝ) / (r : ℝ))) :=
        mul_le_mul_of_nonneg_left hlogSq hrPos.le
      _ = 4 * (X : ℝ) := by field_simp
  rw [hweight, div_pow]
  calc
    (r : ℝ) *
        ((Real.log ((X : ℝ) / (r : ℝ))) ^ 2 /
          (Real.log (X : ℝ)) ^ 2) =
        ((r : ℝ) *
          (Real.log ((X : ℝ) / (r : ℝ))) ^ 2) /
            (Real.log (X : ℝ)) ^ 2 := by ring
    _ ≤ (4 * (X : ℝ)) / (Real.log (X : ℝ)) ^ 2 :=
      div_le_div_of_nonneg_right hnum (sq_nonneg _)

/-- The global weighted square mass of Selberg's linear logarithmic taper
has an explicit `1 / log(X)^2` saving.  The constant `4` comes from the
elementary pointwise bound `(log y)^2 ≤ 4y`. -/
theorem sum_Icc_mul_sq_selbergMoebiusWeight_le_four_mul_sq_div_log_sq
    (X : ℕ) (hX : 2 ≤ X) :
    (∑ r ∈ Finset.Icc 1 X,
        (r : ℝ) * (selbergMoebiusWeight X r) ^ 2) ≤
      4 * (X : ℝ) ^ 2 / (Real.log X) ^ 2 := by
  calc
    (∑ r ∈ Finset.Icc 1 X,
        (r : ℝ) * (selbergMoebiusWeight X r) ^ 2) ≤
        ∑ _r ∈ Finset.Icc 1 X,
          4 * (X : ℝ) / (Real.log X) ^ 2 := by
      apply Finset.sum_le_sum
      intro r hr
      exact
        mul_sq_selbergMoebiusWeight_le_four_mul_div_log_sq
          hX (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2
    _ = 4 * (X : ℝ) ^ 2 / (Real.log X) ^ 2 := by
      simp [Nat.card_Icc]
      ring

/-- Substituting the logarithmically decaying taper-energy estimate into
the existing exact harmonic-tail boundary estimate. -/
theorem
    selbergSqrtZetaSignedReducedRayBoundaryTerm_sq_le_four_mul_harmonicTail_sq_mul_harmonic_mul_sq_div_log_sq
    {N X a b : ℕ} (hX : 2 ≤ X) :
    (selbergSqrtZetaSignedReducedRayBoundaryTerm N X a b) ^ 2 ≤
      (∑ d ∈ Finset.Ioc
          (min N X / b)
          (min (X / a) (N * X / b)),
          (d : ℝ)⁻¹) ^ 2 *
        (harmonic X : ℝ) *
        (4 * (X : ℝ) ^ 2 / (Real.log X) ^ 2) := by
  calc
    (selbergSqrtZetaSignedReducedRayBoundaryTerm N X a b) ^ 2 ≤
        (∑ d ∈ Finset.Ioc
            (min N X / b)
            (min (X / a) (N * X / b)),
            (d : ℝ)⁻¹) ^ 2 *
          (harmonic X : ℝ) *
          ∑ r ∈ Finset.Icc 1 X,
            (r : ℝ) * (selbergMoebiusWeight X r) ^ 2 :=
      selbergSqrtZetaSignedReducedRayBoundaryTerm_sq_le_harmonicTail_sq_mul_uniformLinearTaperEnergy
        hX
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left
      · exact
          sum_Icc_mul_sq_selbergMoebiusWeight_le_four_mul_sq_div_log_sq
            X hX
      · exact
          mul_nonneg (sq_nonneg _)
            (harmonic_real_nonneg X)

end HardyTheorem
