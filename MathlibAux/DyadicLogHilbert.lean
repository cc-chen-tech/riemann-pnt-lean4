import MathlibAux.DiscreteHilbertInequality

open Complex

namespace MathlibAux

/-- The symmetric linearly weighted Hilbert form.  On a dyadic block this is
the principal part of the logarithmic-frequency kernel. -/
noncomputable def symmetricWeightedHilbertForm
    (s : Finset ℕ) (coeff : ℕ → ℂ) : ℂ :=
  ∑ m ∈ s, ∑ n ∈ s,
    if m = n then 0
    else (starRingEnd ℂ) (coeff n) * coeff m *
      (((m : ℂ) + (n : ℂ)) / ((m : ℂ) - (n : ℂ)))

private theorem symmetricWeightedHilbertForm_eq_scaled_bilinear
    {M : ℕ} (hM : 0 < M) (s : Finset ℕ) (coeff : ℕ → ℂ) :
    symmetricWeightedHilbertForm s coeff =
      discreteHilbertBilinearForm s
          (fun n => ((Real.sqrt M : ℝ) : ℂ) * coeff n)
          (fun m => (((m : ℝ) / Real.sqrt M : ℝ) : ℂ) * coeff m) +
        discreteHilbertBilinearForm s
          (fun n => (((n : ℝ) / Real.sqrt M : ℝ) : ℂ) * coeff n)
          (fun m => ((Real.sqrt M : ℝ) : ℂ) * coeff m) := by
  have hsqrt : Real.sqrt (M : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hM))
  have hsqrtC : ((Real.sqrt (M : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hsqrt
  unfold symmetricWeightedHilbertForm discreteHilbertBilinearForm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hmn : m = n
  · simp [hmn]
  · simp only [hmn, ↓reduceIte, map_mul, Complex.conj_ofReal]
    have hden : (m : ℂ) - (n : ℂ) ≠ 0 :=
      sub_ne_zero.mpr (Nat.cast_injective.ne hmn)
    field_simp [hsqrt, hsqrtC, hden]
    push_cast
    field_simp [hsqrtC]

private theorem sum_normSq_sqrt_mul
    {M : ℕ} (s : Finset ℕ) (coeff : ℕ → ℂ) :
    (∑ n ∈ s,
        Complex.normSq (((Real.sqrt M : ℝ) : ℂ) * coeff n)) =
      M * ∑ n ∈ s, Complex.normSq (coeff n) := by
  calc
    (∑ n ∈ s,
        Complex.normSq (((Real.sqrt M : ℝ) : ℂ) * coeff n)) =
        ∑ n ∈ s, M * Complex.normSq (coeff n) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Complex.normSq_mul, Complex.normSq_ofReal]
      rw [← pow_two, Real.sq_sqrt (by positivity)]
    _ = M * ∑ n ∈ s, Complex.normSq (coeff n) := by
      rw [Finset.mul_sum]

private theorem sum_normSq_index_div_sqrt_le
    {M : ℕ} (hM : 0 < M) (s : Finset ℕ) (coeff : ℕ → ℂ)
    (hs : ∀ n ∈ s, n ≤ 2 * M) :
    (∑ n ∈ s,
        Complex.normSq
          (((n : ℝ) / Real.sqrt M : ℝ) * (coeff n : ℂ))) ≤
      4 * M * ∑ n ∈ s, Complex.normSq (coeff n) := by
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast hM
  have hsqrt : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.2 hMreal
  have hsqrt_sq : (Real.sqrt (M : ℝ)) ^ 2 = M :=
    Real.sq_sqrt hMreal.le
  calc
    (∑ n ∈ s,
        Complex.normSq
          (((n : ℝ) / Real.sqrt M : ℝ) * (coeff n : ℂ))) ≤
        ∑ n ∈ s, (4 * M) * Complex.normSq (coeff n) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [Complex.normSq_mul, Complex.normSq_ofReal]
      have hnreal : (n : ℝ) ≤ 2 * M := by exact_mod_cast hs n hn
      have hnnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hweight :
          ((n : ℝ) / Real.sqrt M) * ((n : ℝ) / Real.sqrt M) ≤
            4 * M := by
        rw [div_mul_div_comm]
        rw [show Real.sqrt (M : ℝ) * Real.sqrt M = M by
          nlinarith [hsqrt_sq]]
        rw [div_le_iff₀ hMreal]
        nlinarith
      exact mul_le_mul_of_nonneg_right hweight
        (Complex.normSq_nonneg (coeff n))
    _ = 4 * M * ∑ n ∈ s, Complex.normSq (coeff n) := by
      rw [Finset.mul_sum]

/-- On indices `n ≤ 2M`, the symmetric weighted kernel costs only `O(M)` in
the coefficient square sum.  Reciprocal square-root scaling is what prevents
the bilinear Hilbert estimate from losing a second factor of `M`. -/
theorem norm_symmetricWeightedHilbertForm_le
    {M : ℕ} (hM : 0 < M) (s : Finset ℕ) (coeff : ℕ → ℂ)
    (hs : ∀ n ∈ s, n ≤ 2 * M) :
    ‖symmetricWeightedHilbertForm s coeff‖ ≤
      10 * Real.pi * M * ∑ n ∈ s, Complex.normSq (coeff n) := by
  let sqrtCoeff : ℕ → ℂ := fun n =>
    ((Real.sqrt M : ℝ) : ℂ) * coeff n
  let divCoeff : ℕ → ℂ := fun n =>
    (((n : ℝ) / Real.sqrt M : ℝ) : ℂ) * coeff n
  have hdecomp : symmetricWeightedHilbertForm s coeff =
      discreteHilbertBilinearForm s sqrtCoeff divCoeff +
        discreteHilbertBilinearForm s divCoeff sqrtCoeff := by
    simpa only [sqrtCoeff, divCoeff] using
      symmetricWeightedHilbertForm_eq_scaled_bilinear hM s coeff
  have hsqrtSum :
      (∑ n ∈ s, Complex.normSq (sqrtCoeff n)) =
        M * ∑ n ∈ s, Complex.normSq (coeff n) := by
    simpa only [sqrtCoeff] using sum_normSq_sqrt_mul s coeff
  have hdivSum :
      (∑ n ∈ s, Complex.normSq (divCoeff n)) ≤
        4 * M * ∑ n ∈ s, Complex.normSq (coeff n) := by
    simpa only [divCoeff] using
      sum_normSq_index_div_sqrt_le hM s coeff hs
  have hfirst :=
    norm_discreteHilbertBilinearForm_le_pi_mul_add_sum_normSq
      s sqrtCoeff divCoeff
  have hsecond :=
    norm_discreteHilbertBilinearForm_le_pi_mul_add_sum_normSq
      s divCoeff sqrtCoeff
  have hsum : 0 ≤ ∑ n ∈ s, Complex.normSq (coeff n) := by
    apply Finset.sum_nonneg
    intro n hn
    exact Complex.normSq_nonneg (coeff n)
  rw [hdecomp]
  calc
    ‖discreteHilbertBilinearForm s sqrtCoeff divCoeff +
        discreteHilbertBilinearForm s divCoeff sqrtCoeff‖ ≤
        ‖discreteHilbertBilinearForm s sqrtCoeff divCoeff‖ +
          ‖discreteHilbertBilinearForm s divCoeff sqrtCoeff‖ :=
      norm_add_le _ _
    _ ≤ Real.pi *
          ((∑ n ∈ s, Complex.normSq (sqrtCoeff n)) +
            ∑ n ∈ s, Complex.normSq (divCoeff n)) +
        Real.pi *
          ((∑ n ∈ s, Complex.normSq (divCoeff n)) +
            ∑ n ∈ s, Complex.normSq (sqrtCoeff n)) :=
      add_le_add hfirst hsecond
    _ ≤ 10 * Real.pi * M *
          ∑ n ∈ s, Complex.normSq (coeff n) := by
      rw [hsqrtSum]
      nlinarith [Real.pi_pos]

end MathlibAux
