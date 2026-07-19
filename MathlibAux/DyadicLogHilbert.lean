import MathlibAux.DiscreteHilbertInequality
import MathlibAux.LogKernelRemainder
import Mathlib.Algebra.Order.Chebyshev

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

/-- The Hilbert form associated to logarithmic frequencies `log n`. -/
noncomputable def logarithmicHilbertForm
    (s : Finset ℕ) (coeff : ℕ → ℂ) : ℂ :=
  ∑ m ∈ s, ∑ n ∈ s,
    if m = n then 0
    else (starRingEnd ℂ) (coeff n) * coeff m *
      ((1 / (Real.log (m : ℝ) - Real.log (n : ℝ)) : ℝ) : ℂ)

private noncomputable def logarithmicKernelRemainderForm
    (s : Finset ℕ) (coeff : ℕ → ℂ) : ℂ :=
  ∑ m ∈ s, ∑ n ∈ s,
    if m = n then 0
    else (starRingEnd ℂ) (coeff n) * coeff m *
      (((1 / (Real.log (m : ℝ) - Real.log (n : ℝ)) -
        ((m : ℝ) + n) / (2 * ((m : ℝ) - n))) : ℝ) : ℂ)

private theorem logarithmicHilbertForm_eq_principal_add_remainder
    (s : Finset ℕ) (coeff : ℕ → ℂ) :
    logarithmicHilbertForm s coeff =
      (1 / 2 : ℂ) * symmetricWeightedHilbertForm s coeff +
        logarithmicKernelRemainderForm s coeff := by
  unfold logarithmicHilbertForm symmetricWeightedHilbertForm
    logarithmicKernelRemainderForm
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hmn : m = n
  · simp [hmn]
  · simp only [hmn, ↓reduceIte]
    push_cast
    have hden : (m : ℂ) - (n : ℂ) ≠ 0 :=
      sub_ne_zero.mpr (Nat.cast_injective.ne hmn)
    field_simp [hden]
    ring

private theorem norm_logarithmicKernelRemainderForm_le_sq_norm_sum
    {M : ℕ} (hM : 0 < M) (s : Finset ℕ) (coeff : ℕ → ℂ)
    (hlower : ∀ n ∈ s, M ≤ n) (hupper : ∀ n ∈ s, n ≤ 2 * M) :
    ‖logarithmicKernelRemainderForm s coeff‖ ≤
      (∑ n ∈ s, ‖coeff n‖) ^ 2 := by
  unfold logarithmicKernelRemainderForm
  calc
    ‖∑ m ∈ s, ∑ n ∈ s,
        if m = n then 0
        else (starRingEnd ℂ) (coeff n) * coeff m *
          (((1 / (Real.log (m : ℝ) - Real.log (n : ℝ)) -
            ((m : ℝ) + n) / (2 * ((m : ℝ) - n))) : ℝ) : ℂ)‖ ≤
        ∑ m ∈ s, ‖∑ n ∈ s,
          if m = n then 0
          else (starRingEnd ℂ) (coeff n) * coeff m *
            (((1 / (Real.log (m : ℝ) - Real.log (n : ℝ)) -
              ((m : ℝ) + n) / (2 * ((m : ℝ) - n))) : ℝ) : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ m ∈ s, ∑ n ∈ s,
        ‖if m = n then 0
          else (starRingEnd ℂ) (coeff n) * coeff m *
            (((1 / (Real.log (m : ℝ) - Real.log (n : ℝ)) -
              ((m : ℝ) + n) / (2 * ((m : ℝ) - n))) : ℝ) : ℂ)‖ := by
      apply Finset.sum_le_sum
      intro m hm
      exact norm_sum_le _ _
    _ ≤ ∑ m ∈ s, ∑ n ∈ s, ‖coeff n‖ * ‖coeff m‖ := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro n hn
      by_cases hmn : m = n
      · simp only [hmn, ↓reduceIte, norm_zero]
        exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
      · simp only [hmn, ↓reduceIte, norm_mul, Complex.norm_conj,
          norm_real, Real.norm_eq_abs]
        have hmpos : 0 < (m : ℝ) := by
          exact_mod_cast lt_of_lt_of_le hM (hlower m hm)
        have hnpos : 0 < (n : ℝ) := by
          exact_mod_cast lt_of_lt_of_le hM (hlower n hn)
        have hmn2 : (m : ℝ) ≤ 2 * n := by
          exact_mod_cast (hupper m hm).trans
            (Nat.mul_le_mul_left 2 (hlower n hn))
        have hnm2 : (n : ℝ) ≤ 2 * m := by
          exact_mod_cast (hupper n hn).trans
            (Nat.mul_le_mul_left 2 (hlower m hm))
        have hrem := abs_inv_log_sub_sub_symmetric_le_one
          hmpos hnpos (by exact_mod_cast hmn) hmn2 hnm2
        calc
          ‖coeff n‖ * ‖coeff m‖ *
              |1 / (Real.log (m : ℝ) - Real.log (n : ℝ)) -
                ((m : ℝ) + n) / (2 * ((m : ℝ) - n))| ≤
              ‖coeff n‖ * ‖coeff m‖ * 1 := by
            gcongr
          _ = ‖coeff n‖ * ‖coeff m‖ := by ring
    _ = (∑ n ∈ s, ‖coeff n‖) ^ 2 := by
      rw [pow_two]
      simp only [Finset.sum_mul, Finset.mul_sum]

private theorem sq_norm_sum_le_three_mul
    {M : ℕ} (hM : 0 < M) (s : Finset ℕ) (coeff : ℕ → ℂ)
    (hupper : ∀ n ∈ s, n ≤ 2 * M) :
    (∑ n ∈ s, ‖coeff n‖) ^ 2 ≤
      3 * M * ∑ n ∈ s, Complex.normSq (coeff n) := by
  have hsubset : s ⊆ Finset.range (2 * M + 1) := by
    intro n hn
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hupper n hn))
  have hcardNat : s.card ≤ 2 * M + 1 := by
    simpa using Finset.card_le_card hsubset
  have hcard : (s.card : ℝ) ≤ 3 * M := by
    exact_mod_cast (show s.card ≤ 3 * M by omega)
  have hcauchy :
      (∑ n ∈ s, ‖coeff n‖) ^ 2 ≤
        (s.card : ℝ) * ∑ n ∈ s, ‖coeff n‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  calc
    (∑ n ∈ s, ‖coeff n‖) ^ 2 ≤
        (s.card : ℝ) * ∑ n ∈ s, ‖coeff n‖ ^ 2 := hcauchy
    _ ≤ (3 * M) * ∑ n ∈ s, ‖coeff n‖ ^ 2 := by
      gcongr
    _ = 3 * M * ∑ n ∈ s, Complex.normSq (coeff n) := by
      simp only [Complex.sq_norm]

/-- On one dyadic block, the logarithmic-frequency Hilbert form has an
`O(M)` bound.  The principal singularity is controlled by Hilbert's inequality;
the bounded logarithmic remainder is controlled by finite Cauchy--Schwarz. -/
theorem norm_logarithmicHilbertForm_le
    {M : ℕ} (hM : 0 < M) (s : Finset ℕ) (coeff : ℕ → ℂ)
    (hlower : ∀ n ∈ s, M ≤ n) (hupper : ∀ n ∈ s, n ≤ 2 * M) :
    ‖logarithmicHilbertForm s coeff‖ ≤
      (5 * Real.pi + 3) * M *
        ∑ n ∈ s, Complex.normSq (coeff n) := by
  have hprincipal := norm_symmetricWeightedHilbertForm_le hM s coeff hupper
  have hremainder :=
    norm_logarithmicKernelRemainderForm_le_sq_norm_sum
      hM s coeff hlower hupper
  have hsquare := sq_norm_sum_le_three_mul hM s coeff hupper
  rw [logarithmicHilbertForm_eq_principal_add_remainder]
  calc
    ‖(1 / 2 : ℂ) * symmetricWeightedHilbertForm s coeff +
        logarithmicKernelRemainderForm s coeff‖ ≤
        ‖(1 / 2 : ℂ) * symmetricWeightedHilbertForm s coeff‖ +
          ‖logarithmicKernelRemainderForm s coeff‖ := norm_add_le _ _
    _ ≤ (1 / 2 : ℝ) *
          (10 * Real.pi * M *
            ∑ n ∈ s, Complex.normSq (coeff n)) +
        3 * M * ∑ n ∈ s, Complex.normSq (coeff n) := by
      rw [norm_mul, norm_div, norm_one, norm_ofNat]
      norm_num
      gcongr
      exact hremainder.trans hsquare
    _ = (5 * Real.pi + 3) * M *
        ∑ n ∈ s, Complex.normSq (coeff n) := by ring

end MathlibAux
