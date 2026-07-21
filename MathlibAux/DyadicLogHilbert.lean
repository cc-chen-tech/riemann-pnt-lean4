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

/-- The two-sequence logarithmic Hilbert form.  This is the form that occurs
after the two endpoints of a shifted Hardy correlation acquire different
phase twists. -/
noncomputable def logarithmicHilbertBilinearForm
    (s : Finset ℕ) (left right : ℕ → ℂ) : ℂ :=
  ∑ m ∈ s, ∑ n ∈ s,
    if m = n then 0
    else (starRingEnd ℂ) (left n) * right m *
      ((1 / (Real.log (m : ℝ) - Real.log (n : ℝ)) : ℝ) : ℂ)

private noncomputable def symmetricWeightedHilbertBilinearForm
    (s : Finset ℕ) (left right : ℕ → ℂ) : ℂ :=
  ∑ m ∈ s, ∑ n ∈ s,
    if m = n then 0
    else (starRingEnd ℂ) (left n) * right m *
      (((m : ℂ) + (n : ℂ)) / ((m : ℂ) - (n : ℂ)))

private noncomputable def logarithmicKernelRemainderBilinearForm
    (s : Finset ℕ) (left right : ℕ → ℂ) : ℂ :=
  ∑ m ∈ s, ∑ n ∈ s,
    if m = n then 0
    else (starRingEnd ℂ) (left n) * right m *
      (((1 / (Real.log (m : ℝ) - Real.log (n : ℝ)) -
        ((m : ℝ) + n) / (2 * ((m : ℝ) - n))) : ℝ) : ℂ)

private theorem symmetricWeightedHilbertBilinearForm_eq_scaled
    {M : ℕ} (hM : 0 < M) (s : Finset ℕ) (left right : ℕ → ℂ) :
    symmetricWeightedHilbertBilinearForm s left right =
      discreteHilbertBilinearForm s
          (fun n => ((Real.sqrt M : ℝ) : ℂ) * left n)
          (fun m => (((m : ℝ) / Real.sqrt M : ℝ) : ℂ) * right m) +
        discreteHilbertBilinearForm s
          (fun n => (((n : ℝ) / Real.sqrt M : ℝ) : ℂ) * left n)
          (fun m => ((Real.sqrt M : ℝ) : ℂ) * right m) := by
  have hsqrt : Real.sqrt (M : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hM))
  have hsqrtC : ((Real.sqrt (M : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hsqrt
  unfold symmetricWeightedHilbertBilinearForm discreteHilbertBilinearForm
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

private theorem logarithmicHilbertBilinearForm_eq_principal_add_remainder
    (s : Finset ℕ) (left right : ℕ → ℂ) :
    logarithmicHilbertBilinearForm s left right =
      (1 / 2 : ℂ) * symmetricWeightedHilbertBilinearForm s left right +
        logarithmicKernelRemainderBilinearForm s left right := by
  unfold logarithmicHilbertBilinearForm
    symmetricWeightedHilbertBilinearForm
    logarithmicKernelRemainderBilinearForm
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

private theorem norm_symmetricWeightedHilbertBilinearForm_le
    {M : ℕ} (hM : 0 < M) (s : Finset ℕ) (left right : ℕ → ℂ)
    (hupper : ∀ n ∈ s, n ≤ 2 * M) :
    ‖symmetricWeightedHilbertBilinearForm s left right‖ ≤
      5 * Real.pi * M *
        ((∑ n ∈ s, Complex.normSq (left n)) +
          ∑ n ∈ s, Complex.normSq (right n)) := by
  let sqrtLeft : ℕ → ℂ := fun n =>
    ((Real.sqrt M : ℝ) : ℂ) * left n
  let sqrtRight : ℕ → ℂ := fun n =>
    ((Real.sqrt M : ℝ) : ℂ) * right n
  let divLeft : ℕ → ℂ := fun n =>
    (((n : ℝ) / Real.sqrt M : ℝ) : ℂ) * left n
  let divRight : ℕ → ℂ := fun n =>
    (((n : ℝ) / Real.sqrt M : ℝ) : ℂ) * right n
  have hdecomp : symmetricWeightedHilbertBilinearForm s left right =
      discreteHilbertBilinearForm s sqrtLeft divRight +
        discreteHilbertBilinearForm s divLeft sqrtRight := by
    simpa only [sqrtLeft, sqrtRight, divLeft, divRight] using
      symmetricWeightedHilbertBilinearForm_eq_scaled hM s left right
  have hsqrtLeft :
      (∑ n ∈ s, Complex.normSq (sqrtLeft n)) =
        M * ∑ n ∈ s, Complex.normSq (left n) := by
    simpa only [sqrtLeft] using sum_normSq_sqrt_mul s left
  have hsqrtRight :
      (∑ n ∈ s, Complex.normSq (sqrtRight n)) =
        M * ∑ n ∈ s, Complex.normSq (right n) := by
    simpa only [sqrtRight] using sum_normSq_sqrt_mul s right
  have hdivLeft :
      (∑ n ∈ s, Complex.normSq (divLeft n)) ≤
        4 * M * ∑ n ∈ s, Complex.normSq (left n) := by
    simpa only [divLeft] using
      sum_normSq_index_div_sqrt_le hM s left hupper
  have hdivRight :
      (∑ n ∈ s, Complex.normSq (divRight n)) ≤
        4 * M * ∑ n ∈ s, Complex.normSq (right n) := by
    simpa only [divRight] using
      sum_normSq_index_div_sqrt_le hM s right hupper
  have hfirst :=
    norm_discreteHilbertBilinearForm_le_pi_mul_add_sum_normSq
      s sqrtLeft divRight
  have hsecond :=
    norm_discreteHilbertBilinearForm_le_pi_mul_add_sum_normSq
      s divLeft sqrtRight
  rw [hdecomp]
  calc
    ‖discreteHilbertBilinearForm s sqrtLeft divRight +
        discreteHilbertBilinearForm s divLeft sqrtRight‖ ≤
        ‖discreteHilbertBilinearForm s sqrtLeft divRight‖ +
          ‖discreteHilbertBilinearForm s divLeft sqrtRight‖ :=
      norm_add_le _ _
    _ ≤ Real.pi *
          ((∑ n ∈ s, Complex.normSq (sqrtLeft n)) +
            ∑ n ∈ s, Complex.normSq (divRight n)) +
        Real.pi *
          ((∑ n ∈ s, Complex.normSq (divLeft n)) +
            ∑ n ∈ s, Complex.normSq (sqrtRight n)) :=
      add_le_add hfirst hsecond
    _ ≤ 5 * Real.pi * M *
          ((∑ n ∈ s, Complex.normSq (left n)) +
            ∑ n ∈ s, Complex.normSq (right n)) := by
      rw [hsqrtLeft, hsqrtRight]
      nlinarith [Real.pi_pos]

private theorem norm_logarithmicKernelRemainderBilinearForm_le
    {M : ℕ} (hM : 0 < M) (s : Finset ℕ) (left right : ℕ → ℂ)
    (hlower : ∀ n ∈ s, M ≤ n) (hupper : ∀ n ∈ s, n ≤ 2 * M) :
    ‖logarithmicKernelRemainderBilinearForm s left right‖ ≤
      3 * M * ((∑ n ∈ s, Complex.normSq (left n)) +
        ∑ n ∈ s, Complex.normSq (right n)) := by
  have hraw :
      ‖logarithmicKernelRemainderBilinearForm s left right‖ ≤
        (∑ n ∈ s, ‖left n‖) * (∑ n ∈ s, ‖right n‖) := by
    unfold logarithmicKernelRemainderBilinearForm
    calc
      ‖∑ m ∈ s, ∑ n ∈ s,
          if m = n then 0
          else (starRingEnd ℂ) (left n) * right m *
            (((1 / (Real.log (m : ℝ) - Real.log (n : ℝ)) -
              ((m : ℝ) + n) / (2 * ((m : ℝ) - n))) : ℝ) : ℂ)‖ ≤
          ∑ m ∈ s, ‖∑ n ∈ s,
            if m = n then 0
            else (starRingEnd ℂ) (left n) * right m *
              (((1 / (Real.log (m : ℝ) - Real.log (n : ℝ)) -
                ((m : ℝ) + n) / (2 * ((m : ℝ) - n))) : ℝ) : ℂ)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ m ∈ s, ∑ n ∈ s,
          ‖if m = n then 0
            else (starRingEnd ℂ) (left n) * right m *
              (((1 / (Real.log (m : ℝ) - Real.log (n : ℝ)) -
                ((m : ℝ) + n) / (2 * ((m : ℝ) - n))) : ℝ) : ℂ)‖ := by
        apply Finset.sum_le_sum
        intro m hm
        exact norm_sum_le _ _
      _ ≤ ∑ m ∈ s, ∑ n ∈ s, ‖left n‖ * ‖right m‖ := by
        apply Finset.sum_le_sum
        intro m hm
        apply Finset.sum_le_sum
        intro n hn
        by_cases hmn : m = n
        · simp only [hmn, ↓reduceIte, norm_zero]
          positivity
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
            ‖left n‖ * ‖right m‖ *
                |1 / (Real.log (m : ℝ) - Real.log (n : ℝ)) -
                  ((m : ℝ) + n) / (2 * ((m : ℝ) - n))| ≤
                ‖left n‖ * ‖right m‖ * 1 := by
              gcongr
            _ = ‖left n‖ * ‖right m‖ := by ring
      _ = (∑ n ∈ s, ‖left n‖) * (∑ n ∈ s, ‖right n‖) := by
        simp only [Finset.sum_mul, Finset.mul_sum]
  have hleft := sq_norm_sum_le_three_mul hM s left hupper
  have hright := sq_norm_sum_le_three_mul hM s right hupper
  have hleftNonneg : 0 ≤ ∑ n ∈ s, ‖left n‖ := by positivity
  have hrightNonneg : 0 ≤ ∑ n ∈ s, ‖right n‖ := by positivity
  calc
    ‖logarithmicKernelRemainderBilinearForm s left right‖ ≤
        (∑ n ∈ s, ‖left n‖) * (∑ n ∈ s, ‖right n‖) := hraw
    _ ≤ (∑ n ∈ s, ‖left n‖) ^ 2 +
          (∑ n ∈ s, ‖right n‖) ^ 2 := by nlinarith
    _ ≤ 3 * M * ((∑ n ∈ s, Complex.normSq (left n)) +
          ∑ n ∈ s, Complex.normSq (right n)) := by
      nlinarith

/-- Bilinear logarithmic Hilbert inequality on one dyadic block.  Different
left and right phase twists are allowed, which is essential for shifted
Hardy correlations. -/
theorem norm_logarithmicHilbertBilinearForm_le
    {M : ℕ} (hM : 0 < M) (s : Finset ℕ) (left right : ℕ → ℂ)
    (hlower : ∀ n ∈ s, M ≤ n) (hupper : ∀ n ∈ s, n ≤ 2 * M) :
    ‖logarithmicHilbertBilinearForm s left right‖ ≤
      (5 * Real.pi + 3) * M *
        ((∑ n ∈ s, Complex.normSq (left n)) +
          ∑ n ∈ s, Complex.normSq (right n)) := by
  have hprincipal := norm_symmetricWeightedHilbertBilinearForm_le
    hM s left right hupper
  have hremainder := norm_logarithmicKernelRemainderBilinearForm_le
    hM s left right hlower hupper
  rw [logarithmicHilbertBilinearForm_eq_principal_add_remainder]
  calc
    ‖(1 / 2 : ℂ) * symmetricWeightedHilbertBilinearForm s left right +
        logarithmicKernelRemainderBilinearForm s left right‖ ≤
        ‖(1 / 2 : ℂ) * symmetricWeightedHilbertBilinearForm s left right‖ +
          ‖logarithmicKernelRemainderBilinearForm s left right‖ :=
      norm_add_le _ _
    _ ≤ (1 / 2 : ℝ) *
          (5 * Real.pi * M *
            ((∑ n ∈ s, Complex.normSq (left n)) +
              ∑ n ∈ s, Complex.normSq (right n))) +
        3 * M * ((∑ n ∈ s, Complex.normSq (left n)) +
          ∑ n ∈ s, Complex.normSq (right n)) := by
      rw [norm_mul, norm_div, norm_one, norm_ofNat]
      norm_num
      exact add_le_add (mul_le_mul_of_nonneg_left hprincipal (by norm_num))
        hremainder
    _ ≤ (5 * Real.pi + 3) * M *
        ((∑ n ∈ s, Complex.normSq (left n)) +
          ∑ n ∈ s, Complex.normSq (right n)) := by
      have hleftSum : 0 ≤ ∑ n ∈ s, Complex.normSq (left n) := by
        apply Finset.sum_nonneg
        intro n hn
        exact Complex.normSq_nonneg (left n)
      have hrightSum : 0 ≤ ∑ n ∈ s, Complex.normSq (right n) := by
        apply Finset.sum_nonneg
        intro n hn
        exact Complex.normSq_nonneg (right n)
      have hsum : 0 ≤
          (∑ n ∈ s, Complex.normSq (left n)) +
            ∑ n ∈ s, Complex.normSq (right n) :=
        add_nonneg hleftSum hrightSum
      have hMreal : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
      have hpiMS : 0 ≤ Real.pi * (M : ℝ) *
          ((∑ n ∈ s, Complex.normSq (left n)) +
            ∑ n ∈ s, Complex.normSq (right n)) := by positivity
      nlinarith

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

private theorem sq_norm_sum_le_two_mul_upper
    {N : ℕ} (hN : 0 < N) (s : Finset ℕ) (coeff : ℕ → ℂ)
    (hupper : ∀ n ∈ s, n ≤ N) :
    (∑ n ∈ s, ‖coeff n‖) ^ 2 ≤
      2 * N * ∑ n ∈ s, Complex.normSq (coeff n) := by
  have hsubset : s ⊆ Finset.range (N + 1) := by
    intro n hn
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hupper n hn))
  have hcardNat : s.card ≤ N + 1 := by
    simpa using Finset.card_le_card hsubset
  have hcard : (s.card : ℝ) ≤ 2 * N := by
    exact_mod_cast (show s.card ≤ 2 * N by omega)
  have hcauchy :
      (∑ n ∈ s, ‖coeff n‖) ^ 2 ≤
        (s.card : ℝ) * ∑ n ∈ s, ‖coeff n‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  calc
    (∑ n ∈ s, ‖coeff n‖) ^ 2 ≤
        (s.card : ℝ) * ∑ n ∈ s, ‖coeff n‖ ^ 2 := hcauchy
    _ ≤ (2 * N) * ∑ n ∈ s, ‖coeff n‖ ^ 2 := by gcongr
    _ = 2 * N * ∑ n ∈ s, Complex.normSq (coeff n) := by
      simp only [Complex.sq_norm]

private theorem norm_logarithmicKernelRemainderBilinearForm_le_of_upper
    {N : ℕ} (hN : 0 < N) (s : Finset ℕ) (left right : ℕ → ℂ)
    (hpositive : ∀ n ∈ s, n ≠ 0) (hupper : ∀ n ∈ s, n ≤ N) :
    ‖logarithmicKernelRemainderBilinearForm s left right‖ ≤
      4 * N * ((∑ n ∈ s, Complex.normSq (left n)) +
        ∑ n ∈ s, Complex.normSq (right n)) := by
  have hraw :
      ‖logarithmicKernelRemainderBilinearForm s left right‖ ≤
        4 * ((∑ n ∈ s, ‖left n‖) * (∑ n ∈ s, ‖right n‖)) := by
    unfold logarithmicKernelRemainderBilinearForm
    calc
      ‖∑ m ∈ s, ∑ n ∈ s,
          if m = n then 0
          else (starRingEnd ℂ) (left n) * right m *
            (((1 / (Real.log (m : ℝ) - Real.log (n : ℝ)) -
              ((m : ℝ) + n) / (2 * ((m : ℝ) - n))) : ℝ) : ℂ)‖ ≤
          ∑ m ∈ s, ‖∑ n ∈ s,
            if m = n then 0
            else (starRingEnd ℂ) (left n) * right m *
              (((1 / (Real.log (m : ℝ) - Real.log (n : ℝ)) -
                ((m : ℝ) + n) / (2 * ((m : ℝ) - n))) : ℝ) : ℂ)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ m ∈ s, ∑ n ∈ s,
          ‖if m = n then 0
            else (starRingEnd ℂ) (left n) * right m *
              (((1 / (Real.log (m : ℝ) - Real.log (n : ℝ)) -
                ((m : ℝ) + n) / (2 * ((m : ℝ) - n))) : ℝ) : ℂ)‖ := by
        apply Finset.sum_le_sum
        intro m hm
        exact norm_sum_le _ _
      _ ≤ ∑ m ∈ s, ∑ n ∈ s, 4 * (‖left n‖ * ‖right m‖) := by
        apply Finset.sum_le_sum
        intro m hm
        apply Finset.sum_le_sum
        intro n hn
        by_cases hmn : m = n
        · simp only [hmn, ↓reduceIte, norm_zero]
          positivity
        · simp only [hmn, ↓reduceIte, norm_mul, Complex.norm_conj,
            norm_real, Real.norm_eq_abs]
          have hmpos : 0 < (m : ℝ) := by
            exact_mod_cast Nat.pos_of_ne_zero (hpositive m hm)
          have hnpos : 0 < (n : ℝ) := by
            exact_mod_cast Nat.pos_of_ne_zero (hpositive n hn)
          have hrem := abs_inv_log_sub_sub_symmetric_le_four
            hmpos hnpos (by exact_mod_cast hmn)
          calc
            ‖left n‖ * ‖right m‖ *
                |1 / (Real.log (m : ℝ) - Real.log (n : ℝ)) -
                  ((m : ℝ) + n) / (2 * ((m : ℝ) - n))| ≤
                ‖left n‖ * ‖right m‖ * 4 := by gcongr
            _ = 4 * (‖left n‖ * ‖right m‖) := by ring
      _ = 4 * ((∑ n ∈ s, ‖left n‖) * (∑ n ∈ s, ‖right n‖)) := by
        simp only [Finset.sum_mul, Finset.mul_sum]
  have hleft := sq_norm_sum_le_two_mul_upper hN s left hupper
  have hright := sq_norm_sum_le_two_mul_upper hN s right hupper
  have hleftNonneg : 0 ≤ ∑ n ∈ s, ‖left n‖ := by positivity
  have hrightNonneg : 0 ≤ ∑ n ∈ s, ‖right n‖ := by positivity
  calc
    ‖logarithmicKernelRemainderBilinearForm s left right‖ ≤
        4 * ((∑ n ∈ s, ‖left n‖) * (∑ n ∈ s, ‖right n‖)) := hraw
    _ ≤ 2 * ((∑ n ∈ s, ‖left n‖) ^ 2 +
          (∑ n ∈ s, ‖right n‖) ^ 2) := by
      nlinarith [sq_nonneg ((∑ n ∈ s, ‖left n‖) -
        ∑ n ∈ s, ‖right n‖)]
    _ ≤ 4 * N * ((∑ n ∈ s, Complex.normSq (left n)) +
          ∑ n ∈ s, Complex.normSq (right n)) := by
      nlinarith

/-- Global finite logarithmic Hilbert inequality.  Unlike the sharper dyadic
version, this only assumes positive indices bounded by `N`; hence it controls
all cross-block interactions of a truncated Dirichlet polynomial at once. -/
theorem norm_logarithmicHilbertBilinearForm_le_of_upper
    {N : ℕ} (hN : 0 < N) (s : Finset ℕ) (left right : ℕ → ℂ)
    (hpositive : ∀ n ∈ s, n ≠ 0) (hupper : ∀ n ∈ s, n ≤ N) :
    ‖logarithmicHilbertBilinearForm s left right‖ ≤
      (5 * Real.pi + 4) * N *
        ((∑ n ∈ s, Complex.normSq (left n)) +
          ∑ n ∈ s, Complex.normSq (right n)) := by
  have hupper2 : ∀ n ∈ s, n ≤ 2 * N := by
    intro n hn
    have hnN := hupper n hn
    omega
  have hprincipal := norm_symmetricWeightedHilbertBilinearForm_le
    hN s left right hupper2
  have hremainder := norm_logarithmicKernelRemainderBilinearForm_le_of_upper
    hN s left right hpositive hupper
  rw [logarithmicHilbertBilinearForm_eq_principal_add_remainder]
  calc
    ‖(1 / 2 : ℂ) * symmetricWeightedHilbertBilinearForm s left right +
        logarithmicKernelRemainderBilinearForm s left right‖ ≤
        ‖(1 / 2 : ℂ) * symmetricWeightedHilbertBilinearForm s left right‖ +
          ‖logarithmicKernelRemainderBilinearForm s left right‖ := norm_add_le _ _
    _ ≤ (1 / 2 : ℝ) *
          (5 * Real.pi * N *
            ((∑ n ∈ s, Complex.normSq (left n)) +
              ∑ n ∈ s, Complex.normSq (right n))) +
        4 * N * ((∑ n ∈ s, Complex.normSq (left n)) +
          ∑ n ∈ s, Complex.normSq (right n)) := by
      rw [norm_mul, norm_div, norm_one, norm_ofNat]
      norm_num
      exact add_le_add (mul_le_mul_of_nonneg_left hprincipal (by norm_num))
        hremainder
    _ ≤ (5 * Real.pi + 4) * N *
        ((∑ n ∈ s, Complex.normSq (left n)) +
          ∑ n ∈ s, Complex.normSq (right n)) := by
      have hsum : 0 ≤
          (∑ n ∈ s, Complex.normSq (left n)) +
            ∑ n ∈ s, Complex.normSq (right n) := by
        exact add_nonneg
          (Finset.sum_nonneg fun n hn => Complex.normSq_nonneg (left n))
          (Finset.sum_nonneg fun n hn => Complex.normSq_nonneg (right n))
      have hNreal : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      have hNS : 0 ≤ (N : ℝ) *
          ((∑ n ∈ s, Complex.normSq (left n)) +
            ∑ n ∈ s, Complex.normSq (right n)) :=
        mul_nonneg hNreal hsum
      nlinarith [Real.pi_pos]

end MathlibAux
