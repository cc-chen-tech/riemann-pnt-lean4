import MathlibAux.DyadicLogHilbert

open Complex MeasureTheory Set

namespace MathlibAux

private noncomputable def logTwistedCoeff
    (coeff : ℕ → ℂ) (t : ℝ) (n : ℕ) : ℂ :=
  coeff n * Complex.exp (I * ((Real.log n * t : ℝ) : ℂ))

private theorem conj_mul_logExponentialPolynomial_eq_double_sum
    (s : Finset ℕ) (coeff : ℕ → ℂ) (t : ℝ) :
    (starRingEnd ℂ)
          (exponentialPolynomial s coeff (fun n => Real.log n) t) *
        exponentialPolynomial s coeff (fun n => Real.log n) t =
      ∑ m ∈ s, ∑ n ∈ s,
        (starRingEnd ℂ) (coeff n) * coeff m *
          Complex.exp (I * ((Real.log m - Real.log n) * t)) := by
  simp only [exponentialPolynomial, map_sum, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  rw [map_mul, ← Complex.exp_conj]
  simp only [map_mul, conj_I, conj_ofReal]
  rw [show
      (starRingEnd ℂ) (coeff n) *
          Complex.exp (-I * ((Real.log n : ℂ) * t)) *
          (coeff m * Complex.exp (I * ((Real.log m : ℂ) * t))) =
        ((starRingEnd ℂ) (coeff n) * coeff m) *
          (Complex.exp (-I * ((Real.log n : ℂ) * t)) *
            Complex.exp (I * ((Real.log m : ℂ) * t))) by ring]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem integral_log_exponential_pair
    (coeff : ℕ → ℂ) (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0)
    {a b : ℝ} :
    (∫ t in a..b,
      (starRingEnd ℂ) (coeff n) * coeff m *
        Complex.exp (I * ((Real.log m - Real.log n) * t))) =
      (if m = n then
          ((b - a : ℝ) : ℂ) * Complex.normSq (coeff n)
        else 0) +
      (1 / I) *
        ((if m = n then 0 else
            (starRingEnd ℂ) (logTwistedCoeff coeff b n) *
              logTwistedCoeff coeff b m /
                ((Real.log m - Real.log n : ℝ) : ℂ)) -
          (if m = n then 0 else
            (starRingEnd ℂ) (logTwistedCoeff coeff a n) *
              logTwistedCoeff coeff a m /
                ((Real.log m - Real.log n : ℝ) : ℂ))) := by
  by_cases hmn : m = n
  · subst n
    simp only [sub_self, zero_mul, mul_zero, Complex.exp_zero, mul_one]
    rw [intervalIntegral.integral_const]
    change (((b - a : ℝ) : ℂ) *
        ((starRingEnd ℂ) (coeff m) * coeff m)) = _
    rw [show (starRingEnd ℂ) (coeff m) * coeff m =
        (Complex.normSq (coeff m) : ℂ) by
      exact (Complex.normSq_eq_conj_mul_self (z := coeff m)).symm]
    push_cast
    ring
  · have hlog : Real.log m - Real.log n ≠ 0 := by
      apply sub_ne_zero.mpr
      intro hlogs
      have hcasts : (m : ℝ) = (n : ℝ) :=
        Real.log_injOn_pos
          (show (m : ℝ) ∈ Ioi 0 by
            exact (show 0 < (m : ℝ) by
              exact_mod_cast Nat.pos_of_ne_zero hm))
          (show (n : ℝ) ∈ Ioi 0 by
            exact (show 0 < (n : ℝ) by
              exact_mod_cast Nat.pos_of_ne_zero hn)) hlogs
      exact hmn (Nat.cast_injective hcasts)
    have hI : I * ((Real.log m - Real.log n : ℝ) : ℂ) ≠ 0 :=
      mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hlog)
    simp only [if_neg hmn, zero_add]
    rw [show (fun t : ℝ =>
        (starRingEnd ℂ) (coeff n) * coeff m *
          Complex.exp (I * ((Real.log m - Real.log n) * t))) =
      fun t : ℝ => ((starRingEnd ℂ) (coeff n) * coeff m) *
        Complex.exp ((I * ((Real.log m - Real.log n : ℝ) : ℂ)) * t) by
      funext t
      congr 2
      push_cast
      ring]
    calc
      (∫ t in a..b,
          ((starRingEnd ℂ) (coeff n) * coeff m) *
            Complex.exp
              ((I * ((Real.log m - Real.log n : ℝ) : ℂ)) * t)) =
          ((starRingEnd ℂ) (coeff n) * coeff m) *
            ∫ t in a..b,
              Complex.exp
                ((I * ((Real.log m - Real.log n : ℝ) : ℂ)) * t) :=
        intervalIntegral.integral_const_mul _ _
      _ = _ := by
        rw [integral_exp_mul_complex hI]
        dsimp only [logTwistedCoeff]
        simp only [map_mul, ← Complex.exp_conj, map_mul, conj_I, conj_ofReal]
        field_simp [hlog, hI]
        rw [← Complex.exp_add, ← Complex.exp_add]
        congr 1
        push_cast
        ring

private theorem integral_conj_mul_logExponentialPolynomial_eq
    (s : Finset ℕ) (coeff : ℕ → ℂ)
    (hpositive : ∀ n ∈ s, n ≠ 0) {a b : ℝ} :
    (∫ t in a..b,
      (starRingEnd ℂ)
          (exponentialPolynomial s coeff (fun n => Real.log n) t) *
        exponentialPolynomial s coeff (fun n => Real.log n) t) =
      ((b - a : ℝ) : ℂ) *
          (∑ n ∈ s, Complex.normSq (coeff n)) +
        (1 / I) *
          (logarithmicHilbertForm s (logTwistedCoeff coeff b) -
            logarithmicHilbertForm s (logTwistedCoeff coeff a)) := by
  calc
    (∫ t in a..b,
        (starRingEnd ℂ)
            (exponentialPolynomial s coeff (fun n => Real.log n) t) *
          exponentialPolynomial s coeff (fun n => Real.log n) t) =
        ∫ t in a..b, ∑ m ∈ s, ∑ n ∈ s,
          (starRingEnd ℂ) (coeff n) * coeff m *
            Complex.exp (I * ((Real.log m - Real.log n) * t)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact conj_mul_logExponentialPolynomial_eq_double_sum s coeff t
    _ = ∑ m ∈ s, ∑ n ∈ s,
        ((if m = n then
            ((b - a : ℝ) : ℂ) * Complex.normSq (coeff n)
          else 0) +
        (1 / I) *
          ((if m = n then 0 else
              (starRingEnd ℂ) (logTwistedCoeff coeff b n) *
                logTwistedCoeff coeff b m /
                  ((Real.log m - Real.log n : ℝ) : ℂ)) -
            (if m = n then 0 else
              (starRingEnd ℂ) (logTwistedCoeff coeff a n) *
                logTwistedCoeff coeff a m /
                  ((Real.log m - Real.log n : ℝ) : ℂ)))) := by
      rw [intervalIntegral.integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro m hm
        rw [intervalIntegral.integral_finset_sum]
        · apply Finset.sum_congr rfl
          intro n hn
          exact integral_log_exponential_pair coeff m n
            (hpositive m hm) (hpositive n hn)
        · intro n hn
          apply Continuous.intervalIntegrable
          fun_prop
      · intro m hm
        apply Continuous.intervalIntegrable
        fun_prop
    _ = ((b - a : ℝ) : ℂ) *
          (∑ n ∈ s, Complex.normSq (coeff n)) +
        (1 / I) *
          (logarithmicHilbertForm s (logTwistedCoeff coeff b) -
            logarithmicHilbertForm s (logTwistedCoeff coeff a)) := by
      unfold logarithmicHilbertForm
      simp only [Finset.sum_add_distrib]
      congr 1
      · calc
          (∑ m ∈ s, ∑ n ∈ s,
              if m = n then
                ((b - a : ℝ) : ℂ) * Complex.normSq (coeff n)
              else 0) =
              ∑ m ∈ s,
                ((b - a : ℝ) : ℂ) * Complex.normSq (coeff m) := by
            apply Finset.sum_congr rfl
            intro m hm
            rw [Finset.sum_eq_single m]
            · simp
            · intro n hn hnm
              simp [hnm.symm]
            · intro hnot
              exact (hnot hm).elim
          _ = ((b - a : ℝ) : ℂ) *
              (∑ n ∈ s, Complex.normSq (coeff n)) := by
            push_cast
            rw [Finset.mul_sum]
      · rw [mul_sub, Finset.mul_sum, Finset.mul_sum,
          ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro m hm
        rw [Finset.mul_sum, Finset.mul_sum,
          ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro n hn
        by_cases hmn : m = n
        · simp [hmn]
        · simp only [hmn, ↓reduceIte]
          push_cast
          ring

/-- A logarithmic-frequency exponential polynomial supported on one dyadic
block has the expected diagonal second moment, with only an `O(M)` endpoint
error. -/
theorem integral_normSq_logExponentialPolynomial_le
    {M : ℕ} (hM : 0 < M) (s : Finset ℕ) (coeff : ℕ → ℂ)
    (hlower : ∀ n ∈ s, M ≤ n) (hupper : ∀ n ∈ s, n ≤ 2 * M)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b,
        Complex.normSq
          (exponentialPolynomial s coeff (fun n => Real.log n) t)) ≤
      ((b - a) + 2 * ((5 * Real.pi + 3) * M)) *
        ∑ n ∈ s, Complex.normSq (coeff n) := by
  let P : ℝ → ℂ := fun t =>
    exponentialPolynomial s coeff (fun n => Real.log n) t
  have hPcont : Continuous P := by
    dsimp only [P, exponentialPolynomial]
    fun_prop
  have hre :
      (∫ t in a..b, Complex.normSq (P t)) =
        (∫ t in a..b, (starRingEnd ℂ) (P t) * P t).re := by
    have hcomplexInt : IntervalIntegrable
        (fun t : ℝ => (starRingEnd ℂ) (P t) * P t) volume a b := by
      apply Continuous.intervalIntegrable
      fun_prop
    calc
      (∫ t in a..b, Complex.normSq (P t)) =
          ∫ t in a..b, ((starRingEnd ℂ) (P t) * P t).re := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact congrArg Complex.re
          (Complex.normSq_eq_conj_mul_self (z := P t))
      _ = (∫ t in a..b, (starRingEnd ℂ) (P t) * P t).re :=
        Complex.reCLM.intervalIntegral_comp_comm hcomplexInt
  have hpositive : ∀ n ∈ s, n ≠ 0 := by
    intro n hn hzero
    subst n
    have := hlower 0 hn
    omega
  have hexact := integral_conj_mul_logExponentialPolynomial_eq
    (s := s) (coeff := coeff) hpositive (a := a) (b := b)
  have htwist (t : ℝ) (n : ℕ) :
      Complex.normSq (logTwistedCoeff coeff t n) =
        Complex.normSq (coeff n) := by
    dsimp only [logTwistedCoeff]
    have hexp : Complex.normSq
        (Complex.exp (I * ((Real.log n * t : ℝ) : ℂ))) = 1 := by
      rw [Complex.normSq_eq_norm_sq,
        Complex.norm_exp_I_mul_ofReal]
      norm_num
    rw [Complex.normSq_mul, hexp, mul_one]
  have hbnd (t : ℝ) :
      ‖logarithmicHilbertForm s (logTwistedCoeff coeff t)‖ ≤
        (5 * Real.pi + 3) * M *
          ∑ n ∈ s, Complex.normSq (coeff n) := by
    have h := norm_logarithmicHilbertForm_le hM s
      (logTwistedCoeff coeff t) hlower hupper
    simpa only [htwist] using h
  rw [hre, hexact]
  have himajor :
      ((1 / I) *
        (logarithmicHilbertForm s (logTwistedCoeff coeff b) -
          logarithmicHilbertForm s (logTwistedCoeff coeff a))).re ≤
        2 * ((5 * Real.pi + 3) * M *
          ∑ n ∈ s, Complex.normSq (coeff n)) := by
    calc
      ((1 / I) *
          (logarithmicHilbertForm s (logTwistedCoeff coeff b) -
            logarithmicHilbertForm s (logTwistedCoeff coeff a))).re ≤
          ‖(1 / I) *
            (logarithmicHilbertForm s (logTwistedCoeff coeff b) -
              logarithmicHilbertForm s (logTwistedCoeff coeff a))‖ :=
        Complex.re_le_norm _
      _ = ‖logarithmicHilbertForm s (logTwistedCoeff coeff b) -
              logarithmicHilbertForm s (logTwistedCoeff coeff a)‖ := by
        rw [norm_mul, norm_div, norm_one, norm_I, div_one, one_mul]
      _ ≤ ‖logarithmicHilbertForm s (logTwistedCoeff coeff b)‖ +
            ‖logarithmicHilbertForm s (logTwistedCoeff coeff a)‖ :=
        norm_sub_le _ _
      _ ≤ 2 * ((5 * Real.pi + 3) * M *
            ∑ n ∈ s, Complex.normSq (coeff n)) := by
        nlinarith [hbnd a, hbnd b]
  rw [show
      (((b - a : ℝ) : ℂ) *
          ((∑ n ∈ s, Complex.normSq (coeff n) : ℝ) : ℂ) +
        (1 / I) *
          (logarithmicHilbertForm s (logTwistedCoeff coeff b) -
            logarithmicHilbertForm s (logTwistedCoeff coeff a))).re =
        (b - a) * (∑ n ∈ s, Complex.normSq (coeff n)) +
          ((1 / I) *
            (logarithmicHilbertForm s (logTwistedCoeff coeff b) -
              logarithmicHilbertForm s (logTwistedCoeff coeff a))).re by
    simp]
  have hlength : 0 ≤ b - a := sub_nonneg.mpr hab
  nlinarith

end MathlibAux
