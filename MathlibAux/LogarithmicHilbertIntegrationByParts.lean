import MathlibAux.DyadicLogHilbert
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

open Complex MeasureTheory Set

namespace MathlibAux

private noncomputable def logOffDiagonalTerm
    (left right : ℕ → ℂ) (m n : ℕ) (t : ℝ) : ℂ :=
  if m = n then 0
  else (starRingEnd ℂ) (left n) * right m *
    Complex.exp (I * ((Real.log m - Real.log n) * t))

private noncomputable def logarithmicHilbertPrimitiveTerm
    (left right : ℕ → ℂ) (m n : ℕ) (t : ℝ) : ℂ :=
  if m = n then 0
  else ((starRingEnd ℂ) (left n) * right m /
      ((Real.log m - Real.log n : ℝ) : ℂ)) *
    Complex.exp (I * ((Real.log m - Real.log n) * t))

/-- The off-diagonal part of the product of two logarithmic-frequency
exponential polynomials. -/
noncomputable def logOffDiagonalForm
    (s : Finset ℕ) (left right : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ m ∈ s, ∑ n ∈ s, logOffDiagonalTerm left right m n t

private noncomputable def logarithmicHilbertPrimitive
    (s : Finset ℕ) (left right : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ m ∈ s, ∑ n ∈ s,
    logarithmicHilbertPrimitiveTerm left right m n t

private noncomputable def logarithmicTwist
    (coeff : ℕ → ℂ) (t : ℝ) (n : ℕ) : ℂ :=
  coeff n * Complex.exp (I * ((Real.log n * t : ℝ) : ℂ))

private theorem hasDerivAt_logarithmicHilbertPrimitiveTerm
    (left right : ℕ → ℂ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (t : ℝ) :
    HasDerivAt (logarithmicHilbertPrimitiveTerm left right m n)
      (I * logOffDiagonalTerm left right m n t) t := by
  by_cases hmn : m = n
  · subst n
    have hzero : logarithmicHilbertPrimitiveTerm left right m m =
        fun _ : ℝ => 0 := by
      funext x
      simp [logarithmicHilbertPrimitiveTerm]
    rw [hzero]
    simpa [logOffDiagonalTerm] using (hasDerivAt_const t (0 : ℂ))
  · have hmpos : 0 < (m : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hm
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    have hlog : Real.log m - Real.log n ≠ 0 := by
      apply sub_ne_zero.mpr
      intro heq
      have hcast : (m : ℝ) = (n : ℝ) :=
        Real.log_injOn_pos hmpos hnpos heq
      exact hmn (Nat.cast_injective hcast)
    have hcast : HasDerivAt
        (fun x : ℝ => (((Real.log m - Real.log n) * x : ℝ) : ℂ))
        ((Real.log m - Real.log n : ℝ) : ℂ) t := by
      convert Complex.ofRealCLM.hasDerivAt.const_mul
        ((Real.log m - Real.log n : ℝ) : ℂ) using 1
      · funext x
        simp only [Complex.ofRealCLM_apply, Complex.ofReal_sub,
          Complex.ofReal_mul]
      · simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one]
    have harg : HasDerivAt
        (fun x : ℝ => I *
          (((Real.log m - Real.log n) * x : ℝ) : ℂ))
        (I * ((Real.log m - Real.log n : ℝ) : ℂ)) t :=
      hcast.const_mul I
    have hexp := harg.cexp
    have hterm := hexp.const_mul
      ((starRingEnd ℂ) (left n) * right m /
        ((Real.log m - Real.log n : ℝ) : ℂ))
    rw [show logarithmicHilbertPrimitiveTerm left right m n =
        fun y : ℝ =>
          ((starRingEnd ℂ) (left n) * right m /
            ((Real.log m - Real.log n : ℝ) : ℂ)) *
              Complex.exp (I * ((Real.log m - Real.log n) * y)) by
      funext y
      simp only [logarithmicHilbertPrimitiveTerm, if_neg hmn]]
    rw [show logOffDiagonalTerm left right m n t =
        (starRingEnd ℂ) (left n) * right m *
          Complex.exp (I * ((Real.log m - Real.log n) * t)) by
      simp only [logOffDiagonalTerm, if_neg hmn]]
    convert hterm using 1
    · funext y
      rw [show I * (((Real.log m - Real.log n) * y : ℝ) : ℂ) =
          I * ((Real.log m : ℝ) : ℂ) * (y : ℂ) -
            I * ((Real.log n : ℝ) : ℂ) * (y : ℂ) by
        push_cast
        ring]
      ring
    · rw [show I * (((Real.log m - Real.log n) * t : ℝ) : ℂ) =
          I * (((Real.log m : ℝ) : ℂ) -
            ((Real.log n : ℝ) : ℂ)) * (t : ℂ) by
        push_cast
        ring]
      have hlogC : ((Real.log m - Real.log n : ℝ) : ℂ) ≠ 0 :=
        ofReal_ne_zero.mpr hlog
      field_simp [hlogC]

private theorem hasDerivAt_logarithmicHilbertPrimitive
    (s : Finset ℕ) (left right : ℕ → ℂ)
    (hpositive : ∀ n ∈ s, n ≠ 0) (t : ℝ) :
    HasDerivAt (logarithmicHilbertPrimitive s left right)
      (I * logOffDiagonalForm s left right t) t := by
  unfold logarithmicHilbertPrimitive logOffDiagonalForm
  convert HasDerivAt.fun_sum (u := s) (x := t)
    (fun m hm => HasDerivAt.fun_sum (u := s) (x := t)
      (fun n hn => hasDerivAt_logarithmicHilbertPrimitiveTerm
        left right (hpositive m hm) (hpositive n hn) t)) using 1
  simp only [Finset.mul_sum]

private theorem logarithmicHilbertPrimitive_eq_bilinearForm
    (s : Finset ℕ) (left right : ℕ → ℂ) (t : ℝ) :
    logarithmicHilbertPrimitive s left right t =
      logarithmicHilbertBilinearForm s
        (logarithmicTwist left t) (logarithmicTwist right t) := by
  unfold logarithmicHilbertPrimitive logarithmicHilbertBilinearForm
    logarithmicHilbertPrimitiveTerm logarithmicTwist
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hmn : m = n
  · simp [hmn]
  · simp only [hmn, ↓reduceIte, map_mul, ← Complex.exp_conj,
      conj_I, conj_ofReal]
    have hexp :
        Complex.exp (I * ((Real.log m - Real.log n) * t)) =
          Complex.exp (-I * ((Real.log n * t : ℝ) : ℂ)) *
            Complex.exp (I * ((Real.log m * t : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    push_cast
    field_simp

private theorem normSq_logarithmicTwist
    (coeff : ℕ → ℂ) (t : ℝ) (n : ℕ) :
    Complex.normSq (logarithmicTwist coeff t n) =
      Complex.normSq (coeff n) := by
  unfold logarithmicTwist
  rw [Complex.normSq_mul]
  have hexp : Complex.normSq
      (Complex.exp (I * ((Real.log n * t : ℝ) : ℂ))) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_I_mul_ofReal]
    norm_num
  rw [hexp, mul_one]

private theorem norm_logarithmicHilbertPrimitive_le
    {M : ℕ} (hM : 0 < M) (s : Finset ℕ) (left right : ℕ → ℂ)
    (hlower : ∀ n ∈ s, M ≤ n) (hupper : ∀ n ∈ s, n ≤ 2 * M)
    (t : ℝ) :
    ‖logarithmicHilbertPrimitive s left right t‖ ≤
      (5 * Real.pi + 3) * M *
        ((∑ n ∈ s, Complex.normSq (left n)) +
          ∑ n ∈ s, Complex.normSq (right n)) := by
  rw [logarithmicHilbertPrimitive_eq_bilinearForm]
  have h := norm_logarithmicHilbertBilinearForm_le hM s
    (logarithmicTwist left t) (logarithmicTwist right t) hlower hupper
  simpa only [normSq_logarithmicTwist] using h

/-- Integration by parts for a bounded-variation amplitude preserves the
dyadic logarithmic Hilbert bound.  The finite sum is integrated as a whole,
so the off-diagonal cancellation is not lost term by term. -/
theorem norm_integral_amplitude_mul_logOffDiagonalForm_le
    {M : ℕ} (hM : 0 < M) (s : Finset ℕ) (left right : ℕ → ℂ)
    (hlower : ∀ n ∈ s, M ≤ n) (hupper : ∀ n ∈ s, n ≤ 2 * M)
    {A A' : ℝ → ℂ} {a b V : ℝ} (hab : a ≤ b)
    (hA : ∀ x ∈ Set.uIcc a b, HasDerivAt A (A' x) x)
    (hAend : ‖A a‖ ≤ 1 ∧ ‖A b‖ ≤ 1)
    (hA'int : IntervalIntegrable A' volume a b)
    (hvariation : (∫ x in a..b, ‖A' x‖) ≤ V) :
    ‖∫ t in a..b, A t * logOffDiagonalForm s left right t‖ ≤
      (2 + V) * ((5 * Real.pi + 3) * M *
        ((∑ n ∈ s, Complex.normSq (left n)) +
          ∑ n ∈ s, Complex.normSq (right n))) := by
  let H : ℝ → ℂ := logarithmicHilbertPrimitive s left right
  let B : ℝ → ℂ := logOffDiagonalForm s left right
  let K : ℝ := (5 * Real.pi + 3) * M *
    ((∑ n ∈ s, Complex.normSq (left n)) +
      ∑ n ∈ s, Complex.normSq (right n))
  have hpositive : ∀ n ∈ s, n ≠ 0 := by
    intro n hn hzero
    subst n
    have := hlower 0 hn
    omega
  have hHderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt H (I * B x) x := by
    intro x hx
    exact hasDerivAt_logarithmicHilbertPrimitive s left right hpositive x
  have hHbound : ∀ x : ℝ, ‖H x‖ ≤ K := by
    intro x
    exact norm_logarithmicHilbertPrimitive_le hM s left right
      hlower hupper x
  have hBint : IntervalIntegrable (fun x => I * B x) volume a b := by
    apply Continuous.intervalIntegrable
    dsimp only [B, logOffDiagonalForm, logOffDiagonalTerm]
    apply Continuous.const_mul
    apply continuous_finset_sum
    intro m hm
    apply continuous_finset_sum
    intro n hn
    split_ifs <;> fun_prop
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hA hHderiv hA'int hBint
  have hleft :
      (∫ x in a..b, A x * (I * B x)) =
        I * ∫ x in a..b, A x * B x := by
    calc
      (∫ x in a..b, A x * (I * B x)) =
          ∫ x in a..b, I * (A x * B x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        ring
      _ = I * ∫ x in a..b, A x * B x :=
        intervalIntegral.integral_const_mul _ _
  have hidentity :
      I * ∫ x in a..b, A x * B x =
        A b * H b - A a * H a - ∫ x in a..b, A' x * H x :=
    hleft.symm.trans hparts
  have hsumNonneg : 0 ≤
      (∑ n ∈ s, Complex.normSq (left n)) +
        ∑ n ∈ s, Complex.normSq (right n) := by
    apply add_nonneg
    · apply Finset.sum_nonneg
      intro n hn
      exact Complex.normSq_nonneg (left n)
    · apply Finset.sum_nonneg
      intro n hn
      exact Complex.normSq_nonneg (right n)
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hrem : ‖∫ x in a..b, A' x * H x‖ ≤ K * V := by
    have hmajorInt : IntervalIntegrable (fun x => K * ‖A' x‖)
        volume a b := (hA'int.norm).const_mul K
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le hab
      (by
        filter_upwards with x
        intro hx
        calc
          ‖A' x * H x‖ = ‖A' x‖ * ‖H x‖ := norm_mul _ _
          _ ≤ ‖A' x‖ * K :=
            mul_le_mul_of_nonneg_left (hHbound x) (norm_nonneg _)
          _ = K * ‖A' x‖ := by ring)
      hmajorInt
    calc
      ‖∫ x in a..b, A' x * H x‖ ≤
          ∫ x in a..b, K * ‖A' x‖ := hnorm
      _ = K * ∫ x in a..b, ‖A' x‖ :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ K * V := mul_le_mul_of_nonneg_left hvariation hK
  have hend : ‖A b * H b - A a * H a‖ ≤ 2 * K := by
    calc
      ‖A b * H b - A a * H a‖ ≤
          ‖A b * H b‖ + ‖A a * H a‖ := norm_sub_le _ _
      _ = ‖A b‖ * ‖H b‖ + ‖A a‖ * ‖H a‖ := by
        rw [norm_mul, norm_mul]
      _ ≤ 1 * K + 1 * K := by
        exact add_le_add
          (mul_le_mul hAend.2 (hHbound b) (norm_nonneg _) (by norm_num))
          (mul_le_mul hAend.1 (hHbound a) (norm_nonneg _) (by norm_num))
      _ = 2 * K := by ring
  calc
    ‖∫ t in a..b, A t * logOffDiagonalForm s left right t‖ =
        ‖I * ∫ t in a..b, A t * B t‖ := by
      rw [norm_mul, norm_I, one_mul]
    _ = ‖A b * H b - A a * H a - ∫ x in a..b, A' x * H x‖ := by
      rw [hidentity]
    _ ≤ ‖A b * H b - A a * H a‖ +
          ‖∫ x in a..b, A' x * H x‖ := norm_sub_le _ _
    _ ≤ 2 * K + K * V := add_le_add hend hrem
    _ = (2 + V) * K := by ring

end MathlibAux
