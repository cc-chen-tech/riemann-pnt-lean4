import MathlibAux.DyadicLogHilbert
import MathlibAux.LogarithmicHilbertIntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Star

open Complex MeasureTheory Set
open scoped BigOperators

namespace MathlibAux

/-- A logarithmic-frequency coefficient carrying both its slowly varying
amplitude and the unitary Fourier twist. -/
noncomputable def timeLogTwist
    (coeff : ℝ → ℕ → ℂ) (t : ℝ) (n : ℕ) : ℂ :=
  coeff t n * Complex.exp (I * ((Real.log n * t : ℝ) : ℂ))

/-- A logarithmic-frequency polynomial with coefficients that may vary with
the integration parameter. -/
noncomputable def timeDependentLogPolynomial
    (s : Finset ℕ) (coeff : ℝ → ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ s, timeLogTwist coeff t n

/-- The same moving logarithmic polynomial with negative frequencies. -/
noncomputable def timeDependentNegLogPolynomial
    (s : Finset ℕ) (coeff : ℝ → ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ s,
    coeff t n * Complex.exp (-I * ((Real.log n * t : ℝ) : ℂ))

/-- Negative logarithmic frequencies are the conjugate of the positive-frequency
polynomial with conjugated coefficients. -/
theorem timeDependentNegLogPolynomial_eq_conj
    (s : Finset ℕ) (coeff : ℝ → ℕ → ℂ) (t : ℝ) :
    timeDependentNegLogPolynomial s coeff t =
      (starRingEnd ℂ)
        (timeDependentLogPolynomial s
          (fun x n => (starRingEnd ℂ) (coeff x n)) t) := by
  unfold timeDependentNegLogPolynomial timeDependentLogPolynomial timeLogTwist
  simp only [map_sum, map_mul, RingHomCompTriple.comp_apply,
    RingHom.id_apply, ← Complex.exp_conj, conj_I, conj_ofReal]

private theorem exp_log_gap_eq_twists (m n : ℕ) (t : ℝ) :
    Complex.exp (-(I * ((Real.log n * t : ℝ) : ℂ))) *
        Complex.exp (I * ((Real.log m * t : ℝ) : ℂ)) =
      Complex.exp (I *
        (((Real.log m - Real.log n) * t : ℝ) : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact diagonal/off-diagonal expansion of the moving logarithmic
polynomial. -/
theorem normSq_timeDependentLogPolynomial_eq
    (s : Finset ℕ) (coeff : ℝ → ℕ → ℂ) (t : ℝ) :
    Complex.normSq (timeDependentLogPolynomial s coeff t) =
      (∑ n ∈ s, Complex.normSq (coeff t n)) +
        (logOffDiagonalForm s (coeff t) (coeff t) t).re := by
  have hcomplex :
      (starRingEnd ℂ) (timeDependentLogPolynomial s coeff t) *
          timeDependentLogPolynomial s coeff t =
        ((∑ n ∈ s, Complex.normSq (coeff t n) : ℝ) : ℂ) +
          logOffDiagonalForm s (coeff t) (coeff t) t := by
    unfold timeDependentLogPolynomial timeLogTwist logOffDiagonalForm
      logOffDiagonalTerm
    simp only [map_sum, Finset.sum_mul, Finset.mul_sum, map_mul,
      ← Complex.exp_conj, conj_I, conj_ofReal]
    rw [show
        (∑ m ∈ s, ∑ n ∈ s,
          ((starRingEnd ℂ) (coeff t n) *
              Complex.exp (-I * ((Real.log n * t : ℝ) : ℂ))) *
            (coeff t m *
              Complex.exp (I * ((Real.log m * t : ℝ) : ℂ)))) =
        (∑ m ∈ s, ∑ n ∈ s,
          if m = n then (Complex.normSq (coeff t n) : ℂ)
          else (starRingEnd ℂ) (coeff t n) * coeff t m *
            Complex.exp (I *
              ((((Real.log m : ℝ) : ℂ) - ((Real.log n : ℝ) : ℂ)) *
                (t : ℂ)))) by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hmn : m = n
      · subst n
        rw [if_pos rfl]
        rw [show
            (starRingEnd ℂ) (coeff t m) *
                Complex.exp (-I * ((Real.log m * t : ℝ) : ℂ)) *
                (coeff t m *
                  Complex.exp (I * ((Real.log m * t : ℝ) : ℂ))) =
              ((starRingEnd ℂ) (coeff t m) * coeff t m) *
                (Complex.exp (-I * ((Real.log m * t : ℝ) : ℂ)) *
                  Complex.exp (I * ((Real.log m * t : ℝ) : ℂ))) by ring]
        rw [show Complex.exp (-I * ((Real.log m * t : ℝ) : ℂ)) *
            Complex.exp (I * ((Real.log m * t : ℝ) : ℂ)) = 1 by
          rw [← Complex.exp_add]
          simp]
        rw [mul_one, ← Complex.normSq_eq_conj_mul_self]
      · rw [if_neg hmn]
        rw [show
            (starRingEnd ℂ) (coeff t n) *
                Complex.exp (-I * ((Real.log n * t : ℝ) : ℂ)) *
                (coeff t m *
                  Complex.exp (I * ((Real.log m * t : ℝ) : ℂ))) =
              ((starRingEnd ℂ) (coeff t n) * coeff t m) *
                (Complex.exp (-(I * ((Real.log n * t : ℝ) : ℂ))) *
                  Complex.exp (I * ((Real.log m * t : ℝ) : ℂ))) by ring]
        rw [exp_log_gap_eq_twists]
        push_cast
        ring]
    have hsplit (m n : ℕ) :
        (if m = n then (Complex.normSq (coeff t n) : ℂ)
          else (starRingEnd ℂ) (coeff t n) * coeff t m *
            Complex.exp (I *
              ((((Real.log m : ℝ) : ℂ) - ((Real.log n : ℝ) : ℂ)) *
                (t : ℂ)))) =
        (if m = n then (Complex.normSq (coeff t n) : ℂ) else 0) +
          (if m = n then 0
            else (starRingEnd ℂ) (coeff t n) * coeff t m *
              Complex.exp (I *
                ((((Real.log m : ℝ) : ℂ) - ((Real.log n : ℝ) : ℂ)) *
                  (t : ℂ)))) := by
      by_cases hmn : m = n <;> simp [hmn]
    simp_rw [hsplit]
    simp only [Finset.sum_add_distrib]
    congr 1
    calc
      (∑ m ∈ s, ∑ n ∈ s,
          if m = n then (Complex.normSq (coeff t n) : ℂ) else 0) =
          ∑ m ∈ s, (Complex.normSq (coeff t m) : ℂ) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [Finset.sum_eq_single m]
        · simp
        · intro n hn hnm
          simp [hnm.symm]
        · intro hnot
          exact (hnot hm).elim
      _ = ((∑ n ∈ s, Complex.normSq (coeff t n) : ℝ) : ℂ) := by
        push_cast
        rfl
  rw [show Complex.normSq (timeDependentLogPolynomial s coeff t) =
      ((starRingEnd ℂ) (timeDependentLogPolynomial s coeff t) *
        timeDependentLogPolynomial s coeff t).re by
      exact congrArg Complex.re
        (Complex.normSq_eq_conj_mul_self
          (z := timeDependentLogPolynomial s coeff t))]
  rw [hcomplex]
  simp

/-- The integration-by-parts primitive for the off-diagonal part of a
logarithmic polynomial with time-dependent coefficients. -/
noncomputable def timeDependentLogHilbertPrimitive
    (s : Finset ℕ) (coeff : ℝ → ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ m ∈ s, ∑ n ∈ s,
    if m = n then 0
    else ((starRingEnd ℂ) (coeff t n) * coeff t m *
        ((1 / (Real.log (m : ℝ) - Real.log (n : ℝ)) : ℝ) : ℂ)) *
      Complex.exp (I *
        (((Real.log m - Real.log n) * t : ℝ) : ℂ))

/-- The two amplitude-derivative terms produced by differentiating the
moving Hilbert primitive. -/
noncomputable def timeDependentLogHilbertVariation
    (s : Finset ℕ) (coeff coeff' : ℝ → ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ m ∈ s, ∑ n ∈ s,
    if m = n then 0
    else (((starRingEnd ℂ) (coeff' t n) * coeff t m +
          (starRingEnd ℂ) (coeff t n) * coeff' t m) *
        ((1 / (Real.log (m : ℝ) - Real.log (n : ℝ)) : ℝ) : ℂ)) *
      Complex.exp (I *
        (((Real.log m - Real.log n) * t : ℝ) : ℂ))

private theorem normSq_timeLogTwist
    (coeff : ℝ → ℕ → ℂ) (t : ℝ) (n : ℕ) :
    Complex.normSq (timeLogTwist coeff t n) =
      Complex.normSq (coeff t n) := by
  unfold timeLogTwist
  rw [Complex.normSq_mul]
  have hexp : Complex.normSq
      (Complex.exp (I * ((Real.log n * t : ℝ) : ℂ))) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_I_mul_ofReal]
    norm_num
  rw [hexp, mul_one]

private theorem hasDerivAt_timeDependentLogHilbertPrimitiveTerm
    (coeff coeff' : ℝ → ℕ → ℂ) {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) {t : ℝ}
    (hmDeriv : HasDerivAt (fun x ↦ coeff x m) (coeff' t m) t)
    (hnDeriv : HasDerivAt (fun x ↦ coeff x n) (coeff' t n) t) :
    HasDerivAt
      (fun x : ℝ =>
        if m = n then 0
        else ((starRingEnd ℂ) (coeff x n) * coeff x m *
            ((1 / (Real.log (m : ℝ) - Real.log (n : ℝ)) : ℝ) : ℂ)) *
          Complex.exp (I *
            (((Real.log m - Real.log n) * x : ℝ) : ℂ)))
      (if m = n then 0
        else I * logOffDiagonalTerm (coeff t) (coeff t) m n t +
          ((((starRingEnd ℂ) (coeff' t n) * coeff t m +
              (starRingEnd ℂ) (coeff t n) * coeff' t m) *
            ((1 / (Real.log (m : ℝ) - Real.log (n : ℝ)) : ℝ) : ℂ)) *
          Complex.exp (I *
            (((Real.log m - Real.log n) * t : ℝ) : ℂ)))) t := by
  by_cases hmn : m = n
  · subst n
    simpa using (hasDerivAt_const t (0 : ℂ))
  · have hmpos : 0 < (m : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hm
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    have hgap : Real.log (m : ℝ) - Real.log (n : ℝ) ≠ 0 := by
      apply sub_ne_zero.mpr
      intro hlog
      exact hmn (Nat.cast_injective
        (Real.log_injOn_pos hmpos hnpos hlog))
    have hamp := hnDeriv.star.mul hmDeriv
    have harg : HasDerivAt
        (fun x : ℝ => I *
          (((Real.log m - Real.log n) * x : ℝ) : ℂ))
        (I * ((Real.log m - Real.log n : ℝ) : ℂ)) t := by
      convert (Complex.ofRealCLM.hasDerivAt.const_mul
        (I * ((Real.log m - Real.log n : ℝ) : ℂ))) using 1 <;>
        simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one]
      funext x
      push_cast
      ring
    have hterm := (hamp.mul harg.cexp).mul_const
      (((1 / (Real.log (m : ℝ) - Real.log (n : ℝ)) : ℝ) : ℂ))
    simp only [hmn, if_false]
    convert hterm using 1
    · funext x
      simp only [Pi.mul_apply, starRingEnd_apply]
      push_cast
      ring
    · unfold logOffDiagonalTerm
      simp only [hmn, if_false, Pi.mul_apply, starRingEnd_apply]
      have hgapC :
          ((Real.log (m : ℝ) - Real.log (n : ℝ) : ℝ) : ℂ) ≠ 0 :=
        ofReal_ne_zero.mpr hgap
      have hcancel :
          ((Real.log (m : ℝ) - Real.log (n : ℝ) : ℝ) : ℂ) *
              ((Real.log (m : ℝ) - Real.log (n : ℝ) : ℝ) : ℂ)⁻¹ = 1 :=
        mul_inv_cancel₀ hgapC
      have hmain :
          I * (star (coeff t n) * coeff t m *
            Complex.exp (I *
              ((((Real.log m : ℝ) : ℂ) - ((Real.log n : ℝ) : ℂ)) *
                (t : ℂ)))) =
            I * star (coeff t n) * coeff t m *
              Complex.exp (I *
                ((((Real.log m : ℝ) : ℂ) - ((Real.log n : ℝ) : ℂ)) *
                  (t : ℂ))) *
              ((Real.log (m : ℝ) - Real.log (n : ℝ) : ℝ) : ℂ) *
              ((Real.log (m : ℝ) - Real.log (n : ℝ) : ℝ) : ℂ)⁻¹ := by
        calc
          I * (star (coeff t n) * coeff t m *
              Complex.exp (I *
                ((((Real.log m : ℝ) : ℂ) - ((Real.log n : ℝ) : ℂ)) *
                  (t : ℂ)))) =
              (I * star (coeff t n) * coeff t m *
                Complex.exp (I *
                  ((((Real.log m : ℝ) : ℂ) - ((Real.log n : ℝ) : ℂ)) *
                    (t : ℂ)))) * 1 := by ring
          _ = (I * star (coeff t n) * coeff t m *
                Complex.exp (I *
                  ((((Real.log m : ℝ) : ℂ) - ((Real.log n : ℝ) : ℂ)) *
                    (t : ℂ)))) *
              (((Real.log (m : ℝ) - Real.log (n : ℝ) : ℝ) : ℂ) *
                ((Real.log (m : ℝ) - Real.log (n : ℝ) : ℝ) : ℂ)⁻¹) := by
                  rw [hcancel]
          _ = _ := by ring
      rw [hmain]
      push_cast
      ring

/-- Differentiating the moving Hilbert primitive gives the off-diagonal
form plus the two amplitude-variation forms. -/
theorem hasDerivAt_timeDependentLogHilbertPrimitive
    (s : Finset ℕ) (coeff coeff' : ℝ → ℕ → ℂ)
    (hpositive : ∀ n ∈ s, n ≠ 0) {t : ℝ}
    (hderiv : ∀ n ∈ s,
      HasDerivAt (fun x ↦ coeff x n) (coeff' t n) t) :
    HasDerivAt (timeDependentLogHilbertPrimitive s coeff)
      (I * logOffDiagonalForm s (coeff t) (coeff t) t +
        timeDependentLogHilbertVariation s coeff coeff' t) t := by
  unfold timeDependentLogHilbertPrimitive
  convert HasDerivAt.fun_sum (u := s) (x := t)
    (fun m hm => HasDerivAt.fun_sum (u := s) (x := t)
      (fun n hn => hasDerivAt_timeDependentLogHilbertPrimitiveTerm
        coeff coeff' (hpositive m hm) (hpositive n hn)
        (hderiv m hm) (hderiv n hn))) using 1
  unfold logOffDiagonalForm timeDependentLogHilbertVariation
  simp only [Finset.mul_sum]
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hmn : m = n <;> simp [hmn, logOffDiagonalTerm]

private theorem timeDependentLogHilbertPrimitive_eq_bilinear
    (s : Finset ℕ) (coeff : ℝ → ℕ → ℂ) (t : ℝ) :
    timeDependentLogHilbertPrimitive s coeff t =
      logarithmicHilbertBilinearForm s
        (timeLogTwist coeff t) (timeLogTwist coeff t) := by
  unfold timeDependentLogHilbertPrimitive
    logarithmicHilbertBilinearForm timeLogTwist
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hmn : m = n
  · simp [hmn]
  · simp only [hmn, if_false, map_mul, ← Complex.exp_conj,
      conj_I, conj_ofReal]
    rw [← exp_log_gap_eq_twists]
    ring

private theorem timeDependentLogHilbertVariation_eq_bilinear
    (s : Finset ℕ) (coeff coeff' : ℝ → ℕ → ℂ) (t : ℝ) :
    timeDependentLogHilbertVariation s coeff coeff' t =
      logarithmicHilbertBilinearForm s
          (timeLogTwist coeff' t) (timeLogTwist coeff t) +
        logarithmicHilbertBilinearForm s
          (timeLogTwist coeff t) (timeLogTwist coeff' t) := by
  unfold timeDependentLogHilbertVariation
    logarithmicHilbertBilinearForm timeLogTwist
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hmn : m = n
  · simp [hmn]
  · simp only [hmn, if_false, map_mul, ← Complex.exp_conj,
      conj_I, conj_ofReal]
    rw [← exp_log_gap_eq_twists]
    ring

/-- Pointwise Hilbert bound for the moving primitive under a global index
cutoff. -/
theorem norm_timeDependentLogHilbertPrimitive_le
    {N : ℕ} (hN : 0 < N) (s : Finset ℕ) (coeff : ℝ → ℕ → ℂ)
    (hpositive : ∀ n ∈ s, n ≠ 0) (hupper : ∀ n ∈ s, n ≤ N)
    (t : ℝ) :
    ‖timeDependentLogHilbertPrimitive s coeff t‖ ≤
      2 * (5 * Real.pi + 4) * N *
        ∑ n ∈ s, Complex.normSq (coeff t n) := by
  rw [timeDependentLogHilbertPrimitive_eq_bilinear]
  have h := norm_logarithmicHilbertBilinearForm_le_of_upper
    hN s (timeLogTwist coeff t) (timeLogTwist coeff t)
    hpositive hupper
  simp_rw [normSq_timeLogTwist] at h
  nlinarith

private theorem logarithmicHilbertBilinearForm_eq_scaled
    (s : Finset ℕ) (left right : ℕ → ℂ) {q : ℝ} (hq : 0 < q) :
    logarithmicHilbertBilinearForm s left right =
      logarithmicHilbertBilinearForm s
        (fun n => (q : ℂ) * left n)
        (fun n => ((q : ℂ)⁻¹) * right n) := by
  have hqC : (q : ℂ) ≠ 0 := ofReal_ne_zero.mpr hq.ne'
  unfold logarithmicHilbertBilinearForm
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hmn : m = n
  · simp [hmn]
  · simp only [hmn, if_false, map_mul, conj_ofReal]
    symm
    calc
      (q : ℂ) * (starRingEnd ℂ) (left n) *
          ((q : ℂ)⁻¹ * right m) *
          ((1 / (Real.log (m : ℝ) - Real.log (n : ℝ)) : ℝ) : ℂ) =
          ((q : ℂ) * (q : ℂ)⁻¹) *
            ((starRingEnd ℂ) (left n) * right m *
              ((1 / (Real.log (m : ℝ) - Real.log (n : ℝ)) : ℝ) : ℂ)) := by
            ring
      _ = (starRingEnd ℂ) (left n) * right m *
          ((1 / (Real.log (m : ℝ) - Real.log (n : ℝ)) : ℝ) : ℂ) := by
            rw [mul_inv_cancel₀ hqC, one_mul]

private theorem sum_normSq_scaled
    (s : Finset ℕ) (coeff : ℕ → ℂ) (q : ℝ) :
    (∑ n ∈ s, Complex.normSq ((q : ℂ) * coeff n)) =
      q ^ 2 * ∑ n ∈ s, Complex.normSq (coeff n) := by
  simp only [Complex.normSq_mul, Complex.normSq_ofReal, Finset.mul_sum]
  ring

private theorem sum_normSq_invScaled
    (s : Finset ℕ) (coeff : ℕ → ℂ) {q : ℝ} (hq : 0 < q) :
    (∑ n ∈ s, Complex.normSq (((q : ℂ)⁻¹) * coeff n)) =
      (q ^ 2)⁻¹ * ∑ n ∈ s, Complex.normSq (coeff n) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Complex.normSq_mul, Complex.normSq_inv,
    Complex.normSq_ofReal]
  field_simp [hq.ne']

/-- Opposite scaling of the two differentiated coefficient sequences gives
a balanced variation bound. -/
theorem norm_timeDependentLogHilbertVariation_le
    {N : ℕ} (hN : 0 < N) (s : Finset ℕ)
    (coeff coeff' : ℝ → ℕ → ℂ)
    (hpositive : ∀ n ∈ s, n ≠ 0) (hupper : ∀ n ∈ s, n ≤ N)
    {q t E D : ℝ} (hq : 0 < q)
    (henergy : (∑ n ∈ s, Complex.normSq (coeff t n)) ≤ E)
    (hderivEnergy : (∑ n ∈ s, Complex.normSq (coeff' t n)) ≤ D) :
    ‖timeDependentLogHilbertVariation s coeff coeff' t‖ ≤
      2 * (5 * Real.pi + 4) * N *
        (q ^ 2 * D + (q ^ 2)⁻¹ * E) := by
  let left : ℕ → ℂ := fun n => (q : ℂ) * timeLogTwist coeff' t n
  let right : ℕ → ℂ := fun n => ((q : ℂ)⁻¹) * timeLogTwist coeff t n
  have hfirst :
      logarithmicHilbertBilinearForm s
          (timeLogTwist coeff' t) (timeLogTwist coeff t) =
        logarithmicHilbertBilinearForm s left right := by
    simpa only [left, right] using logarithmicHilbertBilinearForm_eq_scaled
      s (timeLogTwist coeff' t) (timeLogTwist coeff t) hq
  have hsecond :
      logarithmicHilbertBilinearForm s
          (timeLogTwist coeff t) (timeLogTwist coeff' t) =
        logarithmicHilbertBilinearForm s right left := by
    have hqinv : 0 < q⁻¹ := inv_pos.mpr hq
    have h := logarithmicHilbertBilinearForm_eq_scaled
      s (timeLogTwist coeff t) (timeLogTwist coeff' t) hqinv
    simpa only [left, right, inv_inv, Complex.ofReal_inv] using h
  have hleftSum :
      (∑ n ∈ s, Complex.normSq (left n)) ≤ q ^ 2 * D := by
    rw [show (∑ n ∈ s, Complex.normSq (left n)) =
        q ^ 2 * ∑ n ∈ s, Complex.normSq (coeff' t n) by
      simpa only [left, normSq_timeLogTwist] using
        sum_normSq_scaled s (timeLogTwist coeff' t) q]
    exact mul_le_mul_of_nonneg_left hderivEnergy (sq_nonneg q)
  have hrightSum :
      (∑ n ∈ s, Complex.normSq (right n)) ≤ (q ^ 2)⁻¹ * E := by
    rw [show (∑ n ∈ s, Complex.normSq (right n)) =
        (q ^ 2)⁻¹ * ∑ n ∈ s, Complex.normSq (coeff t n) by
      simpa only [right, normSq_timeLogTwist] using
        sum_normSq_invScaled s (timeLogTwist coeff t) hq]
    exact mul_le_mul_of_nonneg_left henergy (by positivity)
  have hb1 := norm_logarithmicHilbertBilinearForm_le_of_upper
    hN s left right hpositive hupper
  have hb2 := norm_logarithmicHilbertBilinearForm_le_of_upper
    hN s right left hpositive hupper
  rw [timeDependentLogHilbertVariation_eq_bilinear, hfirst, hsecond]
  calc
    ‖logarithmicHilbertBilinearForm s left right +
        logarithmicHilbertBilinearForm s right left‖ ≤
        ‖logarithmicHilbertBilinearForm s left right‖ +
          ‖logarithmicHilbertBilinearForm s right left‖ := norm_add_le _ _
    _ ≤ 2 * ((5 * Real.pi + 4) * N *
        ((∑ n ∈ s, Complex.normSq (left n)) +
          ∑ n ∈ s, Complex.normSq (right n))) := by linarith
    _ ≤ 2 * (5 * Real.pi + 4) * N *
        (q ^ 2 * D + (q ^ 2)⁻¹ * E) := by
      have hconst : 0 ≤ (5 * Real.pi + 4) * (N : ℝ) := by positivity
      nlinarith

/-- Whole-sum integration by parts for a logarithmic polynomial with
time-dependent coefficients.  The endpoint cost uses the coefficient
energy, while the interior cost uses the much smaller derivative energy. -/
theorem norm_integral_timeDependentLogOffDiagonal_le
    {N : ℕ} (hN : 0 < N) (s : Finset ℕ)
    (coeff coeff' : ℝ → ℕ → ℂ)
    (hpositive : ∀ n ∈ s, n ≠ 0) (hupper : ∀ n ∈ s, n ≤ N)
    {a b q E D : ℝ} (hab : a ≤ b) (hq : 0 < q)
    (hderiv : ∀ t ∈ Set.uIcc a b, ∀ n ∈ s,
      HasDerivAt (fun x ↦ coeff x n) (coeff' t n) t)
    (hoffInt : IntervalIntegrable
      (fun t => logOffDiagonalForm s (coeff t) (coeff t) t)
      volume a b)
    (hvarInt : IntervalIntegrable
      (timeDependentLogHilbertVariation s coeff coeff') volume a b)
    (henergy : ∀ t ∈ Set.uIcc a b,
      (∑ n ∈ s, Complex.normSq (coeff t n)) ≤ E)
    (hderivEnergy : ∀ t ∈ Set.uIcc a b,
      (∑ n ∈ s, Complex.normSq (coeff' t n)) ≤ D) :
    ‖∫ t in a..b, logOffDiagonalForm s (coeff t) (coeff t) t‖ ≤
      4 * (5 * Real.pi + 4) * N * E +
        |b - a| *
          (2 * (5 * Real.pi + 4) * N *
            (q ^ 2 * D + (q ^ 2)⁻¹ * E)) := by
  let H : ℝ → ℂ := timeDependentLogHilbertPrimitive s coeff
  let F : ℝ → ℂ := fun t => logOffDiagonalForm s (coeff t) (coeff t) t
  let V : ℝ → ℂ := timeDependentLogHilbertVariation s coeff coeff'
  have hHderiv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt H (I * F t + V t) t := by
    intro t ht
    exact hasDerivAt_timeDependentLogHilbertPrimitive s coeff coeff'
      hpositive (fun n hn => hderiv t ht n hn)
  have htotalInt : IntervalIntegrable
      (fun t => I * F t + V t) volume a b := by
    exact (hoffInt.const_mul I).add hvarInt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    hHderiv htotalInt
  have hidentity :
      I * (∫ t in a..b, F t) =
        H b - H a - ∫ t in a..b, V t := by
    calc
      I * (∫ t in a..b, F t) = ∫ t in a..b, I * F t :=
        (intervalIntegral.integral_const_mul _ _).symm
      _ = (∫ t in a..b, I * F t + V t) - ∫ t in a..b, V t := by
        rw [intervalIntegral.integral_add (hoffInt.const_mul I) hvarInt]
        ring
      _ = H b - H a - ∫ t in a..b, V t := by rw [hFTC]
  have haMem : a ∈ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    exact ⟨le_rfl, hab⟩
  have hbMem : b ∈ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    exact ⟨hab, le_rfl⟩
  have hHa : ‖H a‖ ≤ 2 * (5 * Real.pi + 4) * N * E := by
    dsimp only [H]
    exact (norm_timeDependentLogHilbertPrimitive_le
      hN s coeff hpositive hupper a).trans
        (mul_le_mul_of_nonneg_left (henergy a haMem) (by positivity))
  have hHb : ‖H b‖ ≤ 2 * (5 * Real.pi + 4) * N * E := by
    dsimp only [H]
    exact (norm_timeDependentLogHilbertPrimitive_le
      hN s coeff hpositive hupper b).trans
        (mul_le_mul_of_nonneg_left (henergy b hbMem) (by positivity))
  let B : ℝ := 2 * (5 * Real.pi + 4) * N *
    (q ^ 2 * D + (q ^ 2)⁻¹ * E)
  have hVpoint : ∀ t ∈ Set.uIcc a b, ‖V t‖ ≤ B := by
    intro t ht
    dsimp only [V, B]
    exact norm_timeDependentLogHilbertVariation_le
      hN s coeff coeff' hpositive hupper hq
        (henergy t ht) (hderivEnergy t ht)
  have hVint : ‖∫ t in a..b, V t‖ ≤ B * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    apply hVpoint t
    exact Set.uIoc_subset_uIcc ht
  calc
    ‖∫ t in a..b, F t‖ = ‖I * ∫ t in a..b, F t‖ := by
      rw [norm_mul, norm_I, one_mul]
    _ = ‖H b - H a - ∫ t in a..b, V t‖ := by rw [hidentity]
    _ ≤ ‖H b‖ + ‖H a‖ + ‖∫ t in a..b, V t‖ := by
      calc
        ‖H b - H a - ∫ t in a..b, V t‖ ≤
            ‖H b - H a‖ + ‖∫ t in a..b, V t‖ := norm_sub_le _ _
        _ ≤ ‖H b‖ + ‖H a‖ + ‖∫ t in a..b, V t‖ := by
          gcongr
          exact norm_sub_le _ _
    _ ≤ 4 * (5 * Real.pi + 4) * N * E + B * |b - a| := by
      nlinarith
    _ = 4 * (5 * Real.pi + 4) * N * E +
        |b - a| *
          (2 * (5 * Real.pi + 4) * N *
            (q ^ 2 * D + (q ^ 2)⁻¹ * E)) := by
      dsimp only [B]
      ring

end MathlibAux
