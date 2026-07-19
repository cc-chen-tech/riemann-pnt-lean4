import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

open Complex
open scoped BigOperators ComplexConjugate Interval

namespace PrimeNumberTheorem
namespace DirichletPolynomial

/-- A finite exponential sum with real frequencies. -/
noncomputable def finiteExponentialSum {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c : ι → ℂ) (omega : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ n ∈ S, c n * Complex.exp (Complex.I * (omega n * t))

/-- The finite Dirichlet polynomial on a vertical line, written with arbitrary
complex coefficients. -/
noncomputable def finiteDirichletPolynomial
    (S : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) : ℂ :=
  finiteExponentialSum S c (fun n => -Real.log n) t

/-- Twist the coefficients of a finite exponential sum by their phases at time `t`. -/
noncomputable def phaseTwist {ι : Type*}
    (c : ι → ℂ) (omega : ι → ℝ) (t : ℝ) (n : ι) : ℂ :=
  c n * Complex.exp (Complex.I * (omega n * t))

/-- The off-diagonal Hilbert form attached to a finite family of real frequencies. -/
noncomputable def hilbertForm {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c : ι → ℂ) (omega : ι → ℝ) : ℂ :=
  ∑ m ∈ S, ∑ n ∈ S,
    if m = n then 0 else conj (c m) * c n / (omega n - omega m)

/-- The off-diagonal Hilbert form is purely imaginary.  This is the finite
matrix symmetry used by two-sided positive-kernel proofs of Hilbert's
inequality. -/
theorem conj_hilbertForm_eq_neg {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c : ι → ℂ) (omega : ι → ℝ) :
    conj (hilbertForm S c omega) = -hilbertForm S c omega := by
  unfold hilbertForm
  simp only [map_sum]
  calc
    (∑ m ∈ S, ∑ n ∈ S,
        conj (if m = n then 0
          else conj (c m) * c n / (omega n - omega m))) =
        ∑ m ∈ S, ∑ n ∈ S,
          -(if n = m then 0
            else conj (c n) * c m / (omega m - omega n)) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hmn : m = n
      · subst n
        simp
      · simp only [if_neg hmn, if_neg (Ne.symm hmn)]
        have hden :
            ((omega n : ℂ) - (omega m : ℂ))⁻¹ =
              -((omega m : ℂ) - (omega n : ℂ))⁻¹ := by
          rw [show (omega m : ℂ) - (omega n : ℂ) =
            -((omega n : ℂ) - (omega m : ℂ)) by ring, inv_neg]
          ring
        change conj (conj (c m) * c n *
            (((omega n : ℂ) - (omega m : ℂ))⁻¹)) =
          -(conj (c n) * c m *
            (((omega m : ℂ) - (omega n : ℂ))⁻¹))
        rw [map_mul, map_mul, map_inv₀, map_sub, conj_conj,
          conj_ofReal, conj_ofReal, hden]
        ring
    _ = ∑ m ∈ S, ∑ n ∈ S,
          -(if m = n then 0
            else conj (c m) * c n / (omega n - omega m)) := by
      rw [Finset.sum_comm]
    _ = -(∑ m ∈ S, ∑ n ∈ S,
          if m = n then 0
          else conj (c m) * c n / (omega n - omega m)) := by
      simp

/-- Real-part formulation of `conj_hilbertForm_eq_neg`. -/
theorem hilbertForm_re_eq_zero {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c : ι → ℂ) (omega : ι → ℝ) :
    (hilbertForm S c omega).re = 0 := by
  have h := congrArg Complex.re (conj_hilbertForm_eq_neg S c omega)
  simp only [conj_re, neg_re] at h
  linarith

/-- A two-sided positive-kernel certificate controls the norm of the Hilbert
form.  Fourier proofs of the weighted Hilbert--Montgomery--Vaughan inequality
produce exactly these two real-part inequalities. -/
theorem norm_hilbertForm_le_of_two_sided_re_nonneg
    {ι : Type*} [DecidableEq ι] {S : Finset ι}
    {c : ι → ℂ} {omega : ι → ℝ} {D : ℝ}
    (hplus : 0 ≤ ((D : ℂ) + Complex.I * hilbertForm S c omega).re)
    (hminus : 0 ≤ ((D : ℂ) - Complex.I * hilbertForm S c omega).re) :
    ‖hilbertForm S c omega‖ ≤ D := by
  have hre := hilbertForm_re_eq_zero S c omega
  have himUpper : (hilbertForm S c omega).im ≤ D := by
    simpa using hplus
  have himLower : -D ≤ (hilbertForm S c omega).im := by
    have h : 0 ≤ D + (hilbertForm S c omega).im := by
      simpa using hminus
    linarith
  rw [Complex.norm_def, Complex.normSq_apply, hre, zero_mul, zero_add,
    ← pow_two, Real.sqrt_sq_eq_abs]
  exact abs_le.mpr ⟨himLower, himUpper⟩

private theorem integral_exp_mul_complex {a b : ℝ} {c : ℂ} (hc : c ≠ 0) :
    (∫ x in a..b, Complex.exp (c * x)) =
      (Complex.exp (c * b) - Complex.exp (c * a)) / c := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => Complex.exp (c * y) / c)
        (Complex.exp (c * x)) x := by
    intro x
    conv => congr
    rw [← mul_div_cancel_right₀ (Complex.exp (c * x)) hc]
    apply ((Complex.hasDerivAt_exp _).comp x _).div_const c
    simpa only [mul_one] using
      ((hasDerivAt_id (x : ℂ)).const_mul _).comp_ofReal
  rw [intervalIntegral.integral_deriv_eq_sub' _
    (funext fun x => (hderiv x).deriv)
    (fun x _ => (hderiv x).differentiableAt)]
  · ring
  · fun_prop

/-- A single nonzero real frequency has interval integral at most `2 / |d|`.
This is the off-diagonal kernel estimate in the finite mean-square bound. -/
theorem norm_integral_exp_I_mul_le_two_div {a b d : ℝ} (hd : d ≠ 0) :
    ‖∫ t in a..b, Complex.exp (Complex.I * (d * t))‖ ≤ 2 / |d| := by
  have hId : Complex.I * (d : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (ofReal_ne_zero.mpr hd)
  have hfun :
      (fun t : ℝ => Complex.exp (Complex.I * (d * t))) =
        fun t : ℝ => Complex.exp ((Complex.I * (d : ℂ)) * t) := by
    funext t
    congr 1
    ring
  rw [hfun, integral_exp_mul_complex hId, norm_div]
  have hnorm : ‖Complex.I * (d : ℂ)‖ = |d| := by simp
  rw [← hnorm]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖Complex.exp ((Complex.I * (d : ℂ)) * b) -
        Complex.exp ((Complex.I * (d : ℂ)) * a)‖
        ≤ ‖Complex.exp ((Complex.I * (d : ℂ)) * b)‖ +
          ‖Complex.exp ((Complex.I * (d : ℂ)) * a)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [Complex.norm_exp]

private lemma conj_mul_finiteExponentialSum_eq {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c : ι → ℂ) (omega : ι → ℝ) (t : ℝ) :
    conj (finiteExponentialSum S c omega t) *
        finiteExponentialSum S c omega t =
      ∑ m ∈ S, ∑ n ∈ S,
        conj (c m) * c n *
          Complex.exp (Complex.I * ((omega n - omega m) * t)) := by
  simp only [finiteExponentialSum, map_sum, map_mul, ← Complex.exp_conj,
    conj_I, conj_ofReal, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  calc
    conj (c m) * Complex.exp (-Complex.I * (omega m * t)) *
        (c n * Complex.exp (Complex.I * (omega n * t))) =
        conj (c m) * c n *
          (Complex.exp (-Complex.I * (omega m * t)) *
            Complex.exp (Complex.I * (omega n * t))) := by ring
    _ = conj (c m) * c n *
          Complex.exp (Complex.I * ((omega n - omega m) * t)) := by
      rw [← Complex.exp_add]
      congr 2
      ring

private lemma finiteExponentialMeanSquare_cast_eq {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c : ι → ℂ) (omega : ι → ℝ) (a b : ℝ) :
    ((∫ t in a..b, ‖finiteExponentialSum S c omega t‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ S, ∑ n ∈ S,
        conj (c m) * c n *
          (∫ t in a..b,
            Complex.exp (Complex.I * ((omega n - omega m) * t))) := by
  rw [← intervalIntegral.integral_ofReal]
  calc
    (∫ t in a..b,
        ((‖finiteExponentialSum S c omega t‖ ^ 2 : ℝ) : ℂ)) =
        ∫ t in a..b,
          conj (finiteExponentialSum S c omega t) *
            finiteExponentialSum S c omega t := by
      congr 1
      funext t
      rw [← Complex.normSq_eq_norm_sq,
        Complex.normSq_eq_conj_mul_self]
    _ = ∫ t in a..b, ∑ m ∈ S, ∑ n ∈ S,
          conj (c m) * c n *
            Complex.exp (Complex.I * ((omega n - omega m) * t)) := by
      congr 1
      funext t
      exact conj_mul_finiteExponentialSum_eq S c omega t
    _ = ∑ m ∈ S, ∑ n ∈ S,
          ∫ t in a..b, conj (c m) * c n *
            Complex.exp (Complex.I * ((omega n - omega m) * t)) := by
      rw [intervalIntegral.integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro m hm
        rw [intervalIntegral.integral_finset_sum]
        intro n hn
        exact Continuous.intervalIntegrable (μ := MeasureTheory.volume)
          (by fun_prop : Continuous fun t : ℝ =>
            conj (c m) * c n *
              Complex.exp (Complex.I * ((omega n - omega m) * t))) a b
      · intro m hm
        exact Continuous.intervalIntegrable (μ := MeasureTheory.volume)
          (by fun_prop : Continuous fun t : ℝ =>
            ∑ n ∈ S, conj (c m) * c n *
              Complex.exp (Complex.I * ((omega n - omega m) * t))) a b
    _ = ∑ m ∈ S, ∑ n ∈ S,
          conj (c m) * c n *
            (∫ t in a..b,
              Complex.exp (Complex.I * ((omega n - omega m) * t))) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      simpa only [mul_assoc] using
        (intervalIntegral.integral_const_mul (conj (c m) * c n)
          (fun t : ℝ =>
            Complex.exp (Complex.I * ((omega n - omega m) * t))))

private lemma conj_phaseTwist_mul_phaseTwist {ι : Type*}
    (c : ι → ℂ) (omega : ι → ℝ) (t : ℝ) (m n : ι) :
    conj (phaseTwist c omega t m) * phaseTwist c omega t n =
      conj (c m) * c n *
        Complex.exp (Complex.I * ((omega n - omega m) * t)) := by
  simp only [phaseTwist, map_mul, ← Complex.exp_conj, conj_I, conj_ofReal]
  calc
    conj (c m) * Complex.exp (-Complex.I * (omega m * t)) *
        (c n * Complex.exp (Complex.I * (omega n * t))) =
        conj (c m) * c n *
          (Complex.exp (-Complex.I * (omega m * t)) *
            Complex.exp (Complex.I * (omega n * t))) := by ring
    _ = conj (c m) * c n *
        Complex.exp (Complex.I * ((omega n - omega m) * t)) := by
      rw [← Complex.exp_add]
      congr 2
      ring

/-- Exact finite mean-square decomposition into its diagonal term and the
difference of two phase-twisted Hilbert forms.  Unlike the pairwise norm bound,
this identity retains the cancellation needed by Montgomery--Vaughan. -/
theorem finiteExponentialMeanSquare_cast_eq_diagonal_add_hilbert
    {ι : Type*} [DecidableEq ι] {S : Finset ι} {c : ι → ℂ}
    {omega : ι → ℝ} {a b : ℝ}
    (homega : Set.InjOn omega (S : Set ι)) :
    ((∫ t in a..b, ‖finiteExponentialSum S c omega t‖ ^ 2 : ℝ) : ℂ) =
      (b - a) * (∑ n ∈ S, (‖c n‖ ^ 2 : ℂ)) -
        Complex.I *
          (hilbertForm S (phaseTwist c omega b) omega -
            hilbertForm S (phaseTwist c omega a) omega) := by
  rw [finiteExponentialMeanSquare_cast_eq]
  have hpair : ∀ m ∈ S, ∀ n ∈ S,
      conj (c m) * c n *
          (∫ t in a..b,
            Complex.exp (Complex.I * ((omega n - omega m) * t))) =
        if m = n then (b - a) * (‖c m‖ ^ 2 : ℂ)
        else -Complex.I *
          (conj (phaseTwist c omega b m) * phaseTwist c omega b n /
              (omega n - omega m) -
            conj (phaseTwist c omega a m) * phaseTwist c omega a n /
              (omega n - omega m)) := by
    intro m hm n hn
    by_cases hmn : m = n
    · subst n
      have hzero :
          (fun t : ℝ =>
            Complex.exp (Complex.I * ((omega m - omega m) * t))) =
            fun _ : ℝ => (1 : ℂ) := by
        funext t
        norm_num
      rw [if_pos rfl, hzero, intervalIntegral.integral_const]
      change (conj (c m) * c m) * ((b - a) • (1 : ℂ)) =
        ((b : ℂ) - a) * (‖c m‖ ^ 2 : ℂ)
      rw [Complex.real_smul, ofReal_sub]
      simp only [mul_one]
      rw [← ofReal_pow, ← Complex.normSq_eq_norm_sq,
        Complex.normSq_eq_conj_mul_self]
      ring
    · rw [if_neg hmn]
      have hfreq : omega n - omega m ≠ 0 := by
        rw [sub_ne_zero]
        intro heq
        exact hmn (homega hm hn heq.symm)
      have hfreqC : (omega n : ℂ) - omega m ≠ 0 := by
        rw [sub_ne_zero]
        exact ofReal_injective.ne (sub_ne_zero.mp hfreq)
      have hId : Complex.I * ((omega n : ℂ) - omega m) ≠ 0 :=
        mul_ne_zero Complex.I_ne_zero hfreqC
      have hfun :
          (fun t : ℝ => Complex.exp (Complex.I * ((omega n - omega m) * t))) =
            fun t : ℝ =>
              Complex.exp ((Complex.I * (omega n - omega m : ℂ)) * t) := by
        funext t
        congr 1
        ring
      rw [hfun, integral_exp_mul_complex hId,
        conj_phaseTwist_mul_phaseTwist, conj_phaseTwist_mul_phaseTwist]
      field_simp [Complex.I_ne_zero, hfreqC]
      rw [Complex.I_sq]
      ring
  calc
    (∑ m ∈ S, ∑ n ∈ S,
        conj (c m) * c n *
          (∫ t in a..b,
            Complex.exp (Complex.I * ((omega n - omega m) * t)))) =
        ∑ m ∈ S, ∑ n ∈ S,
          if m = n then (b - a) * (‖c m‖ ^ 2 : ℂ)
          else -Complex.I *
            (conj (phaseTwist c omega b m) * phaseTwist c omega b n /
                (omega n - omega m) -
              conj (phaseTwist c omega a m) * phaseTwist c omega a n /
                (omega n - omega m)) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      exact hpair m hm n hn
    _ = (b - a) * (∑ n ∈ S, (‖c n‖ ^ 2 : ℂ)) -
        Complex.I *
          (hilbertForm S (phaseTwist c omega b) omega -
            hilbertForm S (phaseTwist c omega a) omega) := by
      have hsplit :
          (∑ m ∈ S, ∑ n ∈ S,
            if m = n then (b - a) * (‖c m‖ ^ 2 : ℂ)
            else -Complex.I *
              (conj (phaseTwist c omega b m) * phaseTwist c omega b n /
                  (omega n - omega m) -
                conj (phaseTwist c omega a m) * phaseTwist c omega a n /
                  (omega n - omega m))) =
            (∑ m ∈ S, ∑ n ∈ S,
              if m = n then (b - a) * (‖c m‖ ^ 2 : ℂ) else 0) +
            (∑ m ∈ S, ∑ n ∈ S,
              if m = n then 0 else -Complex.I *
                (conj (phaseTwist c omega b m) * phaseTwist c omega b n /
                    (omega n - omega m) -
                  conj (phaseTwist c omega a m) * phaseTwist c omega a n /
                    (omega n - omega m))) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro m hm
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro n hn
        by_cases hmn : m = n <;> simp [hmn]
      have hdiag :
          (∑ m ∈ S, ∑ n ∈ S,
            if m = n then (b - a) * (‖c m‖ ^ 2 : ℂ) else 0) =
            (b - a) * (∑ n ∈ S, (‖c n‖ ^ 2 : ℂ)) := by
        calc
          (∑ m ∈ S, ∑ n ∈ S,
              if m = n then (b - a) * (‖c m‖ ^ 2 : ℂ) else 0) =
              ∑ m ∈ S, (b - a) * (‖c m‖ ^ 2 : ℂ) := by
            apply Finset.sum_congr rfl
            intro m hm
            simp [hm]
          _ = (b - a) * (∑ n ∈ S, (‖c n‖ ^ 2 : ℂ)) := by
            rw [Finset.mul_sum]
      have hoff :
          (∑ m ∈ S, ∑ n ∈ S,
            if m = n then 0 else -Complex.I *
              (conj (phaseTwist c omega b m) * phaseTwist c omega b n /
                  (omega n - omega m) -
                conj (phaseTwist c omega a m) * phaseTwist c omega a n /
                  (omega n - omega m))) =
            -Complex.I *
              (hilbertForm S (phaseTwist c omega b) omega -
                hilbertForm S (phaseTwist c omega a) omega) := by
        simp only [hilbertForm]
        rw [mul_sub, Finset.mul_sum, Finset.mul_sum,
          ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro m hm
        rw [Finset.mul_sum, Finset.mul_sum,
          ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro n hn
        by_cases hmn : m = n <;> simp [hmn]
        ring
      rw [hsplit, hdiag, hoff]
      ring

/-- Transfer a weighted Hilbert-form bound to a diagonal mean-square bound.
The hypothesis is purely finite-dimensional; all interval integration and phase
bookkeeping are discharged by this theorem. -/
theorem finiteExponentialSum_meanSquare_le_of_hilbert
    {ι : Type*} [DecidableEq ι] {S : Finset ι} {c : ι → ℂ}
    {omega weight : ι → ℝ} {a b C : ℝ}
    (hab : a ≤ b) (homega : Set.InjOn omega (S : Set ι))
    (hweight : ∀ n ∈ S, 0 ≤ weight n)
    (hHilbert : ∀ d : ι → ℂ,
      ‖hilbertForm S d omega‖ ≤
        C * ∑ n ∈ S, weight n * ‖d n‖ ^ 2) :
    ∫ t in a..b, ‖finiteExponentialSum S c omega t‖ ^ 2 ≤
      (b - a) * ∑ n ∈ S, ‖c n‖ ^ 2 +
        2 * C * ∑ n ∈ S, weight n * ‖c n‖ ^ 2 := by
  let L : ℝ := ∫ t in a..b, ‖finiteExponentialSum S c omega t‖ ^ 2
  let D : ℝ := ∑ n ∈ S, ‖c n‖ ^ 2
  let W : ℝ := ∑ n ∈ S, weight n * ‖c n‖ ^ 2
  have hL : 0 ≤ L := by
    dsimp [L]
    exact intervalIntegral.integral_nonneg hab (fun t _ => sq_nonneg _)
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hW : 0 ≤ W := by
    dsimp [W]
    exact Finset.sum_nonneg fun n hn =>
      mul_nonneg (hweight n hn) (sq_nonneg _)
  have hphase (t : ℝ) :
      (∑ n ∈ S, weight n * ‖phaseTwist c omega t n‖ ^ 2) = W := by
    dsimp [W]
    apply Finset.sum_congr rfl
    intro n hn
    simp [phaseTwist, Complex.norm_exp]
  have hHb := hHilbert (phaseTwist c omega b)
  have hHa := hHilbert (phaseTwist c omega a)
  rw [hphase] at hHb hHa
  have heq :=
    finiteExponentialMeanSquare_cast_eq_diagonal_add_hilbert
      (S := S) (c := c) (omega := omega) (a := a) (b := b) homega
  have hsumcast :
      (∑ n ∈ S, (‖c n‖ ^ 2 : ℂ)) = (D : ℂ) := by
    dsimp [D]
    push_cast
    rfl
  have hdiagNorm :
      ‖((b : ℂ) - a) * (∑ n ∈ S, (‖c n‖ ^ 2 : ℂ))‖ =
        (b - a) * D := by
    have hbaNorm : ‖(b : ℂ) - a‖ = b - a := by
      rw [← ofReal_sub]
      exact Complex.norm_of_nonneg (sub_nonneg.mpr hab)
    have hDNorm : ‖(D : ℂ)‖ = D := by
      exact Complex.norm_of_nonneg hD
    rw [hsumcast, norm_mul, hbaNorm, hDNorm]
  have hnormL : ‖(L : ℂ)‖ = L := by
    exact Complex.norm_of_nonneg hL
  have heqL :
      (L : ℂ) =
        ((b : ℂ) - a) * (∑ n ∈ S, (‖c n‖ ^ 2 : ℂ)) -
          Complex.I *
            (hilbertForm S (phaseTwist c omega b) omega -
              hilbertForm S (phaseTwist c omega a) omega) := by
    simpa only [L] using heq
  change L ≤ (b - a) * D + 2 * C * W
  calc
    L = ‖(L : ℂ)‖ := hnormL.symm
    _ = ‖((b : ℂ) - a) * (∑ n ∈ S, (‖c n‖ ^ 2 : ℂ)) -
          Complex.I *
            (hilbertForm S (phaseTwist c omega b) omega -
              hilbertForm S (phaseTwist c omega a) omega)‖ := by
      apply congrArg norm
      exact heqL
    _ ≤ ‖((b : ℂ) - a) * (∑ n ∈ S, (‖c n‖ ^ 2 : ℂ))‖ +
          ‖Complex.I *
            (hilbertForm S (phaseTwist c omega b) omega -
              hilbertForm S (phaseTwist c omega a) omega)‖ :=
      norm_sub_le _ _
    _ = (b - a) * D +
          ‖hilbertForm S (phaseTwist c omega b) omega -
            hilbertForm S (phaseTwist c omega a) omega‖ := by
      rw [hdiagNorm, norm_mul, norm_I, one_mul]
    _ ≤ (b - a) * D +
          (‖hilbertForm S (phaseTwist c omega b) omega‖ +
            ‖hilbertForm S (phaseTwist c omega a) omega‖) :=
      add_le_add (le_refl _) (norm_sub_le _ _)
    _ ≤ (b - a) * D + (C * W + C * W) :=
      add_le_add (le_refl _) (add_le_add hHb hHa)
    _ = (b - a) * D + 2 * C * W := by ring

/-- Transfer two-sided positive-kernel certificates directly to a finite
exponential-sum mean-square bound.  This is the interface used by the Fourier
proof of the weighted Hilbert--Montgomery--Vaughan inequality. -/
theorem finiteExponentialSum_meanSquare_le_of_two_sided_certificate
    {ι : Type*} [DecidableEq ι] {S : Finset ι} {c : ι → ℂ}
    {omega weight : ι → ℝ} {a b C : ℝ}
    (hab : a ≤ b) (homega : Set.InjOn omega (S : Set ι))
    (hweight : ∀ n ∈ S, 0 ≤ weight n)
    (hplus : ∀ d : ι → ℂ,
      0 ≤ (((C * ∑ n ∈ S, weight n * ‖d n‖ ^ 2 : ℝ) : ℂ) +
        Complex.I * hilbertForm S d omega).re)
    (hminus : ∀ d : ι → ℂ,
      0 ≤ (((C * ∑ n ∈ S, weight n * ‖d n‖ ^ 2 : ℝ) : ℂ) -
        Complex.I * hilbertForm S d omega).re) :
    ∫ t in a..b, ‖finiteExponentialSum S c omega t‖ ^ 2 ≤
      (b - a) * ∑ n ∈ S, ‖c n‖ ^ 2 +
        2 * C * ∑ n ∈ S, weight n * ‖c n‖ ^ 2 := by
  apply finiteExponentialSum_meanSquare_le_of_hilbert
    hab homega hweight
  intro d
  exact norm_hilbertForm_le_of_two_sided_re_nonneg
    (hplus d) (hminus d)

/-- A finite-frequency Montgomery--Vaughan type mean-square bound.  The
diagonal contributes the interval length, while each pair of distinct
frequencies contributes the reciprocal-frequency kernel. -/
theorem finiteExponentialSum_meanSquare_le {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {c : ι → ℂ} {omega : ι → ℝ} {a b : ℝ}
    (hab : a ≤ b) (homega : Set.InjOn omega (S : Set ι)) :
    ∫ t in a..b, ‖finiteExponentialSum S c omega t‖ ^ 2 ≤
      ∑ m ∈ S, ∑ n ∈ S,
        ‖c m‖ * ‖c n‖ *
          if m = n then b - a else 2 / |omega n - omega m| := by
  let L : ℝ := ∫ t in a..b, ‖finiteExponentialSum S c omega t‖ ^ 2
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact intervalIntegral.integral_nonneg hab (fun t _ => sq_nonneg _)
  have hcast := finiteExponentialMeanSquare_cast_eq S c omega a b
  have hnormL : ‖(L : ℂ)‖ = L := by
    simp [abs_of_nonneg hL_nonneg]
  calc
    (∫ t in a..b, ‖finiteExponentialSum S c omega t‖ ^ 2) = L := rfl
    _ = ‖(L : ℂ)‖ := hnormL.symm
    _ = ‖∑ m ∈ S, ∑ n ∈ S,
          conj (c m) * c n *
            (∫ t in a..b,
              Complex.exp (Complex.I * ((omega n - omega m) * t)))‖ :=
      congrArg norm hcast
    _ ≤ ∑ m ∈ S, ‖∑ n ∈ S,
          conj (c m) * c n *
            (∫ t in a..b,
              Complex.exp (Complex.I * ((omega n - omega m) * t)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ m ∈ S, ∑ n ∈ S,
          ‖conj (c m) * c n *
            (∫ t in a..b,
              Complex.exp (Complex.I * ((omega n - omega m) * t)))‖ := by
      apply Finset.sum_le_sum
      intro m hm
      exact norm_sum_le _ _
    _ ≤ ∑ m ∈ S, ∑ n ∈ S,
          ‖c m‖ * ‖c n‖ *
            if m = n then b - a else 2 / |omega n - omega m| := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro n hn
      by_cases hmn : m = n
      · subst n
        simp only [sub_self, zero_mul, intervalIntegral.integral_const,
          if_pos, norm_mul, norm_conj]
        rw [norm_smul]
        simp [abs_of_nonneg (sub_nonneg.mpr hab)]
      · rw [if_neg hmn, norm_mul, norm_mul, norm_conj]
        have hfreq : omega n - omega m ≠ 0 := by
          rw [sub_ne_zero]
          intro heq
          exact hmn (homega hm hn heq.symm)
        apply mul_le_mul_of_nonneg_left _
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        simpa only [ofReal_sub, ofReal_mul] using
          (norm_integral_exp_I_mul_le_two_div
            (a := a) (b := b) (d := omega n - omega m) hfreq)

/-- Reciprocal separation of the logarithmic frequencies.  This is the
elementary arithmetic input that turns the local gap weight in the weighted
Hilbert inequality into Ramaré's `(n + 1)` weight. -/
theorem inv_abs_log_sub_log_le_nat_add_one {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    1 / |Real.log m - Real.log n| ≤ (n : ℝ) + 1 := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1R : 0 < (n : ℝ) + 1 := by positivity
  have hlogne : Real.log (m : ℝ) - Real.log (n : ℝ) ≠ 0 := by
    rw [sub_ne_zero]
    intro hlog
    have hmnR : (m : ℝ) = (n : ℝ) :=
      Real.log_injOn_pos hmR hnR hlog
    exact hmn (Nat.cast_injective hmnR)
  have habspos : 0 < |Real.log (m : ℝ) - Real.log (n : ℝ)| :=
    abs_pos.mpr hlogne
  have hgap :
      1 / ((n : ℝ) + 1) ≤
        |Real.log (m : ℝ) - Real.log (n : ℝ)| := by
    rcases lt_or_gt_of_ne hmn with hmn_lt | hnm_lt
    · have hmnR : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn_lt
      have hm1nR : (m : ℝ) + 1 ≤ n := by
        exact_mod_cast (Nat.succ_le_iff.mpr hmn_lt)
      have hfrac :
          1 / ((n : ℝ) + 1) ≤ 1 - (m : ℝ) / n := by
        field_simp
        nlinarith
      have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hnR hmR)
      rw [inv_div, Real.log_div hnR.ne' hmR.ne'] at hlog
      rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_lt_log hmR hmnR).le)]
      linarith
    · have hnmR : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm_lt
      have hn1mR : (n : ℝ) + 1 ≤ m := by
        exact_mod_cast (Nat.succ_le_iff.mpr hnm_lt)
      have hfrac :
          1 / ((n : ℝ) + 1) ≤ 1 - (n : ℝ) / m := by
        field_simp
        nlinarith [show 1 ≤ (n : ℝ) by exact_mod_cast hn]
      have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hmR hnR)
      rw [inv_div, Real.log_div hmR.ne' hnR.ne'] at hlog
      rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_lt_log hnR hnmR).le)]
      linarith
  apply (div_le_iff₀ habspos).2
  have := (div_le_iff₀ hn1R).1 hgap
  nlinarith

/-- The finite-frequency mean-square bound specialized to the frequencies
`-log n` of a Dirichlet polynomial. -/
theorem finiteDirichletPolynomial_meanSquare_le
    {S : Finset ℕ} {c : ℕ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hpos : ∀ n ∈ S, 0 < n) :
    ∫ t in a..b, ‖finiteDirichletPolynomial S c t‖ ^ 2 ≤
      ∑ m ∈ S, ∑ n ∈ S,
        ‖c m‖ * ‖c n‖ *
          if m = n then b - a
          else 2 / |Real.log n - Real.log m| := by
  have hlog : Set.InjOn (fun n : ℕ => -Real.log n) (S : Set ℕ) := by
    intro m hm n hn hmn
    have hmpos : 0 < (m : ℝ) := by exact_mod_cast hpos m hm
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hpos n hn
    have hlogs : Real.log (m : ℝ) = Real.log (n : ℝ) := neg_injective hmn
    exact_mod_cast Real.log_injOn_pos hmpos hnpos hlogs
  simpa only [finiteDirichletPolynomial, neg_sub_neg, abs_sub_comm] using
    (finiteExponentialSum_meanSquare_le
      (S := S) (c := c) (omega := fun n : ℕ => -Real.log n) hab hlog)

end DirichletPolynomial
end PrimeNumberTheorem
