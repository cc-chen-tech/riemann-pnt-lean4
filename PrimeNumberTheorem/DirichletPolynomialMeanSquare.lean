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
