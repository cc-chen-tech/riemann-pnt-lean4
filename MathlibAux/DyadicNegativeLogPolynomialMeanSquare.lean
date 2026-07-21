import MathlibAux.DyadicPartition
import MathlibAux.FiberwiseNormSq
import MathlibAux.LogDirichletPolynomialMeanSquare

open Complex MeasureTheory Set
open scoped BigOperators

namespace MathlibAux

/-!
# Dyadic mean square for negative logarithmic frequencies

Each finite polynomial with frequencies `-log n` is split into its dyadic index
blocks.  Finite Cauchy--Schwarz costs only the number of blocks, while the
existing logarithmic Hilbert estimate charges each block according to its own
scale `2^j`.  In particular, the endpoint loss is not the largest index times
the total coefficient energy.
-/

private theorem negLogExponentialPolynomial_eq_logExponentialPolynomial_neg
    (s : Finset ℕ) (coeff : ℕ → ℂ) (t : ℝ) :
    exponentialPolynomial s coeff (fun n ↦ -Real.log n) t =
      exponentialPolynomial s coeff (fun n ↦ Real.log n) (-t) := by
  simp only [exponentialPolynomial]
  apply Finset.sum_congr rfl
  intro n hn
  congr 2
  push_cast
  ring

/-- The logarithmic-frequency mean-square estimate on one dyadic block,
reflected to the negative frequencies used by Dirichlet polynomials on the
critical line. -/
theorem integral_normSq_negLogExponentialPolynomial_le_dyadicBlock
    {M : ℕ} (hM : 0 < M) (s : Finset ℕ) (coeff : ℕ → ℂ)
    (hlower : ∀ n ∈ s, M ≤ n) (hupper : ∀ n ∈ s, n ≤ 2 * M)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b,
        Complex.normSq
          (exponentialPolynomial s coeff (fun n ↦ -Real.log n) t)) ≤
      ((b - a) + 2 * ((5 * Real.pi + 3) * M)) *
        ∑ n ∈ s, Complex.normSq (coeff n) := by
  have hreflect :
      (∫ t in a..b,
          Complex.normSq
            (exponentialPolynomial s coeff (fun n ↦ -Real.log n) t)) =
        ∫ t in -b..-a,
          Complex.normSq
            (exponentialPolynomial s coeff (fun n ↦ Real.log n) t) := by
    calc
      (∫ t in a..b,
          Complex.normSq
            (exponentialPolynomial s coeff (fun n ↦ -Real.log n) t)) =
          ∫ t in a..b,
            Complex.normSq
              (exponentialPolynomial s coeff (fun n ↦ Real.log n) (-t)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact congrArg Complex.normSq
          (negLogExponentialPolynomial_eq_logExponentialPolynomial_neg
            s coeff t)
      _ = ∫ t in -b..-a,
          Complex.normSq
            (exponentialPolynomial s coeff (fun n ↦ Real.log n) t) :=
        intervalIntegral.integral_comp_neg
          (f := fun t : ℝ => Complex.normSq
            (exponentialPolynomial s coeff (fun n ↦ Real.log n) t))
          (a := a) (b := b)
  rw [hreflect]
  have hbound := integral_normSq_logExponentialPolynomial_le
    hM s coeff hlower hupper (a := -b) (b := -a) (by linarith)
  simpa only [neg_sub_neg] using hbound

/-- A negative-logarithmic exponential polynomial supported below `2^K` has
a dyadically weighted mean-square bound.  The factor `K` is the finite
Cauchy--Schwarz cost for recombining the blocks; each endpoint term retains
its own scale `2^j` and its own block energy. -/
theorem integral_normSq_negLogExponentialPolynomial_le_dyadic
    (s : Finset ℕ) (coeff : ℕ → ℂ) {K : ℕ}
    (hpositive : ∀ n ∈ s, n ≠ 0)
    (hbound : ∀ n ∈ s, n < 2 ^ K)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b,
        Complex.normSq
          (exponentialPolynomial s coeff (fun n ↦ -Real.log n) t)) ≤
      (K : ℝ) *
        ∑ j ∈ Finset.range K,
          ((b - a) +
              2 * ((5 * Real.pi + 3) * ((2 ^ j : ℕ) : ℝ))) *
            ∑ n ∈ dyadicBlock s j, Complex.normSq (coeff n) := by
  let blockPolynomial : ℕ → ℝ → ℂ := fun j t =>
    exponentialPolynomial (dyadicBlock s j) coeff
      (fun n ↦ -Real.log n) t
  have hdecomp (t : ℝ) :
      exponentialPolynomial s coeff (fun n ↦ -Real.log n) t =
        ∑ j ∈ Finset.range K, blockPolynomial j t := by
    dsimp only [blockPolynomial, exponentialPolynomial]
    convert (sum_dyadicBlocks s K
      (fun n ↦ coeff n * Complex.exp (I * (-Real.log n * t)))
      hpositive hbound).symm using 1 <;> push_cast <;> rfl
  have hpoint (t : ℝ) :
      Complex.normSq
          (exponentialPolynomial s coeff (fun n ↦ -Real.log n) t) ≤
        (K : ℝ) *
          ∑ j ∈ Finset.range K, Complex.normSq (blockPolynomial j t) := by
    rw [hdecomp]
    simpa using normSq_finset_sum_le_card_mul_sum_normSq
      (Finset.range K) (fun j ↦ blockPolynomial j t)
  have hleftInt : IntervalIntegrable
      (fun t : ℝ => Complex.normSq
        (exponentialPolynomial s coeff (fun n ↦ -Real.log n) t))
      volume a b := by
    apply Continuous.intervalIntegrable
    unfold exponentialPolynomial
    fun_prop
  have hrightInt : IntervalIntegrable
      (fun t : ℝ => (K : ℝ) *
        ∑ j ∈ Finset.range K, Complex.normSq (blockPolynomial j t))
      volume a b := by
    apply Continuous.intervalIntegrable
    dsimp only [blockPolynomial, exponentialPolynomial]
    fun_prop
  calc
    (∫ t in a..b,
        Complex.normSq
          (exponentialPolynomial s coeff (fun n ↦ -Real.log n) t)) ≤
        ∫ t in a..b, (K : ℝ) *
          ∑ j ∈ Finset.range K, Complex.normSq (blockPolynomial j t) :=
      intervalIntegral.integral_mono_on hab hleftInt hrightInt
        (fun t _ht ↦ hpoint t)
    _ = (K : ℝ) * ∑ j ∈ Finset.range K,
        ∫ t in a..b, Complex.normSq (blockPolynomial j t) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_finset_sum]
      intro j hj
      apply Continuous.intervalIntegrable
      dsimp only [blockPolynomial, exponentialPolynomial]
      fun_prop
    _ ≤ (K : ℝ) *
        ∑ j ∈ Finset.range K,
          ((b - a) +
              2 * ((5 * Real.pi + 3) * ((2 ^ j : ℕ) : ℝ))) *
            ∑ n ∈ dyadicBlock s j, Complex.normSq (coeff n) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro j hj
      apply integral_normSq_negLogExponentialPolynomial_le_dyadicBlock
        (show 0 < 2 ^ j by positivity)
      · intro n hn
        exact (mem_dyadicBlock.mp hn).2.1
      · intro n hn
        have hnlt : n < 2 ^ (j + 1) := (mem_dyadicBlock.mp hn).2.2
        rw [pow_succ] at hnlt
        omega
      · exact hab

end MathlibAux
