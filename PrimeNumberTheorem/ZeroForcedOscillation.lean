import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Complex Set
open scoped ComplexConjugate Interval

namespace PrimeNumberTheorem.ZeroForcedOscillation

noncomputable section

/-- A finite complex exponential polynomial with coefficients and real
frequencies kept as independent data. -/
def exponentialPolynomial {ι : Type*} (S : Finset ι)
    (c : ι → ℂ) (ω : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ i ∈ S, c i * Complex.exp (Complex.I * (ω i * t))

/-- The ordered off-diagonal budget. Each unordered pair occurs twice. -/
def offDiagonalBound {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c : ι → ℂ) (ω : ι → ℝ) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ S.erase i,
    2 * ‖c i‖ * ‖c j‖ / |ω j - ω i|

/-- Multiplicity is an explicit natural-number factor in each coefficient;
the supporting finset records distinct frequencies, not analytic order. -/
def multiplicityWeightedExponentialPolynomial {ι : Type*} (S : Finset ι)
    (multiplicity : ι → ℕ) (c : ι → ℂ) (ω : ι → ℝ) (t : ℝ) : ℂ :=
  exponentialPolynomial S (fun i => (multiplicity i : ℂ) * c i) ω t

private lemma offDiagonal_integrand_eq
    (c d : ℂ) (u v t : ℝ) :
    conj (c * exp (I * (u * t))) * (d * exp (I * (v * t))) =
      conj c * d * exp ((I * (v - u)) * t) := by
  rw [map_mul, ← Complex.exp_conj]
  simp only [map_mul, conj_I, conj_ofReal, neg_mul]
  calc
    conj c * exp (-(I * (u * t))) * (d * exp (I * (v * t))) =
        conj c * d * (exp (-(I * (u * t))) * exp (I * (v * t))) := by ring
    _ = conj c * d * exp (-(I * (u * t)) + I * (v * t)) := by
      rw [exp_add]
    _ = conj c * d * exp ((I * (v - u)) * t) := by
      congr 2
      ring

/-- Exact integral of one ordered off-diagonal product. -/
theorem intervalIntegral_offDiagonal_eq
    (c d : ℂ) {u v a b : ℝ} (huv : u ≠ v) :
    (∫ t in a..b,
        conj (c * exp (I * (u * t))) * (d * exp (I * (v * t)))) =
      conj c * d *
        ((exp ((I * (v - u)) * b) - exp ((I * (v - u)) * a)) /
          (I * (v - u))) := by
  simp_rw [offDiagonal_integrand_eq]
  calc
    (∫ t in a..b, conj c * d * exp ((I * (v - u)) * t)) =
        conj c * d * (∫ t in a..b, exp ((I * (v - u)) * t)) := by
      exact intervalIntegral.integral_const_mul
        (a := a) (b := b) (conj c * d)
          (fun t : ℝ => exp ((I * (v - u)) * t))
    _ = conj c * d *
        ((exp ((I * (v - u)) * b) - exp ((I * (v - u)) * a)) /
          (I * (v - u))) := by
      rw [integral_exp_mul_complex]
      intro h
      have him := congrArg Complex.im h
      simp at him
      exact huv (by linarith)

/-- An ordered off-diagonal pair contributes at most
`2 * ‖c‖ * ‖d‖ / |v-u|`, independently of the interval length. -/
theorem norm_intervalIntegral_offDiagonal_le
    (c d : ℂ) {u v a b : ℝ} (huv : u ≠ v) :
    ‖∫ t in a..b,
        conj (c * exp (I * (u * t))) * (d * exp (I * (v * t)))‖ ≤
      2 * ‖c‖ * ‖d‖ / |v - u| := by
  rw [intervalIntegral_offDiagonal_eq c d huv]
  rw [norm_mul, norm_mul, norm_conj, norm_div]
  have hnum :
      ‖exp ((I * (v - u)) * b) - exp ((I * (v - u)) * a)‖ ≤ 2 := by
    calc
      ‖exp ((I * (v - u)) * b) - exp ((I * (v - u)) * a)‖ ≤
          ‖exp ((I * (v - u)) * b)‖ + ‖exp ((I * (v - u)) * a)‖ :=
        norm_sub_le _ _
      _ = 2 := by norm_num [norm_exp]
  have hden : ‖I * ((v : ℂ) - (u : ℂ))‖ = |v - u| := by
    calc
      ‖I * ((v : ℂ) - (u : ℂ))‖ =
          ‖I‖ * ‖(v : ℂ) - (u : ℂ)‖ := norm_mul _ _
      _ = ‖((v - u : ℝ) : ℂ)‖ := by simp
      _ = |v - u| := by rw [norm_real, Real.norm_eq_abs]
  rw [hden]
  have hpos : 0 < |v - u| := abs_pos.mpr (sub_ne_zero.mpr huv.symm)
  calc
    ‖c‖ * ‖d‖ *
          (‖exp ((I * (v - u)) * b) - exp ((I * (v - u)) * a)‖ / |v - u|) ≤
        ‖c‖ * ‖d‖ * (2 / |v - u|) := by
      gcongr
    _ = 2 * ‖c‖ * ‖d‖ / |v - u| := by ring

private lemma intervalIntegral_sqNorm_exponentialPolynomial_expansion
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c : ι → ℂ) (ω : ι → ℝ) {a b : ℝ} :
    (∫ t in a..b,
        conj (exponentialPolynomial S c ω t) *
          exponentialPolynomial S c ω t) =
      ((b - a) * ∑ i ∈ S, ‖c i‖ ^ 2 : ℝ) +
        ∑ i ∈ S, ∑ j ∈ S.erase i,
          ∫ t in a..b,
            conj (c i * exp (I * (ω i * t))) *
              (c j * exp (I * (ω j * t))) := by
  let q : ι → ℝ → ℂ := fun i t => c i * exp (I * (ω i * t))
  have hq (i : ι) : Continuous (q i) := by
    dsimp [q]
    fun_prop
  have hpair (i j : ι) :
      IntervalIntegrable (fun t => conj (q i t) * q j t) MeasureTheory.volume a b :=
    Continuous.intervalIntegrable (by fun_prop) a b
  have hdiag (i : ι) :
      (∫ t in a..b, conj (q i t) * q i t) =
        ((b - a) * ‖c i‖ ^ 2 : ℝ) := by
    calc
      (∫ t in a..b, conj (q i t) * q i t) =
          ∫ _t in a..b, ((‖c i‖ ^ 2 : ℝ) : ℂ) := by
        apply intervalIntegral.integral_congr
        intro t _ht
        dsimp [q]
        rw [offDiagonal_integrand_eq]
        simp [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
      _ = ((b - a) * ‖c i‖ ^ 2 : ℝ) := by
        simp only [intervalIntegral.integral_const]
        change (((b - a : ℝ) : ℂ) * ((‖c i‖ ^ 2 : ℝ) : ℂ)) = _
        norm_cast
  calc
    (∫ t in a..b,
        conj (exponentialPolynomial S c ω t) *
          exponentialPolynomial S c ω t) =
        ∫ t in a..b, ∑ i ∈ S, ∑ j ∈ S, conj (q i t) * q j t := by
      apply intervalIntegral.integral_congr
      intro t _ht
      simp only [exponentialPolynomial, q, map_sum]
      rw [Finset.sum_mul_sum]
    _ = ∑ i ∈ S, ∑ j ∈ S,
        ∫ t in a..b, conj (q i t) * q j t := by
      rw [intervalIntegral.integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [intervalIntegral.integral_finset_sum]
        intro j hj
        exact hpair i j
      · intro i hi
        exact Continuous.intervalIntegrable (by fun_prop) a b
    _ = ∑ i ∈ S,
        (((b - a) * ‖c i‖ ^ 2 : ℝ) +
          ∑ j ∈ S.erase i, ∫ t in a..b, conj (q i t) * q j t) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← hdiag i, ← Finset.sum_erase_add S _ hi, add_comm]
    _ = ((b - a) * ∑ i ∈ S, ‖c i‖ ^ 2 : ℝ) +
        ∑ i ∈ S, ∑ j ∈ S.erase i,
          ∫ t in a..b,
            conj (c i * exp (I * (ω i * t))) *
              (c j * exp (I * (ω j * t))) := by
      simp only [Finset.sum_add_distrib, q]
      push_cast
      rw [Finset.mul_sum]

/-- The finite exponential-polynomial mean square differs from its diagonal
mass by at most the explicit ordered off-diagonal budget. -/
theorem abs_intervalIntegral_sqNorm_exponentialPolynomial_sub_diagonal_le
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c : ι → ℂ) (ω : ι → ℝ) {a b : ℝ} (hω : Set.InjOn ω ↑S) :
    |(∫ t in a..b, ‖exponentialPolynomial S c ω t‖ ^ 2) -
        (b - a) * ∑ i ∈ S, ‖c i‖ ^ 2| ≤
      offDiagonalBound S c ω := by
  let R : ℝ :=
    (∫ t in a..b, ‖exponentialPolynomial S c ω t‖ ^ 2) -
      (b - a) * ∑ i ∈ S, ‖c i‖ ^ 2
  let E : ℂ := ∑ i ∈ S, ∑ j ∈ S.erase i,
    ∫ t in a..b,
      conj (c i * exp (I * (ω i * t))) *
        (c j * exp (I * (ω j * t)))
  have herror :
      (R : ℂ) = E := by
    have hexpansion :=
      intervalIntegral_sqNorm_exponentialPolynomial_expansion S c ω (a := a) (b := b)
    calc
      (R : ℂ) =
          (∫ t in a..b,
              ((‖exponentialPolynomial S c ω t‖ ^ 2 : ℝ) : ℂ)) -
            (((b - a) * ∑ i ∈ S, ‖c i‖ ^ 2 : ℝ) : ℂ) := by
        rw [intervalIntegral.integral_ofReal]
        simp only [R]
        push_cast
        rfl
      _ = (∫ t in a..b,
              conj (exponentialPolynomial S c ω t) *
                exponentialPolynomial S c ω t) -
            (((b - a) * ∑ i ∈ S, ‖c i‖ ^ 2 : ℝ) : ℂ) := by
        congr 1
        apply intervalIntegral.integral_congr
        intro t _ht
        dsimp
        rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
      _ = E := by
        rw [hexpansion]
        simp only [E]
        push_cast
        ring
  calc
    |(∫ t in a..b, ‖exponentialPolynomial S c ω t‖ ^ 2) -
        (b - a) * ∑ i ∈ S, ‖c i‖ ^ 2| = |R| := rfl
    _ = ‖(R : ℂ)‖ := by simp
    _ = ‖E‖ := congrArg norm herror
    _ ≤ ∑ i ∈ S, ‖∑ j ∈ S.erase i,
          ∫ t in a..b,
            conj (c i * exp (I * (ω i * t))) *
              (c j * exp (I * (ω j * t)))‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ i ∈ S, ∑ j ∈ S.erase i,
        ‖∫ t in a..b,
            conj (c i * exp (I * (ω i * t))) *
              (c j * exp (I * (ω j * t)))‖ := by
      gcongr with i hi
      exact norm_sum_le _ _
    _ ≤ offDiagonalBound S c ω := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact norm_intervalIntegral_offDiagonal_le (c i) (c j)
        (hω.ne hi (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj).symm)

/-- The aggregate mean-square estimate with analytic multiplicities retained
as explicit natural-number factors in the coefficients. -/
theorem
    abs_intervalIntegral_sqNorm_multiplicityWeightedExponentialPolynomial_sub_diagonal_le
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (multiplicity : ι → ℕ) (c : ι → ℂ) (ω : ι → ℝ)
    {a b : ℝ} (hω : Set.InjOn ω ↑S) :
    |(∫ t in a..b,
          ‖multiplicityWeightedExponentialPolynomial S multiplicity c ω t‖ ^ 2) -
        (b - a) * ∑ i ∈ S, ‖(multiplicity i : ℂ) * c i‖ ^ 2| ≤
      offDiagonalBound S (fun i => (multiplicity i : ℂ) * c i) ω := by
  simpa [multiplicityWeightedExponentialPolynomial] using
    abs_intervalIntegral_sqNorm_exponentialPolynomial_sub_diagonal_le
      S (fun i => (multiplicity i : ℂ) * c i) ω hω

/-- On every nondegenerate interval, some interior point reaches the diagonal
mass minus the explicit ordered off-diagonal budget per unit length. -/
theorem exists_mem_Ioo_sqNorm_exponentialPolynomial_ge
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c : ι → ℂ) (ω : ι → ℝ) {a b : ℝ} (hab : a < b)
    (hω : Set.InjOn ω ↑S) :
    ∃ t ∈ Set.Ioo a b,
      (∑ i ∈ S, ‖c i‖ ^ 2) - offDiagonalBound S c ω / (b - a) ≤
        ‖exponentialPolynomial S c ω t‖ ^ 2 := by
  let f : ℝ → ℝ := fun t => ‖exponentialPolynomial S c ω t‖ ^ 2
  let D : ℝ := ∑ i ∈ S, ‖c i‖ ^ 2
  let B : ℝ := offDiagonalBound S c ω
  let A : ℝ := D - B / (b - a)
  have hf : Continuous f := by
    dsimp [f, exponentialPolynomial]
    fun_prop
  have haggregate :=
    abs_intervalIntegral_sqNorm_exponentialPolynomial_sub_diagonal_le
      S c ω (a := a) (b := b) hω
  have hlower : (b - a) * D - B ≤ ∫ t in a..b, f t := by
    have hleft := (abs_le.mp haggregate).1
    dsimp [f, D, B] at hleft ⊢
    linarith
  have hlength : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  have hscale : (b - a) * A = (b - a) * D - B := by
    dsimp [A]
    field_simp
  by_contra! hnone
  have hdiff : IntervalIntegrable (fun t => A - f t) MeasureTheory.volume a b :=
    Continuous.intervalIntegrable (continuous_const.sub hf) a b
  have hpositive : 0 < ∫ t in a..b, A - f t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      hdiff (fun t ht => sub_pos.mpr (hnone t ht)) hab
  rw [intervalIntegral.integral_sub
      (Continuous.intervalIntegrable continuous_const a b)
      (Continuous.intervalIntegrable hf a b),
    intervalIntegral.integral_const] at hpositive
  change 0 < (b - a) * A - ∫ t in a..b, f t at hpositive
  rw [hscale] at hpositive
  linarith

end

end PrimeNumberTheorem.ZeroForcedOscillation
