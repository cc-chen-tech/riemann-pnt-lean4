import HardyTheorem.SelbergSArithmeticDivisorExpansion
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Dirichlet

open scoped BigOperators ArithmeticFunction LSeries.notation ArithmeticFunction.zeta

namespace HardyTheorem

/-!
# Selberg S-arith: summability of the squarefree Euler coefficient

The squarefree coefficient occurring after expansion of
`prod_{p | r} (1 + 9/p)` is dominated, after one further division by `d`,
by the Dirichlet series of the nine-fold divisor function at `s = 2`.
-/

/-- The nine-fold divisor function, as a natural-valued arithmetic function. -/
noncomputable def selbergTauNineNat : ArithmeticFunction ℕ :=
  (ζ : ArithmeticFunction ℕ) ^ 9

private theorem zeta_pow_apply_prime (k : ℕ) {p : ℕ} (hp : p.Prime) :
    ((ζ : ArithmeticFunction ℕ) ^ k) p = k := by
  induction k with
  | zero => simp [hp.ne_one]
  | succ k ih =>
      rw [pow_succ, mul_comm, ← pow_one p,
        ArithmeticFunction.zeta_mul_apply,
        Nat.sum_divisors_prime_pow hp]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero,
        Nat.pow_zero, Nat.pow_one, zero_add, ih]
      rw [(ArithmeticFunction.isMultiplicative_zeta.pow).map_one]
      omega

/-- On a prime, the nine-fold divisor function has value nine. -/
theorem selbergTauNineNat_apply_prime {p : ℕ} (hp : p.Prime) :
    selbergTauNineNat p = 9 := by
  unfold selbergTauNineNat
  exact zeta_pow_apply_prime 9 hp

/-- On squarefree integers, the nine-fold divisor function is the product of
the local values nine. -/
theorem selbergTauNineNat_apply_of_squarefree {n : ℕ} (hn : Squarefree n) :
    selbergTauNineNat n = ∏ p ∈ n.primeFactors, 9 := by
  unfold selbergTauNineNat
  rw [← (ArithmeticFunction.isMultiplicative_zeta.pow).prod_primeFactors hn]
  apply Finset.prod_congr rfl
  intro p hp
  exact zeta_pow_apply_prime 9 (Nat.prime_of_mem_primeFactors hp)

/-- Exact comparison identity on the squarefree support. -/
theorem selbergNineCoeff_div_eq_tauNine_div_sq
    {n : ℕ} (hn : Squarefree n) :
    selbergNineSquarefreeDivisorCoeff n / (n : ℝ) =
      selbergTauNineNat n / (n : ℝ) ^ 2 := by
  classical
  rw [selbergNineSquarefreeDivisorCoeff_apply, if_pos hn,
    selbergTauNineNat_apply_of_squarefree hn]
  have hnprod : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) := by
    simpa using congrArg (fun m : ℕ => (m : ℝ))
      (Nat.prod_primeFactors_of_squarefree hn).symm
  rw [hnprod]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  push_cast
  ring

private theorem natCoe_arithmeticFunction_pow
    (f : ArithmeticFunction ℕ) (k : ℕ) :
    (↑(f ^ k) : ArithmeticFunction ℂ) =
      (↑f : ArithmeticFunction ℂ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, pow_succ, ArithmeticFunction.natCoe_mul, ih]

private theorem selbergTauNine_complex_eq :
    (↑selbergTauNineNat : ArithmeticFunction ℂ) =
      (ζ : ArithmeticFunction ℂ) ^ 9 := by
  exact natCoe_arithmeticFunction_pow ζ 9

private theorem summable_selbergTauNine_div_sq :
    Summable (fun n : ℕ => (selbergTauNineNat n : ℝ) / (n : ℝ) ^ 2) := by
  have hz : LSeriesSummable ↗(ζ : ArithmeticFunction ℂ) (2 : ℂ) :=
    ArithmeticFunction.LSeriesSummable_zeta_iff.mpr (by norm_num)
  have h2 := ArithmeticFunction.LSeriesSummable_mul hz hz
  have h3 := ArithmeticFunction.LSeriesSummable_mul h2 hz
  have h4 := ArithmeticFunction.LSeriesSummable_mul h3 hz
  have h5 := ArithmeticFunction.LSeriesSummable_mul h4 hz
  have h6 := ArithmeticFunction.LSeriesSummable_mul h5 hz
  have h7 := ArithmeticFunction.LSeriesSummable_mul h6 hz
  have h8 := ArithmeticFunction.LSeriesSummable_mul h7 hz
  have h9 := ArithmeticFunction.LSeriesSummable_mul h8 hz
  have hpow : LSeriesSummable
      ↗((ζ : ArithmeticFunction ℂ) ^ 9) (2 : ℂ) := by
    simpa [pow_succ] using h9
  have hnorm := hpow.norm
  refine hnorm.congr (fun n => ?_)
  rw [LSeries.norm_term_eq]
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, if_false]
    rw [← selbergTauNine_complex_eq]
    simp

/-- The reciprocal-weighted squarefree Euler coefficient is summable. -/
theorem summable_selbergNineSquarefreeDivisorCoeff_div :
    Summable (fun n : ℕ =>
      selbergNineSquarefreeDivisorCoeff n / (n : ℝ)) := by
  refine Summable.of_nonneg_of_le
    (fun n => div_nonneg (selbergNineSquarefreeDivisorCoeff_nonneg n)
      (Nat.cast_nonneg n)) (fun n => ?_) summable_selbergTauNine_div_sq
  by_cases hn : Squarefree n
  · rw [selbergNineCoeff_div_eq_tauNine_div_sq hn]
  · rw [selbergNineSquarefreeDivisorCoeff_apply, if_neg hn]
    have ht : 0 ≤ (selbergTauNineNat n : ℝ) := Nat.cast_nonneg _
    have hd : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
    simpa using div_nonneg ht hd

/-- Consequently all finite partial sums have one uniform constant. -/
theorem exists_selbergNineSquarefreeDivisorCoeff_partialSum_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : Finset ℕ,
      ∑ n ∈ s, selbergNineSquarefreeDivisorCoeff n / (n : ℝ) ≤ C := by
  let f : ℕ → ℝ := fun n =>
    selbergNineSquarefreeDivisorCoeff n / (n : ℝ)
  have hf : Summable f :=
    summable_selbergNineSquarefreeDivisorCoeff_div
  have hf0 (n : ℕ) : 0 ≤ f n :=
    div_nonneg (selbergNineSquarefreeDivisorCoeff_nonneg n)
      (Nat.cast_nonneg n)
  refine ⟨∑' n, f n, tsum_nonneg hf0, ?_⟩
  intro s
  exact hf.sum_le_tsum s (fun n _ => hf0 n)

end HardyTheorem
