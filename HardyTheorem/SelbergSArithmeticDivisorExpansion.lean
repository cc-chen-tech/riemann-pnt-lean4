import HardyTheorem.SelbergSArithmeticEulerWeight
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

open scoped BigOperators ArithmeticFunction

namespace HardyTheorem

/-!
# Selberg S-arith: squarefree divisor expansion

The majorant `prod_{p | r} (1 + 9/p)` is expanded exactly over divisors of
the radical of `r`.  Keeping the squarefree support explicit is what makes
the subsequent reciprocal series converge.
-/

noncomputable def selbergNineSquarefreeDivisorCoeff : ArithmeticFunction ℝ :=
  by
    classical
    exact
      ⟨fun n => if Squarefree n then
          ∏ p ∈ n.primeFactors, 9 * (p : ℝ)⁻¹
        else 0,
        by simp⟩

@[simp] theorem selbergNineSquarefreeDivisorCoeff_apply (n : ℕ) :
    selbergNineSquarefreeDivisorCoeff n =
      if Squarefree n then
        ∏ p ∈ n.primeFactors, 9 * (p : ℝ)⁻¹
      else 0 := by
  rfl

theorem selbergNineSquarefreeDivisorCoeff_nonneg (n : ℕ) :
    0 ≤ selbergNineSquarefreeDivisorCoeff n := by
  classical
  rw [selbergNineSquarefreeDivisorCoeff_apply]
  split_ifs
  · positivity
  · exact le_rfl

@[simp] theorem selbergNineSquarefreeDivisorCoeff_apply_one :
    selbergNineSquarefreeDivisorCoeff 1 = 1 := by
  simp [selbergNineSquarefreeDivisorCoeff]

theorem selbergNineSquarefreeDivisorCoeff_apply_prime
    {p : ℕ} (hp : p.Prime) :
    selbergNineSquarefreeDivisorCoeff p = 9 * (p : ℝ)⁻¹ := by
  simp [selbergNineSquarefreeDivisorCoeff, hp.squarefree, hp.primeFactors]

theorem selbergNineSquarefreeDivisorCoeff_isMultiplicative :
    selbergNineSquarefreeDivisorCoeff.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨selbergNineSquarefreeDivisorCoeff_apply_one, ?_⟩
  intro m n hm hn hcop
  classical
  rw [selbergNineSquarefreeDivisorCoeff_apply,
    selbergNineSquarefreeDivisorCoeff_apply,
    selbergNineSquarefreeDivisorCoeff_apply]
  simp only [Nat.squarefree_mul hcop]
  by_cases hmSq : Squarefree m
  · by_cases hnSq : Squarefree n
    · simp only [hmSq, hnSq, if_true]
      rw [Nat.primeFactors_mul hm hn,
        Finset.prod_union hcop.disjoint_primeFactors]
      simp
    · simp [hmSq, hnSq]
  · simp [hmSq]

private theorem squarefree_prod_primeFactors (r : ℕ) :
    Squarefree (∏ p ∈ r.primeFactors, p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime
    (fun p hp q hq hpq => ?_) (fun p hp => ?_)
  · change IsRelPrime p q
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes
      (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr hpq)
  · exact (Nat.prime_of_mem_primeFactors hp).squarefree

/-- Exact divisor expansion of the finite product majorizing the fourth
Euler weight. -/
theorem selbergNineProduct_eq_squarefreeDivisorSum (r : ℕ) :
    (∏ p ∈ r.primeFactors, (1 + 9 * (p : ℝ)⁻¹)) =
      ∑ d ∈ (∏ p ∈ r.primeFactors, p).divisors,
        selbergNineSquarefreeDivisorCoeff d := by
  let R : ℕ := ∏ p ∈ r.primeFactors, p
  have hR : Squarefree R := squarefree_prod_primeFactors r
  have h := selbergNineSquarefreeDivisorCoeff_isMultiplicative
    |>.prodPrimeFactors_one_add_of_squarefree hR
  have hprime : R.primeFactors = r.primeFactors := by
    dsimp [R]
    exact Nat.primeFactors_prod_primeFactors r
  calc
    (∏ p ∈ r.primeFactors, (1 + 9 * (p : ℝ)⁻¹)) =
        ∏ p ∈ r.primeFactors,
          (1 + selbergNineSquarefreeDivisorCoeff p) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [selbergNineSquarefreeDivisorCoeff_apply_prime
        (Nat.prime_of_mem_primeFactors hp)]
    _ = ∑ d ∈ R.divisors, selbergNineSquarefreeDivisorCoeff d := by
      rw [← hprime]
      exact h
    _ = ∑ d ∈ (∏ p ∈ r.primeFactors, p).divisors,
          selbergNineSquarefreeDivisorCoeff d := by
      rfl

end HardyTheorem
