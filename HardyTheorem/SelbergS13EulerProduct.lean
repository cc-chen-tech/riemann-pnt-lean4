import HardyTheorem.SelbergS13DivisorPair
import Mathlib.NumberTheory.EulerProduct.Basic

open scoped BigOperators
open Nat Finset

namespace HardyTheorem

/-!
# Selberg's S13 estimate: the supported reciprocal Euler product

For a finite prime set, the reciprocal sum over positive integers supported
on that set has the exact Euler product.  This file records the exact
`HasSum` statement and its finite-subsum consequence.
-/

/-- The completely multiplicative function `n ↦ 1 / n` on positive natural
numbers (with the harmless convention `0⁻¹ = 0`). -/
noncomputable def selbergNatReciprocalMonoidHom : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' m n := by simp [Nat.cast_mul, mul_comm]

@[simp] theorem selbergNatReciprocalMonoidHom_apply (n : ℕ) :
    selbergNatReciprocalMonoidHom n = (n : ℝ)⁻¹ :=
  rfl

private theorem norm_selbergNatReciprocalMonoidHom_prime_lt_one
    {p : ℕ} (hp : p.Prime) :
    ‖selbergNatReciprocalMonoidHom p‖ < 1 := by
  rw [selbergNatReciprocalMonoidHom_apply, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p))]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

/-- Exact Euler product for reciprocals of the positive integers supported
on the primes dividing `rho`. -/
theorem selbergS13ReciprocalHasSum (rho : ℕ) :
    HasSum
      (fun m : factoredNumbers rho.primeFactors => (m.1 : ℝ)⁻¹)
      (∏ p ∈ rho.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹) := by
  have h :=
    (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
      (f := selbergNatReciprocalMonoidHom)
      norm_selbergNatReciprocalMonoidHom_prime_lt_one rho.primeFactors).2
  simpa only [selbergNatReciprocalMonoidHom_apply,
    Finset.filter_eq_self.2 (fun p hp => Nat.prime_of_mem_primeFactors hp)] using h

/-- Every finite reciprocal sum over numbers supported on the primes of
`rho` is bounded by the corresponding full Euler product. -/
theorem selbergS13FiniteSupportedReciprocalSum_le_eulerProduct
    (rho : ℕ) (S : Finset (factoredNumbers rho.primeFactors)) :
    (∑ m ∈ S, (m.1 : ℝ)⁻¹) ≤
      ∏ p ∈ rho.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ := by
  have hsum := (selbergS13ReciprocalHasSum rho).summable
  calc
    (∑ m ∈ S, (m.1 : ℝ)⁻¹) ≤
        ∑' m : factoredNumbers rho.primeFactors, (m.1 : ℝ)⁻¹ := by
      exact hsum.sum_le_tsum S (fun m _hm => by positivity)
    _ = ∏ p ∈ rho.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ :=
      (selbergS13ReciprocalHasSum rho).tsum_eq

/-- The S13 pair mass after writing the grouped product as `D = rho * m`,
where every `m` in `S` is supported on the primes of `rho`. -/
noncomputable def selbergS13FiniteMultiplierPairMass
    (rho : ℕ) (S : Finset (factoredNumbers rho.primeFactors)) : ℝ :=
  ∑ m ∈ S,
    selbergS13RestrictedDivisorPairMass rho (rho * m.1) /
      ((rho * m.1 : ℕ) : ℝ)

/-- Finite, exact S13: after grouping by `D = rho * m`, the total restricted
coefficient mass is bounded by
`rho⁻¹ * ∏_{p | rho} (1 - p⁻¹)⁻¹`.

This theorem has no asymptotic hypothesis and is uniform in the finite set
of supported multipliers. -/
theorem selbergS13FiniteMultiplierPairMass_le_eulerProduct
    (rho : ℕ) (S : Finset (factoredNumbers rho.primeFactors)) :
    selbergS13FiniteMultiplierPairMass rho S ≤
      (rho : ℝ)⁻¹ *
        ∏ p ∈ rho.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ := by
  unfold selbergS13FiniteMultiplierPairMass
  calc
    (∑ m ∈ S,
        selbergS13RestrictedDivisorPairMass rho (rho * m.1) /
          ((rho * m.1 : ℕ) : ℝ)) ≤
        ∑ m ∈ S, (((rho * m.1 : ℕ) : ℝ))⁻¹ := by
      apply Finset.sum_le_sum
      intro m _hm
      have hdenom : 0 ≤ (((rho * m.1 : ℕ) : ℝ))⁻¹ := by positivity
      rw [div_eq_mul_inv]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right
          (selbergS13RestrictedDivisorPairMass_le_one rho (rho * m.1))
          hdenom
    _ = (rho : ℝ)⁻¹ * ∑ m ∈ S, (m.1 : ℝ)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _hm
      simp [Nat.cast_mul, mul_comm]
    _ ≤ (rho : ℝ)⁻¹ *
        ∏ p ∈ rho.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ := by
      exact mul_le_mul_of_nonneg_left
        (selbergS13FiniteSupportedReciprocalSum_le_eulerProduct rho S)
        (inv_nonneg.mpr (Nat.cast_nonneg rho))

end HardyTheorem
