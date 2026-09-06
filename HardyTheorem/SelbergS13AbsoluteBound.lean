import HardyTheorem.SelbergS13EulerProduct
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds

open scoped BigOperators
open Nat Finset

namespace HardyTheorem

/-!
# Selberg's S13 estimate: an absolute Euler-product constant

The ratio between Selberg's two finite Euler products is bounded by
`ζ(2) = π² / 6 < 2`.  Combining this with the preceding fixed-product
majorant gives a concrete constant-two form of (S13).
-/

/-- The completely multiplicative square-reciprocal function. -/
noncomputable def selbergNatReciprocalSqMonoidHom : ℕ →* ℝ where
  toFun n := ((n : ℝ) ^ 2)⁻¹
  map_one' := by simp
  map_mul' m n := by simp [Nat.cast_mul, mul_pow, mul_comm]

@[simp] theorem selbergNatReciprocalSqMonoidHom_apply (n : ℕ) :
    selbergNatReciprocalSqMonoidHom n = ((n : ℝ) ^ 2)⁻¹ :=
  rfl

private theorem norm_selbergNatReciprocalSqMonoidHom_prime_lt_one
    {p : ℕ} (hp : p.Prime) :
    ‖selbergNatReciprocalSqMonoidHom p‖ < 1 := by
  rw [selbergNatReciprocalSqMonoidHom_apply, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg (p : ℝ)))]
  exact inv_lt_one_of_one_lt₀ (by nlinarith [show (1 : ℝ) < p by exact_mod_cast hp.one_lt])

/-- The finite correction Euler product is bounded by `ζ(2)`. -/
theorem selbergS13CorrectionEulerProduct_le_zetaTwo (rho : ℕ) :
    (∏ p ∈ rho.primeFactors, (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹) ≤
      Real.pi ^ 2 / 6 := by
  have hEuler :=
    (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
      (f := selbergNatReciprocalSqMonoidHom)
      norm_selbergNatReciprocalSqMonoidHom_prime_lt_one rho.primeFactors).2
  have hEuler' :
      HasSum
        (fun m : factoredNumbers rho.primeFactors => ((m.1 : ℝ) ^ 2)⁻¹)
        (∏ p ∈ rho.primeFactors, (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹) := by
    simpa only [selbergNatReciprocalSqMonoidHom_apply,
      Finset.filter_eq_self.2 (fun p hp => Nat.prime_of_mem_primeFactors hp)] using hEuler
  calc
    (∏ p ∈ rho.primeFactors, (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹) =
        ∑' m : factoredNumbers rho.primeFactors, ((m.1 : ℝ) ^ 2)⁻¹ :=
      hEuler'.tsum_eq.symm
    _ ≤ ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹ := by
      exact Summable.tsum_subtype_le
        (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹)
        (factoredNumbers rho.primeFactors)
        (fun _ => by positivity)
        (by simpa only [one_div] using hasSum_zeta_two.summable)
    _ = Real.pi ^ 2 / 6 := by
      simpa only [one_div] using hasSum_zeta_two.tsum_eq

/-- Factor the `S13` Euler product into the desired `(1 + 1/p)` product
and a square-reciprocal correction product. -/
theorem selbergS13MinusEulerProduct_eq_plus_mul_correction (rho : ℕ) :
    (∏ p ∈ rho.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹) =
      (∏ p ∈ rho.primeFactors, (1 + (p : ℝ)⁻¹)) *
        ∏ p ∈ rho.primeFactors, (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹ := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _hp
  have hplus : 1 + (p : ℝ)⁻¹ ≠ 0 := by positivity
  have hfactor :
      1 - ((p : ℝ) ^ 2)⁻¹ =
        (1 - (p : ℝ)⁻¹) * (1 + (p : ℝ)⁻¹) := by
    rw [← inv_pow]
    ring
  rw [hfactor, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hplus, one_mul]

theorem selbergS13CorrectionEulerProduct_le_two (rho : ℕ) :
    (∏ p ∈ rho.primeFactors, (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹) ≤ 2 := by
  refine (selbergS13CorrectionEulerProduct_le_zetaTwo rho).trans ?_
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpipos : 0 < Real.pi := Real.pi_pos
  nlinarith

/-- Concrete absolute-constant form of the Euler-product comparison in S13. -/
theorem selbergS13MinusEulerProduct_le_two_mul_plus (rho : ℕ) :
    (∏ p ∈ rho.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹) ≤
      2 * ∏ p ∈ rho.primeFactors, (1 + (p : ℝ)⁻¹) := by
  rw [selbergS13MinusEulerProduct_eq_plus_mul_correction]
  have hplus : 0 ≤ ∏ p ∈ rho.primeFactors, (1 + (p : ℝ)⁻¹) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left
    (selbergS13CorrectionEulerProduct_le_two rho) hplus]

/-- Concrete constant-two finite S13 bound. -/
theorem selbergS13FiniteMultiplierPairMass_le_two_mul_plus
    (rho : ℕ) (S : Finset (factoredNumbers rho.primeFactors)) :
    selbergS13FiniteMultiplierPairMass rho S ≤
      2 * (rho : ℝ)⁻¹ *
        ∏ p ∈ rho.primeFactors, (1 + (p : ℝ)⁻¹) := by
  calc
    selbergS13FiniteMultiplierPairMass rho S ≤
        (rho : ℝ)⁻¹ *
          ∏ p ∈ rho.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ :=
      selbergS13FiniteMultiplierPairMass_le_eulerProduct rho S
    _ ≤ (rho : ℝ)⁻¹ *
        (2 * ∏ p ∈ rho.primeFactors, (1 + (p : ℝ)⁻¹)) := by
      exact mul_le_mul_of_nonneg_left
        (selbergS13MinusEulerProduct_le_two_mul_plus rho)
        (inv_nonneg.mpr (Nat.cast_nonneg rho))
    _ = 2 * (rho : ℝ)⁻¹ *
        ∏ p ∈ rho.primeFactors, (1 + (p : ℝ)⁻¹) := by ring

end HardyTheorem
