import HardyTheorem.SelbergMollifiedTripleConstant
import MathlibAux.SlidingExponentialPolynomialMeanSquare

open Complex MeasureTheory
open scoped BigOperators

namespace HardyTheorem

/-!
# Mean-square reduction for the ratio-frequency Selberg polynomial

This file removes the exact zero-frequency coefficient from
`P_N M_X * conj(M_X)` and reduces the sliding-integral square mean of the
remaining finite polynomial to the standard diagonal-plus-gap sum.  It makes
no estimate for the collected arithmetic coefficients.
-/

/-- Every collected rational key is positive. -/
theorem selbergMollifiedTripleCollectedKey_pos_of_mem
    {N X : ℕ} {q : ℚ}
    (hq : q ∈ selbergMollifiedTripleCollectedSupport N X) :
    0 < q := by
  rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
  exact selbergMollifiedTripleKey_pos_of_mem hp

/-- Distinct collected rational keys have distinct logarithmic frequencies. -/
theorem selbergMollifiedTripleCollectedFrequency_injective_on_support
    {N X : ℕ} {q r : ℚ}
    (hq : q ∈ selbergMollifiedTripleCollectedSupport N X)
    (hr : r ∈ selbergMollifiedTripleCollectedSupport N X)
    (hqr : q ≠ r) :
    selbergMollifiedTripleCollectedFrequency q ≠
      selbergMollifiedTripleCollectedFrequency r := by
  intro hfreq
  have hqpos : (0 : ℝ) < (q : ℚ) := by
    exact_mod_cast selbergMollifiedTripleCollectedKey_pos_of_mem hq
  have hrpos : (0 : ℝ) < (r : ℚ) := by
    exact_mod_cast selbergMollifiedTripleCollectedKey_pos_of_mem hr
  have hcast : (q : ℝ) = (r : ℝ) :=
    Real.log_injOn_pos hqpos hrpos hfreq
  exact hqr (by exact_mod_cast hcast)

/-- Ratio one occurs whenever both finite polynomials contain their unit
term. -/
theorem one_mem_selbergMollifiedTripleCollectedSupport
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) :
    (1 : ℚ) ∈ selbergMollifiedTripleCollectedSupport N X := by
  apply Finset.mem_image.mpr
  refine ⟨(1, (1, 1)), ?_, ?_⟩
  · exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨le_rfl, hN⟩,
        Finset.mem_product.mpr
          ⟨Finset.mem_Icc.mpr ⟨le_rfl, hX⟩,
            Finset.mem_Icc.mpr ⟨le_rfl, hX⟩⟩⟩
  · norm_num [selbergMollifiedTripleKey]

/-- The nonzero rational frequencies after removing the exact main term. -/
noncomputable def selbergMollifiedTripleNonconstantSupport
    (N X : ℕ) : Finset ℚ :=
  (selbergMollifiedTripleCollectedSupport N X).erase 1

/-- The collected ratio-frequency polynomial with its zero-frequency main
coefficient removed. -/
noncomputable def selbergMollifiedTripleNonconstantPolynomial
    (N X : ℕ) (t : ℝ) : ℂ :=
  MathlibAux.exponentialPolynomial
    (selbergMollifiedTripleNonconstantSupport N X)
    (selbergMollifiedTripleCollectedCoeff N X)
    selbergMollifiedTripleCollectedFrequency t

/-- Subtracting the collected coefficient at ratio one is exactly the
polynomial over the erased support. -/
theorem selbergMollifiedTripleCollectedPolynomial_sub_constant_eq
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) (t : ℝ) :
    selbergMollifiedTripleCollectedPolynomial N X t -
        selbergMollifiedTripleCollectedCoeff N X 1 =
      selbergMollifiedTripleNonconstantPolynomial N X t := by
  classical
  unfold selbergMollifiedTripleCollectedPolynomial
    selbergMollifiedTripleNonconstantPolynomial
    selbergMollifiedTripleNonconstantSupport
    MathlibAux.exponentialPolynomial
  have hone := one_mem_selbergMollifiedTripleCollectedSupport hN hX
  rw [← Finset.sum_erase_add _ _ hone]
  simp [selbergMollifiedTripleCollectedFrequency]

/-- The short integral of the nonconstant ratio-frequency polynomial. -/
noncomputable def selbergMollifiedTripleNonconstantShortIntegral
    (H : ℝ) (N X : ℕ) (t : ℝ) : ℂ :=
  ∫ u in t..t + H,
    (selbergMollifiedTripleCollectedPolynomial N X u -
      selbergMollifiedTripleCollectedCoeff N X 1)

/-- The ratio-frequency short error is exactly the standard sliding integral
of the collected nonconstant exponential polynomial. -/
theorem selbergMollifiedTripleNonconstantShortIntegral_eq_sliding
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) (H t : ℝ) :
    selbergMollifiedTripleNonconstantShortIntegral H N X t =
      MathlibAux.slidingExponentialPolynomialIntegral
        (selbergMollifiedTripleNonconstantSupport N X)
        (selbergMollifiedTripleCollectedCoeff N X)
        selbergMollifiedTripleCollectedFrequency H t := by
  unfold selbergMollifiedTripleNonconstantShortIntegral
  apply intervalIntegral.integral_congr
  intro u _hu
  change selbergMollifiedTripleCollectedPolynomial N X u -
      selbergMollifiedTripleCollectedCoeff N X 1 = _
  rw [selbergMollifiedTripleCollectedPolynomial_sub_constant_eq hN hX]
  rfl

/-- The start-variable square mean of the nonconstant ratio-frequency short
integral is reduced to its exact finite diagonal-plus-gap sum. -/
theorem integral_normSq_selbergMollifiedTripleNonconstantShortIntegral_le
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) {A B H : ℝ} :
    (∫ t in A..B,
        Complex.normSq
          (selbergMollifiedTripleNonconstantShortIntegral H N X t)) ≤
      ∑ q ∈ selbergMollifiedTripleNonconstantSupport N X,
        ∑ r ∈ selbergMollifiedTripleNonconstantSupport N X,
          if q = r then
            (B - A) * Complex.normSq
              (MathlibAux.slidingExponentialCoefficient H
                (selbergMollifiedTripleCollectedCoeff N X)
                selbergMollifiedTripleCollectedFrequency r)
          else
            2 * ‖MathlibAux.slidingExponentialCoefficient H
                  (selbergMollifiedTripleCollectedCoeff N X)
                  selbergMollifiedTripleCollectedFrequency q‖ *
                ‖MathlibAux.slidingExponentialCoefficient H
                  (selbergMollifiedTripleCollectedCoeff N X)
                  selbergMollifiedTripleCollectedFrequency r‖ /
              |selbergMollifiedTripleCollectedFrequency q -
                selbergMollifiedTripleCollectedFrequency r| := by
  rw [show (fun t : ℝ => Complex.normSq
      (selbergMollifiedTripleNonconstantShortIntegral H N X t)) =
      fun t : ℝ => Complex.normSq
        (MathlibAux.slidingExponentialPolynomialIntegral
          (selbergMollifiedTripleNonconstantSupport N X)
          (selbergMollifiedTripleCollectedCoeff N X)
          selbergMollifiedTripleCollectedFrequency H t) by
    funext t
    rw [selbergMollifiedTripleNonconstantShortIntegral_eq_sliding hN hX]]
  apply MathlibAux.integral_normSq_slidingExponentialPolynomialIntegral_le
  intro q hq r hr hqr
  apply selbergMollifiedTripleCollectedFrequency_injective_on_support
  · exact Finset.mem_of_mem_erase hq
  · exact Finset.mem_of_mem_erase hr
  · exact hqr

end HardyTheorem
