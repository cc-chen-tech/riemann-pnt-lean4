import PrimeNumberTheorem.QPowerDetectorAlgebra

open Polynomial
open scoped BigOperators

namespace PrimeNumberTheorem
namespace PrimeSideDetector

noncomputable section

/-- Positive weighted coefficient mass of a real polynomial at `r`. -/
def polynomialPositiveMassAt (r : Real) (p : Polynomial Real) : Real :=
  ∑ k ∈ p.support, max (p.coeff k) 0 * r ^ k

/-- Negative weighted coefficient mass of a real polynomial at `r`. -/
def polynomialNegativeMassAt (r : Real) (p : Polynomial Real) : Real :=
  ∑ k ∈ p.support, max (-p.coeff k) 0 * r ^ k

/-- Weighted coefficient `L¹` mass of a real polynomial at `r`. -/
def polynomialWeightedL1At (r : Real) (p : Polynomial Real) : Real :=
  ∑ k ∈ p.support, |p.coeff k| * r ^ k

private theorem eq_max_sub_max_neg (x : Real) :
    x = max x 0 - max (-x) 0 := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
    simp
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [max_eq_right hx', max_eq_left (neg_nonneg.mpr hx')]
    ring

private theorem abs_eq_max_add_max_neg (x : Real) :
    |x| = max x 0 + max (-x) 0 := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
    simp
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [abs_of_nonpos hx', max_eq_right hx', max_eq_left (neg_nonneg.mpr hx')]
    ring

/-- Polynomial evaluation is positive weighted mass minus negative weighted
mass. -/
theorem polynomial_eval_eq_positive_sub_negative
    (r : Real) (p : Polynomial Real) :
    p.eval r = polynomialPositiveMassAt r p -
      polynomialNegativeMassAt r p := by
  rw [p.eval_eq_sum]
  unfold polynomialPositiveMassAt polynomialNegativeMassAt
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← sub_mul, ← eq_max_sub_max_neg]

private theorem polynomialWeightedL1At_eq_positive_add_negative
    (r : Real) (p : Polynomial Real) :
    polynomialWeightedL1At r p =
      polynomialPositiveMassAt r p + polynomialNegativeMassAt r p := by
  unfold polynomialWeightedL1At polynomialPositiveMassAt polynomialNegativeMassAt
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← add_mul, ← abs_eq_max_add_max_neg]

/-- At a nonnegative real zero, negative weighted mass is exactly half the
weighted coefficient `L¹` mass. -/
theorem polynomialNegativeMassAt_eq_half_weightedL1At
    {r : Real} {p : Polynomial Real} (_hr : 0 ≤ r) (hzero : p.eval r = 0) :
    polynomialNegativeMassAt r p = polynomialWeightedL1At r p / 2 := by
  have hbalance :
      polynomialPositiveMassAt r p = polynomialNegativeMassAt r p := by
    rw [polynomial_eval_eq_positive_sub_negative] at hzero
    linarith
  rw [polynomialWeightedL1At_eq_positive_add_negative, hbalance]
  ring

private theorem evalRealPolynomial_ofReal
    (p : Polynomial Real) (r : Real) :
    evalRealPolynomial p r = p.eval r := by
  rw [evalRealPolynomial, ← Polynomial.eval₂_eq_eval_map]
  change p.eval₂ Complex.ofRealHom (Complex.ofRealHom r) =
    Complex.ofRealHom (p.eval r)
  rw [Polynomial.eval₂_at_apply]

/-- The normalized q-power detector cancels the main node, so its negative
coefficient mass there is exactly half its weighted `L¹` mass. -/
theorem normalizedQPowerPolynomial_negativeMass_eq_half
    {q : Nat} {realNodes : Finset Real} {pairNodes : Finset Complex}
    {z0 : Complex} (hq : q ≠ 0) :
    polynomialNegativeMassAt ((q : Real)⁻¹)
        (normalizedQPowerPolynomial q realNodes pairNodes z0) =
      polynomialWeightedL1At ((q : Real)⁻¹)
        (normalizedQPowerPolynomial q realNodes pairNodes z0) / 2 := by
  apply polynomialNegativeMassAt_eq_half_weightedL1At
  · positivity
  · have hmain := normalizedQPowerPolynomial_eval_main
      (q := q) (realNodes := realNodes) (pairNodes := pairNodes)
      (z0 := z0) hq
    rw [← Complex.ofReal_inv] at hmain
    rw [evalRealPolynomial_ofReal] at hmain
    exact_mod_cast hmain

end

end PrimeSideDetector
end PrimeNumberTheorem
