import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import PrimeNumberTheorem.SecondOrderExplicitFormula

open MeasureTheory Set

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

/-- The next Perron kernel after `secondOrderExplicitFormulaIntegrand`.

The existing second-order integrand has denominator `s ^ 2`.  Dividing it once
more produces denominator `s ^ 3`; after integration in the vertical variable,
this is the first denominator order whose scalar tail has order `H ^ (-2)`.
-/
noncomputable def thirdOrderExplicitFormulaIntegrand (x : ℝ) (s : ℂ) : ℂ :=
  secondOrderExplicitFormulaIntegrand x s / s

lemma thirdOrderExplicitFormulaIntegrand_eq_explicitFormulaIntegrand_div_sq
    (x : ℝ) (s : ℂ) :
    thirdOrderExplicitFormulaIntegrand x s = explicitFormulaIntegrand x s / s ^ 2 := by
  simp only [thirdOrderExplicitFormulaIntegrand, secondOrderExplicitFormulaIntegrand]
  ring

lemma thirdOrderExplicitFormulaIntegrand_eq_neg_logDeriv_kernel
    (x : ℝ) (s : ℂ) :
    thirdOrderExplicitFormulaIntegrand x s =
      (x : ℂ) ^ s * (-deriv riemannZeta s / riemannZeta s) / s ^ 3 := by
  rw [thirdOrderExplicitFormulaIntegrand,
    secondOrderExplicitFormulaIntegrand_eq_neg_logDeriv_kernel]
  ring

/-- Dividing a regularized simple-pole term by `z ^ 2` changes its residue
coefficient from `r` to `r / p ^ 2`.  The other two displayed terms are poles
at the Perron origin and therefore belong to the real-axis correction package.
-/
lemma simplePoleTerm_div_sq_eq
    {z p r : ℂ} (hz : z ≠ 0) (hp : p ≠ 0) (hzp : z ≠ p) :
    ((z - p)⁻¹ * r) / z ^ 2 =
      (z - p)⁻¹ * (r / p ^ 2) - z⁻¹ * (r / p ^ 2) - (z ^ 2)⁻¹ * (r / p) := by
  field_simp [sub_ne_zero.mpr hzp, hz, hp]
  ring

/-- The scalar vertical tail attached to a cubic Perron denominator is exactly
`H ^ (-2) / 2`.  This is the analytic-order certificate behind an `H⁻²`
truncation target; it does not by itself prove a zeta contour-remainder bound.
-/
lemma integral_Ioi_rpow_neg_three (H : ℝ) (hH : 0 < H) :
    ∫ t : ℝ in Ioi H, t ^ (-3 : ℝ) = H ^ (-2 : ℝ) / 2 := by
  convert integral_Ioi_rpow_of_lt (a := (-3 : ℝ)) (by norm_num) hH using 1 <;>
    norm_num

/-- In ordinary powers, the same cubic-kernel tail is `1 / (2 * H ^ 2)`.
-/
lemma integral_Ioi_rpow_neg_three_eq_inv_sq (H : ℝ) (hH : 0 < H) :
    ∫ t : ℝ in Ioi H, t ^ (-3 : ℝ) = 1 / (2 * H ^ 2) := by
  rw [integral_Ioi_rpow_neg_three H hH]
  rw [Real.rpow_neg hH.le]
  field_simp [hH.ne']
  exact (Real.rpow_natCast H 2).symm

end ExplicitFormulaResidues
end PrimeNumberTheorem
