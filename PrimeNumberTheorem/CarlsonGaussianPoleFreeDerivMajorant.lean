import PrimeNumberTheorem.CarlsonGaussianHilbertMemLp

/-!
# An integrable majorant for local Carlson Gaussian derivatives

This file packages the real-variable majorant used by the dominated-convergence
step in the `L²(ℝ)`-valued Carlson argument.  The exponent `20` matches the
available polynomial square-growth bound for the pole-free mollified-error
derivative.  No analytic number theory estimate is asserted here.
-/

open MeasureTheory

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- A degree-20 polynomial times a Gaussian of half the original decay rate.
The shift `zIm - w` is the one occurring in a Carlson vertical section. -/
noncomputable def carlsonGaussianDerivativeMajorant
    (Delta w zIm K t : ℝ) : ℝ :=
  K * (1 + |zIm + t - w|) ^ 20 *
    Real.exp (-(1 / (2 * Delta ^ 2)) * (zIm + t - w) ^ 2)

/-- The local Carlson derivative majorant is integrable whenever the Gaussian
width is nonzero. -/
theorem integrable_carlsonGaussianDerivativeMajorant
    {Delta w zIm : ℝ} (hDelta : 0 < Delta) (K : ℝ) :
    Integrable (carlsonGaussianDerivativeMajorant Delta w zIm K) volume := by
  have hb : 0 < 1 / (2 * Delta ^ 2) := by positivity
  have hbase :
      Integrable (fun t : ℝ =>
        (1 + |t|) ^ 20 * Real.exp (-(1 / (2 * Delta ^ 2)) * t ^ 2)) :=
    integrable_one_add_abs_pow_mul_exp_neg_mul_sq hb 20
  have hshift := Integrable.comp_sub_right hbase (w - zIm)
  have hK := hshift.const_mul K
  convert hK using 1
  funext t
  unfold carlsonGaussianDerivativeMajorant
  have ht : t - (w - zIm) = zIm + t - w := by ring
  rw [ht]
  ring

end CarlsonZeroDensity
end PrimeNumberTheorem
