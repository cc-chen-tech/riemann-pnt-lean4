import PrimeNumberTheorem.CarlsonGaussianPoleFreeDerivMajorantBound

open Complex Set

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example {Delta w rho : ℝ} {z : ℂ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    (hrho : 0 < rho) (hrhoSmall : rho ≤ 1 / 48)
    (hleft : 1 / 2 + 2 * rho ≤ z.re)
    (hright : z.re + 2 * rho ≤ 4) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v ∈ Metric.closedBall z rho, ∀ t : ℝ,
      ‖carlsonGaussianHilbertSectionDeriv Delta w
          (poleFreeTwoScaleMollifiedZetaError Y0 Y1) v t‖ ^ 2 ≤
        carlsonGaussianDerivativeMajorant Delta w z.im K t :=
  exists_carlsonGaussianDerivativeMajorant_bound_on_closedBall_of_radius
    hDelta hY0 hY01 hrho hrhoSmall hleft hright

example {Delta w : ℝ} {z : ℂ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    (hzre : z.re ∈ Icc (29 / 48 : ℝ) (187 / 48)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v ∈ Metric.closedBall z (1 / 48 : ℝ), ∀ t : ℝ,
      ‖carlsonGaussianHilbertSectionDeriv Delta w
          (poleFreeTwoScaleMollifiedZetaError Y0 Y1) v t‖ ^ 2 ≤
        carlsonGaussianDerivativeMajorant Delta w z.im K t :=
  exists_carlsonGaussianDerivativeMajorant_bound_on_closedBall
    hDelta hY0 hY01 hzre

#print axioms
  exists_carlsonGaussianDerivativeMajorant_bound_on_closedBall
#print axioms
  exists_carlsonGaussianDerivativeMajorant_bound_on_closedBall_of_radius

end CarlsonZeroDensity
end PrimeNumberTheorem
