import PrimeNumberTheorem.CarlsonGaussianPoleFreeDerivMajorantBound

open Complex Set

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

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

end CarlsonZeroDensity
end PrimeNumberTheorem
