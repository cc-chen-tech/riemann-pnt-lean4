import PrimeNumberTheorem.CarlsonGaussianHilbertSectionDeriv

open Complex

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example {Delta w : ℝ} {H : ℂ → ℂ} {z : ℂ} {t : ℝ}
    (hDelta : Delta ≠ 0)
    (hH : AnalyticAt ℂ H (z + I * (t : ℂ))) :
    HasDerivAt
      (fun u : ℂ => carlsonGaussianHilbertSection Delta w H u t)
      (carlsonGaussianHilbertSectionDeriv Delta w H z t) z :=
  hasDerivAt_carlsonGaussianHilbertSection hDelta hH

#print axioms hasDerivAt_carlsonGaussianHilbertSection

end CarlsonZeroDensity
end PrimeNumberTheorem
