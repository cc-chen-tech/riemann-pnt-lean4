import PrimeNumberTheorem.VKEdgePiOverTwoGaussianTail

open MeasureTheory

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

#check gaussianTail
#check normalizedGaussian_le_doubled_scaledGaussian

example {m : ℝ} (hm : 0 < m) :
    (∫ t : ℝ in gaussianTail m, normalizedGaussian m t) ≤
      2 * Real.exp (-18 * m) :=
  integral_normalizedGaussian_gaussianTail_le hm

end VKEdgePiOverTwo
end PrimeNumberTheorem
