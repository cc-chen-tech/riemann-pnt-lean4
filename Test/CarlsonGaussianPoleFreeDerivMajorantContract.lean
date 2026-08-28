import PrimeNumberTheorem.CarlsonGaussianPoleFreeDerivMajorant

open MeasureTheory

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example {Delta w zIm K : ℝ} (hDelta : 0 < Delta) :
    Integrable (carlsonGaussianDerivativeMajorant Delta w zIm K) volume :=
  integrable_carlsonGaussianDerivativeMajorant hDelta K

#print axioms integrable_carlsonGaussianDerivativeMajorant

end CarlsonZeroDensity
end PrimeNumberTheorem
