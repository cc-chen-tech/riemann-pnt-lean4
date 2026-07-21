import PrimeNumberTheorem.FourierL1L2

open FourierTransform MeasureTheory

namespace PrimeNumberTheorem
namespace FourierL1L2

example {f : ℝ → ℂ}
    (hf1 : MemLp f 1)
    (hf2 : MemLp f 2)
    (hfourier2 : MemLp (𝓕 f) 2) :
    𝓕 hf2.toLp = hfourier2.toLp :=
  fourier_toLp_two_eq_toLp_fourier hf1 hf2 hfourier2

#print axioms fourier_toLp_two_eq_toLp_fourier

end FourierL1L2
end PrimeNumberTheorem
