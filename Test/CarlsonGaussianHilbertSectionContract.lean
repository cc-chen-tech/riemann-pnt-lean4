import PrimeNumberTheorem.CarlsonGaussianHilbertSection

open Complex

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example {Delta w t : ℝ} (hDelta : Delta ≠ 0)
    (H : ℂ → ℂ) (z : ℂ) :
    ‖carlsonGaussianHilbertSection Delta w H z t‖ ^ 2 =
      Real.exp
          ((z.re ^ 2 - (z.im + t - w) ^ 2) / Delta ^ 2) *
        ‖H (z + I * (t : ℂ))‖ ^ 2 :=
  norm_sq_carlsonGaussianHilbertSection hDelta H z t

example {Delta w x t : ℝ} (hDelta : Delta ≠ 0)
    (H : ℂ → ℂ) :
    ‖carlsonGaussianHilbertSection Delta w H (x : ℂ) t‖ ^ 2 =
      Real.exp (x ^ 2 / Delta ^ 2) *
        carlsonGaussianWeight Delta w t *
        ‖H ((x : ℂ) + I * (t : ℂ))‖ ^ 2 :=
  norm_sq_carlsonGaussianHilbertSection_real hDelta H x t

#print axioms norm_sq_carlsonGaussianHilbertSection
#print axioms norm_sq_carlsonGaussianHilbertSection_real

end CarlsonZeroDensity
end PrimeNumberTheorem
