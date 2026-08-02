import MathlibAux.FourierWeightedTail

set_option autoImplicit false

open Complex FourierTransform MeasureTheory Set
open scoped FourierTransform

namespace MathlibAux

example {F : ℝ → ℂ} (hF2 : MemLp F 2) {H : ℝ} (hH : 0 < H) :
    (∫ y : ℝ in {y | 1 / H < |y|},
      ‖(𝓕 (hF2.toLp F) :
        Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) y‖ ^ 2 / y ^ 2) ≤
      H ^ 2 * ∫ y : ℝ, ‖F y‖ ^ 2 :=
  integral_normSq_fourier_weightedTail_le hF2 hH

end MathlibAux
