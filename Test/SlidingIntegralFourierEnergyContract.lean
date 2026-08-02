import MathlibAux.SlidingIntegralFourierEnergy

set_option autoImplicit false

open Complex FourierTransform MeasureTheory Set
open scoped FourierTransform

namespace MathlibAux

example {F : ℝ → ℂ} (hF1 : Integrable F) (hF2 : MemLp F 2)
    {H a b : ℝ} (hH : 0 < H) (hab : a ≤ b) :
    (∫ t in a..b,
      Complex.normSq (∫ u in t..t + H, F u)) ≤
      H ^ 2 * (∫ y : ℝ in {y | |y| ≤ 1 / H},
        ‖(𝓕 (hF2.toLp F) :
          Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) y‖ ^ 2) +
      4 * (∫ y : ℝ in {y | 1 / H < |y|},
        ‖(𝓕 (hF2.toLp F) :
          Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) y‖ ^ 2 / y ^ 2) :=
  integral_normSq_slidingIntegral_le_fourier_low_high hF1 hF2 hH hab

end MathlibAux
