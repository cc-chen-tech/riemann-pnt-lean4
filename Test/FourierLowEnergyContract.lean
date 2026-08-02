import MathlibAux.FourierLowEnergy

set_option autoImplicit false

open FourierTransform MeasureTheory Set
open scoped FourierTransform

namespace MathlibAux

example (F : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ))
    (s : Set ℝ) :
    (∫ y : ℝ in s,
      ‖(𝓕 F : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) y‖ ^ 2) ≤
      ∫ t : ℝ, ‖F t‖ ^ 2 :=
  integral_norm_sq_fourier_restrict_le F s

example (F : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) (H : ℝ) :
    (∫ y : ℝ in {y | |y| ≤ 1 / H},
      ‖(𝓕 F : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) y‖ ^ 2) ≤
      ∫ t : ℝ, ‖F t‖ ^ 2 :=
  integral_norm_sq_fourier_low_le F H

end MathlibAux
