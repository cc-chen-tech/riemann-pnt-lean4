import MathlibAux.SlidingIntegralFourierCompatibility

set_option autoImplicit false

open Complex FourierTransform MeasureTheory
open scoped FourierTransform Interval

#check MathlibAux.fourier_toLp_two_eq_of_integrable
#check MathlibAux.fourierInv_rectangularMultiplierLp_ae_eq_slidingIntegral

theorem slidingIntegralCompatibility_contract
    {F : ℝ → ℂ} (hF1 : Integrable F) (hF2 : MemLp F 2)
    {H : ℝ} (hH : 0 ≤ H) :
    (fun t => (𝓕⁻ (MathlibAux.rectangularMultiplierLp (hF2.toLp F) H hH) :
        Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) t) =ᵐ[volume]
      fun t => ∫ u in t..t + H, F u :=
  MathlibAux.fourierInv_rectangularMultiplierLp_ae_eq_slidingIntegral hF1 hF2 hH

#print axioms MathlibAux.fourier_mul_convolution_eq_of_integrable
#print axioms MathlibAux.coe_fourier_toLp_two_ae_eq_of_integrable
#print axioms MathlibAux.fourierInv_rectangularMultiplierLp_ae_eq_slidingIntegral
