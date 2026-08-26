import HardyTheorem.SelbergCompletedMollifiedL2
import MathlibAux.SlidingIntegralFourierCompatibility

open Complex FourierTransform MeasureTheory
open scoped FourierTransform

namespace HardyTheorem

/-! # Compatibility of S1 with Mathlib's L2 Fourier transform -/

theorem selbergFourierLp_ae_eq_sqrt_mul_explicitKernel
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (X : ℕ) :
    (fun w => (𝓕 ((memLp_two_selbergCompletedMollifiedF_complex
        hdelta0 hdeltaPi X).toLp
          (selbergCompletedMollifiedFComplex delta X)) :
        Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) w) =ᵐ[volume]
      fun w => (Real.sqrt (2 * Real.pi) : ℂ) *
        selbergExplicitInverseFourierKernel delta X (2 * Real.pi * w) := by
  let F : ℝ → ℂ := selbergCompletedMollifiedFComplex delta X
  let hF2 : MemLp F 2 :=
    memLp_two_selbergCompletedMollifiedF_complex hdelta0 hdeltaPi X
  have hcompat := MathlibAux.coe_fourier_toLp_two_ae_eq_of_integrable
    (integrable_selbergCompletedMollifiedF_complex hdelta0 hdeltaPi X) hF2
  filter_upwards [hcompat] with w hw
  change (𝓕 (hF2.toLp F) :
      Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) w = _
  rw [hw]
  exact fourier_selbergCompletedMollifiedF_eq_explicitKernel
    hdelta0 hdeltaPi X w

end HardyTheorem
