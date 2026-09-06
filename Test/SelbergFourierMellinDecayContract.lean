import HardyTheorem.SelbergFourierMellinDecay

open Complex Filter Topology

namespace HardyTheorem

#check selbergSqrtZetaPsiStripBound
#check selbergSqrtZetaPsiStripBound_nonneg
#check norm_selbergSqrtZetaPsi_le_stripBound
#check real_Gamma_half_le_four
#check norm_GammaR_mul_norm_selbergFourierZ_cpow_le
#check exists_norm_selbergMellinRaw_horizontal_le
#check tendsto_selbergMellinRaw_upper_horizontalIntegral_zero
#check tendsto_selbergMellinRaw_lower_horizontalIntegral_zero

example {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ) (X : ℕ) :
    Tendsto
      (fun T : ℝ => ∫ sigma : ℝ in (1 / 2)..2,
        selbergMellinRawIntegrand (selbergFourierZ delta y) X
          ((sigma : ℂ) + I * T))
      atTop (𝓝 0) :=
  tendsto_selbergMellinRaw_upper_horizontalIntegral_zero
    hdelta0 hdeltaPi y X

end HardyTheorem
