import Mathlib.Analysis.Fourier.LpSpace

open FourierTransform MeasureTheory

namespace PrimeNumberTheorem

namespace FourierL1L2

/-- For an `L¹ ∩ L²` function whose pointwise Fourier transform is in `L²`,
the pointwise transform represents the abstract Plancherel transform. -/
theorem fourier_toLp_two_eq_toLp_fourier
    {f : ℝ → ℂ}
    (hf1 : MemLp f 1)
    (hf2 : MemLp f 2)
    (hfourier2 : MemLp (𝓕 f) 2) :
    𝓕 hf2.toLp = hfourier2.toLp := by
  have hinj : Function.Injective
      (Lp.toTemperedDistributionCLM ℂ (volume : Measure ℝ) 2) := by
    exact LinearMap.ker_eq_bot.mp <|
      Lp.ker_toTemperedDistributionCLM_eq_bot
        (E := ℝ) (F := ℂ) (μ := volume) (p := 2)
  apply hinj
  simp only [Lp.toTemperedDistributionCLM_apply]
  rw [← Lp.fourier_toTemperedDistribution_eq]
  ext phi
  simp only [TemperedDistribution.fourier_apply,
    Lp.toTemperedDistribution_apply]
  have hfIntegrable : Integrable f := memLp_one_iff_integrable.mp hf1
  have hswap := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (L := innerₗ ℝ)
    (μ := volume) (ν := volume) Real.continuous_fourierChar
    continuous_inner hfIntegrable phi.integrable
  have hnonflip (g : ℝ → ℂ) (x : ℝ) :
      VectorFourier.fourierIntegral Real.fourierChar volume
        (innerₗ ℝ) g x = 𝓕 g x := by
    rfl
  have hflip (g : ℝ → ℂ) (x : ℝ) :
      VectorFourier.fourierIntegral Real.fourierChar volume
        (innerₗ ℝ).flip g x = 𝓕 g x := by
    simp [VectorFourier.fourierIntegral, Real.fourier_eq,
      real_inner_comm]
  have hswap' :
      ∫ x, (𝓕 f) x * phi x =
        ∫ x, f x * (𝓕 (phi : ℝ → ℂ)) x := by
    simpa only [smul_eq_mul, hnonflip, hflip] using hswap
  have hphi (x : ℝ) :
      (𝓕 phi) x = (𝓕 (phi : ℝ → ℂ)) x :=
    congrFun (SchwartzMap.fourier_coe phi) x
  calc
    ∫ x, (𝓕 phi) x • (hf2.toLp : ℝ → ℂ) x =
        ∫ x, (𝓕 phi) x • f x := by
      apply integral_congr_ae
      filter_upwards [hf2.coeFn_toLp] with x hx
      rw [hx]
    _ = ∫ x, phi x • 𝓕 f x := by
      simp_rw [hphi]
      simpa [smul_eq_mul, mul_comm] using hswap'.symm
    _ = ∫ x, phi x • (hfourier2.toLp : ℝ → ℂ) x := by
      apply integral_congr_ae
      filter_upwards [hfourier2.coeFn_toLp] with x hx
      rw [hx]

end FourierL1L2

end PrimeNumberTheorem
