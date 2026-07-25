import PrimeNumberTheorem.VKEdgePiOverTwoProjectedPsiWindow

open Filter MeasureTheory Polynomial Set Topology

open PrimeNumberTheorem

namespace PrimeNumberTheorem.VKEdgePiOverTwo

#check projectedPsiKernel
#check localizedPsiGaussianAverage_eq_logarithmic
#check neg_re_localizedPsiGaussianAverage_div_pi_eq
#check eventually_bddAbove_normalizedWindowValues
#check projectedPsiCoefficient
#check projectedPsiTailRemainder
#check tendsto_projectedPsiTailRemainder
#check eventually_projectedPsiWindow_upper_bound
#check localizedPsiGaussianAverage_C_mul
#check relativeProjectedPsiKernel
#check neg_re_mul_localizedPsiGaussianAverage_div_pi_eq
#check relativeProjectedPsiTailRemainder
#check tendsto_relativeProjectedPsiTailRemainder

example (A : ℂ[X]) {w : ℂ} {m : ℝ}
    (hm : 0 < m) (hw : 0 < w.re) :
    -(localizedPsiGaussianAverage A w m).re / Real.pi =
      ∫ y : ℝ in Set.Ioi 0,
        normalizedPsiError w y * projectedPsiKernel A w m y :=
  neg_re_localizedPsiGaussianAverage_div_pi_eq A hm hw

example (A : ℂ[X]) {u v : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Tendsto
      (projectedPsiTailRemainder A ((u : ℂ) + Complex.I * v))
      atTop (𝓝 0) :=
  tendsto_projectedPsiTailRemainder A hu hu1 v

end PrimeNumberTheorem.VKEdgePiOverTwo
