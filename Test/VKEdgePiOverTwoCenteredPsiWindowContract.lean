import PrimeNumberTheorem.VKEdgePiOverTwoCenteredPsiWindow

open Complex Filter MeasureTheory Polynomial Set Topology

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

#check projectedPsiKernelAtCenter
#check relativeProjectedPsiKernelAtCenter
#check projectedPsiTailRemainderAtCenter
#check relativeProjectedPsiTailRemainderAtCenter
#check neg_re_localizedPsiGaussianAverageAtCenter_div_pi_eq
#check neg_re_mul_localizedPsiGaussianAverageAtCenter_div_pi_eq
#check tendsto_projectedPsiTailRemainderAtCenter
#check tendsto_relativeProjectedPsiTailRemainderAtCenter

example (q : ℝ) (A : ℂ[X]) {w : ℂ} {m : ℝ}
    (hm : 0 < m) (hw : 0 < w.re) :
    -(localizedPsiGaussianAverageAtCenter q A w m).re / Real.pi =
      ∫ y : ℝ in Set.Ioi 0,
        normalizedPsiError w y *
          projectedPsiKernelAtCenter q A w m y :=
  neg_re_localizedPsiGaussianAverageAtCenter_div_pi_eq q A hm hw

example (q d : ℝ) (A : ℂ[X])
    (hq : 0 < q) (hd : 0 < d) (hdq : d < q)
    (hmargin : 16 * (q + d) ≤ d ^ 2)
    {u v : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Tendsto
      (projectedPsiTailRemainderAtCenter q d A
        ((u : ℂ) + I * v))
      atTop (𝓝 0) :=
  tendsto_projectedPsiTailRemainderAtCenter
    q d A hq hd hdq hmargin hu hu1 v

example (q d : ℝ) (c : ℂ) (A : ℂ[X])
    (hq : 0 < q) (hd : 0 < d) (hdq : d < q)
    (hmargin : 16 * (q + d) ≤ d ^ 2)
    {u v lambda : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Tendsto
      (relativeProjectedPsiTailRemainderAtCenter q d A
        ((u : ℂ) + I * v) ((u : ℂ) + I * lambda) c)
      atTop (𝓝 0) :=
  tendsto_relativeProjectedPsiTailRemainderAtCenter
    q d c A hq hd hdq hmargin hu hu1 v lambda

end VKEdgePiOverTwo
end PrimeNumberTheorem
