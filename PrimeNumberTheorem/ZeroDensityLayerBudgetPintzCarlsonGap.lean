import Mathlib

open Filter Topology

namespace PrimeNumberTheorem

/-!
# The quantitative Pintz-Carlson exponent gap

For a candidate height of square-root logarithmic exponential scale,

`H(x) = exp (k * sqrt (log x))`,

a density factor `H(x)^a` contributes the exponential rate `a * k`, while a
Pintz envelope lower bound of size `2 * sqrt(c * log x)` contributes the
decay rate `2 * sqrt c`. The strict inequality

`a * k < 2 * sqrt c`

is the quantitative room needed to absorb every fixed power of
`sqrt (log x)`.
-/

/-- The real square-root logarithmic scale. -/
noncomputable def pintzCarlsonSqrtLogScale (x : ℝ) : ℝ :=
  Real.sqrt (Real.log x)

/-- The real square-root logarithmic scale tends to infinity. -/
theorem tendsto_pintzCarlsonSqrtLogScale_atTop :
    Tendsto pintzCarlsonSqrtLogScale atTop atTop := by
  exact Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop

/-- Any fixed real power is absorbed by the strict Pintz-Carlson exponential
gap. The parameter `a` is the density exponent and `k` is the exponential
height rate. -/
theorem tendsto_pintzCarlsonGap_rpow_mul_exp
    (p a k c : ℝ) (hgap : a * k < 2 * Real.sqrt c) :
    Tendsto
      (fun x : ℝ =>
        pintzCarlsonSqrtLogScale x ^ p *
          Real.exp
            ((a * k - 2 * Real.sqrt c) *
              pintzCarlsonSqrtLogScale x))
      atTop (𝓝 0) := by
  let d := 2 * Real.sqrt c - a * k
  have hd : 0 < d := by
    dsimp [d]
    linarith
  have hreal :
      Tendsto
        (fun u : ℝ => u ^ p * Real.exp (-d * u))
        atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p d hd
  refine
    (hreal.comp tendsto_pintzCarlsonSqrtLogScale_atTop).congr' ?_
  filter_upwards with x
  congr 2
  dsimp [d]
  ring

/-- Carlson's classical fixed-strip exponent inserted into the gap criterion.
This is the exact admissible-rate inequality for the power part of the
classical density majorant. -/
theorem tendsto_carlsonExponent_pintzGap
    (p sigma k c : ℝ)
    (hgap :
      (4 * sigma * (1 - sigma)) * k < 2 * Real.sqrt c) :
    Tendsto
      (fun x : ℝ =>
        pintzCarlsonSqrtLogScale x ^ p *
          Real.exp
            (((4 * sigma * (1 - sigma)) * k -
                2 * Real.sqrt c) *
              pintzCarlsonSqrtLogScale x))
      atTop (𝓝 0) :=
  tendsto_pintzCarlsonGap_rpow_mul_exp
    p (4 * sigma * (1 - sigma)) k c hgap

end PrimeNumberTheorem
