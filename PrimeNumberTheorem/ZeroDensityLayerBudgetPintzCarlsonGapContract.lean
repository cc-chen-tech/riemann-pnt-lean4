import PrimeNumberTheorem.ZeroDensityLayerBudgetPintzCarlsonGap

open Filter Topology

namespace PrimeNumberTheorem

/-! Public contract for the quantitative Pintz-Carlson exponent gap. -/

example
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
  tendsto_carlsonExponent_pintzGap p sigma k c hgap

end PrimeNumberTheorem
