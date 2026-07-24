import PrimeNumberTheorem.ZeroDensityLayerBudgetPintzCarlsonHeight

open Filter Topology

namespace PrimeNumberTheorem

/-! Public contract for explicit Pintz-Carlson truncation heights. -/

example {k : ℝ} (hk : 0 < k) :
    Tendsto (pintzCarlsonHeight k) atTop atTop :=
  tendsto_pintzCarlsonHeight_atTop hk

example :
    ∃ c > 0, ∀ (C sigma k : ℝ), 0 ≤ C → 0 < k →
      k < 2 * Real.sqrt c →
      Tendsto
        (fun x : ℝ =>
          C *
            pintzCarlsonHeight k x ^ (4 * sigma * (1 - sigma)) *
            Real.log (pintzCarlsonHeight k x) ^ 4 *
            Real.exp (-Pintz.pintzZeroEnvelope x))
        atTop (𝓝 0) :=
  exists_pintzConstant_carlsonMajorantAtHeight_tendsto

end PrimeNumberTheorem
