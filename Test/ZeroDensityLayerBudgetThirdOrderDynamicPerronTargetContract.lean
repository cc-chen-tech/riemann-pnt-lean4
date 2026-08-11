import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderDynamicPerronTarget

open Complex Set Filter Topology
open scoped ArithmeticFunction BigOperators LSeries.notation

namespace PrimeNumberTheorem

example (x c W : ℝ) :
    thirdOrderPerronErrorMajorant x c W =
      ∑' n : ℕ, vonMangoldt n * (x / n) ^ c /
        (8 * Real.pi ^ 3 * W ^ 2) := rfl

example {x c W : ℝ} (hx : 0 < x) :
    thirdOrderPerronErrorMajorant x c W =
      (x ^ c / (8 * Real.pi ^ 3 * W ^ 2)) *
        ExplicitFormulaResidues.vonMangoldtLSeriesNorm (c - 1) :=
  thirdOrderPerronErrorMajorant_eq hx

example (beta c x : ℝ) :
    thirdOrderNormalizedDynamicPerronPowerMajorant beta c x =
      (ExplicitFormulaResidues.vonMangoldtLSeriesNorm (c - 1) /
          (2 * Real.pi)) *
        x ^ (c - 3 / 2 - beta) := rfl

example {beta c : ℝ} (hexponent : c - 3 / 2 - beta < 0) :
    Tendsto (thirdOrderNormalizedDynamicPerronPowerMajorant beta c)
      atTop (nhds 0) :=
  tendsto_thirdOrderNormalizedDynamicPerronPowerMajorant hexponent

example {beta c : ℝ} (hbeta : 2 / 3 < beta) (hcTwo : c ≤ 2) :
    Tendsto (thirdOrderNormalizedDynamicPerronPowerMajorant beta c)
      atTop (nhds 0) :=
  tendsto_thirdOrderNormalizedDynamicPerronPowerMajorant_of_targetRange
    hbeta hcTwo

example {beta c x T : ℝ} (hx : 1 ≤ x)
    (hT : T ∈ Icc (x ^ (3 / 4 : ℝ)) (x ^ (3 / 4 : ℝ) + 1)) :
    x ^ (-beta) *
        thirdOrderPerronErrorMajorant x c (T / (2 * Real.pi)) ≤
      thirdOrderNormalizedDynamicPerronPowerMajorant beta c x :=
  normalized_thirdOrderPerronErrorMajorant_le_dynamic hx hT

end PrimeNumberTheorem
