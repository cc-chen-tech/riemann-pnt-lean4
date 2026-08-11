import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderDynamicContourDecay

open Complex MeasureTheory Set Filter Topology
open scoped ArithmeticFunction BigOperators LSeries.notation

namespace PrimeNumberTheorem.ExplicitFormulaResidues

example (C alpha c x : ℝ) :
    thirdOrderDynamicContourLogPowerMajorant C alpha c x =
      let B := vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
        2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3) + Real.pi
      ((2 * (C * (c + 1) * (alpha + 2) ^ 2)) *
          (x ^ (2 - 3 * alpha) * Real.log x ^ 8) +
        (2 * (B + 2) * (alpha + 2)) *
          (x ^ (alpha - 1) * Real.log x ^ 4 +
            x ^ (-1 : ℝ) * Real.log x ^ 4)) / (2 * Real.pi) := rfl

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {x c : ℝ}, 1 < x → 1 < c → c ≤ 2 →
      ∀ A : ℝ, 4 ≤ A →
        ∃ T ∈ Set.Icc A (A + 1),
          ExplicitFormulaAux.goodHeight T ∧
            ‖thirdOrderContourRemainder x (-1) c
                (T / (2 * Real.pi))‖ ≤
              thirdOrderGoodHeightContourRemainderMajorant x C A T c :=
  exists_uniform_goodHeight_Icc_norm_thirdOrderContourRemainder_le

example {C alpha c : ℝ}
    (halpha23 : 2 / 3 < alpha) (halpha1 : alpha < 1) :
    Tendsto (thirdOrderDynamicContourLogPowerMajorant C alpha c)
      atTop (nhds 0) :=
  tendsto_thirdOrderDynamicContourLogPowerMajorant halpha23 halpha1

example {x C alpha c T : ℝ}
    (hx : 1 < x) (hC : 0 ≤ C) (hc : 1 < c)
    (halpha : 0 < alpha)
    (hT : T ∈ Set.Icc (x ^ alpha) (x ^ alpha + 1))
    (hlog :
      1 + Real.log (x ^ alpha + 6) ≤
        (alpha + 2) * Real.log x ^ 4) :
    thirdOrderGoodHeightContourRemainderMajorant
        x C (x ^ alpha) T c ≤
      thirdOrderDynamicContourLogPowerMajorant C alpha c x :=
  thirdOrderGoodHeightContourRemainderMajorant_le_dynamic
    hx hC hc halpha hT hlog

example {alpha c : ℝ}
    (halpha23 : 2 / 3 < alpha) (halpha1 : alpha < 1)
    (hc : 1 < c) (hc2 : c ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x : ℝ in atTop,
        ∃ T ∈ Set.Icc (x ^ alpha) (x ^ alpha + 1),
          ExplicitFormulaAux.goodHeight T ∧
            ‖thirdOrderContourRemainder x (-1) c
                (T / (2 * Real.pi))‖ < ε :=
  exists_uniform_eventually_goodHeight_norm_thirdOrderContourRemainder_lt
    halpha23 halpha1 hc hc2

end PrimeNumberTheorem.ExplicitFormulaResidues
