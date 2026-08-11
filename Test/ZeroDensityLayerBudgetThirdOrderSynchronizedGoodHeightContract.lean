import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderSynchronizedGoodHeight

open Complex Set Filter Topology

namespace PrimeNumberTheorem

example {beta c : ℝ} (hbeta : 2 / 3 < beta)
    (hc : 1 < c) (hcTwo : c ≤ 2) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x : ℝ in atTop,
        ∃ T ∈ Icc (x ^ (3 / 4 : ℝ)) (x ^ (3 / 4 : ℝ) + 1),
          ExplicitFormulaAux.goodHeight T ∧
          ‖ExplicitFormulaResidues.thirdOrderContourRemainder
              x (-1) c (T / (2 * Real.pi))‖ < ε ∧
          x ^ (-beta) *
              thirdOrderPerronErrorMajorant x c (T / (2 * Real.pi)) < ε :=
  eventually_exists_goodHeight_thirdOrderContour_and_normalizedPerron_lt
    hbeta hc hcTwo

end PrimeNumberTheorem
