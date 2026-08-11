import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderDynamicPerronTarget
import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderDynamicContourDecay

open Complex Set Filter Topology

namespace PrimeNumberTheorem

/-- At one selected height in the `x^(3/4)` window, both analytic errors are
small at the target-amplitude scale. -/
theorem eventually_exists_goodHeight_thirdOrderContour_and_normalizedPerron_lt
    {beta c : ℝ} (hbeta : 2 / 3 < beta)
    (hc : 1 < c) (hcTwo : c ≤ 2) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x : ℝ in atTop,
        ∃ T ∈ Icc (x ^ (3 / 4 : ℝ)) (x ^ (3 / 4 : ℝ) + 1),
          ExplicitFormulaAux.goodHeight T ∧
          ‖ExplicitFormulaResidues.thirdOrderContourRemainder
              x (-1) c (T / (2 * Real.pi))‖ < ε ∧
          x ^ (-beta) *
              thirdOrderPerronErrorMajorant x c (T / (2 * Real.pi)) < ε := by
  obtain ⟨C, hC, hcontour⟩ :=
    ExplicitFormulaResidues.exists_uniform_eventually_goodHeight_norm_thirdOrderContourRemainder_lt
      (alpha := (3 / 4 : ℝ)) (c := c)
      (by norm_num) (by norm_num) hc hcTwo
  have hperron :=
    tendsto_thirdOrderNormalizedDynamicPerronPowerMajorant_of_targetRange
      hbeta hcTwo
  intro ε hε
  have hperronLt :
      ∀ᶠ x : ℝ in atTop,
        thirdOrderNormalizedDynamicPerronPowerMajorant beta c x < ε :=
    (tendsto_order.1 hperron).2 ε hε
  filter_upwards [hcontour ε hε, hperronLt,
      eventually_ge_atTop (1 : ℝ)] with x hxContour hxPerron hxOne
  obtain ⟨T, hT, hgood, hrem⟩ := hxContour
  refine ⟨T, hT, hgood, hrem, ?_⟩
  exact (normalized_thirdOrderPerronErrorMajorant_le_dynamic hxOne hT).trans_lt
    hxPerron

end PrimeNumberTheorem
