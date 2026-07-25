import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTParametricTwoStrip

open Filter Topology

namespace PrimeNumberTheorem

/-! Public contract for the parametric two-strip PNT transfer. -/

example {threshold : ℝ} (hhalf : 1 / 2 < threshold) :
    (1 : Fin 2) ∈
      pintzCarlsonHighDensityIndices
        (pntParametricTwoStripSigma threshold) :=
  pntParametricTwoStrip_one_mem_highDensityIndices hhalf

example
    (threshold : ℝ) (hhalf : 1 / 2 < threshold) (hlt : threshold < 1) :
    ∃ c > 0,
      (1 : Fin 2) ∈
          pintzCarlsonHighDensityIndices
            (pntParametricTwoStripSigma threshold) ∧
      ∀ rate : ℝ, 0 < rate → rate < 2 * Real.sqrt c →
        Tendsto
          (fun x : ℝ =>
            pintzCarlsonHybridDensityBudget
              (pntParametricTwoStripSigma threshold) x
              (pintzCarlsonHeight rate x))
          atTop (𝓝 0) :=
  exists_pintzConstant_parametricTwoStripHybridDensityBudget_tendsto
    threshold hhalf hlt

example (threshold : ℝ) {rate : ℝ} (hrate : 0 < rate) :
    ∃ C, 0 ≤ C ∧
      Nonempty
        (FixedSigmaPNTUpperSchedule C rate
          (pntParametricTwoStripSigma threshold)) :=
  exists_parametricTwoStripPNTUpperSchedule threshold hrate

example
    (threshold : ℝ) (hhalf : 1 / 2 < threshold) (hlt : threshold < 1) :
    ∃ rate : ℝ, 0 < rate ∧ rate ≤ 1 ∧
      Tendsto
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        atTop (𝓝 0) :=
  exists_fixedRate_parametricTwoStrip_relativeChebyshevPsi0Error_tendsto
    threshold hhalf hlt

end PrimeNumberTheorem
