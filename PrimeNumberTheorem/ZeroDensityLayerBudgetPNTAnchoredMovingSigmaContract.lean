import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTAnchoredMovingSigma

open Filter Topology

namespace PrimeNumberTheorem

#check MovingSigmaAnchoredAt
#check anchoredMovingSigmaDensityMajorant
#check pintzCarlsonHybridDensityBudget_le_anchoredMajorant
#check exists_pintzConstant_anchoredMovingSigmaDensityMajorant_tendsto
#check exists_pintzConstant_anchoredUniformMovingSigmaDensityDecay

example
    {n : ℕ} (sigma0 : ℝ)
    (hhalf : 1 / 2 < sigma0) (hlt : sigma0 < 1)
    (inputAtHeight : ∀ T : ℝ, PositiveZeroBucketInput T n)
    (hanchor : MovingSigmaAnchoredAt sigma0 inputAtHeight) :
    ∃ rate : ℝ, 0 < rate ∧ rate ≤ 1 ∧
      Tendsto
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        atTop (nhds 0) :=
  exists_fixedRate_anchoredMovingSigma_relativeChebyshevPsi0Error_tendsto
    sigma0 hhalf hlt inputAtHeight hanchor

end PrimeNumberTheorem
