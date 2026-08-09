import PrimeNumberTheorem.ZeroDensityLayerBudgetPintzCarlsonTargetLayer

/-!
# Contract for Pintz--Carlson target-layer certificates
-/

namespace PrimeNumberTheorem

#check PintzCarlsonTargetLayerBudget
#check PintzCarlsonTargetLayerBudget.targetAmplitudeNegligible
#check targetAmplitudeNegligible_finset_sum_of_pintzCarlsonBudgets
#check twoHeightTargetComplementControl_of_pintzCarlsonBudgets

example {amplitude layer countBudget kernelBudget : ℝ → ℝ}
    (hamplitude : ∀ᶠ x in Filter.atTop, 0 < amplitude x)
    (budget :
      PintzCarlsonTargetLayerBudget
        amplitude layer countBudget kernelBudget) :
    TargetAmplitudeNegligible amplitude layer :=
  budget.targetAmplitudeNegligible hamplitude

end PrimeNumberTheorem
