import PrimeNumberTheorem.ZeroDensityLayerBudgetTwoHeightComplementSplit

/-!
# Contract for two-height target-amplitude complement aggregation
-/

namespace PrimeNumberTheorem

#check targetAmplitudeNegligible_zero
#check TargetAmplitudeNegligible.add
#check targetAmplitudeNegligible_finset_sum
#check twoHeightComplement
#check TwoHeightTargetComplementControl
#check TwoHeightTargetComplementControl.combined_negligible

example {amplitude inner annulus : ℝ → ℝ}
    (control : TwoHeightTargetComplementControl amplitude inner annulus) :
    TargetAmplitudeNegligible amplitude
      (twoHeightComplement inner annulus) :=
  control.combined_negligible

end PrimeNumberTheorem
