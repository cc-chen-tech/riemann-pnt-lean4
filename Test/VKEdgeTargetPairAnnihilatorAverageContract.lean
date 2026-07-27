import PrimeNumberTheorem.VKEdgeTargetPairAnnihilatorAverage

open scoped Interval
open PrimeNumberTheorem.VKEdgePiOverTwo

#check frequencyAnnihilatorMultiplier
#check frequencyAnnihilatorMultiplier_target
#check intervalIntegral_frequencyAnnihilatorMultiplier_sq
#check normalizedStepMultiplierEnergy
#check tendsto_normalizedStepMultiplierEnergy
#check eventually_two_le_normalizedStepMultiplierEnergy

example (gamma h : ℝ) :
    frequencyAnnihilatorMultiplier gamma gamma h = 0 :=
  frequencyAnnihilatorMultiplier_target gamma h
