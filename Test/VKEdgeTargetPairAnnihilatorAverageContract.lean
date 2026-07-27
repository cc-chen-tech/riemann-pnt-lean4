import PrimeNumberTheorem.VKEdgeTargetPairAnnihilatorAverage

open scoped Interval
open PrimeNumberTheorem.VKEdgePiOverTwo

#check frequencyAnnihilatorMultiplier
#check frequencyAnnihilatorMultiplier_target
#check intervalIntegral_frequencyAnnihilatorMultiplier_sq

example (gamma h : ℝ) :
    frequencyAnnihilatorMultiplier gamma gamma h = 0 :=
  frequencyAnnihilatorMultiplier_target gamma h
