import PrimeNumberTheorem.VKEdgeTargetPairAnnihilatorAverage

open scoped Interval
open PrimeNumberTheorem.VKEdgePiOverTwo

#check frequencyAnnihilatorMultiplier
#check frequencyAnnihilatorMultiplier_target
#check intervalIntegral_frequencyAnnihilatorMultiplier_sq
#check normalizedStepMultiplierEnergy
#check tendsto_normalizedStepMultiplierEnergy
#check eventually_two_le_normalizedStepMultiplierEnergy
#check eventually_two_le_normalizedStepMultiplierEnergy_finset
#check annihilatedExponentialPolynomial
#check stepAveragedDiagonalEnergy
#check eventually_two_mul_coefficientEnergy_le_stepAveragedDiagonalEnergy
#check abs_intervalIntegral_annihilatedExponentialPolynomial_sub_diagonal_le

example (gamma h : ℝ) :
    frequencyAnnihilatorMultiplier gamma gamma h = 0 :=
  frequencyAnnihilatorMultiplier_target gamma h

example {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (omega : ι → ℝ) {gamma : ℝ}
    (hgamma : 0 < gamma)
    (homega : ∀ i ∈ S, 0 < omega i)
    (hne : ∀ i ∈ S, omega i ≠ gamma) :
    ∀ᶠ H in Filter.atTop, ∀ i ∈ S,
      2 ≤ normalizedStepMultiplierEnergy gamma (omega i) H :=
  eventually_two_le_normalizedStepMultiplierEnergy_finset
    S omega hgamma homega hne
