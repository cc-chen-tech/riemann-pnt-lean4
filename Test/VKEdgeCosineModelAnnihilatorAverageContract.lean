import PrimeNumberTheorem.VKEdgeCosineModelAnnihilatorAverage

open Complex Filter
open scoped Interval

open PrimeNumberTheorem.VKEdgePiOverTwo

#check (frequencyAnnihilatorMultiplier :
  ℝ → ℝ → ℝ → ℝ)

#check (frequencyAnnihilatorMultiplier_target :
  ∀ gamma h : ℝ,
    frequencyAnnihilatorMultiplier gamma gamma h = 0)

#check (intervalIntegral_frequencyAnnihilatorMultiplier_sq :
  ∀ {gamma lambda H : ℝ},
    gamma ≠ 0 →
    lambda ≠ 0 →
    lambda ≠ gamma →
    lambda ≠ -gamma →
    (∫ h in (0 : ℝ)..H,
        frequencyAnnihilatorMultiplier gamma lambda h ^ 2) =
      4 * H +
        Real.sin (2 * lambda * H) / lambda +
        Real.sin (2 * gamma * H) / gamma -
        4 * Real.sin ((lambda - gamma) * H) / (lambda - gamma) -
        4 * Real.sin ((lambda + gamma) * H) / (lambda + gamma))

#check (normalizedStepMultiplierEnergy :
  ℝ → ℝ → ℝ → ℝ)

#check (tendsto_normalizedStepMultiplierEnergy :
  ∀ {gamma lambda : ℝ},
    0 < gamma →
    0 < lambda →
    lambda ≠ gamma →
    Tendsto (normalizedStepMultiplierEnergy gamma lambda)
      atTop (nhds 4))

#check (eventually_two_le_normalizedStepMultiplierEnergy :
  ∀ {gamma lambda : ℝ},
    0 < gamma →
    0 < lambda →
    lambda ≠ gamma →
    ∀ᶠ H in atTop,
      2 ≤ normalizedStepMultiplierEnergy gamma lambda H)

#check (annihilatedExponentialPolynomial :
  ∀ {ι : Type}, Finset ι → (ι → ℂ) → (ι → ℝ) →
    ℝ → ℝ → ℝ → ℂ)

#check (exists_step_intervalIntegral_annihilatedExponentialPolynomial_pos :
  ∀ {ι : Type} [DecidableEq ι]
      (S : Finset ι) (c : ι → ℂ) (omega : ι → ℝ) {gamma : ℝ},
    0 < gamma →
    (∀ i ∈ S, 0 < omega i) →
    (∀ i ∈ S, omega i ≠ gamma) →
    Set.InjOn omega ↑S →
    0 < ∑ i ∈ S, ‖c i‖ ^ 2 →
    ∃ h L : ℝ,
      0 < L ∧
        0 < ∫ y in (0 : ℝ)..L,
          ‖annihilatedExponentialPolynomial
            S c omega gamma h y‖ ^ 2)
