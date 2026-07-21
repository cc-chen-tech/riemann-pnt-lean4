import HardyTheorem.HardyPhasePartialSecondMoment

open Complex MeasureTheory Set

example {N : ℕ} (hN : 0 < N) (s : Finset ℕ)
    {delta a b q E D : ℝ} (ha : 0 < a) (hab : a ≤ b) (hq : 0 < q)
    (hpositive : ∀ n ∈ s, n ≠ 0) (hupper : ∀ n ∈ s, n ≤ N)
    (henergy : ∀ t ∈ Set.Icc a b,
      (∑ n ∈ s, Complex.normSq
        (HardyTheorem.hardyPhaseLinearizedCoeff n delta t)) ≤ E)
    (hderivEnergy : ∀ t ∈ Set.Icc a b,
      (∑ n ∈ s, Complex.normSq
        (deriv (HardyTheorem.hardyPhaseWindowCoeff n delta) t)) ≤ D) :
    (∫ t in a..b,
      Complex.normSq
        (HardyTheorem.hardyPhaseLinearizedPartialSum s delta t)) ≤
      (b - a) * E +
        4 * (5 * Real.pi + 4) * N * E +
        |b - a| *
          (2 * (5 * Real.pi + 4) * N *
            (q ^ 2 * D + (q ^ 2)⁻¹ * E)) :=
  HardyTheorem.integral_normSq_hardyPhaseLinearizedPartialSum_le
    hN s ha hab hq hpositive hupper henergy hderivEnergy

#print axioms HardyTheorem.integral_normSq_hardyPhaseLinearizedPartialSum_le
