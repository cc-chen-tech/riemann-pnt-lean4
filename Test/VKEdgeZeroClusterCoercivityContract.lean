import PrimeNumberTheorem.VKEdgeZeroClusterCoercivity

open Complex
open scoped Interval

namespace Test

#check
  (PrimeNumberTheorem.VKEdgePiOverTwo.normalizedFiniteZeroClusterContribution :
    Finset ℂ → (ℂ → ℕ) → ℝ → ℝ → ℂ)

#check
  (PrimeNumberTheorem.VKEdgePiOverTwo.finiteZeroClusterCoefficientAt :
    (ℂ → ℕ) → ℝ → ℝ → ℂ → ℂ)

#check
  (@PrimeNumberTheorem.VKEdgePiOverTwo.normalizedFiniteZeroClusterContribution_eq_drifting :
    ∀ (S : Finset ℂ) (multiplicity : ℂ → ℕ) (beta a y : ℝ),
      PrimeNumberTheorem.VKEdgePiOverTwo.normalizedFiniteZeroClusterContribution
          S multiplicity beta y =
        MathlibAux.driftingExponentialPolynomial S
          (PrimeNumberTheorem.VKEdgePiOverTwo.finiteZeroClusterCoefficientAt
            multiplicity beta a)
          Complex.im (fun rho => rho.re - beta) a y)

#check
  (@PrimeNumberTheorem.VKEdgePiOverTwo.integral_normSq_normalizedFiniteZeroClusterContribution_ge_merged :
    ∀ {S : Finset ℂ} {multiplicity : ℂ → ℕ}
      {beta a L delta : ℝ},
      0 ≤ L →
      0 ≤ delta →
      (∀ rho ∈ S, beta - delta ≤ rho.re ∧ rho.re ≤ beta) →
      (1 / 2 : ℝ) *
          (L *
              ∑ u ∈ MathlibAux.mergedFrequencySupport S Complex.im,
                ‖MathlibAux.mergedFrequencyCoefficient S
                    (PrimeNumberTheorem.VKEdgePiOverTwo.finiteZeroClusterCoefficientAt
                      multiplicity beta a)
                    Complex.im u‖ ^ 2 -
            PrimeNumberTheorem.ZeroForcedOscillation.offDiagonalBound
              (MathlibAux.mergedFrequencySupport S Complex.im)
              (MathlibAux.mergedFrequencyCoefficient S
                (PrimeNumberTheorem.VKEdgePiOverTwo.finiteZeroClusterCoefficientAt
                  multiplicity beta a)
                Complex.im)
              id) -
        L * (1 - Real.exp (-delta * L)) ^ 2 *
          (∑ rho ∈ S,
            ‖PrimeNumberTheorem.VKEdgePiOverTwo.finiteZeroClusterCoefficientAt
              multiplicity beta a rho‖) ^ 2 ≤
        ∫ y in a..(a + L),
          ‖PrimeNumberTheorem.VKEdgePiOverTwo.normalizedFiniteZeroClusterContribution
              S multiplicity beta y‖ ^ 2)

end Test
