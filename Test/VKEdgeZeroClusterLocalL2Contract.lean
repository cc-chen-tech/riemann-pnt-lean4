import PrimeNumberTheorem.VKEdgeZeroClusterLocalL2

open Complex MeasureTheory Set
open scoped BigOperators Interval

#check @PrimeNumberTheorem.VKEdgePiOverTwo.finiteZeroClusterCoefficientMass
#check @PrimeNumberTheorem.VKEdgePiOverTwo.finiteZeroClusterMergedEnergy
#check @PrimeNumberTheorem.VKEdgePiOverTwo.finiteZeroClusterLocalSeparationEnergy
#check @PrimeNumberTheorem.VKEdgePiOverTwo.integral_normSq_normalizedFiniteZeroClusterContribution_ge_localSeparation
#check @PrimeNumberTheorem.VKEdgePiOverTwo.integral_normSq_normalizedFiniteZeroClusterContribution_ge_phaseCoercive_localSeparation
#check @PrimeNumberTheorem.VKEdgePiOverTwo.integral_normSq_normalizedFiniteZeroClusterContribution_pos_of_localSeparation

open PrimeNumberTheorem.VKEdgePiOverTwo

example
    {S : Finset ℂ} {multiplicity : ℂ → ℕ}
    {beta a L delta : ℝ}
    (hL : 0 ≤ L)
    (hdelta : 0 ≤ delta)
    (hband : ∀ rho ∈ S, beta - delta ≤ rho.re ∧ rho.re ≤ beta)
    (hsupport : (MathlibAux.mergedFrequencySupport S Complex.im).Nontrivial) :
    (1 / 2 : ℝ) *
          (L * finiteZeroClusterMergedEnergy S multiplicity beta a -
            4 * Real.pi *
              finiteZeroClusterLocalSeparationEnergy
                S multiplicity beta a) -
        L * (1 - Real.exp (-delta * L)) ^ 2 *
          finiteZeroClusterCoefficientMass S multiplicity beta a ^ 2 ≤
      ∫ y in a..(a + L),
        ‖normalizedFiniteZeroClusterContribution
          S multiplicity beta y‖ ^ 2 :=
  integral_normSq_normalizedFiniteZeroClusterContribution_ge_localSeparation
    hL hdelta hband hsupport

example
    {S : Finset ℂ} {multiplicity : ℂ → ℕ}
    {beta a L delta : ℝ}
    (hL : 0 ≤ L)
    (hdelta : 0 ≤ delta)
    (hband : ∀ rho ∈ S, beta - delta ≤ rho.re ∧ rho.re ≤ beta)
    (hre : ∀ rho ∈ S, 0 < rho.re ∧ rho.re ≤ 1)
    (him : ∀ rho ∈ S, 1 ≤ rho.im)
    (hsupport : (MathlibAux.mergedFrequencySupport S Complex.im).Nontrivial) :
    (1 / 2 : ℝ) *
          (L /
                (4 *
                  (MathlibAux.mergedFrequencySupport S Complex.im).card) *
              finiteZeroClusterCoefficientMass S multiplicity beta a ^ 2 -
            4 * Real.pi *
              finiteZeroClusterLocalSeparationEnergy
                S multiplicity beta a) -
        L * (1 - Real.exp (-delta * L)) ^ 2 *
          finiteZeroClusterCoefficientMass S multiplicity beta a ^ 2 ≤
      ∫ y in a..(a + L),
        ‖normalizedFiniteZeroClusterContribution
          S multiplicity beta y‖ ^ 2 :=
  integral_normSq_normalizedFiniteZeroClusterContribution_ge_phaseCoercive_localSeparation
    hL hdelta hband hre him hsupport

example
    {S : Finset ℂ} {multiplicity : ℂ → ℕ}
    {beta a L delta : ℝ}
    (hL : 0 ≤ L)
    (hdelta : 0 ≤ delta)
    (hband : ∀ rho ∈ S, beta - delta ≤ rho.re ∧ rho.re ≤ beta)
    (hre : ∀ rho ∈ S, 0 < rho.re ∧ rho.re ≤ 1)
    (him : ∀ rho ∈ S, 1 ≤ rho.im)
    (hsupport : (MathlibAux.mergedFrequencySupport S Complex.im).Nontrivial)
    (hcoercive :
      4 * Real.pi *
            finiteZeroClusterLocalSeparationEnergy
              S multiplicity beta a +
          2 * L * (1 - Real.exp (-delta * L)) ^ 2 *
            finiteZeroClusterCoefficientMass S multiplicity beta a ^ 2 <
        L /
            (4 * (MathlibAux.mergedFrequencySupport S Complex.im).card) *
          finiteZeroClusterCoefficientMass S multiplicity beta a ^ 2) :
    0 <
      ∫ y in a..(a + L),
        ‖normalizedFiniteZeroClusterContribution
          S multiplicity beta y‖ ^ 2 :=
  integral_normSq_normalizedFiniteZeroClusterContribution_pos_of_localSeparation
    hL hdelta hband hre him hsupport hcoercive
