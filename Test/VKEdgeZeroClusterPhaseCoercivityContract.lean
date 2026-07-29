import PrimeNumberTheorem.VKEdgeZeroClusterPhaseCoercivity

open Complex
open scoped BigOperators

#check @PrimeNumberTheorem.VKEdgePiOverTwo.half_norm_finiteZeroClusterCoefficientAt_le_neg_im

#check @PrimeNumberTheorem.VKEdgePiOverTwo.half_sum_norm_finiteZeroClusterCoefficientAt_le_norm_mergedFrequencyCoefficient

#check @PrimeNumberTheorem.VKEdgePiOverTwo.quarter_sum_sameOrdinateFiberMass_sq_le_mergedFrequencyEnergy

#check @PrimeNumberTheorem.VKEdgePiOverTwo.totalCoefficientMass_sq_le_four_card_mul_mergedFrequencyEnergy

example
    {multiplicity : ℂ → ℕ} {beta a gamma : ℝ} {rho : ℂ}
    (hre : 0 < rho.re) (hre1 : rho.re ≤ 1)
    (him : rho.im = gamma) (hgamma : 1 ≤ gamma) :
    (1 / 2 : ℝ) *
          ‖PrimeNumberTheorem.VKEdgePiOverTwo.finiteZeroClusterCoefficientAt
            multiplicity beta a rho‖ ≤
      -(PrimeNumberTheorem.VKEdgePiOverTwo.finiteZeroClusterCoefficientAt
        multiplicity beta a rho).im :=
  PrimeNumberTheorem.VKEdgePiOverTwo.half_norm_finiteZeroClusterCoefficientAt_le_neg_im
      hre hre1 him hgamma

example
    {S : Finset ℂ} {multiplicity : ℂ → ℕ}
    {beta a gamma : ℝ}
    (hre : ∀ rho ∈ S, 0 < rho.re ∧ rho.re ≤ 1)
    (hgamma : 1 ≤ gamma) :
    (1 / 2 : ℝ) *
          ∑ rho ∈ S.filter (fun rho => rho.im = gamma),
            ‖PrimeNumberTheorem.VKEdgePiOverTwo.finiteZeroClusterCoefficientAt
              multiplicity beta a rho‖ ≤
      ‖MathlibAux.mergedFrequencyCoefficient S
          (PrimeNumberTheorem.VKEdgePiOverTwo.finiteZeroClusterCoefficientAt
            multiplicity beta a)
          Complex.im gamma‖ :=
  PrimeNumberTheorem.VKEdgePiOverTwo.half_sum_norm_finiteZeroClusterCoefficientAt_le_norm_mergedFrequencyCoefficient
      hre hgamma

example
    {S : Finset ℂ} {multiplicity : ℂ → ℕ}
    {beta a : ℝ}
    (hre : ∀ rho ∈ S, 0 < rho.re ∧ rho.re ≤ 1)
    (him : ∀ rho ∈ S, 1 ≤ rho.im) :
    (1 / 4 : ℝ) *
          ∑ gamma ∈ MathlibAux.mergedFrequencySupport S Complex.im,
            (∑ rho ∈ S.filter (fun rho => rho.im = gamma),
              ‖PrimeNumberTheorem.VKEdgePiOverTwo.finiteZeroClusterCoefficientAt
                  multiplicity beta a rho‖) ^ 2 ≤
      ∑ gamma ∈ MathlibAux.mergedFrequencySupport S Complex.im,
        ‖MathlibAux.mergedFrequencyCoefficient S
            (PrimeNumberTheorem.VKEdgePiOverTwo.finiteZeroClusterCoefficientAt
              multiplicity beta a)
            Complex.im gamma‖ ^ 2 :=
  PrimeNumberTheorem.VKEdgePiOverTwo.quarter_sum_sameOrdinateFiberMass_sq_le_mergedFrequencyEnergy
      hre him

example
    {S : Finset ℂ} {multiplicity : ℂ → ℕ}
    {beta a : ℝ}
    (hre : ∀ rho ∈ S, 0 < rho.re ∧ rho.re ≤ 1)
    (him : ∀ rho ∈ S, 1 ≤ rho.im) :
    (∑ rho ∈ S,
        ‖PrimeNumberTheorem.VKEdgePiOverTwo.finiteZeroClusterCoefficientAt
          multiplicity beta a rho‖) ^ 2 ≤
      4 * (MathlibAux.mergedFrequencySupport S Complex.im).card *
        ∑ gamma ∈ MathlibAux.mergedFrequencySupport S Complex.im,
          ‖MathlibAux.mergedFrequencyCoefficient S
              (PrimeNumberTheorem.VKEdgePiOverTwo.finiteZeroClusterCoefficientAt
                multiplicity beta a)
              Complex.im gamma‖ ^ 2 :=
  PrimeNumberTheorem.VKEdgePiOverTwo.totalCoefficientMass_sq_le_four_card_mul_mergedFrequencyEnergy
    hre him
