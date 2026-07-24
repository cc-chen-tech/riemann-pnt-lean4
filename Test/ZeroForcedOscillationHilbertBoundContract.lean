import PrimeNumberTheorem.ZeroForcedOscillationHilbertBound

open Complex Set
open scoped BigOperators Interval

open PrimeNumberTheorem
open PrimeNumberTheorem.DirichletPolynomial
open PrimeNumberTheorem.ZeroForcedOscillation

example {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {c : ι → ℂ} {omega : ι → ℝ} {a b : ℝ}
    (hS : S.Nontrivial) (homega : Set.InjOn omega (S : Set ι)) :
    |(∫ t in a..b, ‖finiteExponentialSum S c omega t‖ ^ 2) -
        (b - a) * ∑ n ∈ S, ‖c n‖ ^ 2| ≤
      4 * Real.pi *
        ∑ n ∈ S, ‖c n‖ ^ 2 / localFrequencySeparation S omega n :=
  abs_finiteExponentialMeanSquare_sub_diagonal_le_localSeparation
    hS homega

example {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {omega : ι → ℝ} {n : ι}
    (hS : S.Nontrivial) (hn : n ∈ S) :
    minimumPositiveFrequencySpacing S omega ≤
      localFrequencySeparation S omega n :=
  minimumPositiveFrequencySpacing_le_localFrequencySeparation hS hn

example {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {c : ι → ℂ} {omega : ι → ℝ}
    (hS : S.Nontrivial) (homega : Set.InjOn omega (S : Set ι)) :
    (∑ n ∈ S, ‖c n‖ ^ 2 / localFrequencySeparation S omega n) ≤
      (∑ n ∈ S, ‖c n‖ ^ 2) /
        minimumPositiveFrequencySpacing S omega :=
  sum_sqNorm_div_localFrequencySeparation_le_div_minimumSpacing
    hS homega

example {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {c : ι → ℂ} {omega : ι → ℝ} {a b : ℝ}
    (hS : S.Nontrivial) (homega : Set.InjOn omega (S : Set ι)) :
    |(∫ t in a..b, ‖finiteExponentialSum S c omega t‖ ^ 2) -
        (b - a) * ∑ n ∈ S, ‖c n‖ ^ 2| ≤
      4 * Real.pi * (∑ n ∈ S, ‖c n‖ ^ 2) /
        minimumPositiveFrequencySpacing S omega :=
  abs_finiteExponentialMeanSquare_sub_diagonal_le_minimumSpacing
    hS homega

example (T : ℝ)
    (hpackage : (maximalRealPartZeroPackage T).Nontrivial)
    {a b : ℝ} :
    |(∫ y in a..b,
        ‖finiteExponentialSum (maximalRealPartZeroPackage T)
          (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹)
          Complex.im y‖ ^ 2) -
        (b - a) * maximalZeroPackageEnergy T| ≤
      4 * Real.pi * maximalZeroPackageEnergy T /
        maximalZeroPackageMinimumImaginarySpacing T :=
  abs_maximalZeroPackageFiniteExponentialMeanSquare_sub_diagonal_le
    T hpackage
