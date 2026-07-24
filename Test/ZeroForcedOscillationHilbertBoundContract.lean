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

example {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {c : ι → ℂ} {omega : ι → ℝ} {a b : ℝ}
    (hS : S.Nontrivial) (hab : a < b)
    (homega : Set.InjOn omega (S : Set ι)) :
    ∃ t ∈ Set.Ioo a b,
      (∑ n ∈ S, ‖c n‖ ^ 2) -
          (4 * Real.pi * (∑ n ∈ S, ‖c n‖ ^ 2) /
            minimumPositiveFrequencySpacing S omega) / (b - a) ≤
        ‖finiteExponentialSum S c omega t‖ ^ 2 :=
  exists_mem_Ioo_sqNorm_finiteExponentialSum_ge_hilbert
    hS hab homega

example (T : ℝ)
    (hpackage : (maximalRealPartZeroPackage T).Nontrivial)
    {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Set.Ioo a b,
      Real.exp (maximalZeroRealPart T * y) ^ 2 *
          (maximalZeroPackageEnergy T -
            (4 * Real.pi * maximalZeroPackageEnergy T /
              maximalZeroPackageMinimumImaginarySpacing T) / (b - a)) ≤
        ‖equalRealPartZeroPackageContribution (Real.exp y) T
          (maximalZeroRealPart T)‖ ^ 2 :=
  exists_mem_Ioo_sqNorm_maximalZeroPackageContribution_ge_hilbert
    T hpackage hab

example (T : ℝ)
    (hpackage : (maximalRealPartZeroPackage T).Nontrivial)
    {a b : ℝ}
    (hlength :
      4 * Real.pi / maximalZeroPackageMinimumImaginarySpacing T < b - a) :
    ∃ y ∈ Set.Ioo a b,
      0 < ‖equalRealPartZeroPackageContribution (Real.exp y) T
        (maximalZeroRealPart T)‖ ^ 2 :=
  exists_mem_Ioo_sqNorm_maximalZeroPackageContribution_pos_of_hilbert
    T hpackage hlength

example (T : ℝ) :
    maximalZeroPackageHilbertIntervalLengthThreshold T =
      4 * Real.pi / maximalZeroPackageMinimumImaginarySpacing T := rfl

example (T : ℝ) :
    maximalZeroPackageUnifiedCanonicalIntervalLength T =
      maximalZeroPackageUnifiedIntervalLengthThreshold T + 1 := rfl

example (T : ℝ) (hcard : (maximalRealPartZeroPackage T).card = 1) :
    maximalZeroPackageUnifiedCanonicalIntervalLength T =
      maximalZeroPackageCanonicalIntervalLength T :=
  maximalZeroPackageUnifiedCanonical_eq_exact_of_card_eq_one T hcard

example
    (T : ℝ) (hpackage : (maximalRealPartZeroPackage T).Nonempty)
    (hnontrivial : (maximalRealPartZeroPackage T).Nontrivial) :
    maximalZeroPackageUnifiedCanonicalIntervalLength T ≤
      min
        (2 * (((maximalRealPartZeroPackage T).card - 1 : ℕ) : ℝ) /
          maximalZeroPackageMinimumImaginarySpacing T)
        (maximalZeroPackageHilbertIntervalLengthThreshold T) + 1 :=
  maximalZeroPackageUnifiedCanonicalIntervalLength_le_min_pairwise_hilbert
    T hpackage hnontrivial

example (T : ℝ) :
    maximalZeroPackageHilbertIntervalLengthThreshold T <
        2 * (((maximalRealPartZeroPackage T).card - 1 : ℕ) : ℝ) /
          maximalZeroPackageMinimumImaginarySpacing T ↔
      8 ≤ (maximalRealPartZeroPackage T).card :=
  maximalZeroPackageHilbertIntervalLengthThreshold_lt_pairwise_iff T

example
    (T : ℝ) (hpackage : (maximalRealPartZeroPackage T).Nonempty)
    {a b : ℝ}
    (hlength : maximalZeroPackageIntervalLengthThreshold T < b - a) :
    ∃ y ∈ Set.Ioo a b,
      0 < ‖equalRealPartZeroPackageContribution (Real.exp y) T
        (maximalZeroRealPart T)‖ ^ 2 :=
  exists_mem_Ioo_sqNorm_maximalZeroPackageContribution_pos_of_exact
    T hpackage hlength

example
    (T : ℝ) (hpackage : (maximalRealPartZeroPackage T).Nonempty)
    (a : ℝ) :
    ∃ y ∈ Set.Ioo a
        (a + maximalZeroPackageUnifiedCanonicalIntervalLength T),
      0 < ‖equalRealPartZeroPackageContribution (Real.exp y) T
        (maximalZeroRealPart T)‖ ^ 2 :=
  exists_mem_Ioo_sqNorm_maximalZeroPackageContribution_pos_on_unified_canonical
    T hpackage a
