import PrimeNumberTheorem.CarneiroLittmannProfile
import PrimeNumberTheorem.ZeroForcedOscillationComplementaryBound

/-!
# Hilbert bounds for zero-forced oscillation

This module replaces the cardinality-dependent pairwise mean-square error by
the concrete Hilbert--Montgomery--Vaughan estimate. For a nontrivial finite
frequency family the error is at most `4π` times the coefficient energy divided
by the actual minimum spacing. The final theorem specializes this estimate to
the maximal-real-part zeta-zero package, retaining analytic multiplicity.

This is a finite-package estimate. It does not supply a uniform lower bound for
the zero spacing and does not control the explicit-formula remainder.
-/

open Complex Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem.ZeroForcedOscillation

noncomputable section

open DirichletPolynomial

/-- The concrete Carneiro--Littmann Hilbert certificate controls both endpoint
Hilbert forms in the exact mean-square identity. -/
theorem abs_finiteExponentialMeanSquare_sub_diagonal_le_localSeparation
    {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {c : ι → ℂ} {omega : ι → ℝ} {a b : ℝ}
    (hS : S.Nontrivial) (homega : Set.InjOn omega (S : Set ι)) :
    |(∫ t in a..b, ‖finiteExponentialSum S c omega t‖ ^ 2) -
        (b - a) * ∑ n ∈ S, ‖c n‖ ^ 2| ≤
      4 * Real.pi *
        ∑ n ∈ S, ‖c n‖ ^ 2 / localFrequencySeparation S omega n := by
  let L : ℝ := ∫ t in a..b, ‖finiteExponentialSum S c omega t‖ ^ 2
  let D : ℝ := (b - a) * ∑ n ∈ S, ‖c n‖ ^ 2
  let W : ℝ :=
    ∑ n ∈ S, ‖c n‖ ^ 2 / localFrequencySeparation S omega n
  have heq :=
    finiteExponentialMeanSquare_cast_eq_diagonal_add_hilbert
      (S := S) (c := c) (omega := omega) (a := a) (b := b) homega
  have hcast : ((L - D : ℝ) : ℂ) =
      -Complex.I *
        (hilbertForm S (phaseTwist c omega b) omega -
          hilbertForm S (phaseTwist c omega a) omega) := by
    dsimp [L, D]
    rw [ofReal_sub]
    push_cast
    rw [heq]
    ring
  have hphase (t : ℝ) :
      (∑ n ∈ S,
          ‖phaseTwist c omega t n‖ ^ 2 /
            localFrequencySeparation S omega n) = W := by
    dsimp [W]
    apply Finset.sum_congr rfl
    intro n hn
    simp [phaseTwist, Complex.norm_exp]
  have hHb :=
    hilbertForm_norm_le_two_pi_localSeparation_carneiroLittmann
      S (phaseTwist c omega b) omega hS homega
  have hHa :=
    hilbertForm_norm_le_two_pi_localSeparation_carneiroLittmann
      S (phaseTwist c omega a) omega hS homega
  rw [hphase] at hHb hHa
  calc
    |L - D| = ‖((L - D : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖-Complex.I *
        (hilbertForm S (phaseTwist c omega b) omega -
          hilbertForm S (phaseTwist c omega a) omega)‖ :=
      congrArg norm hcast
    _ = ‖hilbertForm S (phaseTwist c omega b) omega -
          hilbertForm S (phaseTwist c omega a) omega‖ := by
      rw [norm_mul, norm_neg, norm_I, one_mul]
    _ ≤ ‖hilbertForm S (phaseTwist c omega b) omega‖ +
          ‖hilbertForm S (phaseTwist c omega a) omega‖ :=
      norm_sub_le _ _
    _ ≤ 4 * Real.pi * W := by linarith
    _ = 4 * Real.pi *
        ∑ n ∈ S, ‖c n‖ ^ 2 /
          localFrequencySeparation S omega n := rfl

/-- The global minimum spacing is no larger than every local separation in a
nontrivial finite family. -/
theorem minimumPositiveFrequencySpacing_le_localFrequencySeparation
    {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {omega : ι → ℝ} {n : ι}
    (hS : S.Nontrivial) (hn : n ∈ S) :
    minimumPositiveFrequencySpacing S omega ≤
      localFrequencySeparation S omega n := by
  have hErase : (S.erase n).Nonempty := hS.erase_nonempty
  rw [localFrequencySeparation, dif_pos hErase, Finset.le_inf'_iff]
  intro m hm
  have hmS : m ∈ S := Finset.mem_of_mem_erase hm
  have hmn : m ≠ n := (Finset.mem_erase.mp hm).1
  exact minimumPositiveFrequencySpacing_le_abs_sub S omega hmS hn hmn

/-- Summing the local bounds loses no cardinality factor: the weighted local
energy is at most total energy divided by the global minimum spacing. -/
theorem sum_sqNorm_div_localFrequencySeparation_le_div_minimumSpacing
    {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {c : ι → ℂ} {omega : ι → ℝ}
    (hS : S.Nontrivial) (homega : Set.InjOn omega (S : Set ι)) :
    (∑ n ∈ S, ‖c n‖ ^ 2 / localFrequencySeparation S omega n) ≤
      (∑ n ∈ S, ‖c n‖ ^ 2) /
        minimumPositiveFrequencySpacing S omega := by
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro n hn
  have hmin := minimumPositiveFrequencySpacing_pos S omega homega
  have hlocal := localFrequencySeparation_pos hS hn homega
  exact div_le_div_of_nonneg_left (sq_nonneg _)
    hmin (minimumPositiveFrequencySpacing_le_localFrequencySeparation hS hn)

/-- Cardinality-free `4π / Δ` mean-square error for a nontrivial finite
frequency family. -/
theorem abs_finiteExponentialMeanSquare_sub_diagonal_le_minimumSpacing
    {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {c : ι → ℂ} {omega : ι → ℝ} {a b : ℝ}
    (hS : S.Nontrivial) (homega : Set.InjOn omega (S : Set ι)) :
    |(∫ t in a..b, ‖finiteExponentialSum S c omega t‖ ^ 2) -
        (b - a) * ∑ n ∈ S, ‖c n‖ ^ 2| ≤
      4 * Real.pi * (∑ n ∈ S, ‖c n‖ ^ 2) /
        minimumPositiveFrequencySpacing S omega := by
  calc
    _ ≤ 4 * Real.pi *
        ∑ n ∈ S, ‖c n‖ ^ 2 /
          localFrequencySeparation S omega n :=
      abs_finiteExponentialMeanSquare_sub_diagonal_le_localSeparation
        hS homega
    _ ≤ 4 * Real.pi *
        ((∑ n ∈ S, ‖c n‖ ^ 2) /
          minimumPositiveFrequencySpacing S omega) := by
      gcongr
      exact
        sum_sqNorm_div_localFrequencySeparation_le_div_minimumSpacing
          hS homega
    _ = _ := by ring

/-- The cardinality-free mean-square error specialized to the maximal
real-part package of zeta zeros. Analytic multiplicity is retained in the
coefficient energy. -/
theorem abs_maximalZeroPackageFiniteExponentialMeanSquare_sub_diagonal_le
    (T : ℝ) (hpackage : (maximalRealPartZeroPackage T).Nontrivial)
    {a b : ℝ} :
    |(∫ y in a..b,
        ‖finiteExponentialSum (maximalRealPartZeroPackage T)
          (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹)
          Complex.im y‖ ^ 2) -
        (b - a) * maximalZeroPackageEnergy T| ≤
      4 * Real.pi * maximalZeroPackageEnergy T /
        maximalZeroPackageMinimumImaginarySpacing T := by
  have him :
      Set.InjOn Complex.im (maximalRealPartZeroPackage T : Set ℂ) := by
    apply im_injOn_of_re_eq _ (maximalZeroRealPart T)
    intro ρ hρ
    exact (mem_maximalRealPartZeroPackage.mp hρ).2.2
  simpa [maximalZeroPackageEnergy,
    maximalZeroPackageMinimumImaginarySpacing] using
    (abs_finiteExponentialMeanSquare_sub_diagonal_le_minimumSpacing
      (S := maximalRealPartZeroPackage T)
      (c := fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹)
      (omega := Complex.im) (a := a) (b := b) hpackage him)

end

end PrimeNumberTheorem.ZeroForcedOscillation
