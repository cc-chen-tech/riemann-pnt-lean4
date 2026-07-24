import PrimeNumberTheorem.CarneiroLittmannProfile
import PrimeNumberTheorem.ZeroForcedOscillationComplementaryBound

/-!
# Hilbert bounds for zero-forced oscillation

This module replaces the cardinality-dependent pairwise mean-square error by
the concrete Hilbert--Montgomery--Vaughan estimate. For a nontrivial finite
frequency family the error is at most `4π` times the coefficient energy divided
by the actual minimum spacing. The final theorem specializes this estimate to
the maximal-real-part zeta-zero package, retaining analytic multiplicity, and
extracts an interior point where that package contribution is strictly visible.

This is a finite-package estimate. A unified canonical interval below routes a
singleton package through the exact pairwise mean square and a nontrivial
package through the better of that exact threshold and the Hilbert threshold.
It does not supply a uniform lower bound for the zero spacing or control the
explicit-formula remainder.
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

/-- On every nondegenerate interval, the Hilbert mean-square bound supplies an
interior point attaining the diagonal energy minus `4π E / (Δ L)`. -/
theorem exists_mem_Ioo_sqNorm_finiteExponentialSum_ge_hilbert
    {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {c : ι → ℂ} {omega : ι → ℝ} {a b : ℝ}
    (hS : S.Nontrivial) (hab : a < b)
    (homega : Set.InjOn omega (S : Set ι)) :
    ∃ t ∈ Set.Ioo a b,
      (∑ n ∈ S, ‖c n‖ ^ 2) -
          (4 * Real.pi * (∑ n ∈ S, ‖c n‖ ^ 2) /
            minimumPositiveFrequencySpacing S omega) / (b - a) ≤
        ‖finiteExponentialSum S c omega t‖ ^ 2 := by
  let f : ℝ → ℝ := fun t => ‖finiteExponentialSum S c omega t‖ ^ 2
  let D : ℝ := ∑ n ∈ S, ‖c n‖ ^ 2
  let B : ℝ :=
    4 * Real.pi * D / minimumPositiveFrequencySpacing S omega
  let A : ℝ := D - B / (b - a)
  have hf : Continuous f := by
    dsimp [f, finiteExponentialSum]
    fun_prop
  have haggregate :=
    abs_finiteExponentialMeanSquare_sub_diagonal_le_minimumSpacing
      (S := S) (c := c) (omega := omega) (a := a) (b := b) hS homega
  have hlower : (b - a) * D - B ≤ ∫ t in a..b, f t := by
    have hleft := (abs_le.mp haggregate).1
    dsimp [f, D, B] at hleft ⊢
    linarith
  have hlength : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  have hscale : (b - a) * A = (b - a) * D - B := by
    dsimp [A]
    field_simp
  by_contra! hnone
  have hdiff : IntervalIntegrable (fun t => A - f t)
      MeasureTheory.volume a b :=
    Continuous.intervalIntegrable (continuous_const.sub hf) a b
  have hpositive : 0 < ∫ t in a..b, A - f t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      hdiff (fun t ht => sub_pos.mpr (hnone t ht)) hab
  rw [intervalIntegral.integral_sub
      (Continuous.intervalIntegrable continuous_const a b)
      (Continuous.intervalIntegrable hf a b),
    intervalIntegral.integral_const] at hpositive
  change 0 < (b - a) * A - ∫ t in a..b, f t at hpositive
  rw [hscale] at hpositive
  linarith

/-- Quantitative specialization to the maximal zeta-zero package. The lower
bound retains the growth exponent, analytic multiplicities, total coefficient
energy, actual minimum spacing, and interval length. -/
theorem
    exists_mem_Ioo_sqNorm_maximalZeroPackageContribution_ge_hilbert
    (T : ℝ) (hpackage : (maximalRealPartZeroPackage T).Nontrivial)
    {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Set.Ioo a b,
      Real.exp (maximalZeroRealPart T * y) ^ 2 *
          (maximalZeroPackageEnergy T -
            (4 * Real.pi * maximalZeroPackageEnergy T /
              maximalZeroPackageMinimumImaginarySpacing T) / (b - a)) ≤
        ‖equalRealPartZeroPackageContribution (Real.exp y) T
          (maximalZeroRealPart T)‖ ^ 2 := by
  have him :
      Set.InjOn Complex.im (maximalRealPartZeroPackage T : Set ℂ) := by
    apply im_injOn_of_re_eq _ (maximalZeroRealPart T)
    intro ρ hρ
    exact (mem_maximalRealPartZeroPackage.mp hρ).2.2
  rcases exists_mem_Ioo_sqNorm_finiteExponentialSum_ge_hilbert
      (S := maximalRealPartZeroPackage T)
      (c := fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹)
      (omega := Complex.im) hpackage hab him with ⟨y, hy, hpoint⟩
  refine ⟨y, hy, ?_⟩
  rw [equalRealPartZeroPackageContribution_exp_eq_exponentialPolynomial,
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_pow]
  have hpoly :
      multiplicityWeightedExponentialPolynomial
          (maximalRealPartZeroPackage T)
          (analyticOrderNatAt riemannZeta) (fun ρ => ρ⁻¹) Complex.im y =
        finiteExponentialSum (maximalRealPartZeroPackage T)
          (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹)
          Complex.im y := by
    rfl
  change Real.exp (maximalZeroRealPart T * y) ^ 2 *
      (maximalZeroPackageEnergy T -
        (4 * Real.pi * maximalZeroPackageEnergy T /
          maximalZeroPackageMinimumImaginarySpacing T) / (b - a)) ≤
    Real.exp (maximalZeroRealPart T * y) ^ 2 *
      ‖multiplicityWeightedExponentialPolynomial
        (maximalRealPartZeroPackage T)
        (analyticOrderNatAt riemannZeta) (fun ρ => ρ⁻¹) Complex.im y‖ ^ 2
  rw [hpoly]
  apply mul_le_mul_of_nonneg_left
  · simpa [maximalZeroPackageEnergy,
      maximalZeroPackageMinimumImaginarySpacing] using hpoint
  · exact sq_nonneg _

/-- If the maximal zero package has at least two members, every logarithmic
interval longer than `4π / Δ_T` contains a point where its actual
multiplicity-aware contribution is strictly nonzero. This statement concerns
only the selected finite package, not the explicit-formula remainder. -/
theorem
    exists_mem_Ioo_sqNorm_maximalZeroPackageContribution_pos_of_hilbert
    (T : ℝ) (hpackage : (maximalRealPartZeroPackage T).Nontrivial)
    {a b : ℝ}
    (hlength :
      4 * Real.pi / maximalZeroPackageMinimumImaginarySpacing T < b - a) :
    ∃ y ∈ Set.Ioo a b,
      0 < ‖equalRealPartZeroPackageContribution (Real.exp y) T
        (maximalZeroRealPart T)‖ ^ 2 := by
  have hab : a < b := by
    have hspacing := maximalZeroPackageMinimumImaginarySpacing_pos T
    have hpi : 0 < 4 * Real.pi := by positivity
    have hpositive :
        0 < 4 * Real.pi / maximalZeroPackageMinimumImaginarySpacing T :=
      div_pos hpi hspacing
    linarith
  have him :
      Set.InjOn Complex.im (maximalRealPartZeroPackage T : Set ℂ) := by
    apply im_injOn_of_re_eq _ (maximalZeroRealPart T)
    intro ρ hρ
    exact (mem_maximalRealPartZeroPackage.mp hρ).2.2
  rcases exists_mem_Ioo_sqNorm_finiteExponentialSum_ge_hilbert
      (S := maximalRealPartZeroPackage T)
      (c := fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹)
      (omega := Complex.im) hpackage hab him with ⟨y, hy, hpoint⟩
  have henergy : 0 < maximalZeroPackageEnergy T :=
    maximalZeroPackageEnergy_pos T hpackage.nonempty
  have hinterval : 0 < b - a := sub_pos.mpr hab
  have hbracket :
      0 < maximalZeroPackageEnergy T -
        (4 * Real.pi * maximalZeroPackageEnergy T /
          maximalZeroPackageMinimumImaginarySpacing T) / (b - a) := by
    have hmul :
        4 * Real.pi * maximalZeroPackageEnergy T /
            maximalZeroPackageMinimumImaginarySpacing T <
          (b - a) * maximalZeroPackageEnergy T := by
      calc
        4 * Real.pi * maximalZeroPackageEnergy T /
            maximalZeroPackageMinimumImaginarySpacing T =
            (4 * Real.pi / maximalZeroPackageMinimumImaginarySpacing T) *
              maximalZeroPackageEnergy T := by ring
        _ < (b - a) * maximalZeroPackageEnergy T :=
          mul_lt_mul_of_pos_right hlength henergy
    have hratio :
        (4 * Real.pi * maximalZeroPackageEnergy T /
            maximalZeroPackageMinimumImaginarySpacing T) / (b - a) <
          maximalZeroPackageEnergy T := by
      exact (div_lt_iff₀ hinterval).mpr (by simpa [mul_comm] using hmul)
    linarith
  have hfinite :
      0 < ‖finiteExponentialSum (maximalRealPartZeroPackage T)
          (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹)
          Complex.im y‖ ^ 2 := by
    have hpoint' :
        maximalZeroPackageEnergy T -
            (4 * Real.pi * maximalZeroPackageEnergy T /
              maximalZeroPackageMinimumImaginarySpacing T) / (b - a) ≤
          ‖finiteExponentialSum (maximalRealPartZeroPackage T)
            (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹)
            Complex.im y‖ ^ 2 := by
      simpa [maximalZeroPackageEnergy,
        maximalZeroPackageMinimumImaginarySpacing] using hpoint
    exact lt_of_lt_of_le hbracket hpoint'
  refine ⟨y, hy, ?_⟩
  rw [equalRealPartZeroPackageContribution_exp_eq_exponentialPolynomial]
  change 0 <
    ‖((Real.exp (maximalZeroRealPart T * y) : ℝ) : ℂ) *
      multiplicityWeightedExponentialPolynomial
        (maximalRealPartZeroPackage T)
        (analyticOrderNatAt riemannZeta) (fun ρ => ρ⁻¹) Complex.im y‖ ^ 2
  rw [norm_mul, mul_pow]
  have hgrowth :
      0 < ‖((Real.exp (maximalZeroRealPart T * y) : ℝ) : ℂ)‖ ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact sq_pos_of_pos (Real.exp_pos _)
  have hpoly :
      multiplicityWeightedExponentialPolynomial
          (maximalRealPartZeroPackage T)
          (analyticOrderNatAt riemannZeta) (fun ρ => ρ⁻¹) Complex.im y =
        finiteExponentialSum (maximalRealPartZeroPackage T)
          (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹)
          Complex.im y := by
    rfl
  rw [hpoly]
  exact mul_pos hgrowth hfinite

/-- The cardinality-free Hilbert interval threshold for the maximal package.
Its strict-visibility use requires a nontrivial package; the totalized spacing
definition alone does not make the Hilbert argument valid for a singleton. -/
def maximalZeroPackageHilbertIntervalLengthThreshold (T : ℝ) : ℝ :=
  4 * Real.pi / maximalZeroPackageMinimumImaginarySpacing T

/-- The honest unified threshold. A nontrivial package uses the better of the
exact pairwise threshold and `4π / Δ_T`; an empty or singleton package retains
the exact threshold. -/
def maximalZeroPackageUnifiedIntervalLengthThreshold (T : ℝ) : ℝ :=
  if (maximalRealPartZeroPackage T).Nontrivial then
    min (maximalZeroPackageIntervalLengthThreshold T)
      (maximalZeroPackageHilbertIntervalLengthThreshold T)
  else
    maximalZeroPackageIntervalLengthThreshold T

/-- A canonical interval length strictly exceeding the selected unified
threshold. No uniform control in `T` is asserted. -/
def maximalZeroPackageUnifiedCanonicalIntervalLength (T : ℝ) : ℝ :=
  maximalZeroPackageUnifiedIntervalLengthThreshold T + 1

/-- Outside the nontrivial case, in particular for a singleton, the unified
canonical length is exactly the original exact-pairwise canonical length. -/
theorem maximalZeroPackageUnifiedCanonical_eq_exact_of_not_nontrivial
    (T : ℝ) (hpackage : ¬(maximalRealPartZeroPackage T).Nontrivial) :
    maximalZeroPackageUnifiedCanonicalIntervalLength T =
      maximalZeroPackageCanonicalIntervalLength T := by
  simp only [maximalZeroPackageUnifiedCanonicalIntervalLength,
    maximalZeroPackageUnifiedIntervalLengthThreshold, if_neg hpackage,
    maximalZeroPackageCanonicalIntervalLength]

/-- Explicit singleton specialization of the unified canonical length. -/
theorem maximalZeroPackageUnifiedCanonical_eq_exact_of_card_eq_one
    (T : ℝ) (hcard : (maximalRealPartZeroPackage T).card = 1) :
    maximalZeroPackageUnifiedCanonicalIntervalLength T =
      maximalZeroPackageCanonicalIntervalLength T := by
  apply maximalZeroPackageUnifiedCanonical_eq_exact_of_not_nontrivial
  intro hnontrivial
  have hsubsingleton :
      (maximalRealPartZeroPackage T : Set ℂ).Subsingleton :=
    Finset.card_le_one_iff_subsingleton.mp hcard.le
  exact hsubsingleton.not_nontrivial hnontrivial

/-- The unified canonical length is bounded by the minimum of the old
cardinality/spacing estimate and the cardinality-free Hilbert estimate. The
exact threshold remains inside the definition and can be strictly better than
both displayed coarse bounds. -/
theorem
    maximalZeroPackageUnifiedCanonicalIntervalLength_le_min_pairwise_hilbert
    (T : ℝ) (hpackage : (maximalRealPartZeroPackage T).Nonempty)
    (hnontrivial : (maximalRealPartZeroPackage T).Nontrivial) :
    maximalZeroPackageUnifiedCanonicalIntervalLength T ≤
      min
        (2 * (((maximalRealPartZeroPackage T).card - 1 : ℕ) : ℝ) /
          maximalZeroPackageMinimumImaginarySpacing T)
        (maximalZeroPackageHilbertIntervalLengthThreshold T) + 1 := by
  simp only [maximalZeroPackageUnifiedCanonicalIntervalLength,
    maximalZeroPackageUnifiedIntervalLengthThreshold, if_pos hnontrivial]
  have hmin := min_le_min
    (maximalZeroPackageIntervalLengthThreshold_le_card_sub_one_div_spacing
      T hpackage)
    (le_refl (maximalZeroPackageHilbertIntervalLengthThreshold T))
  linarith

/-- Exact cardinality criterion for the Hilbert threshold to improve strictly
on the old `2 * (card - 1) / Δ_T` bound. Since `6 < 2π < 7`, this happens
exactly when the maximal package has at least eight distinct zeros. -/
theorem
    maximalZeroPackageHilbertIntervalLengthThreshold_lt_pairwise_iff
    (T : ℝ) :
    maximalZeroPackageHilbertIntervalLengthThreshold T <
        2 * (((maximalRealPartZeroPackage T).card - 1 : ℕ) : ℝ) /
          maximalZeroPackageMinimumImaginarySpacing T ↔
      8 ≤ (maximalRealPartZeroPackage T).card := by
  have hspacing := maximalZeroPackageMinimumImaginarySpacing_pos T
  simp only [maximalZeroPackageHilbertIntervalLengthThreshold]
  rw [div_lt_div_iff_of_pos_right hspacing]
  constructor
  · intro h
    have hpi : 3 < Real.pi := Real.pi_gt_three
    have hcast :
        (6 : ℝ) < (((maximalRealPartZeroPackage T).card - 1 : ℕ) : ℝ) := by
      nlinarith
    have hnat : 6 < (maximalRealPartZeroPackage T).card - 1 := by
      exact_mod_cast hcast
    omega
  · intro hcard
    have hnat : 7 ≤ (maximalRealPartZeroPackage T).card - 1 := by
      omega
    have hcast :
        (7 : ℝ) ≤ (((maximalRealPartZeroPackage T).card - 1 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    nlinarith [Real.pi_lt_d2]

/-- The exact pairwise threshold supplies a strictly visible package point for
every nonempty maximal package, including a singleton. -/
theorem
    exists_mem_Ioo_sqNorm_maximalZeroPackageContribution_pos_of_exact
    (T : ℝ) (hpackage : (maximalRealPartZeroPackage T).Nonempty)
    {a b : ℝ}
    (hlength : maximalZeroPackageIntervalLengthThreshold T < b - a) :
    ∃ y ∈ Set.Ioo a b,
      0 < ‖equalRealPartZeroPackageContribution (Real.exp y) T
        (maximalZeroRealPart T)‖ ^ 2 := by
  have hinterval : 0 < b - a :=
    lt_of_le_of_lt
      (maximalZeroPackageIntervalLengthThreshold_nonneg T) hlength
  have hab : a < b := sub_pos.mp hinterval
  rcases exists_mem_Ioo_sqNorm_equalRealPartZeroPackageContribution_ge
      T (maximalZeroRealPart T) hab with ⟨y, hy, hmean⟩
  have hmean' :
      maximalZeroPackageMeanSquareMain T (b - a) y ≤
        ‖equalRealPartZeroPackageContribution (Real.exp y) T
          (maximalZeroRealPart T)‖ ^ 2 := by
    simpa only [maximalZeroPackageMeanSquareMain, maximalZeroPackageEnergy,
      maximalZeroPackageOffDiagonalBound, maximalRealPartZeroPackage] using
      hmean
  exact
    ⟨y, hy,
      lt_of_lt_of_le
        (maximalZeroPackageMeanSquareMain_pos T y hpackage hlength) hmean'⟩

/-- Every nonempty maximal package has an interior point with strictly positive
actual multiplicity-aware contribution on the unified canonical interval.
Singletons use the exact mean square; nontrivial packages use whichever of the
exact and Hilbert thresholds is smaller. -/
theorem
    exists_mem_Ioo_sqNorm_maximalZeroPackageContribution_pos_on_unified_canonical
    (T : ℝ) (hpackage : (maximalRealPartZeroPackage T).Nonempty)
    (a : ℝ) :
    ∃ y ∈ Set.Ioo a
        (a + maximalZeroPackageUnifiedCanonicalIntervalLength T),
      0 < ‖equalRealPartZeroPackageContribution (Real.exp y) T
        (maximalZeroRealPart T)‖ ^ 2 := by
  by_cases hnontrivial : (maximalRealPartZeroPackage T).Nontrivial
  · by_cases hexact :
        maximalZeroPackageIntervalLengthThreshold T ≤
          maximalZeroPackageHilbertIntervalLengthThreshold T
    · have hlength :
          maximalZeroPackageIntervalLengthThreshold T <
            (a + maximalZeroPackageUnifiedCanonicalIntervalLength T) - a := by
        simp only [maximalZeroPackageUnifiedCanonicalIntervalLength,
          maximalZeroPackageUnifiedIntervalLengthThreshold,
          if_pos hnontrivial, min_eq_left hexact, add_sub_cancel_left]
        exact lt_add_one _
      exact
        exists_mem_Ioo_sqNorm_maximalZeroPackageContribution_pos_of_exact
          T hpackage hlength
    · have hhilbert :
          maximalZeroPackageHilbertIntervalLengthThreshold T ≤
            maximalZeroPackageIntervalLengthThreshold T :=
        le_of_not_ge hexact
      have hlength :
          4 * Real.pi / maximalZeroPackageMinimumImaginarySpacing T <
            (a + maximalZeroPackageUnifiedCanonicalIntervalLength T) - a := by
        rw [maximalZeroPackageUnifiedCanonicalIntervalLength,
          maximalZeroPackageUnifiedIntervalLengthThreshold,
          if_pos hnontrivial, add_sub_cancel_left, min_eq_right hhilbert]
        exact lt_add_one
          (4 * Real.pi / maximalZeroPackageMinimumImaginarySpacing T)
      exact
        exists_mem_Ioo_sqNorm_maximalZeroPackageContribution_pos_of_hilbert
          T hnontrivial hlength
  · have hlength :
        maximalZeroPackageIntervalLengthThreshold T <
          (a + maximalZeroPackageUnifiedCanonicalIntervalLength T) - a := by
      simp only [maximalZeroPackageUnifiedCanonicalIntervalLength,
        maximalZeroPackageUnifiedIntervalLengthThreshold,
        if_neg hnontrivial, add_sub_cancel_left]
      exact lt_add_one _
    exact
      exists_mem_Ioo_sqNorm_maximalZeroPackageContribution_pos_of_exact
        T hpackage hlength

end

end PrimeNumberTheorem.ZeroForcedOscillation
