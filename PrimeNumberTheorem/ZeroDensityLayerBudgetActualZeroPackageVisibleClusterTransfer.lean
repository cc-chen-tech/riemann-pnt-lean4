import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZeroPackageFloorTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualClusterSignedComplement
import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonActualStripTransfer
import PrimeNumberTheorem.RiemannVonMangoldt.CriticalLinePartition

/-!
# Actual equal-real-part package as a visible PNT cluster

This module identifies the finite equal-real-part package used by the
mean-square anti-cancellation argument with the real visible-cluster main term
used by the dynamic Carlson transfer.  The exact energy coefficient is
retained; it is not normalized to one.
-/

open scoped BigOperators ComplexConjugate

namespace PrimeNumberTheorem

open Complex
open Filter
open ZeroForcedOscillation

private theorem norm_eq_abs_re_of_conj_eq_self
    {z : ℂ} (hz : conj z = z) :
    ‖z‖ = |z.re| := by
  have hreal : ((z.re : ℝ) : ℂ) = z :=
    Complex.conj_eq_iff_re.mp hz
  calc
    ‖z‖ = ‖((z.re : ℝ) : ℂ)‖ := congrArg norm hreal.symm
    _ = |z.re| := by rw [Complex.norm_real, Real.norm_eq_abs]

/-- The actual equal-real-part package is closed under complex conjugation. -/
theorem equalRealPartZeroPackage_isConjugationInvariant
    (T beta : ℝ) :
    IsConjugationInvariantCluster (equalRealPartZeroPackage T beta) := by
  intro rho
  rw [mem_equalRealPartZeroPackage, mem_equalRealPartZeroPackage]
  constructor
  · rintro ⟨hzero, hheight, hre⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa using RiemannVonMangoldt.isNontrivialZero_conj hzero
    · simpa using hheight
    · simpa using hre
  · rintro ⟨hzero, hheight, hre⟩
    refine ⟨RiemannVonMangoldt.isNontrivialZero_conj hzero, ?_, ?_⟩
    · simpa using hheight
    · simpa using hre

/-- On the positive real axis the conjugation-invariant actual package has a
real-valued contribution. -/
theorem conj_equalRealPartZeroPackageContribution_eq_self
    {x : ℝ} (hx : 0 < x) (T beta : ℝ) :
    conj (equalRealPartZeroPackageContribution x T beta) =
      equalRealPartZeroPackageContribution x T beta := by
  classical
  let S := equalRealPartZeroPackage T beta
  let term : ℂ → ℂ := fun rho => pntExplicitFormulaZeroTerm x rho
  have hS : IsConjugationInvariantCluster S := by
    exact equalRealPartZeroPackage_isConjugationInvariant T beta
  have hterm :
      ∀ rho ∈ S, term (conj rho) = conj (term rho) := by
    intro rho hrho
    exact pntExplicitFormulaZeroTerm_conj hx
      (mem_equalRealPartZeroPackage.mp hrho).1
  change conj (∑ rho ∈ S, term rho) = ∑ rho ∈ S, term rho
  rw [map_sum]
  exact
    Finset.sum_equiv Complex.conjAe.toEquiv
      (fun rho => (hS rho).symm)
      (fun rho hrho => (hterm rho hrho).symm)

/-- The norm of the actual package is therefore exactly the absolute value of
its real part, not merely an upper bound for it. -/
theorem norm_equalRealPartZeroPackageContribution_eq_abs_re
    {x : ℝ} (hx : 0 < x) (T beta : ℝ) :
    ‖equalRealPartZeroPackageContribution x T beta‖ =
      |(equalRealPartZeroPackageContribution x T beta).re| := by
  exact norm_eq_abs_re_of_conj_eq_self
    (conj_equalRealPartZeroPackageContribution_eq_self hx T beta)

/-- Once the dynamic truncation height covers the fixed package height, the
visible relative zero sum is exactly `-x⁻¹` times the package contribution. -/
theorem dynamicVisibleClusterPNTZeroSum_equalRealPartZeroPackage
    (H : ℝ → ℝ) {x T beta : ℝ} (hTH : T ≤ H x) :
    dynamicVisibleClusterPNTZeroSum H
        (equalRealPartZeroPackage T beta) x =
      -((x : ℂ)⁻¹) *
        equalRealPartZeroPackageContribution x T beta := by
  classical
  let S := equalRealPartZeroPackage T beta
  have hfilter :
      (nontrivialZerosFinset (H x)).filter (fun rho => rho ∈ S) = S := by
    ext rho
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => h.2
    · intro hrho
      have hmem := mem_equalRealPartZeroPackage.mp hrho
      exact ⟨mem_nontrivialZerosFinset.mpr
        ⟨hmem.1, hmem.2.1.trans hTH⟩, hrho⟩
  change
    (∑ rho ∈ nontrivialZerosFinset (H x),
        if rho ∈ S then pntRelativeZeroContribution x rho else 0) =
      -((x : ℂ)⁻¹) *
        ∑ rho ∈ S,
          (analyticOrderNatAt riemannZeta rho : ℂ) *
            (x : ℂ) ^ rho / rho
  rw [← Finset.sum_filter, hfilter]
  simp only [pntRelativeZeroContribution, pntFiniteZeroContribution,
    pntExplicitFormulaZeroTerm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho _
  ring

/-- Exact absolute-value bridge from the complex package to the real visible
PNT main term. -/
theorem abs_dynamicVisibleClusterPNTMain_equalRealPartZeroPackage
    (H : ℝ → ℝ) {x T beta : ℝ} (hx : 0 < x) (hTH : T ≤ H x) :
    |dynamicVisibleClusterPNTMain H
        (equalRealPartZeroPackage T beta) x| =
      ‖equalRealPartZeroPackageContribution x T beta‖ / x := by
  rw [dynamicVisibleClusterPNTMain,
    dynamicVisibleClusterPNTZeroSum_equalRealPartZeroPackage H hTH]
  let P := equalRealPartZeroPackageContribution x T beta
  let z := -((x : ℂ)⁻¹) * P
  have hP : conj P = P := by
    exact conj_equalRealPartZeroPackageContribution_eq_self hx T beta
  have hz : conj z = z := by
    dsimp [z]
    simp [hP]
  change |z.re| = ‖P‖ / x
  rw [← norm_eq_abs_re_of_conj_eq_self hz]
  dsimp [z]
  rw [norm_mul, norm_neg, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hx]
  ring

/-- If the dynamic height covers the fixed package throughout a logarithmic
window, the actual visible PNT main has a witness at the exact
`sqrt(energy) * x^(beta-1)` scale in that window. -/
theorem exists_far_actualZeroPackage_visibleClusterMain_ge
    (H : ℝ → ℝ) (T beta L X : ℝ) (hL : 0 < L)
    (hcover :
      ∀ y ∈ Set.Ioo X (X + L), T ≤ H (Real.exp y)) :
    ∃ y ∈ Set.Ioo X (X + L),
      Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L) *
          Real.exp ((beta - 1) * y) ≤
        |dynamicVisibleClusterPNTMain H
          (equalRealPartZeroPackage T beta) (Real.exp y)| := by
  rcases exists_far_norm_actualEqualRealPartZeroPackageContribution_ge
      T beta L hL X with ⟨y, hy, hmain⟩
  refine ⟨y, hy, ?_⟩
  rw [abs_dynamicVisibleClusterPNTMain_equalRealPartZeroPackage
    H (Real.exp_pos y) (hcover y hy)]
  have hdiv := div_le_div_of_nonneg_right hmain (Real.exp_nonneg y)
  calc
    Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L) *
          Real.exp ((beta - 1) * y) =
        Real.exp (beta * y) *
            Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L) /
          Real.exp y := by
            rw [div_eq_mul_inv, ← Real.exp_neg]
            have hexp : Real.exp ((beta - 1) * y) =
                Real.exp (beta * y) * Real.exp (-y) := by
              rw [← Real.exp_add]
              congr 1
              ring
            rw [hexp]
            ring
    _ ≤ _ := hdiv

/-- A cofinal dynamic height automatically covers the fixed package on every
sufficiently far logarithmic window.  Consequently the visible main has far
witnesses with the exact energy coefficient on the standard target-power
scale. -/
theorem hasFarTargetAmplitudeWitness_actualZeroPackage_visibleCluster
    (H : ℝ → ℝ) (hH : Tendsto H atTop atTop)
    (T beta L : ℝ) (hL : 0 < L) :
    HasFarTargetAmplitudeWitness
      (dynamicVisibleClusterPNTMain H
        (equalRealPartZeroPackage T beta))
      (fun x =>
        Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L) *
          targetZeroPowerAmplitude beta x) := by
  have hheight : ∀ᶠ x : ℝ in atTop, T ≤ H x :=
    tendsto_atTop.mp hH T
  rcases eventually_atTop.1 hheight with ⟨X₀, hX₀⟩
  intro X
  let Y := max (max X X₀) 1
  have hXleY : X ≤ Y :=
    le_trans (le_max_left X X₀) (le_max_left (max X X₀) 1)
  have hX₀leY : X₀ ≤ Y :=
    le_trans (le_max_right X X₀) (le_max_left (max X X₀) 1)
  have hcover :
      ∀ y ∈ Set.Ioo Y (Y + L), T ≤ H (Real.exp y) := by
    intro y hy
    have hyexp : y ≤ Real.exp y := by
      linarith [Real.add_one_le_exp y]
    exact hX₀ (Real.exp y)
      (le_trans hX₀leY (le_trans hy.1.le hyexp))
  rcases exists_far_actualZeroPackage_visibleClusterMain_ge
      H T beta L Y hL hcover with ⟨y, hy, hmain⟩
  refine ⟨Real.exp y, ?_, ?_⟩
  · have hyexp : y ≤ Real.exp y := by
      linarith [Real.add_one_le_exp y]
    exact le_trans hXleY (le_trans hy.1.le hyexp)
  · have hpower :
        targetZeroPowerAmplitude beta (Real.exp y) =
          Real.exp ((beta - 1) * y) := by
      unfold targetZeroPowerAmplitude
      rw [Real.rpow_def_of_pos (Real.exp_pos y), Real.log_exp]
      congr 1
      ring
    change
      Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L) *
          targetZeroPowerAmplitude beta (Real.exp y) ≤
        |dynamicVisibleClusterPNTMain H
          (equalRealPartZeroPackage T beta) (Real.exp y)|
    rw [hpower]
    exact hmain

end PrimeNumberTheorem
