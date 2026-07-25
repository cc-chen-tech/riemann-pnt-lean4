import PrimeNumberTheorem.ZeroForcedOscillationExplicitFormula
import PrimeNumberTheorem.ZeroForcedOscillationComplementaryBound
import PrimeNumberTheorem.ZeroForcedOscillation
import PrimeNumberTheorem.PintzEnvelope

open Complex Set
open scoped BigOperators

namespace PrimeNumberTheorem
namespace VKEdgeConditionalPackage

open PrimeNumberTheorem.ZeroForcedOscillation

/-- Conditional-package envelope assumptions for the half-isolated regime. -/
structure HalfIsolatedEnvelopeInput where
  rho0 : ℂ
  T : ℝ
  Y : ℝ
  C : ℕ
  M : ℕ
  delta : ℝ
  epsilon : ℝ
  hRho : RiemannHypothesis.IsNontrivialZero rho0
  hY : 1 < Y
  hC : 1 < C
  hM : 1 ≤ M
  hDelta : 0 < delta
  hWindow : Real.log Y < Real.log (Y ^ C)
  hRhoInPackage : rho0 ∈ equalRealPartZeroPackage T rho0.re
  hFiniteVertical : (equalRealPartZeroPackage T rho0.re).card ≤ M
  hSpectralLower :
    (∑ ρ ∈ equalRealPartZeroPackage T rho0.re,
        ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹‖ ^ 2) -
      offDiagonalBound (equalRealPartZeroPackage T rho0.re)
          (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹) Complex.im /
        (Real.log (Y ^ C) - Real.log Y) ≥
      (Real.pi / 2 + delta + epsilon) ^ 2 *
        ‖(analyticOrderNatAt riemannZeta rho0 : ℂ) * rho0⁻¹‖ ^ 2
  hRemainderWindow :
    ∀ y ∈ Set.Icc (Real.log Y) (Real.log (Y ^ C)),
      ‖zeroPackageExplicitFormulaRemainder y T rho0.re‖ ≤
        epsilon * Real.exp (rho0.re * y) *
          ‖(analyticOrderNatAt riemannZeta rho0 : ℂ) * rho0⁻¹‖
  hCoeffLower : (1 / max 1 ‖rho0‖) ≤ ‖(analyticOrderNatAt riemannZeta rho0 : ℂ) * rho0⁻¹‖
  hEpsilonNonneg : 0 ≤ epsilon

/-- Conditional-package envelope assumptions for the clustered (uniform real-part-gap) regime. -/
structure ClusteredEnvelopeInput where
  rho0 : ℂ
  T : ℝ
  Y : ℝ
  C : ℕ
  M : ℕ
  delta : ℝ
  epsilon : ℝ
  hY : 1 < Y
  hC : 1 < C
  hWindow : Real.log Y < Real.log (Y ^ C)
  hM : 1 ≤ M
  hRho : RiemannHypothesis.IsNontrivialZero rho0
  hDelta : 0 < delta
  hFiniteVertical : (equalRealPartZeroPackage T rho0.re).card ≤ M
  hClusterFrequencyGap : ℝ
  hClusterFrequencyGapPos : 0 < hClusterFrequencyGap
  hClusterPairwiseGap :
    ∀ ρ₁ ∈ equalRealPartZeroPackage T rho0.re,
      ∀ ρ₂ ∈ equalRealPartZeroPackage T rho0.re,
        ρ₁ ≠ ρ₂ → hClusterFrequencyGap ≤ |ρ₂.im - ρ₁.im|
  hClusterGapLower :
    (∑ ρ ∈ equalRealPartZeroPackage T rho0.re,
        ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹‖ ^ 2) -
      (2 * (M : ℝ) / hClusterFrequencyGap) *
        (∑ ρ ∈ equalRealPartZeroPackage T rho0.re,
          ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹‖ ^ 2) /
        (Real.log (Y ^ C) - Real.log Y) ≥
      (Real.pi / 2 + delta + epsilon) ^ 2 *
        ‖(analyticOrderNatAt riemannZeta rho0 : ℂ) * rho0⁻¹‖ ^ 2
  hRemainderWindow :
    ∀ y ∈ Set.Icc (Real.log Y) (Real.log (Y ^ C)),
      ‖zeroPackageExplicitFormulaRemainder y T rho0.re‖ ≤
        epsilon * Real.exp (rho0.re * y) * ‖(analyticOrderNatAt riemannZeta rho0 : ℂ) * rho0⁻¹‖
  hCoeffLower : (1 / max 1 ‖rho0‖) ≤ ‖(analyticOrderNatAt riemannZeta rho0 : ℂ) * rho0⁻¹‖
  hEpsilonNonneg : 0 ≤ epsilon

/-- Target local oscillation conclusion for the half-isolated branch. -/
def HalfIsolatedConclusion (h : HalfIsolatedEnvelopeInput) : Prop :=
  ∃ x ∈ Set.Icc h.Y (h.Y ^ h.C),
    ‖((chebyshevPsi0 x - x : ℝ) : ℂ)‖ ≥
      (Real.pi / 2 + h.delta) *
        (Real.exp (h.rho0.re * Real.log x) / max 1 ‖h.rho0‖)

/-- Target local oscillation conclusion for the clustered branch. -/
def ClusteredConclusion (h : ClusteredEnvelopeInput) : Prop :=
  ∃ x ∈ Set.Icc h.Y (h.Y ^ h.C),
    ‖((chebyshevPsi0 x - x : ℝ) : ℂ)‖ ≥
      (Real.pi / 2 + h.delta) *
        (Real.exp (h.rho0.re * Real.log x) / max 1 ‖h.rho0‖)

/-- Monotonicity of the equal-real-part zero package in truncation height. -/
theorem equalRealPartZeroPackage_mono {T U β : ℝ} (hTU : T ≤ U) :
    ((↑(equalRealPartZeroPackage T β) : Set ℂ) ⊆
      (↑(equalRealPartZeroPackage U β) : Set ℂ)) := by
  intro ρ hρ
  rcases mem_equalRealPartZeroPackage.mp hρ with ⟨hzero, hρT, hβ⟩
  exact mem_equalRealPartZeroPackage.mpr ⟨hzero, le_trans hρT hTU, hβ⟩

/-- Tail control in BY-scale requires an explicit coefficient upper bound at `ρ₀`. -/
theorem clustered_tailsum_byBY_scale (h : ClusteredEnvelopeInput) (K : ℝ)
    (hCoeffUpper : ‖(analyticOrderNatAt riemannZeta h.rho0 : ℂ) * h.rho0⁻¹‖ ≤ K) :
    ∀ y ∈ Set.Icc (Real.log h.Y) (Real.log (h.Y ^ h.C)),
      ‖zeroPackageExplicitFormulaRemainder y h.T h.rho0.re‖ ≤
        (h.epsilon * K * (max 1 ‖h.rho0‖)) *
          (Real.exp (h.rho0.re * y) / max 1 ‖h.rho0‖) := by
  intro y hy
  let a0 : ℝ := ‖(analyticOrderNatAt riemannZeta h.rho0 : ℂ) * h.rho0⁻¹‖
  have hrem : ‖zeroPackageExplicitFormulaRemainder y h.T h.rho0.re‖ ≤
      h.epsilon * a0 * Real.exp (h.rho0.re * y) := by
    dsimp [a0]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      h.hRemainderWindow y hy
  have hcoeff_scale : h.epsilon * a0 * Real.exp (h.rho0.re * y) ≤
      h.epsilon * K * Real.exp (h.rho0.re * y) := by
    have hmul : a0 * Real.exp (h.rho0.re * y) ≤ K * Real.exp (h.rho0.re * y) := by
      exact mul_le_mul_of_nonneg_right hCoeffUpper (by positivity)
    have hmul2 : h.epsilon * (a0 * Real.exp (h.rho0.re * y)) ≤
        h.epsilon * (K * Real.exp (h.rho0.re * y)) := by
      exact mul_le_mul_of_nonneg_left hmul h.hEpsilonNonneg
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul2
  have hscalex : h.epsilon * K * Real.exp (h.rho0.re * y) =
      (h.epsilon * K * (max 1 ‖h.rho0‖)) *
        (Real.exp (h.rho0.re * y) / max 1 ‖h.rho0‖) := by
    have hmax : (0 : ℝ) < max 1 ‖h.rho0‖ := by
      exact lt_of_lt_of_le (by norm_num) (le_max_left 1 ‖h.rho0‖)
    field_simp [hmax.ne', mul_assoc, mul_left_comm, mul_comm]
  exact hrem.trans (hcoeff_scale.trans (le_of_eq (by simpa [a0] using hscalex)))

theorem clustered_offDiagonalBound_le_pairwise_gap
    (S : Finset ℂ) (c : ℂ → ℂ) (M : ℕ) (gap : ℝ)
    (hGapPos : 0 < gap) (hcard : (S.card : ℝ) ≤ M)
    (hGap : ∀ ρ₁ ∈ S, ∀ ρ₂ ∈ S, ρ₁ ≠ ρ₂ → gap ≤ |ρ₂.im - ρ₁.im|) :
    offDiagonalBound S c Complex.im ≤ (2 * (M : ℝ) / gap) * ∑ ρ ∈ S, ‖c ρ‖ ^ 2 := by
  let D : ℝ := ∑ ρ ∈ S, ‖c ρ‖ ^ 2
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    exact Finset.sum_nonneg fun ρ hρ => sq_nonneg ‖c ρ‖
  have hpairBound :
      offDiagonalBound S c Complex.im ≤
        ∑ ρ₁ ∈ S, ∑ ρ₂ ∈ S.erase ρ₁, (2 / gap) * (‖c ρ₁‖ * ‖c ρ₂‖) := by
    dsimp [offDiagonalBound]
    apply Finset.sum_le_sum
    intro ρ₁ hρ₁
    apply Finset.sum_le_sum
    intro ρ₂ hρ₂
    have hne : ρ₁ ≠ ρ₂ := (Finset.ne_of_mem_erase hρ₂).symm
    have hsep : gap ≤ |ρ₂.im - ρ₁.im| :=
      hGap ρ₁ hρ₁ ρ₂ (Finset.mem_of_mem_erase hρ₂) hne
    have hgaprec : (1 / |ρ₂.im - ρ₁.im|) ≤ (1 / gap) :=
      one_div_le_one_div_of_le hGapPos hsep
    calc
      2 * ‖c ρ₁‖ * ‖c ρ₂‖ / |ρ₂.im - ρ₁.im| =
          (2 * ‖c ρ₁‖ * ‖c ρ₂‖) * (1 / |ρ₂.im - ρ₁.im|) := by
        ring_nf
      _ ≤ (2 * ‖c ρ₁‖ * ‖c ρ₂‖) * (1 / gap) := by
        exact mul_le_mul_of_nonneg_left hgaprec (by positivity)
      _ = (2 / gap) * (‖c ρ₁‖ * ‖c ρ₂‖) := by ring
  have hsum_pairs :
      ∑ ρ₁ ∈ S, ∑ ρ₂ ∈ S.erase ρ₁, ‖c ρ₁‖ * ‖c ρ₂‖ ≤ (∑ ρ ∈ S, ‖c ρ‖) ^ 2 := by
    calc
      ∑ ρ₁ ∈ S,
          ∑ ρ₂ ∈ S.erase ρ₁, ‖c ρ₁‖ * ‖c ρ₂‖ ≤
          ∑ ρ₁ ∈ S, ∑ ρ₂ ∈ S, ‖c ρ₁‖ * ‖c ρ₂‖ := by
        apply Finset.sum_le_sum
        intro ρ₁ hρ₁
        exact Finset.sum_le_sum_of_subset_of_nonneg (s := S.erase ρ₁) (t := S)
          (Finset.erase_subset ρ₁ S) (fun ρ₂ hρ₂ hρ₂' => by positivity)
      _ = ∑ ρ₁ ∈ S, (‖c ρ₁‖ * ∑ ρ₂ ∈ S, ‖c ρ₂‖) := by
        refine Finset.sum_congr rfl ?_
        intro ρ₁ hρ₁
        rw [Finset.mul_sum]
      _ = (∑ ρ ∈ S, ‖c ρ‖) * (∑ ρ ∈ S, ‖c ρ‖) := by
        rw [Finset.sum_mul]
      _ = (∑ ρ ∈ S, ‖c ρ‖) ^ 2 := by ring
  have hpairFactor :
      (2 / gap) * ∑ ρ₁ ∈ S, ∑ ρ₂ ∈ S.erase ρ₁, ‖c ρ₁‖ * ‖c ρ₂‖ =
        ∑ ρ₁ ∈ S, ∑ ρ₂ ∈ S.erase ρ₁, (2 / gap) * (‖c ρ₁‖ * ‖c ρ₂‖) := by
    calc
      (2 / gap) * ∑ ρ₁ ∈ S, ∑ ρ₂ ∈ S.erase ρ₁, ‖c ρ₁‖ * ‖c ρ₂‖
          = ∑ ρ₁ ∈ S, ((2 / gap) * (∑ ρ₂ ∈ S.erase ρ₁, ‖c ρ₁‖ * ‖c ρ₂‖)) := by
        simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
      _ = ∑ ρ₁ ∈ S, ∑ ρ₂ ∈ S.erase ρ₁, (2 / gap) * (‖c ρ₁‖ * ‖c ρ₂‖) := by
        refine Finset.sum_congr rfl ?_
        intro ρ₁ hρ₁
        simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  have hsum_sq : (∑ ρ ∈ S, ‖c ρ‖) ^ 2 ≤ (S.card : ℝ) * D := by
    simpa [D, pow_two] using
      (sq_sum_le_card_mul_sum_sq (s := S) (f := fun ρ => ‖c ρ‖))
  have hsum :
      ∑ ρ₁ ∈ S, ∑ ρ₂ ∈ S.erase ρ₁, ‖c ρ₁‖ * ‖c ρ₂‖ ≤ (S.card : ℝ) * D := by
    exact hsum_pairs.trans hsum_sq
  have hratio : (S.card : ℝ) * D ≤ (M : ℝ) * D := by
    nlinarith [hcard, hD_nonneg]
  have hcoef : (2 / gap) * ((S.card : ℝ) * D) ≤ (2 * (M : ℝ) / gap) * D := by
    have hcoef' : (2 / gap) * ((S.card : ℝ) * D) ≤ (2 / gap) * ((M : ℝ) * D) := by
      exact mul_le_mul_of_nonneg_left hratio (by positivity)
    calc
      (2 / gap) * ((S.card : ℝ) * D) ≤ (2 / gap) * ((M : ℝ) * D) := hcoef'
      _ = (2 * (M : ℝ) / gap) * D := by ring
  have hmul : (2 / gap) * (∑ ρ₁ ∈ S, ∑ ρ₂ ∈ S.erase ρ₁, ‖c ρ₁‖ * ‖c ρ₂‖) ≤
      (2 / gap) * ((S.card : ℝ) * D) := by
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  have hmul2 : (2 / gap) * (∑ ρ₁ ∈ S, ∑ ρ₂ ∈ S.erase ρ₁, ‖c ρ₁‖ * ‖c ρ₂‖) ≤
      (2 * (M : ℝ) / gap) * D := by
    exact le_trans hmul hcoef
  calc
    offDiagonalBound S c Complex.im ≤
        ∑ ρ₁ ∈ S, ∑ ρ₂ ∈ S.erase ρ₁, (2 / gap) * (‖c ρ₁‖ * ‖c ρ₂‖) := hpairBound
    _ = (2 / gap) * ∑ ρ₁ ∈ S, ∑ ρ₂ ∈ S.erase ρ₁, ‖c ρ₁‖ * ‖c ρ₂‖ := hpairFactor.symm
    _ ≤ (2 * (M : ℝ) / gap) * D := hmul2

theorem clustered_spectralLower_from_gap (h : ClusteredEnvelopeInput) :
    (∑ ρ ∈ equalRealPartZeroPackage h.T h.rho0.re,
        ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹‖ ^ 2) -
      offDiagonalBound (equalRealPartZeroPackage h.T h.rho0.re)
        (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹) Complex.im /
        (Real.log (h.Y ^ h.C) - Real.log h.Y) ≥
      (Real.pi / 2 + h.delta + h.epsilon) ^ 2 *
        ‖(analyticOrderNatAt riemannZeta h.rho0 : ℂ) * h.rho0⁻¹‖ ^ 2 := by
  have hOffDiag :
      offDiagonalBound (equalRealPartZeroPackage h.T h.rho0.re)
        (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹) Complex.im ≤
        (2 * (h.M : ℝ) / h.hClusterFrequencyGap) *
          ∑ ρ ∈ equalRealPartZeroPackage h.T h.rho0.re,
            ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹‖ ^ 2 := by
    exact clustered_offDiagonalBound_le_pairwise_gap (S := equalRealPartZeroPackage h.T h.rho0.re)
      (c := fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹)
      (M := h.M) (gap := h.hClusterFrequencyGap) h.hClusterFrequencyGapPos
      (by exact_mod_cast h.hFiniteVertical) h.hClusterPairwiseGap
  have hWindowPos : 0 < Real.log (h.Y ^ h.C) - Real.log h.Y := by
    exact sub_pos.mpr h.hWindow
  have hOffDiv :
      offDiagonalBound (equalRealPartZeroPackage h.T h.rho0.re)
        (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹) Complex.im /
          (Real.log (h.Y ^ h.C) - Real.log h.Y) ≤
        ((2 * (h.M : ℝ) / h.hClusterFrequencyGap) *
          ∑ ρ ∈ equalRealPartZeroPackage h.T h.rho0.re,
            ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹‖ ^ 2) /
          (Real.log (h.Y ^ h.C) - Real.log h.Y) := by
    exact div_le_div_of_nonneg_right hOffDiag hWindowPos.le
  nlinarith [h.hClusterGapLower, hOffDiv]

/-- Fixed-slope finite-envelope transfer for the half-isolated route. -/
theorem halfIsolatedEnvelopeBridge (h : HalfIsolatedEnvelopeInput) :
    HalfIsolatedConclusion h := by
  have hy := exists_mem_Ioo_sqNorm_equalRealPartZeroPackageContribution_ge
    (T := h.T) (β := h.rho0.re) h.hWindow
  rcases hy with ⟨y, hyIoo, hsq⟩

  let coeff : ℝ := ‖(analyticOrderNatAt riemannZeta h.rho0 : ℂ) * h.rho0⁻¹‖
  let pkg : ℝ :=
    (∑ ρ ∈ equalRealPartZeroPackage h.T h.rho0.re,
        ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹‖ ^ 2) -
      offDiagonalBound (equalRealPartZeroPackage h.T h.rho0.re)
        (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹) Complex.im /
        (Real.log (h.Y ^ h.C) - Real.log h.Y)

  have hcoeff_nonneg : 0 ≤ coeff := by
    dsimp [coeff]
    exact norm_nonneg _

  have hpkg_sq : (Real.pi / 2 + h.delta + h.epsilon) ^ 2 * coeff ^ 2 *
      Real.exp (h.rho0.re * y) ^ 2 ≤
      ‖equalRealPartZeroPackageContribution (Real.exp y) h.T h.rho0.re‖ ^ 2 := by
    have hmass : (Real.pi / 2 + h.delta + h.epsilon) ^ 2 * coeff ^ 2 ≤ pkg := by
      dsimp [coeff, pkg]
      nlinarith [h.hSpectralLower]
    have hmass_mul :
        (Real.exp (h.rho0.re * y) ^ 2) * ((Real.pi / 2 + h.delta + h.epsilon) ^ 2 * coeff ^ 2) ≤
          (Real.exp (h.rho0.re * y) ^ 2) * pkg := by
      exact mul_le_mul_of_nonneg_left hmass (sq_nonneg (Real.exp (h.rho0.re * y)))
    have hsq_pkg :
        (Real.exp (h.rho0.re * y) ^ 2) * pkg ≤
          ‖equalRealPartZeroPackageContribution (Real.exp y) h.T h.rho0.re‖ ^ 2 := by
      simpa [pkg, mul_assoc, mul_comm, mul_left_comm] using hsq
    nlinarith [hmass_mul, hsq_pkg]

  have hpkg_lower :
      (Real.pi / 2 + h.delta + h.epsilon) * coeff * Real.exp (h.rho0.re * y) ≤
        ‖equalRealPartZeroPackageContribution (Real.exp y) h.T h.rho0.re‖ := by
    have hterm_nonneg :
        0 ≤ (Real.pi / 2 + h.delta + h.epsilon) * coeff * Real.exp (h.rho0.re * y) := by
      have hA : 0 < Real.pi / 2 + h.delta + h.epsilon := by
        nlinarith [Real.pi_pos, h.hDelta, h.hEpsilonNonneg]
      have hexp : 0 ≤ Real.exp (h.rho0.re * y) := by positivity
      exact mul_nonneg (mul_nonneg (le_of_lt hA) hcoeff_nonneg) hexp
    have hpkg_nonneg :
        0 ≤ ‖equalRealPartZeroPackageContribution (Real.exp y) h.T h.rho0.re‖ := by
      exact norm_nonneg _
    have hsq_eq :
        ((Real.pi / 2 + h.delta + h.epsilon) * coeff * Real.exp (h.rho0.re * y)) ^ 2 =
          (Real.pi / 2 + h.delta + h.epsilon) ^ 2 * coeff ^ 2 *
            Real.exp (h.rho0.re * y) ^ 2 := by
      ring
    have hsq₂ : ((Real.pi / 2 + h.delta + h.epsilon) * coeff * Real.exp (h.rho0.re * y)) ^ 2 ≤
        ‖equalRealPartZeroPackageContribution (Real.exp y) h.T h.rho0.re‖ ^ 2 := by
      rw [hsq_eq]
      exact hpkg_sq
    have hsq_nonneg :
        0 ≤ (‖equalRealPartZeroPackageContribution (Real.exp y) h.T h.rho0.re‖ -
          (Real.pi / 2 + h.delta + h.epsilon) * coeff * Real.exp (h.rho0.re * y)) ^ 2 := by
      exact sq_nonneg _
    nlinarith [hterm_nonneg, hpkg_nonneg, hsq₂, hsq_nonneg]

  have hrem : ‖zeroPackageExplicitFormulaRemainder y h.T h.rho0.re‖ ≤ h.epsilon * coeff * Real.exp (h.rho0.re * y) := by
    have hyIcc : y ∈ Set.Icc (Real.log h.Y) (Real.log (h.Y ^ h.C)) := by
      exact ⟨le_of_lt hyIoo.1, le_of_lt hyIoo.2⟩
    simpa [coeff, mul_assoc, mul_comm, mul_left_comm] using h.hRemainderWindow y hyIcc

  have htransfer :=
    norm_zeroPackage_sub_norm_remainder_le_norm_chebyshevPsi0_sub_exp h.T h.rho0.re y
  have hdelta_gap :
      (Real.pi / 2 + h.delta) * coeff * Real.exp (h.rho0.re * y) ≤
        ‖((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ)‖ := by
    have hpkg_minus :
        (Real.pi / 2 + h.delta + h.epsilon) * coeff * Real.exp (h.rho0.re * y) -
          h.epsilon * coeff * Real.exp (h.rho0.re * y) ≤
            ‖equalRealPartZeroPackageContribution (Real.exp y) h.T h.rho0.re‖ -
              ‖zeroPackageExplicitFormulaRemainder y h.T h.rho0.re‖ := by
      nlinarith [hrem, hpkg_lower, hcoeff_nonneg]
    have hdrop :
        (Real.pi / 2 + h.delta) * coeff * Real.exp (h.rho0.re * y) ≤
          (Real.pi / 2 + h.delta + h.epsilon) * coeff * Real.exp (h.rho0.re * y) -
            h.epsilon * coeff * Real.exp (h.rho0.re * y) := by
      have hnonneg : 0 ≤ h.epsilon * coeff * Real.exp (h.rho0.re * y) := by
        exact mul_nonneg (mul_nonneg h.hEpsilonNonneg hcoeff_nonneg) (by positivity)
      have hA : 0 ≤ Real.pi / 2 + h.delta := by nlinarith [h.hDelta, Real.pi_pos]
      have htmp :
          (Real.pi / 2 + h.delta) * coeff * Real.exp (h.rho0.re * y) =
            (Real.pi / 2 + h.delta + h.epsilon) * coeff * Real.exp (h.rho0.re * y) -
              h.epsilon * coeff * Real.exp (h.rho0.re * y) := by
        ring
      nlinarith [htmp]
    have htmp :
        (Real.pi / 2 + h.delta + h.epsilon) * coeff * Real.exp (h.rho0.re * y) -
          h.epsilon * coeff * Real.exp (h.rho0.re * y) ≤
            ‖((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ)‖ := by
      nlinarith [hpkg_minus, htransfer]
    linarith

  have hcoeff :
      (Real.pi / 2 + h.delta) * (Real.exp (h.rho0.re * y) / max 1 ‖h.rho0‖) ≤
        (Real.pi / 2 + h.delta) * coeff * Real.exp (h.rho0.re * y) := by
    have hpi_nonneg : 0 ≤ Real.pi / 2 + h.delta := by
      nlinarith [h.hDelta, Real.pi_pos]
    have hmult : (1 / max 1 ‖h.rho0‖) * Real.exp (h.rho0.re * y) ≤
        coeff * Real.exp (h.rho0.re * y) := by
      exact mul_le_mul_of_nonneg_right h.hCoeffLower (by positivity)
    have hmul := mul_le_mul_of_nonneg_left hmult hpi_nonneg
    calc
      (Real.pi / 2 + h.delta) * (Real.exp (h.rho0.re * y) / max 1 ‖h.rho0‖)
          = (Real.pi / 2 + h.delta) * ((1 / max 1 ‖h.rho0‖) * Real.exp (h.rho0.re * y)) := by
            ring
      _ ≤ (Real.pi / 2 + h.delta) * (coeff * Real.exp (h.rho0.re * y)) := hmul
      _ = (Real.pi / 2 + h.delta) * coeff * Real.exp (h.rho0.re * y) := by ring

  have hfinal_log :
      (Real.pi / 2 + h.delta) * (Real.exp (h.rho0.re * Real.log (Real.exp y)) / max 1 ‖h.rho0‖) ≤
        ‖((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ)‖ := by
    have hcoeff' :
        (Real.pi / 2 + h.delta) * (Real.exp (h.rho0.re * y) / max 1 ‖h.rho0‖) ≤
          ‖((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ)‖ :=
      hcoeff.trans hdelta_gap
    have hlogexp : Real.log (Real.exp y) = y := by simp
    simpa [hlogexp] using hcoeff'

  refine ⟨Real.exp y, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · have hYpos : 0 < h.Y := lt_trans zero_lt_one h.hY
      have hyL : Real.log h.Y ≤ y := le_of_lt hyIoo.1
      calc
        h.Y = Real.exp (Real.log h.Y) := (Real.exp_log hYpos).symm
        _ ≤ Real.exp y := Real.exp_le_exp.mpr hyL
    · have hYCpos : 0 < h.Y ^ h.C := by
        exact pow_pos (lt_trans zero_lt_one h.hY) h.C
      have hyU : y ≤ Real.log (h.Y ^ h.C) := le_of_lt hyIoo.2
      have hlogYC : Real.exp y ≤ Real.exp (Real.log (h.Y ^ h.C)) := Real.exp_le_exp.mpr hyU
      calc
        Real.exp y ≤ Real.exp (Real.log (h.Y ^ h.C)) := hlogYC
        _ = h.Y ^ h.C := Real.exp_log hYCpos
  · have hlogexp : Real.log (Real.exp y) = y := by simp
    simpa [hlogexp] using hfinal_log

theorem clusteredEnvelopeBridge (h : ClusteredEnvelopeInput) :
    ClusteredConclusion h := by
  have hspectral :
      (∑ ρ ∈ equalRealPartZeroPackage h.T h.rho0.re,
          ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹‖ ^ 2) -
        offDiagonalBound (equalRealPartZeroPackage h.T h.rho0.re)
          (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹) Complex.im /
          (Real.log (h.Y ^ h.C) - Real.log h.Y) ≥
      (Real.pi / 2 + h.delta + h.epsilon) ^ 2 *
        ‖(analyticOrderNatAt riemannZeta h.rho0 : ℂ) * h.rho0⁻¹‖ ^ 2 :=
    clustered_spectralLower_from_gap h
  have hy := exists_mem_Ioo_sqNorm_equalRealPartZeroPackageContribution_ge
    (T := h.T) (β := h.rho0.re) h.hWindow
  rcases hy with ⟨y, hyIoo, hsq⟩

  let coeff : ℝ := ‖(analyticOrderNatAt riemannZeta h.rho0 : ℂ) * h.rho0⁻¹‖
  let pkg : ℝ :=
    (∑ ρ ∈ equalRealPartZeroPackage h.T h.rho0.re,
        ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹‖ ^ 2) -
      offDiagonalBound (equalRealPartZeroPackage h.T h.rho0.re)
        (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹) Complex.im /
        (Real.log (h.Y ^ h.C) - Real.log h.Y)

  have hcoeff_nonneg : 0 ≤ coeff := by
    dsimp [coeff]
    exact norm_nonneg _

  have hpkg_sq : (Real.pi / 2 + h.delta + h.epsilon) ^ 2 * coeff ^ 2 *
      Real.exp (h.rho0.re * y) ^ 2 ≤
        ‖equalRealPartZeroPackageContribution (Real.exp y) h.T h.rho0.re‖ ^ 2 := by
    have hmass : (Real.pi / 2 + h.delta + h.epsilon) ^ 2 * coeff ^ 2 ≤ pkg := by
      dsimp [coeff, pkg]
      nlinarith [hspectral]
    have hmass_mul :
        (Real.exp (h.rho0.re * y) ^ 2) * ((Real.pi / 2 + h.delta + h.epsilon) ^ 2 * coeff ^ 2) ≤
          (Real.exp (h.rho0.re * y) ^ 2) * pkg := by
      exact mul_le_mul_of_nonneg_left hmass (sq_nonneg (Real.exp (h.rho0.re * y)))
    have hsq_pkg :
        (Real.exp (h.rho0.re * y) ^ 2) * pkg ≤
          ‖equalRealPartZeroPackageContribution (Real.exp y) h.T h.rho0.re‖ ^ 2 := by
      simpa [pkg, mul_assoc, mul_comm, mul_left_comm] using hsq
    nlinarith [hmass_mul, hsq_pkg]

  have hpkg_lower :
      (Real.pi / 2 + h.delta + h.epsilon) * coeff * Real.exp (h.rho0.re * y) ≤
        ‖equalRealPartZeroPackageContribution (Real.exp y) h.T h.rho0.re‖ := by
    have hterm_nonneg :
        0 ≤ (Real.pi / 2 + h.delta + h.epsilon) * coeff * Real.exp (h.rho0.re * y) := by
      have hA : 0 < Real.pi / 2 + h.delta + h.epsilon := by
        nlinarith [Real.pi_pos, h.hDelta, h.hEpsilonNonneg]
      have hexp : 0 ≤ Real.exp (h.rho0.re * y) := by positivity
      exact mul_nonneg (mul_nonneg (le_of_lt hA) hcoeff_nonneg) hexp
    have hpkg_nonneg :
        0 ≤ ‖equalRealPartZeroPackageContribution (Real.exp y) h.T h.rho0.re‖ := by
      exact norm_nonneg _
    have hsq_eq :
        ((Real.pi / 2 + h.delta + h.epsilon) * coeff * Real.exp (h.rho0.re * y)) ^ 2 =
          (Real.pi / 2 + h.delta + h.epsilon) ^ 2 * coeff ^ 2 *
            Real.exp (h.rho0.re * y) ^ 2 := by
      ring
    have hsq₂ : ((Real.pi / 2 + h.delta + h.epsilon) * coeff * Real.exp (h.rho0.re * y)) ^ 2 ≤
        ‖equalRealPartZeroPackageContribution (Real.exp y) h.T h.rho0.re‖ ^ 2 := by
      rw [hsq_eq]
      exact hpkg_sq
    have hsq_nonneg :
        0 ≤ (‖equalRealPartZeroPackageContribution (Real.exp y) h.T h.rho0.re‖ -
          (Real.pi / 2 + h.delta + h.epsilon) * coeff * Real.exp (h.rho0.re * y)) ^ 2 := by
      exact sq_nonneg _
    nlinarith [hterm_nonneg, hpkg_nonneg, hsq₂, hsq_nonneg]

  have hrem : ‖zeroPackageExplicitFormulaRemainder y h.T h.rho0.re‖ ≤ h.epsilon * coeff * Real.exp (h.rho0.re * y) := by
    have hyIcc : y ∈ Set.Icc (Real.log h.Y) (Real.log (h.Y ^ h.C)) := by
      exact ⟨le_of_lt hyIoo.1, le_of_lt hyIoo.2⟩
    simpa [coeff, mul_assoc, mul_comm, mul_left_comm] using h.hRemainderWindow y hyIcc

  have htransfer :=
    norm_zeroPackage_sub_norm_remainder_le_norm_chebyshevPsi0_sub_exp h.T h.rho0.re y

  have hdelta_gap :
      (Real.pi / 2 + h.delta) * coeff * Real.exp (h.rho0.re * y) ≤
        ‖((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ)‖ := by
    have hpkg_minus :
        (Real.pi / 2 + h.delta + h.epsilon) * coeff * Real.exp (h.rho0.re * y) -
          h.epsilon * coeff * Real.exp (h.rho0.re * y) ≤
            ‖equalRealPartZeroPackageContribution (Real.exp y) h.T h.rho0.re‖ -
              ‖zeroPackageExplicitFormulaRemainder y h.T h.rho0.re‖ := by
      nlinarith [hrem, hpkg_lower, hcoeff_nonneg]
    have hdrop :
        (Real.pi / 2 + h.delta) * coeff * Real.exp (h.rho0.re * y) ≤
          (Real.pi / 2 + h.delta + h.epsilon) * coeff * Real.exp (h.rho0.re * y) -
            h.epsilon * coeff * Real.exp (h.rho0.re * y) := by
      have hnonneg : 0 ≤ h.epsilon * coeff * Real.exp (h.rho0.re * y) := by
        exact mul_nonneg (mul_nonneg h.hEpsilonNonneg hcoeff_nonneg) (by positivity)
      have htmp :
          (Real.pi / 2 + h.delta) * coeff * Real.exp (h.rho0.re * y) =
            (Real.pi / 2 + h.delta + h.epsilon) * coeff * Real.exp (h.rho0.re * y) -
              h.epsilon * coeff * Real.exp (h.rho0.re * y) := by
        ring
      nlinarith [htmp]
    have htmp :
        (Real.pi / 2 + h.delta + h.epsilon) * coeff * Real.exp (h.rho0.re * y) -
          h.epsilon * coeff * Real.exp (h.rho0.re * y) ≤
            ‖((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ)‖ := by
      nlinarith [hpkg_minus, htransfer]
    linarith

  have hcoeff :
      (Real.pi / 2 + h.delta) * (Real.exp (h.rho0.re * y) / max 1 ‖h.rho0‖) ≤
        (Real.pi / 2 + h.delta) * coeff * Real.exp (h.rho0.re * y) := by
    have hpi_nonneg : 0 ≤ Real.pi / 2 + h.delta := by
      nlinarith [h.hDelta, Real.pi_pos]
    have hmult : (1 / max 1 ‖h.rho0‖) * Real.exp (h.rho0.re * y) ≤
        coeff * Real.exp (h.rho0.re * y) := by
      exact mul_le_mul_of_nonneg_right h.hCoeffLower (by positivity)
    have hmul := mul_le_mul_of_nonneg_left hmult hpi_nonneg
    calc
      (Real.pi / 2 + h.delta) * (Real.exp (h.rho0.re * y) / max 1 ‖h.rho0‖)
          = (Real.pi / 2 + h.delta) * ((1 / max 1 ‖h.rho0‖) * Real.exp (h.rho0.re * y)) := by
            ring
      _ ≤ (Real.pi / 2 + h.delta) * (coeff * Real.exp (h.rho0.re * y)) := hmul
      _ = (Real.pi / 2 + h.delta) * coeff * Real.exp (h.rho0.re * y) := by ring

  have hfinal_log :
      (Real.pi / 2 + h.delta) * (Real.exp (h.rho0.re * Real.log (Real.exp y)) / max 1 ‖h.rho0‖) ≤
        ‖((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ)‖ := by
    have hcoeff' :
        (Real.pi / 2 + h.delta) * (Real.exp (h.rho0.re * y) / max 1 ‖h.rho0‖) ≤
          ‖((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ)‖ :=
      hcoeff.trans hdelta_gap
    have hlogexp : Real.log (Real.exp y) = y := by simp
    simpa [hlogexp] using hcoeff'

  refine ⟨Real.exp y, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · have hYpos : 0 < h.Y := lt_trans zero_lt_one h.hY
      have hyL : Real.log h.Y ≤ y := le_of_lt hyIoo.1
      calc
        h.Y = Real.exp (Real.log h.Y) := (Real.exp_log hYpos).symm
        _ ≤ Real.exp y := Real.exp_le_exp.mpr hyL
    · have hYCpos : 0 < h.Y ^ h.C := by
        exact pow_pos (lt_trans zero_lt_one h.hY) h.C
      have hyU : y ≤ Real.log (h.Y ^ h.C) := le_of_lt hyIoo.2
      have hlogYC : Real.exp y ≤ Real.exp (Real.log (h.Y ^ h.C)) := Real.exp_le_exp.mpr hyU
      calc
        Real.exp y ≤ Real.exp (Real.log (h.Y ^ h.C)) := hlogYC
        _ = h.Y ^ h.C := Real.exp_log hYCpos
  · have hlogexp : Real.log (Real.exp y) = y := by simp
    simpa [hlogexp] using hfinal_log

end VKEdgeConditionalPackage
end PrimeNumberTheorem
