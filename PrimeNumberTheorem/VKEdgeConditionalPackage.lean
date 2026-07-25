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
  Y : ℝ
  C : ℕ
  M : ℕ
  delta : ℝ
  hRho : RiemannHypothesis.IsNontrivialZero rho0
  hY : 1 ≤ Y
  hC : 1 ≤ C
  hM : 1 ≤ M
  hDelta : 0 < delta
  hFiniteVertical : Prop
  hLocalApprox : Prop
  hTailDominance : Prop
  hClusterDecomposition : Prop
  hClusterMoment : Prop
  hSpectralInvertibility : Prop

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
  · have hYpos : 0 < h.Y := lt_trans zero_lt_one h.hY
    have hyL : Real.log h.Y ≤ y := le_of_lt hyIoo.1
    have hyU : y ≤ Real.log (h.Y ^ h.C) := le_of_lt hyIoo.2
    have hxL : h.Y ≤ Real.exp y := by
      have hlogY : Real.exp (Real.log h.Y) ≤ Real.exp y := Real.exp_le_exp.mpr hyL
      have hYlog : Real.exp (Real.log h.Y) = h.Y := Real.exp_log hYpos
      simpa [hYlog] using hlogY
    have hxU : Real.exp y ≤ h.Y ^ h.C := by
      have hlogYC : Real.exp y ≤ Real.exp (Real.log (h.Y ^ h.C)) := Real.exp_le_exp.mpr hyU
      have hYCpos : 0 < h.Y ^ h.C := by positivity
      calc
        Real.exp y ≤ Real.exp (Real.log (h.Y ^ h.C)) := hlogYC
        _ = h.Y ^ h.C := Real.exp_log hYCpos
    exact ⟨hxL, hxU⟩
  · have hlogexp : Real.log (Real.exp y) = y := by simp
    simpa [hlogexp] using hfinal_log

/-!
`clusteredEnvelopeBridge` is not closed in this branch.

The clustered-route closure is deferred to a follow-up branch; all missing clustered
input assumptions and blockers are documented in
`docs/research/vk-edge-conditional-package-audit.md` and `docs/research/vk-edge-conditional-package-zeta-bridge.md`.
-/

end VKEdgeConditionalPackage
end PrimeNumberTheorem
