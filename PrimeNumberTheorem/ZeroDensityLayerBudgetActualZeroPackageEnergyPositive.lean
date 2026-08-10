import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZeroPackageCarlsonTransfer

/-!
# Positivity of the actual equal-real-part zero-package energy

This file removes one avoidable external hypothesis from the actual
zero-package/Carlson transfer.  The mean-square energy is positive whenever
the off-diagonal budget is smaller than `L` times the diagonal energy.
Moreover, positivity of the diagonal energy alone permits an explicit choice
of a sufficiently large positive window length `L`.

No zero-density estimate or positivity of a particular zeta-zero package is
asserted here.  Those remain separate mathematical inputs.
-/

namespace PrimeNumberTheorem

open ZeroForcedOscillation

noncomputable def actualEqualRealPartZeroPackageDiagonalEnergy
    (T beta : ℝ) : ℝ :=
  ∑ rho ∈ equalRealPartZeroPackage T beta,
    ‖(analyticOrderNatAt riemannZeta rho : ℂ) * rho⁻¹‖ ^ 2

/-- The exact off-diagonal comparison needed for positivity of the
actual equal-real-part package energy. -/
theorem actualEqualRealPartZeroPackageEnergy_pos_of_offDiagonal_lt
    {T beta L : ℝ} (hL : 0 < L)
    (hbudget :
      offDiagonalBound (equalRealPartZeroPackage T beta)
          (fun rho =>
            (analyticOrderNatAt riemannZeta rho : ℂ) * rho⁻¹)
          Complex.im <
        L * actualEqualRealPartZeroPackageDiagonalEnergy T beta) :
    0 < actualEqualRealPartZeroPackageEnergy T beta L := by
  have hdiv :
      offDiagonalBound (equalRealPartZeroPackage T beta)
            (fun rho =>
              (analyticOrderNatAt riemannZeta rho : ℂ) * rho⁻¹)
            Complex.im /
          L <
        actualEqualRealPartZeroPackageDiagonalEnergy T beta := by
    apply (div_lt_iff₀ hL).2
    simpa [mul_comm] using hbudget
  exact sub_pos.mpr (by
    simpa [actualEqualRealPartZeroPackageEnergy,
      actualEqualRealPartZeroPackageDiagonalEnergy] using hdiv)

/-- A positive diagonal energy always admits a positive window length for
which the actual package energy is positive. -/
theorem exists_actualEqualRealPartZeroPackageEnergy_pos
    {T beta : ℝ}
    (hdiagonal :
      0 < actualEqualRealPartZeroPackageDiagonalEnergy T beta) :
    ∃ L : ℝ, 0 < L ∧
      0 < actualEqualRealPartZeroPackageEnergy T beta L := by
  let D := actualEqualRealPartZeroPackageDiagonalEnergy T beta
  let B :=
    offDiagonalBound (equalRealPartZeroPackage T beta)
      (fun rho =>
        (analyticOrderNatAt riemannZeta rho : ℂ) * rho⁻¹)
      Complex.im
  let L := max 1 (B / D + 1)
  have hD : 0 < D := by
    simpa [D] using hdiagonal
  have hL : 0 < L := by
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hratio : B / D < L := by
    exact lt_of_lt_of_le (lt_add_one (B / D)) (le_max_right _ _)
  have hbudget : B < L * D := (div_lt_iff₀ hD).1 hratio
  refine ⟨L, hL, actualEqualRealPartZeroPackageEnergy_pos_of_offDiagonal_lt hL ?_⟩
  simpa [B, D] using hbudget

/-- Every member of the actual package contributes a strictly positive
diagonal term, so a nonempty package has positive diagonal energy. -/
theorem actualEqualRealPartZeroPackageDiagonalEnergy_pos_of_nonempty
    {T beta : ℝ}
    (hnonempty : (equalRealPartZeroPackage T beta).Nonempty) :
    0 < actualEqualRealPartZeroPackageDiagonalEnergy T beta := by
  unfold actualEqualRealPartZeroPackageDiagonalEnergy
  apply Finset.sum_pos
  · intro rho hrho
    have hmem := mem_equalRealPartZeroPackage.mp hrho
    rcases hmem.1 with ⟨hzeta, hre_pos, hre_lt⟩
    have hrho_zero : rho ≠ 0 := by
      intro hz
      have hzre := congrArg Complex.re hz
      simp only [Complex.zero_re] at hzre
      linarith
    have hrho_one : rho ≠ 1 := by
      intro hone
      have honere := congrArg Complex.re hone
      norm_num at honere
      linarith
    have horder : 0 < analyticOrderNatAt riemannZeta rho :=
      ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero
        hrho_one hzeta
    have horder_ne :
        (analyticOrderNatAt riemannZeta rho : ℂ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt horder
    exact pow_pos
      (norm_pos_iff.mpr (mul_ne_zero horder_ne (inv_ne_zero hrho_zero))) 2
  · exact hnonempty

/-- A specified nontrivial zeta zero belongs to its equal-real-part package
as soon as the package height covers its ordinate. -/
theorem equalRealPartZeroPackage_nonempty_of_nontrivialZero
    {rho : ℂ} {T : ℝ}
    (hzero : RiemannHypothesis.IsNontrivialZero rho)
    (hT : |rho.im| ≤ T) :
    (equalRealPartZeroPackage T rho.re).Nonempty := by
  exact ⟨rho, mem_equalRealPartZeroPackage.mpr ⟨hzero, hT, rfl⟩⟩

/-- Nonemptiness of the actual equal-real-part package is enough to choose a
positive window length with positive mean-square energy. -/
theorem exists_actualEqualRealPartZeroPackageEnergy_pos_of_nonempty
    {T beta : ℝ}
    (hnonempty : (equalRealPartZeroPackage T beta).Nonempty) :
    ∃ L : ℝ, 0 < L ∧
      0 < actualEqualRealPartZeroPackageEnergy T beta L :=
  exists_actualEqualRealPartZeroPackageEnergy_pos
    (actualEqualRealPartZeroPackageDiagonalEnergy_pos_of_nonempty hnonempty)

/-- A specified covered nontrivial zeta zero is enough to choose a positive
mean-square window for its full equal-real-part package. -/
theorem exists_actualEqualRealPartZeroPackageEnergy_pos_of_nontrivialZero
    {rho : ℂ} {T : ℝ}
    (hzero : RiemannHypothesis.IsNontrivialZero rho)
    (hT : |rho.im| ≤ T) :
    ∃ L : ℝ, 0 < L ∧
      0 < actualEqualRealPartZeroPackageEnergy T rho.re L :=
  exists_actualEqualRealPartZeroPackageEnergy_pos_of_nonempty
    (equalRealPartZeroPackage_nonempty_of_nontrivialZero hzero hT)

/-- The actual zero-package/Carlson transfer with the window length chosen
from positivity of the diagonal energy rather than supplied together with a
separate package-energy hypothesis. -/
theorem unified_parametricPNTUpper_actualZeroPackageCarlsonLower_of_diagonalEnergy_pos
    (threshold : ℝ) (hhalf : 1 / 2 < threshold) (hlt : threshold < 1)
    {T beta alpha : ℝ} (hbeta : 0 < beta)
    (hdiagonal :
      0 < actualEqualRealPartZeroPackageDiagonalEnergy T beta)
    (hmargin : 1 - beta < alpha)
    {n : ℕ}
    {input : (x : ℝ) →
      PositiveZeroOutsideClusterBucketInput
        (carlsonPolynomialHeight alpha x)
        (equalRealPartZeroPackage T beta) n}
    (certificate :
      ActualCarlsonOutsideClusterFiniteStripCertificate beta alpha
        (equalRealPartZeroPackage T beta) n input)
    (remainderCertificate :
      ActualPolynomialExplicitFormulaRemainderCertificate alpha) :
    ∃ L : ℝ, 0 < L ∧
      ((∃ rate : ℝ, 0 < rate ∧ rate ≤ 1 ∧
          Filter.Tendsto
            (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
            Filter.atTop (nhds 0)) ∧
        HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
          (fun x =>
            Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L) *
                targetZeroPowerAmplitude beta x /
              2)) := by
  obtain ⟨L, hL, henergy⟩ :=
    exists_actualEqualRealPartZeroPackageEnergy_pos hdiagonal
  exact ⟨L, hL,
    unified_parametricPNTUpper_actualZeroPackageEnergyCarlsonLower
      threshold hhalf hlt hbeta L hL henergy hmargin certificate
        remainderCertificate⟩

/-- The actual zero-package/Carlson transfer with its mean-square window
chosen automatically from nonemptiness of the equal-real-part package. -/
theorem unified_parametricPNTUpper_actualZeroPackageCarlsonLower_of_nonempty
    (threshold : ℝ) (hhalf : 1 / 2 < threshold) (hlt : threshold < 1)
    {T beta alpha : ℝ} (hbeta : 0 < beta)
    (hnonempty : (equalRealPartZeroPackage T beta).Nonempty)
    (hmargin : 1 - beta < alpha)
    {n : ℕ}
    {input : (x : ℝ) →
      PositiveZeroOutsideClusterBucketInput
        (carlsonPolynomialHeight alpha x)
        (equalRealPartZeroPackage T beta) n}
    (certificate :
      ActualCarlsonOutsideClusterFiniteStripCertificate beta alpha
        (equalRealPartZeroPackage T beta) n input)
    (remainderCertificate :
      ActualPolynomialExplicitFormulaRemainderCertificate alpha) :
    ∃ L : ℝ, 0 < L ∧
      ((∃ rate : ℝ, 0 < rate ∧ rate ≤ 1 ∧
          Filter.Tendsto
            (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
            Filter.atTop (nhds 0)) ∧
        HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
          (fun x =>
            Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L) *
                targetZeroPowerAmplitude beta x /
              2)) :=
  unified_parametricPNTUpper_actualZeroPackageCarlsonLower_of_diagonalEnergy_pos
    threshold hhalf hlt hbeta
      (actualEqualRealPartZeroPackageDiagonalEnergy_pos_of_nonempty hnonempty)
      hmargin certificate remainderCertificate

end PrimeNumberTheorem
