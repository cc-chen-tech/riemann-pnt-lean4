import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZeroPackageEnergyPositive

/-!
# Quantitative actual zero-package energy windows

The existing positivity theorem chooses a smoothing window whose normalized
off-diagonal contribution is smaller than the full diagonal energy.  The same
construction works with any strict target below the diagonal energy and gives
a quantitative lower bound for the resulting package energy.
-/

namespace PrimeNumberTheorem

open ZeroForcedOscillation

noncomputable section

/-- Every strict lower target below the diagonal energy is achieved by the
actual package energy for a sufficiently large positive window. -/
theorem exists_actualEqualRealPartZeroPackageEnergy_gt
    {T beta d : ℝ}
    (hd : d < actualEqualRealPartZeroPackageDiagonalEnergy T beta) :
    ∃ L : ℝ, 0 < L ∧
      d < actualEqualRealPartZeroPackageEnergy T beta L := by
  let D := actualEqualRealPartZeroPackageDiagonalEnergy T beta
  let B :=
    offDiagonalBound (equalRealPartZeroPackage T beta)
      (fun rho =>
        (analyticOrderNatAt riemannZeta rho : ℂ) * rho⁻¹)
      Complex.im
  let gap := D - d
  let L := max 1 (B / gap + 1)
  have hgap : 0 < gap := by
    dsimp [gap, D]
    linarith
  have hL : 0 < L :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hratio : B / gap < L :=
    lt_of_lt_of_le (lt_add_one (B / gap)) (le_max_right _ _)
  have hB : B < L * gap := (div_lt_iff₀ hgap).1 hratio
  have hdiv : B / L < gap := by
    apply (div_lt_iff₀ hL).2
    simpa [mul_comm] using hB
  refine ⟨L, hL, ?_⟩
  change d < D - B / L
  dsimp [gap] at hdiv
  linarith

/-- A positive diagonal energy admits a window retaining more than half of
that diagonal energy. -/
theorem exists_actualEqualRealPartZeroPackageEnergy_gt_diagonal_half
    {T beta : ℝ}
    (hdiagonal :
      0 < actualEqualRealPartZeroPackageDiagonalEnergy T beta) :
    ∃ L : ℝ, 0 < L ∧
      actualEqualRealPartZeroPackageDiagonalEnergy T beta / 2 <
        actualEqualRealPartZeroPackageEnergy T beta L := by
  apply exists_actualEqualRealPartZeroPackageEnergy_gt
  linarith

end
end PrimeNumberTheorem
