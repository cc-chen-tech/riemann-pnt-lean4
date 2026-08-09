import HardyTheorem.SelbergSqrtZetaSignedAutocorrelationShiftBudgetL2
import HardyTheorem.SelbergSqrtZetaSignedModelL2
import HardyTheorem.SelbergSqrtZetaSignedTotalShiftBudget
import HardyTheorem.SelbergSqrtZetaSignedPseudoLeOrdinary

/-!
# Explicit L2 total shift budget for the signed Selberg model

This module discharges the abstract square-mass inputs in the L2
autocorrelation transfer.  The actual and finite-model masses are replaced by
their explicit dyadic budgets.  The pseudo-correlation is then dominated by
the ordinary conjugate correlation, leaving only the ordinary-gap and
diagonal budgets.
-/

open Complex MeasureTheory Set

namespace HardyTheorem

/-- The L2 cost of replacing the actual mollified Hardy function by the finite
theta model on the shift square. -/
noncomputable def selbergSqrtZetaSignedModelTransferShiftBudgetL2
    (Cactual Ctransfer T : ℝ) (X : ℕ) (H : ℝ) : ℝ :=
  H ^ 2 * (4 * Ctransfer * X / Real.sqrt T) *
    Real.sqrt (T - H) *
    (Real.sqrt (selbergSqrtZetaSignedActualL2Budget Cactual T X) +
      Real.sqrt (selbergSqrtZetaSignedModelL2Budget T X))

/-- The complete L2-based shift-square budget after the pseudo-correlation is
absorbed into the ordinary conjugate correlation. -/
noncomputable def selbergSqrtZetaSignedTotalShiftBudgetL2
    (Cactual Ctransfer T : ℝ) (X : ℕ) (H : ℝ) : ℝ :=
  selbergSqrtZetaSignedModelTransferShiftBudgetL2
      Cactual Ctransfer T X H +
    selbergSqrtZetaSignedOrdinaryGapShiftBudget T X H +
    selbergSqrtZetaSignedDiagonalShiftBudget T X H

/-- The actual mollified autocorrelation has a completely explicit L2-based
shift-square budget.  No abstract model supremum or square-mass parameter
remains in the statement. -/
theorem
    exists_abs_integral_integral_integral_selbergSqrtZetaMollifiedAutocorrelation_le_totalShiftBudgetL2 :
    ∃ Cactual Ctransfer T0 : ℝ,
      0 ≤ Cactual ∧ 0 ≤ Ctransfer ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T H : ℝ,
        T0 ≤ T → 0 ≤ H → H ≤ T →
        |∫ v in 0..H, ∫ w in 0..H, ∫ t in T..2 * T - H,
            selbergSqrtZetaMollifiedHardyZ X (t + v) *
              selbergSqrtZetaMollifiedHardyZ X (t + w)| ≤
          selbergSqrtZetaSignedTotalShiftBudgetL2
            Cactual Ctransfer T X H := by
  obtain ⟨Cactual, T0actual, hCactual, hT0actual, hactualMass⟩ :=
    exists_integral_sq_selbergSqrtZetaMollifiedHardyZ_le_actualL2Budget
  obtain ⟨kappa, Ctransfer, T0transfer, hCtransfer, hT0transfer,
      htransfer⟩ :=
    exists_abs_integral_integral_integral_selbergSqrtZetaMollifiedAutocorrelation_sub_signedThetaModel_le_L2
  refine ⟨Cactual, Ctransfer, max T0actual T0transfer,
    hCactual, hCtransfer, hT0actual.trans (le_max_left _ _), ?_⟩
  intro X hX T H hT hH hHT
  have hTactual : T0actual ≤ T :=
    (le_max_left T0actual T0transfer).trans hT
  have hTtransfer : T0transfer ≤ T :=
    (le_max_right T0actual T0transfer).trans hT
  have hTone : 1 ≤ T := hT0actual.trans hTactual
  have hTpos : 0 < T := zero_lt_one.trans_le hTone
  let actual : ℝ :=
    ∫ v in 0..H, ∫ w in 0..H, ∫ t in T..2 * T - H,
      selbergSqrtZetaMollifiedHardyZ X (t + v) *
        selbergSqrtZetaMollifiedHardyZ X (t + w)
  let model : ℝ :=
    ∫ v in 0..H, ∫ w in 0..H, ∫ t in T..2 * T - H,
      selbergSqrtZetaSignedThetaModel kappa T X (t + v) *
        selbergSqrtZetaSignedThetaModel kappa T X (t + w)
  let ordinary : ℂ :=
    ∫ v in 0..H, ∫ w in 0..H, ∫ t in T..2 * T - H,
      selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
        (starRingEnd ℂ)
          (selbergSqrtZetaSignedComplexModel kappa T X (t + w))
  let pseudo : ℂ :=
    ∫ v in 0..H, ∫ w in 0..H, ∫ t in T..2 * T - H,
      selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
        selbergSqrtZetaSignedComplexModel kappa T X (t + w)
  have hactualDyadic :
      (∫ x in T..2 * T,
        selbergSqrtZetaMollifiedHardyZ X x ^ 2) ≤
          selbergSqrtZetaSignedActualL2Budget Cactual T X :=
    hactualMass X hX T hTactual
  have hmodelDyadic :
      (∫ x in T..2 * T,
        selbergSqrtZetaSignedThetaModel kappa T X x ^ 2) ≤
          selbergSqrtZetaSignedModelL2Budget T X :=
    integral_sq_selbergSqrtZetaSignedThetaModel_le_modelL2Budget
      kappa T X hTpos
  have htransfer' :
      |actual - model| ≤
        selbergSqrtZetaSignedModelTransferShiftBudgetL2
          Cactual Ctransfer T X H := by
    simpa only [actual, model,
      selbergSqrtZetaSignedModelTransferShiftBudgetL2] using
      htransfer X hX T H
        (selbergSqrtZetaSignedActualL2Budget Cactual T X)
        (selbergSqrtZetaSignedModelL2Budget T X)
        hTtransfer hH hHT hactualDyadic hmodelDyadic
  have hmodelSplit :
      |model| ≤
        selbergSqrtZetaSignedOrdinaryGapShiftBudget T X H +
          selbergSqrtZetaSignedDiagonalShiftBudget T X H := by
    have hdecomp :=
      abs_integral_integral_integral_selbergSqrtZetaSignedThetaModel_mul_shift_le
        kappa T X hTpos hH hHT
    have hord :=
      norm_integral_integral_integral_selbergSqrtZetaSignedOrdinaryCorrelation_le
        kappa T X hTpos hH hHT
    have hpseudo :=
      norm_integral_integral_integral_selbergSqrtZetaSignedComplexModel_mul_shift_le_conj_shift
        kappa T X hTpos hH hHT
    have hdecomp' :
        |model| ≤ (‖ordinary‖ + ‖pseudo‖) / 2 := by
      simpa only [model, ordinary, pseudo] using hdecomp
    have hpseudo' : ‖pseudo‖ ≤ ‖ordinary‖ := by
      simpa only [ordinary, pseudo] using hpseudo
    have hord' :
        ‖ordinary‖ ≤
          selbergSqrtZetaSignedOrdinaryGapShiftBudget T X H +
            selbergSqrtZetaSignedDiagonalShiftBudget T X H := by
      simpa only [ordinary,
        selbergSqrtZetaSignedOrdinaryGapShiftBudget,
        selbergSqrtZetaSignedDiagonalShiftBudget] using hord
    calc
      |model| ≤ (‖ordinary‖ + ‖pseudo‖) / 2 := hdecomp'
      _ ≤ (‖ordinary‖ + ‖ordinary‖) / 2 := by
        exact div_le_div_of_nonneg_right
          (add_le_add le_rfl hpseudo') (by norm_num)
      _ = ‖ordinary‖ := by ring
      _ ≤ selbergSqrtZetaSignedOrdinaryGapShiftBudget T X H +
          selbergSqrtZetaSignedDiagonalShiftBudget T X H := hord'
  change |actual| ≤ _
  calc
    |actual| = |(actual - model) + model| := by ring_nf
    _ ≤ |actual - model| + |model| := abs_add_le _ _
    _ ≤ selbergSqrtZetaSignedModelTransferShiftBudgetL2
          Cactual Ctransfer T X H +
        (selbergSqrtZetaSignedOrdinaryGapShiftBudget T X H +
          selbergSqrtZetaSignedDiagonalShiftBudget T X H) :=
      add_le_add htransfer' hmodelSplit
    _ = selbergSqrtZetaSignedTotalShiftBudgetL2
          Cactual Ctransfer T X H := by
      unfold selbergSqrtZetaSignedTotalShiftBudgetL2
      ring

end HardyTheorem
