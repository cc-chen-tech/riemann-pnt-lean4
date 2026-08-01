import HardyTheorem.SelbergSqrtZetaSignedAutocorrelationShiftBudget
import HardyTheorem.SelbergSqrtZetaSignedModelSupBound
import HardyTheorem.SelbergSqrtZetaSignedOrdinaryShiftBudget
import HardyTheorem.SelbergSqrtZetaSignedPseudoFiberBudget

/-!
# Total shift-square budget for the signed Selberg second moment

This module closes the analytic bookkeeping for the excessive-signed-mass
route. The actual square-root-zeta autocorrelation is compared with the finite
theta model; the theta model is split into ordinary and pseudo correlations;
and the ordinary part is split into unequal- and equal-frequency blocks.

The raw theorem accepts a uniform finite-model bound. A second theorem
discharges that input by the explicit coefficient `L1` norm, leaving only
finite arithmetic estimates for the budgets defined below.
-/

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

/-- The finite unequal-frequency budget for the ordinary correlation. -/
noncomputable def selbergSqrtZetaSignedOrdinaryGapShiftBudget
    (T : ℝ) (X : ℕ) (H : ℝ) : ℝ :=
  H ^ 2 *
    ∑ omega ∈
        selbergSqrtZetaSignedCollectedFrequencySupport
          (firstZetaApproximationCutoff T) X,
      ∑ nu ∈
          selbergSqrtZetaSignedCollectedFrequencySupport
            (firstZetaApproximationCutoff T) X,
        if omega = nu then 0
        else
          ‖selbergSqrtZetaSignedCollectedCoeff
            (firstZetaApproximationCutoff T) X omega‖ *
          ‖selbergSqrtZetaSignedCollectedCoeff
            (firstZetaApproximationCutoff T) X nu‖ *
          ((2 + H / 2) / |omega - nu|)

/-- The exact same-frequency multiplicity-energy budget. -/
noncomputable def selbergSqrtZetaSignedDiagonalShiftBudget
    (T : ℝ) (X : ℕ) (H : ℝ) : ℝ :=
  H ^ 2 * (T - H) *
    ∑ omega ∈
        selbergSqrtZetaSignedCollectedFrequencySupport
          (firstZetaApproximationCutoff T) X,
      (((selbergSqrtZetaSignedPhaseSupport
          (firstZetaApproximationCutoff T) X).filter
        (fun p => selbergSqrtZetaSignedPhaseFrequency p = omega)).card : ℝ) *
      ∑ p ∈
          (selbergSqrtZetaSignedPhaseSupport
            (firstZetaApproximationCutoff T) X).filter
            (fun p => selbergSqrtZetaSignedPhaseFrequency p = omega),
        Complex.normSq (selbergSqrtZetaSignedPhaseCoeff X p)

/-- The pseudo-correlation budget after finite Cauchy--Schwarz compression. -/
noncomputable def selbergSqrtZetaSignedPseudoShiftFiberBudget
    (T : ℝ) (X : ℕ) (H : ℝ) : ℝ :=
  H ^ 2 *
    ((12 * Real.sqrt (4 * T)) *
      ((selbergSqrtZetaSignedCollectedFrequencySupport
        (firstZetaApproximationCutoff T) X).card : ℝ) *
      ∑ omega ∈
          selbergSqrtZetaSignedCollectedFrequencySupport
            (firstZetaApproximationCutoff T) X,
        (((selbergSqrtZetaSignedPhaseSupport
            (firstZetaApproximationCutoff T) X).filter
          (fun p => selbergSqrtZetaSignedPhaseFrequency p = omega)).card : ℝ) *
        ∑ p ∈
            (selbergSqrtZetaSignedPhaseSupport
              (firstZetaApproximationCutoff T) X).filter
              (fun p => selbergSqrtZetaSignedPhaseFrequency p = omega),
          Complex.normSq (selbergSqrtZetaSignedPhaseCoeff X p))

/-- The shift-square cost of replacing the actual mollified Hardy function by
the finite theta model, assuming the latter is bounded by `M`. -/
noncomputable def selbergSqrtZetaSignedModelTransferShiftBudget
    (C T : ℝ) (X : ℕ) (H M : ℝ) : ℝ :=
  H ^ 2 * (T - H) *
    (2 * (M + 4 * C * X / Real.sqrt T) *
      (4 * C * X / Real.sqrt T))

/-- The complete explicit analytic budget. The factor `1/2` comes from the
identity `Re z * Re w = (Re (z * conj w) + Re (z * w)) / 2`. -/
noncomputable def selbergSqrtZetaSignedTotalShiftBudget
    (C T : ℝ) (X : ℕ) (H M : ℝ) : ℝ :=
  selbergSqrtZetaSignedModelTransferShiftBudget C T X H M +
    (selbergSqrtZetaSignedOrdinaryGapShiftBudget T X H +
      selbergSqrtZetaSignedDiagonalShiftBudget T X H +
      selbergSqrtZetaSignedPseudoShiftFiberBudget T X H) / 2

/-- The actual shift-square autocorrelation is bounded by the complete
explicit analytic budget. No conditional correlation estimate remains: only
the finite-model sup bound `M` and the arithmetic size of the displayed finite
budgets remain to be supplied. -/
theorem
    exists_abs_integral_integral_integral_selbergSqrtZetaMollifiedAutocorrelation_le_totalShiftBudget :
    ∃ kappa C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T H M : ℝ,
        T0 ≤ T → 0 ≤ H → H ≤ T → 0 ≤ M →
        (∀ x ∈ Icc T (2 * T),
          |selbergSqrtZetaSignedThetaModel kappa T X x| ≤ M) →
        |∫ v in 0..H, ∫ w in 0..H, ∫ t in T..2 * T - H,
            selbergSqrtZetaMollifiedHardyZ X (t + v) *
              selbergSqrtZetaMollifiedHardyZ X (t + w)| ≤
          selbergSqrtZetaSignedTotalShiftBudget C T X H M := by
  obtain ⟨kappa, C, T0, hC, hT0, htransfer⟩ :=
    exists_abs_integral_integral_integral_selbergSqrtZetaMollifiedAutocorrelation_sub_signedThetaModel_le
  refine ⟨kappa, C, T0, hC, hT0, ?_⟩
  intro X hX T H M hT hH hHT hM hmodel
  have hTone : 1 ≤ T := hT0.trans hT
  have hTpos : 0 < T := zero_lt_one.trans_le hTone
  let actual : ℝ :=
    ∫ v in 0..H, ∫ w in 0..H, ∫ t in T..2 * T - H,
      selbergSqrtZetaMollifiedHardyZ X (t + v) *
        selbergSqrtZetaMollifiedHardyZ X (t + w)
  let model : ℝ :=
    ∫ v in 0..H, ∫ w in 0..H, ∫ t in T..2 * T - H,
      selbergSqrtZetaSignedThetaModel kappa T X (t + v) *
        selbergSqrtZetaSignedThetaModel kappa T X (t + w)
  have htransfer' :
      |actual - model| ≤
        selbergSqrtZetaSignedModelTransferShiftBudget C T X H M := by
    simpa only [actual, model,
      selbergSqrtZetaSignedModelTransferShiftBudget] using
      htransfer X hX T H M hT hH hHT hM hmodel
  have hmodelSplit :
      |model| ≤
        (selbergSqrtZetaSignedOrdinaryGapShiftBudget T X H +
          selbergSqrtZetaSignedDiagonalShiftBudget T X H +
          selbergSqrtZetaSignedPseudoShiftFiberBudget T X H) / 2 := by
    have hdecomp :=
      abs_integral_integral_integral_selbergSqrtZetaSignedThetaModel_mul_shift_le
        kappa T X hTpos hH hHT
    have hord :=
      norm_integral_integral_integral_selbergSqrtZetaSignedOrdinaryCorrelation_le
        kappa T X hTpos hH hHT
    have hpseudo :=
      norm_integral_integral_integral_selbergSqrtZetaSignedComplexModel_mul_shift_le_fiber_budget
        kappa X hTone hH hHT
    apply hdecomp.trans
    apply div_le_div_of_nonneg_right
    · simpa only [selbergSqrtZetaSignedOrdinaryGapShiftBudget,
          selbergSqrtZetaSignedDiagonalShiftBudget,
          selbergSqrtZetaSignedPseudoShiftFiberBudget,
          add_assoc] using
        add_le_add hord hpseudo
    · norm_num
  change |actual| ≤ _
  calc
    |actual| = |(actual - model) + model| := by ring_nf
    _ ≤ |actual - model| + |model| := abs_add_le _ _
    _ ≤ selbergSqrtZetaSignedModelTransferShiftBudget C T X H M +
        (selbergSqrtZetaSignedOrdinaryGapShiftBudget T X H +
          selbergSqrtZetaSignedDiagonalShiftBudget T X H +
          selbergSqrtZetaSignedPseudoShiftFiberBudget T X H) / 2 :=
      add_le_add htransfer' hmodelSplit
    _ = selbergSqrtZetaSignedTotalShiftBudget C T X H M := rfl

/-- The same total budget with the finite model bound discharged by the
coefficient `L1` norm. The only remaining right-hand side is an explicit
finite arithmetic expression. -/
theorem
    exists_abs_integral_integral_integral_selbergSqrtZetaMollifiedAutocorrelation_le_totalShiftBudget_modelSupBound :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T H : ℝ,
        T0 ≤ T → 0 ≤ H → H ≤ T →
        |∫ v in 0..H, ∫ w in 0..H, ∫ t in T..2 * T - H,
            selbergSqrtZetaMollifiedHardyZ X (t + v) *
              selbergSqrtZetaMollifiedHardyZ X (t + w)| ≤
          selbergSqrtZetaSignedTotalShiftBudget C T X H
            (selbergSqrtZetaSignedModelSupBoundL1 T X) := by
  obtain ⟨kappa, C, T0, hC, hT0, htotal⟩ :=
    exists_abs_integral_integral_integral_selbergSqrtZetaMollifiedAutocorrelation_le_totalShiftBudget
  refine ⟨C, T0, hC, hT0, ?_⟩
  intro X hX T H hT hH hHT
  apply htotal X hX T H
    (selbergSqrtZetaSignedModelSupBoundL1 T X) hT hH hHT
  · unfold selbergSqrtZetaSignedModelSupBoundL1
    positivity
  · intro x _hx
    exact
      abs_selbergSqrtZetaSignedThetaModel_le_modelSupBoundL1
        kappa T X x

end HardyTheorem
