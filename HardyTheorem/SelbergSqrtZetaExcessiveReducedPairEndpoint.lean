import HardyTheorem.SelbergSqrtZetaSignedActualFourierTransfer
import HardyTheorem.SelbergSqrtZetaSignedLagIntegral
import HardyTheorem.SelbergSqrtZetaSignedRationalReducedPairShortModel

/-!
# Excessive-window endpoint from canonical reduced-pair energy

The analytic transfer to the actual mollified Hardy function can be driven
directly by the canonical coprime-pair budget.  This removes the abstract
local-frequency separation and the older global model `L²` budget from the
remaining arithmetic hypothesis.
-/

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

/-- The explicit arithmetic budget produced by the canonical reduced-pair
short-model estimate. -/
noncomputable def selbergSqrtZetaSignedReducedPairShortModelBudget
    (T : ℝ) (X : ℕ) (H : ℝ) : ℝ :=
  (T - H) *
      ∑ q ∈ selbergSqrtZetaSignedRationalSupport
          (firstZetaApproximationCutoff T) X,
        Complex.normSq
          (selbergSqrtZetaSignedRationalCoeff
            (firstZetaApproximationCutoff T) X q) +
    4 * Real.pi *
      ∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport
          (firstZetaApproximationCutoff T) X,
        (2 *
            (((X * min (p.1 * firstZetaApproximationCutoff T) p.2 +
                1 : ℕ) : ℝ) *
              ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
                (selbergSqrtZetaSignedReducedRayCompleteTerm
                  (firstZetaApproximationCutoff T) X p.1 p.2) ^ 2)) +
          2 *
            (((X * min (p.1 * firstZetaApproximationCutoff T) p.2 +
                1 : ℕ) : ℝ) *
              ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
                (selbergSqrtZetaSignedReducedRayBoundaryTerm
                  (firstZetaApproximationCutoff T) X p.1 p.2) ^ 2)))

/-- Named-budget form of the actual rational short-model estimate. -/
theorem
    integral_normSq_selbergSqrtZetaSignedRationalShortModel_le_reducedPairBudget
    (kappa T : ℝ) (X : ℕ) {H : ℝ}
    (hT : 0 < T) (hH : 0 ≤ H) (hroom : H ≤ T)
    (hQ :
      (selbergSqrtZetaSignedRationalSupport
        (firstZetaApproximationCutoff T) X).Nontrivial) :
    (∫ t in T..2 * T - H,
        Complex.normSq
          (selbergSqrtZetaSignedRationalShortModel T X H t)) ≤
      H ^ 2 * selbergSqrtZetaSignedReducedPairShortModelBudget T X H := by
  simpa only [selbergSqrtZetaSignedReducedPairShortModelBudget] using
    integral_normSq_selbergSqrtZetaSignedRationalShortModel_le_reducedPairComplete_add_boundary
      kappa T X hT hH hroom hQ

/-- The actual signed-window second moment in terms of the canonical
reduced-pair arithmetic budget plus the uniform first-zeta approximation
error. -/
theorem
    exists_integral_sq_selbergSqrtZetaSignedShortIntegral_le_reducedPairBudget_add_error :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T H : ℝ,
        T0 ≤ T → 0 < H → H ≤ T →
        (selbergSqrtZetaSignedRationalSupport
          (firstZetaApproximationCutoff T) X).Nontrivial →
          (∫ t in T..2 * T - H,
            (selbergSqrtZetaSignedShortIntegral X H t) ^ 2) ≤
            2 * H ^ 2 *
                selbergSqrtZetaSignedReducedPairShortModelBudget T X H +
              2 * T * (4 * C * H * X / Real.sqrt T) ^ 2 := by
  obtain ⟨C, T0, hC, hT0, htransfer⟩ :=
    exists_integral_sq_selbergSqrtZetaSignedShortIntegral_le_rationalShortModel_add_error
  refine ⟨C, T0, hC, hT0, ?_⟩
  intro X hX T H hT hH hroom hQ
  have hTpos : 0 < T := zero_lt_one.trans_le (hT0.trans hT)
  have hrational :=
    integral_normSq_selbergSqrtZetaSignedRationalShortModel_le_reducedPairBudget
      0 T X hTpos hH.le hroom hQ
  calc
    (∫ t in T..2 * T - H,
        (selbergSqrtZetaSignedShortIntegral X H t) ^ 2) ≤
        2 * (∫ t in T..2 * T - H,
          Complex.normSq
            (selbergSqrtZetaSignedRationalShortModel T X H t)) +
          2 * T * (4 * C * H * X / Real.sqrt T) ^ 2 :=
      htransfer X hX T H hT hH hroom
    _ ≤ 2 * (H ^ 2 *
          selbergSqrtZetaSignedReducedPairShortModelBudget T X H) +
        2 * T * (4 * C * H * X / Real.sqrt T) ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hrational (by norm_num)) le_rfl
    _ = 2 * H ^ 2 *
          selbergSqrtZetaSignedReducedPairShortModelBudget T X H +
        2 * T * (4 * C * H * X / Real.sqrt T) ^ 2 := by ring

/-- Final excessive-window endpoint for the canonical reduced-pair route.
The remaining mathematical input is the explicit arithmetic estimate
`ReducedPairShortModelBudget ≤ T / 384`. -/
theorem
    exists_volume_selbergSqrtZetaExcessiveSignedMassStarts_inter_Icc_le_T_div_24_of_reducedPairBudget_le :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T H : ℝ,
        T0 ≤ T → 0 < H → H ≤ T →
        (selbergSqrtZetaSignedRationalSupport
          (firstZetaApproximationCutoff T) X).Nontrivial →
        selbergSqrtZetaSignedReducedPairShortModelBudget T X H ≤ T / 384 →
        6144 * C ^ 2 * (X : ℝ) ^ 2 ≤ T →
        volume.real
            (Icc T (2 * T - H) ∩
              selbergSqrtZetaExcessiveSignedMassStarts X H (H / 2)) ≤
          T / 24 := by
  obtain ⟨C, T0, hC, hT0, hsecond⟩ :=
    exists_integral_sq_selbergSqrtZetaSignedShortIntegral_le_reducedPairBudget_add_error
  refine ⟨C, T0, hC, hT0, ?_⟩
  intro X hX T H hT hH hroom hQ hbudget happrox
  have hTpos : 0 < T := zero_lt_one.trans_le (hT0.trans hT)
  have hAB : T ≤ 2 * T - H := by linarith
  have hsqrtPos : 0 < Real.sqrt T := Real.sqrt_pos.2 hTpos
  have hsqrtSq : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt hTpos.le
  have hbudgetTerm :
      2 * H ^ 2 *
          selbergSqrtZetaSignedReducedPairShortModelBudget T X H ≤
        T * H ^ 2 / 192 := by
    have hscaled :=
      mul_le_mul_of_nonneg_left hbudget
        (show 0 ≤ 2 * H ^ 2 by positivity)
    nlinarith
  have herrorEq :
      2 * T * (4 * C * H * X / Real.sqrt T) ^ 2 =
        32 * C ^ 2 * H ^ 2 * (X : ℝ) ^ 2 := by
    field_simp [ne_of_gt hsqrtPos]
    nlinarith [hsqrtSq]
  have herrorTerm :
      2 * T * (4 * C * H * X / Real.sqrt T) ^ 2 ≤
        T * H ^ 2 / 192 := by
    rw [herrorEq]
    have hscaled :=
      mul_le_mul_of_nonneg_right happrox (sq_nonneg H)
    nlinarith
  have hmoment :
      (∫ t in T..2 * T - H,
          (selbergSqrtZetaSignedShortIntegral X H t) ^ 2) ≤
        T * (H / 2) ^ 2 / 24 := by
    calc
      (∫ t in T..2 * T - H,
          (selbergSqrtZetaSignedShortIntegral X H t) ^ 2) ≤
          2 * H ^ 2 *
              selbergSqrtZetaSignedReducedPairShortModelBudget T X H +
            2 * T * (4 * C * H * X / Real.sqrt T) ^ 2 :=
        hsecond X hX T H hT hH hroom hQ
      _ ≤ T * H ^ 2 / 192 + T * H ^ 2 / 192 :=
        add_le_add hbudgetTerm herrorTerm
      _ = T * (H / 2) ^ 2 / 24 := by ring
  have hcheb :=
    volume_selbergSqrtZetaExcessiveSignedMassStarts_inter_Icc_le_secondMoment
      X (A := T) (B := 2 * T - H) (H := H) (eta := H / 2)
        hAB (half_pos hH)
  rw [Set.inter_comm]
  refine hcheb.trans ?_
  rw [div_le_iff₀ (sq_pos_of_pos (half_pos hH))]
  calc
    (∫ t in T..2 * T - H,
        (selbergSqrtZetaSignedShortIntegral X H t) ^ 2) ≤
        T * (H / 2) ^ 2 / 24 := hmoment
    _ = T / 24 * (H / 2) ^ 2 := by ring

end HardyTheorem
