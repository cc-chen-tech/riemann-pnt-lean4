import HardyTheorem.SelbergSqrtZetaSignedActualFourierTransfer
import HardyTheorem.SelbergSqrtZetaSignedRationalCarrierEnergy
import HardyTheorem.SelbergSqrtZetaSignedRationalNoncarrierPlainEnergyBound
import HardyTheorem.SelbergSqrtZetaSignedRationalNoncarrierShortKernel
import HardyTheorem.SelbergSqrtZetaSignedRationalNoncarrierWeightedEnergyBound

/-!
# Carrier/noncarrier second-moment endpoint

The obsolete reduced-pair endpoint charged the oscillatory ratio-one carrier
through the full local-separation energy.  Here the carrier is paid for by its
Hardy-phase cancellation, while the remaining second moment is kept on the
canonical positive coprime-pair support with `(1,1)` erased.
-/

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

/-- The two explicit arithmetic sums left after deleting the ratio-one
carrier.  The weighted term uses the full rational support's local separation,
which dominates the separation cost recomputed after deletion. -/
noncomputable def selbergSqrtZetaSignedRationalNoncarrierEraseBudget
    (T : ℝ) (X : ℕ) (H : ℝ) : ℝ :=
  let N := firstZetaApproximationCutoff T
  (T - H) *
      ∑ p ∈ (selbergSqrtZetaSignedRationalReducedPairSupport N X).erase (1, 1),
        Complex.normSq
          (selbergSqrtZetaSignedRationalCoeff N X
            (selbergSqrtZetaSignedReducedPairKey p)) +
    4 * Real.pi *
      ∑ p ∈ (selbergSqrtZetaSignedRationalReducedPairSupport N X).erase (1, 1),
        Complex.normSq
            (selbergSqrtZetaSignedRationalCoeff N X
              (selbergSqrtZetaSignedReducedPairKey p)) /
          PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
            (selbergSqrtZetaSignedRationalSupport N X)
            selbergSqrtZetaSignedRationalFrequency
            (selbergSqrtZetaSignedReducedPairKey p)

/-- Explicit plain-energy majorant for the rational noncarrier.  The complete
part retains the signed high-product energy; the boundary part retains the
erased-pair harmonic-tail taper budget. -/
noncomputable def selbergSqrtZetaSignedRationalNoncarrierPlainExplicitBudget
    (N X : ℕ) : ℝ :=
  2 * (((X : ℝ) ^ 2 + 1) *
      ((19 : ℝ) / 4 + selbergSqrtZetaCompleteProductHighEnergy X)) +
    2 * selbergSqrtZetaSignedRationalNoncarrierBoundaryTaperBudget N X

/-- Explicit local-separation majorant for the rational noncarrier.  The
carrier pair is erased before the complete and boundary squares are split. -/
noncomputable def
    selbergSqrtZetaSignedRationalNoncarrierWeightedExplicitBudget
    (N X : ℕ) : ℝ :=
  ∑ p ∈ (selbergSqrtZetaSignedRationalReducedPairSupport N X).erase (1, 1),
    (2 * (((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
      ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
        (selbergSqrtZetaSignedReducedRayCompleteTerm N X p.1 p.2) ^ 2)) +
    2 * (((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
      ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
        ((∑ d ∈ Finset.Ioc
            (min N X / p.2)
            (min (X / p.1) (N * X / p.2)),
            (d : ℝ)⁻¹) ^ 2 *
          (harmonic X : ℝ) *
          (4 * (X : ℝ) ^ 2 / (Real.log X) ^ 2)))))

/-- The complete explicit arithmetic budget left after the oscillatory
carrier has been removed. -/
noncomputable def selbergSqrtZetaSignedRationalNoncarrierExplicitBudget
    (T : ℝ) (X : ℕ) (H : ℝ) : ℝ :=
  let N := firstZetaApproximationCutoff T
  (T - H) *
      selbergSqrtZetaSignedRationalNoncarrierPlainExplicitBudget N X +
    4 * Real.pi *
      selbergSqrtZetaSignedRationalNoncarrierWeightedExplicitBudget N X

/-- The exact deleted-support budget is bounded by the explicit complete,
high-product, and harmonic-tail arithmetic budget. -/
theorem selbergSqrtZetaSignedRationalNoncarrierEraseBudget_le_explicitBudget
    (T : ℝ) (X : ℕ) {H : ℝ}
    (hN : 1 ≤ firstZetaApproximationCutoff T)
    (hXN : X ≤ firstZetaApproximationCutoff T) (hX : 1 < X)
    (hroom : H ≤ T) (hlarge : Real.log 4 + 5 ≤ Real.log X)
    (hQ :
      (selbergSqrtZetaSignedRationalSupport
        (firstZetaApproximationCutoff T) X).Nontrivial) :
    selbergSqrtZetaSignedRationalNoncarrierEraseBudget T X H ≤
      selbergSqrtZetaSignedRationalNoncarrierExplicitBudget T X H := by
  let N := firstZetaApproximationCutoff T
  have hplain :
      (∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
          Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q)) ≤
        selbergSqrtZetaSignedRationalNoncarrierPlainExplicitBudget N X := by
    simpa only [selbergSqrtZetaSignedRationalNoncarrierPlainExplicitBudget] using
      sum_normSq_selbergSqrtZetaSignedRationalNoncarrierCoeff_le_completeHigh_add_boundaryTaper
        hN hXN hX hlarge
  have hplainPair :
      (∑ p ∈ (selbergSqrtZetaSignedRationalReducedPairSupport N X).erase (1, 1),
          Complex.normSq
            (selbergSqrtZetaSignedRationalCoeff N X
              (selbergSqrtZetaSignedReducedPairKey p))) ≤
        selbergSqrtZetaSignedRationalNoncarrierPlainExplicitBudget N X := by
    rw [← sum_normSq_noncarrier_eq_reducedPairSupport_erase_one hN
      (by omega : 1 ≤ X)]
    exact hplain
  have hweighted :
      (∑ p ∈ (selbergSqrtZetaSignedRationalReducedPairSupport N X).erase (1, 1),
          Complex.normSq
                (selbergSqrtZetaSignedRationalCoeff N X
                  (selbergSqrtZetaSignedReducedPairKey p)) /
              PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
                (selbergSqrtZetaSignedRationalSupport N X)
                selbergSqrtZetaSignedRationalFrequency
                (selbergSqrtZetaSignedReducedPairKey p)) ≤
        selbergSqrtZetaSignedRationalNoncarrierWeightedExplicitBudget N X := by
    simpa only [selbergSqrtZetaSignedRationalNoncarrierWeightedExplicitBudget] using
      sum_normSq_div_fullLocalSeparation_reducedPairErase_le_complete_add_explicitBoundary
        (by omega : 2 ≤ X) hQ
  unfold selbergSqrtZetaSignedRationalNoncarrierEraseBudget
    selbergSqrtZetaSignedRationalNoncarrierExplicitBudget
  dsimp only [N]
  exact add_le_add
    (mul_le_mul_of_nonneg_left hplainPair (sub_nonneg.mpr hroom))
    (mul_le_mul_of_nonneg_left hweighted (by positivity))

/-- Named-budget form of the proved noncarrier short-model estimate. -/
theorem
    integral_normSq_selbergSqrtZetaSignedRationalNoncarrierShortModel_le_eraseBudget
    (T : ℝ) (X : ℕ) {H : ℝ}
    (hT : 0 < T) (hH : 0 ≤ H) (hroom : H ≤ T)
    (hcutoff : 1 ≤ firstZetaApproximationCutoff T) (hX : 1 ≤ X)
    (hNoncarrier :
      (selbergSqrtZetaSignedRationalNoncarrierSupport
        (firstZetaApproximationCutoff T) X).Nontrivial) :
    (∫ t in T..2 * T - H,
        Complex.normSq
          (selbergSqrtZetaSignedRationalNoncarrierShortModel T X H t)) ≤
      H ^ 2 *
        selbergSqrtZetaSignedRationalNoncarrierEraseBudget T X H := by
  simpa only [selbergSqrtZetaSignedRationalNoncarrierEraseBudget] using
    integral_normSq_selbergSqrtZetaSignedRationalNoncarrierShortModel_le_reducedPairEraseBudget
      T X hT hH hroom hcutoff hX hNoncarrier

/-- The complete rational short-model second moment is controlled by the
oscillatory carrier budget plus the genuine deleted-support noncarrier budget.
No full-support diagonal energy is charged to the carrier. -/
theorem
    integral_normSq_selbergSqrtZetaSignedRationalShortModel_le_carrier_add_noncarrierEraseBudget
    (T : ℝ) (X : ℕ) {H : ℝ}
    (hcutoff : 1 ≤ firstZetaApproximationCutoff T) (hX : 2 ≤ X)
    (hXN : X ≤ firstZetaApproximationCutoff T)
    (hT : 1 < T) (hH : 0 ≤ H) (hroom : H ≤ T)
    (hpi : 2 * Real.log (2 * Real.pi) ≤ Real.log T)
    (hwindow : 4 * H ≤ T * Real.log T)
    (hNoncarrier :
      (selbergSqrtZetaSignedRationalNoncarrierSupport
        (firstZetaApproximationCutoff T) X).Nontrivial) :
    (∫ t in T..2 * T - H,
        Complex.normSq
          (selbergSqrtZetaSignedRationalShortModel T X H t)) ≤
      2 * (T - H) *
          ((1 + Real.log X) * (32 / Real.log T)) ^ 2 +
        2 * H ^ 2 *
          selbergSqrtZetaSignedRationalNoncarrierEraseBudget T X H := by
  let carrier : ℝ := (1 + Real.log X) * (32 / Real.log T)
  have hTpos : 0 < T := zero_lt_one.trans hT
  have hlong : T ≤ 2 * T - H := by linarith
  have hcarrier : 0 ≤ carrier := by
    dsimp only [carrier]
    exact mul_nonneg
      (add_nonneg zero_le_one
        (Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))))
      (div_nonneg (by norm_num) (Real.log_pos hT).le)
  have hfullInt :=
    intervalIntegrable_normSq_selbergSqrtZetaSignedRationalShortModel
      T X hTpos hH hroom
  have hnonInt :=
    intervalIntegrable_normSq_selbergSqrtZetaSignedRationalNoncarrierShortModel
      T X hTpos hH hroom
  have hmajorInt :
      IntervalIntegrable
        (fun t : ℝ =>
          2 * carrier ^ 2 +
            2 * Complex.normSq
              (selbergSqrtZetaSignedRationalNoncarrierShortModel T X H t))
        volume T (2 * T - H) :=
    (continuous_const.intervalIntegrable _ _).add (hnonInt.const_mul 2)
  have hpoint : ∀ t ∈ Icc T (2 * T - H),
      Complex.normSq
          (selbergSqrtZetaSignedRationalShortModel T X H t) ≤
        2 * carrier ^ 2 +
          2 * Complex.normSq
            (selbergSqrtZetaSignedRationalNoncarrierShortModel T X H t) := by
    intro t ht
    have hnorm :=
      norm_selbergSqrtZetaSignedRationalShortModel_le_log_carrier_add_noncarrier
        hcutoff hX hXN hT ht.1 hH hpi hwindow
    have hfullNonneg :
        0 ≤ ‖selbergSqrtZetaSignedRationalShortModel T X H t‖ :=
      norm_nonneg _
    have hnonNonneg :
        0 ≤ ‖selbergSqrtZetaSignedRationalNoncarrierShortModel T X H t‖ :=
      norm_nonneg _
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    change
      ‖selbergSqrtZetaSignedRationalShortModel T X H t‖ ≤
        carrier +
          ‖selbergSqrtZetaSignedRationalNoncarrierShortModel T X H t‖ at hnorm
    nlinarith
      [sq_nonneg
        (carrier -
          ‖selbergSqrtZetaSignedRationalNoncarrierShortModel T X H t‖),
       sq_nonneg
        (carrier +
          ‖selbergSqrtZetaSignedRationalNoncarrierShortModel T X H t‖ -
            ‖selbergSqrtZetaSignedRationalShortModel T X H t‖)]
  have hmono :=
    intervalIntegral.integral_mono_on
      hlong hfullInt hmajorInt hpoint
  have hnon :=
    integral_normSq_selbergSqrtZetaSignedRationalNoncarrierShortModel_le_eraseBudget
      T X hTpos hH hroom hcutoff (by omega) hNoncarrier
  have hnonScaled :
      2 * (∫ t in T..2 * T - H,
        Complex.normSq
          (selbergSqrtZetaSignedRationalNoncarrierShortModel T X H t)) ≤
        2 * (H ^ 2 *
          selbergSqrtZetaSignedRationalNoncarrierEraseBudget T X H) :=
    mul_le_mul_of_nonneg_left hnon (by norm_num)
  calc
    (∫ t in T..2 * T - H,
        Complex.normSq
          (selbergSqrtZetaSignedRationalShortModel T X H t)) ≤
        ∫ t in T..2 * T - H,
          (2 * carrier ^ 2 +
            2 * Complex.normSq
              (selbergSqrtZetaSignedRationalNoncarrierShortModel T X H t)) :=
      hmono
    _ = 2 * (T - H) * carrier ^ 2 +
          2 * (∫ t in T..2 * T - H,
            Complex.normSq
              (selbergSqrtZetaSignedRationalNoncarrierShortModel T X H t)) := by
      rw [intervalIntegral.integral_add
        (continuous_const.intervalIntegrable _ _) (hnonInt.const_mul 2),
        intervalIntegral.integral_const,
        intervalIntegral.integral_const_mul]
      simp only [smul_eq_mul]
      ring
    _ ≤ 2 * (T - H) * carrier ^ 2 +
          2 * (H ^ 2 *
            selbergSqrtZetaSignedRationalNoncarrierEraseBudget T X H) :=
      add_le_add le_rfl hnonScaled
    _ = 2 * (T - H) *
          ((1 + Real.log X) * (32 / Real.log T)) ^ 2 +
        2 * H ^ 2 *
          selbergSqrtZetaSignedRationalNoncarrierEraseBudget T X H := by
      dsimp only [carrier]
      ring

/-- Fully explicit carrier/noncarrier endpoint.  All remaining noncarrier
input is an arithmetic finite-sum budget; no further analytic transfer or
full-support carrier energy appears in the statement. -/
theorem
    integral_normSq_selbergSqrtZetaSignedRationalShortModel_le_carrier_add_noncarrierExplicitBudget
    (T : ℝ) (X : ℕ) {H : ℝ}
    (hcutoff : 1 ≤ firstZetaApproximationCutoff T) (hX : 2 ≤ X)
    (hXN : X ≤ firstZetaApproximationCutoff T)
    (hT : 1 < T) (hH : 0 ≤ H) (hroom : H ≤ T)
    (hpi : 2 * Real.log (2 * Real.pi) ≤ Real.log T)
    (hwindow : 4 * H ≤ T * Real.log T)
    (hlarge : Real.log 4 + 5 ≤ Real.log X)
    (hNoncarrier :
      (selbergSqrtZetaSignedRationalNoncarrierSupport
        (firstZetaApproximationCutoff T) X).Nontrivial)
    (hQ :
      (selbergSqrtZetaSignedRationalSupport
        (firstZetaApproximationCutoff T) X).Nontrivial) :
    (∫ t in T..2 * T - H,
        Complex.normSq
          (selbergSqrtZetaSignedRationalShortModel T X H t)) ≤
      2 * (T - H) *
          ((1 + Real.log X) * (32 / Real.log T)) ^ 2 +
        2 * H ^ 2 *
          selbergSqrtZetaSignedRationalNoncarrierExplicitBudget T X H := by
  have hbase :=
    integral_normSq_selbergSqrtZetaSignedRationalShortModel_le_carrier_add_noncarrierEraseBudget
      T X hcutoff hX hXN hT hH hroom hpi hwindow hNoncarrier
  have hbudget :=
    selbergSqrtZetaSignedRationalNoncarrierEraseBudget_le_explicitBudget
      T X hcutoff hXN (by omega) hroom hlarge hQ
  have hscaled :
      2 * H ^ 2 * selbergSqrtZetaSignedRationalNoncarrierEraseBudget T X H ≤
        2 * H ^ 2 *
          selbergSqrtZetaSignedRationalNoncarrierExplicitBudget T X H :=
    mul_le_mul_of_nonneg_left hbudget (mul_nonneg (by norm_num) (sq_nonneg H))
  exact hbase.trans (add_le_add le_rfl hscaled)

end HardyTheorem
