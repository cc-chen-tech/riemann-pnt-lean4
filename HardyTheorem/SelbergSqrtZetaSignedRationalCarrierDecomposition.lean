import HardyTheorem.HardyPhaseCorrelation
import HardyTheorem.SelbergSqrtZetaSignedRationalShortModel
import HardyTheorem.SelbergSqrtZetaSignedReducedRayCompleteBoundary

/-!
# Carrier decomposition of the signed rational short model

The rational frequency `q = 1` has logarithmic frequency zero, so after the
common Hardy theta phase is restored it is the distinguished carrier term.
This file extracts that term exactly and leaves every other rational
frequency in a finite noncarrier remainder.
-/

open scoped BigOperators

namespace HardyTheorem

/-- Ratio one belongs to the signed rational support whenever all three
finite index boxes contain one. -/
theorem one_mem_selbergSqrtZetaSignedRationalSupport
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) :
    (1 : ℚ) ∈ selbergSqrtZetaSignedRationalSupport N X := by
  apply Finset.mem_image.mpr
  refine ⟨(1, (1, 1)), ?_, ?_⟩
  · exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨le_rfl, hN⟩,
        Finset.mem_product.mpr
          ⟨Finset.mem_Icc.mpr ⟨le_rfl, hX⟩,
            Finset.mem_Icc.mpr ⟨le_rfl, hX⟩⟩⟩
  · norm_num [selbergSqrtZetaSignedRationalKey]

/-- The actual signed rational support with the distinguished carrier ratio
one removed. -/
noncomputable def selbergSqrtZetaSignedRationalNoncarrierSupport
    (N X : ℕ) : Finset ℚ :=
  (selbergSqrtZetaSignedRationalSupport N X).erase 1

/-- The exact rational short model over all frequencies other than the
carrier ratio one. -/
noncomputable def selbergSqrtZetaSignedRationalNoncarrierShortModel
    (T : ℝ) (X : ℕ) (H t : ℝ) : ℂ :=
  ∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport
      (firstZetaApproximationCutoff T) X,
    selbergSqrtZetaSignedRationalCoeff
        (firstZetaApproximationCutoff T) X q *
      thetaFrequencyShortIntegral
        (selbergSqrtZetaSignedRationalFrequency q) H t

/-- Exact carrier-plus-remainder decomposition of the rational short model.
No triangle inequality or coefficient estimate is used. -/
theorem selbergSqrtZetaSignedRationalShortModel_eq_carrier_add_noncarrier
    {T : ℝ} {X : ℕ} (hT : 1 ≤ firstZetaApproximationCutoff T)
    (hX : 1 ≤ X) (H t : ℝ) :
    selbergSqrtZetaSignedRationalShortModel T X H t =
      selbergSqrtZetaSignedRationalCoeff
          (firstZetaApproximationCutoff T) X 1 *
        thetaFrequencyShortIntegral 0 H t +
      selbergSqrtZetaSignedRationalNoncarrierShortModel T X H t := by
  classical
  let N := firstZetaApproximationCutoff T
  let Q := selbergSqrtZetaSignedRationalSupport N X
  let term : ℚ → ℂ := fun q =>
    selbergSqrtZetaSignedRationalCoeff N X q *
      thetaFrequencyShortIntegral
        (selbergSqrtZetaSignedRationalFrequency q) H t
  have hone : (1 : ℚ) ∈ Q := by
    exact one_mem_selbergSqrtZetaSignedRationalSupport hT hX
  have hfrequency :
      selbergSqrtZetaSignedRationalFrequency (1 : ℚ) = 0 := by
    simp [selbergSqrtZetaSignedRationalFrequency]
  change (∑ q ∈ Q, term q) =
    selbergSqrtZetaSignedRationalCoeff N X 1 *
        thetaFrequencyShortIntegral 0 H t +
      ∑ q ∈ Q.erase 1, term q
  rw [← Finset.sum_erase_add _ _ hone]
  rw [show term 1 =
      selbergSqrtZetaSignedRationalCoeff N X 1 *
        thetaFrequencyShortIntegral 0 H t by
    simp only [term, hfrequency]]
  ring

/-- The exact carrier coefficient is the `(1,1)` reduced ray, split into its
complete arithmetic main term and finite-cutoff boundary defect. -/
theorem selbergSqrtZetaSignedRationalCoeff_one_eq_complete_add_boundary
    (N X : ℕ) :
    selbergSqrtZetaSignedRationalCoeff N X 1 =
      ((selbergSqrtZetaSignedReducedRayCompleteTerm N X 1 1 +
        selbergSqrtZetaSignedReducedRayBoundaryTerm N X 1 1 : ℝ) : ℂ) := by
  have hcoeff :=
    selbergSqrtZetaSignedRationalCoeff_reduced_eq_coprimeRayScaleSum
      N X 1 1 (by norm_num) (by norm_num)
  norm_num at hcoeff
  rw [hcoeff]
  rw [← Complex.ofReal_sum]
  have hscale :=
    selbergSqrtZetaSignedCoprimeRayScaleSum_eq_invSqrt_mul_bilinearScaleSum
      N X 1 1
  norm_num at hscale
  rw [hscale]
  rw [selbergSqrtZetaSignedCoprimeRayBilinearScaleSum_eq_complete_add_boundary
    N X 1 1 (by norm_num)]

private theorem thetaModel_eq_hardyPhase_one_carrier :
    thetaModel = OscillatoryIntegral.hardyPhase 1 := by
  funext x
  simp [thetaModel, OscillatoryIntegral.hardyPhase]
  ring

/-- The distinguished carrier keeps the reciprocal Hardy-phase derivative
gain.  This replaces the old trivial window-length estimate when the carrier
is uniformly nonstationary across the short window. -/
theorem norm_thetaFrequencyShortIntegral_zero_le_of_base_frequency
    {T t H : ℝ} (hT : 0 < T) (hTt : T ≤ t) (hH : 0 ≤ H)
    (hgap : 0 < |deriv thetaModel t|)
    (hshift : H / (2 * T) ≤ |deriv thetaModel t| / 2) :
    ‖thetaFrequencyShortIntegral 0 H t‖ ≤
      8 / |deriv thetaModel t| := by
  have hphaseGap :
      0 < |deriv (OscillatoryIntegral.hardyPhase 1) t| := by
    simpa only [thetaModel_eq_hardyPhase_one_carrier] using hgap
  have hphaseShift :
      H / (2 * T) ≤
        |deriv (OscillatoryIntegral.hardyPhase 1) t| / 2 := by
    simpa only [thetaModel_eq_hardyPhase_one_carrier] using hshift
  have hbound :=
    OscillatoryIntegral.norm_integral_cexp_shifted_hardyPhase_le_of_base_frequency
      (n := 1) (by norm_num) hT hTt hH hphaseGap hphaseShift
  simpa only [thetaFrequencyShortIntegral, zero_mul, add_zero,
    thetaModel_eq_hardyPhase_one_carrier] using hbound

/-- The carrier contribution to the rational model inherits the same
reciprocal-derivative gain, with only its exact collected coefficient left. -/
theorem norm_selbergSqrtZetaSignedRationalCarrier_le_of_base_frequency
    (N X : ℕ) {T t H : ℝ} (hT : 0 < T) (hTt : T ≤ t)
    (hH : 0 ≤ H) (hgap : 0 < |deriv thetaModel t|)
    (hshift : H / (2 * T) ≤ |deriv thetaModel t| / 2) :
    ‖selbergSqrtZetaSignedRationalCoeff N X 1 *
        thetaFrequencyShortIntegral 0 H t‖ ≤
      ‖selbergSqrtZetaSignedRationalCoeff N X 1‖ *
        (8 / |deriv thetaModel t|) := by
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_thetaFrequencyShortIntegral_zero_le_of_base_frequency
      hT hTt hH hgap hshift)
    (norm_nonneg _)

/-- A logarithmic height threshold places the derivative of the carrier
Hardy phase above one quarter of `log T` throughout `[T, +∞)`. -/
theorem quarter_log_le_deriv_thetaModel
    {T t : ℝ} (hT : 0 < T) (hTt : T ≤ t)
    (hpi : 2 * Real.log (2 * Real.pi) ≤ Real.log T) :
    (1 / 4 : ℝ) * Real.log T ≤ deriv thetaModel t := by
  have ht : 0 < t := hT.trans_le hTt
  have hlogTt : Real.log T ≤ Real.log t :=
    Real.log_le_log hT hTt
  rw [deriv_thetaModel ht, Real.log_div (ne_of_gt ht)
    (by positivity : (2 * Real.pi : ℝ) ≠ 0)]
  nlinarith

/-- The carrier short integral has an explicit `32 / log T` bound at high
height.  The window condition is precisely what keeps the phase derivative
away from zero throughout the interval. -/
theorem norm_thetaFrequencyShortIntegral_zero_le_thirtytwo_div_log
    {T t H : ℝ} (hT : 1 < T) (hTt : T ≤ t) (hH : 0 ≤ H)
    (hpi : 2 * Real.log (2 * Real.pi) ≤ Real.log T)
    (hwindow : 4 * H ≤ T * Real.log T) :
    ‖thetaFrequencyShortIntegral 0 H t‖ ≤ 32 / Real.log T := by
  have hTpos : 0 < T := zero_lt_one.trans hT
  have hlogT : 0 < Real.log T := Real.log_pos hT
  have hderivLower :
      (1 / 4 : ℝ) * Real.log T ≤ deriv thetaModel t :=
    quarter_log_le_deriv_thetaModel hTpos hTt hpi
  have hderivPos : 0 < deriv thetaModel t := by
    nlinarith
  have habsDeriv : |deriv thetaModel t| = deriv thetaModel t :=
    abs_of_pos hderivPos
  have hHT : H / T ≤ (1 / 4 : ℝ) * Real.log T := by
    rw [div_le_iff₀ hTpos]
    nlinarith
  have hshift :
      H / (2 * T) ≤ |deriv thetaModel t| / 2 := by
    rw [habsDeriv]
    have hbase : H / T ≤ deriv thetaModel t := hHT.trans hderivLower
    have htwoT : (2 : ℝ) * T ≠ 0 := mul_ne_zero (by norm_num) hTpos.ne'
    field_simp [htwoT, hTpos.ne'] at ⊢ hbase
    nlinarith
  have hraw :=
    norm_thetaFrequencyShortIntegral_zero_le_of_base_frequency
      hTpos hTt hH (by simpa only [habsDeriv] using hderivPos) hshift
  calc
    ‖thetaFrequencyShortIntegral 0 H t‖ ≤
        8 / |deriv thetaModel t| := hraw
    _ ≤ 32 / Real.log T := by
      rw [habsDeriv]
      rw [div_le_div_iff₀ hderivPos hlogT]
      nlinarith

/-- The complete carrier term therefore costs only its exact collected
coefficient times `32 / log T`. -/
theorem norm_selbergSqrtZetaSignedRationalCarrier_le_thirtytwo_div_log
    (N X : ℕ) {T t H : ℝ} (hT : 1 < T) (hTt : T ≤ t)
    (hH : 0 ≤ H)
    (hpi : 2 * Real.log (2 * Real.pi) ≤ Real.log T)
    (hwindow : 4 * H ≤ T * Real.log T) :
    ‖selbergSqrtZetaSignedRationalCoeff N X 1 *
        thetaFrequencyShortIntegral 0 H t‖ ≤
      ‖selbergSqrtZetaSignedRationalCoeff N X 1‖ *
        (32 / Real.log T) := by
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_thetaFrequencyShortIntegral_zero_le_thirtytwo_div_log
      hT hTt hH hpi hwindow)
    (norm_nonneg _)

/-- Pointwise nonvacuous replacement for the old raw-energy bound: the
carrier receives its logarithmic oscillation saving, while only the genuine
noncarrier remainder is left for an `L²` estimate. -/
theorem norm_selbergSqrtZetaSignedRationalShortModel_le_carrier_add_noncarrier
    {T t H : ℝ} {X : ℕ}
    (hcutoff : 1 ≤ firstZetaApproximationCutoff T) (hX : 1 ≤ X)
    (hT : 1 < T) (hTt : T ≤ t) (hH : 0 ≤ H)
    (hpi : 2 * Real.log (2 * Real.pi) ≤ Real.log T)
    (hwindow : 4 * H ≤ T * Real.log T) :
    ‖selbergSqrtZetaSignedRationalShortModel T X H t‖ ≤
      ‖selbergSqrtZetaSignedRationalCoeff
          (firstZetaApproximationCutoff T) X 1‖ *
          (32 / Real.log T) +
        ‖selbergSqrtZetaSignedRationalNoncarrierShortModel T X H t‖ := by
  rw [selbergSqrtZetaSignedRationalShortModel_eq_carrier_add_noncarrier
    hcutoff hX]
  exact (norm_add_le _ _).trans
    (add_le_add
      (norm_selbergSqrtZetaSignedRationalCarrier_le_thirtytwo_div_log
        (firstZetaApproximationCutoff T) X hT hTt hH hpi hwindow)
      le_rfl)

end HardyTheorem
