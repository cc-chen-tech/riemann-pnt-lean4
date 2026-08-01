import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBoundaryExtensionAbsoluteMass
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualReciprocalOutsideClusterLowLayer

/-!
# Reciprocal absolute mass for moving extensions

The reciprocal low-layer argument also controls the sum of individual kernel
norms, not merely the norm of their signed sum.  This stronger form survives
arbitrary subset selection and therefore controls a moving-cluster extension
without any cancellation hypothesis.  The old polynomial-height loss is
replaced by the strict margin `sigma - beta + epsilon < 0`.
-/

open scoped BigOperators Topology

namespace PrimeNumberTheorem

open Complex Filter

noncomputable section

/-- A finite outside-cluster layer's absolute kernel mass is bounded by the
global multiplicity-weighted reciprocal-zero mass. -/
theorem
    PositiveZeroOutsideClusterBucketInput.sum_norm_layer_le_rpow_mul_globalReciprocal
    {T : ℝ} {S : Finset ℂ} {n : ℕ}
    (input : PositiveZeroOutsideClusterBucketInput T S n)
    (i : Fin n) {sigma x : ℝ}
    (hx : 1 ≤ x)
    (hre : ∀ rho ∈ input.layer i, rho.re ≤ sigma) :
    (∑ rho ∈ input.layer i, ‖pntRelativeZeroContribution x rho‖) ≤
      x ^ (sigma - 1) *
        ExplicitFormulaAux.globalReciprocalZeroMultiplicity T := by
  classical
  have hxPos : 0 < x := zero_lt_one.trans_le hx
  have hxNonneg : 0 ≤ x := hxPos.le
  have hsubset : input.layer i ⊆ nontrivialZerosFinset T := by
    intro rho hrho
    have hOutside :=
      mem_positiveNontrivialZerosOutsideClusterFinset.mp
        (Finset.mem_filter.mp hrho).1
    apply mem_nontrivialZerosFinset.mpr
    refine ⟨hOutside.1, ?_⟩
    rw [abs_of_pos hOutside.2.1]
    exact hOutside.2.2.1
  have hmass :
      (∑ rho ∈ input.layer i,
          (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖) ≤
        ExplicitFormulaAux.globalReciprocalZeroMultiplicity T := by
    unfold ExplicitFormulaAux.globalReciprocalZeroMultiplicity
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun rho _ _ => div_nonneg (Nat.cast_nonneg _) (norm_nonneg rho))
  calc
    (∑ rho ∈ input.layer i, ‖pntRelativeZeroContribution x rho‖)
        ≤ ∑ rho ∈ input.layer i,
          x ^ (sigma - 1) *
            ((analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖) := by
      apply Finset.sum_le_sum
      intro rho hrho
      have hrpow : x ^ (rho.re - 1) ≤ x ^ (sigma - 1) :=
        Real.rpow_le_rpow_of_exponent_le hx (by linarith [hre rho hrho])
      have hmult : 0 ≤ (analyticOrderNatAt riemannZeta rho : ℝ) :=
        Nat.cast_nonneg _
      rw [norm_pntRelativeZeroContribution_eq_multiplicity_mul_norm,
        norm_pntRelativeSimpleZeroKernel_eq hxPos]
      calc
        (analyticOrderNatAt riemannZeta rho : ℝ) *
              (x ^ (rho.re - 1) / ‖rho‖)
            ≤ (analyticOrderNatAt riemannZeta rho : ℝ) *
                (x ^ (sigma - 1) / ‖rho‖) := by
          exact mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hrpow (norm_nonneg rho)) hmult
        _ = x ^ (sigma - 1) *
              ((analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖) := by
          ring_nf
    _ = x ^ (sigma - 1) *
          (∑ rho ∈ input.layer i,
            (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖) := by
      rw [Finset.mul_sum]
    _ ≤ x ^ (sigma - 1) *
          ExplicitFormulaAux.globalReciprocalZeroMultiplicity T :=
      mul_le_mul_of_nonneg_left hmass
        (Real.rpow_nonneg hxNonneg _)

/-- The selected low layer's absolute mass tends to zero after target-scale
normalization under the reciprocal exponent margin. -/
theorem
    tendsto_dynamicPositiveOutsideClusterPNTLayerAbsoluteMass_div_target_zero_reciprocal
    {n : ℕ} {S : Finset ℂ} {H : ℝ → ℝ}
    {beta sigma alpha epsilon : ℝ}
    (input : (x : ℝ) → PositiveZeroOutsideClusterBucketInput (H x) S n)
    (i : Fin n)
    (hHle : ∀ᶠ x : ℝ in atTop,
      H x ≤ carlsonPolynomialHeight alpha x)
    (hHtop : Tendsto H atTop atTop)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta + epsilon < 0)
    (hre : ∀ x rho, rho ∈ (input x).layer i → rho.re ≤ sigma) :
    Tendsto
      (fun m : ℕ =>
        (∑ rho ∈ (input (m : ℝ)).layer i,
            ‖pntRelativeZeroContribution (m : ℝ) rho‖) /
          targetZeroPowerAmplitude beta (m : ℝ))
      atTop (nhds 0) := by
  rcases ExplicitFormulaAux.exists_globalReciprocalZeroMultiplicity_le_log_sq with
    ⟨C, hC, hglobal⟩
  have hlogReal :=
    eventually_one_add_log_polynomialHeight_add_six_le_log_four halpha
  have hlog :
      ∀ᶠ m : ℕ in atTop,
        1 + Real.log ((m : ℝ) ^ alpha + 6) ≤
          (alpha + 2) * Real.log (m : ℝ) ^ 4 :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hlogReal
  have hmajor :
      Tendsto
        (fun m : ℕ =>
          actualReciprocalLowNormalizedLogPowerMajorant
            C alpha beta sigma (m : ℝ))
        atTop (nhds 0) :=
    (tendsto_actualReciprocalLowNormalizedLogPowerMajorant_zero
      hepsilon hmargin).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hHleNat :
      ∀ᶠ m : ℕ in atTop,
        H (m : ℝ) ≤ carlsonPolynomialHeight alpha (m : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hHle
  have hHtopNat : Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop :=
    hHtop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hmPos : 0 < (m : ℝ) := by
      exact_mod_cast (Nat.zero_lt_of_lt hm)
    exact div_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Real.rpow_nonneg hmPos.le _)
  · filter_upwards [
      eventually_ge_atTop (1 : ℕ),
      hHtopNat.eventually (eventually_ge_atTop (4 : ℝ)),
      hHleNat, hlog] with m hm hHfour hHupper hlogBound
    have hmPos : 0 < (m : ℝ) := by
      exact_mod_cast (Nat.zero_lt_of_lt hm)
    have hmNonneg : 0 ≤ (m : ℝ) := hmPos.le
    have hAmplitude : 0 < targetZeroPowerAmplitude beta (m : ℝ) :=
      Real.rpow_pos_of_pos hmPos _
    have hphysical :=
      (input (m : ℝ)).sum_norm_layer_le_rpow_mul_globalReciprocal
        (sigma := sigma) (x := (m : ℝ)) i
        (by exact_mod_cast hm) (hre (m : ℝ))
    have hglobalBound :
        ExplicitFormulaAux.globalReciprocalZeroMultiplicity (H (m : ℝ)) ≤
          C * (1 + Real.log (H (m : ℝ) + 6)) ^ 2 :=
      hglobal (H (m : ℝ)) hHfour
    have hlogMono :
        1 + Real.log (H (m : ℝ) + 6) ≤
          1 + Real.log ((m : ℝ) ^ alpha + 6) := by
      have hlogRaw :
          Real.log (H (m : ℝ) + 6) ≤
            Real.log ((m : ℝ) ^ alpha + 6) := by
        apply Real.log_le_log
        · linarith
        · simpa [carlsonPolynomialHeight] using hHupper
      linarith
    have hleftNonneg :
        0 ≤ 1 + Real.log (H (m : ℝ) + 6) := by
      have hlogPos : 0 < Real.log (H (m : ℝ) + 6) :=
        Real.log_pos (by linarith)
      linarith
    have hlogCombined :
        1 + Real.log (H (m : ℝ) + 6) ≤
          (alpha + 2) * Real.log (m : ℝ) ^ 4 :=
      hlogMono.trans hlogBound
    have hrightNonneg :
        0 ≤ (alpha + 2) * Real.log (m : ℝ) ^ 4 :=
      hleftNonneg.trans hlogCombined
    have hfactorNonneg :
        0 ≤
          ((alpha + 2) * Real.log (m : ℝ) ^ 4 -
              (1 + Real.log (H (m : ℝ) + 6))) *
            ((alpha + 2) * Real.log (m : ℝ) ^ 4 +
              (1 + Real.log (H (m : ℝ) + 6))) :=
      mul_nonneg (sub_nonneg.mpr hlogCombined)
        (add_nonneg hrightNonneg hleftNonneg)
    have hlogSquare :
        (1 + Real.log (H (m : ℝ) + 6)) ^ 2 ≤
          ((alpha + 2) * Real.log (m : ℝ) ^ 4) ^ 2 := by
      nlinarith
    have hreciprocal :
        ExplicitFormulaAux.globalReciprocalZeroMultiplicity (H (m : ℝ)) ≤
          C * ((alpha + 2) * Real.log (m : ℝ) ^ 4) ^ 2 :=
      hglobalBound.trans
        (mul_le_mul_of_nonneg_left hlogSquare hC)
    have hphysicalBound :
        (∑ rho ∈ (input (m : ℝ)).layer i,
            ‖pntRelativeZeroContribution (m : ℝ) rho‖) ≤
          (m : ℝ) ^ (sigma - 1) *
            (C * ((alpha + 2) * Real.log (m : ℝ) ^ 4) ^ 2) :=
      hphysical.trans
        (mul_le_mul_of_nonneg_left hreciprocal
          (Real.rpow_nonneg hmNonneg _))
    have hnormalized :=
      (div_le_div_iff_of_pos_right hAmplitude).2 hphysicalBound
    calc
      (∑ rho ∈ (input (m : ℝ)).layer i,
          ‖pntRelativeZeroContribution (m : ℝ) rho‖) /
          targetZeroPowerAmplitude beta (m : ℝ)
          ≤ ((m : ℝ) ^ (sigma - 1) *
                (C * ((alpha + 2) * Real.log (m : ℝ) ^ 4) ^ 2)) /
              targetZeroPowerAmplitude beta (m : ℝ) := hnormalized
      _ = C * ((alpha + 2) * Real.log (m : ℝ) ^ 4) ^ 2 *
            ((m : ℝ) ^ (sigma - 1) /
              (m : ℝ) ^ (beta - 1)) := by
        unfold targetZeroPowerAmplitude
        ring_nf
      _ = C * ((alpha + 2) * Real.log (m : ℝ) ^ 4) ^ 2 *
            (m : ℝ) ^ ((sigma - 1) - (beta - 1)) := by
        rw [← Real.rpow_sub hmPos]
      _ = actualReciprocalLowNormalizedLogPowerMajorant
            C alpha beta sigma (m : ℝ) := by
        unfold actualReciprocalLowNormalizedLogPowerMajorant
        ring_nf

/-- The selected positive outside absolute mass is eventually below the
residual boundary mass plus any positive loss under the reciprocal margin. -/
theorem
    eventually_selectedPositiveOutsideClusterPNTAbsoluteMass_div_target_lt_boundaryMass_add_reciprocal
    {H : ℝ → ℝ} {S : Finset ℂ}
    {beta sigma alpha epsilon delta : ℝ}
    (input : (x : ℝ) → PositiveZeroOutsideClusterBucketInput (H x) S 2)
    (hreLow : ∀ x rho, rho ∈ (input x).layer (0 : Fin 2) →
      rho.re ≤ sigma)
    (hlowCover : ∀ x,
      ∀ rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) S,
        rho.re ≤ sigma → (input x).bucket rho = (0 : Fin 2))
    (hHle : ∀ᶠ x : ℝ in atTop,
      H x ≤ carlsonPolynomialHeight alpha x)
    (hHtop : Tendsto H atTop atTop)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (halpha : 0 < alpha) (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta + epsilon < 0)
    (hreHigh : ∀ index : ActualCarlsonPositiveZeroIndex sigma,
      actualCarlsonPositiveZero index ∉ S →
        actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hdelta : 0 < delta) :
    ∀ᶠ m : ℕ in atTop,
      dynamicPositiveOutsideClusterPNTAbsoluteMass H S (m : ℝ) /
          targetZeroPowerAmplitude beta (m : ℝ) <
        actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S + delta := by
  have hlow :=
    tendsto_dynamicPositiveOutsideClusterPNTLayerAbsoluteMass_div_target_zero_reciprocal
      input (0 : Fin 2) hHle hHtop halpha hepsilon hmargin hreLow
  have htail :=
    actualCarlsonOutsideClusterNormalizedKernelTail_tendsto_boundaryMass
      S hhalf hone hreHigh
  have hmajor := hlow.add htail
  have hmajorLt :=
    (tendsto_order.mp hmajor).2
      (actualCarlsonOutsideClusterBoundaryMass
        (sigma := sigma) beta S + delta)
      (by
        simpa using
          (lt_add_of_pos_right
            (actualCarlsonOutsideClusterBoundaryMass
              (sigma := sigma) beta S) hdelta))
  filter_upwards [hmajorLt, eventually_ge_atTop (1 : ℕ)] with m hmMajor hm
  have hsplit :=
    truncatedPositiveZeroAbsoluteMass_div_target_le_low_add_CarlsonTail_of_le
      (input (m : ℝ)) (0 : Fin 2)
      (hreLow (m : ℝ)) (hlowCover (m : ℝ))
      hhalf hone hreHigh hm
  exact hsplit.trans_lt hmMajor

/-- Conjugation and the strictly-left real slice upgrade the reciprocal
positive absolute bound to the complete outside absolute mass. -/
theorem
    eventually_selectedFullOutsideClusterPNTAbsoluteMass_div_target_lt_two_mul_boundaryMass_add_reciprocal
    {H : ℝ → ℝ} {S : Finset ℂ}
    {beta sigma alpha epsilon delta : ℝ}
    (input : (x : ℝ) → PositiveZeroOutsideClusterBucketInput (H x) S 2)
    (hS : IsConjugationInvariantCluster S)
    (hreLow : ∀ x rho, rho ∈ (input x).layer (0 : Fin 2) →
      rho.re ≤ sigma)
    (hlowCover : ∀ x,
      ∀ rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) S,
        rho.re ≤ sigma → (input x).bucket rho = (0 : Fin 2))
    (hHnonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ H x)
    (hHle : ∀ᶠ x : ℝ in atTop,
      H x ≤ carlsonPolynomialHeight alpha x)
    (hHtop : Tendsto H atTop atTop)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (halpha : 0 < alpha) (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta + epsilon < 0)
    (hreHigh : ∀ index : ActualCarlsonPositiveZeroIndex sigma,
      actualCarlsonPositiveZero index ∉ S →
        actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hreReal : ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
      rho.re < beta)
    (hdelta : 0 < delta) :
    ∀ᶠ m : ℕ in atTop,
      dynamicFullOutsideClusterPNTAbsoluteMass H S (m : ℝ) /
          targetZeroPowerAmplitude beta (m : ℝ) <
        2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S + delta := by
  have hdelta4 : 0 < delta / 4 := div_pos hdelta (by norm_num)
  have hdelta2 : 0 < delta / 2 := div_pos hdelta (by norm_num)
  have hpositive :=
    eventually_selectedPositiveOutsideClusterPNTAbsoluteMass_div_target_lt_boundaryMass_add_reciprocal
      input hreLow hlowCover hHle hHtop hhalf hone halpha hepsilon
      hmargin hreHigh hdelta4
  have hreal :=
    (dynamicRealOrdinateOutsideClusterPNTAbsoluteMass_targetAmplitudeNegligible
      H S beta hHnonneg hreReal).naturalPoint
  have hrealLt :
      ∀ᶠ m : ℕ in atTop,
        |dynamicRealOrdinateOutsideClusterPNTAbsoluteMass H S (m : ℝ)| /
            targetZeroPowerAmplitude beta (m : ℝ) < delta / 2 :=
    (tendsto_order.mp hreal).2 _ (by simpa using hdelta2)
  filter_upwards
      [hpositive, hrealLt, eventually_gt_atTop (0 : ℕ)] with
      m hpositiveM hrealM hm
  have hmx : 0 < (m : ℝ) := by exact_mod_cast hm
  have hrealNonneg :
      0 ≤ dynamicRealOrdinateOutsideClusterPNTAbsoluteMass H S (m : ℝ) :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  rw [abs_of_nonneg hrealNonneg] at hrealM
  rw [dynamicFullOutsideClusterPNTAbsoluteMass_eq_two_positive_add_real
    hS hmx, add_div, add_div]
  linarith

/-- The reciprocal absolute boundary estimate controls every finite moving
right-edge extension without cancellation. -/
theorem
    eventually_selectedMovingRightEdgeExtension_div_target_lt_two_mul_boundaryMass_add_reciprocal
    {H : ℝ → ℝ} {S : Finset ℂ}
    {beta sigma transferTau alpha epsilon delta : ℝ}
    (input : (x : ℝ) → PositiveZeroOutsideClusterBucketInput (H x) S 2)
    (hS : IsConjugationInvariantCluster S)
    (hreLow : ∀ x rho, rho ∈ (input x).layer (0 : Fin 2) →
      rho.re ≤ sigma)
    (hlowCover : ∀ x,
      ∀ rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) S,
        rho.re ≤ sigma → (input x).bucket rho = (0 : Fin 2))
    (hHnonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ H x)
    (hHle : ∀ᶠ x : ℝ in atTop,
      H x ≤ carlsonPolynomialHeight alpha x)
    (hHtop : Tendsto H atTop atTop)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (halpha : 0 < alpha) (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta + epsilon < 0)
    (hreHigh : ∀ index : ActualCarlsonPositiveZeroIndex sigma,
      actualCarlsonPositiveZero index ∉ S →
        actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hreReal : ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
      rho.re < beta)
    (hdelta : 0 < delta) :
    ∀ᶠ m : ℕ in atTop,
      |dynamicVisibleClusterPNTMain H
          (movingRightEdgeExceptionalCluster H transferTau (m : ℝ) \ S)
          (m : ℝ)| /
          targetZeroPowerAmplitude beta (m : ℝ) <
        2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S + delta := by
  have hfull :=
    eventually_selectedFullOutsideClusterPNTAbsoluteMass_div_target_lt_two_mul_boundaryMass_add_reciprocal
      input hS hreLow hlowCover hHnonneg hHle hHtop hhalf hone
      halpha hepsilon hmargin hreHigh hreReal hdelta
  exact
    eventually_selectedMovingRightEdgeExtension_div_target_lt_two_mul_boundaryMass_add
      (sigma := sigma) (transferTau := transferTau) hfull

end
end PrimeNumberTheorem
