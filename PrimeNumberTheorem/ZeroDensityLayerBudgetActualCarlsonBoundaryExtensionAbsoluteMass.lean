import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonPointwiseGapExtensionAbsoluteMass
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBoundaryTruncatedSplit
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonFiniteSeedGapTransferCluster

/-!
# Carlson boundary capture for moving-extension absolute mass

The strict pointwise gap of stack86 is replaced by a non-strict real-part cap.
Boundary zeros contribute the summable residual boundary mass, which can be
made arbitrarily small by enlarging the finite conjugation-stable cluster.
-/

namespace PrimeNumberTheorem

open scoped BigOperators Topology
open Filter Complex

noncomputable section

/-- The finite positive absolute mass obeys the non-strict Carlson tail bound.
Zeros on `Re rho = beta` remain in the limiting boundary mass. -/
theorem truncatedPositiveZeroAbsoluteMass_div_target_le_low_add_CarlsonTail_of_le
    {T sigma beta : ℝ} {S : Finset ℂ} {n : ℕ}
    (input : PositiveZeroOutsideClusterBucketInput T S n) (i : Fin n)
    (hreLow : ∀ rho ∈ input.layer i, rho.re ≤ sigma)
    (hlowCover :
      ∀ rho ∈ positiveNontrivialZerosOutsideClusterFinset T S,
        rho.re ≤ sigma → input.bucket rho = i)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hreHigh :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index ≤ beta)
    {m : ℕ} (hm : 1 ≤ m) :
    (∑ rho ∈ positiveNontrivialZerosOutsideClusterFinset T S,
        ‖pntRelativeZeroContribution (m : ℝ) rho‖) /
          targetZeroPowerAmplitude beta (m : ℝ) ≤
      (∑ rho ∈ input.layer i,
          ‖pntRelativeZeroContribution (m : ℝ) rho‖) /
            targetZeroPowerAmplitude beta (m : ℝ) +
        actualCarlsonOutsideClusterNormalizedKernelTail
          (sigma := sigma) beta S m := by
  let all := positiveNontrivialZerosOutsideClusterFinset T S
  let high := actualHighPositiveZerosOutsideClusterFinset sigma T S
  let contribution : ℂ → ℝ :=
    fun rho => ‖pntRelativeZeroContribution (m : ℝ) rho‖
  have hlow :
      input.layer i = all.filter (fun rho => rho.re ≤ sigma) :=
    lowLayer_eq_filter_re_le input i hreLow hlowCover
  have hhigh :
      high = all.filter (fun rho => ¬rho.re ≤ sigma) := by
    ext rho
    simp only [high, all, actualHighPositiveZerosOutsideClusterFinset,
      Finset.mem_filter]
    constructor
    · rintro ⟨hbase, hlt⟩
      exact ⟨hbase, not_le.mpr hlt⟩
    · rintro ⟨hbase, hnle⟩
      exact ⟨hbase, lt_of_not_ge hnle⟩
  have hpartition :
      (∑ rho ∈ all, contribution rho) =
        (∑ rho ∈ input.layer i, contribution rho) +
          ∑ rho ∈ high, contribution rho := by
    rw [hlow, hhigh]
    exact
      (Finset.sum_filter_add_sum_filter_not
        all (fun rho => rho.re ≤ sigma) contribution).symm
  have houtside :
      ∀ rho ∈ actualHighPositiveZeroSubtypeFinset sigma T S,
        rho.1 ∉ S :=
    fun _ hrho => actualHighPositiveZeroSubtypeFinset_outside hrho
  have hfinite :=
    finite_actualHighPositiveZeroKernelSum_le_CarlsonTail_of_le
      S hhalf hone hreHigh
      (actualHighPositiveZeroSubtypeFinset sigma T S)
      houtside hm
  have hfinite' :
      (∑ rho ∈ high,
        contribution rho / targetZeroPowerAmplitude beta (m : ℝ)) ≤
          actualCarlsonOutsideClusterNormalizedKernelTail
            (sigma := sigma) beta S m := by
    change
      (∑ rho ∈ actualHighPositiveZerosOutsideClusterFinset sigma T S,
        ‖pntRelativeZeroContribution (m : ℝ) rho‖ /
          targetZeroPowerAmplitude beta (m : ℝ)) ≤
        actualCarlsonOutsideClusterNormalizedKernelTail
          (sigma := sigma) beta S m
    rw [← sum_actualHighPositiveZeroSubtypeFinset sigma T S]
    simpa [targetZeroPowerAmplitude] using hfinite
  change
    (∑ rho ∈ all, contribution rho) /
          targetZeroPowerAmplitude beta (m : ℝ) ≤ _
  have hhighDiv :
      (∑ rho ∈ high, contribution rho) /
          targetZeroPowerAmplitude beta (m : ℝ) =
        ∑ rho ∈ high,
          contribution rho / targetZeroPowerAmplitude beta (m : ℝ) := by
    rw [Finset.sum_div]
  rw [hpartition, add_div, hhighDiv]
  exact add_le_add le_rfl hfinite'

/-- The selected positive outside absolute mass is eventually bounded by the
residual Carlson boundary mass plus any positive loss. -/
theorem
    eventually_selectedPositiveOutsideClusterPNTAbsoluteMass_div_target_lt_boundaryMass_add
    {H : ℝ → ℝ} {S : Finset ℂ}
    {beta sigma alpha gammaLow epsilonLow delta : ℝ}
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (halpha : 0 < alpha)
    (hgammaLow : 0 < gammaLow)
    (hepsilonLow : 0 < epsilonLow)
    (hlowLow : gammaLow + sigma - beta + epsilonLow < 0)
    (hlowHigh : alpha + sigma - beta - gammaLow + epsilonLow < 0)
    (hHle :
      ∀ᶠ x : ℝ in atTop,
        H x ≤ carlsonPolynomialHeight alpha x)
    (hreHigh :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hdelta : 0 < delta) :
    ∀ᶠ m : ℕ in atTop,
      dynamicPositiveOutsideClusterPNTAbsoluteMass H S (m : ℝ) /
          targetZeroPowerAmplitude beta (m : ℝ) <
        actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S + delta := by
  let polynomialInput := fun y =>
    pntHybridCanonicalTwoStripOutsideClusterBucketInput
      sigma (carlsonPolynomialHeight alpha y) S
  rcases
      exists_canonicalTwoStripOutsideCluster_uniform_norm_lower_bound
        (carlsonPolynomialHeight alpha) sigma S with
    ⟨kappa, hkappa, hnorm⟩
  have hlowReal :=
    tendsto_dynamicOutsideClusterTwoHeightMass_div_target
      polynomialInput 0 hkappa hnorm
      (fun _ _ hrho =>
        pntHybridCanonicalTwoStripOutsideCluster_lowLayer_re_le hrho)
      halpha hgammaLow hepsilonLow hlowLow hlowHigh
  have hlow := hlowReal.comp tendsto_natCast_atTop_atTop
  have htail :=
    actualCarlsonOutsideClusterNormalizedKernelTail_tendsto_boundaryMass
      S hsigma hsigmaOne hreHigh
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
  have hHleNat := tendsto_natCast_atTop_atTop.eventually hHle
  filter_upwards
      [hmajorLt, eventually_ge_atTop (1 : ℕ), hHleNat] with
      m hmajorM hm hHm
  have hamp : 0 < targetZeroPowerAmplitude beta (m : ℝ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (Nat.zero_lt_of_lt hm)) _
  let selectedInput :=
    pntHybridCanonicalTwoStripOutsideClusterBucketInput
      sigma (H (m : ℝ)) S
  have hsplit :=
    truncatedPositiveZeroAbsoluteMass_div_target_le_low_add_CarlsonTail_of_le
      selectedInput 0
      (fun _ hrho =>
        pntHybridCanonicalTwoStripOutsideCluster_lowLayer_re_le hrho)
      (fun rho hrho hre =>
        pntHybridCanonicalTwoStripOutsideCluster_low_cover hrho hre)
      hsigma hsigmaOne hreHigh hm
  have hselectedLow :=
    canonicalSelectedLowLayerAbsoluteMass_le_polynomialTwoHeightMass
      (S := S) (sigma := sigma) (gamma := gammaLow)
      (x := (m : ℝ)) hHm
  have hselectedLowDiv :=
    (div_le_div_iff_of_pos_right hamp).2 hselectedLow
  have hbound := hsplit.trans (add_le_add hselectedLowDiv le_rfl)
  have hbound' :
      dynamicPositiveOutsideClusterPNTAbsoluteMass H S (m : ℝ) /
          targetZeroPowerAmplitude beta (m : ℝ) ≤
        (dynamicOutsideClusterLowOrdinateMass
              (carlsonPolynomialHeight alpha)
              (carlsonPolynomialHeight gammaLow) S polynomialInput 0 (m : ℝ) +
            dynamicOutsideClusterHighAnnulusMass
              (carlsonPolynomialHeight alpha)
              (carlsonPolynomialHeight gammaLow) S polynomialInput 0 (m : ℝ)) /
            targetZeroPowerAmplitude beta (m : ℝ) +
          actualCarlsonOutsideClusterNormalizedKernelTail
            (sigma := sigma) beta S m := by
    simpa [dynamicPositiveOutsideClusterPNTAbsoluteMass,
      selectedInput, polynomialInput] using hbound
  exact hbound'.trans_lt hmajorM

/-- Conjugation upgrades the positive boundary estimate to the complete
outside absolute mass; the finite real-ordinate slice is target-negligible. -/
theorem
    eventually_selectedFullOutsideClusterPNTAbsoluteMass_div_target_lt_two_mul_boundaryMass_add
    {H : ℝ → ℝ} {S : Finset ℂ}
    {beta sigma alpha gammaLow epsilonLow delta : ℝ}
    (hS : IsConjugationInvariantCluster S)
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (halpha : 0 < alpha)
    (hgammaLow : 0 < gammaLow)
    (hepsilonLow : 0 < epsilonLow)
    (hlowLow : gammaLow + sigma - beta + epsilonLow < 0)
    (hlowHigh : alpha + sigma - beta - gammaLow + epsilonLow < 0)
    (hHnonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ H x)
    (hHle :
      ∀ᶠ x : ℝ in atTop,
        H x ≤ carlsonPolynomialHeight alpha x)
    (hreHigh :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hreReal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
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
    eventually_selectedPositiveOutsideClusterPNTAbsoluteMass_div_target_lt_boundaryMass_add
      hsigma hsigmaOne halpha hgammaLow hepsilonLow
      hlowLow hlowHigh hHle hreHigh hdelta4
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
      0 ≤ dynamicRealOrdinateOutsideClusterPNTAbsoluteMass H S (m : ℝ) := by
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  rw [abs_of_nonneg hrealNonneg] at hrealM
  rw [dynamicFullOutsideClusterPNTAbsoluteMass_eq_two_positive_add_real
    hS hmx, add_div, add_div]
  linarith

/-- Every moving finite extension is bounded by twice the residual boundary
mass, independently of cancellation inside the selected subset. -/
theorem
    eventually_selectedMovingRightEdgeExtension_div_target_lt_two_mul_boundaryMass_add
    {H : ℝ → ℝ} {S : Finset ℂ} {sigma beta transferTau delta : ℝ}
    (hfull :
      ∀ᶠ m : ℕ in atTop,
        dynamicFullOutsideClusterPNTAbsoluteMass H S (m : ℝ) /
            targetZeroPowerAmplitude beta (m : ℝ) <
          2 * actualCarlsonOutsideClusterBoundaryMass
            (sigma := sigma) beta S + delta) :
    ∀ᶠ m : ℕ in atTop,
      |dynamicVisibleClusterPNTMain H
          (movingRightEdgeExceptionalCluster H transferTau (m : ℝ) \ S)
          (m : ℝ)| /
          targetZeroPowerAmplitude beta (m : ℝ) <
        2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S + delta := by
  have hamplitude :=
    eventually_naturalPoint_pos_of_eventually_pos
      (targetZeroPowerAmplitude_eventually_pos beta)
  filter_upwards [hfull, hamplitude] with m hfullM hamp
  exact
    ((div_le_div_iff_of_pos_right hamp).2
      (abs_dynamicVisibleClusterPNTMain_sdiff_le_fullOutsideAbsoluteMass
        H S (movingRightEdgeExceptionalCluster H transferTau (m : ℝ))
          (m : ℝ))).trans_lt hfullM

/-- A finite conjugation-stable enlargement captures enough boundary mass to
put every residual moving extension strictly below the prescribed gap
`c - q`.  No oscillation witness for the enlarged cluster is asserted. -/
theorem exists_boundaryCapturedCluster_movingRightEdgeExtension_div_target_lt
    {S₀ : Finset ℂ} {H : ℝ → ℝ}
    {sigma beta alpha gammaLow epsilonLow transferTau c q : ℝ}
    (hS₀ : ∀ rho : ℂ, rho ∈ S₀ ↔ (starRingEnd ℂ) rho ∈ S₀)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (halpha : 0 < alpha)
    (hgammaLow : 0 < gammaLow)
    (hepsilonLow : 0 < epsilonLow)
    (hlowLow : gammaLow + sigma - beta + epsilonLow < 0)
    (hlowHigh : alpha + sigma - beta - gammaLow + epsilonLow < 0)
    (hHnonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ H x)
    (hHle :
      ∀ᶠ x : ℝ in atTop,
        H x ≤ carlsonPolynomialHeight alpha x)
    (hqC : q < c)
    (hcap : OutsideClusterRealPartCap S₀ beta) :
    ∃ S : Finset ℂ,
      (∀ rho ∈ S₀, rho ∈ S) ∧
      (∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S) ∧
      OutsideClusterRealPartCap S beta ∧
      (∀ rho ∈ S, rho ∉ S₀ →
        rho ∉ realOrdinateNontrivialZerosFinset 0 → rho.re = beta) ∧
      ∀ᶠ m : ℕ in atTop,
        |dynamicVisibleClusterPNTMain H
            (movingRightEdgeExceptionalCluster H transferTau (m : ℝ) \ S)
            (m : ℝ)| /
            targetZeroPowerAmplitude beta (m : ℝ) < c - q := by
  rcases
      exists_actualCarlsonFiniteSeedGapTransferCluster
        hS₀ hhalf hone hqC hcap with
    ⟨S, hS₀S, hS, hcapS, hboundaryAdded,
      hreHigh, hreReal, hboundary⟩
  let delta := (c - q) -
    2 * actualCarlsonOutsideClusterBoundaryMass
      (sigma := sigma) beta S
  have hdelta : 0 < delta := by
    simpa [delta] using hboundary
  have hfull :=
    eventually_selectedFullOutsideClusterPNTAbsoluteMass_div_target_lt_two_mul_boundaryMass_add
      (fun rho => (hS rho).symm) hhalf hone halpha hgammaLow hepsilonLow
      hlowLow hlowHigh hHnonneg hHle hreHigh hreReal hdelta
  have hextension :=
    eventually_selectedMovingRightEdgeExtension_div_target_lt_two_mul_boundaryMass_add
      (sigma := sigma) (transferTau := transferTau) (delta := delta) hfull
  refine ⟨S, hS₀S, hS, hcapS, hboundaryAdded, ?_⟩
  simpa [delta] using hextension

end

end PrimeNumberTheorem
