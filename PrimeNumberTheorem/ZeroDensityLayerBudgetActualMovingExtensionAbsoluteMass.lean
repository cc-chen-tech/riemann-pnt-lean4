import PrimeNumberTheorem.ZeroDensityLayerBudgetActualMovingRightEdgeSignedSeedStabilityTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualPositiveOutsideClusterCapUnifiedTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightTwoHeightFullTail

/-!
# Cancellation-free absolute mass for a moving right-edge extension

The norm of a complete signed outside-cluster sum cannot dominate a sub-sum,
because the complete sum may contain additional cancellation.  This module
instead sums the norms of all outside-seed terms.  The resulting absolute mass
is monotone, inherits the selected two-height Carlson bounds, and dominates
the moving extension pointwise.
-/

open Complex Filter
open scoped BigOperators Topology ComplexConjugate

namespace PrimeNumberTheorem

/-- Absolute multiplicity-weighted mass of the positive-ordinate zero terms
outside a fixed cluster. -/
noncomputable def dynamicPositiveOutsideClusterPNTAbsoluteMass
    (H : ℝ → ℝ) (S : Finset ℂ) (x : ℝ) : ℝ :=
  ∑ rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) S,
    ‖pntRelativeZeroContribution x rho‖

/-- Absolute mass of the negative-ordinate zero terms outside a fixed
cluster. -/
noncomputable def dynamicNegativeOutsideClusterPNTAbsoluteMass
    (H : ℝ → ℝ) (S : Finset ℂ) (x : ℝ) : ℝ :=
  ∑ rho ∈ negativeNontrivialZerosOutsideClusterFinset (H x) S,
    ‖pntRelativeZeroContribution x rho‖

/-- Absolute mass of the real-ordinate zero terms outside a fixed cluster. -/
noncomputable def dynamicRealOrdinateOutsideClusterPNTAbsoluteMass
    (H : ℝ → ℝ) (S : Finset ℂ) (x : ℝ) : ℝ :=
  ∑ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset (H x) S,
    ‖pntRelativeZeroContribution x rho‖

/-- Absolute mass of every visible nontrivial-zero term outside a fixed
cluster. -/
noncomputable def dynamicFullOutsideClusterPNTAbsoluteMass
    (H : ℝ → ℝ) (S : Finset ℂ) (x : ℝ) : ℝ :=
  ∑ rho ∈ nontrivialZerosOutsideClusterFinset (H x) S,
    ‖pntRelativeZeroContribution x rho‖

/-- The selected canonical low-layer absolute mass is dominated by the
polynomial-envelope two-height mass. -/
theorem canonicalSelectedLowLayerAbsoluteMass_le_polynomialTwoHeightMass
    {H : ℝ → ℝ} {alpha gamma sigma x : ℝ} {S : Finset ℂ}
    (hHle : H x ≤ carlsonPolynomialHeight alpha x) :
    (∑ rho ∈
        (pntHybridCanonicalTwoStripOutsideClusterBucketInput
          sigma (H x) S).layer 0,
        ‖pntRelativeZeroContribution x rho‖) ≤
      dynamicOutsideClusterLowOrdinateMass
          (carlsonPolynomialHeight alpha)
          (carlsonPolynomialHeight gamma) S
          (fun y =>
            pntHybridCanonicalTwoStripOutsideClusterBucketInput
              sigma (carlsonPolynomialHeight alpha y) S)
          0 x +
        dynamicOutsideClusterHighAnnulusMass
          (carlsonPolynomialHeight alpha)
          (carlsonPolynomialHeight gamma) S
          (fun y =>
            pntHybridCanonicalTwoStripOutsideClusterBucketInput
              sigma (carlsonPolynomialHeight alpha y) S)
          0 x := by
  calc
    (∑ rho ∈
        (pntHybridCanonicalTwoStripOutsideClusterBucketInput
          sigma (H x) S).layer 0,
        ‖pntRelativeZeroContribution x rho‖) ≤
      ∑ rho ∈
        (pntHybridCanonicalTwoStripOutsideClusterBucketInput
          sigma (carlsonPolynomialHeight alpha x) S).layer 0,
        ‖pntRelativeZeroContribution x rho‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (canonicalSelectedLayer_subset_polynomialLayer 0 hHle)
        (fun _ _ _ => norm_nonneg _)
    _ = _ :=
      dynamicOutsideClusterLayerMass_eq_low_add_high
        (carlsonPolynomialHeight alpha)
        (carlsonPolynomialHeight gamma) S
        (fun y =>
          pntHybridCanonicalTwoStripOutsideClusterBucketInput
            sigma (carlsonPolynomialHeight alpha y) S)
        0 x

/-- The selected canonical high-layer absolute mass is dominated by the
polynomial-envelope Carlson strip mass. -/
theorem canonicalSelectedHighLayerAbsoluteMass_le_polynomialCarlsonStrip
    {H : ℝ → ℝ} {alpha sigma tau x : ℝ} {S : Finset ℂ}
    (hHle : H x ≤ carlsonPolynomialHeight alpha x)
    (hcap :
      ∀ rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) S,
        sigma < rho.re → rho.re ≤ tau) :
    (∑ rho ∈
        (pntHybridCanonicalTwoStripOutsideClusterBucketInput
          sigma (H x) S).layer 1,
        ‖pntRelativeZeroContribution x rho‖) ≤
      ∑ rho ∈ actualPositiveCarlsonStrip sigma tau
          (carlsonPolynomialHeight alpha x),
        ‖pntRelativeZeroContribution x rho‖ :=
  Finset.sum_le_sum_of_subset_of_nonneg
    (canonicalSelectedHighLayer_subset_polynomialCarlsonStrip
      hHle hcap)
    (fun _ _ _ => norm_nonneg _)

/-- Pointwise selected-height positive absolute-mass majorant. -/
theorem dynamicSelectedPositiveOutsideClusterPNTAbsoluteMass_le
    {H : ℝ → ℝ} {alpha gamma sigma tau x : ℝ} {S : Finset ℂ}
    (hHle : H x ≤ carlsonPolynomialHeight alpha x)
    (hcap :
      ∀ rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) S,
        sigma < rho.re → rho.re ≤ tau) :
    dynamicPositiveOutsideClusterPNTAbsoluteMass H S x ≤
      (dynamicOutsideClusterLowOrdinateMass
          (carlsonPolynomialHeight alpha)
          (carlsonPolynomialHeight gamma) S
          (fun y =>
            pntHybridCanonicalTwoStripOutsideClusterBucketInput
              sigma (carlsonPolynomialHeight alpha y) S)
          0 x +
        dynamicOutsideClusterHighAnnulusMass
          (carlsonPolynomialHeight alpha)
          (carlsonPolynomialHeight gamma) S
          (fun y =>
            pntHybridCanonicalTwoStripOutsideClusterBucketInput
              sigma (carlsonPolynomialHeight alpha y) S)
          0 x) +
      ∑ rho ∈ actualPositiveCarlsonStrip sigma tau
          (carlsonPolynomialHeight alpha x),
        ‖pntRelativeZeroContribution x rho‖ := by
  let input := fun y =>
    pntHybridCanonicalTwoStripOutsideClusterBucketInput
      sigma (H y) S
  have hdecomp :
      dynamicPositiveOutsideClusterPNTAbsoluteMass H S x =
        ∑ i : Fin 2, ∑ rho ∈ (input x).layer i,
          ‖pntRelativeZeroContribution x rho‖ := by
    have hcomplex :=
      (input x).certificate.sum_decomposition
        (fun rho => (‖pntRelativeZeroContribution x rho‖ : ℂ))
    norm_cast at hcomplex
  rw [hdecomp, Fin.sum_univ_two]
  exact add_le_add
    (canonicalSelectedLowLayerAbsoluteMass_le_polynomialTwoHeightMass
      (gamma := gamma) hHle)
    (canonicalSelectedHighLayerAbsoluteMass_le_polynomialCarlsonStrip
      hHle hcap)

/-- Selected positive outside absolute mass is negligible at the target
amplitude under the two-height Carlson margins. -/
theorem
    selectedPositiveOutsideClusterPNTAbsoluteMass_targetAmplitudeNegligible
    {H : ℝ → ℝ} {S : Finset ℂ}
    {beta sigma tau alpha gammaLow epsilonLow
      gammaHigh epsilonHigh : ℝ}
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (halpha : 0 < alpha)
    (hgammaLow : 0 < gammaLow)
    (hepsilonLow : 0 < epsilonLow)
    (hlowLow : gammaLow + sigma - beta + epsilonLow < 0)
    (hlowHigh :
      alpha + sigma - beta - gammaLow + epsilonLow < 0)
    (hgammaHigh : 0 < gammaHigh)
    (hgammaHighAlpha : gammaHigh ≤ alpha)
    (hepsilonHigh : 0 < epsilonHigh)
    (hstripLow :
      targetAmplitudeCarlsonTwoHeightLowExponent
          beta sigma tau gammaHigh + epsilonHigh < 0)
    (hstripHigh :
      targetAmplitudeCarlsonTwoHeightHighExponent
          beta sigma tau alpha gammaHigh + epsilonHigh < 0)
    (hHle :
      ∀ᶠ x : ℝ in atTop,
        H x ≤ carlsonPolynomialHeight alpha x)
    (hcap :
      ∀ x rho,
        rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) S →
          sigma < rho.re → rho.re ≤ tau) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (dynamicPositiveOutsideClusterPNTAbsoluteMass H S) := by
  let polynomialInput := fun y =>
    pntHybridCanonicalTwoStripOutsideClusterBucketInput
      sigma (carlsonPolynomialHeight alpha y) S
  rcases
      exists_canonicalTwoStripOutsideCluster_uniform_norm_lower_bound
        (carlsonPolynomialHeight alpha) sigma S with
    ⟨kappa, hkappa, hnorm⟩
  have hlow :=
    tendsto_dynamicOutsideClusterTwoHeightMass_div_target
      polynomialInput 0 hkappa hnorm
      (fun _ _ hrho =>
        pntHybridCanonicalTwoStripOutsideCluster_lowLayer_re_le hrho)
      halpha hgammaLow hepsilonLow hlowLow hlowHigh
  have hstrip :=
    tendsto_actualPositiveCarlsonStripTargetAmplitudeMass_twoHeight
      hsigma hsigmaOne halpha hgammaHigh hgammaHighAlpha
      hepsilonHigh hstripLow hstripHigh
  have hmajor := hlow.add hstrip
  unfold TargetAmplitudeNegligible
  refine squeeze_zero' ?_ ?_ (by simpa using hmajor)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact div_nonneg (abs_nonneg _)
      (Real.rpow_nonneg (zero_le_one.trans hx) _)
  · filter_upwards
      [eventually_ge_atTop (1 : ℝ), hHle] with x hx hHx
    have hamp : 0 < targetZeroPowerAmplitude beta x :=
      Real.rpow_pos_of_pos (zero_lt_one.trans_le hx) _
    have hp :=
      dynamicSelectedPositiveOutsideClusterPNTAbsoluteMass_le
        (gamma := gammaLow) hHx (hcap x)
    have hmassNonneg :
        0 ≤ dynamicPositiveOutsideClusterPNTAbsoluteMass H S x :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    rw [abs_of_nonneg hmassNonneg]
    have hdiv := (div_le_div_iff_of_pos_right hamp).2 hp
    simpa [actualPositiveCarlsonStripTargetAmplitudeMass, add_div] using hdiv

/-- Real-ordinate outside absolute mass is negligible when the fixed real
slice lies strictly left of the target line. -/
theorem
    dynamicRealOrdinateOutsideClusterPNTAbsoluteMass_targetAmplitudeNegligible
    (H : ℝ → ℝ) (S : Finset ℂ) (beta : ℝ)
    (hHnonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ H x)
    (hre :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (dynamicRealOrdinateOutsideClusterPNTAbsoluteMass H S) := by
  let realZeros := realOrdinateNontrivialZerosOutsideClusterFinset 0 S
  have hsum :
      Tendsto
        (fun x : ℝ =>
          ∑ rho ∈ realZeros,
            ‖pntRelativeZeroContribution x rho‖ /
              targetZeroPowerAmplitude beta x)
        atTop (nhds 0) := by
    simpa only [Finset.sum_const_zero] using
      (tendsto_finset_sum realZeros fun rho hrho =>
        tendsto_norm_pntRelativeZeroContribution_div_targetZeroPowerAmplitude
          (hre rho hrho))
  unfold TargetAmplitudeNegligible
  refine squeeze_zero' ?_ ?_ hsum
  · filter_upwards
      [targetZeroPowerAmplitude_eventually_pos beta] with x hx
    exact div_nonneg (abs_nonneg _) hx.le
  · filter_upwards
      [targetZeroPowerAmplitude_eventually_pos beta, hHnonneg] with
      x hxAmplitude hxHeight
    have hset :
        realOrdinateNontrivialZerosOutsideClusterFinset (H x) S =
          realZeros :=
      realOrdinateNontrivialZerosOutsideClusterFinset_eq_zeroHeight
        hxHeight
    rw [dynamicRealOrdinateOutsideClusterPNTAbsoluteMass, hset,
      abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _),
      Finset.sum_div]

/-- Exact positive/negative/real partition of the outside absolute mass. -/
theorem dynamicFullOutsideClusterPNTAbsoluteMass_eq_positive_add_negative_add_real
    (H : ℝ → ℝ) (S : Finset ℂ) (x : ℝ) :
    dynamicFullOutsideClusterPNTAbsoluteMass H S x =
      dynamicPositiveOutsideClusterPNTAbsoluteMass H S x +
        dynamicNegativeOutsideClusterPNTAbsoluteMass H S x +
          dynamicRealOrdinateOutsideClusterPNTAbsoluteMass H S x := by
  have hpartition :=
    finiteZeroSumOutsideCluster_eq_positive_add_negative_add_real
      (H x) S (fun rho => (‖pntRelativeZeroContribution x rho‖ : ℂ))
  have hre := congrArg Complex.re hpartition
  simpa [dynamicFullOutsideClusterPNTAbsoluteMass,
    dynamicPositiveOutsideClusterPNTAbsoluteMass,
    dynamicNegativeOutsideClusterPNTAbsoluteMass,
    dynamicRealOrdinateOutsideClusterPNTAbsoluteMass] using hre

/-- Conjugation identifies negative and positive outside absolute masses. -/
theorem dynamicNegativeOutsideClusterPNTAbsoluteMass_eq_positive
    {H : ℝ → ℝ} {S : Finset ℂ}
    (hS : IsConjugationInvariantCluster S)
    {x : ℝ} (hx : 0 < x) :
    dynamicNegativeOutsideClusterPNTAbsoluteMass H S x =
      dynamicPositiveOutsideClusterPNTAbsoluteMass H S x := by
  have hconj :=
    sum_negativeOutsideCluster_eq_conj_sum_positiveOutsideCluster
      (H x) S (fun rho => (‖pntRelativeZeroContribution x rho‖ : ℂ))
      hS (by
        intro rho hrho
        have hzero := (mem_nontrivialZerosFinset.mp hrho).1
        change
          (‖pntRelativeZeroContribution x ((starRingEnd ℂ) rho)‖ : ℂ) =
            (starRingEnd ℂ)
              (‖pntRelativeZeroContribution x rho‖ : ℂ)
        rw [pntRelativeZeroContribution_conj hx hzero, norm_conj]
        simp)
  have hre := congrArg Complex.re hconj
  simpa [dynamicNegativeOutsideClusterPNTAbsoluteMass,
    dynamicPositiveOutsideClusterPNTAbsoluteMass] using hre

/-- Full outside absolute mass is twice the positive mass plus the real
mass for a conjugation-invariant fixed seed. -/
theorem dynamicFullOutsideClusterPNTAbsoluteMass_eq_two_positive_add_real
    {H : ℝ → ℝ} {S : Finset ℂ}
    (hS : IsConjugationInvariantCluster S)
    {x : ℝ} (hx : 0 < x) :
    dynamicFullOutsideClusterPNTAbsoluteMass H S x =
      dynamicPositiveOutsideClusterPNTAbsoluteMass H S x +
        dynamicPositiveOutsideClusterPNTAbsoluteMass H S x +
          dynamicRealOrdinateOutsideClusterPNTAbsoluteMass H S x := by
  rw [dynamicFullOutsideClusterPNTAbsoluteMass_eq_positive_add_negative_add_real,
    dynamicNegativeOutsideClusterPNTAbsoluteMass_eq_positive hS hx]

/-- Selected full outside absolute mass is negligible at the target
amplitude. -/
theorem selectedFullOutsideClusterPNTAbsoluteMass_targetAmplitudeNegligible
    {H : ℝ → ℝ} {S : Finset ℂ}
    {beta sigma tau alpha gammaLow epsilonLow
      gammaHigh epsilonHigh : ℝ}
    (hS : IsConjugationInvariantCluster S)
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (halpha : 0 < alpha)
    (hgammaLow : 0 < gammaLow)
    (hepsilonLow : 0 < epsilonLow)
    (hlowLow : gammaLow + sigma - beta + epsilonLow < 0)
    (hlowHigh :
      alpha + sigma - beta - gammaLow + epsilonLow < 0)
    (hgammaHigh : 0 < gammaHigh)
    (hgammaHighAlpha : gammaHigh ≤ alpha)
    (hepsilonHigh : 0 < epsilonHigh)
    (hstripLow :
      targetAmplitudeCarlsonTwoHeightLowExponent
          beta sigma tau gammaHigh + epsilonHigh < 0)
    (hstripHigh :
      targetAmplitudeCarlsonTwoHeightHighExponent
          beta sigma tau alpha gammaHigh + epsilonHigh < 0)
    (hHnonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ H x)
    (hHle :
      ∀ᶠ x : ℝ in atTop,
        H x ≤ carlsonPolynomialHeight alpha x)
    (hcap :
      ∀ x rho,
        rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) S →
          sigma < rho.re → rho.re ≤ tau)
    (hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (dynamicFullOutsideClusterPNTAbsoluteMass H S) := by
  have hpositive :=
    selectedPositiveOutsideClusterPNTAbsoluteMass_targetAmplitudeNegligible
      hsigma hsigmaOne halpha hgammaLow hepsilonLow
      hlowLow hlowHigh hgammaHigh hgammaHighAlpha
      hepsilonHigh hstripLow hstripHigh hHle hcap
  have hrealMass :=
    dynamicRealOrdinateOutsideClusterPNTAbsoluteMass_targetAmplitudeNegligible
      H S beta hHnonneg hreal
  have hamplitude := targetZeroPowerAmplitude_eventually_pos beta
  have hmajor :=
    (hpositive.add hamplitude hpositive).add hamplitude hrealMass
  apply hmajor.of_eventually_abs_le hamplitude
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [dynamicFullOutsideClusterPNTAbsoluteMass_eq_two_positive_add_real
    hS hx]
  rw [abs_of_nonneg]
  exact add_nonneg
    (add_nonneg
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Finset.sum_nonneg fun _ _ => norm_nonneg _))
    (Finset.sum_nonneg fun _ _ => norm_nonneg _)

/-- Every moving finite extension of `S` is pointwise dominated by the full
outside absolute mass of `S`. -/
theorem abs_dynamicVisibleClusterPNTMain_sdiff_le_fullOutsideAbsoluteMass
    (H : ℝ → ℝ) (S E : Finset ℂ) (x : ℝ) :
    |dynamicVisibleClusterPNTMain H (E \ S) x| ≤
      dynamicFullOutsideClusterPNTAbsoluteMass H S x := by
  unfold dynamicVisibleClusterPNTMain dynamicVisibleClusterPNTZeroSum
  calc
    |(∑ rho ∈ nontrivialZerosFinset (H x),
        if rho ∈ E \ S then pntRelativeZeroContribution x rho else 0).re| ≤
      ‖∑ rho ∈ nontrivialZerosFinset (H x),
        if rho ∈ E \ S then pntRelativeZeroContribution x rho else 0‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ∑ rho ∈ nontrivialZerosFinset (H x),
        ‖if rho ∈ E \ S then pntRelativeZeroContribution x rho else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ rho ∈ nontrivialZerosFinset (H x),
        if rho ∈ S then 0 else ‖pntRelativeZeroContribution x rho‖ := by
      apply Finset.sum_le_sum
      intro rho hrho
      by_cases hE : rho ∈ E \ S
      · have hnotS := (Finset.mem_sdiff.mp hE).2
        simp [hE, hnotS]
      · by_cases hmemS : rho ∈ S <;> simp [hE, hmemS]
    _ = dynamicFullOutsideClusterPNTAbsoluteMass H S x := by
      unfold dynamicFullOutsideClusterPNTAbsoluteMass
        nontrivialZerosOutsideClusterFinset
      rw [show nontrivialZerosFinset (H x) \ S =
          (nontrivialZerosFinset (H x)).filter (fun rho => rho ∉ S) by
        ext rho
        simp]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro rho hrho
      by_cases hmemS : rho ∈ S <;> simp [hmemS]

/-- The exact moving right-edge extension used in stacks81-82 is negligible
whenever the fixed-seed outside absolute mass is negligible. -/
theorem selectedMovingRightEdgeExtension_targetAmplitudeNegligible
    {H : ℝ → ℝ} {S : Finset ℂ} {beta tau : ℝ}
    (hfull :
      TargetAmplitudeNegligible
        (targetZeroPowerAmplitude beta)
        (dynamicFullOutsideClusterPNTAbsoluteMass H S)) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (fun x =>
        dynamicVisibleClusterPNTMain H
          (movingRightEdgeExceptionalCluster H tau x \ S) x) := by
  apply hfull.of_eventually_abs_le
    (targetZeroPowerAmplitude_eventually_pos beta)
  filter_upwards with x
  exact
    abs_dynamicVisibleClusterPNTMain_sdiff_le_fullOutsideAbsoluteMass
      H S (movingRightEdgeExceptionalCluster H tau x) x

/-- A genuine outside-seed real-part gap automatically discharges the moving
extension budget and transfers signed seed oscillation to the actual PNT
error at coefficient `c / 4`. -/
theorem
    exists_automaticGoodHeight_positiveOutsideClusterGapMovingSeedSignedNaturalTargetTransfer
    {S : Finset ℂ} {beta theta c : ℝ}
    (hbeta : 2 / 3 < beta)
    (hbetaOne : beta < 1)
    (htheta : theta < (3 * beta - 1) / 2)
    (hc : 0 < c)
    (hseed : IsTargetRealPartNontrivialZeroSeed beta S)
    (hS : IsConjugationInvariantCluster S)
    (hcap : PositiveOutsideClusterRealPartCap S theta)
    (hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) :
    ∃ sigma tau alpha : ℝ,
      1 / 2 < sigma ∧
      sigma < tau ∧
      theta < tau ∧
      tau < beta ∧
      1 - beta < alpha ∧
      0 < alpha ∧
      alpha ≤ 1 ∧
      ∀ (selection : UniformNaturalPointGoodHeightSelection),
        HasFarNaturalPointPositiveTargetAmplitudeWitness
            (fun m : ℕ =>
              dynamicVisibleClusterPNTMain
                (selectedUniformGoodHeight alpha selection) S (m : ℝ))
            (fun m : ℕ =>
              c * targetZeroPowerAmplitude beta (m : ℝ)) →
        HasFarNaturalPointNegativeTargetAmplitudeWitness
            (fun m : ℕ =>
              dynamicVisibleClusterPNTMain
                (selectedUniformGoodHeight alpha selection) S (m : ℝ))
            (fun m : ℕ =>
              c * targetZeroPowerAmplitude beta (m : ℝ)) →
        (∃ rate : ℝ,
            0 < rate ∧
            rate ≤ 1 ∧
            Tendsto
              (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
              atTop (nhds 0)) ∧
          HasFarSignedTargetAmplitudeWitnesses
            relativeChebyshevPsi0Error
            (fun x =>
              (c / 4) * targetZeroPowerAmplitude beta x) := by
  rcases
      exists_jointTwoHeightTargetAmplitudeParameters_above_cap
        hbeta hbetaOne htheta with
    ⟨sigma, tau, alpha, gammaLow, gammaHigh,
      epsilonLow, epsilonHigh,
      hsigmaHalf, hsigmaTau, hthetaTau, htauBeta, hsigmaOne,
      hcontour, halpha, halphaOne, _hgammaLowEq,
      hgammaLow, _hgammaLowAlpha, _hgammaHighEq,
      hgammaHigh, hgammaHighAlpha,
      hepsilonLow, hepsilonHigh,
      hlowLow, hlowHigh, hstripLow, hstripHigh⟩
  refine
    ⟨sigma, tau, alpha,
      hsigmaHalf, hsigmaTau, hthetaTau, htauBeta,
      hcontour, halpha, halphaOne, ?_⟩
  intro selection hseedPos hseedNeg
  let H := selectedUniformGoodHeight alpha selection
  have hheight :=
    eventually_selectedUniformGoodHeight_nonneg_le_polynomial
      halpha selection
  have hHnonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ H x :=
    hheight.mono fun _ hx => hx.1
  have hHle :
      ∀ᶠ x : ℝ in atTop,
        H x ≤ carlsonPolynomialHeight alpha x :=
    hheight.mono fun _ hx => hx.2
  have hselectedCap :
      ∀ x rho,
        rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) S →
          sigma < rho.re → rho.re ≤ tau := by
    intro x rho hrho _hright
    rcases mem_positiveNontrivialZerosOutsideClusterFinset.mp hrho with
      ⟨hzero, him, _hheight, hout⟩
    exact (hcap rho hzero him hout).trans hthetaTau.le
  have hfull :=
    selectedFullOutsideClusterPNTAbsoluteMass_targetAmplitudeNegligible
      hS hsigmaHalf hsigmaOne halpha
      hgammaLow hepsilonLow hlowLow hlowHigh
      hgammaHigh hgammaHighAlpha.le hepsilonHigh
      hstripLow hstripHigh hHnonneg hHle hselectedCap hreal
  have hextension :=
    selectedMovingRightEdgeExtension_targetAmplitudeNegligible
      (tau := tau) hfull
  have hloss : 0 < c / 2 := by linarith
  have hnew :=
    eventually_abs_lt_mul_of_naturalPointTargetAmplitudeNegligible
      (eventually_naturalPoint_pos_of_eventually_pos
        (targetZeroPowerAmplitude_eventually_pos beta))
      hextension.naturalPoint hloss
  have hbetaPos : 0 < beta := by linarith
  have hnet : 0 < c - c / 2 := by linarith
  have hresult :=
    unified_automaticGoodHeight_twoHeight_movingRightEdgeSignedSeedNaturalTargetTransfer
      (S₀ := S) (c := c) (loss := c / 2)
      hbetaPos halphaOne hcontour selection
      hsigmaHalf hsigmaOne htauBeta halpha
      hgammaLow hepsilonLow hlowLow hlowHigh
      hgammaHigh hgammaHighAlpha.le
      hepsilonHigh hstripLow hstripHigh
      hnet hseed
      (by simpa [H] using hseedPos)
      (by simpa [H] using hseedNeg)
      (by simpa [H] using hnew)
  refine ⟨hresult.1, ?_⟩
  convert hresult.2 using 1 <;> funext x <;> ring

end PrimeNumberTheorem
