import PrimeNumberTheorem.ZeroDensityLayerBudgetActualMovingExtensionAbsoluteMass
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonFiniteHighSum

/-!
# Pointwise-gap Carlson control of moving-extension absolute mass

The high strip is dominated by the summable dyadic reciprocal Carlson tail.
Only pointwise strict real-part separation outside the finite cluster is used;
no uniform outside gap is assumed.
-/

namespace PrimeNumberTheorem

open scoped BigOperators Topology
open Filter Complex

noncomputable section

/-- The complete finite positive absolute mass is bounded by its canonical low
layer plus the infinite outside-cluster Carlson kernel tail. -/
theorem truncatedPositiveZeroAbsoluteMass_div_target_le_low_add_CarlsonTail
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
          actualCarlsonPositiveZeroRealPart index < beta)
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
    finite_actualHighPositiveZeroKernelSum_le_CarlsonTail
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

/-- At natural points, the selected positive outside absolute mass is
target-negligible under pointwise strict separation in the high Carlson
strip. -/
theorem
    selectedPositiveOutsideClusterPNTAbsoluteMass_naturalPointNegligible_of_CarlsonPointwiseGap
    {H : ℝ → ℝ} {S : Finset ℂ}
    {beta sigma alpha gammaLow epsilonLow : ℝ}
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
          actualCarlsonPositiveZeroRealPart index < beta) :
    NaturalPointTargetAmplitudeNegligible
      (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
      (fun m : ℕ =>
        dynamicPositiveOutsideClusterPNTAbsoluteMass H S (m : ℝ)) := by
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
    actualCarlsonOutsideClusterNormalizedKernelTail_tendsto_zero
      S hsigma hsigmaOne hreHigh
  have hmajor := hlow.add htail
  unfold NaturalPointTargetAmplitudeNegligible
  refine squeeze_zero' ?_ ?_ (by simpa using hmajor)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hamp : 0 < targetZeroPowerAmplitude beta (m : ℝ) :=
      Real.rpow_pos_of_pos (by exact_mod_cast (Nat.zero_lt_of_lt hm)) _
    exact div_nonneg (abs_nonneg _) hamp.le
  · have hHleNat := tendsto_natCast_atTop_atTop.eventually hHle
    filter_upwards
        [eventually_ge_atTop (1 : ℕ), hHleNat] with m hm hHm
    have hamp : 0 < targetZeroPowerAmplitude beta (m : ℝ) :=
      Real.rpow_pos_of_pos (by exact_mod_cast (Nat.zero_lt_of_lt hm)) _
    let selectedInput :=
      pntHybridCanonicalTwoStripOutsideClusterBucketInput
        sigma (H (m : ℝ)) S
    have hsplit :=
      truncatedPositiveZeroAbsoluteMass_div_target_le_low_add_CarlsonTail
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
    rw [abs_of_nonneg]
    · simpa [dynamicPositiveOutsideClusterPNTAbsoluteMass,
        selectedInput, polynomialInput] using hbound
    · exact Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- Conjugation and the real-ordinate slice upgrade pointwise-gap positive
decay to full outside absolute-mass decay at natural points. -/
theorem
    selectedFullOutsideClusterPNTAbsoluteMass_naturalPointNegligible_of_CarlsonPointwiseGap
    {H : ℝ → ℝ} {S : Finset ℂ}
    {beta sigma alpha gammaLow epsilonLow : ℝ}
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
          actualCarlsonPositiveZeroRealPart index < beta)
    (hreReal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) :
    NaturalPointTargetAmplitudeNegligible
      (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
      (fun m : ℕ =>
        dynamicFullOutsideClusterPNTAbsoluteMass H S (m : ℝ)) := by
  have hpositive :=
    selectedPositiveOutsideClusterPNTAbsoluteMass_naturalPointNegligible_of_CarlsonPointwiseGap
      hsigma hsigmaOne halpha hgammaLow hepsilonLow
      hlowLow hlowHigh hHle hreHigh
  have hreal :=
    (dynamicRealOrdinateOutsideClusterPNTAbsoluteMass_targetAmplitudeNegligible
      H S beta hHnonneg hreReal).naturalPoint
  have hamplitude :=
    eventually_naturalPoint_pos_of_eventually_pos
      (targetZeroPowerAmplitude_eventually_pos beta)
  have hmajor :=
    (hpositive.add hamplitude hpositive).add hamplitude hreal
  apply hmajor.of_eventually_abs_le hamplitude
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
  have hmx : 0 < (m : ℝ) := by exact_mod_cast hm
  rw [dynamicFullOutsideClusterPNTAbsoluteMass_eq_two_positive_add_real
    hS hmx]
  rw [abs_of_nonneg]
  exact add_nonneg
    (add_nonneg
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Finset.sum_nonneg fun _ _ => norm_nonneg _))
    (Finset.sum_nonneg fun _ _ => norm_nonneg _)

/-- Every moving finite extension is negligible once the full outside
absolute mass has pointwise-gap Carlson decay. -/
theorem
    selectedMovingRightEdgeExtension_naturalPointNegligible_of_CarlsonPointwiseGap
    {H : ℝ → ℝ} {S : Finset ℂ} {beta transferTau : ℝ}
    (hfull :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
        (fun m : ℕ =>
          dynamicFullOutsideClusterPNTAbsoluteMass H S (m : ℝ))) :
    NaturalPointTargetAmplitudeNegligible
      (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
      (fun m : ℕ =>
        dynamicVisibleClusterPNTMain H
          (movingRightEdgeExceptionalCluster H transferTau (m : ℝ) \ S)
          (m : ℝ)) := by
  apply hfull.of_eventually_abs_le
    (eventually_naturalPoint_pos_of_eventually_pos
      (targetZeroPowerAmplitude_eventually_pos beta))
  filter_upwards with m
  exact
    abs_dynamicVisibleClusterPNTMain_sdiff_le_fullOutsideAbsoluteMass
      H S (movingRightEdgeExceptionalCluster H transferTau (m : ℝ)) (m : ℝ)

/-- Pointwise strict separation of every residual Carlson-indexed zero
automatically discharges the moving-extension loss and transfers signed seed
witnesses to the actual PNT error at coefficient `c / 4`. -/
theorem
    exists_automaticGoodHeight_CarlsonPointwiseGapMovingSeedSignedNaturalTargetTransfer
    {S : Finset ℂ} {beta c : ℝ}
    (hbeta : 2 / 3 < beta)
    (hbetaOne : beta < 1)
    (hc : 0 < c)
    (hseed : IsTargetRealPartNontrivialZeroSeed beta S)
    (hS : IsConjugationInvariantCluster S) :
    ∃ sigma transferTau alpha : ℝ,
      1 / 2 < sigma ∧
      sigma < transferTau ∧
      1 / 2 < transferTau ∧
      transferTau < beta ∧
      1 - beta < alpha ∧
      0 < alpha ∧
      alpha ≤ 1 ∧
      ∀ (selection : UniformNaturalPointGoodHeightSelection),
        (∀ index : ActualCarlsonPositiveZeroIndex sigma,
          actualCarlsonPositiveZero index ∉ S →
            actualCarlsonPositiveZeroRealPart index < beta) →
        (∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
          rho.re < beta) →
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
            (fun x => (c / 4) * targetZeroPowerAmplitude beta x) := by
  have hhalf : (1 / 2 : ℝ) < (3 * beta - 1) / 2 := by linarith
  rcases
      exists_jointTwoHeightTargetAmplitudeParameters_above_cap
        (theta := (1 / 2 : ℝ)) hbeta hbetaOne hhalf with
    ⟨sigma, transferTau, alpha, gammaLow, gammaHigh,
      epsilonLow, epsilonHigh,
      hsigmaHalf, hsigmaTau, hhalfTau, htauBeta, hsigmaOne,
      hcontour, halpha, halphaOne, _hgammaLowEq,
      hgammaLow, _hgammaLowAlpha, _hgammaHighEq,
      hgammaHigh, hgammaHighAlpha,
      hepsilonLow, hepsilonHigh,
      hlowLow, hlowHigh, hstripLow, hstripHigh⟩
  refine
    ⟨sigma, transferTau, alpha,
      hsigmaHalf, hsigmaTau, hhalfTau, htauBeta,
      hcontour, halpha, halphaOne, ?_⟩
  intro selection hreHigh hreReal hseedPos hseedNeg
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
  have hfull :=
    selectedFullOutsideClusterPNTAbsoluteMass_naturalPointNegligible_of_CarlsonPointwiseGap
      hS hsigmaHalf hsigmaOne halpha hgammaLow hepsilonLow
      hlowLow hlowHigh hHnonneg hHle hreHigh hreReal
  have hextension :=
    selectedMovingRightEdgeExtension_naturalPointNegligible_of_CarlsonPointwiseGap
      (transferTau := transferTau) hfull
  have hloss : 0 < c / 2 := by linarith
  have hnew :=
    eventually_abs_lt_mul_of_naturalPointTargetAmplitudeNegligible
      (eventually_naturalPoint_pos_of_eventually_pos
        (targetZeroPowerAmplitude_eventually_pos beta))
      hextension hloss
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

end

end PrimeNumberTheorem
