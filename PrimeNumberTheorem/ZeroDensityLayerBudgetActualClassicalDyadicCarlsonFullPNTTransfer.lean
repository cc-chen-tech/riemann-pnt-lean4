import PrimeNumberTheorem.ZeroDensityLayerBudgetActualClassicalDyadicCarlsonMiddleMass
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightNaturalRemainderDecay
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightMovingCarlsonPNTTransfer

open Filter Real Complex
open scoped Topology BigOperators

namespace PrimeNumberTheorem


end PrimeNumberTheorem

namespace PrimeNumberTheorem

lemma eventually_pintzCarlsonHeight_add_one_le_real_rpow
    {k alpha : ℝ} (hk : 0 ≤ k) (halpha : 0 < alpha) :
    ∀ᶠ x : ℝ in atTop,
      pintzCarlsonHeight k x + 1 ≤ x ^ alpha := by
  have hs : Tendsto pintzCarlsonSqrtLogScale atTop atTop :=
    tendsto_pintzCarlsonSqrtLogScale_atTop
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    hs.eventually_ge_atTop (max 1 ((k + 1) / alpha))] with x hx hsqrt
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hs_nonneg : 0 ≤ pintzCarlsonSqrtLogScale x := Real.sqrt_nonneg _
  have hs_one : 1 ≤ pintzCarlsonSqrtLogScale x :=
    le_trans (le_max_left _ _) hsqrt
  have hs_ratio : (k + 1) / alpha ≤ pintzCarlsonSqrtLogScale x :=
    le_trans (le_max_right _ _) hsqrt
  have hmul : k + 1 ≤ alpha * pintzCarlsonSqrtLogScale x := by
    have := (div_le_iff₀ halpha).mp hs_ratio
    nlinarith
  have hlogtwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hexp_one : 1 ≤ Real.exp (k * pintzCarlsonSqrtLogScale x) := by
    rw [one_le_exp_iff]
    positivity
  have hexp_sum : Real.exp (k * pintzCarlsonSqrtLogScale x) + 1 ≤
      2 * Real.exp (k * pintzCarlsonSqrtLogScale x) := by
    linarith
  have hscale : Real.log 2 + k * pintzCarlsonSqrtLogScale x ≤
      alpha * (pintzCarlsonSqrtLogScale x) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hmul hs_nonneg
    nlinarith
  calc
    pintzCarlsonHeight k x + 1 =
        Real.exp (k * pintzCarlsonSqrtLogScale x) + 1 := rfl
    _ ≤ 2 * Real.exp (k * pintzCarlsonSqrtLogScale x) := hexp_sum
    _ = Real.exp (Real.log 2 + k * pintzCarlsonSqrtLogScale x) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ Real.exp (alpha * (pintzCarlsonSqrtLogScale x) ^ 2) :=
      Real.exp_le_exp.mpr hscale
    _ = x ^ alpha := by
      rw [show (pintzCarlsonSqrtLogScale x) ^ 2 = Real.log x by
        simpa [pintzCarlsonSqrtLogScale] using Real.sq_sqrt hlog]
      rw [mul_comm]
      exact (Real.rpow_def_of_pos hxpos alpha).symm

lemma tendsto_selectedClassicalAdmissibleGoodHeight_atTop
    {b : ℝ} (hb : 0 < b)
    (selection : UniformNaturalPointGoodHeightSelection) :
    Tendsto (selectedClassicalAdmissibleGoodHeight b selection) atTop atTop := by
  have hk := classicalAdmissibleBalancedRate_pos hb
  have hbase := tendsto_pintzCarlsonHeight_atTop hk
  refine tendsto_atTop.2 ?_
  intro A
  filter_upwards [eventually_selectedClassicalAdmissibleGoodHeight_mem hb selection,
    hbase.eventually (eventually_ge_atTop (A + 1))] with x hx hlarge
  dsimp [pintzCarlsonGoodHeightBase] at hx
  linarith [hx.1]

lemma eventually_selectedClassicalAdmissibleGoodHeight_le_polynomialHeight_real
    {b alpha : ℝ} (hb : 0 < b) (halpha : 0 < alpha)
    (selection : UniformNaturalPointGoodHeightSelection) :
    ∀ᶠ x : ℝ in atTop,
      selectedClassicalAdmissibleGoodHeight b selection x ≤
        carlsonPolynomialHeight alpha x := by
  have hk := (classicalAdmissibleBalancedRate_pos hb).le
  filter_upwards [eventually_selectedClassicalAdmissibleGoodHeight_mem hb selection,
    eventually_pintzCarlsonHeight_add_one_le_real_rpow hk halpha] with x hx hheight
  dsimp [pintzCarlsonGoodHeightBase] at hx
  unfold carlsonPolynomialHeight
  linarith [hx.2]

end PrimeNumberTheorem

namespace PrimeNumberTheorem

lemma tendsto_actualSelectedClassicalAdmissibleCriticalHalfPNTLayerNorm_zero
    {b alpha epsilon : ℝ}
    (hb : 0 < b) (halpha : 0 < alpha) (hepsilon : 0 < epsilon)
    (hmargin : alpha + epsilon < 1 / 2)
    (selection : UniformNaturalPointGoodHeightSelection) :
    Tendsto
      (fun m : ℕ =>
        dynamicPositiveOutsideClusterPNTLayerNorm
          (selectedClassicalAdmissibleGoodHeight b selection) ∅
          (actualSelectedHeightCriticalHalfCanonicalInput
            (selectedClassicalAdmissibleGoodHeight b selection))
          (0 : Fin 2) (m : ℝ))
      atTop (𝓝 0) := by
  let H := selectedClassicalAdmissibleGoodHeight b selection
  rcases exists_canonicalTwoStripOutsideCluster_uniform_norm_lower_bound
      H (1 / 2) ∅ with ⟨kappa, hkappa, hnorm⟩
  have hreal :=
    tendsto_dynamicPositiveOutsideClusterPNTLayerNorm_div_targetAmplitude_zero_of_hybrid_selectedHeight
      (input := actualSelectedHeightCriticalHalfCanonicalInput H)
      (i := (0 : Fin 2)) (beta := 1) (tau := (1 / 2 : ℝ))
      (alpha := alpha) (kappa := kappa) (epsilon := epsilon)
      (eventually_selectedClassicalAdmissibleGoodHeight_le_polynomialHeight_real
        hb halpha selection)
      (tendsto_selectedClassicalAdmissibleGoodHeight_atTop hb selection)
      hkappa
      (by
        intro x rho hrho
        exact hnorm x rho hrho)
      (by
        intro x rho hrho
        exact actualSelectedHeightCriticalHalfCanonicalInput_low_re_le hrho)
      halpha hepsilon (by linarith)
  have hreal' :
      Tendsto
        (fun x : ℝ =>
          dynamicPositiveOutsideClusterPNTLayerNorm H ∅
            (actualSelectedHeightCriticalHalfCanonicalInput H)
            (0 : Fin 2) x)
        atTop (𝓝 0) := by
    convert hreal using 1
    funext x
    simp [targetZeroPowerAmplitude,
      dynamicPositiveOutsideClusterPNTLayerNorm]
  exact hreal'.comp tendsto_natCast_atTop_atTop

lemma tendsto_dynamicRealOrdinatePNTZeroTailNorm_of_height_tendsto
    {H : ℝ → ℝ} (hHtop : Tendsto H atTop atTop) :
    Tendsto (fun m : ℕ => dynamicRealOrdinatePNTZeroTailNorm H (m : ℝ))
      atTop (𝓝 0) := by
  have hheight : ∀ᶠ x : ℝ in atTop, 0 ≤ H x :=
    hHtop.eventually (eventually_ge_atTop (0 : ℝ))
  have hre :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 ∅,
        rho.re < 1 := by
    intro rho hrho
    have hreal : rho ∈ realOrdinateNontrivialZerosFinset 0 := by
      simpa [realOrdinateNontrivialZerosOutsideClusterFinset] using hrho
    have hzero : RiemannHypothesis.IsNontrivialZero rho :=
      (mem_nontrivialZerosFinset.mp
        (mem_realOrdinateNontrivialZerosFinset.mp hreal).1).1
    exact hzero.2.2
  have hnegligible :=
    dynamicRealOrdinateOutsideClusterPNTZeroTailNorm_targetAmplitudeNegligible
      H ∅ 1 hheight hre
  have heq :
      dynamicRealOrdinateOutsideClusterPNTZeroTailNorm H ∅ =
        dynamicRealOrdinatePNTZeroTailNorm H := by
    funext x
    simp [dynamicRealOrdinateOutsideClusterPNTZeroTailNorm,
      realOrdinateNontrivialZerosOutsideClusterFinset,
      dynamicRealOrdinatePNTZeroTailNorm]
  rw [heq] at hnegligible
  unfold TargetAmplitudeNegligible at hnegligible
  have hrealTendsto :
      Tendsto (dynamicRealOrdinatePNTZeroTailNorm H) atTop (𝓝 0) := by
    have habs : Tendsto
        (fun x : ℝ => |dynamicRealOrdinatePNTZeroTailNorm H x|)
        atTop (𝓝 0) := by
      simpa [targetZeroPowerAmplitude] using hnegligible
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Real.norm_eq_abs] using habs
  exact hrealTendsto.comp tendsto_natCast_atTop_atTop

lemma tendsto_selectedClassicalAdmissibleRealOrdinatePNTZeroTailNorm_zero
    {b : ℝ} (hb : 0 < b)
    (selection : UniformNaturalPointGoodHeightSelection) :
    Tendsto
      (fun m : ℕ => dynamicRealOrdinatePNTZeroTailNorm
        (selectedClassicalAdmissibleGoodHeight b selection) (m : ℝ))
      atTop (𝓝 0) :=
  tendsto_dynamicRealOrdinatePNTZeroTailNorm_of_height_tendsto
    (tendsto_selectedClassicalAdmissibleGoodHeight_atTop hb selection)

end PrimeNumberTheorem

namespace PrimeNumberTheorem

lemma actualSelectedHeightMovingCarlsonStripMass_le_dyadicFixedAnchor
    {H : ℝ → ℝ} {alpha : ℝ} {delta : ℕ → ℝ} {m : ℕ}
    (hheight : H (m : ℝ) ≤ carlsonPolynomialHeight alpha (m : ℝ))
    (hdelta_pos : 0 < delta m) (hdelta_le : delta m ≤ 1 / 16) :
    actualSelectedHeightMovingCarlsonStripMass H delta m ≤
      actualDyadicCarlsonFixedAnchorMass alpha delta
        (dyadicCarlsonLayerSchedule delta) m := by
  unfold actualSelectedHeightMovingCarlsonStripMass
    actualDyadicCarlsonFixedAnchorMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro rho hrho
    have hr := mem_actualPositiveCarlsonStrip.mp hrho
    apply mem_actualDyadicCarlsonMinimalFixedAnchorWindow
    · exact hr.1
    · exact hr.2.1
    · exact hr.2.2.1.trans hheight
    · exact hdelta_pos
    · linarith [hr.2.2.2.1]
    · exact hr.2.2.2.2
  · intro rho _ _
    positivity

lemma tendsto_actualSelectedClassicalAdmissibleMovingStripMass_zero_of_dyadic
    {b alpha : ℝ} {delta : ℕ → ℝ}
    (hb : 0 < b) (halpha : 0 < alpha) (halpha_lt : alpha < 1 / 16)
    (selection : UniformNaturalPointGoodHeightSelection)
    (hdelta_nonneg : ∀ m, 0 ≤ delta m)
    (hdelta_pos : ∀ᶠ m : ℕ in atTop, 0 < delta m)
    (hdelta_le_eighth : ∀ᶠ m : ℕ in atTop, delta m ≤ 1 / 8)
    (hdelta_le_sixteenth : ∀ᶠ m : ℕ in atTop, delta m ≤ 1 / 16)
    (hgap : IsCarlsonMovingDyadicLogPowerGap delta) :
    Tendsto
      (actualSelectedHeightMovingCarlsonStripMass
        (selectedClassicalAdmissibleGoodHeight b selection) delta)
      atTop (𝓝 0) := by
  have hheightReal :=
    eventually_selectedClassicalAdmissibleGoodHeight_le_polynomialHeight_real
      hb halpha selection
  have hheight := tendsto_natCast_atTop_atTop.eventually hheightReal
  obtain ⟨A, C₁, C₂, hA, hC₁, hC₂, hfixed⟩ :=
    exists_constants_tendsto_actualDyadicCarlsonMinimalFixedAnchorMass_zero_automatic
      halpha halpha_lt.le hdelta_nonneg hdelta_pos hdelta_le_eighth hgap
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun m => by
      unfold actualSelectedHeightMovingCarlsonStripMass
      positivity
  · filter_upwards [hheight, hdelta_pos, hdelta_le_sixteenth] with m hH hpos hle
    exact actualSelectedHeightMovingCarlsonStripMass_le_dyadicFixedAnchor
      hH hpos hle
  · exact hfixed

lemma eventually_classicalAdmissibleDyadicCarlsonGapWidth_le
    {rate epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ m : ℕ in atTop,
      classicalAdmissibleDyadicCarlsonGapWidth rate m ≤ epsilon := by
  filter_upwards [tendsto_pntSqrtLog_atTop.eventually_ge_atTop (rate / epsilon)] with m hm
  have hden : 0 < 1 + pntSqrtLog m := by
    have hsqrt : 0 ≤ pntSqrtLog m := Real.sqrt_nonneg _
    linarith
  unfold classicalAdmissibleDyadicCarlsonGapWidth
  apply (div_le_iff₀ hden).2
  have hmul := (div_le_iff₀ hepsilon).mp hm
  nlinarith

lemma eventually_classicalAdmissibleDyadicCarlsonGapWidth_le_sixteenth
    {rate : ℝ} :
    ∀ᶠ m : ℕ in atTop,
      classicalAdmissibleDyadicCarlsonGapWidth rate m ≤ 1 / 16 :=
  eventually_classicalAdmissibleDyadicCarlsonGapWidth_le
    (by norm_num : (0 : ℝ) < 1 / 16)

end PrimeNumberTheorem

namespace PrimeNumberTheorem

lemma tendsto_dynamicPositivePNTTailNorm_of_selectedClassicalAdmissibleDyadicCarlson
    {b alpha epsilon : ℝ} {delta : ℕ → ℝ}
    (hb : 0 < b) (halpha : 0 < alpha) (halpha_lt : alpha < 1 / 16)
    (hepsilon : 0 < epsilon) (hmargin : alpha + epsilon < 1 / 2)
    (selection : UniformNaturalPointGoodHeightSelection)
    (hdelta_nonneg : ∀ m, 0 ≤ delta m)
    (hdelta_pos : ∀ᶠ m : ℕ in atTop, 0 < delta m)
    (hdelta_le_eighth : ∀ᶠ m : ℕ in atTop, delta m ≤ 1 / 8)
    (hdelta_le_sixteenth : ∀ᶠ m : ℕ in atTop, delta m ≤ 1 / 16)
    (hgap : IsCarlsonMovingDyadicLogPowerGap delta)
    (hzeroFree : IsSelectedHeightDynamicZeroFree
      (selectedClassicalAdmissibleGoodHeight b selection) delta) :
    Tendsto
      (fun m : ℕ => dynamicPositivePNTTailNorm
        (selectedClassicalAdmissibleGoodHeight b selection) (m : ℝ))
      atTop (𝓝 0) := by
  let H := selectedClassicalAdmissibleGoodHeight b selection
  have hcap :=
    eventually_actualSelectedHeightMovingPositiveRightEdgeCap_of_dynamicZeroFree
      hzeroFree
  have hcritical :=
    tendsto_actualSelectedClassicalAdmissibleCriticalHalfPNTLayerNorm_zero
      hb halpha hepsilon hmargin selection
  have hmiddle :=
    tendsto_actualSelectedClassicalAdmissibleMovingMiddleMass_zero_of_dyadic
      hb halpha halpha_lt
      selection hdelta_nonneg hdelta_pos hdelta_le_eighth hgap
  have hstrip :=
    tendsto_actualSelectedClassicalAdmissibleMovingStripMass_zero_of_dyadic
      hb halpha halpha_lt selection hdelta_nonneg hdelta_pos
      hdelta_le_eighth hdelta_le_sixteenth hgap
  have hmajorant :
      Tendsto
        (fun m : ℕ =>
          dynamicPositiveOutsideClusterPNTLayerNorm H ∅
              (actualSelectedHeightCriticalHalfCanonicalInput H)
              (0 : Fin 2) (m : ℝ) +
            actualSelectedHeightMovingCarlsonMiddleMass H delta m +
            actualSelectedHeightMovingCarlsonStripMass H delta m)
        atTop (𝓝 0) := by
    simpa [H] using (hcritical.add hmiddle).add hstrip
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun m => norm_nonneg _
  · filter_upwards [hcap] with m hm
    exact dynamicPositivePNTTailNorm_le_selectedCriticalHalf_add_movingMasses hm
  · exact hmajorant

lemma tendsto_dynamicFullPNTZeroTailNorm_of_selectedClassicalAdmissibleDyadicCarlson
    {b alpha epsilon : ℝ} {delta : ℕ → ℝ}
    (hb : 0 < b) (halpha : 0 < alpha) (halpha_lt : alpha < 1 / 16)
    (hepsilon : 0 < epsilon) (hmargin : alpha + epsilon < 1 / 2)
    (selection : UniformNaturalPointGoodHeightSelection)
    (hdelta_nonneg : ∀ m, 0 ≤ delta m)
    (hdelta_pos : ∀ᶠ m : ℕ in atTop, 0 < delta m)
    (hdelta_le_eighth : ∀ᶠ m : ℕ in atTop, delta m ≤ 1 / 8)
    (hdelta_le_sixteenth : ∀ᶠ m : ℕ in atTop, delta m ≤ 1 / 16)
    (hgap : IsCarlsonMovingDyadicLogPowerGap delta)
    (hzeroFree : IsSelectedHeightDynamicZeroFree
      (selectedClassicalAdmissibleGoodHeight b selection) delta) :
    Tendsto
      (fun m : ℕ => dynamicFullPNTZeroTailNorm
        (selectedClassicalAdmissibleGoodHeight b selection) (m : ℝ))
      atTop (𝓝 0) := by
  let H := selectedClassicalAdmissibleGoodHeight b selection
  have hpositive :=
    tendsto_dynamicPositivePNTTailNorm_of_selectedClassicalAdmissibleDyadicCarlson
      hb halpha halpha_lt hepsilon hmargin selection hdelta_nonneg
      hdelta_pos hdelta_le_eighth hdelta_le_sixteenth hgap hzeroFree
  have hreal :=
    tendsto_selectedClassicalAdmissibleRealOrdinatePNTZeroTailNorm_zero
      hb selection
  have hmajorant :
      Tendsto
        (fun m : ℕ =>
          dynamicPositivePNTTailNorm H (m : ℝ) +
            dynamicPositivePNTTailNorm H (m : ℝ) +
            dynamicRealOrdinatePNTZeroTailNorm H (m : ℝ))
        atTop (𝓝 0) := by
    simpa [H] using (hpositive.add hpositive).add hreal
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun m => norm_nonneg _
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
    exact dynamicFullPNTZeroTailNorm_le_two_positive_add_real hmpos
  · exact hmajorant

end PrimeNumberTheorem

namespace PrimeNumberTheorem

noncomputable def selectedClassicalAdmissibleNaturalRemainderUpperBound
    (b : ℝ) (selection : UniformNaturalPointGoodHeightSelection)
    (m : ℕ) : ℝ :=
  (cofinalPNTFormulaRemainderBound selection.constant
      (pintzCarlsonGoodHeightBase (classicalAdmissibleBalancedRate b) (m : ℝ))
      (selectedClassicalAdmissibleGoodHeight b selection (m : ℝ)) m 0 +
    ‖(1 / 2 : ℂ) *
      (Real.log (1 - (m : ℝ) ^ (-2 : ℝ)) : ℂ)‖) / (m : ℝ)

lemma eventually_abs_selectedClassicalAdmissibleGoodHeight_actualRemainder_le
    {b : ℝ} (hb : 0 < b)
    (selection : UniformNaturalPointGoodHeightSelection) :
    ∀ᶠ m : ℕ in atTop,
      |actualPNTExplicitFormulaRelativeRemainder
        (selectedClassicalAdmissibleGoodHeight b selection) (m : ℝ)| ≤
      selectedClassicalAdmissibleNaturalRemainderUpperBound b selection m := by
  have hrate := classicalAdmissibleBalancedRate_pos hb
  filter_upwards [
    eventually_pintzCarlsonGoodHeightBase_ge_eight hrate,
    eventually_ge_atTop (3 : ℕ)] with m hbase hm
  rcases selectedClassicalAdmissibleGoodHeight_truncatedCertificate
      selection m 0 hm hbase with ⟨certificate, htrivial, hremainder⟩
  have hmpos : 0 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) hm)
  have hbound :=
    certificate.abs_actualPNTExplicitFormulaRelativeRemainder_le
      (htrivial.trans (cofinalTrivialZeroContribution_zero m)) hmpos
  unfold actualPNTExplicitFormulaRelativeRemainder
  rw [hremainder] at hbound
  simpa [selectedClassicalAdmissibleNaturalRemainderUpperBound] using hbound

lemma tendsto_selectedClassicalAdmissibleNaturalRemainderUpperBound_zero
    {b : ℝ} (hb : 0 < b)
    (selection : UniformNaturalPointGoodHeightSelection) :
    Tendsto
      (selectedClassicalAdmissibleNaturalRemainderUpperBound b selection)
      atTop (𝓝 0) := by
  have hcontour :=
    selectedClassicalAdmissibleGoodHeight_contourRelative_tendsto hb selection
  have hclosedNegligible :=
    selectedNaturalClosedLogRelative_targetNegligible
      (show (0 : ℝ) < 1 by norm_num)
  unfold NaturalPointTargetAmplitudeNegligible at hclosedNegligible
  have hclosedAbs :
      Tendsto
        (fun m : ℕ =>
          |‖(1 / 2 : ℂ) *
            (Real.log (1 - (m : ℝ) ^ (-2 : ℝ)) : ℂ)‖ / (m : ℝ)|)
        atTop (𝓝 0) := by
    simpa only [targetZeroPowerAmplitude, sub_self, Real.rpow_zero, div_one] using
      hclosedNegligible
  have hclosed :
      Tendsto
        (fun m : ℕ =>
          ‖(1 / 2 : ℂ) *
            (Real.log (1 - (m : ℝ) ^ (-2 : ℝ)) : ℂ)‖ / (m : ℝ))
        atTop (𝓝 0) := by
    apply hclosedAbs.congr'
    filter_upwards with m
    have hnonneg : 0 ≤
        ‖(1 / 2 : ℂ) *
          (Real.log (1 - (m : ℝ) ^ (-2 : ℝ)) : ℂ)‖ / (m : ℝ) := by
      positivity
    rw [abs_of_nonneg hnonneg]
  have hsum := hcontour.add hclosed
  change Tendsto
    (fun m : ℕ =>
      (cofinalPNTFormulaRemainderBound selection.constant
          (pintzCarlsonGoodHeightBase (classicalAdmissibleBalancedRate b) (m : ℝ))
          (selectedClassicalAdmissibleGoodHeight b selection (m : ℝ)) m 0 +
        ‖(1 / 2 : ℂ) *
          (Real.log (1 - (m : ℝ) ^ (-2 : ℝ)) : ℂ)‖) / (m : ℝ))
    atTop (𝓝 0)
  simpa only [add_div, zero_add] using hsum

lemma selectedClassicalAdmissibleGoodHeight_actualNaturalRemainderCertificate
    {b : ℝ} (hb : 0 < b)
    (selection : UniformNaturalPointGoodHeightSelection) :
    ActualSelectedHeightNaturalPointRemainderCertificate 1
      (selectedClassicalAdmissibleGoodHeight b selection) where
  negligible := by
    unfold NaturalPointTargetAmplitudeNegligible
    have habs :
        Tendsto
          (fun m : ℕ =>
            |actualPNTExplicitFormulaRelativeRemainder
              (selectedClassicalAdmissibleGoodHeight b selection) (m : ℝ)|)
          atTop (𝓝 0) := by
      apply squeeze_zero'
      · exact Filter.Eventually.of_forall fun m => abs_nonneg _
      · exact eventually_abs_selectedClassicalAdmissibleGoodHeight_actualRemainder_le
          hb selection
      · exact tendsto_selectedClassicalAdmissibleNaturalRemainderUpperBound_zero
          hb selection
    simpa [targetZeroPowerAmplitude] using habs

end PrimeNumberTheorem

namespace PrimeNumberTheorem

/-- Canonical Carlson-density and classical explicit-formula transfer on one
subpolynomial selected height. -/
theorem exists_selectedClassicalAdmissibleDyadicCarlsonFullPNTTransfer :
    ∃ b rate : ℝ,
      0 < b ∧ 0 < rate ∧
        IsCarlsonMovingDyadicLogPowerGap
          (classicalAdmissibleDyadicCarlsonGapWidth rate) ∧
        ∀ selection : UniformNaturalPointGoodHeightSelection,
          IsSelectedHeightDynamicZeroFree
              (selectedClassicalAdmissibleGoodHeight b selection)
              (classicalAdmissibleDyadicCarlsonGapWidth rate) ∧
            Tendsto
              (fun m : ℕ => dynamicFullPNTZeroTailNorm
                (selectedClassicalAdmissibleGoodHeight b selection) (m : ℝ))
              atTop (𝓝 0) ∧
            ActualSelectedHeightNaturalPointRemainderCertificate 1
              (selectedClassicalAdmissibleGoodHeight b selection) ∧
            Tendsto (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
              atTop (𝓝 0) := by
  obtain ⟨b, rate, hb, hrate, hgap, hdata⟩ :=
    exists_selectedClassicalAdmissibleDyadicCarlsonMiddleMassDecay
  refine ⟨b, rate, hb, hrate, hgap, ?_⟩
  intro selection
  have hzeroFree := (hdata selection).1
  have hdeltaNonneg : ∀ m, 0 ≤ classicalAdmissibleDyadicCarlsonGapWidth rate m :=
    classicalAdmissibleDyadicCarlsonGapWidth_nonneg hrate
  have hdeltaPos : ∀ᶠ m : ℕ in atTop,
      0 < classicalAdmissibleDyadicCarlsonGapWidth rate m :=
    Filter.Eventually.of_forall fun m =>
      classicalAdmissibleDyadicCarlsonGapWidth_pos hrate m
  have hdeltaEighth : ∀ᶠ m : ℕ in atTop,
      classicalAdmissibleDyadicCarlsonGapWidth rate m ≤ 1 / 8 :=
    eventually_classicalAdmissibleDyadicCarlsonGapWidth_le_eighth hrate
  have hdeltaSixteenth : ∀ᶠ m : ℕ in atTop,
      classicalAdmissibleDyadicCarlsonGapWidth rate m ≤ 1 / 16 :=
    eventually_classicalAdmissibleDyadicCarlsonGapWidth_le_sixteenth
  have hfull :=
    tendsto_dynamicFullPNTZeroTailNorm_of_selectedClassicalAdmissibleDyadicCarlson
      hb (by norm_num : (0 : ℝ) < 1 / 64)
      (by norm_num : (1 / 64 : ℝ) < 1 / 16)
      (by norm_num : (0 : ℝ) < 1 / 64)
      (by norm_num : (1 / 64 : ℝ) + 1 / 64 < 1 / 2)
      selection hdeltaNonneg hdeltaPos hdeltaEighth hdeltaSixteenth
      hgap hzeroFree
  have hremainder :=
    selectedClassicalAdmissibleGoodHeight_actualNaturalRemainderCertificate
      hb selection
  have hpnt :=
    tendsto_relativeChebyshevPsi0Error_of_dynamicFullPNTZeroTailNorm
      hfull hremainder
  exact ⟨hzeroFree, hfull, hremainder, hpnt⟩

end PrimeNumberTheorem
