import MathlibAux.WeightedSecondMomentLevelSet
import PrimeNumberTheorem.VKEdgePiOverTwoOrdinaryL2

open Complex Filter MeasureTheory Set

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# Quantitative measure of strict pi/2 oscillations

This module strengthens the existing positive-measure theorem without assuming
a fourth-moment estimate.  The resulting lower bound is explicit but decays
with the elementary pointwise envelope, so it is deliberately not advertised
as a fixed-proportion theorem.
-/

/-- The limiting weighted energy left after removing the contribution allowed
by a threshold `C`. -/
def centeredThresholdEnergyGap
    (multiplicity mean C : Real) : Real :=
  multiplicity ^ 2 / mean - C ^ 2 * mean

theorem centeredThresholdEnergyGap_pos
    {multiplicity mean C : Real}
    (hmultiplicity : 0 < multiplicity) (hmean : 0 < mean)
    (hC0 : 0 ≤ C) (hC : C < multiplicity / mean) :
    0 < centeredThresholdEnergyGap multiplicity mean C := by
  have hCmean : C * mean < multiplicity :=
    (lt_div_iff₀ hmean).1 hC
  have hsquares : (C * mean) ^ 2 < multiplicity ^ 2 := by
    nlinarith
  unfold centeredThresholdEnergyGap
  apply sub_pos.mpr
  apply (lt_div_iff₀ hmean).2
  nlinarith

/-- The contour lower limit and the kernel-mass limit leave a fixed positive
fraction of the threshold energy gap. -/
theorem
    CenteredLocalizedContourData.eventually_secondMoment_sub_thresholdMass_gt_half_gap
    {q d : Real} {rho : Complex} {multiplicity mean C : Real}
    (data : CenteredLocalizedContourData q d rho multiplicity mean)
    (hmultiplicity : 0 < multiplicity) (hmean : 0 < mean)
    (hC0 : 0 ≤ C) (hC : C < multiplicity / mean) :
    ∀ᶠ m : Real in atTop,
      centeredThresholdEnergyGap multiplicity mean C / 2 <
        centeredNormalizedWindowSecondMoment q d rho data.kernel m -
          C ^ 2 * data.coefficient m := by
  let gap : Real := centeredThresholdEnergyGap multiplicity mean C
  have hgap : 0 < gap := by
    exact centeredThresholdEnergyGap_pos hmultiplicity hmean hC0 hC
  let secondFloor : Real :=
    2 * multiplicity ^ 2 / mean - gap / 4
  have hsecondFloor :
      secondFloor < 2 * multiplicity ^ 2 / mean := by
    dsimp [secondFloor]
    linarith
  have hsecond :=
    data.eventually_secondMoment_gt
      hmultiplicity hmean hsecondFloor
  let coefficientCeiling : Real :=
    2 * mean + gap / (4 * (C ^ 2 + 1))
  have hdenom : 0 < 4 * (C ^ 2 + 1) := by positivity
  have hcoefficientCeiling : 2 * mean < coefficientCeiling := by
    dsimp [coefficientCeiling]
    exact lt_add_of_pos_right _ (div_pos hgap hdenom)
  have hcoefficient :
      ∀ᶠ m : Real in atTop,
        data.coefficient m < coefficientCeiling :=
    (tendsto_order.1 data.coefficient_tendsto).2
      coefficientCeiling hcoefficientCeiling
  have hscaledCeiling :
      C ^ 2 * coefficientCeiling ≤
        2 * C ^ 2 * mean + gap / 4 := by
    have hfraction :
        C ^ 2 * (gap / (4 * (C ^ 2 + 1))) ≤ gap / 4 := by
      rw [show
          C ^ 2 * (gap / (4 * (C ^ 2 + 1))) =
            (C ^ 2 * gap) / (4 * (C ^ 2 + 1)) by ring]
      apply (div_le_iff₀ hdenom).2
      nlinarith [sq_nonneg C]
    dsimp [coefficientCeiling]
    nlinarith
  filter_upwards [hsecond, hcoefficient] with m hsecondM hcoefficientM
  have hscaled :
      C ^ 2 * data.coefficient m ≤
        2 * C ^ 2 * mean + gap / 4 :=
    (mul_le_mul_of_nonneg_left hcoefficientM.le (sq_nonneg C)).trans
      hscaledCeiling
  have hgapIdentity :
      2 * multiplicity ^ 2 / mean =
        2 * C ^ 2 * mean + 2 * gap := by
    dsimp [gap]
    unfold centeredThresholdEnergyGap
    ring
  dsimp [secondFloor] at hsecondM
  rw [hgapIdentity] at hsecondM
  dsimp [gap] at hsecondM hscaled ⊢
  linarith

/-- Elementary pointwise envelope for the normalized PNT error on the
centered logarithmic window. -/
def centeredNormalizedPsiErrorWindowEnvelope
    (q d : Real) (rho : Complex) (m : Real) : Real :=
  norm rho * (Real.log 4 + 5) *
    Real.exp ((1 - rho.re) * ((q + d) * m))

theorem normalizedPsiError_abs_le_centeredWindowEnvelope
    {q d m y : Real} {rho : Complex}
    (hrhoRe1 : rho.re < 1)
    (hy : y ∈ localizedGaussianLogWindow q d m) :
    |normalizedPsiError rho y| ≤
      centeredNormalizedPsiErrorWindowEnvelope q d rho m := by
  have hpsi :
      chebyshevPsi (Real.exp y) ≤
        (Real.log 4 + 4) * Real.exp y := by
    rw [chebyshevPsi_eq_mathlib]
    exact Chebyshev.psi_le_const_mul_self (Real.exp_pos y).le
  have hpsiNonneg : 0 ≤ chebyshevPsi (Real.exp y) := by
    unfold chebyshevPsi
    exact Finset.sum_nonneg fun n _ => by
      rw [vonMangoldt_eq_mathlib]
      exact ArithmeticFunction.vonMangoldt_nonneg
  have herror :
      |chebyshevPsi (Real.exp y) - Real.exp y| ≤
        (Real.log 4 + 5) * Real.exp y := by
    rw [abs_sub_le_iff]
    constructor
    · nlinarith [Real.exp_pos y]
    · nlinarith [Real.exp_pos y,
        Real.log_pos (by norm_num : 1 < (4 : Real))]
  have hcoef : 0 ≤ 1 - rho.re := by linarith
  have hyUpper : y ≤ (q + d) * m := hy.2
  have hexp :
      Real.exp ((1 - rho.re) * y) ≤
        Real.exp ((1 - rho.re) * ((q + d) * m)) := by
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hyUpper hcoef)
  unfold normalizedPsiError centeredNormalizedPsiErrorWindowEnvelope
  rw [abs_mul, abs_mul, abs_of_nonneg (norm_nonneg rho),
    abs_of_pos (Real.exp_pos _)]
  calc
    norm rho * |chebyshevPsi (Real.exp y) - Real.exp y| *
          Real.exp (-rho.re * y) ≤
        norm rho * ((Real.log 4 + 5) * Real.exp y) *
          Real.exp (-rho.re * y) := by
      gcongr
    _ = norm rho * (Real.log 4 + 5) *
          Real.exp ((1 - rho.re) * y) := by
      rw [show
          norm rho * ((Real.log 4 + 5) * Real.exp y) *
                Real.exp (-rho.re * y) =
              norm rho * (Real.log 4 + 5) *
                (Real.exp y * Real.exp (-rho.re * y)) by ring,
        ← Real.exp_add]
      congr 1
      ring_nf
    _ ≤ norm rho * (Real.log 4 + 5) *
          Real.exp ((1 - rho.re) * ((q + d) * m)) := by
      exact mul_le_mul_of_nonneg_left hexp
        (mul_nonneg (norm_nonneg rho) (by positivity))

/-- Pointwise envelope for the weighted normalized-error square. -/
def centeredSharpenedWeightedErrorEnvelope
    (q d : Real) (rho : Complex) (k : Nat) (m : Real) : Real :=
  centeredNormalizedPsiErrorWindowEnvelope q d rho m ^ 2 *
    (centeredSharpenedProjectedPsiKernelEnvelopeConstant q rho k /
      Real.sqrt m)

/-- Explicit lower bound for the logarithmic measure of strict pi/2
oscillations in one centered Gaussian window. -/
def centeredStrictPiOverTwoMeasureLowerBound
    (q d : Real) (rho : Complex) (k : Nat) (m : Real) : Real :=
  let multiplicity : Real := analyticOrderNatAt riemannZeta rho
  let threshold : Real :=
    multiplicity * strictPiOverTwoOscillationConstant k
  (centeredThresholdEnergyGap multiplicity
      (sharpenedMissingHarmonicDenominator k) threshold / 2) /
    centeredSharpenedWeightedErrorEnvelope q d rho k m

/-- The displayed quantitative lower bound is genuinely positive whenever
`rho` is an off-pole zeta zero and the Gaussian scale is positive. -/
theorem centeredStrictPiOverTwoMeasureLowerBound_pos
    {q d m : Real} {rho : Complex} {k : Nat}
    (hm : 0 < m) (hrhoRe0 : 0 < rho.re) (hrhoRe1 : rho.re < 1)
    (hzero : riemannZeta rho = 0) :
    0 < centeredStrictPiOverTwoMeasureLowerBound q d rho k m := by
  let multiplicity : Real := analyticOrderNatAt riemannZeta rho
  let mean : Real := sharpenedMissingHarmonicDenominator k
  let threshold : Real :=
    multiplicity * strictPiOverTwoOscillationConstant k
  have hrho : rho ≠ 0 := ne_zero_of_re_pos hrhoRe0
  have hrho1 : rho ≠ 1 := by
    intro hrhoEq
    have hre := congrArg Complex.re hrhoEq
    norm_num at hre
    linarith
  have hmult : 0 < multiplicity := by
    dsimp [multiplicity]
    exact_mod_cast
      ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero hrho1 hzero
  have hmean : 0 < mean := by
    dsimp [mean]
    exact sharpenedMissingHarmonicDenominator_pos k
  have hthreshold0 : 0 ≤ threshold := by
    dsimp [threshold]
    exact mul_nonneg hmult.le
      (le_trans (by positivity : 0 ≤ Real.pi / 2)
        (pi_div_two_lt_strictPiOverTwoOscillationConstant k).le)
  have hthreshold : threshold < multiplicity / mean := by
    dsimp [threshold, mean]
    rw [show
        multiplicity / sharpenedMissingHarmonicDenominator k =
          multiplicity * sharpenedMissingHarmonicLowerBound k by
      unfold sharpenedMissingHarmonicLowerBound
      ring]
    exact mul_lt_mul_of_pos_left
      (strictPiOverTwoOscillationConstant_lt_lowerBound k) hmult
  have hgap :
      0 < centeredThresholdEnergyGap multiplicity mean threshold :=
    centeredThresholdEnergyGap_pos hmult hmean hthreshold0 hthreshold
  have herrorEnvelope :
      0 < centeredNormalizedPsiErrorWindowEnvelope q d rho m := by
    unfold centeredNormalizedPsiErrorWindowEnvelope
    exact mul_pos
      (mul_pos (norm_pos_iff.mpr hrho) (by positivity))
      (Real.exp_pos _)
  have henvelope :
      0 < centeredSharpenedWeightedErrorEnvelope q d rho k m := by
    unfold centeredSharpenedWeightedErrorEnvelope
    exact mul_pos (sq_pos_of_pos herrorEnvelope)
      (div_pos
        (centeredSharpenedProjectedPsiKernelEnvelopeConstant_pos q rho k)
        (Real.sqrt_pos.2 hm))
  unfold centeredStrictPiOverTwoMeasureLowerBound
  dsimp only [multiplicity, mean, threshold]
  exact div_pos (half_pos hgap) henvelope

theorem eventually_centeredSharpened_measure_gt_explicit_strictPiOverTwo
    {q d : Real} {rho : Complex} {k : Nat}
    (hq : 16 ≤ q) (hd : 0 < d) (hdq : d < q)
    (hmargin : 16 * (q + d) ≤ d ^ 2)
    (hrhoRe0 : 0 < rho.re) (hrhoRe1 : rho.re < 1)
    (hgamma : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (hmissing :
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0) :
    ∀ᶠ m : Real in atTop,
      centeredStrictPiOverTwoMeasureLowerBound q d rho k m <
        volume.real
          {y ∈ localizedGaussianLogWindow q d m |
            (analyticOrderNatAt riemannZeta rho : Real) *
                  strictPiOverTwoOscillationConstant k <
              |normalizedPsiError rho y|} := by
  let multiplicity : Real := analyticOrderNatAt riemannZeta rho
  let mean : Real := sharpenedMissingHarmonicDenominator k
  let threshold : Real :=
    multiplicity * strictPiOverTwoOscillationConstant k
  let data :=
    sharpenedCenteredLocalizedContourData
      q d hq hd hdq hmargin
      hrhoRe0 hrhoRe1 hgamma hzero hmissing
  have hrho : rho ≠ 0 := ne_zero_of_re_pos hrhoRe0
  have hmult : 0 < multiplicity := by
    dsimp [multiplicity]
    have hrho1 : rho ≠ 1 := by
      intro hrhoEq
      have hre := congrArg Complex.re hrhoEq
      norm_num at hre
      linarith
    exact_mod_cast
      ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero
        hrho1 hzero
  have hmean : 0 < mean := by
    dsimp [mean]
    exact sharpenedMissingHarmonicDenominator_pos k
  have hthreshold0 : 0 ≤ threshold := by
    dsimp [threshold]
    exact mul_nonneg hmult.le
      (le_trans (by positivity : 0 ≤ Real.pi / 2)
        (pi_div_two_lt_strictPiOverTwoOscillationConstant k).le)
  have hthreshold : threshold < multiplicity / mean := by
    dsimp [threshold, mean]
    rw [show
        multiplicity / sharpenedMissingHarmonicDenominator k =
          multiplicity * sharpenedMissingHarmonicLowerBound k by
      unfold sharpenedMissingHarmonicLowerBound
      ring]
    exact mul_lt_mul_of_pos_left
      (strictPiOverTwoOscillationConstant_lt_lowerBound k) hmult
  have hgap :=
    data.eventually_secondMoment_sub_thresholdMass_gt_half_gap
      hmult hmean hthreshold0 hthreshold
  filter_upwards [hgap, data.eventually_kernel_integrable,
    data.eventually_second_moment_integrable,
    eventually_ge_atTop (1 : Real)] with
      m hgapM hkernelInt hsecondInt hm
  let window : Set Real := localizedGaussianLogWindow q d m
  let weight : Real -> Real := fun y => |data.kernel m y|
  let envelope : Real :=
    centeredSharpenedWeightedErrorEnvelope q d rho k m
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.2 (zero_lt_one.trans_le hm)
  have herrorEnvelope :
      0 < centeredNormalizedPsiErrorWindowEnvelope q d rho m := by
    unfold centeredNormalizedPsiErrorWindowEnvelope
    exact mul_pos
      (mul_pos (norm_pos_iff.mpr hrho) (by positivity))
      (Real.exp_pos _)
  have henvelope : 0 < envelope := by
    dsimp [envelope]
    unfold centeredSharpenedWeightedErrorEnvelope
    exact mul_pos (sq_pos_of_pos herrorEnvelope)
      (div_pos
        (centeredSharpenedProjectedPsiKernelEnvelopeConstant_pos q rho k)
        hsqrt)
  have hpointwise :
      ∀ y ∈ window,
        normalizedPsiError rho y ^ 2 * weight y ≤ envelope := by
    intro y hy
    have herrorAbs :=
      normalizedPsiError_abs_le_centeredWindowEnvelope
        hrhoRe1 hy
    have herrorSq :
        normalizedPsiError rho y ^ 2 ≤
          centeredNormalizedPsiErrorWindowEnvelope q d rho m ^ 2 := by
      nlinarith [sq_abs (normalizedPsiError rho y),
        abs_nonneg (normalizedPsiError rho y)]
    have hkernel :=
      centeredSharpenedProjectedPsiKernel_abs_le_inv_sqrt
        q hrho hgamma m hm y
    dsimp [weight, envelope]
    unfold centeredSharpenedWeightedErrorEnvelope
    exact mul_le_mul herrorSq hkernel
      (abs_nonneg _) (sq_nonneg _)
  have hmeasureBound :=
    MathlibAux.weightedSecondMoment_sub_thresholdMass_le_envelope_mul_measure
      (mu := volume) (s := window)
      (f := normalizedPsiError rho) (w := weight)
      (C := threshold) (B := envelope)
      measurableSet_Icc isCompact_Icc.measure_lt_top.ne
      (by
        have hpsi : Measurable chebyshevPsi := by
          simpa only [chebyshevPsi_eq_mathlib] using
            Chebyshev.psi_mono.measurable
        unfold normalizedPsiError
        fun_prop)
      (fun _ => abs_nonneg _)
      (by simpa [window, weight] using hsecondInt)
      (by exact hkernelInt.abs.integrableOn)
      hthreshold0 hpointwise
  have hwindowMass :
      (∫ y in window, weight y) ≤ data.coefficient m := by
    have hle :=
      setIntegral_le_integral hkernelInt.abs
        (Filter.Eventually.of_forall fun y => abs_nonneg (data.kernel m y))
    rw [data.coefficient_eq_kernel_mass m] at hle
    simpa [window, weight] using hle
  have hgapWindow :
      centeredThresholdEnergyGap multiplicity mean threshold / 2 <
        centeredNormalizedWindowSecondMoment q d rho data.kernel m -
          threshold ^ 2 * ∫ y in window, weight y := by
    exact hgapM.trans_le
      (sub_le_sub_left
        (mul_le_mul_of_nonneg_left hwindowMass (sq_nonneg threshold)) _)
  have hproduct :
      centeredThresholdEnergyGap multiplicity mean threshold / 2 <
        envelope * volume.real {y ∈ window |
          threshold < |normalizedPsiError rho y|} := by
    exact hgapWindow.trans_le (by
      simpa [centeredNormalizedWindowSecondMoment, window, weight] using
        hmeasureBound)
  unfold centeredStrictPiOverTwoMeasureLowerBound
  dsimp only [multiplicity, mean, threshold] at hproduct ⊢
  apply (div_lt_iff₀ henvelope).2
  simpa [window, envelope, mul_comm]

/-- Carlson supplies a missing odd harmonic, giving an explicit quantitative
measure lower bound in every sufficiently late epsilon logarithmic window. -/
theorem
    exists_eventually_explicit_measure_in_epsilonLogWindow_gt_strictPiOverTwo
    {epsilon : Real} {rho : Complex} {sigma : Real}
    (hepsilon : 0 < epsilon)
    (hgamma : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (hsigma : 1 / 2 < sigma)
    (hsigmaRho : sigma < rho.re)
    (hrhoRe1 : rho.re < 1) :
    exists k : Nat,
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0 ∧
      Real.pi / 2 < strictPiOverTwoOscillationConstant k ∧
      ∀ᶠ Y : Real in atTop,
        0 < centeredStrictPiOverTwoMeasureLowerBound
              (epsilonCenterCoefficient epsilon)
              (epsilonRadiusCoefficient epsilon) rho k
              (epsilonGaussianScale epsilon Y) ∧
          centeredStrictPiOverTwoMeasureLowerBound
                (epsilonCenterCoefficient epsilon)
                (epsilonRadiusCoefficient epsilon) rho k
                (epsilonGaussianScale epsilon Y) <
            volume.real
              {y ∈ Set.Icc (Real.log Y) ((1 + epsilon) * Real.log Y) |
                (analyticOrderNatAt riemannZeta rho : Real) *
                      strictPiOverTwoOscillationConstant k <
                  |normalizedPsiError rho y|} := by
  have hrhoRe0 : 0 < rho.re := by linarith
  rcases
      exists_missing_oddHarmonic_with_strict_gap_of_carlson
        hrhoRe1 hgamma hsigma hsigmaRho with
    ⟨k, hmissing, _⟩
  have hmissing' :
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0 := by
    simpa [missingHarmonicContourCenter] using hmissing
  have hlocal :=
    eventually_centeredSharpened_measure_gt_explicit_strictPiOverTwo
      (epsilonCenterCoefficient_ge_sixteen hepsilon)
      (epsilonRadiusCoefficient_pos hepsilon)
      (epsilonRadiusCoefficient_lt_center hepsilon)
      (epsilonRadius_sq_ge_sixteen_mul hepsilon)
      hrhoRe0 hrhoRe1 hgamma hzero hmissing'
  have hscaled :=
    (tendsto_epsilonGaussianScale_atTop hepsilon).eventually hlocal
  refine
    ⟨k, hmissing',
      pi_div_two_lt_strictPiOverTwoOscillationConstant k, ?_⟩
  filter_upwards [hscaled, eventually_gt_atTop (1 : Real)] with Y hY hYone
  constructor
  · exact centeredStrictPiOverTwoMeasureLowerBound_pos
      (by
        unfold epsilonGaussianScale
        exact div_pos (Real.log_pos hYone)
          (sub_pos.mpr (epsilonRadiusCoefficient_lt_center hepsilon)))
      hrhoRe0 hrhoRe1 hzero
  · simpa only [localizedGaussianLogWindow_epsilonGaussianScale hepsilon Y]
      using hY

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
