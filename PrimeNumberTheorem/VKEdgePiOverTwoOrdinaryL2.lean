import PrimeNumberTheorem.VKEdgePiOverTwoGaussianL2
import PrimeNumberTheorem.VKEdgePiOverTwoEpsilonOscillation

open Complex Filter MeasureTheory Polynomial Set Topology

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- Explicit envelope constant for a relatively normalized projected
kernel. -/
def relativeProjectedPsiKernelAtCenterEnvelopeConstant
    (A : ℂ[X]) (target center c : ℂ) : ℝ :=
  (‖center‖ / ‖target‖) *
    projectedPsiKernelAtCenterEnvelopeConstant (C c * A) center

theorem relativeProjectedPsiKernelAtCenterEnvelopeConstant_nonneg
    (A : ℂ[X]) (target center c : ℂ) :
    0 ≤
      relativeProjectedPsiKernelAtCenterEnvelopeConstant
        A target center c := by
  unfold relativeProjectedPsiKernelAtCenterEnvelopeConstant
  exact mul_nonneg
    (div_nonneg (norm_nonneg center) (norm_nonneg target))
    (projectedPsiKernelAtCenterEnvelopeConstant_nonneg (C c * A) center)

/--
Named positive constant controlling the paired sharpened kernel by
`1 / sqrt(m)`. The additive `1` keeps the public lower-bound constant
strictly positive without requiring coefficient normalization lemmas.
-/
def centeredSharpenedProjectedPsiKernelEnvelopeConstant
    (q : ℝ) (rho : ℂ) (k : ℕ) : ℝ :=
  1 + Real.exp 1 *
    (projectedPsiKernelAtCenterEnvelopeConstant
        (centeredSharpenedTargetFilter q rho) rho +
      relativeProjectedPsiKernelAtCenterEnvelopeConstant
        (centeredSharpenedMissingFilter q rho k) rho
        (missingHarmonicContourCenter rho k)
        (missingHarmonicContourCoefficient rho k))

theorem centeredSharpenedProjectedPsiKernelEnvelopeConstant_pos
    (q : ℝ) (rho : ℂ) (k : ℕ) :
    0 < centeredSharpenedProjectedPsiKernelEnvelopeConstant q rho k := by
  unfold centeredSharpenedProjectedPsiKernelEnvelopeConstant
  have hsum : 0 ≤
      projectedPsiKernelAtCenterEnvelopeConstant
          (centeredSharpenedTargetFilter q rho) rho +
        relativeProjectedPsiKernelAtCenterEnvelopeConstant
          (centeredSharpenedMissingFilter q rho k) rho
          (missingHarmonicContourCenter rho k)
          (missingHarmonicContourCoefficient rho k) :=
    add_nonneg
      (projectedPsiKernelAtCenterEnvelopeConstant_nonneg _ _)
      (relativeProjectedPsiKernelAtCenterEnvelopeConstant_nonneg _ _ _ _)
  positivity

private theorem relativeProjectedPsiKernelAtCenter_abs_le_scaled
    (q : ℝ) (A : ℂ[X]) {target center c : ℂ}
    (_htarget : target ≠ 0) (hcenter : center ≠ 0)
    (m : ℝ) (hm : 1 ≤ m) (y : ℝ) :
    |relativeProjectedPsiKernelAtCenter
        q A target center c m y| ≤
      relativeProjectedPsiKernelAtCenterEnvelopeConstant
          A target center c *
        Real.exp |(Real.sqrt m)⁻¹ * (q * m - y)| *
        normalizedGaussian m (q * m - y) := by
  have hratio : 0 ≤ ‖center‖ / ‖target‖ :=
    div_nonneg (norm_nonneg center) (norm_nonneg target)
  unfold relativeProjectedPsiKernelAtCenter
    relativeProjectedPsiKernelAtCenterEnvelopeConstant
  rw [abs_mul, abs_of_nonneg hratio]
  have hbound :=
    projectedPsiKernelAtCenter_abs_le_scaled_exp_abs_mul
      q (C c * A) hcenter m hm y
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left hbound hratio

/-- The true paired zeta kernel has an explicit global `1 / sqrt(m)`
pointwise bound. -/
theorem centeredSharpenedProjectedPsiKernel_abs_le_inv_sqrt
    (q : ℝ) {rho : ℂ} {k : ℕ}
    (hrho : rho ≠ 0) (hgamma : 0 < rho.im)
    (m : ℝ) (hm : 1 ≤ m) (y : ℝ) :
    |centeredSharpenedProjectedPsiKernel q rho k m y| ≤
      centeredSharpenedProjectedPsiKernelEnvelopeConstant q rho k /
        Real.sqrt m := by
  let center : ℂ := missingHarmonicContourCenter rho k
  have hcenter : center ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    dsimp [center] at him
    rw [missingHarmonicContourCenter, oddHarmonicPoint_im] at him
    have hk : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by positivity
    nlinarith
  let targetC : ℝ :=
    projectedPsiKernelAtCenterEnvelopeConstant
      (centeredSharpenedTargetFilter q rho) rho
  let missingC : ℝ :=
    relativeProjectedPsiKernelAtCenterEnvelopeConstant
      (centeredSharpenedMissingFilter q rho k) rho center
      (missingHarmonicContourCoefficient rho k)
  let envelope : ℝ :=
    Real.exp |(Real.sqrt m)⁻¹ * (q * m - y)| *
      normalizedGaussian m (q * m - y)
  have htarget :
      |projectedPsiKernelAtCenter q
          (centeredSharpenedTargetFilter q rho) rho m y| ≤
        targetC * envelope := by
    simpa only [targetC, envelope, mul_assoc] using
      projectedPsiKernelAtCenter_abs_le_scaled_exp_abs_mul
        q (centeredSharpenedTargetFilter q rho) hrho m hm y
  have hmissing :
      |relativeProjectedPsiKernelAtCenter q
          (centeredSharpenedMissingFilter q rho k) rho center
          (missingHarmonicContourCoefficient rho k) m y| ≤
        missingC * envelope := by
    simpa only [missingC, envelope, mul_assoc] using
      relativeProjectedPsiKernelAtCenter_abs_le_scaled
        (c := missingHarmonicContourCoefficient rho k)
        q (centeredSharpenedMissingFilter q rho k)
        hrho hcenter m hm y
  have hbase : 0 ≤ targetC + missingC := by
    exact add_nonneg
      (projectedPsiKernelAtCenterEnvelopeConstant_nonneg _ _)
      (relativeProjectedPsiKernelAtCenterEnvelopeConstant_nonneg _ _ _ _)
  have hpair :
      |centeredSharpenedProjectedPsiKernel q rho k m y| ≤
        (targetC + missingC) * envelope := by
    unfold centeredSharpenedProjectedPsiKernel
    calc
      |projectedPsiKernelAtCenter q
            (centeredSharpenedTargetFilter q rho) rho m y +
          relativeProjectedPsiKernelAtCenter q
            (centeredSharpenedMissingFilter q rho k) rho center
            (missingHarmonicContourCoefficient rho k) m y| ≤
          |projectedPsiKernelAtCenter q
              (centeredSharpenedTargetFilter q rho) rho m y| +
            |relativeProjectedPsiKernelAtCenter q
              (centeredSharpenedMissingFilter q rho k) rho center
              (missingHarmonicContourCoefficient rho k) m y| :=
        (by
          simpa only [Real.norm_eq_abs] using
            norm_add_le
              (projectedPsiKernelAtCenter q
                (centeredSharpenedTargetFilter q rho) rho m y)
              (relativeProjectedPsiKernelAtCenter q
                (centeredSharpenedMissingFilter q rho k) rho center
                (missingHarmonicContourCoefficient rho k) m y))
      _ ≤ targetC * envelope + missingC * envelope :=
        add_le_add htarget hmissing
      _ = (targetC + missingC) * envelope := by ring
  have hgaussian :
      envelope ≤ Real.exp 1 / Real.sqrt m := by
    exact
      exp_scaled_abs_mul_normalizedGaussian_le_exp_one_div_sqrt
        hm (q * m - y)
  have hsqrtPos : 0 < Real.sqrt m :=
    Real.sqrt_pos.2 (zero_lt_one.trans_le hm)
  calc
    |centeredSharpenedProjectedPsiKernel q rho k m y| ≤
        (targetC + missingC) * envelope := hpair
    _ ≤ (targetC + missingC) * (Real.exp 1 / Real.sqrt m) :=
      mul_le_mul_of_nonneg_left hgaussian hbase
    _ ≤ centeredSharpenedProjectedPsiKernelEnvelopeConstant q rho k /
          Real.sqrt m := by
      rw [show
          (targetC + missingC) * (Real.exp 1 / Real.sqrt m) =
            ((targetC + missingC) * Real.exp 1) / Real.sqrt m by ring]
      apply div_le_div_of_nonneg_right _ hsqrtPos.le
      unfold centeredSharpenedProjectedPsiKernelEnvelopeConstant
      dsimp [targetC, missingC, center]
      nlinarith [Real.exp_pos 1]

/-- The unweighted second moment of the normalized PNT error in a centered
logarithmic window. -/
def centeredNormalizedWindowOrdinarySecondMoment
    (q d : ℝ) (rho : ℂ) (m : ℝ) : ℝ :=
  ∫ y : ℝ in localizedGaussianLogWindow q d m,
    normalizedPsiError rho y ^ 2

/-- Expanded form of the ordinary moment in terms of the standard Chebyshev
error. -/
theorem centeredNormalizedWindowOrdinarySecondMoment_eq
    (q d : ℝ) (rho : ℂ) (m : ℝ) :
    centeredNormalizedWindowOrdinarySecondMoment q d rho m =
      ∫ y : ℝ in localizedGaussianLogWindow q d m,
        ‖rho‖ ^ 2 *
          (chebyshevPsi (Real.exp y) - Real.exp y) ^ 2 *
          Real.exp (-2 * rho.re * y) := by
  unfold centeredNormalizedWindowOrdinarySecondMoment normalizedPsiError
  apply integral_congr_ae
  filter_upwards with y
  have hexp : Real.exp (-rho.re * y) ^ 2 =
      Real.exp (-2 * rho.re * y) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  calc
    (‖rho‖ * (chebyshevPsi (Real.exp y) - Real.exp y) *
        Real.exp (-rho.re * y)) ^ 2 =
      ‖rho‖ ^ 2 *
        (chebyshevPsi (Real.exp y) - Real.exp y) ^ 2 *
        Real.exp (-rho.re * y) ^ 2 := by ring
    _ = _ := by rw [hexp]

/--
A pointwise `K / sqrt(m)` kernel bound converts a weighted second-moment
lower bound into an ordinary local second-moment lower bound.
-/
theorem ordinarySecondMoment_lower_of_weightedSecondMoment
    {q d : ℝ} {rho : ℂ} {kernel : ℝ → ℝ → ℝ}
    {m C2 K : ℝ}
    (hm : 1 ≤ m)
    (hkernel :
      ∀ y ∈ localizedGaussianLogWindow q d m,
        |kernel m y| ≤ K / Real.sqrt m)
    (hweightedInt :
      IntegrableOn
        (fun y => normalizedPsiError rho y ^ 2 * |kernel m y|)
        (localizedGaussianLogWindow q d m))
    (hordinaryInt :
      IntegrableOn
        (fun y => normalizedPsiError rho y ^ 2)
        (localizedGaussianLogWindow q d m))
    (hweighted :
      C2 <
        centeredNormalizedWindowSecondMoment q d rho kernel m) :
    C2 * Real.sqrt m <
      K * centeredNormalizedWindowOrdinarySecondMoment q d rho m := by
  have hsqrtPos : 0 < Real.sqrt m :=
    Real.sqrt_pos.2 (zero_lt_one.trans_le hm)
  have hmajorInt :
      IntegrableOn
        (fun y =>
          (K / Real.sqrt m) * normalizedPsiError rho y ^ 2)
        (localizedGaussianLogWindow q d m) := by
    change Integrable
      (fun y : ℝ =>
        (K / Real.sqrt m) * normalizedPsiError rho y ^ 2)
      (volume.restrict (localizedGaussianLogWindow q d m))
    simpa [mul_comm] using hordinaryInt.const_mul (K / Real.sqrt m)
  have hmomentLe :
      centeredNormalizedWindowSecondMoment q d rho kernel m ≤
        (K / Real.sqrt m) *
          centeredNormalizedWindowOrdinarySecondMoment q d rho m := by
    unfold centeredNormalizedWindowSecondMoment
      centeredNormalizedWindowOrdinarySecondMoment
    calc
      (∫ y : ℝ in localizedGaussianLogWindow q d m,
          normalizedPsiError rho y ^ 2 * |kernel m y|) ≤
          ∫ y : ℝ in localizedGaussianLogWindow q d m,
            (K / Real.sqrt m) * normalizedPsiError rho y ^ 2 := by
        apply integral_mono_ae hweightedInt hmajorInt
        filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
        have hsq : 0 ≤ normalizedPsiError rho y ^ 2 := sq_nonneg _
        calc
          normalizedPsiError rho y ^ 2 * |kernel m y| ≤
              normalizedPsiError rho y ^ 2 * (K / Real.sqrt m) :=
            mul_le_mul_of_nonneg_left (hkernel y hy) hsq
          _ = (K / Real.sqrt m) *
              normalizedPsiError rho y ^ 2 := by ring
      _ = (K / Real.sqrt m) *
          ∫ y : ℝ in localizedGaussianLogWindow q d m,
            normalizedPsiError rho y ^ 2 := by
        rw [integral_const_mul]
  calc
    C2 * Real.sqrt m <
        ((K / Real.sqrt m) *
          centeredNormalizedWindowOrdinarySecondMoment q d rho m) *
            Real.sqrt m :=
      mul_lt_mul_of_pos_right (hweighted.trans_le hmomentLe) hsqrtPos
    _ = K * centeredNormalizedWindowOrdinarySecondMoment q d rho m := by
      field_simp

private theorem measurable_normalizedPsiError_ordinary (rho : ℂ) :
    Measurable (normalizedPsiError rho) := by
  have hpsi : Measurable chebyshevPsi := by
    change Measurable (Chebyshev.psi : ℝ → ℝ)
    simpa only [chebyshevPsi_eq_mathlib] using Chebyshev.psi_mono.measurable
  unfold normalizedPsiError
  fun_prop

private theorem normalizedPsiError_abs_le_exp_growth
    (rho : ℂ) (y : ℝ) :
    |normalizedPsiError rho y| ≤
      ‖rho‖ * (Real.log 4 + 5) *
        Real.exp ((1 - rho.re) * y) := by
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
        Real.log_pos (by norm_num : 1 < (4 : ℝ))]
  unfold normalizedPsiError
  rw [abs_mul, abs_mul, abs_of_nonneg (norm_nonneg rho),
    abs_of_pos (Real.exp_pos _)]
  calc
    ‖rho‖ * |chebyshevPsi (Real.exp y) - Real.exp y| *
          Real.exp (-rho.re * y) ≤
        ‖rho‖ * ((Real.log 4 + 5) * Real.exp y) *
          Real.exp (-rho.re * y) := by
      gcongr
    _ = ‖rho‖ * (Real.log 4 + 5) *
          Real.exp ((1 - rho.re) * y) := by
      calc
        ‖rho‖ * ((Real.log 4 + 5) * Real.exp y) *
              Real.exp (-rho.re * y) =
            ‖rho‖ * (Real.log 4 + 5) *
              (Real.exp y * Real.exp (-rho.re * y)) := by ring
        _ = ‖rho‖ * (Real.log 4 + 5) *
              Real.exp (y + -rho.re * y) := by rw [Real.exp_add]
        _ = _ := by
          congr 1
          ring_nf

private theorem integrableOn_normalizedPsiError_sq_Icc
    {rho : ℂ} (hrhoRe1 : rho.re < 1) (a b : ℝ) :
    IntegrableOn (fun y => normalizedPsiError rho y ^ 2)
      (Set.Icc a b) := by
  let B : ℝ :=
    (‖rho‖ * (Real.log 4 + 5) *
      Real.exp ((1 - rho.re) * b)) ^ 2
  apply IntegrableOn.of_bound isCompact_Icc.measure_lt_top
  · exact
      ((measurable_normalizedPsiError_ordinary rho).pow_const 2
        |>.aestronglyMeasurable).restrict
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    have hcoef : 0 ≤ 1 - rho.re := by linarith
    have hexp :
        Real.exp ((1 - rho.re) * y) ≤
          Real.exp ((1 - rho.re) * b) := by
      exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hy.2 hcoef)
    have habs :=
      (normalizedPsiError_abs_le_exp_growth rho y).trans
        (mul_le_mul_of_nonneg_left hexp
          (mul_nonneg (norm_nonneg rho)
            (by positivity : 0 ≤ Real.log 4 + 5)))
    have hsq :
        normalizedPsiError rho y ^ 2 ≤ B := by
      dsimp [B]
      nlinarith [sq_abs (normalizedPsiError rho y),
        abs_nonneg (normalizedPsiError rho y)]
    rw [Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (normalizedPsiError rho y))]
    exact hsq

/-- Explicit ordinary-L2 constant attached to one target zero and one
missing odd harmonic. -/
def centeredSharpenedOrdinaryL2Constant
    (q : ℝ) (rho : ℂ) (k : ℕ) : ℝ :=
  ((analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 /
      sharpenedMissingHarmonicDenominator k) /
    centeredSharpenedProjectedPsiKernelEnvelopeConstant q rho k

/--
The true zeta contour forces an explicit ordinary local L2 lower bound of
order `sqrt(m)`, retaining analytic multiplicity.
-/
theorem
    eventually_centeredSharpenedNormalizedPsiError_ordinarySecondMoment_gt
    {q d : ℝ} {rho : ℂ} {k : ℕ}
    (hq : 16 ≤ q) (hd : 0 < d) (hdq : d < q)
    (hmargin : 16 * (q + d) ≤ d ^ 2)
    (hrhoRe0 : 0 < rho.re) (hrhoRe1 : rho.re < 1)
    (hgamma : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (hmissing :
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0) :
    ∀ᶠ m : ℝ in atTop,
      centeredSharpenedOrdinaryL2Constant q rho k *
          Real.sqrt m <
        centeredNormalizedWindowOrdinarySecondMoment q d rho m := by
  have hrho : rho ≠ 0 := ne_zero_of_re_pos hrhoRe0
  let multiplicity : ℝ := analyticOrderNatAt riemannZeta rho
  let denominator : ℝ := sharpenedMissingHarmonicDenominator k
  let K : ℝ :=
    centeredSharpenedProjectedPsiKernelEnvelopeConstant q rho k
  let C2 : ℝ := multiplicity ^ 2 / denominator
  have hdenomPos : 0 < denominator :=
    sharpenedMissingHarmonicDenominator_pos k
  have hmultPos : 0 < multiplicity := by
    dsimp [multiplicity]
    exact_mod_cast
      ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero
        (by exact ne_of_apply_ne Complex.re (by simpa using hrhoRe1.ne))
        hzero
  have hC2 :
      C2 < 2 * multiplicity ^ 2 / denominator := by
    dsimp [C2]
    have hsquare : 0 < multiplicity ^ 2 := sq_pos_of_pos hmultPos
    apply (div_lt_div_iff_of_pos_right hdenomPos).2
    nlinarith
  have hweighted :=
    eventually_centeredSharpenedNormalizedPsiError_secondMoment_gt
      hq hd hdq hmargin hrhoRe0 hrhoRe1 hgamma hzero hmissing hC2
  let data :=
    sharpenedCenteredLocalizedContourData
      q d hq hd hdq hmargin
      hrhoRe0 hrhoRe1 hgamma hzero hmissing
  filter_upwards [
      hweighted,
      data.eventually_second_moment_integrable,
      eventually_ge_atTop (1 : ℝ)] with
      m hweightedM hweightedInt hm
  have hordinaryInt :
      IntegrableOn (fun y => normalizedPsiError rho y ^ 2)
        (localizedGaussianLogWindow q d m) := by
    exact integrableOn_normalizedPsiError_sq_Icc hrhoRe1 _ _
  have htransfer :=
    ordinarySecondMoment_lower_of_weightedSecondMoment
      hm
      (fun y _ =>
        centeredSharpenedProjectedPsiKernel_abs_le_inv_sqrt
          q hrho hgamma m hm y)
      hweightedInt hordinaryInt hweightedM
  have hKpos : 0 < K :=
    centeredSharpenedProjectedPsiKernelEnvelopeConstant_pos q rho k
  unfold centeredSharpenedOrdinaryL2Constant
  dsimp [C2, multiplicity, denominator, K] at htransfer ⊢
  rw [show
      (analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 /
            sharpenedMissingHarmonicDenominator k /
            centeredSharpenedProjectedPsiKernelEnvelopeConstant q rho k *
          Real.sqrt m =
        (((analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 /
            sharpenedMissingHarmonicDenominator k) *
          Real.sqrt m) /
            centeredSharpenedProjectedPsiKernelEnvelopeConstant q rho k by
    ring]
  exact (div_lt_iff₀ hKpos).2 (by
    simpa [mul_comm] using htransfer)

/--
For every positive epsilon, Carlson selects a missing odd harmonic and the
ordinary normalized error has an explicit `sqrt(log Y)`-scale L2 lower
bound in every sufficiently late logarithmic window.
-/
theorem exists_eventually_ordinarySecondMoment_in_epsilonLogWindow_gt
    {ε : ℝ} {rho : ℂ} {sigma : ℝ}
    (hε : 0 < ε)
    (hgamma : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (hσ : 1 / 2 < sigma)
    (hσrho : sigma < rho.re)
    (hrhoRe1 : rho.re < 1) :
    ∃ k : ℕ,
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0 ∧
      0 < centeredSharpenedOrdinaryL2Constant
        (epsilonCenterCoefficient ε) rho k ∧
      ∀ᶠ Y : ℝ in atTop,
        centeredSharpenedOrdinaryL2Constant
              (epsilonCenterCoefficient ε) rho k *
            Real.sqrt (epsilonGaussianScale ε Y) <
          ∫ y : ℝ in
              Set.Icc (Real.log Y) ((1 + ε) * Real.log Y),
            normalizedPsiError rho y ^ 2 := by
  have hrhoRe0 : 0 < rho.re := by linarith
  rcases
      exists_missing_oddHarmonic_with_strict_gap_of_carlson
        hrhoRe1 hgamma hσ hσrho with
    ⟨k, hmissing, _⟩
  have hmissing' :
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0 := by
    simpa [missingHarmonicContourCenter] using hmissing
  have hlocal :=
    eventually_centeredSharpenedNormalizedPsiError_ordinarySecondMoment_gt
      (epsilonCenterCoefficient_ge_sixteen hε)
      (epsilonRadiusCoefficient_pos hε)
      (epsilonRadiusCoefficient_lt_center hε)
      (epsilonRadius_sq_ge_sixteen_mul hε)
      hrhoRe0 hrhoRe1 hgamma hzero hmissing'
  have hscaled :=
    (tendsto_epsilonGaussianScale_atTop hε).eventually hlocal
  have hconstantPos :
      0 < centeredSharpenedOrdinaryL2Constant
          (epsilonCenterCoefficient ε) rho k := by
    unfold centeredSharpenedOrdinaryL2Constant
    have hrho : rho ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num at hre
      linarith
    have hmult :
        0 < (analyticOrderNatAt riemannZeta rho : ℝ) := by
      exact_mod_cast
        ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero hrho hzero
    exact div_pos
      (div_pos (sq_pos_of_pos hmult)
        (sharpenedMissingHarmonicDenominator_pos k))
      (centeredSharpenedProjectedPsiKernelEnvelopeConstant_pos
        (epsilonCenterCoefficient ε) rho k)
  refine ⟨k, hmissing', hconstantPos, ?_⟩
  filter_upwards [hscaled] with Y hY
  simpa only [
    centeredNormalizedWindowOrdinarySecondMoment,
    localizedGaussianLogWindow_epsilonGaussianScale hε Y] using hY

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
