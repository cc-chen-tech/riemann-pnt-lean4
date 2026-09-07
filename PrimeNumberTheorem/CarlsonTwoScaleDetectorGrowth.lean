import PrimeNumberTheorem.CarlsonDetectorGrowth
import PrimeNumberTheorem.CarlsonTwoScaleFarRight

open Complex MeromorphicOn

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-!
# Fixed Jensen-circle growth for the two-scale Carlson detector

This file supplies the two detector-specific inputs used by the otherwise
coefficient-generic Jensen and horizontal-side argument: polynomial growth
on the outer circle and a quantitative lower bound at its right-line center.
-/

/-- The fixed outer Jensen disk stays in `Re(s)>0`, where the regularized
two-scale detector is analytic. -/
theorem analyticOnNhd_regularizedTwoScaleCarlsonZeroDetector_fixedJensenOuterDisk
    (Y0 Y1 : ℕ) (T : ℝ) :
    AnalyticOnNhd ℂ (regularizedTwoScaleCarlsonZeroDetector Y0 Y1)
      (Metric.closedBall
        ((4 : ℂ) + I * (T + 1 / 2)) (31 / 8 : ℝ)) := by
  intro z hz
  have hdist :
      ‖z - ((4 : ℂ) + I * (T + 1 / 2))‖ ≤ (31 / 8 : ℝ) := by
    simpa [Metric.mem_closedBall, Complex.dist_eq] using hz
  have hreAbs :=
    Complex.abs_re_le_norm (z - ((4 : ℂ) + I * (T + 1 / 2)))
  have hzre : 0 < z.re := by
    have : |z.re - 4| ≤ (31 / 8 : ℝ) := by
      simpa using hreAbs.trans hdist
    rw [abs_le] at this
    linarith
  exact analyticOnNhd_regularizedTwoScaleCarlsonZeroDetector_re_gt
    (theta := (0 : ℝ)) le_rfl Y0 Y1 z hzre

/-- The regularized two-scale detector has the same polynomial fixed-circle
growth as the sharp detector, with the outer support `Y1` replacing `X`. -/
theorem exists_norm_regularizedTwoScaleCarlsonZeroDetector_le_fixedJensenSphere :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {Y0 Y1 : ℕ}, 1 ≤ Y0 → Y0 < Y1 →
      ∀ {T : ℝ}, 5 ≤ T → ∀ {z : ℂ},
        z ∈ Metric.sphere
          ((4 : ℂ) + I * (T + 1 / 2)) (31 / 8 : ℝ) →
        ‖regularizedTwoScaleCarlsonZeroDetector Y0 Y1 z‖ ≤
          C * (Y1 : ℝ) ^ 2 * (T + 14) ^ 10 := by
  rcases exists_norm_riemannZeta_le_fixedJensenSphere with
    ⟨C₀, hC₀, hzeta⟩
  refine ⟨2 * C₀ ^ 2, by nlinarith, ?_⟩
  intro Y0 Y1 hY0 hY01 T hT z hz
  let U : ℝ := T + 14
  let A : ℝ := C₀ * (Y1 : ℝ) * U ^ 4
  have hU : 1 ≤ U := by dsimp [U]; linarith
  have hY1 : 1 ≤ Y1 := hY0.trans hY01.le
  have hY1Real : 1 ≤ (Y1 : ℝ) := by exact_mod_cast hY1
  have hUPow : 1 ≤ U ^ 4 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hU 4
  have hA : 2 ≤ A := by
    dsimp [A]
    nlinarith [mul_nonneg (show 0 ≤ C₀ by linarith)
        (show 0 ≤ (Y1 : ℝ) by positivity),
      mul_nonneg (show 0 ≤ C₀ * (Y1 : ℝ) by positivity)
        (show 0 ≤ U ^ 4 by positivity)]
  have hre := fixedJensenSphere_re_mem_Icc hT hz
  have him := fixedJensenSphere_abs_im_mem_Icc hT hz
  have hz0 : z ≠ 0 := by
    intro hz0
    subst z
    norm_num at him
  have hz1 : z ≠ 1 := by
    intro hz1
    subst z
    norm_num at him
  have hmollifier :
      ‖HardyTheorem.twoScaleSelbergMollifier Y0 Y1 z‖ ≤ (Y1 : ℝ) :=
    HardyTheorem.norm_twoScaleSelbergMollifier_le_natCast hY0 hY01 hre.1
  have hw :
      ‖riemannZeta z * HardyTheorem.twoScaleSelbergMollifier Y0 Y1 z‖ ≤ A := by
    rw [norm_mul]
    have hmul := mul_le_mul (hzeta hT hz) hmollifier
      (norm_nonneg (HardyTheorem.twoScaleSelbergMollifier Y0 Y1 z))
      (mul_nonneg (show 0 ≤ C₀ by linarith) (pow_nonneg (by positivity) 4))
    simpa [A, U, mul_assoc, mul_left_comm, mul_comm] using hmul
  let w : ℂ :=
    riemannZeta z * HardyTheorem.twoScaleSelbergMollifier Y0 Y1 z
  have htwoSub : ‖(2 : ℂ) - w‖ ≤ 2 + A := by
    calc
      ‖(2 : ℂ) - w‖ ≤ ‖(2 : ℂ)‖ + ‖w‖ := norm_sub_le _ _
      _ ≤ 2 + A := by simpa [w] using add_le_add_left hw 2
  have hdetector : ‖w * (2 - w)‖ ≤ 2 * A ^ 2 := by
    calc
      ‖w * (2 - w)‖ = ‖w‖ * ‖(2 : ℂ) - w‖ := norm_mul _ _
      _ ≤ A * (2 + A) :=
        mul_le_mul (by simpa [w] using hw) htwoSub (norm_nonneg _)
          (by positivity)
      _ ≤ A * (2 * A) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ = 2 * A ^ 2 := by ring
  have hsub := norm_sub_one_le_on_fixedJensenSphere hT hz
  have hsubPow : ‖z - 1‖ ^ 2 ≤ U ^ 2 := by
    apply pow_le_pow_left₀ (norm_nonneg _)
    simpa [U] using hsub
  rw [regularizedTwoScaleCarlsonZeroDetector_eq_sub_one_sq_mul hz0 hz1,
    twoScaleCarlsonZeroDetector_factorization]
  change ‖(z - 1) ^ 2 * (w * (2 - w))‖ ≤ _
  calc
    ‖(z - 1) ^ 2 * (w * (2 - w))‖ =
        ‖z - 1‖ ^ 2 * ‖w * (2 - w)‖ := by rw [norm_mul, norm_pow]
    _ ≤ U ^ 2 * (2 * A ^ 2) :=
      mul_le_mul hsubPow hdetector (norm_nonneg _)
        (pow_nonneg (by positivity) 2)
    _ = (2 * C₀ ^ 2) * (Y1 : ℝ) ^ 2 * (T + 14) ^ 10 := by
      dsimp [A, U]
      ring

/-- Complete multiplicity in the inner factorization disk, measured using
the divisor on the enclosing Jensen disk. -/
noncomputable def regularizedTwoScaleCarlsonFactorDiskZeroMass
    (Y0 Y1 : ℕ) (T : ℝ) : ℝ :=
  let c : ℂ := (4 : ℂ) + I * (T + 1 / 2)
  let outer := Metric.closedBall c (31 / 8 : ℝ)
  ∑ᶠ u ∈ (Metric.closedBall c (123 / 32 : ℝ) : Set ℂ),
    (MeromorphicOn.divisor
      (regularizedTwoScaleCarlsonZeroDetector Y0 Y1) outer u : ℝ)

/-- Jensen converts the outer-circle polynomial bound and a quantitative
right-line center bound into logarithmic local divisor mass. -/
theorem exists_regularizedTwoScaleCarlsonFactorDiskZeroMass_le_logPolynomial :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {Y0 Y1 : ℕ}, 1 ≤ Y0 → Y0 < Y1 →
      ∀ {T : ℝ}, 5 ≤ T →
        ‖twoScaleMollifiedZetaError Y0 Y1
          ((4 : ℂ) + I * (T + 1 / 2))‖ ≤ (1 / 3 : ℝ) →
        regularizedTwoScaleCarlsonFactorDiskZeroMass Y0 Y1 T ≤
          Real.log (C * (Y1 : ℝ) ^ 2 * (T + 14) ^ 10) /
            Real.log ((31 / 8 : ℝ) / (123 / 32 : ℝ)) := by
  rcases
      exists_norm_regularizedTwoScaleCarlsonZeroDetector_le_fixedJensenSphere with
    ⟨C, hC, hsphere⟩
  refine ⟨C, hC, ?_⟩
  intro Y0 Y1 hY0 hY01 T hT herr
  let c : ℂ := (4 : ℂ) + I * (T + 1 / 2)
  let M : ℝ := C * (Y1 : ℝ) ^ 2 * (T + 14) ^ 10
  have hY1 : 1 ≤ Y1 := hY0.trans hY01.le
  have hY1Real : 1 ≤ (Y1 : ℝ) := by exact_mod_cast hY1
  have hTPow : 1 ≤ (T + 14) ^ 10 := by
    have hTBase : 1 ≤ T + 14 := by linarith
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hTBase 10
  have hY1Pow : 1 ≤ (Y1 : ℝ) ^ 2 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hY1Real 2
  have hM : 1 ≤ M := by
    dsimp [M]
    simpa using
      mul_le_mul (mul_le_mul hC hY1Pow (by norm_num) (by positivity))
        hTPow (by norm_num) (by positivity)
  have hanalytic : AnalyticOnNhd ℂ
      (regularizedTwoScaleCarlsonZeroDetector Y0 Y1)
      (Metric.closedBall c (31 / 8 : ℝ)) := by
    simpa [c] using
      analyticOnNhd_regularizedTwoScaleCarlsonZeroDetector_fixedJensenOuterDisk
        Y0 Y1 T
  have hcenter :
      1 ≤ ‖regularizedTwoScaleCarlsonZeroDetector Y0 Y1 c‖ := by
    apply one_le_norm_regularizedTwoScaleCarlsonZeroDetector_of_four_le_re
    · simp [c]
    · simpa [c] using herr
  have hcircle : Real.circleAverage
      (Real.log ‖regularizedTwoScaleCarlsonZeroDetector Y0 Y1 ·‖)
        c (31 / 8 : ℝ) ≤ Real.log M := by
    apply circleAverage_log_norm_le_log_of_norm_le
    · norm_num
    · exact hanalytic.meromorphicOn
    · exact hM
    · intro z hz
      simpa [c, M] using hsphere hY0 hY01 hT (by simpa [c] using hz)
  have hjensen := jensen_inner_zero_multiplicity_le_log_div
    (c := c) (f := regularizedTwoScaleCarlsonZeroDetector Y0 Y1)
    (r := (123 / 32 : ℝ)) (R := (31 / 8 : ℝ)) (K := Real.log M)
    (m := (1 : ℝ)) (by norm_num) (by norm_num) hanalytic one_pos
    hcenter hcircle
  simpa [regularizedTwoScaleCarlsonFactorDiskZeroMass, c, M] using hjensen

/-- The two-scale plateau automatically supplies the quantitative Jensen
center bound, so the local divisor-mass estimate has no remaining far-right
hypothesis. -/
theorem exists_regularizedTwoScaleCarlsonFactorDiskZeroMass_le_logPolynomial_of_two_le_inner :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {Y0 Y1 : ℕ}, 2 ≤ Y0 → Y0 < Y1 →
      ∀ {T : ℝ}, 5 ≤ T →
        regularizedTwoScaleCarlsonFactorDiskZeroMass Y0 Y1 T ≤
          Real.log (C * (Y1 : ℝ) ^ 2 * (T + 14) ^ 10) /
            Real.log ((31 / 8 : ℝ) / (123 / 32 : ℝ)) := by
  rcases
      exists_regularizedTwoScaleCarlsonFactorDiskZeroMass_le_logPolynomial with
    ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro Y0 Y1 hY0 hY01 T hT
  apply hbound (le_trans (by norm_num) hY0) hY01 hT
  apply norm_twoScaleMollifiedZetaError_le_one_div_three_of_four_le_re
    hY0 hY01
  simp

/-- The complete divisor mass computed on the factorization disk itself. -/
noncomputable def regularizedTwoScaleCarlsonInnerFactorDiskZeroMass
    (Y0 Y1 : ℕ) (T : ℝ) : ℝ :=
  ∑ᶠ u,
    (MeromorphicOn.divisor
      (regularizedTwoScaleCarlsonZeroDetector Y0 Y1)
      (Metric.closedBall
        ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ)) u : ℝ)

/-- Distinct zeros of the regularized two-scale detector in the fixed
factorization disk.  Multiplicity remains recorded by the divisor. -/
noncomputable def regularizedTwoScaleCarlsonFactorDiskZeroSupport
    (Y0 Y1 : ℕ) (T : ℝ) : Finset ℂ :=
  ((MeromorphicOn.divisor
      (regularizedTwoScaleCarlsonZeroDetector Y0 Y1)
      (Metric.closedBall
        ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ))).finiteSupport
    (isCompact_closedBall
      ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ))).toFinset

private theorem twoScaleFixedJensenFactorDisk_re_pos
    {T : ℝ} {z : ℂ}
    (hz : z ∈ Metric.closedBall
      ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ)) :
    0 < z.re := by
  have hdist :
      ‖z - ((4 : ℂ) + I * (T + 1 / 2))‖ ≤ (123 / 32 : ℝ) := by
    simpa [Metric.mem_closedBall, Complex.dist_eq] using hz
  have hreAbs :=
    Complex.abs_re_le_norm (z - ((4 : ℂ) + I * (T + 1 / 2)))
  have hre : |z.re - 4| ≤ (123 / 32 : ℝ) := by
    simpa using hreAbs.trans hdist
  rw [abs_le] at hre
  linarith

/-- On the factorization disk, finite divisor support is exactly the zero
set of the regularized two-scale detector. -/
theorem mem_regularizedTwoScaleCarlsonFactorDiskZeroSupport_iff_zero
    {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1)
    {T : ℝ} {z : ℂ}
    (hz : z ∈ Metric.closedBall
      ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ)) :
    z ∈ regularizedTwoScaleCarlsonFactorDiskZeroSupport Y0 Y1 T ↔
      regularizedTwoScaleCarlsonZeroDetector Y0 Y1 z = 0 := by
  classical
  let U : Set ℂ := Metric.closedBall
    ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ)
  let detector : ℂ → ℂ :=
    regularizedTwoScaleCarlsonZeroDetector Y0 Y1
  let D := MeromorphicOn.divisor detector U
  have hanalytic : AnalyticOnNhd ℂ detector U := by
    apply
      (analyticOnNhd_regularizedTwoScaleCarlsonZeroDetector_fixedJensenOuterDisk
        Y0 Y1 T).mono
    exact Metric.closedBall_subset_closedBall (by norm_num [U])
  have hzre : 0 < z.re := twoScaleFixedJensenFactorDisk_re_pos hz
  have horder : analyticOrderAt detector z ≠ ⊤ := by
    dsimp [detector]
    exact analyticOrderAt_regularizedTwoScaleCarlsonZeroDetector_ne_top
      hY0 hY01 hzre
  have hdivisor : D z = (analyticOrderNatAt detector z : ℤ) := by
    rw [MeromorphicOn.divisor_apply hanalytic.meromorphicOn
        (by simpa [U] using hz),
      (hanalytic z (by simpa [U] using hz)).meromorphicOrderAt_eq]
    have hcast := Nat.cast_analyticOrderNatAt horder
    rw [← hcast]
    simp
  have hzAnalytic : AnalyticAt ℂ detector z :=
    hanalytic z (by simpa [U] using hz)
  have hnatCast := Nat.cast_analyticOrderNatAt horder
  rw [regularizedTwoScaleCarlsonFactorDiskZeroSupport]
  rw [(D.finiteSupport (isCompact_closedBall
    ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ))).mem_toFinset]
  simp only [Function.mem_support]
  rw [show MeromorphicOn.divisor
      (regularizedTwoScaleCarlsonZeroDetector Y0 Y1)
      (Metric.closedBall
        ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ)) z = D z by rfl,
    hdivisor, Int.ofNat_ne_zero]
  constructor
  · intro hnat
    apply hzAnalytic.analyticOrderAt_ne_zero.mp
    intro hzero
    have hcastZero : (analyticOrderNatAt detector z : ℕ∞) = 0 :=
      hnatCast.trans hzero
    exact hnat (by simpa using hcastZero)
  · intro hzero hnatZero
    have horderZero : analyticOrderAt detector z = 0 := by
      rw [← hnatCast, hnatZero]
      rfl
    exact (hzAnalytic.analyticOrderAt_eq_zero.mp horderZero) hzero

/-- Imaginary parts of the distinct two-scale detector zeros in the fixed
factorization disk. -/
noncomputable def regularizedTwoScaleCarlsonFactorDiskZeroHeights
    (Y0 Y1 : ℕ) (T : ℝ) : Finset ℝ :=
  (regularizedTwoScaleCarlsonFactorDiskZeroSupport Y0 Y1 T).image Complex.im

/-- Pigeonhole separation available for a horizontal line through a
unit-height Carlson rectangle. -/
noncomputable def regularizedTwoScaleCarlsonFactorHorizontalSeparation
    (Y0 Y1 : ℕ) (T : ℝ) : ℝ :=
  1 / (4 *
    (((regularizedTwoScaleCarlsonFactorDiskZeroHeights Y0 Y1 T).card : ℝ) + 1))

/-- Quantitative radial separation supplied by the fixed good-circle
interval. -/
noncomputable def regularizedTwoScaleCarlsonFactorDiskSeparation
    (Y0 Y1 : ℕ) (T : ℝ) : ℝ :=
  ((122 / 32 : ℝ) - 121 / 32) /
    (4 * ((((regularizedTwoScaleCarlsonFactorDiskZeroSupport Y0 Y1 T).image
      (dist ((4 : ℂ) + I * (T + 1 / 2)))).card : ℝ) + 1))

/-- Logarithmic norm majorant for the extracted nonzero factor on its
selected good circle. -/
noncomputable def regularizedTwoScaleCarlsonFactorCircleLogUpper
    (C : ℝ) (Y0 Y1 : ℕ) (T : ℝ) : ℝ :=
  Real.log (C * (Y1 : ℝ) ^ 2 * (T + 14) ^ 10) -
    Real.log (regularizedTwoScaleCarlsonFactorDiskSeparation Y0 Y1 T) *
      regularizedTwoScaleCarlsonInnerFactorDiskZeroMass Y0 Y1 T

/-- Center lower bound for the same extracted nonzero factor. -/
noncomputable def regularizedTwoScaleCarlsonFactorCenterLogLower
    (Y0 Y1 : ℕ) (T : ℝ) : ℝ :=
  -Real.log (123 / 32 : ℝ) *
    regularizedTwoScaleCarlsonInnerFactorDiskZeroMass Y0 Y1 T

/-- A divisor-mass bound controls the number of distinct zero heights and
hence the horizontal pigeonhole separation. -/
theorem regularizedTwoScaleCarlsonFactorHorizontalSeparation_lower_of_mass_le
    {Y0 Y1 : ℕ} {T L : ℝ}
    (hmass : regularizedTwoScaleCarlsonInnerFactorDiskZeroMass Y0 Y1 T ≤ L) :
    0 < 1 / (4 * (L + 1)) ∧
      1 / (4 * (L + 1)) ≤
        regularizedTwoScaleCarlsonFactorHorizontalSeparation Y0 Y1 T := by
  classical
  let c : ℂ := (4 : ℂ) + I * (T + 1 / 2)
  let b : ℝ := 123 / 32
  let detector : ℂ → ℂ :=
    regularizedTwoScaleCarlsonZeroDetector Y0 Y1
  let D := MeromorphicOn.divisor detector (Metric.closedBall c b)
  let zeros := regularizedTwoScaleCarlsonFactorDiskZeroSupport Y0 Y1 T
  let heights := regularizedTwoScaleCarlsonFactorDiskZeroHeights Y0 Y1 T
  have hanalytic : AnalyticOnNhd ℂ detector (Metric.closedBall c b) := by
    apply
      (analyticOnNhd_regularizedTwoScaleCarlsonZeroDetector_fixedJensenOuterDisk
        Y0 Y1 T).mono
    exact Metric.closedBall_subset_closedBall (by norm_num [b])
  have hDnonneg : 0 ≤ D := hanalytic.divisor_nonneg
  have hmassNonneg :
      0 ≤ regularizedTwoScaleCarlsonInnerFactorDiskZeroMass Y0 Y1 T := by
    change 0 ≤ ∑ᶠ u, (D u : ℝ)
    apply finsum_nonneg
    intro u
    exact_mod_cast hDnonneg u
  have hLnonneg : 0 ≤ L := hmassNonneg.trans hmass
  have hsupportMass : (zeros.card : ℝ) ≤
      regularizedTwoScaleCarlsonInnerFactorDiskZeroMass Y0 Y1 T := by
    have h := card_divisor_support_le_finsum_mass hanalytic
    simpa [zeros, D, detector, c, b,
      regularizedTwoScaleCarlsonFactorDiskZeroSupport,
      regularizedTwoScaleCarlsonInnerFactorDiskZeroMass] using h
  have hheightNat : heights.card ≤ zeros.card := by
    dsimp [heights, regularizedTwoScaleCarlsonFactorDiskZeroHeights]
    exact Finset.card_image_le
  have hheightMass : (heights.card : ℝ) ≤
      regularizedTwoScaleCarlsonInnerFactorDiskZeroMass Y0 Y1 T := by
    have hheightReal : (heights.card : ℝ) ≤ (zeros.card : ℝ) := by
      exact_mod_cast hheightNat
    exact hheightReal.trans hsupportMass
  have hheightL : (heights.card : ℝ) ≤ L := hheightMass.trans hmass
  have hsmallDenPos : 0 < 4 * ((heights.card : ℝ) + 1) := by positivity
  have hlargeDenPos : 0 < 4 * (L + 1) := by positivity
  have hdenLe : 4 * ((heights.card : ℝ) + 1) ≤ 4 * (L + 1) := by
    nlinarith
  have hrecip : 1 / (4 * (L + 1)) ≤
      1 / (4 * ((heights.card : ℝ) + 1)) :=
    one_div_le_one_div_of_le hsmallDenPos hdenLe
  refine ⟨one_div_pos.mpr hlargeDenPos, ?_⟩
  simpa [regularizedTwoScaleCarlsonFactorHorizontalSeparation, heights] using hrecip

/-- A circle strictly inside the factorization disk avoids every two-scale
detector zero there, with quantitative separation from its finite support. -/
theorem exists_regularizedTwoScaleCarlsonZeroDetector_goodFactorCircle
    {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1) {T : ℝ} :
    ∃ r : ℝ,
      0 < r ∧ r ∈ Set.Icc (121 / 32 : ℝ) (122 / 32 : ℝ) ∧
      (∀ z ∈ Metric.sphere
          ((4 : ℂ) + I * (T + 1 / 2)) r,
        ∀ rho ∈ regularizedTwoScaleCarlsonFactorDiskZeroSupport Y0 Y1 T,
          ((122 / 32 : ℝ) - 121 / 32) /
              (4 * ((((regularizedTwoScaleCarlsonFactorDiskZeroSupport
                Y0 Y1 T).image
                (dist ((4 : ℂ) + I * (T + 1 / 2)))).card : ℝ) + 1)) ≤
            dist z rho) ∧
      (∀ z ∈ Metric.sphere
          ((4 : ℂ) + I * (T + 1 / 2)) r,
        z ∈ Metric.closedBall
          ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ)) ∧
      ∀ z ∈ Metric.sphere
          ((4 : ℂ) + I * (T + 1 / 2)) r,
        regularizedTwoScaleCarlsonZeroDetector Y0 Y1 z ≠ 0 := by
  let c : ℂ := (4 : ℂ) + I * (T + 1 / 2)
  let zeros := regularizedTwoScaleCarlsonFactorDiskZeroSupport Y0 Y1 T
  have hcover : ∀ z ∈ Metric.closedBall c (123 / 32 : ℝ),
      regularizedTwoScaleCarlsonZeroDetector Y0 Y1 z = 0 → z ∈ zeros := by
    intro z hz hzero
    exact (mem_regularizedTwoScaleCarlsonFactorDiskZeroSupport_iff_zero
      hY0 hY01 (by simpa [c] using hz)).2 hzero
  simpa [c, zeros] using
    (PrimeNumberTheorem.exists_good_radius_avoiding_covered_finset_zeros
      (f := regularizedTwoScaleCarlsonZeroDetector Y0 Y1) zeros c
      (by norm_num : (0 : ℝ) < 121 / 32)
      (by norm_num : (121 / 32 : ℝ) < 122 / 32)
      (by norm_num : (122 / 32 : ℝ) < 123 / 32) hcover)

/-- One zero-avoiding circle and one extracted factor simultaneously carry
the center lower bound, boundary logarithmic growth, and a logarithmic-
derivative bound throughout the disk containing Carlson's unit rectangle. -/
theorem exists_regularizedTwoScaleCarlsonZeroDetector_goodFactor_logDeriv_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {Y0 Y1 : ℕ}, 2 ≤ Y0 → Y0 < Y1 →
      ∀ {T : ℝ}, 5 ≤ T →
      ∃ r : ℝ, ∃ g : ℂ → ℂ,
        r ∈ Set.Icc (121 / 32 : ℝ) (122 / 32 : ℝ) ∧
        AnalyticOnNhd ℂ g
          (Metric.closedBall
            ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ)) ∧
        (∀ u : (Metric.closedBall
            ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ) : Set ℂ),
          g u ≠ 0) ∧
        regularizedTwoScaleCarlsonFactorCenterLogLower Y0 Y1 T ≤
          Real.log ‖g ((4 : ℂ) + I * (T + 1 / 2))‖ ∧
        (∀ z ∈ Metric.sphere
            ((4 : ℂ) + I * (T + 1 / 2)) r,
          Real.log ‖g z‖ ≤
            regularizedTwoScaleCarlsonFactorCircleLogUpper C Y0 Y1 T) ∧
        (∀ z ∈ Metric.ball
            ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ),
          regularizedTwoScaleCarlsonZeroDetector Y0 Y1 z ≠ 0 →
            logDeriv (regularizedTwoScaleCarlsonZeroDetector Y0 Y1) z =
              (∑ᶠ u,
                (MeromorphicOn.divisor
                  (regularizedTwoScaleCarlsonZeroDetector Y0 Y1)
                  (Metric.closedBall
                    ((4 : ℂ) + I * (T + 1 / 2))
                    (123 / 32 : ℝ)) u : ℂ) * (z - u)⁻¹) +
                logDeriv g z) ∧
        ∀ z ∈ Metric.closedBall
            ((4 : ℂ) + I * (T + 1 / 2)) (15 / 4 : ℝ),
          ‖logDeriv g z‖ ≤
            4 * max
                (regularizedTwoScaleCarlsonFactorCircleLogUpper C Y0 Y1 T -
                  regularizedTwoScaleCarlsonFactorCenterLogLower Y0 Y1 T) 1 *
              (r + 15 / 4) / (r - 15 / 4) ^ 2 := by
  rcases
      exists_norm_regularizedTwoScaleCarlsonZeroDetector_le_fixedJensenSphere with
    ⟨C, hC, hsphereOuter⟩
  refine ⟨C, hC, ?_⟩
  intro Y0 Y1 hY0 hY01 T hT
  let c : ℂ := (4 : ℂ) + I * (T + 1 / 2)
  let b : ℝ := 123 / 32
  let R : ℝ := 31 / 8
  let detector : ℂ → ℂ :=
    regularizedTwoScaleCarlsonZeroDetector Y0 Y1
  let M : ℝ := C * (Y1 : ℝ) ^ 2 * (T + 14) ^ 10
  let D := MeromorphicOn.divisor detector (Metric.closedBall c b)
  let zeros := regularizedTwoScaleCarlsonFactorDiskZeroSupport Y0 Y1 T
  let delta := regularizedTwoScaleCarlsonFactorDiskSeparation Y0 Y1 T
  have hY0one : 1 ≤ Y0 := le_trans (by norm_num) hY0
  have hY1 : 1 ≤ Y1 := hY0one.trans hY01.le
  have hY1Real : 1 ≤ (Y1 : ℝ) := by exact_mod_cast hY1
  have hY1Pow : 1 ≤ (Y1 : ℝ) ^ 2 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hY1Real 2
  have hTBase : 1 ≤ T + 14 := by linarith
  have hTPow : 1 ≤ (T + 14) ^ 10 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hTBase 10
  have hCY : 1 ≤ C * (Y1 : ℝ) ^ 2 := by
    simpa using mul_le_mul hC hY1Pow (by norm_num) (by linarith)
  have hM : 1 ≤ M := by
    dsimp [M]
    simpa using mul_le_mul hCY hTPow (by norm_num)
      (mul_nonneg (by linarith) (by positivity))
  have hanalyticOuter : AnalyticOnNhd ℂ detector
      (Metric.closedBall c R) := by
    simpa [detector, c, R] using
      analyticOnNhd_regularizedTwoScaleCarlsonZeroDetector_fixedJensenOuterDisk
        Y0 Y1 T
  have hdiffOuter : DiffContOnCl ℂ detector (Metric.ball c R) :=
    hanalyticOuter.differentiableOn.diffContOnCl_ball subset_rfl
  have hclosedNorm : ∀ z ∈ Metric.closedBall c R, ‖detector z‖ ≤ M := by
    intro z hz
    apply Complex.norm_le_of_forall_mem_frontier_norm_le
      Metric.isBounded_ball hdiffOuter
    · intro u hu
      have huSphere : u ∈ Metric.sphere c R :=
        Metric.frontier_ball_subset_sphere hu
      simpa [detector, c, R, M] using
        hsphereOuter hY0one hY01 hT (by simpa [c, R] using huSphere)
    · rw [closure_ball c (by norm_num [R] : R ≠ 0)]
      exact hz
  rcases
      exists_regularizedTwoScaleCarlsonZeroDetector_goodFactorCircle
        hY0 hY01 (T := T) with
    ⟨r, hrpos, hrange, hsep, hsphereFactor, hsphereNe⟩
  have hrb : r < b := by
    dsimp [b]
    linarith [hrange.2]
  have hbR : b ≤ R := by norm_num [b, R]
  have hanalyticFactor : AnalyticOnNhd ℂ detector
      (Metric.closedBall c b) :=
    hanalyticOuter.mono (Metric.closedBall_subset_closedBall hbR)
  have hnotop : ∀ u : (Metric.closedBall c b : Set ℂ),
      meromorphicOrderAt detector u ≠ ⊤ := by
    intro u
    rw [(hanalyticFactor u u.property).meromorphicOrderAt_eq]
    intro htop
    apply analyticOrderAt_regularizedTwoScaleCarlsonZeroDetector_ne_top
      hY0 hY01 (twoScaleFixedJensenFactorDisk_re_pos u.property)
    exact ENat.map_eq_top_iff.mp htop
  rcases
      exists_analytic_nonzero_factor_log_norm_logDeriv_pointwise_of_ne_zero
      (f := detector) (c := c) (r := r) (R := b)
      hrb hanalyticFactor hnotop with
    ⟨g, hg, hgne, hfactor, hld⟩
  have hDfinite : D.support.Finite := by
    exact D.finiteSupport (isCompact_closedBall c b)
  have hDnonneg : 0 ≤ D := hanalyticFactor.divisor_nonneg
  have hcenterNorm : 1 ≤ ‖detector c‖ := by
    dsimp [detector]
    apply one_le_norm_regularizedTwoScaleCarlsonZeroDetector_of_four_le_re
    · simp [c]
    · apply norm_twoScaleMollifiedZetaError_le_one_div_three_of_four_le_re
        hY0 hY01
      simp [c]
  have hcenterNe : detector c ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hcenterNorm
    norm_num at hcenterNorm
  have hcenterEq := hfactor c (by simp [hrpos.le]) hcenterNe
  have hcenterSum :=
    finsum_divisor_mul_log_norm_center_sub_le_log_mul_mass
      (f := detector) (c := c) (b := b)
      (by norm_num [b]) hanalyticFactor hcenterNe
  have hcenterF : 0 ≤ Real.log ‖detector c‖ :=
    Real.log_nonneg hcenterNorm
  have hcenterG :
      regularizedTwoScaleCarlsonFactorCenterLogLower Y0 Y1 T ≤
        Real.log ‖g c‖ := by
    change -Real.log b * (∑ᶠ u, (D u : ℝ)) ≤ Real.log ‖g c‖
    simpa [D, detector, c, b,
      regularizedTwoScaleCarlsonInnerFactorDiskZeroMass] using
      (show -Real.log b * (∑ᶠ u, (D u : ℝ)) ≤ Real.log ‖g c‖ by
        linarith)
  have hdelta : 0 < delta := by
    dsimp [delta, regularizedTwoScaleCarlsonFactorDiskSeparation, zeros, c]
    positivity
  have hsphereG : ∀ z ∈ Metric.sphere c r,
      Real.log ‖g z‖ ≤
        regularizedTwoScaleCarlsonFactorCircleLogUpper C Y0 Y1 T := by
    intro z hz
    have hzFactor : z ∈ Metric.closedBall c b :=
      hsphereFactor z (by simpa [c] using hz)
    have hzOuter : z ∈ Metric.closedBall c R :=
      Metric.closedBall_subset_closedBall hbR hzFactor
    have hfz : detector z ≠ 0 := by
      dsimp [detector]
      exact hsphereNe z (by simpa [c] using hz)
    have hfactorZ := hfactor z
      (Metric.sphere_subset_closedBall (by simpa [c] using hz)) hfz
    have hsepSupport : ∀ u ∈ D.support, delta ≤ ‖z - u‖ := by
      intro u hu
      have huZeros : u ∈ zeros := by
        dsimp [zeros, regularizedTwoScaleCarlsonFactorDiskZeroSupport]
        exact hDfinite.mem_toFinset.mpr hu
      have h := hsep z (by simpa [c] using hz) u
        (by simpa [zeros] using huZeros)
      simpa [delta, regularizedTwoScaleCarlsonFactorDiskSeparation, c,
        Complex.dist_eq] using h
    have hsumLower :=
      ZeroFreeRegion.log_mul_finsum_le_finsum_mul_log_norm_sub_of_finiteSupport
        hDfinite (fun u => hDnonneg u) hdelta hsepSupport
    have hlogF : Real.log ‖detector z‖ ≤ Real.log M :=
      Real.log_le_log (norm_pos_iff.mpr hfz) (hclosedNorm z hzOuter)
    change Real.log ‖g z‖ ≤
      Real.log M - Real.log delta * (∑ᶠ u, (D u : ℝ))
    simpa [D, detector, c, M, delta,
      regularizedTwoScaleCarlsonFactorCircleLogUpper,
      regularizedTwoScaleCarlsonInnerFactorDiskZeroMass] using
      (show Real.log ‖g z‖ ≤
          Real.log M - Real.log delta * (∑ᶠ u, (D u : ℝ)) by
        linarith)
  have hgCircle : AnalyticOnNhd ℂ g (Metric.closedBall c r) :=
    hg.mono (Metric.closedBall_subset_closedBall hrb.le)
  have hgneCircle : ∀ z ∈ Metric.closedBall c r, g z ≠ 0 := by
    intro z hz
    exact hgne ⟨z, Metric.closedBall_subset_closedBall hrb.le hz⟩
  have hdR : (15 / 4 : ℝ) < r := by linarith [hrange.1]
  have hlogDeriv : ∀ z ∈ Metric.closedBall c (15 / 4 : ℝ),
      ‖logDeriv g z‖ ≤
        4 * max
            (regularizedTwoScaleCarlsonFactorCircleLogUpper C Y0 Y1 T -
              regularizedTwoScaleCarlsonFactorCenterLogLower Y0 Y1 T) 1 *
          (r + 15 / 4) / (r - 15 / 4) ^ 2 := by
    intro z hz
    exact
      ZeroFreeRegion.norm_logDeriv_le_four_mul_max_sub_mul_add_div_sq_of_sphere_log_norm_le_of_center_lower
        hrpos (by norm_num) hdR hgCircle hgneCircle hcenterG hsphereG hz
  refine ⟨r, g, hrange, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [c, b] using hg
  · simpa [c, b] using hgne
  · simpa [c] using hcenterG
  · intro z hz
    exact hsphereG z (by simpa [c] using hz)
  · intro z hz hfz
    exact hld z (by simpa [detector, c, b] using hz) (by simpa [detector] using hfz)
  · intro z hz
    exact hlogDeriv z (by simpa [c] using hz)

/-- One horizontal side of the unit Carlson rectangle avoids every zero in
the fixed factorization disk.  On that side, the detector logarithmic
derivative is bounded by the extracted factor plus its complete principal
part. -/
theorem exists_regularizedTwoScaleCarlson_horizontal_logDeriv_le_factorDisk :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {Y0 Y1 : ℕ}, 2 ≤ Y0 → Y0 < Y1 →
      ∀ {sigma T : ℝ}, 1 / 2 < sigma → 5 ≤ T →
        ∃ r ∈ Set.Icc (121 / 32 : ℝ) (122 / 32 : ℝ),
        ∃ t ∈ Set.Icc T (T + 1),
          (∀ x ∈ Set.Icc sigma 4,
            regularizedTwoScaleCarlsonZeroDetector Y0 Y1
              ((x : ℂ) + (t : ℂ) * I) ≠ 0) ∧
          ∀ x ∈ Set.Icc sigma 4,
            ‖logDeriv (regularizedTwoScaleCarlsonZeroDetector Y0 Y1)
              ((x : ℂ) + (t : ℂ) * I)‖ ≤
              4 * max
                  (regularizedTwoScaleCarlsonFactorCircleLogUpper C Y0 Y1 T -
                    regularizedTwoScaleCarlsonFactorCenterLogLower Y0 Y1 T) 1 *
                (r + 15 / 4) / (r - 15 / 4) ^ 2 +
              regularizedTwoScaleCarlsonInnerFactorDiskZeroMass Y0 Y1 T /
                regularizedTwoScaleCarlsonFactorHorizontalSeparation Y0 Y1 T := by
  classical
  rcases
      exists_regularizedTwoScaleCarlsonZeroDetector_goodFactor_logDeriv_le with
    ⟨C, hC, hfactor⟩
  refine ⟨C, hC, ?_⟩
  intro Y0 Y1 hY0 hY01 sigma T hsigma hT
  rcases hfactor hY0 hY01 hT with
    ⟨r, g, hr, hg, hgne, hcenter, hsphere, hdecomp, hgBound⟩
  let c : ℂ := (4 : ℂ) + I * (T + 1 / 2)
  let U : Set ℂ := Metric.closedBall c (123 / 32 : ℝ)
  let detector : ℂ → ℂ :=
    regularizedTwoScaleCarlsonZeroDetector Y0 Y1
  let D := MeromorphicOn.divisor detector U
  let H := regularizedTwoScaleCarlsonFactorDiskZeroHeights Y0 Y1 T
  let delta := regularizedTwoScaleCarlsonFactorHorizontalSeparation Y0 Y1 T
  rcases ZeroFreeRegion.exists_radius_separated_from_finset H
      (show T < T + 1 by linarith) with ⟨t, ht, hsep⟩
  have hdelta : 0 < delta := by
    dsimp [delta, regularizedTwoScaleCarlsonFactorHorizontalSeparation]
    positivity
  have hanalyticFactor : AnalyticOnNhd ℂ detector U := by
    simpa [detector, U, c] using
      (analyticOnNhd_regularizedTwoScaleCarlsonZeroDetector_fixedJensenOuterDisk
        Y0 Y1 T).mono
        (Metric.closedBall_subset_closedBall (by norm_num))
  have hDfinite : D.support.Finite := by
    exact D.finiteSupport
      (by simpa [U] using isCompact_closedBall c (123 / 32 : ℝ))
  have hDnonneg : 0 ≤ D := hanalyticFactor.divisor_nonneg
  refine ⟨r, hr, t, ht, ?_, ?_⟩
  · intro x hx
    let z : ℂ := (x : ℂ) + (t : ℂ) * I
    have hzRectangle : z ∈ carlsonDetectorRectangle sigma 4 T (T + 1) := by
      change z.re ∈ Set.Icc sigma 4 ∧ z.im ∈ Set.Icc T (T + 1)
      constructor
      · simpa [z] using hx
      · simpa [z] using ht
    have hzInner : z ∈ Metric.closedBall c (15 / 4 : ℝ) := by
      simpa [c] using
        (carlsonDetectorRectangle_subset_fixedJensenInnerDisk
          hsigma hzRectangle)
    have hzFactor : z ∈ U := by
      dsimp [U]
      exact Metric.closedBall_subset_closedBall (by norm_num) hzInner
    intro hzero
    have hzSupport :
        z ∈ regularizedTwoScaleCarlsonFactorDiskZeroSupport Y0 Y1 T :=
      (mem_regularizedTwoScaleCarlsonFactorDiskZeroSupport_iff_zero
        hY0 hY01 (by simpa [U, c] using hzFactor)).2 hzero
    have hzHeight : z.im ∈ H := by
      dsimp [H, regularizedTwoScaleCarlsonFactorDiskZeroHeights]
      exact Finset.mem_image.mpr ⟨z, hzSupport, rfl⟩
    have hzeroDistance : delta ≤ 0 := by
      simpa [z, delta,
        regularizedTwoScaleCarlsonFactorHorizontalSeparation, H] using
        hsep z.im hzHeight
    exact (not_lt_of_ge hzeroDistance) hdelta
  · intro x hx
    let z : ℂ := (x : ℂ) + (t : ℂ) * I
    have hzRectangle : z ∈ carlsonDetectorRectangle sigma 4 T (T + 1) := by
      change z.re ∈ Set.Icc sigma 4 ∧ z.im ∈ Set.Icc T (T + 1)
      constructor
      · simpa [z] using hx
      · simpa [z] using ht
    have hzInner : z ∈ Metric.closedBall c (15 / 4 : ℝ) := by
      simpa [c] using
        (carlsonDetectorRectangle_subset_fixedJensenInnerDisk
          hsigma hzRectangle)
    have hzFactor : z ∈ U := by
      dsimp [U]
      exact Metric.closedBall_subset_closedBall (by norm_num) hzInner
    have hzFactorBall : z ∈ Metric.ball c (123 / 32 : ℝ) :=
      Metric.closedBall_subset_ball (by norm_num) hzInner
    have hzNe : detector z ≠ 0 := by
      intro hzero
      have hzSupport :
          z ∈ regularizedTwoScaleCarlsonFactorDiskZeroSupport Y0 Y1 T :=
        (mem_regularizedTwoScaleCarlsonFactorDiskZeroSupport_iff_zero
          hY0 hY01 (by simpa [U, c] using hzFactor)).2
          (by simpa [detector] using hzero)
      have hzHeight : z.im ∈ H := by
        dsimp [H, regularizedTwoScaleCarlsonFactorDiskZeroHeights]
        exact Finset.mem_image.mpr ⟨z, hzSupport, rfl⟩
      have hzeroDistance : delta ≤ 0 := by
        simpa [z, delta,
          regularizedTwoScaleCarlsonFactorHorizontalSeparation, H] using
          hsep z.im hzHeight
      exact (not_lt_of_ge hzeroDistance) hdelta
    have hprincipal :
        ‖∑ᶠ u, (D u : ℂ) * (z - u)⁻¹‖ ≤
          regularizedTwoScaleCarlsonInnerFactorDiskZeroMass Y0 Y1 T /
            delta := by
      have hbound := ZeroFreeRegion.norm_finsum_divisor_mul_inv_le_mass_div
        hDfinite (fun u => hDnonneg u) hdelta (by
          intro u hu
          have huSupport :
              u ∈ regularizedTwoScaleCarlsonFactorDiskZeroSupport Y0 Y1 T := by
            dsimp [regularizedTwoScaleCarlsonFactorDiskZeroSupport]
            exact hDfinite.mem_toFinset.mpr hu
          have huHeight : u.im ∈ H := by
            dsimp [H, regularizedTwoScaleCarlsonFactorDiskZeroHeights]
            exact Finset.mem_image.mpr ⟨u, huSupport, rfl⟩
          have hheight : delta ≤ |t - u.im| := by
            simpa [delta,
              regularizedTwoScaleCarlsonFactorHorizontalSeparation, H] using
              hsep u.im huHeight
          have him : |(z - u).im| ≤ ‖z - u‖ :=
            Complex.abs_im_le_norm (z - u)
          have hrewrite : |(z - u).im| = |t - u.im| := by simp [z]
          rw [hrewrite] at him
          exact hheight.trans him)
      simpa [D, detector, U, c,
        regularizedTwoScaleCarlsonInnerFactorDiskZeroMass] using hbound
    have hsplit := hdecomp z (by simpa [c] using hzFactorBall)
      (by simpa [detector] using hzNe)
    have hgAt := hgBound z (by simpa [c] using hzInner)
    rw [show logDeriv detector z =
        (∑ᶠ u, (D u : ℂ) * (z - u)⁻¹) + logDeriv g z by
      simpa [detector, D, U, c] using hsplit]
    calc
      ‖(∑ᶠ u, (D u : ℂ) * (z - u)⁻¹) + logDeriv g z‖ ≤
          ‖∑ᶠ u, (D u : ℂ) * (z - u)⁻¹‖ + ‖logDeriv g z‖ :=
        norm_add_le _ _
      _ ≤ regularizedTwoScaleCarlsonInnerFactorDiskZeroMass Y0 Y1 T /
            delta +
          4 * max
              (regularizedTwoScaleCarlsonFactorCircleLogUpper C Y0 Y1 T -
                regularizedTwoScaleCarlsonFactorCenterLogLower Y0 Y1 T) 1 *
            (r + 15 / 4) / (r - 15 / 4) ^ 2 :=
        add_le_add hprincipal hgAt
      _ = 4 * max
              (regularizedTwoScaleCarlsonFactorCircleLogUpper C Y0 Y1 T -
                regularizedTwoScaleCarlsonFactorCenterLogLower Y0 Y1 T) 1 *
            (r + 15 / 4) / (r - 15 / 4) ^ 2 +
          regularizedTwoScaleCarlsonInnerFactorDiskZeroMass Y0 Y1 T /
            regularizedTwoScaleCarlsonFactorHorizontalSeparation Y0 Y1 T := by
        rw [add_comm]

/-- Divisor locality identifies the inner-disk factorization mass with the
outer Jensen divisor restricted to that same disk. -/
theorem regularizedTwoScaleCarlsonInnerFactorDiskZeroMass_eq :
    regularizedTwoScaleCarlsonInnerFactorDiskZeroMass Y0 Y1 T =
      regularizedTwoScaleCarlsonFactorDiskZeroMass Y0 Y1 T := by
  let c : ℂ := (4 : ℂ) + I * (T + 1 / 2)
  have hanalytic :=
    analyticOnNhd_regularizedTwoScaleCarlsonZeroDetector_fixedJensenOuterDisk
      Y0 Y1 T
  have hlocal := finsum_divisor_closedBall_eq_finsum_mem_of_le
    (f := regularizedTwoScaleCarlsonZeroDetector Y0 Y1)
    (c := c) (b := (123 / 32 : ℝ)) (R := (31 / 8 : ℝ))
    (by norm_num) hanalytic.meromorphicOn
  simpa [regularizedTwoScaleCarlsonInnerFactorDiskZeroMass,
    regularizedTwoScaleCarlsonFactorDiskZeroMass, c] using hlocal

/-- Hence the complete inner factorization divisor mass inherits the
unconditional Jensen logarithmic majorant. -/
theorem exists_regularizedTwoScaleCarlsonInnerFactorDiskZeroMass_le_logPolynomial :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {Y0 Y1 : ℕ}, 2 ≤ Y0 → Y0 < Y1 →
      ∀ {T : ℝ}, 5 ≤ T →
        regularizedTwoScaleCarlsonInnerFactorDiskZeroMass Y0 Y1 T ≤
          Real.log (C * (Y1 : ℝ) ^ 2 * (T + 14) ^ 10) /
            Real.log ((31 / 8 : ℝ) / (123 / 32 : ℝ)) := by
  rcases
      exists_regularizedTwoScaleCarlsonFactorDiskZeroMass_le_logPolynomial_of_two_le_inner with
    ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro Y0 Y1 hY0 hY01 T hT
  rw [regularizedTwoScaleCarlsonInnerFactorDiskZeroMass_eq]
  exact hbound hY0 hY01 hT

/-- All two-scale detector zeros in the inner disk can be extracted into a
finite divisor factor.  The remaining analytic factor is nonvanishing and
has the divisor-mass center lower bound needed by Borel--Caratheodory. -/
theorem exists_regularizedTwoScaleCarlsonZeroDetector_fixedJensenFactor_center_lower
    {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1) {T : ℝ} :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g
        (Metric.closedBall
          ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ)) ∧
      (∀ u : (Metric.closedBall
          ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ) : Set ℂ),
        g u ≠ 0) ∧
      -Real.log (123 / 32 : ℝ) *
          regularizedTwoScaleCarlsonInnerFactorDiskZeroMass Y0 Y1 T ≤
        Real.log ‖g ((4 : ℂ) + I * (T + 1 / 2))‖ := by
  let c : ℂ := (4 : ℂ) + I * (T + 1 / 2)
  let b : ℝ := 123 / 32
  let detector : ℂ → ℂ :=
    regularizedTwoScaleCarlsonZeroDetector Y0 Y1
  have hanalytic : AnalyticOnNhd ℂ detector
      (Metric.closedBall c b) := by
    apply
      (analyticOnNhd_regularizedTwoScaleCarlsonZeroDetector_fixedJensenOuterDisk
        Y0 Y1 T).mono
    exact Metric.closedBall_subset_closedBall (by norm_num [b])
  have hcenterNorm : 1 ≤ ‖detector c‖ := by
    dsimp [detector]
    apply one_le_norm_regularizedTwoScaleCarlsonZeroDetector_of_four_le_re
    · simp [c]
    · apply norm_twoScaleMollifiedZetaError_le_one_div_three_of_four_le_re
        hY0 hY01
      simp [c]
  have hcenter : detector c ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hcenterNorm
    norm_num at hcenterNorm
  have hnotop : ∀ u : (Metric.closedBall c b : Set ℂ),
      meromorphicOrderAt detector u ≠ ⊤ := by
    intro u
    have hdist : ‖(u : ℂ) - c‖ ≤ b := by
      have hdist' : dist (u : ℂ) c ≤ b :=
        Metric.mem_closedBall.mp u.property
      simpa [Complex.dist_eq] using hdist'
    have hreAbs := Complex.abs_re_le_norm ((u : ℂ) - c)
    have hre : 0 < (u : ℂ).re := by
      have habs : |(u : ℂ).re - 4| ≤ b := by
        simpa [c] using hreAbs.trans hdist
      rw [abs_le] at habs
      dsimp [b] at habs
      linarith
    rw [(hanalytic u u.property).meromorphicOrderAt_eq]
    intro htop
    apply analyticOrderAt_regularizedTwoScaleCarlsonZeroDetector_ne_top
      hY0 hY01 hre
    exact ENat.map_eq_top_iff.mp htop
  rcases exists_analytic_nonzero_factor_log_norm_at_center
      (f := detector) (c := c) (R := b)
      (by norm_num [b]) hanalytic hnotop hcenter with
    ⟨g, hg, hgne, hfactor⟩
  have hsum := finsum_divisor_mul_log_norm_center_sub_le_log_mul_mass
    (f := detector) (c := c) (b := b)
    (by norm_num [b]) hanalytic hcenter
  have hcenterLog : 0 ≤ Real.log ‖detector c‖ :=
    Real.log_nonneg hcenterNorm
  refine ⟨g, by simpa [c, b] using hg, by simpa [c, b] using hgne, ?_⟩
  dsimp [regularizedTwoScaleCarlsonInnerFactorDiskZeroMass,
    detector, c, b] at hfactor hsum hcenterLog ⊢
  linarith

/-- Jensen logarithmic majorant for the complete two-scale detector divisor
mass on the factorization disk. -/
noncomputable def regularizedTwoScaleCarlsonFactorZeroLogMajorant
    (C : ℝ) (Y0 Y1 : ℕ) (T : ℝ) : ℝ :=
  Real.log (C * (Y1 : ℝ) ^ 2 * (T + 14) ^ 10) /
    Real.log ((31 / 8 : ℝ) / (123 / 32 : ℝ))

/-- Explicit upper bound for the logarithmic variation of the extracted
factor, assuming `L` bounds the complete inner divisor mass. -/
noncomputable def regularizedTwoScaleCarlsonFactorLogVariationMajorant
    (C : ℝ) (Y0 Y1 : ℕ) (T L : ℝ) : ℝ :=
  Real.log (C * (Y1 : ℝ) ^ 2 * (T + 14) ^ 10) +
    (-Real.log (1 / (128 * (L + 1))) +
      Real.log (123 / 32 : ℝ)) * L

/-- A mass upper bound gives a concrete lower bound for the radial
good-circle separation. -/
theorem regularizedTwoScaleCarlsonFactorDiskSeparation_lower_of_mass_le
    {Y0 Y1 : ℕ} {T L : ℝ}
    (hmass : regularizedTwoScaleCarlsonInnerFactorDiskZeroMass Y0 Y1 T ≤ L) :
    0 < 1 / (128 * (L + 1)) ∧
      1 / (128 * (L + 1)) ≤
        regularizedTwoScaleCarlsonFactorDiskSeparation Y0 Y1 T := by
  classical
  let c : ℂ := (4 : ℂ) + I * (T + 1 / 2)
  let b : ℝ := 123 / 32
  let detector : ℂ → ℂ :=
    regularizedTwoScaleCarlsonZeroDetector Y0 Y1
  let D := MeromorphicOn.divisor detector (Metric.closedBall c b)
  let zeros := regularizedTwoScaleCarlsonFactorDiskZeroSupport Y0 Y1 T
  let radialCard : ℝ := (((zeros.image (dist c)).card : ℕ) : ℝ)
  have hanalytic : AnalyticOnNhd ℂ detector (Metric.closedBall c b) := by
    apply
      (analyticOnNhd_regularizedTwoScaleCarlsonZeroDetector_fixedJensenOuterDisk
        Y0 Y1 T).mono
    exact Metric.closedBall_subset_closedBall (by norm_num [b])
  have hDnonneg : 0 ≤ D := hanalytic.divisor_nonneg
  have hmassNonneg :
      0 ≤ regularizedTwoScaleCarlsonInnerFactorDiskZeroMass Y0 Y1 T := by
    change 0 ≤ ∑ᶠ u, (D u : ℝ)
    apply finsum_nonneg
    intro u
    exact_mod_cast hDnonneg u
  have hLnonneg : 0 ≤ L := hmassNonneg.trans hmass
  have hsupportMass : (zeros.card : ℝ) ≤
      regularizedTwoScaleCarlsonInnerFactorDiskZeroMass Y0 Y1 T := by
    have h := card_divisor_support_le_finsum_mass hanalytic
    simpa [zeros, D, detector, c, b,
      regularizedTwoScaleCarlsonFactorDiskZeroSupport,
      regularizedTwoScaleCarlsonInnerFactorDiskZeroMass] using h
  have hradialNat : (zeros.image (dist c)).card ≤ zeros.card :=
    Finset.card_image_le
  have hradialSupport : radialCard ≤ (zeros.card : ℝ) := by
    dsimp [radialCard]
    exact_mod_cast hradialNat
  have hradialL : radialCard ≤ L :=
    hradialSupport.trans (hsupportMass.trans hmass)
  have hsmallDenPos : 0 < 128 * (radialCard + 1) := by positivity
  have hlargeDenPos : 0 < 128 * (L + 1) := by positivity
  have hdenLe : 128 * (radialCard + 1) ≤ 128 * (L + 1) := by
    nlinarith
  have hrecip : 1 / (128 * (L + 1)) ≤
      1 / (128 * (radialCard + 1)) :=
    one_div_le_one_div_of_le hsmallDenPos hdenLe
  have hsepEq :
      regularizedTwoScaleCarlsonFactorDiskSeparation Y0 Y1 T =
        1 / (128 * (radialCard + 1)) := by
    dsimp only [regularizedTwoScaleCarlsonFactorDiskSeparation, zeros, c]
    change ((122 / 32 : ℝ) - 121 / 32) /
        (4 * (radialCard + 1)) = 1 / (128 * (radialCard + 1))
    have hk : radialCard + 1 ≠ 0 := ne_of_gt (by positivity)
    field_simp [hk]
    ring
  refine ⟨one_div_pos.mpr hlargeDenPos, ?_⟩
  rw [hsepEq]
  exact hrecip

/-- Replacing the actual divisor mass and radial separation by a common mass
majorant gives a fully explicit logarithmic-variation bound. -/
theorem regularizedTwoScaleCarlsonFactorLogVariation_le_of_mass_le
    {C T L : ℝ} {Y0 Y1 : ℕ}
    (hmass : regularizedTwoScaleCarlsonInnerFactorDiskZeroMass Y0 Y1 T ≤ L) :
    regularizedTwoScaleCarlsonFactorCircleLogUpper C Y0 Y1 T -
        regularizedTwoScaleCarlsonFactorCenterLogLower Y0 Y1 T ≤
      regularizedTwoScaleCarlsonFactorLogVariationMajorant C Y0 Y1 T L := by
  let m := regularizedTwoScaleCarlsonInnerFactorDiskZeroMass Y0 Y1 T
  let sep := regularizedTwoScaleCarlsonFactorDiskSeparation Y0 Y1 T
  let delta : ℝ := 1 / (128 * (L + 1))
  have hsep :=
    regularizedTwoScaleCarlsonFactorDiskSeparation_lower_of_mass_le hmass
  have hmNonneg : 0 ≤ m := by
    let c : ℂ := (4 : ℂ) + I * (T + 1 / 2)
    let b : ℝ := 123 / 32
    let detector : ℂ → ℂ :=
      regularizedTwoScaleCarlsonZeroDetector Y0 Y1
    let D := MeromorphicOn.divisor detector (Metric.closedBall c b)
    have hanalytic : AnalyticOnNhd ℂ detector
        (Metric.closedBall c b) := by
      apply
        (analyticOnNhd_regularizedTwoScaleCarlsonZeroDetector_fixedJensenOuterDisk
          Y0 Y1 T).mono
      exact Metric.closedBall_subset_closedBall (by norm_num [b])
    have hDnonneg : 0 ≤ D := hanalytic.divisor_nonneg
    change 0 ≤ ∑ᶠ u, (D u : ℝ)
    apply finsum_nonneg
    intro u
    exact_mod_cast hDnonneg u
  have hLNonneg : 0 ≤ L := hmNonneg.trans hmass
  have hdeltaPos : 0 < delta := by simpa [delta] using hsep.1
  have hdeltaSep : delta ≤ sep := by simpa [delta, sep] using hsep.2
  have hlogDeltaSep : Real.log delta ≤ Real.log sep :=
    Real.log_le_log hdeltaPos hdeltaSep
  have hdeltaLeOne : delta ≤ 1 := by
    dsimp [delta]
    have hden : 1 ≤ 128 * (L + 1) := by nlinarith
    calc
      1 / (128 * (L + 1)) ≤ 1 / 1 :=
        one_div_le_one_div_of_le (by norm_num) hden
      _ = 1 := by norm_num
  have hlogDeltaNonpos : Real.log delta ≤ 0 :=
    Real.log_nonpos hdeltaPos.le hdeltaLeOne
  have hlogBNonneg : 0 ≤ Real.log (123 / 32 : ℝ) :=
    Real.log_nonneg (by norm_num)
  have hcoeffLe :
      -Real.log sep + Real.log (123 / 32 : ℝ) ≤
        -Real.log delta + Real.log (123 / 32 : ℝ) := by
    linarith
  have hcoeffNonneg :
      0 ≤ -Real.log delta + Real.log (123 / 32 : ℝ) := by
    linarith
  have hweighted :
      (-Real.log sep + Real.log (123 / 32 : ℝ)) * m ≤
        (-Real.log delta + Real.log (123 / 32 : ℝ)) * L := by
    exact (mul_le_mul_of_nonneg_right hcoeffLe hmNonneg).trans
      (mul_le_mul_of_nonneg_left hmass hcoeffNonneg)
  dsimp [regularizedTwoScaleCarlsonFactorCircleLogUpper,
    regularizedTwoScaleCarlsonFactorCenterLogLower,
    regularizedTwoScaleCarlsonFactorLogVariationMajorant,
    m, sep, delta]
  linarith

/-- The horizontal estimate with the principal part expressed using any
available upper bound for the complete inner divisor mass. -/
theorem
    exists_regularizedTwoScaleCarlson_horizontal_logDeriv_le_of_factorDiskMass_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {Y0 Y1 : ℕ}, 2 ≤ Y0 → Y0 < Y1 →
      ∀ {sigma T L : ℝ}, 1 / 2 < sigma → 5 ≤ T →
        regularizedTwoScaleCarlsonInnerFactorDiskZeroMass Y0 Y1 T ≤ L →
        ∃ r ∈ Set.Icc (121 / 32 : ℝ) (122 / 32 : ℝ),
        ∃ t ∈ Set.Icc T (T + 1),
          (∀ x ∈ Set.Icc sigma 4,
            regularizedTwoScaleCarlsonZeroDetector Y0 Y1
              ((x : ℂ) + (t : ℂ) * I) ≠ 0) ∧
          ∀ x ∈ Set.Icc sigma 4,
            ‖logDeriv (regularizedTwoScaleCarlsonZeroDetector Y0 Y1)
              ((x : ℂ) + (t : ℂ) * I)‖ ≤
              4 * max
                  (regularizedTwoScaleCarlsonFactorCircleLogUpper C Y0 Y1 T -
                    regularizedTwoScaleCarlsonFactorCenterLogLower Y0 Y1 T) 1 *
                (r + 15 / 4) / (r - 15 / 4) ^ 2 +
              L / (1 / (4 * (L + 1))) := by
  rcases
      exists_regularizedTwoScaleCarlson_horizontal_logDeriv_le_factorDisk with
    ⟨C, hC, hhorizontal⟩
  refine ⟨C, hC, ?_⟩
  intro Y0 Y1 hY0 hY01 sigma T L hsigma hT hmass
  rcases hhorizontal hY0 hY01 hsigma hT with
    ⟨r, hr, t, ht, hne, hbound⟩
  have hsep :=
    regularizedTwoScaleCarlsonFactorHorizontalSeparation_lower_of_mass_le hmass
  have hmassNonneg :
      0 ≤ regularizedTwoScaleCarlsonInnerFactorDiskZeroMass Y0 Y1 T := by
    let c : ℂ := (4 : ℂ) + I * (T + 1 / 2)
    let b : ℝ := 123 / 32
    let detector : ℂ → ℂ :=
      regularizedTwoScaleCarlsonZeroDetector Y0 Y1
    let D := MeromorphicOn.divisor detector (Metric.closedBall c b)
    have hanalytic : AnalyticOnNhd ℂ detector
        (Metric.closedBall c b) := by
      apply
        (analyticOnNhd_regularizedTwoScaleCarlsonZeroDetector_fixedJensenOuterDisk
          Y0 Y1 T).mono
      exact Metric.closedBall_subset_closedBall (by norm_num [b])
    have hDnonneg : 0 ≤ D := hanalytic.divisor_nonneg
    change 0 ≤ ∑ᶠ u, (D u : ℝ)
    apply finsum_nonneg
    intro u
    exact_mod_cast hDnonneg u
  have hprincipal :
      regularizedTwoScaleCarlsonInnerFactorDiskZeroMass Y0 Y1 T /
          regularizedTwoScaleCarlsonFactorHorizontalSeparation Y0 Y1 T ≤
        L / (1 / (4 * (L + 1))) := by
    calc
      regularizedTwoScaleCarlsonInnerFactorDiskZeroMass Y0 Y1 T /
          regularizedTwoScaleCarlsonFactorHorizontalSeparation Y0 Y1 T ≤
          regularizedTwoScaleCarlsonInnerFactorDiskZeroMass Y0 Y1 T /
            (1 / (4 * (L + 1))) :=
        div_le_div_of_nonneg_left hmassNonneg hsep.1 hsep.2
      _ ≤ L / (1 / (4 * (L + 1))) :=
        div_le_div_of_nonneg_right hmass hsep.1.le
  refine ⟨r, hr, t, ht, hne, ?_⟩
  intro x hx
  exact (hbound x hx).trans (add_le_add_right hprincipal _)

/-- The horizontal bound with both factor variation and principal part
expressed only through an assumed divisor-mass majorant. -/
theorem
    exists_regularizedTwoScaleCarlson_horizontal_logDeriv_le_of_factorDiskMass_le_explicit :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {Y0 Y1 : ℕ}, 2 ≤ Y0 → Y0 < Y1 →
      ∀ {sigma T L : ℝ}, 1 / 2 < sigma → 5 ≤ T →
        regularizedTwoScaleCarlsonInnerFactorDiskZeroMass Y0 Y1 T ≤ L →
        ∃ r ∈ Set.Icc (121 / 32 : ℝ) (122 / 32 : ℝ),
        ∃ t ∈ Set.Icc T (T + 1),
          (∀ x ∈ Set.Icc sigma 4,
            regularizedTwoScaleCarlsonZeroDetector Y0 Y1
              ((x : ℂ) + (t : ℂ) * I) ≠ 0) ∧
          ∀ x ∈ Set.Icc sigma 4,
            ‖logDeriv (regularizedTwoScaleCarlsonZeroDetector Y0 Y1)
              ((x : ℂ) + (t : ℂ) * I)‖ ≤
              4 * max
                  (regularizedTwoScaleCarlsonFactorLogVariationMajorant
                    C Y0 Y1 T L) 1 *
                (r + 15 / 4) / (r - 15 / 4) ^ 2 +
              L / (1 / (4 * (L + 1))) := by
  rcases
      exists_regularizedTwoScaleCarlson_horizontal_logDeriv_le_of_factorDiskMass_le with
    ⟨C, hC, hhorizontal⟩
  refine ⟨C, hC, ?_⟩
  intro Y0 Y1 hY0 hY01 sigma T L hsigma hT hmass
  rcases hhorizontal hY0 hY01 hsigma hT hmass with
    ⟨r, hr, t, ht, hne, hbound⟩
  have hvariation :=
    regularizedTwoScaleCarlsonFactorLogVariation_le_of_mass_le
      (C := C) hmass
  have hgapPos : 0 < r - 15 / 4 := by linarith [hr.1]
  have hregular :
      4 * max
          (regularizedTwoScaleCarlsonFactorCircleLogUpper C Y0 Y1 T -
            regularizedTwoScaleCarlsonFactorCenterLogLower Y0 Y1 T) 1 *
          (r + 15 / 4) / (r - 15 / 4) ^ 2 ≤
        4 * max
          (regularizedTwoScaleCarlsonFactorLogVariationMajorant
            C Y0 Y1 T L) 1 *
          (r + 15 / 4) / (r - 15 / 4) ^ 2 := by
    have hmax := max_le_max_right (1 : ℝ) hvariation
    have hnum : 0 ≤ r + 15 / 4 := by linarith [hr.1]
    have hinv : 0 ≤ ((r - 15 / 4) ^ 2)⁻¹ := by positivity
    have hfour := mul_le_mul_of_nonneg_left hmax (by norm_num : (0 : ℝ) ≤ 4)
    have hnumerator := mul_le_mul_of_nonneg_right hfour hnum
    simpa [div_eq_mul_inv] using
      (mul_le_mul_of_nonneg_right hnumerator hinv)
  refine ⟨r, hr, t, ht, hne, ?_⟩
  intro x hx
  exact (hbound x hx).trans (add_le_add_left hregular _)

/-- Completely zero-data-independent horizontal logarithmic-derivative
bound obtained by substituting the unconditional Jensen mass majorant. -/
theorem exists_regularizedTwoScaleCarlson_horizontal_logDeriv_le_logPolynomial :
    ∃ C₁ C₂ : ℝ, 1 ≤ C₁ ∧ 1 ≤ C₂ ∧
      ∀ {Y0 Y1 : ℕ}, 2 ≤ Y0 → Y0 < Y1 →
      ∀ {sigma T : ℝ}, 1 / 2 < sigma → 5 ≤ T →
        ∃ r ∈ Set.Icc (121 / 32 : ℝ) (122 / 32 : ℝ),
        ∃ t ∈ Set.Icc T (T + 1),
          (∀ x ∈ Set.Icc sigma 4,
            regularizedTwoScaleCarlsonZeroDetector Y0 Y1
              ((x : ℂ) + (t : ℂ) * I) ≠ 0) ∧
          ∀ x ∈ Set.Icc sigma 4,
            ‖logDeriv (regularizedTwoScaleCarlsonZeroDetector Y0 Y1)
              ((x : ℂ) + (t : ℂ) * I)‖ ≤
              4 * max
                  (regularizedTwoScaleCarlsonFactorLogVariationMajorant
                    C₁ Y0 Y1 T
                    (regularizedTwoScaleCarlsonFactorZeroLogMajorant
                      C₂ Y0 Y1 T)) 1 *
                (r + 15 / 4) / (r - 15 / 4) ^ 2 +
              regularizedTwoScaleCarlsonFactorZeroLogMajorant C₂ Y0 Y1 T /
                (1 / (4 *
                  (regularizedTwoScaleCarlsonFactorZeroLogMajorant
                    C₂ Y0 Y1 T + 1))) := by
  rcases
      exists_regularizedTwoScaleCarlson_horizontal_logDeriv_le_of_factorDiskMass_le_explicit with
    ⟨C₁, hC₁, hhorizontal⟩
  rcases
      exists_regularizedTwoScaleCarlsonInnerFactorDiskZeroMass_le_logPolynomial with
    ⟨C₂, hC₂, hmass⟩
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro Y0 Y1 hY0 hY01 sigma T hsigma hT
  apply hhorizontal hY0 hY01 hsigma hT
  simpa [regularizedTwoScaleCarlsonFactorZeroLogMajorant] using
    hmass hY0 hY01 hT

end CarlsonZeroDensity
end PrimeNumberTheorem
