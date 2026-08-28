import PrimeNumberTheorem.CarlsonGaussianDetectorCovering

/-!
# Reduction of the Carlson critical boundary to Conrey's two linear mollifiers

This file contains no long-mollifier mean-square theorem.  It proves the
exact elementary reduction showing that the only remaining critical-boundary
input is a local Gaussian second moment for each of the two standard linear
Selberg mollifiers appearing in the plateau--taper decomposition.
-/

open Complex Set MeasureTheory

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- Coefficient of the outer linear Selberg mollifier. -/
noncomputable def conreyOuterMultiplier (Y0 Y1 : ℕ) : ℝ :=
  Real.log Y1 / Real.log ((Y1 : ℝ) / (Y0 : ℝ))

/-- Coefficient of the inner linear Selberg mollifier. -/
noncomputable def conreyInnerMultiplier (Y0 Y1 : ℕ) : ℝ :=
  Real.log Y0 / Real.log ((Y1 : ℝ) / (Y0 : ℝ))

/-- The two real multipliers differ by exactly one. -/
theorem conreyOuterMultiplier_sub_innerMultiplier_eq_one
    {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1) :
    conreyOuterMultiplier Y0 Y1 - conreyInnerMultiplier Y0 Y1 = 1 := by
  have h := HardyTheorem.twoScaleSelbergWeight_eq_linear_combination
    (Y0 := Y0) (Y1 := Y1) (n := 1) hY0 hY01 (by omega) (by omega)
  have h1Y0 : 1 ≤ Y0 := by omega
  simp [HardyTheorem.twoScaleSelbergWeight, h1Y0,
    HardyTheorem.linearLogSelbergWeight] at h
  simpa [conreyOuterMultiplier, conreyInnerMultiplier] using h.symm

/-- Error associated with one standard linearly tapered Selberg mollifier. -/
noncomputable def linearLogSelbergMollifiedZetaError
    (Y : ℕ) (s : ℂ) : ℂ :=
  riemannZeta s * HardyTheorem.linearLogSelbergMollifier Y s - 1

/-- Exact decomposition of the plateau--taper error into the two standard
linear Selberg errors to which Conrey's theorem applies. -/
theorem twoScaleMollifiedZetaError_eq_conrey_linear_combination
    {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1) (s : ℂ) :
    twoScaleMollifiedZetaError Y0 Y1 s =
      (conreyOuterMultiplier Y0 Y1 : ℂ) *
          linearLogSelbergMollifiedZetaError Y1 s -
        (conreyInnerMultiplier Y0 Y1 : ℂ) *
          linearLogSelbergMollifiedZetaError Y0 s := by
  have hAB := conreyOuterMultiplier_sub_innerMultiplier_eq_one hY0 hY01
  have hABc :
      (conreyOuterMultiplier Y0 Y1 : ℂ) -
          (conreyInnerMultiplier Y0 Y1 : ℂ) = 1 := by
    exact_mod_cast hAB
  rw [twoScaleMollifiedZetaError,
    HardyTheorem.twoScaleSelbergMollifier_eq_linear_combination hY0 hY01]
  unfold linearLogSelbergMollifiedZetaError
  dsimp [conreyOuterMultiplier, conreyInnerMultiplier] at hABc ⊢
  push_cast at hABc ⊢
  linear_combination hABc

/-- Pointwise squared-norm form of the two-component reduction. -/
theorem norm_sq_twoScaleMollifiedZetaError_le_conrey_components
    {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1) (s : ℂ) :
    ‖twoScaleMollifiedZetaError Y0 Y1 s‖ ^ 2 ≤
      2 * conreyOuterMultiplier Y0 Y1 ^ 2 *
          ‖linearLogSelbergMollifiedZetaError Y1 s‖ ^ 2 +
        2 * conreyInnerMultiplier Y0 Y1 ^ 2 *
          ‖linearLogSelbergMollifiedZetaError Y0 s‖ ^ 2 := by
  rw [twoScaleMollifiedZetaError_eq_conrey_linear_combination hY0 hY01]
  have htri := norm_sub_le
    ((conreyOuterMultiplier Y0 Y1 : ℂ) *
      linearLogSelbergMollifiedZetaError Y1 s)
    ((conreyInnerMultiplier Y0 Y1 : ℂ) *
      linearLogSelbergMollifiedZetaError Y0 s)
  have htriSq :
      ‖(conreyOuterMultiplier Y0 Y1 : ℂ) *
          linearLogSelbergMollifiedZetaError Y1 s -
        (conreyInnerMultiplier Y0 Y1 : ℂ) *
          linearLogSelbergMollifiedZetaError Y0 s‖ ^ 2 ≤
      (‖(conreyOuterMultiplier Y0 Y1 : ℂ) *
          linearLogSelbergMollifiedZetaError Y1 s‖ +
        ‖(conreyInnerMultiplier Y0 Y1 : ℂ) *
          linearLogSelbergMollifiedZetaError Y0 s‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 htri
  have hsq :
      ‖(conreyOuterMultiplier Y0 Y1 : ℂ) *
          linearLogSelbergMollifiedZetaError Y1 s -
        (conreyInnerMultiplier Y0 Y1 : ℂ) *
          linearLogSelbergMollifiedZetaError Y0 s‖ ^ 2 ≤
      2 * ‖(conreyOuterMultiplier Y0 Y1 : ℂ) *
          linearLogSelbergMollifiedZetaError Y1 s‖ ^ 2 +
        2 * ‖(conreyInnerMultiplier Y0 Y1 : ℂ) *
          linearLogSelbergMollifiedZetaError Y0 s‖ ^ 2 := by
    calc
      _ ≤ (‖(conreyOuterMultiplier Y0 Y1 : ℂ) *
            linearLogSelbergMollifiedZetaError Y1 s‖ +
          ‖(conreyInnerMultiplier Y0 Y1 : ℂ) *
            linearLogSelbergMollifiedZetaError Y0 s‖) ^ 2 := htriSq
      _ ≤ _ := by
        nlinarith [sq_nonneg
          (‖(conreyOuterMultiplier Y0 Y1 : ℂ) *
              linearLogSelbergMollifiedZetaError Y1 s‖ -
            ‖(conreyInnerMultiplier Y0 Y1 : ℂ) *
              linearLogSelbergMollifiedZetaError Y0 s‖)]
  calc
    _ ≤ 2 * ‖(conreyOuterMultiplier Y0 Y1 : ℂ) *
          linearLogSelbergMollifiedZetaError Y1 s‖ ^ 2 +
        2 * ‖(conreyInnerMultiplier Y0 Y1 : ℂ) *
          linearLogSelbergMollifiedZetaError Y0 s‖ ^ 2 := hsq
    _ = _ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [mul_pow, mul_pow, sq_abs, sq_abs]
      ring

/-- The one-scale linearly tapered mollified error is analytic away from the
zeta pole. -/
theorem analyticAt_linearLogSelbergMollifiedZetaError_of_ne_one
    (Y : ℕ) {s : ℂ} (hs1 : s ≠ 1) :
    AnalyticAt ℂ (linearLogSelbergMollifiedZetaError Y) s := by
  have hzeta : AnalyticAt ℂ riemannZeta s :=
    ZeroFreeRegion.analyticOnNhd_riemannZeta_ne_one s hs1
  have hm : AnalyticAt ℂ (HardyTheorem.linearLogSelbergMollifier Y) s := by
    unfold HardyTheorem.linearLogSelbergMollifier
    apply Finset.analyticAt_fun_sum
    intro n hn
    have hn0 : (n : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hn).1)
    have hpow : AnalyticAt ℂ (fun z : ℂ => (n : ℂ) ^ z) s :=
      (differentiable_id.const_cpow (.inl hn0)).analyticAt s
    exact analyticAt_const.mul
      (analyticAt_const.div hpow
        (Complex.cpow_ne_zero_iff.mpr (.inl hn0)))
  unfold linearLogSelbergMollifiedZetaError
  exact (hzeta.mul hm).sub analyticAt_const

/-- Continuity of a one-scale linearly tapered mollified error on the
critical vertical line. -/
theorem continuous_linearLogSelbergMollifiedZetaError_vertical_half
    (Y : ℕ) :
    Continuous fun t : ℝ => linearLogSelbergMollifiedZetaError Y
      (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ)) := by
  rw [continuous_iff_continuousAt]
  intro t
  let point : ℝ → ℂ := fun u => ((1 / 2 : ℝ) : ℂ) + I * (u : ℂ)
  have hpoint : ContinuousAt point t := by
    dsimp [point]
    fun_prop
  have hs1 : point t ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [point] at hre
  have hanalytic :=
    analyticAt_linearLogSelbergMollifiedZetaError_of_ne_one Y hs1
  simpa [point, Function.comp_def] using hanalytic.continuousAt.comp hpoint

/-- Gaussian integrability of the two-scale error follows from Gaussian
integrability of its two one-scale components. -/
theorem integrable_gaussian_norm_sq_twoScaleMollifiedZetaError_half_of_components
    {Delta w : ℝ} {Y0 Y1 : ℕ}
    (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1)
    (hInt0 : Integrable fun t : ℝ => carlsonGaussianWeight Delta w t *
      ‖linearLogSelbergMollifiedZetaError Y0
        (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2)
    (hInt1 : Integrable fun t : ℝ => carlsonGaussianWeight Delta w t *
      ‖linearLogSelbergMollifiedZetaError Y1
        (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2) :
    Integrable fun t : ℝ => carlsonGaussianWeight Delta w t *
      ‖twoScaleMollifiedZetaError Y0 Y1
        (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2 := by
  let major : ℝ → ℝ := fun t =>
    2 * conreyOuterMultiplier Y0 Y1 ^ 2 *
        (carlsonGaussianWeight Delta w t *
          ‖linearLogSelbergMollifiedZetaError Y1
            (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2) +
      2 * conreyInnerMultiplier Y0 Y1 ^ 2 *
        (carlsonGaussianWeight Delta w t *
          ‖linearLogSelbergMollifiedZetaError Y0
            (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2)
  have hmajorInt : Integrable major :=
    (hInt1.const_mul (2 * conreyOuterMultiplier Y0 Y1 ^ 2)).add
      (hInt0.const_mul (2 * conreyInnerMultiplier Y0 Y1 ^ 2))
  have hcont : Continuous fun t : ℝ => carlsonGaussianWeight Delta w t *
      ‖twoScaleMollifiedZetaError Y0 Y1
        (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2 := by
    exact (by
      unfold carlsonGaussianWeight
      fun_prop : Continuous (carlsonGaussianWeight Delta w)).mul
      ((by
        rw [continuous_iff_continuousAt]
        intro t
        let point : ℝ → ℂ := fun u => ((1 / 2 : ℝ) : ℂ) + I * (u : ℂ)
        have hpoint : ContinuousAt point t := by dsimp [point]; fun_prop
        have hs1 : point t ≠ 1 := by
          intro h
          have hre := congrArg Complex.re h
          norm_num [point] at hre
        simpa [point, Function.comp_def] using
          (analyticAt_twoScaleMollifiedZetaError_of_ne_one Y0 Y1 hs1).continuousAt.comp hpoint
        : Continuous fun t : ℝ => twoScaleMollifiedZetaError Y0 Y1
          (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))).norm.pow 2)
  apply Integrable.mono_nonneg hmajorInt hcont.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t =>
      mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  · exact Filter.Eventually.of_forall fun t => by
      have hw : 0 ≤ carlsonGaussianWeight Delta w t := (Real.exp_pos _).le
      have hpoint := norm_sq_twoScaleMollifiedZetaError_le_conrey_components
        hY0 hY01 (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))
      dsimp [major]
      calc
        carlsonGaussianWeight Delta w t *
              ‖twoScaleMollifiedZetaError Y0 Y1
                (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2
            ≤ carlsonGaussianWeight Delta w t *
                (2 * conreyOuterMultiplier Y0 Y1 ^ 2 *
                    ‖linearLogSelbergMollifiedZetaError Y1
                      (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2 +
                  2 * conreyInnerMultiplier Y0 Y1 ^ 2 *
                    ‖linearLogSelbergMollifiedZetaError Y0
                      (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hpoint hw
        _ = _ := by ring

/-- Integral version of the exact two-component reduction. -/
theorem integral_gaussian_norm_sq_twoScaleMollifiedZetaError_half_le_of_components
    {Delta w C0 C1 : ℝ} {Y0 Y1 : ℕ}
    (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1)
    (hInt0 : Integrable fun t : ℝ => carlsonGaussianWeight Delta w t *
      ‖linearLogSelbergMollifiedZetaError Y0
        (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2)
    (hInt1 : Integrable fun t : ℝ => carlsonGaussianWeight Delta w t *
      ‖linearLogSelbergMollifiedZetaError Y1
        (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2)
    (hBound0 : (∫ t : ℝ, carlsonGaussianWeight Delta w t *
      ‖linearLogSelbergMollifiedZetaError Y0
        (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2) ≤ C0)
    (hBound1 : (∫ t : ℝ, carlsonGaussianWeight Delta w t *
      ‖linearLogSelbergMollifiedZetaError Y1
        (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2) ≤ C1) :
    (∫ t : ℝ, carlsonGaussianWeight Delta w t *
      ‖twoScaleMollifiedZetaError Y0 Y1
        (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2) ≤
      2 * conreyOuterMultiplier Y0 Y1 ^ 2 * C1 +
        2 * conreyInnerMultiplier Y0 Y1 ^ 2 * C0 := by
  let f0 : ℝ → ℝ := fun t => carlsonGaussianWeight Delta w t *
    ‖linearLogSelbergMollifiedZetaError Y0
      (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2
  let f1 : ℝ → ℝ := fun t => carlsonGaussianWeight Delta w t *
    ‖linearLogSelbergMollifiedZetaError Y1
      (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2
  let f : ℝ → ℝ := fun t => carlsonGaussianWeight Delta w t *
    ‖twoScaleMollifiedZetaError Y0 Y1
      (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2
  let major : ℝ → ℝ := fun t =>
    2 * conreyOuterMultiplier Y0 Y1 ^ 2 * f1 t +
      2 * conreyInnerMultiplier Y0 Y1 ^ 2 * f0 t
  have hfInt : Integrable f :=
    integrable_gaussian_norm_sq_twoScaleMollifiedZetaError_half_of_components
      hY0 hY01 hInt0 hInt1
  have hmajorInt : Integrable major :=
    (hInt1.const_mul (2 * conreyOuterMultiplier Y0 Y1 ^ 2)).add
      (hInt0.const_mul (2 * conreyInnerMultiplier Y0 Y1 ^ 2))
  have hpoint (t : ℝ) : f t ≤ major t := by
    have hw : 0 ≤ carlsonGaussianWeight Delta w t := (Real.exp_pos _).le
    have h := norm_sq_twoScaleMollifiedZetaError_le_conrey_components
      hY0 hY01 (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))
    dsimp [f, major, f0, f1]
    calc
      carlsonGaussianWeight Delta w t *
            ‖twoScaleMollifiedZetaError Y0 Y1
              (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2
          ≤ carlsonGaussianWeight Delta w t *
              (2 * conreyOuterMultiplier Y0 Y1 ^ 2 *
                  ‖linearLogSelbergMollifiedZetaError Y1
                    (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2 +
                2 * conreyInnerMultiplier Y0 Y1 ^ 2 *
                  ‖linearLogSelbergMollifiedZetaError Y0
                    (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h hw
      _ = _ := by ring
  calc
    (∫ t : ℝ, f t) ≤ ∫ t : ℝ, major t :=
      integral_mono hfInt hmajorInt hpoint
    _ = 2 * conreyOuterMultiplier Y0 Y1 ^ 2 * (∫ t : ℝ, f1 t) +
        2 * conreyInnerMultiplier Y0 Y1 ^ 2 * (∫ t : ℝ, f0 t) := by
      dsimp [major]
      rw [integral_add (hInt1.const_mul _)
        (hInt0.const_mul _), integral_const_mul, integral_const_mul]
    _ ≤ 2 * conreyOuterMultiplier Y0 Y1 ^ 2 * C1 +
        2 * conreyInnerMultiplier Y0 Y1 ^ 2 * C0 := by
      gcongr

/-- The pole-free Gaussian left-boundary norm is controlled by the ordinary
two-scale error Gaussian moment with the exact horizontal exponential factor.
-/
theorem norm_sq_carlsonGaussianPoleFreeLpValue_half_le_error_integral
    {Delta w : ℝ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    (hFInt : Integrable fun t : ℝ => carlsonGaussianWeight Delta w t *
      ‖twoScaleMollifiedZetaError Y0 Y1
        (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2) :
    ‖carlsonGaussianPoleFreeLpValue Delta w Y0 Y1
        hDelta hY0 hY01 ((1 / 2 : ℝ) : ℂ)
          (by norm_num : (((1 / 2 : ℝ) : ℂ).re) ∈ Icc (1 / 2 : ℝ) 4)‖ ^ 2 ≤
      Real.exp ((1 / 2 : ℝ) ^ 2 / Delta ^ 2) *
        ∫ t : ℝ, carlsonGaussianWeight Delta w t *
          ‖twoScaleMollifiedZetaError Y0 Y1
            (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2 := by
  let H : ℂ → ℂ := poleFreeTwoScaleMollifiedZetaError Y0 Y1
  let phi : ℝ → ℂ := carlsonGaussianHilbertSection Delta w H
    ((1 / 2 : ℝ) : ℂ)
  have hmem : MemLp phi 2 volume := by
    exact memLp_carlsonGaussian_poleFreeTwoScaleMollifiedZetaError_on_half_four
      hDelta hY0 hY01
        (by norm_num : (((1 / 2 : ℝ) : ℂ).re) ∈ Icc (1 / 2 : ℝ) 4)
  have hsectionInt : Integrable (fun t => ‖phi t‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hmem.1).mp hmem
  have hmajorInt : Integrable fun t =>
      Real.exp ((1 / 2 : ℝ) ^ 2 / Delta ^ 2) *
        (carlsonGaussianWeight Delta w t *
          ‖twoScaleMollifiedZetaError Y0 Y1
            (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2) :=
    hFInt.const_mul _
  have hpoint (t : ℝ) : ‖phi t‖ ^ 2 ≤
      Real.exp ((1 / 2 : ℝ) ^ 2 / Delta ^ 2) *
        (carlsonGaussianWeight Delta w t *
          ‖twoScaleMollifiedZetaError Y0 Y1
            (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2) := by
    let s : ℂ := ((1 / 2 : ℝ) : ℂ) + I * (t : ℂ)
    have hsre : 0 ≤ s.re := by norm_num [s]
    have hs0 : s ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num [s] at hre
    have hs1 : s ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num [s] at hre
    have hsneg1 : s ≠ -1 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num [s] at hre
    have hH : ‖H s‖ ≤ ‖twoScaleMollifiedZetaError Y0 Y1 s‖ := by
      dsimp [H]
      rw [poleFreeTwoScaleMollifiedZetaError_eq_mul hs0 hs1 hsneg1,
        norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (norm_sub_one_div_add_one_le_one_of_re_nonneg hsre)
    have hHsq := (sq_le_sq₀ (norm_nonneg _)
      (norm_nonneg _)).2 hH
    dsimp [phi]
    rw [norm_sq_carlsonGaussianHilbertSection_real hDelta.ne' H
      (1 / 2 : ℝ) t]
    have hfactorNonneg : 0 ≤
        Real.exp ((1 / 2 : ℝ) ^ 2 / Delta ^ 2) *
          carlsonGaussianWeight Delta w t :=
      mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
    have hmul := mul_le_mul_of_nonneg_left hHsq hfactorNonneg
    simpa [s, mul_assoc] using hmul
  rw [norm_sq_carlsonGaussianPoleFreeLpValue hDelta hY0 hY01]
  calc
    (∫ t : ℝ, ‖phi t‖ ^ 2) ≤
        ∫ t : ℝ, Real.exp ((1 / 2 : ℝ) ^ 2 / Delta ^ 2) *
          (carlsonGaussianWeight Delta w t *
            ‖twoScaleMollifiedZetaError Y0 Y1
              (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2) :=
      integral_mono hsectionInt hmajorInt hpoint
    _ = _ := by rw [integral_const_mul]

/-- Fully elementary constructor: two one-scale Conrey error bounds imply the
critical pole-free Gaussian endpoint bound used by the closed-strip theorem. -/
theorem norm_sq_carlsonGaussianPoleFreeLpValue_half_le_of_conrey_components
    {Delta w C0 C1 : ℝ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1)
    (hInt0 : Integrable fun t : ℝ => carlsonGaussianWeight Delta w t *
      ‖linearLogSelbergMollifiedZetaError Y0
        (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2)
    (hInt1 : Integrable fun t : ℝ => carlsonGaussianWeight Delta w t *
      ‖linearLogSelbergMollifiedZetaError Y1
        (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2)
    (hBound0 : (∫ t : ℝ, carlsonGaussianWeight Delta w t *
      ‖linearLogSelbergMollifiedZetaError Y0
        (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2) ≤ C0)
    (hBound1 : (∫ t : ℝ, carlsonGaussianWeight Delta w t *
      ‖linearLogSelbergMollifiedZetaError Y1
        (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2) ≤ C1) :
    ‖carlsonGaussianPoleFreeLpValue Delta w Y0 Y1
        hDelta (by omega) hY01 ((1 / 2 : ℝ) : ℂ)
          (by norm_num : (((1 / 2 : ℝ) : ℂ).re) ∈ Icc (1 / 2 : ℝ) 4)‖ ^ 2 ≤
      Real.exp ((1 / 2 : ℝ) ^ 2 / Delta ^ 2) *
        (2 * conreyOuterMultiplier Y0 Y1 ^ 2 * C1 +
          2 * conreyInnerMultiplier Y0 Y1 ^ 2 * C0) := by
  have hY0one : 1 ≤ Y0 := by omega
  have hFInt :=
    integrable_gaussian_norm_sq_twoScaleMollifiedZetaError_half_of_components
      hY0 hY01 hInt0 hInt1
  have hleft := norm_sq_carlsonGaussianPoleFreeLpValue_half_le_error_integral
    hDelta hY0one hY01 hFInt
  have hright :=
    integral_gaussian_norm_sq_twoScaleMollifiedZetaError_half_le_of_components
      hY0 hY01 hInt0 hInt1 hBound0 hBound1
  exact hleft.trans (mul_le_mul_of_nonneg_left hright (Real.exp_pos _).le)

/-- Product occurring verbatim in Conrey's local Gaussian mean-square
statement for the standard linear Selberg mollifier. -/
noncomputable def linearLogSelbergMollifiedZetaProduct
    (Y : ℕ) (s : ℂ) : ℂ :=
  riemannZeta s * HardyTheorem.linearLogSelbergMollifier Y s

/-- The error is the Conrey product minus one. -/
theorem linearLogSelbergMollifiedZetaError_eq_product_sub_one
    (Y : ℕ) (s : ℂ) :
    linearLogSelbergMollifiedZetaError Y s =
      linearLogSelbergMollifiedZetaProduct Y s - 1 := by
  rfl

/-- Removing the constant term costs the exact elementary factor two. -/
theorem norm_sq_linearLogSelbergMollifiedZetaError_le_product
    (Y : ℕ) (s : ℂ) :
    ‖linearLogSelbergMollifiedZetaError Y s‖ ^ 2 ≤
      2 * ‖linearLogSelbergMollifiedZetaProduct Y s‖ ^ 2 + 2 := by
  rw [linearLogSelbergMollifiedZetaError_eq_product_sub_one]
  have htri := norm_sub_le (linearLogSelbergMollifiedZetaProduct Y s) 1
  simp only [norm_one] at htri
  have htriSq := (sq_le_sq₀ (norm_nonneg _)
    (add_nonneg (norm_nonneg _) zero_le_one)).2 htri
  calc
    ‖linearLogSelbergMollifiedZetaProduct Y s - 1‖ ^ 2 ≤
        (‖linearLogSelbergMollifiedZetaProduct Y s‖ + 1) ^ 2 := htriSq
    _ ≤ 2 * ‖linearLogSelbergMollifiedZetaProduct Y s‖ ^ 2 + 2 := by
      nlinarith [sq_nonneg
        (‖linearLogSelbergMollifiedZetaProduct Y s‖ - 1)]

/-- Gaussian weights of positive width are integrable. -/
theorem integrable_carlsonGaussianWeight
    {Delta w : ℝ} (hDelta : 0 < Delta) :
    Integrable (carlsonGaussianWeight Delta w) := by
  have hb : 0 < (1 / Delta ^ 2 : ℝ) := by positivity
  have hbase := integrable_exp_neg_mul_sq hb
  have hshift := hbase.comp_sub_right w
  convert hshift using 1
  funext t
  unfold carlsonGaussianWeight
  congr 1
  field_simp [pow_ne_zero 2 hDelta.ne']

/-- A local Gaussian product moment implies integrability of the corresponding
error moment. -/
theorem integrable_gaussian_norm_sq_linearLogSelbergMollifiedZetaError_of_product
    {Delta w : ℝ} {Y : ℕ} (hDelta : 0 < Delta)
    (hProductInt : Integrable fun t : ℝ => carlsonGaussianWeight Delta w t *
      ‖linearLogSelbergMollifiedZetaProduct Y
        (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2) :
    Integrable fun t : ℝ => carlsonGaussianWeight Delta w t *
      ‖linearLogSelbergMollifiedZetaError Y
        (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2 := by
  let productMoment : ℝ → ℝ := fun t =>
    carlsonGaussianWeight Delta w t *
      ‖linearLogSelbergMollifiedZetaProduct Y
        (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2
  let errorMoment : ℝ → ℝ := fun t =>
    carlsonGaussianWeight Delta w t *
      ‖linearLogSelbergMollifiedZetaError Y
        (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2
  let major : ℝ → ℝ := fun t => 2 * productMoment t +
    2 * carlsonGaussianWeight Delta w t
  have hmajorInt : Integrable major :=
    (hProductInt.const_mul 2).add
      ((integrable_carlsonGaussianWeight hDelta).const_mul 2)
  have hcont : Continuous errorMoment := by
    dsimp [errorMoment]
    exact (by
      unfold carlsonGaussianWeight
      fun_prop : Continuous (carlsonGaussianWeight Delta w)).mul
      ((continuous_linearLogSelbergMollifiedZetaError_vertical_half Y).norm.pow 2)
  apply Integrable.mono_nonneg hmajorInt hcont.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t =>
      mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  · exact Filter.Eventually.of_forall fun t => by
      have hw : 0 ≤ carlsonGaussianWeight Delta w t := (Real.exp_pos _).le
      have h := norm_sq_linearLogSelbergMollifiedZetaError_le_product Y
        (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))
      dsimp [errorMoment, major, productMoment]
      calc
        carlsonGaussianWeight Delta w t *
              ‖linearLogSelbergMollifiedZetaError Y
                (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2
            ≤ carlsonGaussianWeight Delta w t *
                (2 * ‖linearLogSelbergMollifiedZetaProduct Y
                  (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2 + 2) :=
          mul_le_mul_of_nonneg_left h hw
        _ = _ := by ring

/-- Exact local conversion from Conrey's product moment to the corresponding
error moment, including the full Gaussian mass of the constant term. -/
theorem integral_gaussian_norm_sq_linearLogSelbergMollifiedZetaError_le_of_product
    {Delta w C : ℝ} {Y : ℕ} (hDelta : 0 < Delta)
    (hProductInt : Integrable fun t : ℝ => carlsonGaussianWeight Delta w t *
      ‖linearLogSelbergMollifiedZetaProduct Y
        (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2)
    (hProductBound : (∫ t : ℝ, carlsonGaussianWeight Delta w t *
      ‖linearLogSelbergMollifiedZetaProduct Y
        (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2) ≤ C) :
    (∫ t : ℝ, carlsonGaussianWeight Delta w t *
      ‖linearLogSelbergMollifiedZetaError Y
        (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2) ≤
      2 * C + 2 * Real.sqrt (Real.pi / (1 / Delta ^ 2)) := by
  let productMoment : ℝ → ℝ := fun t =>
    carlsonGaussianWeight Delta w t *
      ‖linearLogSelbergMollifiedZetaProduct Y
        (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2
  let errorMoment : ℝ → ℝ := fun t =>
    carlsonGaussianWeight Delta w t *
      ‖linearLogSelbergMollifiedZetaError Y
        (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2
  let major : ℝ → ℝ := fun t => 2 * productMoment t +
    2 * carlsonGaussianWeight Delta w t
  have herrorInt : Integrable errorMoment :=
    integrable_gaussian_norm_sq_linearLogSelbergMollifiedZetaError_of_product
      hDelta hProductInt
  have hmajorInt : Integrable major :=
    (hProductInt.const_mul 2).add
      ((integrable_carlsonGaussianWeight hDelta).const_mul 2)
  have hpoint (t : ℝ) : errorMoment t ≤ major t := by
    have hw : 0 ≤ carlsonGaussianWeight Delta w t := (Real.exp_pos _).le
    have h := norm_sq_linearLogSelbergMollifiedZetaError_le_product Y
      (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))
    dsimp [errorMoment, major, productMoment]
    calc
      carlsonGaussianWeight Delta w t *
            ‖linearLogSelbergMollifiedZetaError Y
              (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2
          ≤ carlsonGaussianWeight Delta w t *
              (2 * ‖linearLogSelbergMollifiedZetaProduct Y
                (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2 + 2) :=
        mul_le_mul_of_nonneg_left h hw
      _ = _ := by ring
  calc
    (∫ t : ℝ, errorMoment t) ≤ ∫ t : ℝ, major t :=
      integral_mono herrorInt hmajorInt hpoint
    _ = 2 * (∫ t : ℝ, productMoment t) +
        2 * (∫ t : ℝ, carlsonGaussianWeight Delta w t) := by
      dsimp [major]
      rw [integral_add (hProductInt.const_mul 2)
        ((integrable_carlsonGaussianWeight hDelta).const_mul 2),
        integral_const_mul, integral_const_mul]
    _ ≤ 2 * C + 2 * (∫ t : ℝ, carlsonGaussianWeight Delta w t) := by
      gcongr
    _ = 2 * C + 2 * Real.sqrt (Real.pi / (1 / Delta ^ 2)) := by
      rw [integral_carlsonGaussianWeight hDelta]

/-- Constructor stated with Conrey's original product moments.  Everything
after the two product hypotheses is now proved inside Lean. -/
theorem norm_sq_carlsonGaussianPoleFreeLpValue_half_le_of_conrey_product_components
    {Delta w C0 C1 : ℝ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1)
    (hProductInt0 : Integrable fun t : ℝ => carlsonGaussianWeight Delta w t *
      ‖linearLogSelbergMollifiedZetaProduct Y0
        (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2)
    (hProductInt1 : Integrable fun t : ℝ => carlsonGaussianWeight Delta w t *
      ‖linearLogSelbergMollifiedZetaProduct Y1
        (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2)
    (hProductBound0 : (∫ t : ℝ, carlsonGaussianWeight Delta w t *
      ‖linearLogSelbergMollifiedZetaProduct Y0
        (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2) ≤ C0)
    (hProductBound1 : (∫ t : ℝ, carlsonGaussianWeight Delta w t *
      ‖linearLogSelbergMollifiedZetaProduct Y1
        (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2) ≤ C1) :
    ‖carlsonGaussianPoleFreeLpValue Delta w Y0 Y1
        hDelta (by omega) hY01 ((1 / 2 : ℝ) : ℂ)
          (by norm_num : (((1 / 2 : ℝ) : ℂ).re) ∈ Icc (1 / 2 : ℝ) 4)‖ ^ 2 ≤
      Real.exp ((1 / 2 : ℝ) ^ 2 / Delta ^ 2) *
        (2 * conreyOuterMultiplier Y0 Y1 ^ 2 *
            (2 * C1 + 2 * Real.sqrt (Real.pi / (1 / Delta ^ 2))) +
          2 * conreyInnerMultiplier Y0 Y1 ^ 2 *
            (2 * C0 + 2 * Real.sqrt (Real.pi / (1 / Delta ^ 2)))) := by
  have hErrorInt0 :=
    integrable_gaussian_norm_sq_linearLogSelbergMollifiedZetaError_of_product
      hDelta hProductInt0
  have hErrorInt1 :=
    integrable_gaussian_norm_sq_linearLogSelbergMollifiedZetaError_of_product
      hDelta hProductInt1
  have hErrorBound0 :=
    integral_gaussian_norm_sq_linearLogSelbergMollifiedZetaError_le_of_product
      hDelta hProductInt0 hProductBound0
  have hErrorBound1 :=
    integral_gaussian_norm_sq_linearLogSelbergMollifiedZetaError_le_of_product
      hDelta hProductInt1 hProductBound1
  exact norm_sq_carlsonGaussianPoleFreeLpValue_half_le_of_conrey_components
    hDelta hY0 hY01 hErrorInt0 hErrorInt1 hErrorBound0 hErrorBound1

end CarlsonZeroDensity
end PrimeNumberTheorem
