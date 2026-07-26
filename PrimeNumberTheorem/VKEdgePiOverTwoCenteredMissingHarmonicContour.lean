import PrimeNumberTheorem.VKEdgePiOverTwoCenteredContourDecay
import PrimeNumberTheorem.VKEdgePiOverTwoCenteredPsiWindow
import PrimeNumberTheorem.VKEdgePiOverTwoMissingHarmonicContour

open Complex Filter MeasureTheory Polynomial Set Topology

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- Values of the normalized PNT error inside a centered logarithmic
window. -/
def centeredNormalizedWindowValues
    (q d : ℝ) (rho : ℂ) (m : ℝ) : Set ℝ :=
  (fun y => |normalizedPsiError rho y|) ''
    localizedGaussianLogWindow q d m

/-- The least upper bound of the normalized PNT error in one centered
logarithmic window. -/
def centeredNormalizedWindowSup
    (q d : ℝ) (rho : ℂ) (m : ℝ) : ℝ :=
  sSup (centeredNormalizedWindowValues q d rho m)

/-- The absolute first moment of the normalized PNT error against a
centered projected Gaussian kernel. -/
def centeredNormalizedWindowFirstMoment
    (q d : ℝ) (rho : ℂ) (kernel : ℝ → ℝ → ℝ) (m : ℝ) : ℝ :=
  ∫ y : ℝ in localizedGaussianLogWindow q d m,
    |normalizedPsiError rho y| * |kernel m y|

/-- The second moment of the normalized PNT error against the absolute
centered projected Gaussian kernel. -/
def centeredNormalizedWindowSecondMoment
    (q d : ℝ) (rho : ℂ) (kernel : ℝ → ℝ → ℝ) (m : ℝ) : ℝ :=
  ∫ y : ℝ in localizedGaussianLogWindow q d m,
    normalizedPsiError rho y ^ 2 * |kernel m y|

/-- Quantitative contour data for a general centered logarithmic window. -/
structure CenteredLocalizedContourData
    (q d : ℝ) (rho : ℂ) (multiplicity mean : ℝ) where
  radius_nonneg : 0 ≤ d
  kernel : ℝ → ℝ → ℝ
  signal : ℝ → ℝ
  coefficient : ℝ → ℝ
  remainder : ℝ → ℝ
  eventually_kernel_measurable :
    ∀ᶠ m : ℝ in atTop, Measurable (kernel m)
  eventually_kernel_integrable :
    ∀ᶠ m : ℝ in atTop, Integrable (kernel m)
  coefficient_eq_kernel_mass :
    ∀ m : ℝ, coefficient m = ∫ y : ℝ, |kernel m y|
  eventually_second_moment_integrable :
    ∀ᶠ m : ℝ in atTop,
      IntegrableOn
        (fun y =>
          normalizedPsiError rho y ^ 2 * |kernel m y|)
        (localizedGaussianLogWindow q d m)
  eventually_first_moment_bound :
    ∀ᶠ m : ℝ in atTop,
      signal m ≤
        centeredNormalizedWindowFirstMoment q d rho kernel m +
          remainder m
  signal_tendsto :
    Tendsto signal atTop (𝓝 (2 * multiplicity))
  coefficient_tendsto :
    Tendsto coefficient atTop (𝓝 (2 * mean))
  remainder_tendsto :
    Tendsto remainder atTop (𝓝 0)
  eventually_coefficient_pos :
    ∀ᶠ m : ℝ in atTop, 0 < coefficient m
  eventually_window_bddAbove :
    ∀ᶠ m : ℝ in atTop,
      BddAbove (centeredNormalizedWindowValues q d rho m)
  eventually_upper_bound :
    ∀ᶠ m : ℝ in atTop,
      signal m ≤
        centeredNormalizedWindowSup q d rho m * coefficient m +
          remainder m

private theorem centeredNormalizedWindowValues_nonempty
    (q d : ℝ) (rho : ℂ) {m : ℝ} (hd : 0 ≤ d) (hm : 0 ≤ m) :
    (centeredNormalizedWindowValues q d rho m).Nonempty := by
  refine ⟨|normalizedPsiError rho (q * m)|, ?_⟩
  exact ⟨q * m, ⟨by nlinarith [mul_nonneg hd hm], by nlinarith [mul_nonneg hd hm]⟩, rfl⟩

/-- The centered contour limits force a normalized-error witness in every
sufficiently late centered window. -/
theorem CenteredLocalizedContourData.eventually_exists_normalizedPsiError_gt
    {q d : ℝ} {rho : ℂ} {multiplicity mean C : ℝ}
    (data : CenteredLocalizedContourData q d rho multiplicity mean)
    (_hmultiplicity : 0 < multiplicity) (hmean : 0 < mean)
    (hC : C < multiplicity / mean) :
    ∀ᶠ m : ℝ in atTop,
      ∃ y ∈ localizedGaussianLogWindow q d m,
        C < |normalizedPsiError rho y| := by
  have hmeanTwo : (2 * mean : ℝ) ≠ 0 := by positivity
  have hratio :
      Tendsto
        (fun m =>
          (data.signal m - data.remainder m) /
            data.coefficient m)
        atTop (𝓝 (multiplicity / mean)) := by
    have h :=
      (data.signal_tendsto.sub data.remainder_tendsto).div
        data.coefficient_tendsto hmeanTwo
    convert h using 1
    · congr 1
      field_simp
      ring
  have hratioLower :
      ∀ᶠ m : ℝ in atTop,
        C <
          (data.signal m - data.remainder m) /
            data.coefficient m :=
    (tendsto_order.1 hratio).1 C hC
  filter_upwards [
      data.eventually_coefficient_pos,
      data.eventually_window_bddAbove,
      data.eventually_upper_bound,
      eventually_ge_atTop (0 : ℝ),
      hratioLower] with m hcoefficient hbdd hupper hm hClower
  have hnumerator :
      data.signal m - data.remainder m ≤
        centeredNormalizedWindowSup q d rho m *
          data.coefficient m := by
    linarith
  have hratioLe :
      (data.signal m - data.remainder m) /
          data.coefficient m ≤
        centeredNormalizedWindowSup q d rho m :=
    (div_le_iff₀ hcoefficient).2 (by
      simpa [mul_comm] using hnumerator)
  have hCSup : C < centeredNormalizedWindowSup q d rho m :=
    hClower.trans_le hratioLe
  rcases
      (lt_csSup_iff hbdd
        (centeredNormalizedWindowValues_nonempty
          q d rho data.radius_nonneg hm)).1 hCSup with
    ⟨value, ⟨y, hyWindow, rfl⟩, hyValue⟩
  exact ⟨y, hyWindow, hyValue⟩

/-- Centered near-zero filter at the target center. -/
def centeredSharpenedTargetFilter (q : ℝ) (rho : ℂ) : ℂ[X] :=
  localizedNearZeroFilter rho (centeredPoleRadius q)

/-- Centered near-zero filter at the missing odd-harmonic center. -/
def centeredSharpenedMissingFilter
    (q : ℝ) (rho : ℂ) (k : ℕ) : ℂ[X] :=
  localizedNearZeroFilter
    (missingHarmonicContourCenter rho k) (centeredPoleRadius q)

/--
The real kernel obtained by pairing the target contour with the empty
missing-harmonic contour, normalized against the target zero.
-/
def centeredSharpenedProjectedPsiKernel
    (q : ℝ) (rho : ℂ) (k : ℕ) (m y : ℝ) : ℝ :=
  projectedPsiKernelAtCenter q
      (centeredSharpenedTargetFilter q rho) rho m y +
    relativeProjectedPsiKernelAtCenter q
      (centeredSharpenedMissingFilter q rho k) rho
      (missingHarmonicContourCenter rho k)
      (missingHarmonicContourCoefficient rho k) m y

/--
Absolute mass of the sharpened paired kernel on the full logarithmic line.
The part outside `localizedGaussianLogWindow q d m` is recorded separately
as a vanishing `psiRemainder`, so this full mass is a valid coefficient in
the centered-window estimate.
-/
def centeredSharpenedProjectedPsiCoefficient
    (q : ℝ) (rho : ℂ) (k : ℕ) (m : ℝ) : ℝ :=
  ∫ y : ℝ,
    |centeredSharpenedProjectedPsiKernel q rho k m y|

private def centeredSharpenedLeadingKernel
    (q : ℝ) (rho : ℂ) (k : ℕ) (m y : ℝ) : ℝ :=
  2 * normalizedGaussian m (q * m - y) *
    sharpenedPsiAbelKernel rho rho.im k y

private def centeredProjectedPsiLeadingKernel
    (q : ℝ) (w : ℂ) (m y : ℝ) : ℝ :=
  -(2 / ‖w‖) *
    (Complex.exp (-(I * (w.im : ℂ) * (y : ℂ))) *
      (w * (normalizedGaussian m (q * m - y) : ℂ))).re

private def centeredRelativeProjectedPsiLeadingKernel
    (q : ℝ) (target center c : ℂ) (m y : ℝ) : ℝ :=
  (‖center‖ / ‖target‖) *
    (-(2 / ‖center‖) *
      (Complex.exp (-(I * (center.im : ℂ) * (y : ℂ))) *
        (c * center *
          (normalizedGaussian m (q * m - y) : ℂ))).re)

private theorem missingHarmonicContourCenter_ne_zero
    {rho : ℂ} {k : ℕ} (hgamma : 0 < rho.im) :
    missingHarmonicContourCenter rho k ≠ 0 := by
  intro hzero
  have him := congrArg Complex.im hzero
  rw [missingHarmonicContourCenter, oddHarmonicPoint_im] at him
  simp only [Complex.zero_im] at him
  have hn : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by positivity
  nlinarith

private theorem exp_phase_mul_exp_neg_frequency
    (phase lambda y : ℝ) :
    Complex.exp (((phase : ℝ) : ℂ) * I) *
        Complex.exp (-(I * (lambda : ℂ) * (y : ℂ))) =
      Complex.exp ((((phase - lambda * y : ℝ) : ℂ) * I)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem relativeProjectedPsiKernel_normalizedGaussian
    (q : ℝ) {rho : ℂ} {k : ℕ} (hrho0 : rho ≠ 0)
    (hgamma : 0 < rho.im) (m y : ℝ) :
    centeredRelativeProjectedPsiLeadingKernel q rho
        (missingHarmonicContourCenter rho k)
        (missingHarmonicContourCoefficient rho k) m y =
      -(((-1 : ℝ) ^ k) /
          (((2 * k + 1 : ℕ) : ℝ))) *
        normalizedGaussian m (q * m - y) *
        Real.cos
          (((2 * k + 1 : ℕ) : ℝ) *
            (zeroResiduePhase rho - rho.im * y)) := by
  let n : ℝ := ((2 * k + 1 : ℕ) : ℝ)
  let center : ℂ := missingHarmonicContourCenter rho k
  have hn : 0 < n := by
    dsimp [n]
    positivity
  have hcenter0 : center ≠ 0 := by
    exact missingHarmonicContourCenter_ne_zero hgamma
  have hrhoNorm : 0 < ‖rho‖ := norm_pos_iff.mpr hrho0
  have hcenterNorm : 0 < ‖center‖ := norm_pos_iff.mpr hcenter0
  unfold centeredRelativeProjectedPsiLeadingKernel
  rw [show
      missingHarmonicContourCoefficient rho k * center =
        ((((-1 : ℝ) ^ k) / (2 * n) : ℝ) : ℂ) *
          (‖rho‖ : ℂ) *
          Complex.exp
            (((n * zeroResiduePhase rho : ℝ) : ℂ) * I) by
    unfold missingHarmonicContourCoefficient
    dsimp only [n, center]
    exact div_mul_cancel₀ _ hcenter0]
  rw [show
      Complex.exp
          (-(I * (center.im : ℂ) * (y : ℂ))) *
          ((((((-1 : ℝ) ^ k) / (2 * n) : ℝ) : ℂ) *
              (‖rho‖ : ℂ) *
              Complex.exp
                (((n * zeroResiduePhase rho : ℝ) : ℂ) * I)) *
            (normalizedGaussian m (q * m - y) : ℂ)) =
        ((((((-1 : ℝ) ^ k) / (2 * n)) * ‖rho‖ *
            normalizedGaussian m (q * m - y) : ℝ) : ℂ) *
          Complex.exp
            ((((n * zeroResiduePhase rho -
              n * rho.im * y : ℝ) : ℂ) * I))) by
    rw [show center.im = n * rho.im by
      dsimp [center, n, missingHarmonicContourCenter]
      exact oddHarmonicPoint_im rho.re rho.im k]
    calc
      Complex.exp (-(I * ((n * rho.im : ℝ) : ℂ) * (y : ℂ))) *
            ((((((-1 : ℝ) ^ k) / (2 * n) : ℝ) : ℂ) *
                (‖rho‖ : ℂ) *
                Complex.exp
                  (((n * zeroResiduePhase rho : ℝ) : ℂ) * I)) *
              (normalizedGaussian m (q * m - y) : ℂ)) =
          ((((((-1 : ℝ) ^ k) / (2 * n)) * ‖rho‖ *
              normalizedGaussian m (q * m - y) : ℝ) : ℂ) *
            (Complex.exp
                (((n * zeroResiduePhase rho : ℝ) : ℂ) * I) *
              Complex.exp
                (-(I * ((n * rho.im : ℝ) : ℂ) * (y : ℂ))))) := by
        push_cast
        ring
      _ = _ := by
        rw [exp_phase_mul_exp_neg_frequency]]
  rw [Complex.exp_mul_I]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re,
    Complex.sin_ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero,
    zero_mul, sub_self]
  rw [show
      n * zeroResiduePhase rho - n * rho.im * y =
        n * (zeroResiduePhase rho - rho.im * y) by ring]
  dsimp only [n]
  field_simp [hrhoNorm.ne', hcenterNorm.ne', hn.ne']
  ring_nf
  have hcenterNorm' :
      ‖missingHarmonicContourCenter rho k‖ ≠ 0 := by
    simpa only [center] using hcenterNorm.ne'
  field_simp [hcenterNorm']

private theorem projectedPsiKernel_normalizedGaussian
    (q : ℝ) {rho : ℂ} (hrho0 : rho ≠ 0) (m y : ℝ) :
    centeredProjectedPsiLeadingKernel q rho m y =
      2 * normalizedGaussian m (q * m - y) *
        phaseCos rho rho.im y := by
  have hrhoNorm : 0 < ‖rho‖ := norm_pos_iff.mpr hrho0
  have hpolar := Complex.norm_mul_exp_arg_mul_I rho
  unfold centeredProjectedPsiLeadingKernel phaseCos realPhaseCos
  have hphase :
      -(2 / ‖rho‖) *
          (Complex.exp
              (-(I * (rho.im : ℂ) * (y : ℂ))) *
            (rho * (normalizedGaussian m (q * m - y) : ℂ))).re =
        -2 * normalizedGaussian m (q * m - y) *
          Real.cos (rho.arg - rho.im * y) := by
    rw [show
        Complex.exp
            (-(I * (rho.im : ℂ) * (y : ℂ))) *
              (rho *
                (normalizedGaussian m (q * m - y) : ℂ)) =
          (((‖rho‖ * normalizedGaussian m (q * m - y) : ℝ) : ℂ) *
            Complex.exp
              ((((rho.arg - rho.im * y : ℝ) : ℂ) * I))) by
      rw [show
          rho * (normalizedGaussian m (q * m - y) : ℂ) =
            ((‖rho‖ : ℂ) *
              Complex.exp (((rho.arg : ℝ) : ℂ) * I)) *
            (normalizedGaussian m (q * m - y) : ℂ) by
        rw [hpolar]]
      rw [show
          Complex.exp (-(I * (rho.im : ℂ) * (y : ℂ))) *
              (((‖rho‖ : ℂ) *
                  Complex.exp (((rho.arg : ℝ) : ℂ) * I)) *
                (normalizedGaussian m (q * m - y) : ℂ)) =
            (((‖rho‖ * normalizedGaussian m (q * m - y) : ℝ) : ℂ) *
              (Complex.exp (((rho.arg : ℝ) : ℂ) * I) *
                Complex.exp (-(I * (rho.im : ℂ) * (y : ℂ))))) by
        push_cast
        ring]
      rw [exp_phase_mul_exp_neg_frequency]]
    rw [Complex.exp_mul_I]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re,
      Complex.sin_ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero,
      zero_mul, sub_self]
    field_simp [hrhoNorm.ne']
    ring
  rw [hphase]
  unfold zeroResiduePhase
  rw [show
      rho.arg + Real.pi - rho.im * y =
        (rho.arg - rho.im * y) + Real.pi by ring]
  rw [Real.cos_add_pi]
  ring

private theorem centeredSharpenedProjectedPsiKernel_one_eq_leading
    (q : ℝ) {rho : ℂ} {k : ℕ} (hrho0 : rho ≠ 0)
    (hgamma : 0 < rho.im) (m y : ℝ) :
    centeredProjectedPsiLeadingKernel q rho m y +
        centeredRelativeProjectedPsiLeadingKernel q rho
          (missingHarmonicContourCenter rho k)
          (missingHarmonicContourCoefficient rho k) m y =
      centeredSharpenedLeadingKernel q rho k m y := by
  rw [projectedPsiKernel_normalizedGaussian q hrho0,
    relativeProjectedPsiKernel_normalizedGaussian q hrho0 hgamma]
  unfold centeredSharpenedLeadingKernel sharpenedPsiAbelKernel
    missingOddHarmonicKernel phaseCos realPhaseCos
  ring

private theorem abs_projectedPsiKernel_sub_one_le
    (q : ℝ) (A : ℂ[X]) {w : ℂ} (hw0 : w ≠ 0) (m y : ℝ) :
    |projectedPsiKernelAtCenter q A w m y -
        centeredProjectedPsiLeadingKernel q w m y| ≤
      (2 / ‖w‖) *
        (‖w‖ *
            ‖polynomialGaussianKernel A m (q * m - y) -
              (normalizedGaussian m (q * m - y) : ℂ)‖ +
          ‖polynomialGaussianKernelDeriv A m (q * m - y)‖) := by
  have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  unfold projectedPsiKernelAtCenter centeredProjectedPsiLeadingKernel
  rw [← mul_sub]
  rw [← Complex.sub_re]
  rw [← mul_sub]
  rw [show
      w * polynomialGaussianKernel A m (q * m - y) +
          polynomialGaussianKernelDeriv A m (q * m - y) -
          w * (normalizedGaussian m (q * m - y) : ℂ) =
        w *
            (polynomialGaussianKernel A m (q * m - y) -
              (normalizedGaussian m (q * m - y) : ℂ)) +
          polynomialGaussianKernelDeriv A m (q * m - y) by ring]
  rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 2 / ‖w‖)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    |(Complex.exp (-(I * (w.im : ℂ) * (y : ℂ))) *
          (w *
              (polynomialGaussianKernel A m (q * m - y) -
                (normalizedGaussian m (q * m - y) : ℂ)) +
            polynomialGaussianKernelDeriv A m
              (q * m - y))).re| ≤
        ‖Complex.exp (-(I * (w.im : ℂ) * (y : ℂ))) *
          (w *
              (polynomialGaussianKernel A m (q * m - y) -
                (normalizedGaussian m (q * m - y) : ℂ)) +
            polynomialGaussianKernelDeriv A m
              (q * m - y))‖ :=
      abs_re_le_norm _
    _ =
        ‖w *
              (polynomialGaussianKernel A m (q * m - y) -
                (normalizedGaussian m (q * m - y) : ℂ)) +
            polynomialGaussianKernelDeriv A m
              (q * m - y)‖ := by
      rw [norm_mul, Complex.norm_exp]
      norm_num [Complex.mul_re]
    _ ≤
        ‖w‖ *
            ‖polynomialGaussianKernel A m (q * m - y) -
              (normalizedGaussian m (q * m - y) : ℂ)‖ +
          ‖polynomialGaussianKernelDeriv A m (q * m - y)‖ := by
      simpa only [norm_mul] using norm_add_le
        (w *
          (polynomialGaussianKernel A m (q * m - y) -
            (normalizedGaussian m (q * m - y) : ℂ)))
        (polynomialGaussianKernelDeriv A m (q * m - y))

private theorem abs_relativeProjectedPsiKernel_sub_one_le
    (q : ℝ) (A : ℂ[X]) {target center c : ℂ}
    (htarget0 : target ≠ 0) (hcenter0 : center ≠ 0)
    (m y : ℝ) :
    |relativeProjectedPsiKernelAtCenter q A target center c m y -
        centeredRelativeProjectedPsiLeadingKernel q target center c m y| ≤
      (2 * ‖c‖ / ‖target‖) *
        (‖center‖ *
            ‖polynomialGaussianKernel A m (q * m - y) -
              (normalizedGaussian m (q * m - y) : ℂ)‖ +
          ‖polynomialGaussianKernelDeriv A m (q * m - y)‖) := by
  have htargetNorm : 0 < ‖target‖ := norm_pos_iff.mpr htarget0
  have hcenterNorm : 0 < ‖center‖ := norm_pos_iff.mpr hcenter0
  unfold relativeProjectedPsiKernelAtCenter projectedPsiKernelAtCenter
    centeredRelativeProjectedPsiLeadingKernel
  rw [polynomialGaussianKernel_C_mul,
    polynomialGaussianKernelDeriv_C_mul]
  rw [← mul_sub]
  rw [← mul_sub]
  rw [← Complex.sub_re]
  rw [← mul_sub]
  rw [show
      center * (c * polynomialGaussianKernel A m (q * m - y)) +
            c * polynomialGaussianKernelDeriv A m (q * m - y) -
          c * center *
            (normalizedGaussian m (q * m - y) : ℂ) =
        c *
          (center *
              (polynomialGaussianKernel A m (q * m - y) -
                (normalizedGaussian m (q * m - y) : ℂ)) +
            polynomialGaussianKernelDeriv A m (q * m - y)) by ring]
  rw [abs_mul, abs_of_nonneg
    (div_nonneg (norm_nonneg center) (norm_nonneg target))]
  rw [abs_mul, abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ 2 / ‖center‖)]
  calc
    ‖center‖ / ‖target‖ * (2 / ‖center‖ *
        |(Complex.exp (-(I * (center.im : ℂ) * (y : ℂ))) *
          (c *
            (center *
                (polynomialGaussianKernel A m (q * m - y) -
                  (normalizedGaussian m (q * m - y) : ℂ)) +
              polynomialGaussianKernelDeriv A m
                (q * m - y)))).re|) ≤
        ‖center‖ / ‖target‖ * (2 / ‖center‖ *
          ‖Complex.exp (-(I * (center.im : ℂ) * (y : ℂ))) *
          (c *
            (center *
                (polynomialGaussianKernel A m (q * m - y) -
                  (normalizedGaussian m (q * m - y) : ℂ)) +
              polynomialGaussianKernelDeriv A m
                (q * m - y)))‖) := by
      gcongr
      exact abs_re_le_norm _
    _ =
        (2 * ‖c‖ / ‖target‖) *
          ‖center *
              (polynomialGaussianKernel A m (q * m - y) -
                (normalizedGaussian m (q * m - y) : ℂ)) +
            polynomialGaussianKernelDeriv A m
              (q * m - y)‖ := by
      rw [norm_mul, Complex.norm_exp, norm_mul]
      norm_num [Complex.mul_re]
      field_simp [htargetNorm.ne', hcenterNorm.ne']
    _ ≤
        (2 * ‖c‖ / ‖target‖) *
          (‖center‖ *
              ‖polynomialGaussianKernel A m (q * m - y) -
                (normalizedGaussian m (q * m - y) : ℂ)‖ +
            ‖polynomialGaussianKernelDeriv A m
              (q * m - y)‖) := by
      gcongr
      simpa only [norm_mul] using norm_add_le
        (center *
          (polynomialGaussianKernel A m (q * m - y) -
            (normalizedGaussian m (q * m - y) : ℂ)))
        (polynomialGaussianKernelDeriv A m (q * m - y))
    _ = _ := rfl

private theorem exists_centeredSharpenedProjectedPsiKernel_sub_leading_l1_bound
    (q : ℝ) {rho : ℂ} {k : ℕ} (hrho0 : rho ≠ 0)
    (hgamma : 0 < rho.im) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ m : ℝ, 1 ≤ m →
        Integrable (fun y : ℝ =>
          |centeredSharpenedProjectedPsiKernel q rho k m y -
            centeredSharpenedLeadingKernel q rho k m y|) ∧
        (∫ y : ℝ,
            |centeredSharpenedProjectedPsiKernel q rho k m y -
              centeredSharpenedLeadingKernel q rho k m y|) ≤
            C / Real.sqrt m := by
  let targetA : ℂ[X] := centeredSharpenedTargetFilter q rho
  let center : ℂ := missingHarmonicContourCenter rho k
  let missingA : ℂ[X] := centeredSharpenedMissingFilter q rho k
  let c : ℂ := missingHarmonicContourCoefficient rho k
  have htargetEval : targetA.eval 0 = 1 := by
    exact localizedNearZeroFilter_eval_zero rho (centeredPoleRadius q)
  have hmissingEval : missingA.eval 0 = 1 := by
    exact localizedNearZeroFilter_eval_zero center (centeredPoleRadius q)
  obtain ⟨Ct, hCt, htargetSub⟩ :=
    exists_polynomialGaussianKernel_sub_l1_bound targetA htargetEval
  obtain ⟨Dt, hDt, htargetDeriv⟩ :=
    exists_polynomialGaussianKernelDeriv_l1_bound targetA
  obtain ⟨Cm, hCm, hmissingSub⟩ :=
    exists_polynomialGaussianKernel_sub_l1_bound missingA hmissingEval
  obtain ⟨Dm, hDm, hmissingDeriv⟩ :=
    exists_polynomialGaussianKernelDeriv_l1_bound missingA
  have hcenter0 : center ≠ 0 := by
    exact missingHarmonicContourCenter_ne_zero hgamma
  have hrhoNorm : 0 < ‖rho‖ := norm_pos_iff.mpr hrho0
  let C : ℝ :=
    (2 / ‖rho‖) * (‖rho‖ * Ct + Dt) +
      (2 * ‖c‖ / ‖rho‖) * (‖center‖ * Cm + Dm)
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro m hm
    have hmPos : 0 < m := zero_lt_one.trans_le hm
    let targetMajor : ℝ → ℝ := fun y =>
      (2 / ‖rho‖) *
        (‖rho‖ *
            ‖polynomialGaussianKernel targetA m (q * m - y) -
              (normalizedGaussian m (q * m - y) : ℂ)‖ +
          ‖polynomialGaussianKernelDeriv targetA m (q * m - y)‖)
    let missingMajor : ℝ → ℝ := fun y =>
      (2 * ‖c‖ / ‖rho‖) *
        (‖center‖ *
            ‖polynomialGaussianKernel missingA m (q * m - y) -
              (normalizedGaussian m (q * m - y) : ℂ)‖ +
          ‖polynomialGaussianKernelDeriv missingA m (q * m - y)‖)
    have htargetMajorInt : Integrable targetMajor := by
      have hsub :
          Integrable (fun t : ℝ =>
            ‖polynomialGaussianKernel targetA m t -
              (normalizedGaussian m t : ℂ)‖) :=
        ((integrable_polynomialGaussianKernel targetA hmPos).sub
          (integrable_normalizedGaussian hmPos).ofReal).norm
      have hderiv :
          Integrable (fun t : ℝ =>
            ‖polynomialGaussianKernelDeriv targetA m t‖) :=
        (integrable_polynomialGaussianKernelDeriv targetA hmPos).norm
      exact
        (((hsub.comp_sub_left (q * m)).const_mul ‖rho‖).add
          (hderiv.comp_sub_left (q * m))).const_mul (2 / ‖rho‖)
    have hmissingMajorInt : Integrable missingMajor := by
      have hsub :
          Integrable (fun t : ℝ =>
            ‖polynomialGaussianKernel missingA m t -
              (normalizedGaussian m t : ℂ)‖) :=
        ((integrable_polynomialGaussianKernel missingA hmPos).sub
          (integrable_normalizedGaussian hmPos).ofReal).norm
      have hderiv :
          Integrable (fun t : ℝ =>
            ‖polynomialGaussianKernelDeriv missingA m t‖) :=
        (integrable_polynomialGaussianKernelDeriv missingA hmPos).norm
      exact
        (((hsub.comp_sub_left (q * m)).const_mul ‖center‖).add
          (hderiv.comp_sub_left (q * m))).const_mul
            (2 * ‖c‖ / ‖rho‖)
    have hpointwise :
        ∀ y : ℝ,
          |centeredSharpenedProjectedPsiKernel q rho k m y -
              centeredSharpenedLeadingKernel q rho k m y| ≤
            targetMajor y + missingMajor y := by
      intro y
      rw [← centeredSharpenedProjectedPsiKernel_one_eq_leading
        q hrho0 hgamma]
      unfold centeredSharpenedProjectedPsiKernel
      calc
        |(projectedPsiKernelAtCenter q targetA rho m y +
              relativeProjectedPsiKernelAtCenter q missingA rho center c m y) -
            (centeredProjectedPsiLeadingKernel q rho m y +
              centeredRelativeProjectedPsiLeadingKernel q rho center c m y)| ≤
            |projectedPsiKernelAtCenter q targetA rho m y -
              centeredProjectedPsiLeadingKernel q rho m y| +
            |relativeProjectedPsiKernelAtCenter q missingA rho center c m y -
              centeredRelativeProjectedPsiLeadingKernel q rho center c m y| := by
          rw [show
                (projectedPsiKernelAtCenter q targetA rho m y +
                  relativeProjectedPsiKernelAtCenter q missingA rho center c m y) -
                (centeredProjectedPsiLeadingKernel q rho m y +
                  centeredRelativeProjectedPsiLeadingKernel q rho center c m y) =
                (projectedPsiKernelAtCenter q targetA rho m y -
                  centeredProjectedPsiLeadingKernel q rho m y) +
                (relativeProjectedPsiKernelAtCenter q missingA rho center c m y -
                  centeredRelativeProjectedPsiLeadingKernel q rho center c m y) by ring]
          exact abs_add_le _ _
        _ ≤ targetMajor y + missingMajor y := by
          exact add_le_add
            (abs_projectedPsiKernel_sub_one_le q targetA hrho0 m y)
            (abs_relativeProjectedPsiKernel_sub_one_le
              q missingA hrho0 hcenter0 m y)
    have hsourceInt :
        Integrable (fun y : ℝ =>
          |centeredSharpenedProjectedPsiKernel q rho k m y -
            centeredSharpenedLeadingKernel q rho k m y|) := by
      apply Integrable.mono' (htargetMajorInt.add hmissingMajorInt)
      · have hactual :
            Continuous
              (centeredSharpenedProjectedPsiKernel q rho k m) := by
          unfold centeredSharpenedProjectedPsiKernel
          exact
            (continuous_projectedPsiKernelAtCenter
                q targetA rho hmPos).add
              ((continuous_projectedPsiKernelAtCenter
                q (Polynomial.C c * missingA) center hmPos).const_mul
                  (‖center‖ / ‖rho‖))
        have hleading :
            Continuous (centeredSharpenedLeadingKernel q rho k m) := by
          unfold centeredSharpenedLeadingKernel sharpenedPsiAbelKernel
            missingOddHarmonicKernel normalizedGaussian
          fun_prop
        exact (hactual.sub hleading).abs.aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun y => by
          simpa [Real.norm_eq_abs, Pi.add_apply,
            abs_of_nonneg (abs_nonneg _)] using hpointwise y
    refine ⟨hsourceInt, ?_⟩
    calc
      (∫ y : ℝ,
          |centeredSharpenedProjectedPsiKernel q rho k m y -
            centeredSharpenedLeadingKernel q rho k m y|) ≤
          ∫ y : ℝ, targetMajor y + missingMajor y :=
        integral_mono hsourceInt (htargetMajorInt.add hmissingMajorInt)
          hpointwise
      _ = (∫ y : ℝ, targetMajor y) +
          ∫ y : ℝ, missingMajor y := by
        rw [integral_add htargetMajorInt hmissingMajorInt]
      _ ≤
          (2 / ‖rho‖) *
              (‖rho‖ * (Ct / Real.sqrt m) +
                Dt / Real.sqrt m) +
            (2 * ‖c‖ / ‖rho‖) *
              (‖center‖ * (Cm / Real.sqrt m) +
                Dm / Real.sqrt m) := by
        have htSub := htargetSub m hm
        have htDeriv := htargetDeriv m hm
        have hmSub := hmissingSub m hm
        have hmDeriv := hmissingDeriv m hm
        have htMajorEq :
            (∫ y : ℝ, targetMajor y) =
              (2 / ‖rho‖) *
                (‖rho‖ *
                    (∫ t : ℝ,
                      ‖polynomialGaussianKernel targetA m t -
                        (normalizedGaussian m t : ℂ)‖) +
                  ∫ t : ℝ,
                    ‖polynomialGaussianKernelDeriv targetA m t‖) := by
          have hsub :
              Integrable (fun t : ℝ =>
                ‖polynomialGaussianKernel targetA m t -
                  (normalizedGaussian m t : ℂ)‖) :=
            ((integrable_polynomialGaussianKernel targetA hmPos).sub
              (integrable_normalizedGaussian hmPos).ofReal).norm
          have hderiv :
              Integrable (fun t : ℝ =>
                ‖polynomialGaussianKernelDeriv targetA m t‖) :=
            (integrable_polynomialGaussianKernelDeriv targetA hmPos).norm
          have hsubShift := hsub.comp_sub_left (q * m)
          have hderivShift := hderiv.comp_sub_left (q * m)
          dsimp [targetMajor]
          rw [integral_const_mul,
            integral_add (hsubShift.const_mul ‖rho‖) hderivShift,
            integral_const_mul]
          rw [MeasureTheory.integral_sub_left_eq_self
              (fun t : ℝ =>
                ‖polynomialGaussianKernel targetA m t -
                  (normalizedGaussian m t : ℂ)‖) volume (q * m),
            MeasureTheory.integral_sub_left_eq_self
              (fun t : ℝ =>
                ‖polynomialGaussianKernelDeriv targetA m t‖)
              volume (q * m)]
        have hmMajorEq :
            (∫ y : ℝ, missingMajor y) =
              (2 * ‖c‖ / ‖rho‖) *
                (‖center‖ *
                    (∫ t : ℝ,
                      ‖polynomialGaussianKernel missingA m t -
                        (normalizedGaussian m t : ℂ)‖) +
                  ∫ t : ℝ,
                    ‖polynomialGaussianKernelDeriv missingA m t‖) := by
          have hsub :
              Integrable (fun t : ℝ =>
                ‖polynomialGaussianKernel missingA m t -
                  (normalizedGaussian m t : ℂ)‖) :=
            ((integrable_polynomialGaussianKernel missingA hmPos).sub
              (integrable_normalizedGaussian hmPos).ofReal).norm
          have hderiv :
              Integrable (fun t : ℝ =>
                ‖polynomialGaussianKernelDeriv missingA m t‖) :=
            (integrable_polynomialGaussianKernelDeriv missingA hmPos).norm
          have hsubShift := hsub.comp_sub_left (q * m)
          have hderivShift := hderiv.comp_sub_left (q * m)
          dsimp [missingMajor]
          rw [integral_const_mul,
            integral_add (hsubShift.const_mul ‖center‖) hderivShift,
            integral_const_mul]
          rw [MeasureTheory.integral_sub_left_eq_self
              (fun t : ℝ =>
                ‖polynomialGaussianKernel missingA m t -
                  (normalizedGaussian m t : ℂ)‖) volume (q * m),
            MeasureTheory.integral_sub_left_eq_self
              (fun t : ℝ =>
                ‖polynomialGaussianKernelDeriv missingA m t‖)
              volume (q * m)]
        rw [htMajorEq, hmMajorEq]
        gcongr
      _ = C / Real.sqrt m := by
        dsimp [C]
        ring

/--
The absolute mass of the actual paired polynomial kernels converges to twice
the exact missing-harmonic denominator.  This is the localized coefficient
which preserves the strict gap above `pi / 2`.
-/
theorem tendsto_centeredSharpenedProjectedPsiCoefficient
    (q : ℝ) {rho : ℂ} {k : ℕ} (hrho0 : rho ≠ 0)
    (hgamma : 0 < rho.im) :
    Tendsto
      (centeredSharpenedProjectedPsiCoefficient q rho k)
      atTop
      (𝓝 (2 * sharpenedMissingHarmonicDenominator k)) := by
  let actual : ℝ → ℝ → ℝ := fun m y =>
    centeredSharpenedProjectedPsiKernel q rho k m y
  let leading : ℝ → ℝ → ℝ := fun m y =>
    centeredSharpenedLeadingKernel q rho k m y
  let leadingCoefficient : ℝ → ℝ := fun m =>
    ∫ y : ℝ, |leading m y|
  obtain ⟨C, hC, herror⟩ :=
    exists_centeredSharpenedProjectedPsiKernel_sub_leading_l1_bound
      q hrho0 hgamma
  have hleadingIntegrable :
      ∀ {m : ℝ}, 0 < m → Integrable (leading m) := by
    intro m hm
    have hgaussian :
        Integrable
          (fun y : ℝ =>
            normalizedGaussian m (q * m - y)) :=
      (integrable_normalizedGaussian hm).comp_sub_left (q * m)
    apply Integrable.mono' (hgaussian.const_mul 4)
    · unfold leading centeredSharpenedLeadingKernel sharpenedPsiAbelKernel
        missingOddHarmonicKernel normalizedGaussian
      fun_prop
    · exact Filter.Eventually.of_forall fun y => by
        have hq :=
          abs_sharpenedPsiAbelKernel_le_two rho rho.im k y
        have hnonneg :
            0 ≤ 2 * normalizedGaussian m (q * m - y) :=
          mul_nonneg (by norm_num)
            (normalizedGaussian_pos hm (q * m - y)).le
        simpa only [leading, centeredSharpenedLeadingKernel, Real.norm_eq_abs,
          abs_mul, abs_of_nonneg hnonneg,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)] using
          (mul_le_mul_of_nonneg_left hq hnonneg).trans_eq (by ring)
  have hleadingLimit :
      Tendsto leadingCoefficient atTop
        (𝓝 (2 * sharpenedMissingHarmonicDenominator k)) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hhalf : 0 < ε / 2 := by positivity
    have hperiodic :=
      eventually_uniform_gaussian_abs_sharpenedPsiAbelKernel
        (rho := rho) (gamma := rho.im) (k := k) hgamma hhalf
    rcases
        (eventually_atTop.1
          (hperiodic.and (eventually_ge_atTop (1 : ℝ)))) with
      ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro m hmM
    have hmPair := hM m hmM
    have hmMean := hmPair.1
    have hm := hmPair.2
    have hmPos : 0 < m := zero_lt_one.trans_le hm
    have hchange :
        leadingCoefficient m =
          2 * ∫ t : ℝ,
            normalizedGaussian m t *
              |sharpenedPsiAbelKernel rho rho.im k (q * m - t)| := by
      have hqBound :
          ∀ y : ℝ,
            |sharpenedPsiAbelKernel rho rho.im k y| ≤ 2 :=
        abs_sharpenedPsiAbelKernel_le_two rho rho.im k
      have hfInt :
          Integrable (fun t : ℝ =>
            normalizedGaussian m t *
              |sharpenedPsiAbelKernel rho rho.im k
                (q * m - t)|) := by
        apply Integrable.mono'
          ((integrable_normalizedGaussian hmPos).const_mul 2)
        · unfold sharpenedPsiAbelKernel missingOddHarmonicKernel
            normalizedGaussian
          fun_prop
        · exact Filter.Eventually.of_forall fun t => by
            rw [Real.norm_eq_abs, abs_mul,
              abs_of_nonneg (normalizedGaussian_pos hmPos t).le,
              abs_of_nonneg (abs_nonneg _)]
            exact mul_le_mul_of_nonneg_left
              (hqBound (q * m - t))
              (normalizedGaussian_pos hmPos t).le |>.trans_eq (by ring)
      unfold leadingCoefficient leading centeredSharpenedLeadingKernel
      rw [show
          (fun y : ℝ =>
            |2 * normalizedGaussian m (q * m - y) *
              sharpenedPsiAbelKernel rho rho.im k y|) =
            fun y : ℝ =>
              2 * (normalizedGaussian m (q * m - y) *
                |sharpenedPsiAbelKernel rho rho.im k y|) by
        funext y
        rw [abs_mul, abs_mul,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_nonneg
            (normalizedGaussian_pos hmPos (q * m - y)).le]
        ring]
      rw [integral_const_mul]
      rw [show
          (fun y : ℝ =>
            normalizedGaussian m (q * m - y) *
              |sharpenedPsiAbelKernel rho rho.im k y|) =
            fun y : ℝ =>
              (fun t : ℝ =>
                normalizedGaussian m t *
                  |sharpenedPsiAbelKernel rho rho.im k
                    (q * m - t)|) (q * m - y) by
        funext y
        ring_nf]
      rw [MeasureTheory.integral_sub_left_eq_self
        (fun t : ℝ =>
          normalizedGaussian m t *
            |sharpenedPsiAbelKernel rho rho.im k
              (q * m - t)|) volume (q * m)]
    rw [hchange]
    have hmean := hmMean (q * m)
    rw [Real.dist_eq]
    calc
      |2 * (∫ t : ℝ,
              normalizedGaussian m t *
                |sharpenedPsiAbelKernel rho rho.im k
                  (q * m - t)|) -
            2 * sharpenedMissingHarmonicDenominator k| =
          2 * |(∫ t : ℝ,
              normalizedGaussian m t *
                |sharpenedPsiAbelKernel rho rho.im k
                  (q * m - t)|) -
            sharpenedMissingHarmonicDenominator k| := by
        rw [show
            2 * (∫ t : ℝ,
                normalizedGaussian m t *
                  |sharpenedPsiAbelKernel rho rho.im k
                    (q * m - t)|) -
                2 * sharpenedMissingHarmonicDenominator k =
              2 * ((∫ t : ℝ,
                  normalizedGaussian m t *
                    |sharpenedPsiAbelKernel rho rho.im k
                      (q * m - t)|) -
                sharpenedMissingHarmonicDenominator k) by ring,
          abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ < 2 * (ε / 2) := mul_lt_mul_of_pos_left hmean (by norm_num)
      _ = ε := by ring
  have herrorLimit :
      Tendsto (fun m : ℝ => C / Real.sqrt m) atTop (𝓝 0) := by
    have hinv :
        Tendsto (fun m : ℝ => (Real.sqrt m)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
    convert hinv.const_mul C using 1 <;> simp
  have hcoefficientError :
      Tendsto
        (fun m : ℝ =>
          |centeredSharpenedProjectedPsiCoefficient q rho k m -
            leadingCoefficient m|)
        atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun _ => abs_nonneg _
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with m hm
      have hmPos : 0 < m := zero_lt_one.trans_le hm
      have herr := herror m hm
      have hdiffInt := herr.1
      have hleadingInt := hleadingIntegrable hmPos
      have hactualInt :
          Integrable (actual m) := by
        have hsub :
            Integrable (fun y => actual m y - leading m y) := by
          have hactualCont : Continuous (actual m) := by
            exact
              (continuous_projectedPsiKernelAtCenter q
                (centeredSharpenedTargetFilter q rho) rho hmPos).add
              ((continuous_projectedPsiKernelAtCenter q
                (Polynomial.C (missingHarmonicContourCoefficient rho k) *
                  centeredSharpenedMissingFilter q rho k)
                (missingHarmonicContourCenter rho k) hmPos).const_mul
                  (‖missingHarmonicContourCenter rho k‖ / ‖rho‖))
          have hleadingCont : Continuous (leading m) := by
            unfold leading centeredSharpenedLeadingKernel sharpenedPsiAbelKernel
              missingOddHarmonicKernel normalizedGaussian
            fun_prop
          apply
            (integrable_norm_iff
              (hactualCont.sub hleadingCont).aestronglyMeasurable).mp
          simpa only [actual, leading, Real.norm_eq_abs] using hdiffInt
        have heq :
            actual m =
              (fun y => actual m y - leading m y) + leading m := by
          funext y
          simp
        rw [heq]
        exact hsub.add hleadingInt
      unfold centeredSharpenedProjectedPsiCoefficient
      change
        abs ((∫ y : ℝ, abs (actual m y)) -
            (∫ y : ℝ, abs (leading m y))) ≤ C / Real.sqrt m
      calc
        abs ((∫ y : ℝ, abs (actual m y)) -
              (∫ y : ℝ, abs (leading m y))) =
            abs (∫ y : ℝ, abs (actual m y) - abs (leading m y)) := by
          rw [integral_sub hactualInt.abs hleadingInt.abs]
        _ ≤ ∫ y : ℝ,
              abs (abs (actual m y) - abs (leading m y)) :=
          abs_integral_le_integral_abs
        _ ≤ ∫ y : ℝ, abs (actual m y - leading m y) := by
          apply integral_mono
          · exact (hactualInt.abs.sub hleadingInt.abs).abs
          · exact hdiffInt
          · intro y
            exact abs_abs_sub_abs_le_abs_sub _ _
        _ ≤ C / Real.sqrt m := herr.2
    · exact herrorLimit
  have hsubLimit :
      Tendsto
        (fun m =>
          centeredSharpenedProjectedPsiCoefficient q rho k m -
            leadingCoefficient m)
        atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    exact hcoefficientError
  have hadd := hsubLimit.add hleadingLimit
  simpa using hadd

/-- Every fixed centered projected polynomial-Gaussian kernel is integrable
on the full logarithmic line. -/
private theorem integrable_centeredProjectedPsiKernel
    (q : ℝ) (A : ℂ[X]) (w : ℂ) {m : ℝ} (hm : 0 < m) :
    Integrable (projectedPsiKernelAtCenter q A w m) := by
  have hkernel :
      Integrable (fun y : ℝ =>
        w * polynomialGaussianKernel A m (q * m - y) +
          polynomialGaussianKernelDeriv A m (q * m - y)) :=
    ((integrable_polynomialGaussianKernel A hm).comp_sub_left (q * m)
      |>.const_mul w).add
      ((integrable_polynomialGaussianKernelDeriv A hm).comp_sub_left
        (q * m))
  have hphase :
      AEStronglyMeasurable
        (fun y : ℝ =>
          Complex.exp (-(I * (w.im : ℂ) * (y : ℂ)))) volume := by
    fun_prop
  have hphaseBound :
      ∀ᵐ y : ℝ,
        ‖Complex.exp (-(I * (w.im : ℂ) * (y : ℂ)))‖ ≤ 1 := by
    filter_upwards with y
    rw [Complex.norm_exp]
    norm_num [Complex.mul_re]
  have hproduct := hkernel.bdd_mul hphase hphaseBound
  unfold projectedPsiKernelAtCenter
  exact hproduct.re.const_mul (-(2 / ‖w‖))

/-- Relative centered projected kernels inherit full-line integrability. -/
private theorem integrable_centeredRelativeProjectedPsiKernel
    (q : ℝ) (A : ℂ[X]) (target center c : ℂ)
    {m : ℝ} (hm : 0 < m) :
    Integrable
      (relativeProjectedPsiKernelAtCenter
        q A target center c m) := by
  unfold relativeProjectedPsiKernelAtCenter
  exact
    (integrable_centeredProjectedPsiKernel
      q (C c * A) center hm).const_mul
        (‖center‖ / ‖target‖)

/-- Every sufficiently late centered window has a finite upper bound for
the normalized PNT error. -/
private theorem eventually_bddAbove_centeredNormalizedWindowValues
    (q d : ℝ) {u v : ℝ}
    (hd : 0 < d) (hdq : d < q)
    (_hu : 0 < u) (hu1 : u < 1) :
    ∀ᶠ m : ℝ in atTop,
      BddAbove
        (centeredNormalizedWindowValues q d
          ((u : ℂ) + I * v) m) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with m hm
  let w : ℂ := (u : ℂ) + I * v
  let C : ℝ :=
    ‖w‖ * (Real.log 4 + 5) *
      Real.exp ((1 - u) * ((q + d) * m))
  refine ⟨C, ?_⟩
  rintro z ⟨y, hy, rfl⟩
  have hqPos : 0 < q := hd.trans hdq
  have hm0 : 0 ≤ m := zero_le_one.trans hm
  have hy0 : 0 ≤ y := by
    have hleft : 0 ≤ (q - d) * m :=
      mul_nonneg (sub_nonneg.mpr hdq.le) hm0
    exact hleft.trans hy.1
  have hyUpper : y ≤ (q + d) * m := hy.2
  have hpsi :
      chebyshevPsi (Real.exp y) ≤
        (Real.log 4 + 4) * Real.exp y := by
    rw [chebyshevPsi_eq_mathlib]
    exact Chebyshev.psi_le_const_mul_self (Real.exp_pos y).le
  have hpsiNonneg : 0 ≤ chebyshevPsi (Real.exp y) := by
    unfold chebyshevPsi
    apply Finset.sum_nonneg
    intro n hn
    exact ArithmeticFunction.vonMangoldt_nonneg
  have herror :
      |chebyshevPsi (Real.exp y) - Real.exp y| ≤
        (Real.log 4 + 5) * Real.exp y := by
    rw [abs_sub_le_iff]
    constructor
    · nlinarith [Real.exp_pos y]
    · nlinarith [Real.exp_pos y,
        Real.log_pos (by norm_num : 1 < (4 : ℝ))]
  have hexpOrder :
      Real.exp ((1 - u) * y) ≤
        Real.exp ((1 - u) * ((q + d) * m)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hyUpper (by linarith)
  have hwRe : w.re = u := by
    dsimp [w]
    norm_num [Complex.mul_re]
  unfold normalizedPsiError
  change
    |‖w‖ * (chebyshevPsi (Real.exp y) - Real.exp y) *
      Real.exp (-w.re * y)| ≤ C
  rw [abs_mul, abs_mul, abs_of_nonneg (norm_nonneg w),
    abs_of_pos (Real.exp_pos _), hwRe]
  calc
    ‖w‖ * |chebyshevPsi (Real.exp y) - Real.exp y| *
          Real.exp (-u * y) ≤
        ‖w‖ * ((Real.log 4 + 5) * Real.exp y) *
          Real.exp (-u * y) := by
      gcongr
    _ = ‖w‖ * (Real.log 4 + 5) *
          Real.exp ((1 - u) * y) := by
      calc
        ‖w‖ * ((Real.log 4 + 5) * Real.exp y) *
              Real.exp (-u * y) =
            ‖w‖ * (Real.log 4 + 5) *
              (Real.exp y * Real.exp (-u * y)) := by ring
        _ = ‖w‖ * (Real.log 4 + 5) *
              Real.exp (y + -u * y) := by rw [Real.exp_add]
        _ = _ := by congr 2 <;> ring
    _ ≤ C := by
      dsimp [C]
      gcongr

/--
The paired true-zeta contour is controlled before taking a supremum by the
absolute first moment of the normalized error against the combined projected
Gaussian kernel.
-/
private theorem eventually_centeredSharpenedProjectedPsiWindow_firstMoment_bound
    (q d : ℝ) {rho : ℂ} {k : ℕ}
    (hd : 0 < d) (hdq : d < q)
    (hrhoRe0 : 0 < rho.re) (_hrhoRe1 : rho.re < 1)
    (_hgamma : 0 < rho.im) :
    ∀ᶠ m : ℝ in atTop,
      -((localizedPsiGaussianAverageAtCenter q (centeredSharpenedTargetFilter q rho) rho m +
          missingHarmonicContourCoefficient rho k *
            localizedPsiGaussianAverageAtCenter q
              (centeredSharpenedMissingFilter q rho k)
              (missingHarmonicContourCenter rho k) m).re) / Real.pi ≤
        centeredNormalizedWindowFirstMoment q d rho
            (centeredSharpenedProjectedPsiKernel q rho k) m +
          projectedPsiTailRemainderAtCenter q d
              (centeredSharpenedTargetFilter q rho) rho m +
          relativeProjectedPsiTailRemainderAtCenter q d
              (centeredSharpenedMissingFilter q rho k) rho
              (missingHarmonicContourCenter rho k)
              (missingHarmonicContourCoefficient rho k) m := by
  let targetA := centeredSharpenedTargetFilter q rho
  let center := missingHarmonicContourCenter rho k
  let missingA := centeredSharpenedMissingFilter q rho k
  let c := missingHarmonicContourCoefficient rho k
  have hrho0 : rho ≠ 0 := ne_zero_of_re_pos hrhoRe0
  have hcenterRe : center.re = rho.re := by
    dsimp [center, missingHarmonicContourCenter]
    exact oddHarmonicPoint_re rho.re rho.im k
  have hcenterRe0 : 0 < center.re := hcenterRe.symm ▸ hrhoRe0
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with m hm
  have hrhoEq : (rho.re : ℂ) + I * rho.im = rho := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  have hmPos : 0 < m := zero_lt_one.trans_le hm
  let kernel : ℝ → ℝ := centeredSharpenedProjectedPsiKernel q rho k m
  let fTarget : ℝ → ℝ := fun y =>
    normalizedPsiError rho y * projectedPsiKernelAtCenter q targetA rho m y
  let fMissing : ℝ → ℝ := fun y =>
    normalizedPsiError rho y *
      relativeProjectedPsiKernelAtCenter q missingA rho center c m y
  let f : ℝ → ℝ := fun y =>
    normalizedPsiError rho y * kernel y
  let window : Set ℝ := localizedGaussianLogWindow q d m
  let tail : Set ℝ := Set.Ioi 0 \ window
  have hwindowMeasurable : MeasurableSet window := measurableSet_Icc
  have htailMeasurable : MeasurableSet tail :=
    measurableSet_Ioi.diff hwindowMeasurable
  have hwindowSubset : window ⊆ Set.Ioi (0 : ℝ) := by
    intro y hy
    have hqPos : 0 < q := hd.trans hdq
    exact Set.mem_Ioi.mpr (by
      have hleft : 0 < (q - d) * m :=
        mul_pos (sub_pos.mpr hdq) hmPos
      linarith [hy.1])
  have hfTargetIoi : IntegrableOn fTarget (Set.Ioi 0) := by
    simpa only [fTarget, targetA] using
      integrableOn_normalizedPsiError_mul_projectedPsiKernelAtCenter
        q (centeredSharpenedTargetFilter q rho) hmPos hrhoRe0
  have hfMissingIoi : IntegrableOn fMissing (Set.Ioi 0) := by
    simpa only [fMissing, missingA, center, c] using
      integrableOn_normalizedPsiError_mul_relativeProjectedPsiKernelAtCenter
        q (missingHarmonicContourCoefficient rho k)
        (centeredSharpenedMissingFilter q rho k) hmPos hrhoRe0 hcenterRe0
        hcenterRe
  have hfIoi : IntegrableOn f (Set.Ioi 0) := by
    have hadd := hfTargetIoi.add hfMissingIoi
    apply hadd.congr_fun _ measurableSet_Ioi
    intro y _hy
    dsimp [f, fTarget, fMissing, kernel, targetA, missingA, center, c]
    unfold centeredSharpenedProjectedPsiKernel
    ring
  have hfWindow : IntegrableOn f window :=
    hfIoi.mono_set hwindowSubset
  have hfTail : IntegrableOn f tail :=
    hfIoi.mono_set fun _ hy => hy.1
  have hfTargetTail : IntegrableOn fTarget tail :=
    hfTargetIoi.mono_set fun _ hy => hy.1
  have hfMissingTail : IntegrableOn fMissing tail :=
    hfMissingIoi.mono_set fun _ hy => hy.1
  have hinside :
      (∫ y : ℝ in window, f y) ≤
        centeredNormalizedWindowFirstMoment q d rho
          (centeredSharpenedProjectedPsiKernel q rho k) m := by
    calc
      (∫ y : ℝ in window, f y) ≤
          ∫ y : ℝ in window, |f y| :=
        setIntegral_mono_on hfWindow hfWindow.abs hwindowMeasurable
          (fun y _ => le_abs_self (f y))
      _ = centeredNormalizedWindowFirstMoment q d rho
          (centeredSharpenedProjectedPsiKernel q rho k) m := by
        apply setIntegral_congr_fun hwindowMeasurable
        intro y _hy
        dsimp [f, kernel]
        rw [abs_mul]
  have htail :
      (∫ y : ℝ in tail, f y) ≤
        projectedPsiTailRemainderAtCenter q d targetA rho m +
          relativeProjectedPsiTailRemainderAtCenter q d missingA rho center c m := by
    calc
      (∫ y : ℝ in tail, f y) ≤
          ∫ y : ℝ in tail, |f y| :=
        setIntegral_mono_on hfTail hfTail.abs htailMeasurable
          (fun y _ => le_abs_self (f y))
      _ ≤
          ∫ y : ℝ in tail, (|fTarget y| + |fMissing y|) := by
        apply setIntegral_mono_on hfTail.abs
          (hfTargetTail.abs.add hfMissingTail.abs) htailMeasurable
        intro y _hy
        have hfEq : f y = fTarget y + fMissing y := by
          dsimp [f, fTarget, fMissing, kernel, targetA, missingA, center, c]
          unfold centeredSharpenedProjectedPsiKernel
          ring
        rw [hfEq]
        exact abs_add_le _ _
      _ =
          projectedPsiTailRemainderAtCenter q d targetA rho m +
            relativeProjectedPsiTailRemainderAtCenter q d missingA rho center c m := by
        rw [integral_add hfTargetTail.abs hfMissingTail.abs]
        simp only [projectedPsiTailRemainderAtCenter,
          relativeProjectedPsiTailRemainderAtCenter, tail, window,
          fTarget, fMissing]
  have hdecompose :
      (∫ y : ℝ in window, f y) +
          ∫ y : ℝ in tail, f y =
        ∫ y : ℝ in Set.Ioi 0, f y := by
    have h :=
      integral_inter_add_diff hwindowMeasurable hfIoi
    change
      (∫ y : ℝ in Set.Ioi 0 ∩ window, f y) +
          ∫ y : ℝ in tail, f y =
        ∫ y : ℝ in Set.Ioi 0, f y at h
    rw [Set.inter_eq_right.mpr hwindowSubset] at h
    exact h
  have htargetEq :=
    neg_re_localizedPsiGaussianAverageAtCenter_div_pi_eq
      q targetA hmPos hrhoRe0
  have hmissingEq :=
    neg_re_mul_localizedPsiGaussianAverageAtCenter_div_pi_eq
      q c missingA hmPos hrho0 hcenterRe0 hcenterRe
  have hpairEq :
      -((localizedPsiGaussianAverageAtCenter q targetA rho m +
          c * localizedPsiGaussianAverageAtCenter q missingA center m).re) /
          Real.pi =
        ∫ y : ℝ in Set.Ioi 0, f y := by
    calc
      -((localizedPsiGaussianAverageAtCenter q targetA rho m +
          c * localizedPsiGaussianAverageAtCenter q missingA center m).re) /
            Real.pi =
          -(localizedPsiGaussianAverageAtCenter q targetA rho m).re / Real.pi +
            -(c * localizedPsiGaussianAverageAtCenter q missingA center m).re /
              Real.pi := by
        rw [Complex.add_re]
        ring
      _ =
          (∫ y : ℝ in Set.Ioi 0, fTarget y) +
            ∫ y : ℝ in Set.Ioi 0, fMissing y := by
        rw [htargetEq, hmissingEq]
      _ = ∫ y : ℝ in Set.Ioi 0, fTarget y + fMissing y := by
        exact (integral_add hfTargetIoi hfMissingIoi).symm
      _ = ∫ y : ℝ in Set.Ioi 0, f y := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro y _hy
        dsimp [f, fTarget, fMissing, kernel, targetA, missingA, center, c]
        unfold centeredSharpenedProjectedPsiKernel
        ring
  dsimp only [targetA, missingA, center, c] at *
  rw [hpairEq, ← hdecompose]
  calc
    (∫ y : ℝ in window, f y) + ∫ y : ℝ in tail, f y ≤
        centeredNormalizedWindowFirstMoment q d rho
            (centeredSharpenedProjectedPsiKernel q rho k) m +
          (projectedPsiTailRemainderAtCenter q d
              (centeredSharpenedTargetFilter q rho) rho m +
            relativeProjectedPsiTailRemainderAtCenter q d
              (centeredSharpenedMissingFilter q rho k) rho
              (missingHarmonicContourCenter rho k)
              (missingHarmonicContourCoefficient rho k) m) :=
      add_le_add hinside htail
    _ = _ := by ring

/--
Taking the window supremum in the first-moment contour bound recovers the
original pointwise-localization inequality.
-/
private theorem eventually_centeredSharpenedProjectedPsiWindow_upper_bound
    (q d : ℝ) {rho : ℂ} {k : ℕ}
    (hd : 0 < d) (hdq : d < q)
    (hrhoRe0 : 0 < rho.re) (hrhoRe1 : rho.re < 1)
    (hgamma : 0 < rho.im) :
    ∀ᶠ m : ℝ in atTop,
      -((localizedPsiGaussianAverageAtCenter q (centeredSharpenedTargetFilter q rho) rho m +
          missingHarmonicContourCoefficient rho k *
            localizedPsiGaussianAverageAtCenter q
              (centeredSharpenedMissingFilter q rho k)
              (missingHarmonicContourCenter rho k) m).re) / Real.pi ≤
        centeredNormalizedWindowSup q d rho m *
            centeredSharpenedProjectedPsiCoefficient q rho k m +
          projectedPsiTailRemainderAtCenter q d
              (centeredSharpenedTargetFilter q rho) rho m +
          relativeProjectedPsiTailRemainderAtCenter q d
              (centeredSharpenedMissingFilter q rho k) rho
              (missingHarmonicContourCenter rho k)
              (missingHarmonicContourCoefficient rho k) m := by
  let targetA := centeredSharpenedTargetFilter q rho
  let center := missingHarmonicContourCenter rho k
  let missingA := centeredSharpenedMissingFilter q rho k
  let c := missingHarmonicContourCoefficient rho k
  have hrho0 : rho ≠ 0 := ne_zero_of_re_pos hrhoRe0
  have hcenterRe : center.re = rho.re := by
    dsimp [center, missingHarmonicContourCenter]
    exact oddHarmonicPoint_re rho.re rho.im k
  have hcenterRe0 : 0 < center.re := hcenterRe.symm ▸ hrhoRe0
  have hbddEventual :=
    eventually_bddAbove_centeredNormalizedWindowValues
      q d hd hdq (u := rho.re) (v := rho.im) hrhoRe0 hrhoRe1
  have hrhoEq : (rho.re : ℂ) + I * rho.im = rho := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  have hfirst :=
    eventually_centeredSharpenedProjectedPsiWindow_firstMoment_bound
      q d hd hdq (rho := rho) (k := k) hrhoRe0 hrhoRe1 hgamma
  filter_upwards [
    eventually_ge_atTop (1 : ℝ),
    hbddEventual,
    hfirst] with m hm hbdd hfirstM
  rw [hrhoEq] at hbdd
  have hmPos : 0 < m := zero_lt_one.trans_le hm
  let kernel : ℝ → ℝ := centeredSharpenedProjectedPsiKernel q rho k m
  let fTarget : ℝ → ℝ := fun y =>
    normalizedPsiError rho y * projectedPsiKernelAtCenter q targetA rho m y
  let fMissing : ℝ → ℝ := fun y =>
    normalizedPsiError rho y *
      relativeProjectedPsiKernelAtCenter q missingA rho center c m y
  let f : ℝ → ℝ := fun y => normalizedPsiError rho y * kernel y
  let window : Set ℝ := localizedGaussianLogWindow q d m
  have hwindowMeasurable : MeasurableSet window := measurableSet_Icc
  have hwindowSubset : window ⊆ Set.Ioi (0 : ℝ) := by
    intro y hy
    exact Set.mem_Ioi.mpr (by
      have hleft : 0 < (q - d) * m :=
        mul_pos (sub_pos.mpr hdq) hmPos
      linarith [hy.1])
  have hfTargetIoi : IntegrableOn fTarget (Set.Ioi 0) := by
    simpa only [fTarget, targetA] using
      integrableOn_normalizedPsiError_mul_projectedPsiKernelAtCenter
        q (centeredSharpenedTargetFilter q rho) hmPos hrhoRe0
  have hfMissingIoi : IntegrableOn fMissing (Set.Ioi 0) := by
    simpa only [fMissing, missingA, center, c] using
      integrableOn_normalizedPsiError_mul_relativeProjectedPsiKernelAtCenter
        q (missingHarmonicContourCoefficient rho k)
        (centeredSharpenedMissingFilter q rho k) hmPos hrhoRe0 hcenterRe0
        hcenterRe
  have hfIoi : IntegrableOn f (Set.Ioi 0) := by
    have hadd := hfTargetIoi.add hfMissingIoi
    apply hadd.congr_fun _ measurableSet_Ioi
    intro y _hy
    dsimp [f, fTarget, fMissing, kernel, targetA, missingA, center, c]
    unfold centeredSharpenedProjectedPsiKernel
    ring
  have hfWindow : IntegrableOn f window :=
    hfIoi.mono_set hwindowSubset
  have hkernelInt : Integrable kernel := by
    dsimp [kernel]
    unfold centeredSharpenedProjectedPsiKernel
    exact
      (integrable_centeredProjectedPsiKernel
        q targetA rho hmPos).add
        (integrable_centeredRelativeProjectedPsiKernel
          q missingA rho center c hmPos)
  have hkernelWindow : IntegrableOn (fun y => |kernel y|) window :=
    hkernelInt.abs.integrableOn
  have hsupNonneg :
      0 ≤ centeredNormalizedWindowSup q d rho m := by
    have hvalue :
        |normalizedPsiError rho (q * m)| ∈
          centeredNormalizedWindowValues q d rho m := by
      exact ⟨q * m, ⟨by nlinarith [mul_pos hd hmPos],
        by nlinarith [mul_pos hd hmPos]⟩, rfl⟩
    exact (abs_nonneg _).trans (le_csSup hbdd hvalue)
  have hfirstLe :
      centeredNormalizedWindowFirstMoment q d rho
          (centeredSharpenedProjectedPsiKernel q rho k) m ≤
        centeredNormalizedWindowSup q d rho m *
          centeredSharpenedProjectedPsiCoefficient q rho k m := by
    have hmono :
        centeredNormalizedWindowFirstMoment q d rho
            (centeredSharpenedProjectedPsiKernel q rho k) m ≤
          ∫ y : ℝ in window,
            centeredNormalizedWindowSup q d rho m * |kernel y| := by
      have hsourceInt :
          IntegrableOn
            (fun y =>
              |normalizedPsiError rho y| * |kernel y|)
            window := by
        apply hfWindow.abs.congr
        filter_upwards with y
        dsimp [f]
        rw [abs_mul]
      unfold centeredNormalizedWindowFirstMoment
      apply setIntegral_mono_on hsourceInt
        (hkernelWindow.const_mul
          (centeredNormalizedWindowSup q d rho m))
        measurableSet_Icc
      intro y hy
      have hvalue :
          |normalizedPsiError rho y| ∈
            centeredNormalizedWindowValues q d rho m :=
        ⟨y, hy, rfl⟩
      exact mul_le_mul_of_nonneg_right
        (le_csSup hbdd hvalue) (abs_nonneg _)
    have hmass :
        (∫ y : ℝ in window, |kernel y|) ≤
          ∫ y : ℝ, |kernel y| :=
      setIntegral_le_integral hkernelInt.abs
        (Filter.Eventually.of_forall fun y => abs_nonneg (kernel y))
    calc
      centeredNormalizedWindowFirstMoment q d rho
          (centeredSharpenedProjectedPsiKernel q rho k) m ≤
          centeredNormalizedWindowSup q d rho m *
            ∫ y : ℝ in window, |kernel y| := by
        simpa only [integral_const_mul] using hmono
      _ ≤ centeredNormalizedWindowSup q d rho m *
          ∫ y : ℝ, |kernel y| :=
        mul_le_mul_of_nonneg_left hmass hsupNonneg
      _ = centeredNormalizedWindowSup q d rho m *
          centeredSharpenedProjectedPsiCoefficient q rho k m := by
        rfl
  exact hfirstM.trans
    (by
      gcongr)

/--
The final paired true-zeta contour package.  The construction is implemented
after the coefficient limit and the two selected residue limits have been
assembled.
-/
noncomputable def sharpenedCenteredLocalizedContourData
    (q d : ℝ) {rho : ℂ} {k : ℕ}
    (hq : 16 ≤ q) (hd : 0 < d) (hdq : d < q)
    (hmargin : 16 * (q + d) ≤ d ^ 2)
    (hrhoRe0 : 0 < rho.re) (hrhoRe1 : rho.re < 1)
    (hgamma : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (hmissing :
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0) :
    CenteredLocalizedContourData q d rho
      (analyticOrderNatAt riemannZeta rho : ℝ)
      (sharpenedMissingHarmonicDenominator k) := by
  let targetA := centeredSharpenedTargetFilter q rho
  let center := missingHarmonicContourCenter rho k
  let missingA := centeredSharpenedMissingFilter q rho k
  let c := missingHarmonicContourCoefficient rho k
  let multiplicity : ℝ := analyticOrderNatAt riemannZeta rho
  let zeroPair : ℝ → ℂ := fun m =>
    selectedLocalizedZeroResidueSumAtCenter q targetA rho.re rho.im m +
      c * selectedLocalizedZeroResidueSumAtCenter q missingA rho.re center.im m
  let contourPair : ℝ → ℂ := fun m =>
    selectedLocalizedContourRemainderAtCenter q targetA rho.re rho.im m +
      c * selectedLocalizedContourRemainderAtCenter q missingA rho.re center.im m
  let psiTail : ℝ → ℝ := fun m =>
    projectedPsiTailRemainderAtCenter q d targetA rho m +
      relativeProjectedPsiTailRemainderAtCenter q d missingA rho center c m
  let remainder : ℝ → ℝ := fun m =>
    psiTail m + ‖contourPair m‖ / Real.pi
  have hrho0 : rho ≠ 0 := ne_zero_of_re_pos hrhoRe0
  have hrhoEq : (rho.re : ℂ) + I * rho.im = rho := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  have hcenterRe : center.re = rho.re := by
    dsimp [center, missingHarmonicContourCenter]
    exact oddHarmonicPoint_re rho.re rho.im k
  have hcenterEq : (rho.re : ℂ) + I * center.im = center := by
    apply Complex.ext
    · simpa [Complex.mul_re] using hcenterRe.symm
    · simp [Complex.mul_im]
  have hzeroTarget :
      Tendsto
        (selectedLocalizedZeroResidueSumAtCenter q targetA rho.re rho.im)
        atTop (𝓝 (multiplicity : ℂ)) := by
    have hzero' :
        riemannZeta ((rho.re : ℂ) + I * rho.im) = 0 := by
      rw [hrhoEq]
      exact hzero
    have h :=
      tendsto_selectedLocalizedZeroResidueSumAtCenter_nearZeroFilter q
        hq hrhoRe0 hrhoRe1 hzero'
    rw [hrhoEq] at h
    simpa [targetA, centeredSharpenedTargetFilter, multiplicity] using h
  have hzeroMissing :
      Tendsto
        (selectedLocalizedZeroResidueSumAtCenter q missingA rho.re center.im)
        atTop (𝓝 0) := by
    have hmissing' :
        riemannZeta ((rho.re : ℂ) + I * center.im) ≠ 0 := by
      rw [hcenterEq]
      exact hmissing
    have h :=
      tendsto_selectedLocalizedZeroResidueSumAtCenter_nearZeroFilter_of_ne_zero q
        hq hrhoRe0 hrhoRe1 hmissing'
    rw [hcenterEq] at h
    simpa [missingA, centeredSharpenedMissingFilter] using h
  have hzeroPair :
      Tendsto zeroPair atTop (𝓝 (multiplicity : ℂ)) := by
    have hcMissing :
        Tendsto
          (fun m =>
            c * selectedLocalizedZeroResidueSumAtCenter q
              missingA rho.re center.im m)
          atTop (𝓝 0) := by
      simpa using hzeroMissing.const_mul c
    have h :=
      hzeroTarget.add hcMissing
    simpa [zeroPair] using h
  have hsignal :
      Tendsto (fun m => 2 * (zeroPair m).re)
        atTop (𝓝 (2 * multiplicity)) := by
    have hre :
        Tendsto (fun m => (zeroPair m).re)
          atTop (𝓝 multiplicity) := by
      simpa using
        Complex.continuous_re.continuousAt.tendsto.comp hzeroPair
    exact tendsto_const_nhds.mul hre
  have hcoefficient :=
    tendsto_centeredSharpenedProjectedPsiCoefficient
      q (rho := rho) (k := k) hrho0 hgamma
  have hcoefficientPos :
      ∀ᶠ m : ℝ in atTop,
        0 < centeredSharpenedProjectedPsiCoefficient q rho k m := by
    have hlimitPos :
        0 < 2 * sharpenedMissingHarmonicDenominator k := by
      exact mul_pos (by norm_num) (sharpenedMissingHarmonicDenominator_pos k)
    exact (tendsto_order.1 hcoefficient).1 0 hlimitPos
  have htargetRemainder :
      Tendsto
        (selectedLocalizedContourRemainderAtCenter q
          targetA rho.re rho.im)
        atTop (𝓝 0) :=
    tendsto_selectedLocalizedContourRemainderAtCenter q
      targetA hq hrhoRe0 hrhoRe1 rho.im
  have hmissingRemainder :
      Tendsto
        (selectedLocalizedContourRemainderAtCenter q
          missingA rho.re center.im)
        atTop (𝓝 0) :=
    tendsto_selectedLocalizedContourRemainderAtCenter q
      missingA hq hrhoRe0 hrhoRe1 center.im
  have hcontourPair :
      Tendsto contourPair atTop (𝓝 0) := by
    have hcRemainder :
        Tendsto
          (fun m =>
            c * selectedLocalizedContourRemainderAtCenter q
              missingA rho.re center.im m)
          atTop (𝓝 0) := by
      simpa using hmissingRemainder.const_mul c
    have h :=
      htargetRemainder.add hcRemainder
    simpa [contourPair] using h
  have hcontourNorm :
      Tendsto (fun m => ‖contourPair m‖ / Real.pi)
        atTop (𝓝 0) := by
    have hnorm :
        Tendsto (fun m => ‖contourPair m‖)
          atTop (𝓝 0) := by
      simpa using tendsto_norm.comp hcontourPair
    simpa using hnorm.div_const Real.pi
  have htargetTail :
      Tendsto
        (projectedPsiTailRemainderAtCenter q d targetA rho)
        atTop (𝓝 0) := by
    simpa [hrhoEq] using
      tendsto_projectedPsiTailRemainderAtCenter
        q d targetA (lt_of_lt_of_le (by norm_num) hq)
          hd hdq hmargin hrhoRe0 hrhoRe1 rho.im
  have hmissingTail :
      Tendsto
        (relativeProjectedPsiTailRemainderAtCenter q d
          missingA rho center c)
        atTop (𝓝 0) := by
    simpa [hrhoEq, hcenterEq] using
      tendsto_relativeProjectedPsiTailRemainderAtCenter
        q d c missingA (lt_of_lt_of_le (by norm_num) hq)
          hd hdq hmargin hrhoRe0 hrhoRe1 rho.im center.im
  have hpsiTail :
      Tendsto psiTail atTop (𝓝 0) := by
    simpa [psiTail] using htargetTail.add hmissingTail
  have hremainder :
      Tendsto remainder atTop (𝓝 0) := by
    simpa [remainder] using hpsiTail.add hcontourNorm
  have hwindow :
      ∀ᶠ m : ℝ in atTop,
        BddAbove (centeredNormalizedWindowValues q d rho m) := by
    simpa [hrhoEq] using
      eventually_bddAbove_centeredNormalizedWindowValues
        q d hd hdq (u := rho.re) (v := rho.im)
          hrhoRe0 hrhoRe1
  have hkernelMeasurable :
      ∀ᶠ m : ℝ in atTop,
        Measurable (centeredSharpenedProjectedPsiKernel q rho k m) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with m hm
    unfold centeredSharpenedProjectedPsiKernel
      relativeProjectedPsiKernelAtCenter
    exact
      (continuous_projectedPsiKernelAtCenter
        q targetA rho hm).add
        ((continuous_projectedPsiKernelAtCenter
          q (C c * missingA) center hm).const_mul
            (‖center‖ / ‖rho‖)) |>.measurable
  have hkernelIntegrable :
      ∀ᶠ m : ℝ in atTop,
        Integrable (centeredSharpenedProjectedPsiKernel q rho k m) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with m hm
    unfold centeredSharpenedProjectedPsiKernel
    exact
      (integrable_centeredProjectedPsiKernel
        q targetA rho hm).add
        (integrable_centeredRelativeProjectedPsiKernel
          q missingA rho center c hm)
  have herrorMeasurable :
      Measurable (normalizedPsiError rho) := by
    have hpsi : Measurable chebyshevPsi := by
      simpa only [chebyshevPsi_eq_mathlib] using
        Chebyshev.psi_mono.measurable
    unfold normalizedPsiError
    fun_prop
  have hsecondMomentIntegrable :
      ∀ᶠ m : ℝ in atTop,
        IntegrableOn
          (fun y =>
            normalizedPsiError rho y ^ 2 *
              |centeredSharpenedProjectedPsiKernel q rho k m y|)
          (localizedGaussianLogWindow q d m) := by
    filter_upwards [
      eventually_ge_atTop (1 : ℝ),
      hwindow,
      hkernelMeasurable,
      hkernelIntegrable] with m hm hbdd hkMeas hkInt
    let window : Set ℝ := localizedGaussianLogWindow q d m
    let kernel : ℝ → ℝ := centeredSharpenedProjectedPsiKernel q rho k m
    have hmPos : 0 < m := zero_lt_one.trans_le hm
    have hwindowMeasurable : MeasurableSet window := measurableSet_Icc
    have hsupNonneg :
        0 ≤ centeredNormalizedWindowSup q d rho m := by
      have hvalue :
          |normalizedPsiError rho (q * m)| ∈
            centeredNormalizedWindowValues q d rho m := by
        exact ⟨q * m, ⟨by nlinarith [mul_pos hd hmPos],
          by nlinarith [mul_pos hd hmPos]⟩, rfl⟩
      exact (abs_nonneg _).trans (le_csSup hbdd hvalue)
    have hsourceAES :
        AEStronglyMeasurable
          (fun y =>
            normalizedPsiError rho y ^ 2 * |kernel y|)
          (volume.restrict window) :=
      ((herrorMeasurable.pow_const 2).mul hkMeas.norm)
        |>.aestronglyMeasurable
    have hmajorInt :
        Integrable
          (fun y =>
            centeredNormalizedWindowSup q d rho m ^ 2 *
              |kernel y|) :=
      hkInt.abs.const_mul _
    refine hmajorInt.integrableOn.mono' hsourceAES ?_
    filter_upwards [ae_restrict_mem hwindowMeasurable] with y hy
    have hvalue :
        |normalizedPsiError rho y| ∈
          centeredNormalizedWindowValues q d rho m :=
      ⟨y, hy, rfl⟩
    have herrorLe :
        |normalizedPsiError rho y| ≤
          centeredNormalizedWindowSup q d rho m :=
      le_csSup hbdd hvalue
    have hsqLe :
        normalizedPsiError rho y ^ 2 ≤
          centeredNormalizedWindowSup q d rho m ^ 2 := by
      nlinarith [sq_abs (normalizedPsiError rho y),
        abs_nonneg (normalizedPsiError rho y)]
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (sq_nonneg _) (abs_nonneg _))]
    exact mul_le_mul_of_nonneg_right hsqLe (abs_nonneg _)
  have hfirstPsi :=
    eventually_centeredSharpenedProjectedPsiWindow_firstMoment_bound
      q d hd hdq (rho := rho) (k := k)
        hrhoRe0 hrhoRe1 hgamma
  have hfirstMomentBound :
      ∀ᶠ m : ℝ in atTop,
        2 * (zeroPair m).re ≤
          centeredNormalizedWindowFirstMoment q d rho
              (centeredSharpenedProjectedPsiKernel q rho k) m +
            remainder m := by
    filter_upwards [
      eventually_ge_atTop (1 : ℝ),
      eventually_ge_atTop (targetA.natDegree : ℝ),
      eventually_ge_atTop (missingA.natDegree : ℝ),
      eventually_ge_atTop q,
      hfirstPsi] with m hm htargetDegree hmissingDegree hmq hpsiM
    have hqPos : 0 < q := lt_of_lt_of_le (by norm_num) hq
    have hqScale : q ≤ 27 * m ^ 2 := by
      have hm0 : 0 ≤ m := zero_le_one.trans hm
      nlinarith [mul_nonneg hqPos.le (sub_nonneg.mpr hmq)]
    have htargetValid : centeredLocalizedContourScaleValid q targetA rho.re m :=
      ⟨hq, hrhoRe0, hrhoRe1, hm, htargetDegree, hqScale⟩
    have hmissingValid : centeredLocalizedContourScaleValid q missingA rho.re m :=
      ⟨hq, hrhoRe0, hrhoRe1, hm, hmissingDegree, hqScale⟩
    have htargetContour :=
      selected_localizedPsiGaussianAverageAtCenter_eq q
        targetA (u := rho.re) (v := rho.im) (m := m) htargetValid
    have hmissingContour :=
      selected_localizedPsiGaussianAverageAtCenter_eq q
        missingA (u := rho.re) (v := center.im) (m := m) hmissingValid
    let L : ℂ :=
      localizedPsiGaussianAverageAtCenter q targetA rho m +
        c * localizedPsiGaussianAverageAtCenter q missingA center m
    have hcontourIdentity :
        L = -(2 * Real.pi : ℂ) * zeroPair m + contourPair m := by
      rw [hrhoEq] at htargetContour
      rw [hcenterEq] at hmissingContour
      dsimp [L, zeroPair, contourPair]
      rw [htargetContour, hmissingContour]
      ring
    have hsignalEq :
        2 * (zeroPair m).re =
          -(L.re) / Real.pi + (contourPair m).re / Real.pi := by
      have hscaleRe :
          (-(2 * Real.pi : ℂ) * zeroPair m).re =
            -2 * Real.pi * (zeroPair m).re := by
        norm_num [Complex.mul_re]
      have hre :
          L.re =
            -2 * Real.pi * (zeroPair m).re + (contourPair m).re := by
        calc
          L.re =
              (-(2 * Real.pi : ℂ) * zeroPair m +
                contourPair m).re :=
            congrArg Complex.re hcontourIdentity
          _ = _ := by rw [Complex.add_re, hscaleRe]
      field_simp [Real.pi_ne_zero]
      nlinarith [hre]
    have hcontourLe :
        (contourPair m).re / Real.pi ≤
          ‖contourPair m‖ / Real.pi :=
      (div_le_div_iff_of_pos_right Real.pi_pos).2
        (Complex.re_le_norm _)
    have hpsiM' :
        -(L.re) / Real.pi ≤
          centeredNormalizedWindowFirstMoment q d rho
              (centeredSharpenedProjectedPsiKernel q rho k) m +
            psiTail m := by
      dsimp [L, psiTail, targetA, missingA, center, c]
      convert hpsiM using 1 <;> ring
    rw [hsignalEq]
    change
      -L.re / Real.pi + (contourPair m).re / Real.pi ≤
        centeredNormalizedWindowFirstMoment q d rho
            (centeredSharpenedProjectedPsiKernel q rho k) m +
          (psiTail m + ‖contourPair m‖ / Real.pi)
    calc
      -L.re / Real.pi + (contourPair m).re / Real.pi ≤
          (centeredNormalizedWindowFirstMoment q d rho
              (centeredSharpenedProjectedPsiKernel q rho k) m +
            psiTail m) + ‖contourPair m‖ / Real.pi :=
        add_le_add hpsiM' hcontourLe
      _ = _ := by ring
  refine {
    radius_nonneg := hd.le
    kernel := centeredSharpenedProjectedPsiKernel q rho k
    signal := fun m => 2 * (zeroPair m).re
    coefficient := centeredSharpenedProjectedPsiCoefficient q rho k
    remainder := remainder
    eventually_kernel_measurable := hkernelMeasurable
    eventually_kernel_integrable := hkernelIntegrable
    coefficient_eq_kernel_mass := fun _ => rfl
    eventually_second_moment_integrable := hsecondMomentIntegrable
    eventually_first_moment_bound := hfirstMomentBound
    signal_tendsto := hsignal
    coefficient_tendsto := hcoefficient
    remainder_tendsto := hremainder
    eventually_coefficient_pos := hcoefficientPos
    eventually_window_bddAbove := hwindow
    eventually_upper_bound := ?_
  }
  have hpsi :=
    eventually_centeredSharpenedProjectedPsiWindow_upper_bound
      q d hd hdq (rho := rho) (k := k)
        hrhoRe0 hrhoRe1 hgamma
  filter_upwards [
    eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (targetA.natDegree : ℝ),
    eventually_ge_atTop (missingA.natDegree : ℝ),
    eventually_ge_atTop q,
    hpsi] with m hm htargetDegree hmissingDegree hmq hpsiM
  have hqPos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hqScale : q ≤ 27 * m ^ 2 := by
    have hm0 : 0 ≤ m := zero_le_one.trans hm
    nlinarith [mul_nonneg hqPos.le (sub_nonneg.mpr hmq)]
  have htargetValid : centeredLocalizedContourScaleValid q targetA rho.re m :=
    ⟨hq, hrhoRe0, hrhoRe1, hm, htargetDegree, hqScale⟩
  have hmissingValid : centeredLocalizedContourScaleValid q missingA rho.re m :=
    ⟨hq, hrhoRe0, hrhoRe1, hm, hmissingDegree, hqScale⟩
  have htargetContour :=
    selected_localizedPsiGaussianAverageAtCenter_eq q
      targetA (u := rho.re) (v := rho.im) (m := m) htargetValid
  have hmissingContour :=
    selected_localizedPsiGaussianAverageAtCenter_eq q
      missingA (u := rho.re) (v := center.im) (m := m) hmissingValid
  let L : ℂ :=
    localizedPsiGaussianAverageAtCenter q targetA rho m +
      c * localizedPsiGaussianAverageAtCenter q missingA center m
  have hcontourIdentity :
      L =
        -(2 * Real.pi : ℂ) * zeroPair m + contourPair m := by
    rw [hrhoEq] at htargetContour
    rw [hcenterEq] at hmissingContour
    dsimp [L, zeroPair, contourPair]
    rw [htargetContour, hmissingContour]
    ring
  have hsignalEq :
      2 * (zeroPair m).re =
        -(L.re) / Real.pi + (contourPair m).re / Real.pi := by
    have hscaleRe :
        (-(2 * Real.pi : ℂ) * zeroPair m).re =
          -2 * Real.pi * (zeroPair m).re := by
      norm_num [Complex.mul_re]
    have hre :
        L.re =
          -2 * Real.pi * (zeroPair m).re + (contourPair m).re := by
      calc
        L.re =
            (-(2 * Real.pi : ℂ) * zeroPair m +
              contourPair m).re :=
          congrArg Complex.re hcontourIdentity
        _ = _ := by rw [Complex.add_re, hscaleRe]
    field_simp [Real.pi_ne_zero]
    nlinarith [hre]
  have hcontourLe :
      (contourPair m).re / Real.pi ≤
        ‖contourPair m‖ / Real.pi :=
    (div_le_div_iff_of_pos_right Real.pi_pos).2
      (Complex.re_le_norm _)
  change
    2 * (zeroPair m).re ≤
      centeredNormalizedWindowSup q d rho m *
          centeredSharpenedProjectedPsiCoefficient q rho k m +
        remainder m
  have hpsiM' :
      -(L.re) / Real.pi ≤
        centeredNormalizedWindowSup q d rho m *
            centeredSharpenedProjectedPsiCoefficient q rho k m +
          psiTail m := by
    dsimp [L, psiTail, targetA, missingA, center, c]
    convert hpsiM using 1 <;> ring
  rw [hsignalEq]
  change
    -L.re / Real.pi + (contourPair m).re / Real.pi ≤
      centeredNormalizedWindowSup q d rho m *
          centeredSharpenedProjectedPsiCoefficient q rho k m +
        (psiTail m + ‖contourPair m‖ / Real.pi)
  calc
    -L.re / Real.pi + (contourPair m).re / Real.pi ≤
        (centeredNormalizedWindowSup q d rho m *
            centeredSharpenedProjectedPsiCoefficient q rho k m +
          psiTail m) + ‖contourPair m‖ / Real.pi :=
      add_le_add hpsiM' hcontourLe
    _ = _ := by ring

/-- A zeta zero and a missing odd harmonic force every constant below the
exact multiplicity-sensitive ratio in every sufficiently late centered
window. -/
theorem eventually_exists_normalizedPsiError_in_centeredWindow_gt
    {q d : ℝ} {rho : ℂ} {k : ℕ}
    (hq : 16 ≤ q) (hd : 0 < d) (hdq : d < q)
    (hmargin : 16 * (q + d) ≤ d ^ 2)
    (hrhoRe0 : 0 < rho.re) (hrhoRe1 : rho.re < 1)
    (hgamma : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (hmissing :
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0)
    {C : ℝ}
    (hC :
      C <
        (analyticOrderNatAt riemannZeta rho : ℝ) /
          sharpenedMissingHarmonicDenominator k) :
    ∀ᶠ m : ℝ in atTop,
      ∃ y ∈ localizedGaussianLogWindow q d m,
        C < |normalizedPsiError rho y| := by
  have hrho1 : rho ≠ 1 := by
    intro hrho
    have hre := congrArg Complex.re hrho
    norm_num at hre
    linarith
  have hmultiplicity :
      0 < (analyticOrderNatAt riemannZeta rho : ℝ) := by
    exact_mod_cast
      ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero
        hrho1 hzero
  have hmean := sharpenedMissingHarmonicDenominator_pos k
  exact
    (sharpenedCenteredLocalizedContourData
      q d hq hd hdq hmargin
        hrhoRe0 hrhoRe1 hgamma hzero hmissing
      |>.eventually_exists_normalizedPsiError_gt
        hmultiplicity hmean hC)

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
