import PrimeNumberTheorem.VKEdgePiOverTwoFarZeroDecay
import PrimeNumberTheorem.VKEdgePiOverTwoGaussianDual
import PrimeNumberTheorem.VKEdgePiOverTwoProjectedPsiWindow

open Complex Filter MeasureTheory Polynomial Set Topology

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- The empty contour center at the selected missing odd harmonic. -/
def missingHarmonicContourCenter (rho : ℂ) (k : ℕ) : ℂ :=
  oddHarmonicPoint rho.re rho.im k

/--
The complex coefficient which turns the empty-center contour into the
`(2k+1)`-st correction in `sharpenedPsiAbelKernel`.
-/
def missingHarmonicContourCoefficient (rho : ℂ) (k : ℕ) : ℂ :=
  let n : ℝ := ((2 * k + 1 : ℕ) : ℝ)
  ((((-1 : ℝ) ^ k) / (2 * n) : ℝ) : ℂ) *
    (‖rho‖ : ℂ) *
    Complex.exp (((n * zeroResiduePhase rho : ℝ) : ℂ) * I) /
    missingHarmonicContourCenter rho k

/-- Fixed near-zero filter at the target center. -/
def sharpenedTargetFilter (rho : ℂ) : ℂ[X] :=
  localizedNearZeroFilter rho 5

/-- Fixed near-zero filter at the missing odd-harmonic center. -/
def sharpenedMissingFilter (rho : ℂ) (k : ℕ) : ℂ[X] :=
  localizedNearZeroFilter (missingHarmonicContourCenter rho k) 5

/--
The real kernel obtained by pairing the target contour with the empty
missing-harmonic contour, normalized against the target zero.
-/
def sharpenedProjectedPsiKernel
    (rho : ℂ) (k : ℕ) (m y : ℝ) : ℝ :=
  projectedPsiKernel (sharpenedTargetFilter rho) rho m y +
    relativeProjectedPsiKernel
      (sharpenedMissingFilter rho k) rho
      (missingHarmonicContourCenter rho k)
      (missingHarmonicContourCoefficient rho k) m y

/--
Absolute mass of the sharpened paired kernel on the full logarithmic line.
The part outside `[4m,28m]` is recorded separately as a vanishing
`psiRemainder`, so this full mass is a valid coefficient in the localized
window estimate.
-/
def sharpenedProjectedPsiCoefficient
    (rho : ℂ) (k : ℕ) (m : ℝ) : ℝ :=
  ∫ y : ℝ,
    |sharpenedProjectedPsiKernel rho k m y|

private def sharpenedLeadingKernel
    (rho : ℂ) (k : ℕ) (m y : ℝ) : ℝ :=
  2 * normalizedGaussian m (16 * m - y) *
    sharpenedPsiAbelKernel rho rho.im k y

private def projectedPsiLeadingKernel
    (w : ℂ) (m y : ℝ) : ℝ :=
  -(2 / ‖w‖) *
    (Complex.exp (-(I * (w.im : ℂ) * (y : ℂ))) *
      (w * (normalizedGaussian m (16 * m - y) : ℂ))).re

private def relativeProjectedPsiLeadingKernel
    (target center c : ℂ) (m y : ℝ) : ℝ :=
  (‖center‖ / ‖target‖) *
    (-(2 / ‖center‖) *
      (Complex.exp (-(I * (center.im : ℂ) * (y : ℂ))) *
        (c * center *
          (normalizedGaussian m (16 * m - y) : ℂ))).re)

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
    {rho : ℂ} {k : ℕ} (hrho0 : rho ≠ 0)
    (hgamma : 0 < rho.im) (m y : ℝ) :
    relativeProjectedPsiLeadingKernel rho
        (missingHarmonicContourCenter rho k)
        (missingHarmonicContourCoefficient rho k) m y =
      -(((-1 : ℝ) ^ k) /
          (((2 * k + 1 : ℕ) : ℝ))) *
        normalizedGaussian m (16 * m - y) *
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
  unfold relativeProjectedPsiLeadingKernel
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
            (normalizedGaussian m (16 * m - y) : ℂ)) =
        ((((((-1 : ℝ) ^ k) / (2 * n)) * ‖rho‖ *
            normalizedGaussian m (16 * m - y) : ℝ) : ℂ) *
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
              (normalizedGaussian m (16 * m - y) : ℂ)) =
          ((((((-1 : ℝ) ^ k) / (2 * n)) * ‖rho‖ *
              normalizedGaussian m (16 * m - y) : ℝ) : ℂ) *
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
    {rho : ℂ} (hrho0 : rho ≠ 0) (m y : ℝ) :
    projectedPsiLeadingKernel rho m y =
      2 * normalizedGaussian m (16 * m - y) *
        phaseCos rho rho.im y := by
  have hrhoNorm : 0 < ‖rho‖ := norm_pos_iff.mpr hrho0
  have hpolar := Complex.norm_mul_exp_arg_mul_I rho
  unfold projectedPsiLeadingKernel phaseCos realPhaseCos
  have hphase :
      -(2 / ‖rho‖) *
          (Complex.exp
              (-(I * (rho.im : ℂ) * (y : ℂ))) *
            (rho * (normalizedGaussian m (16 * m - y) : ℂ))).re =
        -2 * normalizedGaussian m (16 * m - y) *
          Real.cos (rho.arg - rho.im * y) := by
    rw [show
        Complex.exp
            (-(I * (rho.im : ℂ) * (y : ℂ))) *
              (rho *
                (normalizedGaussian m (16 * m - y) : ℂ)) =
          (((‖rho‖ * normalizedGaussian m (16 * m - y) : ℝ) : ℂ) *
            Complex.exp
              ((((rho.arg - rho.im * y : ℝ) : ℂ) * I))) by
      rw [show
          rho * (normalizedGaussian m (16 * m - y) : ℂ) =
            ((‖rho‖ : ℂ) *
              Complex.exp (((rho.arg : ℝ) : ℂ) * I)) *
            (normalizedGaussian m (16 * m - y) : ℂ) by
        rw [hpolar]]
      rw [show
          Complex.exp (-(I * (rho.im : ℂ) * (y : ℂ))) *
              (((‖rho‖ : ℂ) *
                  Complex.exp (((rho.arg : ℝ) : ℂ) * I)) *
                (normalizedGaussian m (16 * m - y) : ℂ)) =
            (((‖rho‖ * normalizedGaussian m (16 * m - y) : ℝ) : ℂ) *
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

private theorem sharpenedProjectedPsiKernel_one_eq_leading
    {rho : ℂ} {k : ℕ} (hrho0 : rho ≠ 0)
    (hgamma : 0 < rho.im) (m y : ℝ) :
    projectedPsiLeadingKernel rho m y +
        relativeProjectedPsiLeadingKernel rho
          (missingHarmonicContourCenter rho k)
          (missingHarmonicContourCoefficient rho k) m y =
      sharpenedLeadingKernel rho k m y := by
  rw [projectedPsiKernel_normalizedGaussian hrho0,
    relativeProjectedPsiKernel_normalizedGaussian hrho0 hgamma]
  unfold sharpenedLeadingKernel sharpenedPsiAbelKernel
    missingOddHarmonicKernel phaseCos realPhaseCos
  ring

private theorem abs_projectedPsiKernel_sub_one_le
    (A : ℂ[X]) {w : ℂ} (hw0 : w ≠ 0) (m y : ℝ) :
    |projectedPsiKernel A w m y -
        projectedPsiLeadingKernel w m y| ≤
      (2 / ‖w‖) *
        (‖w‖ *
            ‖polynomialGaussianKernel A m (16 * m - y) -
              (normalizedGaussian m (16 * m - y) : ℂ)‖ +
          ‖polynomialGaussianKernelDeriv A m (16 * m - y)‖) := by
  have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  unfold projectedPsiKernel projectedPsiLeadingKernel
  rw [← mul_sub]
  rw [← Complex.sub_re]
  rw [← mul_sub]
  rw [show
      w * polynomialGaussianKernel A m (16 * m - y) +
          polynomialGaussianKernelDeriv A m (16 * m - y) -
          w * (normalizedGaussian m (16 * m - y) : ℂ) =
        w *
            (polynomialGaussianKernel A m (16 * m - y) -
              (normalizedGaussian m (16 * m - y) : ℂ)) +
          polynomialGaussianKernelDeriv A m (16 * m - y) by ring]
  rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 2 / ‖w‖)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    |(Complex.exp (-(I * (w.im : ℂ) * (y : ℂ))) *
          (w *
              (polynomialGaussianKernel A m (16 * m - y) -
                (normalizedGaussian m (16 * m - y) : ℂ)) +
            polynomialGaussianKernelDeriv A m
              (16 * m - y))).re| ≤
        ‖Complex.exp (-(I * (w.im : ℂ) * (y : ℂ))) *
          (w *
              (polynomialGaussianKernel A m (16 * m - y) -
                (normalizedGaussian m (16 * m - y) : ℂ)) +
            polynomialGaussianKernelDeriv A m
              (16 * m - y))‖ :=
      abs_re_le_norm _
    _ =
        ‖w *
              (polynomialGaussianKernel A m (16 * m - y) -
                (normalizedGaussian m (16 * m - y) : ℂ)) +
            polynomialGaussianKernelDeriv A m
              (16 * m - y)‖ := by
      rw [norm_mul, Complex.norm_exp]
      norm_num [Complex.mul_re]
    _ ≤
        ‖w‖ *
            ‖polynomialGaussianKernel A m (16 * m - y) -
              (normalizedGaussian m (16 * m - y) : ℂ)‖ +
          ‖polynomialGaussianKernelDeriv A m (16 * m - y)‖ := by
      simpa only [norm_mul] using norm_add_le
        (w *
          (polynomialGaussianKernel A m (16 * m - y) -
            (normalizedGaussian m (16 * m - y) : ℂ)))
        (polynomialGaussianKernelDeriv A m (16 * m - y))

private theorem abs_relativeProjectedPsiKernel_sub_one_le
    (A : ℂ[X]) {target center c : ℂ}
    (htarget0 : target ≠ 0) (hcenter0 : center ≠ 0)
    (m y : ℝ) :
    |relativeProjectedPsiKernel A target center c m y -
        relativeProjectedPsiLeadingKernel target center c m y| ≤
      (2 * ‖c‖ / ‖target‖) *
        (‖center‖ *
            ‖polynomialGaussianKernel A m (16 * m - y) -
              (normalizedGaussian m (16 * m - y) : ℂ)‖ +
          ‖polynomialGaussianKernelDeriv A m (16 * m - y)‖) := by
  have htargetNorm : 0 < ‖target‖ := norm_pos_iff.mpr htarget0
  have hcenterNorm : 0 < ‖center‖ := norm_pos_iff.mpr hcenter0
  unfold relativeProjectedPsiKernel projectedPsiKernel
    relativeProjectedPsiLeadingKernel
  rw [polynomialGaussianKernel_C_mul,
    polynomialGaussianKernelDeriv_C_mul]
  rw [← mul_sub]
  rw [← mul_sub]
  rw [← Complex.sub_re]
  rw [← mul_sub]
  rw [show
      center * (c * polynomialGaussianKernel A m (16 * m - y)) +
            c * polynomialGaussianKernelDeriv A m (16 * m - y) -
          c * center *
            (normalizedGaussian m (16 * m - y) : ℂ) =
        c *
          (center *
              (polynomialGaussianKernel A m (16 * m - y) -
                (normalizedGaussian m (16 * m - y) : ℂ)) +
            polynomialGaussianKernelDeriv A m (16 * m - y)) by ring]
  rw [abs_mul, abs_of_nonneg
    (div_nonneg (norm_nonneg center) (norm_nonneg target))]
  rw [abs_mul, abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ 2 / ‖center‖)]
  calc
    ‖center‖ / ‖target‖ * (2 / ‖center‖ *
        |(Complex.exp (-(I * (center.im : ℂ) * (y : ℂ))) *
          (c *
            (center *
                (polynomialGaussianKernel A m (16 * m - y) -
                  (normalizedGaussian m (16 * m - y) : ℂ)) +
              polynomialGaussianKernelDeriv A m
                (16 * m - y)))).re|) ≤
        ‖center‖ / ‖target‖ * (2 / ‖center‖ *
          ‖Complex.exp (-(I * (center.im : ℂ) * (y : ℂ))) *
          (c *
            (center *
                (polynomialGaussianKernel A m (16 * m - y) -
                  (normalizedGaussian m (16 * m - y) : ℂ)) +
              polynomialGaussianKernelDeriv A m
                (16 * m - y)))‖) := by
      gcongr
      exact abs_re_le_norm _
    _ =
        (2 * ‖c‖ / ‖target‖) *
          ‖center *
              (polynomialGaussianKernel A m (16 * m - y) -
                (normalizedGaussian m (16 * m - y) : ℂ)) +
            polynomialGaussianKernelDeriv A m
              (16 * m - y)‖ := by
      rw [norm_mul, Complex.norm_exp, norm_mul]
      norm_num [Complex.mul_re]
      field_simp [htargetNorm.ne', hcenterNorm.ne']
    _ ≤
        (2 * ‖c‖ / ‖target‖) *
          (‖center‖ *
              ‖polynomialGaussianKernel A m (16 * m - y) -
                (normalizedGaussian m (16 * m - y) : ℂ)‖ +
            ‖polynomialGaussianKernelDeriv A m
              (16 * m - y)‖) := by
      gcongr
      simpa only [norm_mul] using norm_add_le
        (center *
          (polynomialGaussianKernel A m (16 * m - y) -
            (normalizedGaussian m (16 * m - y) : ℂ)))
        (polynomialGaussianKernelDeriv A m (16 * m - y))
    _ = _ := rfl

private theorem exists_sharpenedProjectedPsiKernel_sub_leading_l1_bound
    {rho : ℂ} {k : ℕ} (hrho0 : rho ≠ 0)
    (hgamma : 0 < rho.im) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ m : ℝ, 1 ≤ m →
        Integrable (fun y : ℝ =>
          |sharpenedProjectedPsiKernel rho k m y -
            sharpenedLeadingKernel rho k m y|) ∧
        (∫ y : ℝ,
            |sharpenedProjectedPsiKernel rho k m y -
              sharpenedLeadingKernel rho k m y|) ≤
            C / Real.sqrt m := by
  let targetA : ℂ[X] := sharpenedTargetFilter rho
  let center : ℂ := missingHarmonicContourCenter rho k
  let missingA : ℂ[X] := sharpenedMissingFilter rho k
  let c : ℂ := missingHarmonicContourCoefficient rho k
  have htargetEval : targetA.eval 0 = 1 := by
    exact localizedNearZeroFilter_eval_zero rho 5
  have hmissingEval : missingA.eval 0 = 1 := by
    exact localizedNearZeroFilter_eval_zero center 5
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
            ‖polynomialGaussianKernel targetA m (16 * m - y) -
              (normalizedGaussian m (16 * m - y) : ℂ)‖ +
          ‖polynomialGaussianKernelDeriv targetA m (16 * m - y)‖)
    let missingMajor : ℝ → ℝ := fun y =>
      (2 * ‖c‖ / ‖rho‖) *
        (‖center‖ *
            ‖polynomialGaussianKernel missingA m (16 * m - y) -
              (normalizedGaussian m (16 * m - y) : ℂ)‖ +
          ‖polynomialGaussianKernelDeriv missingA m (16 * m - y)‖)
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
        (((hsub.comp_sub_left (16 * m)).const_mul ‖rho‖).add
          (hderiv.comp_sub_left (16 * m))).const_mul (2 / ‖rho‖)
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
        (((hsub.comp_sub_left (16 * m)).const_mul ‖center‖).add
          (hderiv.comp_sub_left (16 * m))).const_mul
            (2 * ‖c‖ / ‖rho‖)
    have hpointwise :
        ∀ y : ℝ,
          |sharpenedProjectedPsiKernel rho k m y -
              sharpenedLeadingKernel rho k m y| ≤
            targetMajor y + missingMajor y := by
      intro y
      rw [← sharpenedProjectedPsiKernel_one_eq_leading
        hrho0 hgamma]
      unfold sharpenedProjectedPsiKernel
      calc
        |(projectedPsiKernel targetA rho m y +
              relativeProjectedPsiKernel missingA rho center c m y) -
            (projectedPsiLeadingKernel rho m y +
              relativeProjectedPsiLeadingKernel rho center c m y)| ≤
            |projectedPsiKernel targetA rho m y -
              projectedPsiLeadingKernel rho m y| +
            |relativeProjectedPsiKernel missingA rho center c m y -
              relativeProjectedPsiLeadingKernel rho center c m y| := by
          rw [show
                (projectedPsiKernel targetA rho m y +
                  relativeProjectedPsiKernel missingA rho center c m y) -
                (projectedPsiLeadingKernel rho m y +
                  relativeProjectedPsiLeadingKernel rho center c m y) =
                (projectedPsiKernel targetA rho m y -
                  projectedPsiLeadingKernel rho m y) +
                (relativeProjectedPsiKernel missingA rho center c m y -
                  relativeProjectedPsiLeadingKernel rho center c m y) by ring]
          exact abs_add_le _ _
        _ ≤ targetMajor y + missingMajor y := by
          exact add_le_add
            (abs_projectedPsiKernel_sub_one_le targetA hrho0 m y)
            (abs_relativeProjectedPsiKernel_sub_one_le
              missingA hrho0 hcenter0 m y)
    have hsourceInt :
        Integrable (fun y : ℝ =>
          |sharpenedProjectedPsiKernel rho k m y -
            sharpenedLeadingKernel rho k m y|) := by
      apply Integrable.mono' (htargetMajorInt.add hmissingMajorInt)
      · have hactual :
            Continuous
              (sharpenedProjectedPsiKernel rho k m) := by
          unfold sharpenedProjectedPsiKernel
          exact
            (continuous_projectedPsiKernel targetA rho hmPos).add
              (continuous_relativeProjectedPsiKernel
                missingA rho center c hmPos)
        have hleading :
            Continuous (sharpenedLeadingKernel rho k m) := by
          unfold sharpenedLeadingKernel sharpenedPsiAbelKernel
            missingOddHarmonicKernel normalizedGaussian
          fun_prop
        exact (hactual.sub hleading).abs.aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun y => by
          simpa [Real.norm_eq_abs, Pi.add_apply,
            abs_of_nonneg (abs_nonneg _)] using hpointwise y
    refine ⟨hsourceInt, ?_⟩
    calc
      (∫ y : ℝ,
          |sharpenedProjectedPsiKernel rho k m y -
            sharpenedLeadingKernel rho k m y|) ≤
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
          have hsubShift := hsub.comp_sub_left (16 * m)
          have hderivShift := hderiv.comp_sub_left (16 * m)
          dsimp [targetMajor]
          rw [integral_const_mul,
            integral_add (hsubShift.const_mul ‖rho‖) hderivShift,
            integral_const_mul]
          rw [MeasureTheory.integral_sub_left_eq_self
              (fun t : ℝ =>
                ‖polynomialGaussianKernel targetA m t -
                  (normalizedGaussian m t : ℂ)‖) volume (16 * m),
            MeasureTheory.integral_sub_left_eq_self
              (fun t : ℝ =>
                ‖polynomialGaussianKernelDeriv targetA m t‖)
              volume (16 * m)]
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
          have hsubShift := hsub.comp_sub_left (16 * m)
          have hderivShift := hderiv.comp_sub_left (16 * m)
          dsimp [missingMajor]
          rw [integral_const_mul,
            integral_add (hsubShift.const_mul ‖center‖) hderivShift,
            integral_const_mul]
          rw [MeasureTheory.integral_sub_left_eq_self
              (fun t : ℝ =>
                ‖polynomialGaussianKernel missingA m t -
                  (normalizedGaussian m t : ℂ)‖) volume (16 * m),
            MeasureTheory.integral_sub_left_eq_self
              (fun t : ℝ =>
                ‖polynomialGaussianKernelDeriv missingA m t‖)
              volume (16 * m)]
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
theorem tendsto_sharpenedProjectedPsiCoefficient
    {rho : ℂ} {k : ℕ} (hrho0 : rho ≠ 0)
    (hgamma : 0 < rho.im) :
    Tendsto
      (sharpenedProjectedPsiCoefficient rho k)
      atTop
      (𝓝 (2 * sharpenedMissingHarmonicDenominator k)) := by
  let actual : ℝ → ℝ → ℝ := fun m y =>
    sharpenedProjectedPsiKernel rho k m y
  let leading : ℝ → ℝ → ℝ := fun m y =>
    sharpenedLeadingKernel rho k m y
  let leadingCoefficient : ℝ → ℝ := fun m =>
    ∫ y : ℝ, |leading m y|
  obtain ⟨C, hC, herror⟩ :=
    exists_sharpenedProjectedPsiKernel_sub_leading_l1_bound
      hrho0 hgamma
  have hleadingIntegrable :
      ∀ {m : ℝ}, 0 < m → Integrable (leading m) := by
    intro m hm
    have hgaussian :
        Integrable
          (fun y : ℝ =>
            normalizedGaussian m (16 * m - y)) :=
      (integrable_normalizedGaussian hm).comp_sub_left (16 * m)
    apply Integrable.mono' (hgaussian.const_mul 4)
    · unfold leading sharpenedLeadingKernel sharpenedPsiAbelKernel
        missingOddHarmonicKernel normalizedGaussian
      fun_prop
    · exact Filter.Eventually.of_forall fun y => by
        have hq :=
          abs_sharpenedPsiAbelKernel_le_two rho rho.im k y
        have hnonneg :
            0 ≤ 2 * normalizedGaussian m (16 * m - y) :=
          mul_nonneg (by norm_num)
            (normalizedGaussian_pos hm (16 * m - y)).le
        simpa only [leading, sharpenedLeadingKernel, Real.norm_eq_abs,
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
              |sharpenedPsiAbelKernel rho rho.im k (16 * m - t)| := by
      have hqBound :
          ∀ y : ℝ,
            |sharpenedPsiAbelKernel rho rho.im k y| ≤ 2 :=
        abs_sharpenedPsiAbelKernel_le_two rho rho.im k
      have hfInt :
          Integrable (fun t : ℝ =>
            normalizedGaussian m t *
              |sharpenedPsiAbelKernel rho rho.im k
                (16 * m - t)|) := by
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
              (hqBound (16 * m - t))
              (normalizedGaussian_pos hmPos t).le |>.trans_eq (by ring)
      unfold leadingCoefficient leading sharpenedLeadingKernel
      rw [show
          (fun y : ℝ =>
            |2 * normalizedGaussian m (16 * m - y) *
              sharpenedPsiAbelKernel rho rho.im k y|) =
            fun y : ℝ =>
              2 * (normalizedGaussian m (16 * m - y) *
                |sharpenedPsiAbelKernel rho rho.im k y|) by
        funext y
        rw [abs_mul, abs_mul,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_nonneg
            (normalizedGaussian_pos hmPos (16 * m - y)).le]
        ring]
      rw [integral_const_mul]
      rw [show
          (fun y : ℝ =>
            normalizedGaussian m (16 * m - y) *
              |sharpenedPsiAbelKernel rho rho.im k y|) =
            fun y : ℝ =>
              (fun t : ℝ =>
                normalizedGaussian m t *
                  |sharpenedPsiAbelKernel rho rho.im k
                    (16 * m - t)|) (16 * m - y) by
        funext y
        ring_nf]
      rw [MeasureTheory.integral_sub_left_eq_self
        (fun t : ℝ =>
          normalizedGaussian m t *
            |sharpenedPsiAbelKernel rho rho.im k
              (16 * m - t)|) volume (16 * m)]
    rw [hchange]
    have hmean := hmMean (16 * m)
    rw [Real.dist_eq]
    calc
      |2 * (∫ t : ℝ,
              normalizedGaussian m t *
                |sharpenedPsiAbelKernel rho rho.im k
                  (16 * m - t)|) -
            2 * sharpenedMissingHarmonicDenominator k| =
          2 * |(∫ t : ℝ,
              normalizedGaussian m t *
                |sharpenedPsiAbelKernel rho rho.im k
                  (16 * m - t)|) -
            sharpenedMissingHarmonicDenominator k| := by
        rw [show
            2 * (∫ t : ℝ,
                normalizedGaussian m t *
                  |sharpenedPsiAbelKernel rho rho.im k
                    (16 * m - t)|) -
                2 * sharpenedMissingHarmonicDenominator k =
              2 * ((∫ t : ℝ,
                  normalizedGaussian m t *
                    |sharpenedPsiAbelKernel rho rho.im k
                      (16 * m - t)|) -
                sharpenedMissingHarmonicDenominator k) by ring,
          abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ < 2 * (ε / 2) := mul_lt_mul_of_pos_left hmean (by norm_num)
      _ = ε := by ring
  have herrorLimit :
      Tendsto (fun m : ℝ => C / Real.sqrt m) atTop (𝓝 0) := by
    have hinv :
        Tendsto (fun m : ℝ => (Real.sqrt m)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
    convert hinv.const_mul C using 1 <;> simp [div_eq_mul_inv]
  have hcoefficientError :
      Tendsto
        (fun m : ℝ =>
          |sharpenedProjectedPsiCoefficient rho k m -
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
              (continuous_projectedPsiKernel
                (sharpenedTargetFilter rho) rho hmPos).add
              (continuous_relativeProjectedPsiKernel
                (sharpenedMissingFilter rho k) rho
                (missingHarmonicContourCenter rho k)
                (missingHarmonicContourCoefficient rho k) hmPos)
          have hleadingCont : Continuous (leading m) := by
            unfold leading sharpenedLeadingKernel sharpenedPsiAbelKernel
              missingOddHarmonicKernel normalizedGaussian
            fun_prop
          apply
            (integrable_norm_iff
              (hactualCont.sub hleadingCont).aestronglyMeasurable).mp
          simpa only [actual, leading, Pi.sub_apply, Real.norm_eq_abs]
            using hdiffInt
        have heq :
            actual m =
              (fun y => actual m y - leading m y) + leading m := by
          funext y
          simp
        rw [heq]
        exact hsub.add hleadingInt
      unfold sharpenedProjectedPsiCoefficient
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
          sharpenedProjectedPsiCoefficient rho k m -
            leadingCoefficient m)
        atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    exact hcoefficientError
  have hadd := hsubLimit.add hleadingLimit
  simpa using hadd

/--
The two true zeta integrals, paired at the target and at the empty odd
harmonic, are controlled by the target window supremum with the combined
kernel mass.  Keeping the kernels combined is what preserves the strict
improvement over `pi / 2`.
-/
private theorem eventually_sharpenedProjectedPsiWindow_upper_bound
    {rho : ℂ} {k : ℕ}
    (hrhoRe0 : 0 < rho.re) (hrhoRe1 : rho.re < 1)
    (hgamma : 0 < rho.im) :
    ∀ᶠ m : ℝ in atTop,
      -((localizedPsiGaussianAverage (sharpenedTargetFilter rho) rho m +
          missingHarmonicContourCoefficient rho k *
            localizedPsiGaussianAverage
              (sharpenedMissingFilter rho k)
              (missingHarmonicContourCenter rho k) m).re) / Real.pi ≤
        normalizedWindowSup rho m *
            sharpenedProjectedPsiCoefficient rho k m +
          projectedPsiTailRemainder
              (sharpenedTargetFilter rho) rho m +
          relativeProjectedPsiTailRemainder
              (sharpenedMissingFilter rho k) rho
              (missingHarmonicContourCenter rho k)
              (missingHarmonicContourCoefficient rho k) m := by
  let targetA := sharpenedTargetFilter rho
  let center := missingHarmonicContourCenter rho k
  let missingA := sharpenedMissingFilter rho k
  let c := missingHarmonicContourCoefficient rho k
  have hrho0 : rho ≠ 0 := ne_zero_of_re_pos hrhoRe0
  have hcenterRe : center.re = rho.re := by
    dsimp [center, missingHarmonicContourCenter]
    exact oddHarmonicPoint_re rho.re rho.im k
  have hcenterRe0 : 0 < center.re := hcenterRe.symm ▸ hrhoRe0
  have hbddEventual :=
    eventually_bddAbove_normalizedWindowValues
      (u := rho.re) (v := rho.im) hrhoRe0 hrhoRe1
  filter_upwards [
    eventually_ge_atTop (1 : ℝ),
    hbddEventual] with m hm hbdd
  have hrhoEq : (rho.re : ℂ) + I * rho.im = rho := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  rw [hrhoEq] at hbdd
  have hmPos : 0 < m := zero_lt_one.trans_le hm
  let kernel : ℝ → ℝ := sharpenedProjectedPsiKernel rho k m
  let fTarget : ℝ → ℝ := fun y =>
    normalizedPsiError rho y * projectedPsiKernel targetA rho m y
  let fMissing : ℝ → ℝ := fun y =>
    normalizedPsiError rho y *
      relativeProjectedPsiKernel missingA rho center c m y
  let f : ℝ → ℝ := fun y =>
    normalizedPsiError rho y * kernel y
  let window : Set ℝ := gaussianLogWindow m
  let tail : Set ℝ := Set.Ioi 0 \ window
  have hwindowMeasurable : MeasurableSet window := measurableSet_Icc
  have htailMeasurable : MeasurableSet tail :=
    measurableSet_Ioi.diff hwindowMeasurable
  have hwindowSubset : window ⊆ Set.Ioi (0 : ℝ) := by
    intro y hy
    exact Set.mem_Ioi.mpr (by nlinarith [hy.1])
  have hfTargetIoi : IntegrableOn fTarget (Set.Ioi 0) := by
    simpa only [fTarget, targetA] using
      integrableOn_normalizedPsiError_mul_projectedPsiKernel
        (sharpenedTargetFilter rho) hmPos hrhoRe0
  have hfMissingIoi : IntegrableOn fMissing (Set.Ioi 0) := by
    simpa only [fMissing, missingA, center, c] using
      integrableOn_normalizedPsiError_mul_relativeProjectedPsiKernel
        (missingHarmonicContourCoefficient rho k)
        (sharpenedMissingFilter rho k) hmPos hrhoRe0 hcenterRe0
        hcenterRe
  have hfIoi : IntegrableOn f (Set.Ioi 0) := by
    have hadd := hfTargetIoi.add hfMissingIoi
    apply hadd.congr_fun _ measurableSet_Ioi
    intro y _hy
    dsimp [f, fTarget, fMissing, kernel, targetA, missingA, center, c]
    unfold sharpenedProjectedPsiKernel
    ring
  have hfWindow : IntegrableOn f window :=
    hfIoi.mono_set hwindowSubset
  have hfTail : IntegrableOn f tail :=
    hfIoi.mono_set fun _ hy => hy.1
  have hfTargetTail : IntegrableOn fTarget tail :=
    hfTargetIoi.mono_set fun _ hy => hy.1
  have hfMissingTail : IntegrableOn fMissing tail :=
    hfMissingIoi.mono_set fun _ hy => hy.1
  have hkernelInt : Integrable kernel := by
    dsimp [kernel]
    unfold sharpenedProjectedPsiKernel
    exact
      (integrable_projectedPsiKernel targetA rho hmPos).add
        (integrable_relativeProjectedPsiKernel missingA rho center c hmPos)
  have hkernelWindow : IntegrableOn (fun y => |kernel y|) window :=
    hkernelInt.abs.integrableOn
  have hsupNonneg : 0 ≤ normalizedWindowSup rho m := by
    have hvalue :
        |normalizedPsiError rho (4 * m)| ∈
          normalizedWindowValues rho m := by
      exact ⟨4 * m, ⟨le_rfl, by nlinarith⟩, rfl⟩
    exact (abs_nonneg _).trans (le_csSup hbdd hvalue)
  have hinside :
      (∫ y : ℝ in window, f y) ≤
        normalizedWindowSup rho m *
          sharpenedProjectedPsiCoefficient rho k m := by
    have hmono :
        (∫ y : ℝ in window, f y) ≤
          ∫ y : ℝ in window,
            normalizedWindowSup rho m * |kernel y| := by
      apply setIntegral_mono_on hfWindow
        (hkernelWindow.const_mul (normalizedWindowSup rho m))
        hwindowMeasurable
      intro y hy
      have hvalue :
          |normalizedPsiError rho y| ∈
            normalizedWindowValues rho m :=
        ⟨y, hy, rfl⟩
      have hsup :
          |normalizedPsiError rho y| ≤ normalizedWindowSup rho m :=
        le_csSup hbdd hvalue
      dsimp [f]
      calc
        normalizedPsiError rho y * kernel y ≤
            |normalizedPsiError rho y * kernel y| :=
          le_abs_self _
        _ = |normalizedPsiError rho y| * |kernel y| := abs_mul _ _
        _ ≤ normalizedWindowSup rho m * |kernel y| :=
          mul_le_mul_of_nonneg_right hsup (abs_nonneg _)
    have hmass :
        (∫ y : ℝ in window, |kernel y|) ≤
          ∫ y : ℝ, |kernel y| :=
      setIntegral_le_integral hkernelInt.abs
        (Filter.Eventually.of_forall fun y => abs_nonneg (kernel y))
    calc
      (∫ y : ℝ in window, f y) ≤
          normalizedWindowSup rho m *
            ∫ y : ℝ in window, |kernel y| := by
        simpa only [integral_const_mul] using hmono
      _ ≤ normalizedWindowSup rho m * ∫ y : ℝ, |kernel y| :=
        mul_le_mul_of_nonneg_left hmass hsupNonneg
      _ =
          normalizedWindowSup rho m *
            sharpenedProjectedPsiCoefficient rho k m := by
        rfl
  have htail :
      (∫ y : ℝ in tail, f y) ≤
        projectedPsiTailRemainder targetA rho m +
          relativeProjectedPsiTailRemainder missingA rho center c m := by
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
          unfold sharpenedProjectedPsiKernel
          ring
        rw [hfEq]
        exact abs_add_le _ _
      _ =
          projectedPsiTailRemainder targetA rho m +
            relativeProjectedPsiTailRemainder missingA rho center c m := by
        rw [integral_add hfTargetTail.abs hfMissingTail.abs]
        rfl
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
    neg_re_localizedPsiGaussianAverage_div_pi_eq
      targetA hmPos hrhoRe0
  have hmissingEq :=
    neg_re_mul_localizedPsiGaussianAverage_div_pi_eq
      c missingA hmPos hrho0 hcenterRe0 hcenterRe
  have hpairEq :
      -((localizedPsiGaussianAverage targetA rho m +
          c * localizedPsiGaussianAverage missingA center m).re) /
          Real.pi =
        ∫ y : ℝ in Set.Ioi 0, f y := by
    calc
      -((localizedPsiGaussianAverage targetA rho m +
          c * localizedPsiGaussianAverage missingA center m).re) /
            Real.pi =
          -(localizedPsiGaussianAverage targetA rho m).re / Real.pi +
            -(c * localizedPsiGaussianAverage missingA center m).re /
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
        unfold sharpenedProjectedPsiKernel
        ring
  dsimp only [targetA, missingA, center, c] at *
  rw [hpairEq, ← hdecompose]
  calc
    (∫ y : ℝ in window, f y) + ∫ y : ℝ in tail, f y ≤
        normalizedWindowSup rho m *
            sharpenedProjectedPsiCoefficient rho k m +
          (projectedPsiTailRemainder
              (sharpenedTargetFilter rho) rho m +
            relativeProjectedPsiTailRemainder
              (sharpenedMissingFilter rho k) rho
              (missingHarmonicContourCenter rho k)
              (missingHarmonicContourCoefficient rho k) m) :=
      add_le_add hinside htail
    _ = _ := by ring

/--
The final paired true-zeta contour package.  The construction is implemented
after the coefficient limit and the two selected residue limits have been
assembled.
-/
noncomputable def sharpenedConcreteLocalizedContourData
    {rho : ℂ} {k : ℕ}
    (hrhoRe0 : 0 < rho.re) (hrhoRe1 : rho.re < 1)
    (hgamma : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (hmissing :
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0) :
    LocalizedContourData rho
      (analyticOrderNatAt riemannZeta rho : ℝ)
      (sharpenedMissingHarmonicDenominator k) := by
  let targetA := sharpenedTargetFilter rho
  let center := missingHarmonicContourCenter rho k
  let missingA := sharpenedMissingFilter rho k
  let c := missingHarmonicContourCoefficient rho k
  let multiplicity : ℝ := analyticOrderNatAt riemannZeta rho
  let zeroPair : ℝ → ℂ := fun m =>
    selectedLocalizedZeroResidueSum targetA rho.re rho.im m +
      c * selectedLocalizedZeroResidueSum missingA rho.re center.im m
  let contourPair : ℝ → ℂ := fun m =>
    selectedLocalizedContourRemainder targetA rho.re rho.im m +
      c * selectedLocalizedContourRemainder missingA rho.re center.im m
  let psiTail : ℝ → ℝ := fun m =>
    projectedPsiTailRemainder targetA rho m +
      relativeProjectedPsiTailRemainder missingA rho center c m
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
        (selectedLocalizedZeroResidueSum targetA rho.re rho.im)
        atTop (𝓝 (multiplicity : ℂ)) := by
    have hzero' :
        riemannZeta ((rho.re : ℂ) + I * rho.im) = 0 := by
      rw [hrhoEq]
      exact hzero
    have h :=
      tendsto_selectedLocalizedZeroResidueSum_nearZeroFilter
        hrhoRe0 hrhoRe1 (by norm_num : (5 : ℝ) ≤ 5)
        hzero'
    rw [hrhoEq] at h
    simpa [targetA, sharpenedTargetFilter, multiplicity] using h
  have hzeroMissing :
      Tendsto
        (selectedLocalizedZeroResidueSum missingA rho.re center.im)
        atTop (𝓝 0) := by
    have hmissing' :
        riemannZeta ((rho.re : ℂ) + I * center.im) ≠ 0 := by
      rw [hcenterEq]
      exact hmissing
    have h :=
      tendsto_selectedLocalizedZeroResidueSum_nearZeroFilter_of_ne_zero
        hrhoRe0 hrhoRe1 (by norm_num : (5 : ℝ) ≤ 5)
        hmissing'
    rw [hcenterEq] at h
    simpa [missingA, sharpenedMissingFilter] using h
  have hzeroPair :
      Tendsto zeroPair atTop (𝓝 (multiplicity : ℂ)) := by
    have hcMissing :
        Tendsto
          (fun m =>
            c * selectedLocalizedZeroResidueSum
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
      simpa [Function.comp_def] using
        Complex.continuous_re.continuousAt.tendsto.comp hzeroPair
    exact tendsto_const_nhds.mul hre
  have hcoefficient :=
    tendsto_sharpenedProjectedPsiCoefficient
      (rho := rho) (k := k) hrho0 hgamma
  have hcoefficientPos :
      ∀ᶠ m : ℝ in atTop,
        0 < sharpenedProjectedPsiCoefficient rho k m := by
    have hlimitPos :
        0 < 2 * sharpenedMissingHarmonicDenominator k := by
      exact mul_pos (by norm_num) (sharpenedMissingHarmonicDenominator_pos k)
    exact (tendsto_order.1 hcoefficient).1 0 hlimitPos
  have htargetRemainder :
      Tendsto
        (selectedLocalizedContourRemainder
          targetA rho.re rho.im)
        atTop (𝓝 0) :=
    tendsto_selectedLocalizedContourRemainder
      targetA hrhoRe0 hrhoRe1 rho.im
  have hmissingRemainder :
      Tendsto
        (selectedLocalizedContourRemainder
          missingA rho.re center.im)
        atTop (𝓝 0) :=
    tendsto_selectedLocalizedContourRemainder
      missingA hrhoRe0 hrhoRe1 center.im
  have hcontourPair :
      Tendsto contourPair atTop (𝓝 0) := by
    have hcRemainder :
        Tendsto
          (fun m =>
            c * selectedLocalizedContourRemainder
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
      simpa [Function.comp_def] using tendsto_norm.comp hcontourPair
    simpa using hnorm.div_const Real.pi
  have htargetTail :
      Tendsto
        (projectedPsiTailRemainder targetA rho)
        atTop (𝓝 0) := by
    simpa [hrhoEq] using
      tendsto_projectedPsiTailRemainder
        targetA hrhoRe0 hrhoRe1 rho.im
  have hmissingTail :
      Tendsto
        (relativeProjectedPsiTailRemainder
          missingA rho center c)
        atTop (𝓝 0) := by
    simpa [hrhoEq, hcenterEq] using
      tendsto_relativeProjectedPsiTailRemainder
        c missingA hrhoRe0 hrhoRe1 rho.im center.im
  have hpsiTail :
      Tendsto psiTail atTop (𝓝 0) := by
    simpa [psiTail] using htargetTail.add hmissingTail
  have hremainder :
      Tendsto remainder atTop (𝓝 0) := by
    simpa [remainder] using hpsiTail.add hcontourNorm
  have hwindow :
      ∀ᶠ m : ℝ in atTop,
        BddAbove (normalizedWindowValues rho m) := by
    simpa [hrhoEq] using
      eventually_bddAbove_normalizedWindowValues
        (u := rho.re) (v := rho.im) hrhoRe0 hrhoRe1
  refine {
    signal := fun m => 2 * (zeroPair m).re
    coefficient := sharpenedProjectedPsiCoefficient rho k
    remainder := remainder
    signal_tendsto := hsignal
    coefficient_tendsto := hcoefficient
    remainder_tendsto := hremainder
    eventually_coefficient_pos := hcoefficientPos
    eventually_window_bddAbove := hwindow
    eventually_upper_bound := ?_
  }
  have hpsi :=
    eventually_sharpenedProjectedPsiWindow_upper_bound
      (rho := rho) (k := k) hrhoRe0 hrhoRe1 hgamma
  filter_upwards [
    eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (targetA.natDegree : ℝ),
    eventually_ge_atTop (missingA.natDegree : ℝ),
    hpsi] with m hm htargetDegree hmissingDegree hpsiM
  have htargetValid : localizedContourScaleValid targetA rho.re m :=
    ⟨hrhoRe0, hrhoRe1, hm, htargetDegree⟩
  have hmissingValid : localizedContourScaleValid missingA rho.re m :=
    ⟨hrhoRe0, hrhoRe1, hm, hmissingDegree⟩
  have htargetContour :=
    selected_localizedPsiGaussianAverage_eq
      targetA (u := rho.re) (v := rho.im) (m := m) htargetValid
  have hmissingContour :=
    selected_localizedPsiGaussianAverage_eq
      missingA (u := rho.re) (v := center.im) (m := m) hmissingValid
  let L : ℂ :=
    localizedPsiGaussianAverage targetA rho m +
      c * localizedPsiGaussianAverage missingA center m
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
      normalizedWindowSup rho m *
          sharpenedProjectedPsiCoefficient rho k m +
        remainder m
  have hpsiM' :
      -(L.re) / Real.pi ≤
        normalizedWindowSup rho m *
            sharpenedProjectedPsiCoefficient rho k m +
          psiTail m := by
    dsimp [L, psiTail, targetA, missingA, center, c]
    convert hpsiM using 1 <;> (try rfl) <;> ring
  rw [hsignalEq]
  change
    -L.re / Real.pi + (contourPair m).re / Real.pi ≤
      normalizedWindowSup rho m *
          sharpenedProjectedPsiCoefficient rho k m +
        (psiTail m + ‖contourPair m‖ / Real.pi)
  calc
    -L.re / Real.pi + (contourPair m).re / Real.pi ≤
        (normalizedWindowSup rho m *
            sharpenedProjectedPsiCoefficient rho k m +
          psiTail m) + ‖contourPair m‖ / Real.pi :=
      add_le_add hpsiM' hcontourLe
    _ = _ := by ring

/--
An actual zeta zero together with one missing positive odd harmonic forces a
strictly-better-than-`pi / 2` PNT-error oscillation in every sufficiently
late power-seven interval.  The coefficient retains the analytic
multiplicity of the target zero.
-/
theorem eventually_exists_psiError_in_powerSevenWindow_gt_strictPiOverTwo
    {rho : ℂ} {k : ℕ}
    (hrhoRe0 : 0 < rho.re) (hrhoRe1 : rho.re < 1)
    (hgamma : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (hmissing :
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0) :
    ∀ᶠ Y : ℝ in atTop,
      ∃ x ∈ powerSevenWindow Y,
        (analyticOrderNatAt riemannZeta rho : ℝ) *
              strictPiOverTwoOscillationConstant k *
              (x ^ rho.re / ‖rho‖) <
          |chebyshevPsi x - x| := by
  have hrho0 : rho ≠ 0 := ne_zero_of_re_pos hrhoRe0
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
  have hconstant :
      (analyticOrderNatAt riemannZeta rho : ℝ) *
          strictPiOverTwoOscillationConstant k <
        (analyticOrderNatAt riemannZeta rho : ℝ) /
          sharpenedMissingHarmonicDenominator k := by
    rw [show
        (analyticOrderNatAt riemannZeta rho : ℝ) /
              sharpenedMissingHarmonicDenominator k =
            (analyticOrderNatAt riemannZeta rho : ℝ) *
              sharpenedMissingHarmonicLowerBound k by
      unfold sharpenedMissingHarmonicLowerBound
      ring]
    exact mul_lt_mul_of_pos_left
      (strictPiOverTwoOscillationConstant_lt_lowerBound k)
      hmultiplicity
  exact
    (sharpenedConcreteLocalizedContourData
      hrhoRe0 hrhoRe1 hgamma hzero hmissing).eventually_exists_psiError_in_powerSevenWindow
        hrho0 hmultiplicity hmean hconstant

/--
Carlson zero density supplies the missing odd harmonic required by the
localized contour theorem.  Consequently every off-critical-line zero in
the stated right half of the strip has a multiplicity-sensitive,
strictly-better-than-`pi / 2` oscillation in every sufficiently late
power-seven interval.
-/
theorem exists_eventually_psiError_in_powerSevenWindow_gt_strictPiOverTwo
    {rho : ℂ} {sigma : ℝ}
    (hrhoRe1 : rho.re < 1) (hgamma : 0 < rho.im)
    (hsigmaHalf : 1 / 2 < sigma) (hsigmaRho : sigma < rho.re)
    (hzero : riemannZeta rho = 0) :
    ∃ k : ℕ,
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0 ∧
      Real.pi / 2 < strictPiOverTwoOscillationConstant k ∧
      ∀ᶠ Y : ℝ in atTop,
        ∃ x ∈ powerSevenWindow Y,
          (analyticOrderNatAt riemannZeta rho : ℝ) *
                strictPiOverTwoOscillationConstant k *
                (x ^ rho.re / ‖rho‖) <
            |chebyshevPsi x - x| := by
  have hrhoRe0 : 0 < rho.re := by linarith
  rcases
      exists_missing_oddHarmonic_with_strict_gap_of_carlson
        hrhoRe1 hgamma hsigmaHalf hsigmaRho with
    ⟨k, hmissing, _hOldGap⟩
  have hmissing' :
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0 := by
    simpa [missingHarmonicContourCenter] using hmissing
  exact
    ⟨k, hmissing',
      pi_div_two_lt_strictPiOverTwoOscillationConstant k,
      eventually_exists_psiError_in_powerSevenWindow_gt_strictPiOverTwo
        hrhoRe0 hrhoRe1 hgamma hzero hmissing'⟩

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
