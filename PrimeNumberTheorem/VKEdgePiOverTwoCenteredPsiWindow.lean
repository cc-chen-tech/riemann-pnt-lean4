import Mathlib.MeasureTheory.Function.JacobianOneDim
import PrimeNumberTheorem.VKEdgePiOverTwoCenteredMellin
import PrimeNumberTheorem.VKEdgePiOverTwoEpsilonWindow
import PrimeNumberTheorem.VKEdgePiOverTwoProjectedPsiWindow

open Complex Filter MeasureTheory Polynomial Set Topology

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- The real dual kernel with logarithmic center `q * m`. -/
def projectedPsiKernelAtCenter
    (q : ℝ) (A : ℂ[X]) (w : ℂ) (m y : ℝ) : ℝ :=
  -(2 / ‖w‖) *
    (Complex.exp
        (-(I * (w.im : ℂ) * (y : ℂ))) *
      (w * polynomialGaussianKernel A m (q * m - y) +
        polynomialGaussianKernelDeriv A m (q * m - y))).re

/-- A centered projected kernel normalized using `target`, while its contour
is centered at `center`. -/
def relativeProjectedPsiKernelAtCenter
    (q : ℝ) (A : ℂ[X]) (target center c : ℂ) (m y : ℝ) : ℝ :=
  (‖center‖ / ‖target‖) *
    projectedPsiKernelAtCenter q (C c * A) center m y

/-- The true normalized-Psi contribution outside the centered logarithmic
window. -/
def projectedPsiTailRemainderAtCenter
    (q d : ℝ) (A : ℂ[X]) (w : ℂ) (m : ℝ) : ℝ :=
  ∫ y : ℝ in Set.Ioi 0 \ localizedGaussianLogWindow q d m,
    |normalizedPsiError w y *
      projectedPsiKernelAtCenter q A w m y|

/-- The target-normalized true-Psi contribution outside the centered
logarithmic window. -/
def relativeProjectedPsiTailRemainderAtCenter
    (q d : ℝ) (A : ℂ[X]) (target center c : ℂ) (m : ℝ) : ℝ :=
  ∫ y : ℝ in Set.Ioi 0 \ localizedGaussianLogWindow q d m,
    |normalizedPsiError target y *
      relativeProjectedPsiKernelAtCenter q A target center c m y|

private def logarithmicLocalizedPsiGaussianIntegrandAtCenter
    (q : ℝ) (A : ℂ[X]) (w : ℂ) (m y : ℝ) : ℂ :=
  ((chebyshevPsi (Real.exp y) - Real.exp y : ℝ) : ℂ) *
    ((2 * Real.pi : ℂ) *
      (Complex.exp (-(w * (y : ℂ))) *
        (w * polynomialGaussianKernel A m (q * m - y) +
          polynomialGaussianKernelDeriv A m (q * m - y))))

theorem localizedPsiGaussianAverageAtCenter_C_mul
    (q : ℝ) (c : ℂ) (A : ℂ[X]) (w : ℂ) (m : ℝ) :
    localizedPsiGaussianAverageAtCenter q (C c * A) w m =
      c * localizedPsiGaussianAverageAtCenter q A w m := by
  calc
    localizedPsiGaussianAverageAtCenter q (C c * A) w m =
        ∫ x : ℝ in Set.Ioi 1,
          c * (psiErrorAboveOneComplex x *
            ((2 * Real.pi : ℂ) *
              ((x : ℂ) ^ (-(w + 1)) *
                (w * polynomialGaussianKernel A m
                    (q * m - Real.log x) +
                  polynomialGaussianKernelDeriv A m
                    (q * m - Real.log x))))) := by
      unfold localizedPsiGaussianAverageAtCenter
      apply integral_congr_ae
      filter_upwards with x
      rw [polynomialGaussianKernel_C_mul,
        polynomialGaussianKernelDeriv_C_mul]
      ring
    _ = c * localizedPsiGaussianAverageAtCenter q A w m := by
      unfold localizedPsiGaussianAverageAtCenter
      exact MeasureTheory.integral_const_mul c _

private lemma image_exp_Ioi_zero_centered :
    Real.exp '' Set.Ioi (0 : ℝ) = Set.Ioi (1 : ℝ) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using Real.exp_lt_exp.mpr hy
  · intro hx
    have hx0 : 0 < x := zero_lt_one.trans hx
    refine ⟨Real.log x, Real.log_pos hx, ?_⟩
    exact Real.exp_log hx0

private lemma exp_mul_cpow_neg_add_one_centered
    (s : ℂ) (y : ℝ) :
    (Real.exp y : ℂ) *
        (Real.exp y : ℂ) ^ (-(s + 1)) =
      Complex.exp (-s * (y : ℂ)) := by
  rw [show (Real.exp y : ℂ) = Complex.exp (y : ℂ) by simp]
  conv_lhs =>
    lhs
    rw [← Complex.cpow_one (Complex.exp (y : ℂ))]
  rw [← Complex.cpow_add _ _ (Complex.exp_ne_zero _),
    Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos]) (by simpa using Real.pi_nonneg)]
  congr 1
  ring

/-- Exact logarithmic-coordinate form of the centered Chebyshev-error
Gaussian average. -/
theorem localizedPsiGaussianAverageAtCenter_eq_logarithmic
    (q : ℝ) (A : ℂ[X]) (w : ℂ) (m : ℝ) :
    localizedPsiGaussianAverageAtCenter q A w m =
      ∫ y : ℝ in Set.Ioi 0,
        logarithmicLocalizedPsiGaussianIntegrandAtCenter q A w m y := by
  let g : ℝ → ℂ := fun x =>
    psiErrorAboveOneComplex x *
      ((2 * Real.pi : ℂ) *
        ((x : ℂ) ^ (-(w + 1)) *
          (w * polynomialGaussianKernel A m
              (q * m - Real.log x) +
            polynomialGaussianKernelDeriv A m
              (q * m - Real.log x))))
  have hchange :=
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      (s := Set.Ioi (0 : ℝ))
      (f := Real.exp) (f' := Real.exp)
      measurableSet_Ioi
      (fun y _hy => (Real.hasDerivAt_exp y).hasDerivWithinAt)
      Real.exp_injective.injOn g
  rw [image_exp_Ioi_zero_centered] at hchange
  have hintegrand :
      ∀ y ∈ Set.Ioi (0 : ℝ),
        |Real.exp y| • g (Real.exp y) =
          logarithmicLocalizedPsiGaussianIntegrandAtCenter q A w m y := by
    intro y hy
    have hyPos : 0 < Real.exp y := Real.exp_pos y
    have hyOne : 1 ≤ Real.exp y := by
      simpa using Real.exp_le_exp.mpr hy.le
    simp only [abs_of_pos hyPos, g, Complex.real_smul]
    rw [show psiErrorAboveOneComplex (Real.exp y) =
        ((chebyshevPsi (Real.exp y) - Real.exp y : ℝ) : ℂ) by
      simp [psiErrorAboveOneComplex, psiErrorAboveOne,
        hyPos, hyOne]]
    rw [Real.log_exp]
    unfold logarithmicLocalizedPsiGaussianIntegrandAtCenter
    rw [show
        (Real.exp y : ℂ) *
            (((chebyshevPsi (Real.exp y) - Real.exp y : ℝ) : ℂ) *
              ((2 * Real.pi : ℂ) *
                ((Real.exp y : ℂ) ^ (-(w + 1)) *
                  (w * polynomialGaussianKernel A m (q * m - y) +
                    polynomialGaussianKernelDeriv A m (q * m - y))))) =
          ((chebyshevPsi (Real.exp y) - Real.exp y : ℝ) : ℂ) *
            ((2 * Real.pi : ℂ) *
              (((Real.exp y : ℂ) *
                  (Real.exp y : ℂ) ^ (-(w + 1))) *
                (w * polynomialGaussianKernel A m (q * m - y) +
                  polynomialGaussianKernelDeriv A m (q * m - y)))) by
      ring]
    rw [exp_mul_cpow_neg_add_one_centered]
    ring
  unfold localizedPsiGaussianAverageAtCenter
  change (∫ x : ℝ in Set.Ioi 1, g x) = _
  rw [hchange]
  exact setIntegral_congr_fun measurableSet_Ioi hintegrand

private theorem
    integrableOn_logarithmicLocalizedPsiGaussianIntegrandAtCenter
    (q : ℝ) (A : ℂ[X]) {w : ℂ} {m : ℝ}
    (hm : 0 < m) (hw : 0 < w.re) :
    IntegrableOn
      (logarithmicLocalizedPsiGaussianIntegrandAtCenter q A w m)
      (Set.Ioi 0) := by
  have hxIntegrable :=
    integrableOn_localizedPsiGaussianAverageAtCenter_integrand
      q A hm hw
  let g : ℝ → ℂ := fun x =>
    psiErrorAboveOneComplex x *
      ((2 * Real.pi : ℂ) *
        ((x : ℂ) ^ (-(w + 1)) *
          (w * polynomialGaussianKernel A m
              (q * m - Real.log x) +
            polynomialGaussianKernelDeriv A m
              (q * m - Real.log x))))
  have hchange :=
    integrableOn_image_iff_integrableOn_abs_deriv_smul
      (s := Set.Ioi (0 : ℝ))
      (f := Real.exp) (f' := Real.exp)
      measurableSet_Ioi
      (fun y _hy => (Real.hasDerivAt_exp y).hasDerivWithinAt)
      Real.exp_injective.injOn g
  rw [image_exp_Ioi_zero_centered] at hchange
  have htrans :
      IntegrableOn
        (fun y : ℝ => |Real.exp y| • g (Real.exp y))
        (Set.Ioi 0) :=
    hchange.mp hxIntegrable
  refine htrans.congr_fun ?_ measurableSet_Ioi
  intro y hy
  have hyPos : 0 < Real.exp y := Real.exp_pos y
  have hyOne : 1 ≤ Real.exp y := by
    simpa using Real.exp_le_exp.mpr hy.le
  simp only [abs_of_pos hyPos, g, Complex.real_smul]
  rw [show psiErrorAboveOneComplex (Real.exp y) =
      ((chebyshevPsi (Real.exp y) - Real.exp y : ℝ) : ℂ) by
    simp [psiErrorAboveOneComplex, psiErrorAboveOne, hyOne]]
  rw [Real.log_exp]
  unfold logarithmicLocalizedPsiGaussianIntegrandAtCenter
  rw [show
      (Real.exp y : ℂ) *
          (((chebyshevPsi (Real.exp y) - Real.exp y : ℝ) : ℂ) *
            ((2 * Real.pi : ℂ) *
              ((Real.exp y : ℂ) ^ (-(w + 1)) *
                (w * polynomialGaussianKernel A m (q * m - y) +
                  polynomialGaussianKernelDeriv A m (q * m - y))))) =
        ((chebyshevPsi (Real.exp y) - Real.exp y : ℝ) : ℂ) *
          ((2 * Real.pi : ℂ) *
            (((Real.exp y : ℂ) *
                (Real.exp y : ℂ) ^ (-(w + 1))) *
              (w * polynomialGaussianKernel A m (q * m - y) +
                polynomialGaussianKernelDeriv A m (q * m - y)))) by
    ring]
  rw [exp_mul_cpow_neg_add_one_centered]
  ring

private theorem logarithmicLocalizedPsiGaussianIntegrandAtCenter_re
    {q : ℝ} {A : ℂ[X]} {w : ℂ} {m y : ℝ}
    (hw : w ≠ 0) :
    -(logarithmicLocalizedPsiGaussianIntegrandAtCenter q A w m y).re /
        Real.pi =
      normalizedPsiError w y *
        projectedPsiKernelAtCenter q A w m y := by
  have hnormPos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hexpSplit :
      Complex.exp (-(w * (y : ℂ))) =
        (Real.exp (-w.re * y) : ℂ) *
          Complex.exp (-(I * (w.im : ℂ) * (y : ℂ))) := by
    rw [show -(w * (y : ℂ)) =
        ((-w.re * y : ℝ) : ℂ) +
          -(I * (w.im : ℂ) * (y : ℂ)) by
      apply Complex.ext <;>
        simp [Complex.mul_re, Complex.mul_im] <;> ring]
    rw [Complex.exp_add]
    simp only [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_exp]
  unfold logarithmicLocalizedPsiGaussianIntegrandAtCenter
    normalizedPsiError projectedPsiKernelAtCenter
  rw [hexpSplit]
  rw [mul_assoc
    (Real.exp (-w.re * y) : ℂ)
    (Complex.exp (-(I * (w.im : ℂ) * (y : ℂ))))
    (w * polynomialGaussianKernel A m (q * m - y) +
      polynomialGaussianKernelDeriv A m (q * m - y))]
  let z : ℂ :=
    Complex.exp (-(I * (w.im : ℂ) * (y : ℂ))) *
      (w * polynomialGaussianKernel A m (q * m - y) +
        polynomialGaussianKernelDeriv A m (q * m - y))
  change
    -((((chebyshevPsi (Real.exp y) - Real.exp y : ℝ) : ℂ) *
        ((2 * Real.pi : ℂ) *
          ((Real.exp (-w.re * y) : ℂ) * z))).re) / Real.pi =
      (‖w‖ * (chebyshevPsi (Real.exp y) - Real.exp y) *
          Real.exp (-w.re * y)) *
        (-(2 / ‖w‖) * z.re)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, add_zero]
  norm_num
  field_simp [Real.pi_ne_zero, hnormPos.ne']

/-- The oriented real part of the centered Gaussian average is exactly the
normalized PNT error paired with the centered projected kernel. -/
theorem neg_re_localizedPsiGaussianAverageAtCenter_div_pi_eq
    (q : ℝ) (A : ℂ[X]) {w : ℂ} {m : ℝ}
    (hm : 0 < m) (hw : 0 < w.re) :
    -(localizedPsiGaussianAverageAtCenter q A w m).re / Real.pi =
      ∫ y : ℝ in Set.Ioi 0,
        normalizedPsiError w y *
          projectedPsiKernelAtCenter q A w m y := by
  have hw0 : w ≠ 0 := ne_zero_of_re_pos hw
  have hint :=
    integrableOn_logarithmicLocalizedPsiGaussianIntegrandAtCenter
      q A hm hw
  rw [localizedPsiGaussianAverageAtCenter_eq_logarithmic]
  rw [show
      (∫ y : ℝ in Set.Ioi 0,
          logarithmicLocalizedPsiGaussianIntegrandAtCenter
            q A w m y).re =
        ∫ y : ℝ in Set.Ioi 0,
          (logarithmicLocalizedPsiGaussianIntegrandAtCenter
            q A w m y).re by
    exact (integral_re hint).symm]
  rw [← integral_neg, ← integral_div]
  apply integral_congr_ae
  filter_upwards with y
  exact logarithmicLocalizedPsiGaussianIntegrandAtCenter_re hw0

/-- The centered normalized-error pairing is integrable on the positive
logarithmic axis. -/
theorem integrableOn_normalizedPsiError_mul_projectedPsiKernelAtCenter
    (q : ℝ) (A : ℂ[X]) {w : ℂ} {m : ℝ}
    (hm : 0 < m) (hw : 0 < w.re) :
    IntegrableOn
      (fun y =>
        normalizedPsiError w y *
          projectedPsiKernelAtCenter q A w m y)
      (Set.Ioi 0) := by
  have hw0 : w ≠ 0 := ne_zero_of_re_pos hw
  have hint :=
    integrableOn_logarithmicLocalizedPsiGaussianIntegrandAtCenter
      q A hm hw
  have hre :
      IntegrableOn
        (fun y =>
          (logarithmicLocalizedPsiGaussianIntegrandAtCenter
            q A w m y).re)
        (Set.Ioi 0) :=
    hint.re
  have hscaled :
      IntegrableOn
        (fun y =>
          -(logarithmicLocalizedPsiGaussianIntegrandAtCenter
            q A w m y).re / Real.pi)
        (Set.Ioi 0) :=
    hre.neg.div_const Real.pi
  apply hscaled.congr_fun _ measurableSet_Ioi
  intro y _hy
  exact logarithmicLocalizedPsiGaussianIntegrandAtCenter_re hw0

/-- A complex multiple of a centered contour on the same vertical line can
be expressed using the target-normalized PNT error. -/
theorem neg_re_mul_localizedPsiGaussianAverageAtCenter_div_pi_eq
    (q : ℝ) (c : ℂ) (A : ℂ[X])
    {target center : ℂ} {m : ℝ}
    (hm : 0 < m) (htarget : target ≠ 0)
    (hcenter : 0 < center.re) (hre : center.re = target.re) :
    -(c * localizedPsiGaussianAverageAtCenter q A center m).re /
        Real.pi =
      ∫ y : ℝ in Set.Ioi 0,
        normalizedPsiError target y *
          relativeProjectedPsiKernelAtCenter
            q A target center c m y := by
  have hcenter0 : center ≠ 0 := ne_zero_of_re_pos hcenter
  have hnormTarget : 0 < ‖target‖ := norm_pos_iff.mpr htarget
  have hnormCenter : 0 < ‖center‖ := norm_pos_iff.mpr hcenter0
  rw [← localizedPsiGaussianAverageAtCenter_C_mul q c A center m]
  rw [neg_re_localizedPsiGaussianAverageAtCenter_div_pi_eq
    q (C c * A) hm hcenter]
  apply integral_congr_ae
  filter_upwards with y
  unfold relativeProjectedPsiKernelAtCenter normalizedPsiError
  rw [hre]
  field_simp [hnormTarget.ne', hnormCenter.ne']

/-- Relative centered projected kernels remain integrable against the
target-normalized PNT error. -/
theorem
    integrableOn_normalizedPsiError_mul_relativeProjectedPsiKernelAtCenter
    (q : ℝ) (c : ℂ) (A : ℂ[X])
    {target center : ℂ} {m : ℝ}
    (hm : 0 < m) (htarget : 0 < target.re)
    (hcenter : 0 < center.re) (hre : center.re = target.re) :
    IntegrableOn
      (fun y =>
        normalizedPsiError target y *
          relativeProjectedPsiKernelAtCenter
            q A target center c m y)
      (Set.Ioi 0) := by
  have htarget0 : target ≠ 0 := ne_zero_of_re_pos htarget
  have hcenter0 : center ≠ 0 := ne_zero_of_re_pos hcenter
  have htargetNorm : 0 < ‖target‖ := norm_pos_iff.mpr htarget0
  have hcenterNorm : 0 < ‖center‖ := norm_pos_iff.mpr hcenter0
  have hbase :=
    integrableOn_normalizedPsiError_mul_projectedPsiKernelAtCenter
      q (C c * A) hm hcenter
  refine hbase.congr_fun ?_ measurableSet_Ioi
  intro y _hy
  unfold normalizedPsiError relativeProjectedPsiKernelAtCenter
  rw [hre]
  field_simp [htargetNorm.ne', hcenterNorm.ne']

private theorem relativeProjectedPsiTailRemainderAtCenter_eq
    (q d : ℝ) (c : ℂ) (A : ℂ[X]) {u v lambda m : ℝ}
    (htarget : ((u : ℂ) + I * v) ≠ 0)
    (hcenter : ((u : ℂ) + I * lambda) ≠ 0) :
    relativeProjectedPsiTailRemainderAtCenter q d A
        ((u : ℂ) + I * v) ((u : ℂ) + I * lambda) c m =
      projectedPsiTailRemainderAtCenter q d (C c * A)
        ((u : ℂ) + I * lambda) m := by
  unfold relativeProjectedPsiTailRemainderAtCenter
    projectedPsiTailRemainderAtCenter relativeProjectedPsiKernelAtCenter
  apply integral_congr_ae
  filter_upwards with y
  unfold normalizedPsiError
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.ofReal_im, Complex.I_im, zero_mul, one_mul,
    add_zero]
  have htNorm : 0 < ‖(u : ℂ) + I * v‖ :=
    norm_pos_iff.mpr htarget
  have hcNorm : 0 < ‖(u : ℂ) + I * lambda‖ :=
    norm_pos_iff.mpr hcenter
  simp only [abs_mul]
  rw [abs_of_nonneg (norm_nonneg ((u : ℂ) + I * v)),
    abs_of_nonneg
      (div_nonneg (norm_nonneg _) (norm_nonneg _))]
  field_simp [htNorm.ne', hcNorm.ne']
  rw [abs_of_nonneg (norm_nonneg ((u : ℂ) + I * lambda))]
  ring

/-- Explicit envelope constant for a centered projected Psi kernel. -/
def projectedPsiKernelAtCenterEnvelopeConstant
    (A : ℂ[X]) (w : ℂ) : ℝ :=
  (2 / ‖w‖) * max ‖w‖ 1 * polynomialGaussianEnvelopeConstant A

theorem projectedPsiKernelAtCenterEnvelopeConstant_nonneg
    (A : ℂ[X]) (w : ℂ) :
    0 ≤ projectedPsiKernelAtCenterEnvelopeConstant A w := by
  unfold projectedPsiKernelAtCenterEnvelopeConstant
  exact mul_nonneg
    (mul_nonneg
      (div_nonneg (by norm_num) (norm_nonneg w))
      (le_trans (norm_nonneg w) (le_max_left ‖w‖ 1)))
    (polynomialGaussianEnvelopeConstant_nonneg A)

/-- Pointwise Hermite-Gaussian envelope for a centered projected Psi
kernel, with a named finite coefficient constant. -/
theorem projectedPsiKernelAtCenter_abs_le_scaled_exp_abs_mul
    (q : ℝ) (A : ℂ[X]) {w : ℂ} (hw : w ≠ 0)
    (m : ℝ) (hm : 1 ≤ m) (y : ℝ) :
    |projectedPsiKernelAtCenter q A w m y| ≤
      projectedPsiKernelAtCenterEnvelopeConstant A w *
        Real.exp |(Real.sqrt m)⁻¹ * (q * m - y)| *
        normalizedGaussian m (q * m - y) := by
  have hnormPos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  let t : ℝ := q * m - y
  have hsum' :
      ‖polynomialGaussianKernel A m t‖ +
          ‖polynomialGaussianKernelDeriv A m t‖ ≤
        polynomialGaussianEnvelopeConstant A *
          Real.exp |(Real.sqrt m)⁻¹ * t| *
          normalizedGaussian m t := by
    exact
      polynomialGaussianKernel_add_deriv_norm_le_scaled_exp_abs_mul
        A hm t
  have hweighted :
      ‖w‖ * ‖polynomialGaussianKernel A m t‖ +
          ‖polynomialGaussianKernelDeriv A m t‖ ≤
        max ‖w‖ 1 *
          (‖polynomialGaussianKernel A m t‖ +
            ‖polynomialGaussianKernelDeriv A m t‖) := by
    have hwLe : ‖w‖ ≤ max ‖w‖ 1 := le_max_left _ _
    have honeLe : 1 ≤ max ‖w‖ 1 := le_max_right _ _
    nlinarith [norm_nonneg (polynomialGaussianKernel A m t),
      norm_nonneg (polynomialGaussianKernelDeriv A m t)]
  unfold projectedPsiKernelAtCenter
  rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 2 / ‖w‖)]
  calc
    2 / ‖w‖ *
          |(Complex.exp (-(I * (w.im : ℂ) * (y : ℂ))) *
            (w * polynomialGaussianKernel A m t +
              polynomialGaussianKernelDeriv A m t)).re| ≤
        2 / ‖w‖ *
          ‖Complex.exp (-(I * (w.im : ℂ) * (y : ℂ))) *
            (w * polynomialGaussianKernel A m t +
              polynomialGaussianKernelDeriv A m t)‖ := by
      gcongr
      exact abs_re_le_norm _
    _ = 2 / ‖w‖ *
          ‖w * polynomialGaussianKernel A m t +
            polynomialGaussianKernelDeriv A m t‖ := by
      rw [norm_mul, Complex.norm_exp]
      norm_num [Complex.mul_re]
    _ ≤ 2 / ‖w‖ *
          (‖w‖ * ‖polynomialGaussianKernel A m t‖ +
            ‖polynomialGaussianKernelDeriv A m t‖) := by
      gcongr
      calc
        ‖w * polynomialGaussianKernel A m t +
            polynomialGaussianKernelDeriv A m t‖ ≤
            ‖w * polynomialGaussianKernel A m t‖ +
              ‖polynomialGaussianKernelDeriv A m t‖ :=
          norm_add_le _ _
        _ = ‖w‖ * ‖polynomialGaussianKernel A m t‖ +
              ‖polynomialGaussianKernelDeriv A m t‖ := by
          rw [norm_mul]
    _ ≤ 2 / ‖w‖ *
          (max ‖w‖ 1 *
            (‖polynomialGaussianKernel A m t‖ +
              ‖polynomialGaussianKernelDeriv A m t‖)) := by
      gcongr
    _ ≤ 2 / ‖w‖ *
          (max ‖w‖ 1 *
            (polynomialGaussianEnvelopeConstant A *
              Real.exp |(Real.sqrt m)⁻¹ * t| *
              normalizedGaussian m t)) := by
      gcongr
    _ = projectedPsiKernelAtCenterEnvelopeConstant A w *
          Real.exp |(Real.sqrt m)⁻¹ * (q * m - y)| *
          normalizedGaussian m (q * m - y) := by
      unfold projectedPsiKernelAtCenterEnvelopeConstant
      dsimp [t]
      ring

private theorem exists_projectedPsiKernelAtCenter_norm_le_scaled_exp_abs_mul
    (q : ℝ) (A : ℂ[X]) {w : ℂ} (hw : w ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ m : ℝ, 1 ≤ m → ∀ y : ℝ,
        |projectedPsiKernelAtCenter q A w m y| ≤
          C *
            Real.exp
              |(Real.sqrt m)⁻¹ * (q * m - y)| *
            normalizedGaussian m (q * m - y) := by
  exact
    ⟨projectedPsiKernelAtCenterEnvelopeConstant A w,
      projectedPsiKernelAtCenterEnvelopeConstant_nonneg A w,
      fun m hm y =>
        projectedPsiKernelAtCenter_abs_le_scaled_exp_abs_mul
          q A hw m hm y⟩

private theorem normalizedPsiError_le_exp_growth_centered
    {u v y : ℝ} (hu : 0 < u) (hu1 : u < 1) (hy : 0 ≤ y) :
    |normalizedPsiError ((u : ℂ) + I * v) y| ≤
      ‖(u : ℂ) + I * v‖ * (Real.log 4 + 5) *
        Real.exp ((1 - u) * y) := by
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
  rw [abs_mul, abs_mul,
    abs_of_nonneg (norm_nonneg ((u : ℂ) + I * v)),
    abs_of_pos (Real.exp_pos _)]
  have hre : (((u : ℂ) + I * v).re) = u := by
    norm_num [Complex.mul_re]
  rw [hre]
  calc
    ‖(u : ℂ) + I * v‖ *
          |chebyshevPsi (Real.exp y) - Real.exp y| *
          Real.exp (-u * y) ≤
        ‖(u : ℂ) + I * v‖ *
          ((Real.log 4 + 5) * Real.exp y) *
          Real.exp (-u * y) := by
      gcongr
    _ = ‖(u : ℂ) + I * v‖ * (Real.log 4 + 5) *
          Real.exp ((1 - u) * y) := by
      calc
        ‖(u : ℂ) + I * v‖ *
              ((Real.log 4 + 5) * Real.exp y) *
              Real.exp (-u * y) =
            ‖(u : ℂ) + I * v‖ * (Real.log 4 + 5) *
              (Real.exp y * Real.exp (-u * y)) := by ring
        _ = ‖(u : ℂ) + I * v‖ * (Real.log 4 + 5) *
              Real.exp (y + -u * y) := by rw [Real.exp_add]
        _ = _ := by congr 2 <;> ring

theorem continuous_projectedPsiKernelAtCenter
    (q : ℝ) (A : ℂ[X]) (w : ℂ) {m : ℝ} (hm : 0 < m) :
    Continuous (projectedPsiKernelAtCenter q A w m) := by
  unfold projectedPsiKernelAtCenter
  apply Continuous.const_mul
  apply Complex.continuous_re.comp
  apply Continuous.mul
  · fun_prop
  · apply Continuous.add
    · exact continuous_const.mul
        ((continuous_polynomialGaussianKernel A hm).comp (by fun_prop))
    · exact
        (continuous_polynomialGaussianKernelDeriv A hm).comp (by fun_prop)

private theorem measurable_normalizedPsiError_centered
    (w : ℂ) :
    Measurable (normalizedPsiError w) := by
  have hpsi : Measurable chebyshevPsi := by
    change Measurable (Chebyshev.psi : ℝ → ℝ)
    simpa only [chebyshevPsi_eq_mathlib] using
      Chebyshev.psi_mono.measurable
  unfold normalizedPsiError
  fun_prop

private theorem radius_margin_eight_le
    {q d : ℝ} (hq : 0 < q) (hd : 0 < d)
    (hmargin : 16 * (q + d) ≤ d ^ 2) :
    8 ≤ d := by
  by_contra h
  have hdlt : d < 8 := lt_of_not_ge h
  have hprod :
      d * (d - 16) < 0 :=
    mul_neg_of_pos_of_neg hd (by linarith)
  nlinarith

private theorem centered_true_tail_exponent_le
    {q d m y : ℝ} (hq : 0 < q) (hd : 0 < d)
    (hmargin : 16 * (q + d) ≤ d ^ 2)
    (hm : 1 ≤ m) (hy : 0 < y)
    (hout :
      y < (q - d) * m ∨ (q + d) * m < y) :
    y + |(Real.sqrt m)⁻¹ * (q * m - y)| -
        (q * m - y) ^ 2 / (4 * m) ≤
      -q * m - (q * m - y) ^ 2 / (8 * m) := by
  have hmPos : 0 < m := zero_lt_one.trans_le hm
  have hsqrtOne : 1 ≤ Real.sqrt m := by
    simpa using Real.sqrt_le_sqrt hm
  have hinvNonneg : 0 ≤ (Real.sqrt m)⁻¹ :=
    inv_nonneg.mpr (Real.sqrt_nonneg m)
  have hinvLe : (Real.sqrt m)⁻¹ ≤ 1 := by
    exact (inv_le_one₀ (Real.sqrt_pos.2 hmPos)).2 hsqrtOne
  let t : ℝ := q * m - y
  have hscaled :
      |(Real.sqrt m)⁻¹ * t| ≤ |t| := by
    rw [abs_mul, abs_of_nonneg hinvNonneg]
    nlinarith [abs_nonneg t]
  have hdEight : 8 ≤ d :=
    radius_margin_eight_le hq hd hmargin
  have hmarginM :
      16 * (q + d) * m ^ 2 ≤ d ^ 2 * m ^ 2 :=
    mul_le_mul_of_nonneg_right hmargin (sq_nonneg m)
  rcases hout with hlow | hhigh
  · have htLower : d * m < t := by
      dsimp [t]
      linarith
    have htPos : 0 < t :=
      (mul_pos hd hmPos).trans htLower
    have habs : |t| = t := abs_of_pos htPos
    have htSquare :
        (d * m) ^ 2 ≤ t ^ 2 := by
      have hfactor :
          0 ≤ (t - d * m) * (t + d * m) :=
        mul_nonneg (sub_nonneg.mpr htLower.le)
          (add_nonneg htPos.le (mul_nonneg hd.le hmPos.le))
      nlinarith
    have hquad :
        2 * q * m ≤ t ^ 2 / (8 * m) := by
      field_simp [hmPos.ne']
      nlinarith
    have hquarter :
        t ^ 2 / (4 * m) = 2 * (t ^ 2 / (8 * m)) := by
      field_simp [hmPos.ne']
      ring
    calc
      y + |(Real.sqrt m)⁻¹ * (q * m - y)| -
            (q * m - y) ^ 2 / (4 * m) =
          y + |(Real.sqrt m)⁻¹ * t| - t ^ 2 / (4 * m) := by
        rfl
      _ ≤ y + t - t ^ 2 / (4 * m) := by
        rw [habs] at hscaled
        linarith
      _ = q * m - t ^ 2 / (4 * m) := by
        dsimp [t]
        ring
      _ ≤ -q * m - t ^ 2 / (8 * m) := by
        rw [hquarter]
        linarith
      _ = -q * m - (q * m - y) ^ 2 / (8 * m) := by
        rfl
  · let r : ℝ := -t
    have hrLower : d * m < r := by
      dsimp [r, t]
      linarith
    have hrPos : 0 < r :=
      (mul_pos hd hmPos).trans hrLower
    have habs : |t| = r := by
      dsimp [r]
      rw [abs_of_neg (by linarith)]
    have hsecond :
        0 ≤ r + d * m - 16 * m := by
      have hdm : 8 * m ≤ d * m :=
        mul_le_mul_of_nonneg_right hdEight hmPos.le
      linarith
    have hfactor :
        0 ≤ (r - d * m) * (r + d * m - 16 * m) :=
      mul_nonneg (sub_nonneg.mpr hrLower.le) hsecond
    have hquadNumerator :
        16 * q * m ^ 2 + 16 * r * m ≤ r ^ 2 := by
      nlinarith
    have hquad :
        2 * q * m + 2 * r ≤ r ^ 2 / (8 * m) := by
      field_simp [hmPos.ne']
      nlinarith
    have hquarter :
        r ^ 2 / (4 * m) = 2 * (r ^ 2 / (8 * m)) := by
      field_simp [hmPos.ne']
      ring
    calc
      y + |(Real.sqrt m)⁻¹ * (q * m - y)| -
            (q * m - y) ^ 2 / (4 * m) =
          y + |(Real.sqrt m)⁻¹ * t| - t ^ 2 / (4 * m) := by
        rfl
      _ ≤ y + r - t ^ 2 / (4 * m) := by
        rw [habs] at hscaled
        linarith
      _ = q * m + 2 * r - r ^ 2 / (4 * m) := by
        dsimp [r, t]
        ring
      _ ≤ -q * m - r ^ 2 / (8 * m) := by
        rw [hquarter]
        linarith
      _ = -q * m - (q * m - y) ^ 2 / (8 * m) := by
        dsimp [r, t]
        ring

private theorem
    exp_mul_scaled_abs_mul_normalizedGaussian_tailAtCenter_le
    {q d m y : ℝ} (hq : 0 < q) (hd : 0 < d)
    (hmargin : 16 * (q + d) ≤ d ^ 2)
    (hm : 1 ≤ m) (hy : 0 < y)
    (hout :
      y < (q - d) * m ∨ (q + d) * m < y) :
    Real.exp y *
        Real.exp |(Real.sqrt m)⁻¹ * (q * m - y)| *
        normalizedGaussian m (q * m - y) ≤
      2 * Real.exp (-q * m) *
        normalizedGaussian (2 * m) (q * m - y) := by
  have hmPos : 0 < m := zero_lt_one.trans_le hm
  let t : ℝ := q * m - y
  have hexponent :=
    centered_true_tail_exponent_le hq hd hmargin hm hy hout
  have hexp :
      Real.exp y *
          Real.exp |(Real.sqrt m)⁻¹ * t| *
          Real.exp (-t ^ 2 / (4 * m)) ≤
        Real.exp (-q * m) *
          Real.exp (-t ^ 2 / (8 * m)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    convert hexponent using 1 <;> ring
  have hroot :
      Real.sqrt (Real.pi * (2 * m)) =
        Real.sqrt 2 * Real.sqrt (Real.pi * m) := by
    calc
      Real.sqrt (Real.pi * (2 * m)) =
          Real.sqrt (2 * (Real.pi * m)) := by ring_nf
      _ = Real.sqrt 2 * Real.sqrt (Real.pi * m) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrtTwo : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hrootLe :
      Real.sqrt (Real.pi * (2 * m)) ≤
        2 * Real.sqrt (Real.pi * m) := by
    rw [hroot]
    exact mul_le_mul_of_nonneg_right hsqrtTwo
      (Real.sqrt_nonneg _)
  have hdenom : 0 < 2 * Real.sqrt (Real.pi * m) := by
    positivity
  have hdenomTwo : 0 < 2 * Real.sqrt (Real.pi * (2 * m)) := by
    positivity
  dsimp [t] at hexp
  unfold normalizedGaussian
  calc
    Real.exp y *
          Real.exp |(Real.sqrt m)⁻¹ * (q * m - y)| *
          (Real.exp (-(q * m - y) ^ 2 / (4 * m)) /
            (2 * Real.sqrt (Real.pi * m))) =
        (Real.exp y *
          Real.exp |(Real.sqrt m)⁻¹ * (q * m - y)| *
          Real.exp (-(q * m - y) ^ 2 / (4 * m))) /
            (2 * Real.sqrt (Real.pi * m)) := by ring
    _ ≤
        (Real.exp (-q * m) *
          Real.exp (-(q * m - y) ^ 2 / (8 * m))) /
            (2 * Real.sqrt (Real.pi * m)) :=
      div_le_div_of_nonneg_right hexp hdenom.le
    _ ≤
        2 * Real.exp (-q * m) *
          (Real.exp (-(q * m - y) ^ 2 / (4 * (2 * m))) /
            (2 * Real.sqrt (Real.pi * (2 * m)))) := by
      have hnum :
          0 ≤ Real.exp (-q * m) *
            Real.exp (-(q * m - y) ^ 2 / (8 * m)) := by
        positivity
      rw [show
          -(q * m - y) ^ 2 / (4 * (2 * m)) =
            -(q * m - y) ^ 2 / (8 * m) by ring]
      rw [show
          2 * Real.exp (-q * m) *
              (Real.exp (-(q * m - y) ^ 2 / (8 * m)) /
                (2 * Real.sqrt (Real.pi * (2 * m)))) =
            (2 * Real.exp (-q * m) *
              Real.exp (-(q * m - y) ^ 2 / (8 * m))) /
                (2 * Real.sqrt (Real.pi * (2 * m))) by ring]
      apply (div_le_div_iff₀ hdenom hdenomTwo).2
      have hdenomLe :
          2 * Real.sqrt (Real.pi * (2 * m)) ≤
            2 * (2 * Real.sqrt (Real.pi * m)) := by
        nlinarith
      calc
        (Real.exp (-q * m) *
              Real.exp (-(q * m - y) ^ 2 / (8 * m))) *
            (2 * Real.sqrt (Real.pi * (2 * m))) ≤
          (Real.exp (-q * m) *
              Real.exp (-(q * m - y) ^ 2 / (8 * m))) *
            (2 * (2 * Real.sqrt (Real.pi * m))) :=
          mul_le_mul_of_nonneg_left hdenomLe hnum
        _ =
            (2 * Real.exp (-q * m) *
              Real.exp (-(q * m - y) ^ 2 / (8 * m))) *
              (2 * Real.sqrt (Real.pi * m)) := by ring

private theorem exists_projectedPsiTailRemainderAtCenter_exp_bound
    (q d : ℝ) (A : ℂ[X])
    (hq : 0 < q) (hd : 0 < d) (hdq : d < q)
    (hmargin : 16 * (q + d) ≤ d ^ 2)
    {u v : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ m : ℝ, 1 ≤ m →
        projectedPsiTailRemainderAtCenter q d A
            ((u : ℂ) + I * v) m ≤
          D * (2 * Real.exp (-q * m)) := by
  let w : ℂ := (u : ℂ) + I * v
  have hw0 : w ≠ 0 := by
    apply ne_zero_of_re_pos
    simpa [w] using hu
  obtain ⟨C, hC, hkernel⟩ :=
    exists_projectedPsiKernelAtCenter_norm_le_scaled_exp_abs_mul q A hw0
  let N : ℝ := ‖w‖ * (Real.log 4 + 5)
  let D : ℝ := N * C
  have hlog : 0 ≤ Real.log 4 + 5 := by
    have := Real.log_pos (by norm_num : 1 < (4 : ℝ))
    linarith
  have hN : 0 ≤ N := mul_nonneg (norm_nonneg w) hlog
  have hDnonneg : 0 ≤ D := mul_nonneg hN hC
  refine ⟨D, hDnonneg, ?_⟩
  intro m hm
  have hmPos : 0 < m := zero_lt_one.trans_le hm
  let tail : Set ℝ :=
    Set.Ioi 0 \ localizedGaussianLogWindow q d m
  let major : ℝ → ℝ := fun y =>
    D * (2 * Real.exp (-q * m) *
      normalizedGaussian (2 * m) (q * m - y))
  have htailMeasurable : MeasurableSet tail := by
    exact measurableSet_Ioi.diff
      (measurableSet_Icc :
        MeasurableSet (localizedGaussianLogWindow q d m))
  have hmajorInt : Integrable major := by
    have htwoM : 0 < 2 * m := by positivity
    have hshift :
        Integrable
          (fun y => normalizedGaussian (2 * m) (q * m - y)) :=
      (integrable_normalizedGaussian htwoM).comp_sub_left (q * m)
    exact (hshift.const_mul (2 * Real.exp (-q * m))).const_mul D
  have hpointwise :
      ∀ y ∈ tail,
        |normalizedPsiError w y *
            projectedPsiKernelAtCenter q A w m y| ≤
          major y := by
    intro y hy
    have hyPos : 0 < y := hy.1
    have hyNonneg : 0 ≤ y := hyPos.le
    have herror :=
      normalizedPsiError_le_exp_growth_centered
        (v := v) hu hu1 hyNonneg
    have herror' :
        |normalizedPsiError w y| ≤ N * Real.exp y := by
      have hexp :
          Real.exp ((1 - u) * y) ≤ Real.exp y := by
        apply Real.exp_le_exp.mpr
        nlinarith
      simpa only [w, N] using herror.trans
        (mul_le_mul_of_nonneg_left hexp
          (mul_nonneg (norm_nonneg w) hlog))
    have hkernel' := hkernel m hm y
    have hproduct :
        |normalizedPsiError w y *
            projectedPsiKernelAtCenter q A w m y| ≤
          D * (Real.exp y *
            Real.exp |(Real.sqrt m)⁻¹ * (q * m - y)| *
            normalizedGaussian m (q * m - y)) := by
      rw [abs_mul]
      calc
        |normalizedPsiError w y| *
              |projectedPsiKernelAtCenter q A w m y| ≤
            (N * Real.exp y) *
              (C *
                Real.exp |(Real.sqrt m)⁻¹ * (q * m - y)| *
                normalizedGaussian m (q * m - y)) :=
          mul_le_mul herror' hkernel' (abs_nonneg _) (by positivity)
        _ = D * (Real.exp y *
              Real.exp |(Real.sqrt m)⁻¹ * (q * m - y)| *
              normalizedGaussian m (q * m - y)) := by
          dsimp [D]
          ring
    have houtside :
        y < (q - d) * m ∨ (q + d) * m < y := by
      simpa only [localizedGaussianLogWindow, Set.mem_Icc,
        not_and_or, not_le] using hy.2
    have htailBound :=
      exp_mul_scaled_abs_mul_normalizedGaussian_tailAtCenter_le
        hq hd hmargin hm hyPos houtside
    calc
      |normalizedPsiError w y *
          projectedPsiKernelAtCenter q A w m y| ≤
        D * (Real.exp y *
          Real.exp |(Real.sqrt m)⁻¹ * (q * m - y)| *
          normalizedGaussian m (q * m - y)) :=
        hproduct
      _ ≤ D * (2 * Real.exp (-q * m) *
          normalizedGaussian (2 * m) (q * m - y)) :=
        mul_le_mul_of_nonneg_left htailBound hDnonneg
      _ = major y := by rfl
  have hsourceAES :
      AEStronglyMeasurable
        (fun y =>
          |normalizedPsiError w y *
            projectedPsiKernelAtCenter q A w m y|)
        (volume.restrict tail) := by
    have hmeas :
        Measurable
          (fun y =>
            |normalizedPsiError w y *
              projectedPsiKernelAtCenter q A w m y|) :=
      ((measurable_normalizedPsiError_centered w).mul
        (continuous_projectedPsiKernelAtCenter
          q A w hmPos).measurable).abs
    exact hmeas.aestronglyMeasurable
  have hsourceInt :
      IntegrableOn
        (fun y =>
          |normalizedPsiError w y *
            projectedPsiKernelAtCenter q A w m y|)
        tail := by
    refine hmajorInt.integrableOn.mono' hsourceAES ?_
    filter_upwards [ae_restrict_mem htailMeasurable] with y hy
    simpa [Real.norm_eq_abs, abs_of_nonneg] using hpointwise y hy
  unfold projectedPsiTailRemainderAtCenter
  change (∫ y : ℝ in tail,
      |normalizedPsiError w y *
        projectedPsiKernelAtCenter q A w m y|) ≤ _
  calc
    (∫ y : ℝ in tail,
        |normalizedPsiError w y *
          projectedPsiKernelAtCenter q A w m y|) ≤
        ∫ y : ℝ in tail, major y := by
      exact setIntegral_mono_on hsourceInt hmajorInt.integrableOn
        htailMeasurable hpointwise
    _ ≤ ∫ y : ℝ, major y :=
      setIntegral_le_integral hmajorInt
        (Filter.Eventually.of_forall fun y => by
          dsimp [major]
          exact mul_nonneg hDnonneg
            (mul_nonneg (by positivity)
              (normalizedGaussian_pos (by positivity) _).le))
    _ = D * (2 * Real.exp (-q * m)) := by
      dsimp [major]
      rw [integral_const_mul, integral_const_mul,
        MeasureTheory.integral_sub_left_eq_self
          (normalizedGaussian (2 * m)) volume (q * m),
        integral_normalizedGaussian (by positivity : 0 < 2 * m)]
      ring

/-- The true target-normalized PNT-error contribution outside the centered
window tends to zero. -/
theorem tendsto_projectedPsiTailRemainderAtCenter
    (q d : ℝ) (A : ℂ[X])
    (hq : 0 < q) (hd : 0 < d) (hdq : d < q)
    (hmargin : 16 * (q + d) ≤ d ^ 2)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) (v : ℝ) :
    Tendsto
      (projectedPsiTailRemainderAtCenter q d A
        ((u : ℂ) + I * v))
      atTop (𝓝 0) := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_projectedPsiTailRemainderAtCenter_exp_bound
      q d A hq hd hdq hmargin hu hu1
  have hlinear :
      Tendsto (fun m : ℝ => -q * m) atTop atBot := by
    simpa [Function.comp_def, id_eq, neg_mul] using
      tendsto_neg_atTop_atBot.comp
        (tendsto_id.const_mul_atTop hq)
  have hupper :
      Tendsto
        (fun m : ℝ => D * (2 * Real.exp (-q * m)))
        atTop (𝓝 0) := by
    have hexp :
        Tendsto (fun m : ℝ => Real.exp (-q * m))
          atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp hlinear
    simpa using
      tendsto_const_nhds.mul (tendsto_const_nhds.mul hexp)
  apply squeeze_zero'
  · filter_upwards with m
    unfold projectedPsiTailRemainderAtCenter
    exact integral_nonneg fun _ => abs_nonneg _
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with m hm
    exact hbound m hm
  · exact hupper

/-- Relative centered tails tend to zero without replacing the target
normalization by the contour center. -/
theorem tendsto_relativeProjectedPsiTailRemainderAtCenter
    (q d : ℝ) (c : ℂ) (A : ℂ[X])
    (hq : 0 < q) (hd : 0 < d) (hdq : d < q)
    (hmargin : 16 * (q + d) ≤ d ^ 2)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1)
    (v lambda : ℝ) :
    Tendsto
      (relativeProjectedPsiTailRemainderAtCenter q d A
        ((u : ℂ) + I * v) ((u : ℂ) + I * lambda) c)
      atTop (𝓝 0) := by
  have htarget : (u : ℂ) + I * v ≠ 0 := by
    apply ne_zero_of_re_pos
    simpa only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
      zero_mul, one_mul, sub_zero, add_zero] using hu
  have hcenter : (u : ℂ) + I * lambda ≠ 0 := by
    apply ne_zero_of_re_pos
    simpa only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
      zero_mul, one_mul, sub_zero, add_zero] using hu
  change Tendsto (fun m =>
      relativeProjectedPsiTailRemainderAtCenter q d A
        ((u : ℂ) + I * v) ((u : ℂ) + I * lambda) c m)
      atTop (𝓝 0)
  rw [show (fun m =>
      relativeProjectedPsiTailRemainderAtCenter q d A
        ((u : ℂ) + I * v) ((u : ℂ) + I * lambda) c m) =
      fun m =>
        projectedPsiTailRemainderAtCenter q d (C c * A)
          ((u : ℂ) + I * lambda) m by
      funext m
      exact relativeProjectedPsiTailRemainderAtCenter_eq
        q d c A htarget hcenter]
  exact tendsto_projectedPsiTailRemainderAtCenter
    q d (C c * A) hq hd hdq hmargin hu hu1 lambda

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
