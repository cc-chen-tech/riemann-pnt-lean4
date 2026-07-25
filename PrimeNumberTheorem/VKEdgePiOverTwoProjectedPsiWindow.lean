import Mathlib.MeasureTheory.Function.JacobianOneDim
import PrimeNumberTheorem.VKEdgePiOverTwoConcreteLocalizedData
import PrimeNumberTheorem.VKEdgePiOverTwoGaussianTail

open Complex Filter MeasureTheory Polynomial Set Topology

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- The real dual kernel obtained by projecting the concrete Gaussian
Mellin integral in the direction which makes the target zero residue
positive. -/
def projectedPsiKernel
    (A : ℂ[X]) (w : ℂ) (m y : ℝ) : ℝ :=
  -(2 / ‖w‖) *
    (Complex.exp
        (-(I * (w.im : ℂ) * (y : ℂ))) *
      (w * polynomialGaussianKernel A m (16 * m - y) +
        polynomialGaussianKernelDeriv A m (16 * m - y))).re

/-- The absolute projected-kernel mass inside the logarithmic Gaussian
window. -/
def projectedPsiCoefficient
    (A : ℂ[X]) (w : ℂ) (m : ℝ) : ℝ :=
  ∫ y : ℝ in gaussianLogWindow m, |projectedPsiKernel A w m y|

/-- The absolute contribution of the normalized PNT error outside the
logarithmic Gaussian window. -/
def projectedPsiTailRemainder
    (A : ℂ[X]) (w : ℂ) (m : ℝ) : ℝ :=
  ∫ y : ℝ in Set.Ioi 0 \ gaussianLogWindow m,
    |normalizedPsiError w y * projectedPsiKernel A w m y|

private def logarithmicLocalizedPsiGaussianIntegrand
    (A : ℂ[X]) (w : ℂ) (m y : ℝ) : ℂ :=
  ((chebyshevPsi (Real.exp y) - Real.exp y : ℝ) : ℂ) *
    ((2 * Real.pi : ℂ) *
      (Complex.exp (-(w * (y : ℂ))) *
        (w * polynomialGaussianKernel A m (16 * m - y) +
          polynomialGaussianKernelDeriv A m (16 * m - y))))

private lemma image_exp_Ioi_zero :
    Real.exp '' Set.Ioi (0 : ℝ) = Set.Ioi (1 : ℝ) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using Real.exp_lt_exp.mpr hy
  · intro hx
    have hx0 : 0 < x := zero_lt_one.trans hx
    refine ⟨Real.log x, Real.log_pos hx, ?_⟩
    exact Real.exp_log hx0

private lemma exp_mul_cpow_neg_add_one
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

/-- Exact logarithmic-coordinate form of the concrete Chebyshev-error
Gaussian average. -/
theorem localizedPsiGaussianAverage_eq_logarithmic
    (A : ℂ[X]) (w : ℂ) (m : ℝ) :
    localizedPsiGaussianAverage A w m =
      ∫ y : ℝ in Set.Ioi 0,
        logarithmicLocalizedPsiGaussianIntegrand A w m y := by
  let g : ℝ → ℂ := fun x =>
    psiErrorAboveOneComplex x *
      ((2 * Real.pi : ℂ) *
        ((x : ℂ) ^ (-(w + 1)) *
          (w * polynomialGaussianKernel A m
              (16 * m - Real.log x) +
            polynomialGaussianKernelDeriv A m
              (16 * m - Real.log x))))
  have hchange :=
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      (s := Set.Ioi (0 : ℝ))
      (f := Real.exp) (f' := Real.exp)
      measurableSet_Ioi
      (fun y _hy => (Real.hasDerivAt_exp y).hasDerivWithinAt)
      Real.exp_injective.injOn g
  rw [image_exp_Ioi_zero] at hchange
  have hintegrand :
      (fun y : ℝ => |Real.exp y| • g (Real.exp y)) =
        logarithmicLocalizedPsiGaussianIntegrand A w m := by
    funext y
    have hyPos : 0 < Real.exp y := Real.exp_pos y
    simp only [abs_of_pos hyPos, g, Complex.real_smul]
    rw [show psiErrorAboveOneComplex (Real.exp y) =
        ((chebyshevPsi (Real.exp y) - Real.exp y : ℝ) : ℂ) by
      simp [psiErrorAboveOneComplex, psiErrorAboveOne,
        Real.exp_pos y, Real.exp_pos y |>.one_le]]
    rw [Real.log_exp]
    unfold logarithmicLocalizedPsiGaussianIntegrand
    rw [exp_mul_cpow_neg_add_one]
    ring
  unfold localizedPsiGaussianAverage
  change (∫ x : ℝ in Set.Ioi 1, g x) = _
  rw [← hintegrand]
  exact hchange

private theorem integrableOn_logarithmicLocalizedPsiGaussianIntegrand
    (A : ℂ[X]) {w : ℂ} {m : ℝ}
    (hm : 0 < m) (hw : 0 < w.re) :
    IntegrableOn
      (logarithmicLocalizedPsiGaussianIntegrand A w m)
      (Set.Ioi 0) := by
  let h := integrable_rightEdgeMellinProduct A hm hw
  have hsections :
      Integrable
        (fun x : ℝ =>
          ∫ t : ℝ, rightEdgeMellinProduct A m w (t, x))
        (volume.restrict (Set.Ioi (1 : ℝ))) :=
    h.integral_prod_right
  have hxIntegrable :
      IntegrableOn
        (fun x : ℝ =>
          psiErrorAboveOneComplex x *
            ((2 * Real.pi : ℂ) *
              ((x : ℂ) ^ (-(w + 1)) *
                (w * polynomialGaussianKernel A m
                    (16 * m - Real.log x) +
                  polynomialGaussianKernelDeriv A m
                    (16 * m - Real.log x)))))
        (Set.Ioi 1) := by
    refine hsections.congr_fun ?_ measurableSet_Ioi
    intro x hx
    exact integral_rightEdgeMellinProduct_fst_eq
      A hm w (zero_lt_one.trans hx)
  let g : ℝ → ℂ := fun x =>
    psiErrorAboveOneComplex x *
      ((2 * Real.pi : ℂ) *
        ((x : ℂ) ^ (-(w + 1)) *
          (w * polynomialGaussianKernel A m
              (16 * m - Real.log x) +
            polynomialGaussianKernelDeriv A m
              (16 * m - Real.log x))))
  have hchange :=
    integrableOn_image_iff_integrableOn_abs_deriv_smul
      (s := Set.Ioi (0 : ℝ))
      (f := Real.exp) (f' := Real.exp)
      measurableSet_Ioi
      (fun y _hy => (Real.hasDerivAt_exp y).hasDerivWithinAt)
      Real.exp_injective.injOn g
  rw [image_exp_Ioi_zero] at hchange
  have htrans :
      IntegrableOn
        (fun y : ℝ => |Real.exp y| • g (Real.exp y))
        (Set.Ioi 0) :=
    hchange.mp hxIntegrable
  refine htrans.congr_fun ?_ measurableSet_Ioi
  intro y _hy
  have hyPos : 0 < Real.exp y := Real.exp_pos y
  simp only [abs_of_pos hyPos, g, Complex.real_smul]
  rw [show psiErrorAboveOneComplex (Real.exp y) =
      ((chebyshevPsi (Real.exp y) - Real.exp y : ℝ) : ℂ) by
    simp [psiErrorAboveOneComplex, psiErrorAboveOne,
      Real.exp_pos y, Real.exp_pos y |>.one_le]]
  rw [Real.log_exp]
  unfold logarithmicLocalizedPsiGaussianIntegrand
  rw [exp_mul_cpow_neg_add_one]
  ring

private theorem logarithmicLocalizedPsiGaussianIntegrand_re
    {A : ℂ[X]} {w : ℂ} {m y : ℝ}
    (hw : w ≠ 0) :
    -(logarithmicLocalizedPsiGaussianIntegrand A w m y).re /
        Real.pi =
      normalizedPsiError w y * projectedPsiKernel A w m y := by
  have hnormPos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hexpSplit :
      Complex.exp (-(w * (y : ℂ))) =
        (Real.exp (-w.re * y) : ℂ) *
          Complex.exp (-(I * (w.im : ℂ) * (y : ℂ))) := by
    rw [← Complex.exp_ofReal_re, ← Complex.exp_add]
    congr 1
    apply Complex.ext
    · simp [Complex.mul_re]
    · simp [Complex.mul_im]
  unfold logarithmicLocalizedPsiGaussianIntegrand
    normalizedPsiError projectedPsiKernel
  rw [hexpSplit]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  field_simp [Real.pi_ne_zero, hnormPos.ne']
  ring

/-- The oriented real part of the concrete Gaussian average is exactly the
normalized PNT error paired with the projected real kernel. -/
theorem neg_re_localizedPsiGaussianAverage_div_pi_eq
    (A : ℂ[X]) {w : ℂ} {m : ℝ}
    (hm : 0 < m) (hw : 0 < w.re) :
    -(localizedPsiGaussianAverage A w m).re / Real.pi =
      ∫ y : ℝ in Set.Ioi 0,
        normalizedPsiError w y * projectedPsiKernel A w m y := by
  have hw0 : w ≠ 0 := ne_zero_of_re_pos hw
  have hint :=
    integrableOn_logarithmicLocalizedPsiGaussianIntegrand A hm hw
  rw [localizedPsiGaussianAverage_eq_logarithmic]
  rw [show
      (∫ y : ℝ in Set.Ioi 0,
          logarithmicLocalizedPsiGaussianIntegrand A w m y).re =
        ∫ y : ℝ in Set.Ioi 0,
          (logarithmicLocalizedPsiGaussianIntegrand A w m y).re by
    exact (integral_re hint).symm]
  rw [← integral_neg, ← integral_div]
  apply integral_congr_ae
  filter_upwards with y
  exact logarithmicLocalizedPsiGaussianIntegrand_re hw0

private theorem integrableOn_normalizedPsiError_mul_projectedPsiKernel
    (A : ℂ[X]) {w : ℂ} {m : ℝ}
    (hm : 0 < m) (hw : 0 < w.re) :
    IntegrableOn
      (fun y =>
        normalizedPsiError w y * projectedPsiKernel A w m y)
      (Set.Ioi 0) := by
  have hw0 : w ≠ 0 := ne_zero_of_re_pos hw
  have hint :=
    integrableOn_logarithmicLocalizedPsiGaussianIntegrand A hm hw
  have hre :
      IntegrableOn
        (fun y =>
          (logarithmicLocalizedPsiGaussianIntegrand A w m y).re)
        (Set.Ioi 0) :=
    hint.re
  have hscaled :
      IntegrableOn
        (fun y =>
          -(logarithmicLocalizedPsiGaussianIntegrand A w m y).re /
            Real.pi)
        (Set.Ioi 0) :=
    hre.neg.div_const Real.pi
  apply hscaled.congr_fun _ measurableSet_Ioi
  intro y _hy
  exact logarithmicLocalizedPsiGaussianIntegrand_re hw0

private theorem exists_projectedPsiKernel_norm_le_exp_abs_mul
    (A : ℂ[X]) {w : ℂ} (hw : w ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ m : ℝ, 1 ≤ m → ∀ y : ℝ,
        |projectedPsiKernel A w m y| ≤
          C * Real.exp |16 * m - y| *
            normalizedGaussian m (16 * m - y) := by
  obtain ⟨D, hD, hDbound⟩ :=
    exists_polynomialGaussianKernel_add_deriv_norm_le_exp_abs_mul A
  let C : ℝ := (2 / ‖w‖) * max ‖w‖ 1 * D
  have hnormPos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  refine ⟨C, by positivity, ?_⟩
  intro m hm y
  let t : ℝ := 16 * m - y
  have hsum := hDbound m hm t
  have hmaxNonneg : 0 ≤ max ‖w‖ 1 := by positivity
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
  unfold projectedPsiKernel
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 / ‖w‖)]
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
      exact norm_add_le _ _
    _ ≤ 2 / ‖w‖ *
          (max ‖w‖ 1 *
            (‖polynomialGaussianKernel A m t‖ +
              ‖polynomialGaussianKernelDeriv A m t‖)) := by
      gcongr
    _ ≤ 2 / ‖w‖ *
          (max ‖w‖ 1 *
            (D * Real.exp |t| * normalizedGaussian m t)) := by
      gcongr
    _ = C * Real.exp |16 * m - y| *
          normalizedGaussian m (16 * m - y) := by
      dsimp [C, t]
      ring

private theorem normalizedPsiError_le_exp_growth
    {u v y : ℝ} (hu : 0 < u) (hu1 : u < 1) (hy : 0 ≤ y) :
    |normalizedPsiError ((u : ℂ) + I * v) y| ≤
      ‖(u : ℂ) + I * v‖ * (Real.log 4 + 5) *
        Real.exp ((1 - u) * y) := by
  have hxy : 1 ≤ Real.exp y := by
    simpa using Real.exp_le_exp.mpr hy
  have hpsi :
      chebyshevPsi (Real.exp y) ≤
        (Real.log 4 + 4) * Real.exp y := by
    rw [chebyshevPsi_eq_mathlib]
    exact Chebyshev.psi_le_const_mul_self hxy
  have hpsiNonneg : 0 ≤ chebyshevPsi (Real.exp y) :=
    chebyshevPsi_nonneg _
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
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.ofReal_im, Complex.I_im, zero_mul, one_mul,
    add_zero]
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
      rw [← Real.exp_add]
      ring_nf

private theorem exp_shift_abs_mul_normalizedGaussian_rightTail_le
    {m t : ℝ} (hm : 0 < m) (ht : t ≤ -12 * m) :
    Real.exp (16 * m - t + |t|) * normalizedGaussian m t ≤
      3 * Real.exp (-6 * m) * normalizedGaussian (6 * m) t := by
  have htAbs : |t| = -t := abs_of_nonpos (by linarith)
  have hquad :
      16 * m - t + |t| - t ^ 2 / (4 * m) ≤
        -6 * m - t ^ 2 / (24 * m) := by
    rw [htAbs]
    have hq : 12 * m ≤ -t := by linarith
    have hfactor :
        (5 * (-t) + 12 * m) * ((-t) - 12 * m) ≥ 0 := by positivity
    field_simp
    nlinarith
  have hexp :
      Real.exp (16 * m - t + |t|) *
          Real.exp (-t ^ 2 / (4 * m)) ≤
        Real.exp (-6 * m) *
          Real.exp (-t ^ 2 / (24 * m)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hpim : 0 < Real.pi * m := by positivity
  have hpiSixM : 0 < Real.pi * (6 * m) := by positivity
  have hroot :
      Real.sqrt (Real.pi * (6 * m)) ≤
        3 * Real.sqrt (Real.pi * m) := by
    have hsqrtM := Real.sq_sqrt hpim.le
    have hsqrtSixM := Real.sq_sqrt hpiSixM.le
    have hleft := Real.sqrt_nonneg (Real.pi * (6 * m))
    have hright := Real.sqrt_nonneg (Real.pi * m)
    nlinarith
  have hreciprocal :
      1 / (2 * Real.sqrt (Real.pi * m)) ≤
        3 / (2 * Real.sqrt (Real.pi * (6 * m))) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  unfold normalizedGaussian
  calc
    Real.exp (16 * m - t + |t|) *
          (Real.exp (-t ^ 2 / (4 * m)) /
            (2 * Real.sqrt (Real.pi * m))) =
        (Real.exp (16 * m - t + |t|) *
          Real.exp (-t ^ 2 / (4 * m))) *
            (1 / (2 * Real.sqrt (Real.pi * m))) := by ring
    _ ≤
        (Real.exp (-6 * m) *
          Real.exp (-t ^ 2 / (24 * m))) *
            (3 / (2 * Real.sqrt (Real.pi * (6 * m)))) :=
      mul_le_mul hexp hreciprocal (by positivity) (by positivity)
    _ = 3 * Real.exp (-6 * m) *
          (Real.exp (-t ^ 2 / (4 * (6 * m))) /
            (2 * Real.sqrt (Real.pi * (6 * m)))) := by
      ring

private theorem exists_projectedPsiTailRemainder_exp_bound
    (A : ℂ[X]) {u v : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ m : ℝ, 1 ≤ m →
        projectedPsiTailRemainder A ((u : ℂ) + I * v) m ≤
          D * (2 * Real.exp (-2 * m) +
            3 * Real.exp (-6 * m)) := by
  let w : ℂ := (u : ℂ) + I * v
  have hw0 : w ≠ 0 := by
    apply ne_zero_of_re_pos
    simpa [w] using hu
  obtain ⟨C, hC, hkernel⟩ :=
    exists_projectedPsiKernel_norm_le_exp_abs_mul A hw0
  let N : ℝ := ‖w‖ * (Real.log 4 + 5)
  let D : ℝ := N * C
  have hlog : 0 ≤ Real.log 4 + 5 := by
    have := Real.log_pos (by norm_num : 1 < (4 : ℝ))
    linarith
  have hN : 0 ≤ N := mul_nonneg (norm_nonneg w) hlog
  have hDnonneg : 0 ≤ D := mul_nonneg hN hC
  refine ⟨D, hDnonneg, ?_⟩
  intro m hm
  have hmPos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  let tail : Set ℝ := Set.Ioi 0 \ gaussianLogWindow m
  let major : ℝ → ℝ := fun y =>
    D *
      (2 * Real.exp (-2 * m) *
          normalizedGaussian (2 * m) (16 * m - y) +
        3 * Real.exp (-6 * m) *
          normalizedGaussian (6 * m) (16 * m - y))
  have htailMeasurable : MeasurableSet tail := by
    exact measurableSet_Ioi.diff
      (measurableSet_Icc :
        MeasurableSet (gaussianLogWindow m))
  have hsourceInt :
      IntegrableOn
        (fun y =>
          |normalizedPsiError w y * projectedPsiKernel A w m y|)
        tail := by
    have hbase :=
      integrableOn_normalizedPsiError_mul_projectedPsiKernel
        A hmPos (by simpa [w] using hu)
    exact hbase.norm.mono_set (by
      intro y hy
      exact hy.1)
  have hmajorInt : Integrable major := by
    have htwo : 0 < 2 * m := by positivity
    have hsix : 0 < 6 * m := by positivity
    have htwoShift :
        Integrable
          (fun y => normalizedGaussian (2 * m) (16 * m - y)) :=
      (integrable_normalizedGaussian htwo).comp_sub_left (16 * m)
    have hsixShift :
        Integrable
          (fun y => normalizedGaussian (6 * m) (16 * m - y)) :=
      (integrable_normalizedGaussian hsix).comp_sub_left (16 * m)
    exact
      ((htwoShift.const_mul
          (2 * Real.exp (-2 * m))).add
        (hsixShift.const_mul
          (3 * Real.exp (-6 * m)))).const_mul D
  have hpointwise :
      ∀ y ∈ tail,
        |normalizedPsiError w y * projectedPsiKernel A w m y| ≤
          major y := by
    intro y hy
    have hyPos : 0 < y := hy.1
    have hyNonneg : 0 ≤ y := hyPos.le
    have herror :=
      normalizedPsiError_le_exp_growth hu hu1 hyNonneg
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
        |normalizedPsiError w y * projectedPsiKernel A w m y| ≤
          D * (Real.exp (y + |16 * m - y|) *
            normalizedGaussian m (16 * m - y)) := by
      rw [abs_mul]
      calc
        |normalizedPsiError w y| *
              |projectedPsiKernel A w m y| ≤
            (N * Real.exp y) *
              (C * Real.exp |16 * m - y| *
                normalizedGaussian m (16 * m - y)) :=
          mul_le_mul herror' hkernel' (abs_nonneg _) (by positivity)
        _ = D * (Real.exp (y + |16 * m - y|) *
              normalizedGaussian m (16 * m - y)) := by
          rw [Real.exp_add]
          dsimp [D]
          ring
    have houtside :
        y < 4 * m ∨ 28 * m < y := by
      simpa only [gaussianLogWindow, Set.mem_Icc,
        not_and_or, not_le] using hy.2
    rcases houtside with hlow | hhigh
    · have ht : 12 * m ≤ 16 * m - y := by linarith
      have htTail : 16 * m - y ∈ gaussianTail m := by
        rw [gaussianTail, Set.mem_setOf_eq]
        rw [abs_of_nonneg (by linarith : 0 ≤ 16 * m - y)]
        exact ht
      have hgaussian :=
        normalizedGaussian_le_doubled_scaledGaussian hmPos htTail
      have hshift :
          y + |16 * m - y| = 16 * m := by
        rw [abs_of_nonneg (by linarith : 0 ≤ 16 * m - y)]
        ring
      have hlowBound :
          Real.exp (y + |16 * m - y|) *
              normalizedGaussian m (16 * m - y) ≤
            2 * Real.exp (-2 * m) *
              normalizedGaussian (2 * m) (16 * m - y) := by
        rw [hshift]
        calc
          Real.exp (16 * m) *
                normalizedGaussian m (16 * m - y) ≤
              Real.exp (16 * m) *
                (2 * Real.exp (-18 * m) *
                  normalizedGaussian (2 * m) (16 * m - y)) := by
            gcongr
          _ = 2 * Real.exp (-2 * m) *
                normalizedGaussian (2 * m) (16 * m - y) := by
            rw [← Real.exp_add]
            ring_nf
      calc
        |normalizedPsiError w y *
              projectedPsiKernel A w m y| ≤
            D * (Real.exp (y + |16 * m - y|) *
              normalizedGaussian m (16 * m - y)) :=
          hproduct
        _ ≤ D *
            (2 * Real.exp (-2 * m) *
              normalizedGaussian (2 * m) (16 * m - y)) := by
          gcongr
        _ ≤ major y := by
          dsimp [major]
          have hsixNonneg :
              0 ≤ 3 * Real.exp (-6 * m) *
                normalizedGaussian (6 * m) (16 * m - y) := by positivity
          nlinarith [hDnonneg]
    · have ht : 16 * m - y ≤ -12 * m := by linarith
      have hhighBound :=
        exp_shift_abs_mul_normalizedGaussian_rightTail_le hmPos ht
      have hrewrite :
          y + |16 * m - y| =
            16 * m - (16 * m - y) + |16 * m - y| := by ring_nf
      calc
        |normalizedPsiError w y *
              projectedPsiKernel A w m y| ≤
            D * (Real.exp (y + |16 * m - y|) *
              normalizedGaussian m (16 * m - y)) :=
          hproduct
        _ ≤ D *
            (3 * Real.exp (-6 * m) *
              normalizedGaussian (6 * m) (16 * m - y)) := by
          rw [hrewrite]
          gcongr
        _ ≤ major y := by
          dsimp [major]
          have htwoNonneg :
              0 ≤ 2 * Real.exp (-2 * m) *
                normalizedGaussian (2 * m) (16 * m - y) := by positivity
          nlinarith [hDnonneg]
  unfold projectedPsiTailRemainder
  change (∫ y : ℝ in tail,
      |normalizedPsiError w y * projectedPsiKernel A w m y|) ≤ _
  calc
    (∫ y : ℝ in tail,
        |normalizedPsiError w y * projectedPsiKernel A w m y|) ≤
        ∫ y : ℝ in tail, major y := by
      exact setIntegral_mono_on hsourceInt hmajorInt.integrableOn
        htailMeasurable hpointwise
    _ ≤ ∫ y : ℝ, major y :=
      setIntegral_le_integral hmajorInt
        (Filter.Eventually.of_forall fun y => by
          dsimp [major]
          positivity)
    _ = D * (2 * Real.exp (-2 * m) +
          3 * Real.exp (-6 * m)) := by
      dsimp [major]
      rw [integral_const_mul, integral_add,
        integral_const_mul, integral_const_mul,
        MeasureTheory.integral_sub_left_eq_self
          (normalizedGaussian (2 * m)) volume (16 * m),
        MeasureTheory.integral_sub_left_eq_self
          (normalizedGaussian (6 * m)) volume (16 * m),
        integral_normalizedGaussian (by positivity : 0 < 2 * m),
        integral_normalizedGaussian (by positivity : 0 < 6 * m)]
      · ring
      · exact
          (integrable_normalizedGaussian (by positivity : 0 < 6 * m)).comp_sub_left
            (16 * m) |>.const_mul _
      · exact
          (integrable_normalizedGaussian (by positivity : 0 < 2 * m)).comp_sub_left
            (16 * m) |>.const_mul _

/-- For every fixed polynomial and every center in the critical strip, the
true PNT-error contribution outside `[4m,28m]` tends to zero. -/
theorem tendsto_projectedPsiTailRemainder
    (A : ℂ[X]) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) (v : ℝ) :
    Tendsto
      (projectedPsiTailRemainder A ((u : ℂ) + I * v))
      atTop (𝓝 0) := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_projectedPsiTailRemainder_exp_bound A hu hu1
  have htwoBot :
      Tendsto (fun m : ℝ => -2 * m) atTop atBot := by
    simpa only [neg_mul] using
      tendsto_neg_atTop_atBot.comp
        (tendsto_id.const_mul_atTop (by norm_num : 0 < (2 : ℝ)))
  have hsixBot :
      Tendsto (fun m : ℝ => -6 * m) atTop atBot := by
    simpa only [neg_mul] using
      tendsto_neg_atTop_atBot.comp
        (tendsto_id.const_mul_atTop (by norm_num : 0 < (6 : ℝ)))
  have hupper :
      Tendsto
        (fun m : ℝ =>
          D * (2 * Real.exp (-2 * m) +
            3 * Real.exp (-6 * m)))
        atTop (𝓝 0) := by
    have htwoExp : Tendsto (fun m : ℝ => Real.exp (-2 * m))
        atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp htwoBot
    have hsixExp : Tendsto (fun m : ℝ => Real.exp (-6 * m))
        atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp hsixBot
    simpa using
      tendsto_const_nhds.mul
        ((tendsto_const_nhds.mul htwoExp).add
          (tendsto_const_nhds.mul hsixExp))
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with m hm
    unfold projectedPsiTailRemainder
    exact integral_nonneg fun _ => abs_nonneg _
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with m hm
    exact hbound m hm
  · exact hupper

private theorem continuous_projectedPsiKernel
    (A : ℂ[X]) (w : ℂ) {m : ℝ} (hm : 0 < m) :
    Continuous (projectedPsiKernel A w m) := by
  unfold projectedPsiKernel
  apply Continuous.const_mul
  apply Continuous.re
  apply Continuous.mul
  · fun_prop
  · apply Continuous.add
    · exact continuous_const.mul
        ((continuous_polynomialGaussianKernel A hm).comp (by fun_prop))
    · exact
        (continuous_polynomialGaussianKernelDeriv A hm).comp (by fun_prop)

/-- The exact projected zeta integral is bounded by the window supremum
times the true projected-kernel mass plus the true outside-window tail. -/
theorem eventually_projectedPsiWindow_upper_bound
    (A : ℂ[X]) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) (v : ℝ) :
    ∀ᶠ m : ℝ in atTop,
      -(localizedPsiGaussianAverage A
          ((u : ℂ) + I * v) m).re / Real.pi ≤
        normalizedWindowSup ((u : ℂ) + I * v) m *
            projectedPsiCoefficient A ((u : ℂ) + I * v) m +
          projectedPsiTailRemainder A ((u : ℂ) + I * v) m := by
  have hbddEventual :=
    eventually_bddAbove_normalizedWindowValues hu hu1 (v := v)
  filter_upwards [
    eventually_ge_atTop (1 : ℝ),
    hbddEventual] with m hm hbdd
  let w : ℂ := (u : ℂ) + I * v
  let f : ℝ → ℝ := fun y =>
    normalizedPsiError w y * projectedPsiKernel A w m y
  let window : Set ℝ := gaussianLogWindow m
  let tail : Set ℝ := Set.Ioi 0 \ window
  have hmPos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hwRe : 0 < w.re := by simpa [w] using hu
  have hwindowMeasurable : MeasurableSet window := by
    exact measurableSet_Icc
  have htailMeasurable : MeasurableSet tail :=
    measurableSet_Ioi.diff hwindowMeasurable
  have hwindowSubset : window ⊆ Set.Ioi (0 : ℝ) := by
    intro y hy
    have hyLower : 4 * m ≤ y := hy.1
    exact Set.mem_Ioi.mpr (by nlinarith)
  have hfIoi : IntegrableOn f (Set.Ioi 0) := by
    simpa only [f] using
      integrableOn_normalizedPsiError_mul_projectedPsiKernel
        A hmPos hwRe
  have hfWindow : IntegrableOn f window :=
    hfIoi.mono_set hwindowSubset
  have hfTail : IntegrableOn f tail :=
    hfIoi.mono_set fun y hy => hy.1
  have hkernelWindow :
      IntegrableOn
        (fun y => |projectedPsiKernel A w m y|) window := by
    exact
      (continuous_projectedPsiKernel A w hmPos).abs.integrableOn_compact
        isCompact_Icc
  have hinside :
      (∫ y : ℝ in window, f y) ≤
        normalizedWindowSup w m *
          ∫ y : ℝ in window, |projectedPsiKernel A w m y| := by
    apply setIntegral_mono_on hfWindow
      (hkernelWindow.const_mul (normalizedWindowSup w m))
      hwindowMeasurable
    intro y hy
    have hvalue :
        |normalizedPsiError w y| ∈ normalizedWindowValues w m :=
      ⟨y, hy, rfl⟩
    have hsup :
        |normalizedPsiError w y| ≤ normalizedWindowSup w m :=
      le_csSup hbdd hvalue
    dsimp [f]
    calc
      normalizedPsiError w y * projectedPsiKernel A w m y ≤
          |normalizedPsiError w y *
            projectedPsiKernel A w m y| :=
        le_abs_self _
      _ = |normalizedPsiError w y| *
          |projectedPsiKernel A w m y| := abs_mul _ _
      _ ≤ normalizedWindowSup w m *
          |projectedPsiKernel A w m y| :=
        mul_le_mul_of_nonneg_right hsup (abs_nonneg _)
  have htail :
      (∫ y : ℝ in tail, f y) ≤
        projectedPsiTailRemainder A w m := by
    unfold projectedPsiTailRemainder
    change (∫ y : ℝ in tail, f y) ≤ ∫ y : ℝ in tail, |f y|
    exact integral_le_integral_abs
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
  rw [neg_re_localizedPsiGaussianAverage_div_pi_eq A hmPos hwRe]
  change
    (∫ y : ℝ in Set.Ioi 0, f y) ≤
      normalizedWindowSup w m *
          projectedPsiCoefficient A w m +
        projectedPsiTailRemainder A w m
  rw [← hdecompose]
  unfold projectedPsiCoefficient
  change
    (∫ y : ℝ in window, f y) +
        ∫ y : ℝ in tail, f y ≤
      normalizedWindowSup w m *
          (∫ y : ℝ in window, |projectedPsiKernel A w m y|) +
        projectedPsiTailRemainder A w m
  exact add_le_add hinside htail

/-- Every sufficiently late Gaussian window has a finite upper bound for
the normalized PNT error. This is a growth estimate, not continuity of
`chebyshevPsi`. -/
theorem eventually_bddAbove_normalizedWindowValues
    {u v : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    ∀ᶠ m : ℝ in atTop,
      BddAbove
        (normalizedWindowValues ((u : ℂ) + I * v) m) := by
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with m hm
  let w : ℂ := (u : ℂ) + I * v
  let C : ℝ :=
    ‖w‖ * (Real.log 4 + 5) *
      Real.exp ((1 - u) * (28 * m))
  refine ⟨C, ?_⟩
  rintro z ⟨y, hy, rfl⟩
  have hy0 : 0 ≤ y := by
    have := hy.1
    nlinarith
  have hyUpper : y ≤ 28 * m := hy.2
  have hxy : 1 ≤ Real.exp y := by
    simpa using Real.exp_le_exp.mpr hy0
  have hpsi :
      chebyshevPsi (Real.exp y) ≤
        (Real.log 4 + 4) * Real.exp y := by
    rw [chebyshevPsi_eq_mathlib]
    exact Chebyshev.psi_le_const_mul_self hxy
  have hpsiNonneg : 0 ≤ chebyshevPsi (Real.exp y) :=
    chebyshevPsi_nonneg _
  have herror :
      |chebyshevPsi (Real.exp y) - Real.exp y| ≤
        (Real.log 4 + 5) * Real.exp y := by
    rw [abs_sub_le_iff]
    constructor
    · nlinarith [Real.exp_pos y]
    · nlinarith [Real.exp_pos y, Real.log_pos (by norm_num : 1 < (4 : ℝ))]
  have hexpOrder :
      Real.exp ((1 - u) * y) ≤
        Real.exp ((1 - u) * (28 * m)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hyUpper (by linarith)
  have hwRe : w.re = u := by
    simp [w]
  unfold normalizedPsiError
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
      rw [← Real.exp_add]
      ring_nf
    _ ≤ C := by
      dsimp [C]
      gcongr

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
