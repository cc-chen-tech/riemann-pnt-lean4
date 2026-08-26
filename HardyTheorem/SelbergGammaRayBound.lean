import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Group.Integral

open Complex

namespace HardyTheorem

/-!
# A rotated-ray bound for the complex Gamma function

We work in logarithmic coordinates, where Euler's Gamma integrand becomes
the entire function `exp (s*z - exp z)`.  The finite rectangle identity and
its boundary estimates are the analytic core of the ray rotation.
-/

/-- Euler's Gamma integrand after the substitution `x = exp z`. -/
noncomputable def gammaLogKernel (s z : ℂ) : ℂ :=
  Complex.exp (s * z - Complex.exp z)

theorem differentiable_gammaLogKernel (s : ℂ) :
    Differentiable ℂ (gammaLogKernel s) := by
  unfold gammaLogKernel
  fun_prop

private theorem exp_mul_cpow_sub_one (s : ℂ) (x : ℝ) :
    (Real.exp x : ℂ) * (Real.exp x : ℂ) ^ (s - 1) =
      Complex.exp (s * x) := by
  rw [show (Real.exp x : ℂ) = Complex.exp (x : ℂ) by simp]
  conv_lhs =>
    lhs
    rw [← Complex.cpow_one (Complex.exp (x : ℂ))]
  rw [← Complex.cpow_add _ _ (Complex.exp_ne_zero _),
    Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos])
      (by simpa using Real.pi_nonneg)]
  congr 1
  ring

private theorem abs_exp_smul_gammaEulerIntegrand
    (s : ℂ) (x : ℝ) :
    |Real.exp x| •
        ((Real.exp (-Real.exp x) : ℂ) *
          (Real.exp x : ℂ) ^ (s - 1)) =
      gammaLogKernel s x := by
  rw [abs_of_pos (Real.exp_pos x)]
  change (Real.exp x : ℂ) *
      ((Real.exp (-Real.exp x) : ℂ) *
        (Real.exp x : ℂ) ^ (s - 1)) = _
  rw [mul_left_comm, exp_mul_cpow_sub_one]
  unfold gammaLogKernel
  rw [show (Real.exp (-Real.exp x) : ℂ) =
      Complex.exp (-(Complex.exp (x : ℂ))) by simp,
    ← Complex.exp_add]
  congr 1
  ring

/-- Euler convergence, transported by `y = exp x`, gives integrability of
the logarithmic Gamma kernel on the real axis. -/
theorem integrable_gammaLogKernel_real (s : ℂ) (hs : 0 < s.re) :
    MeasureTheory.Integrable (fun x : ℝ => gammaLogKernel s x) := by
  let g : ℝ → ℂ := fun y =>
    (Real.exp (-y) : ℂ) * (y : ℂ) ^ (s - 1)
  have hchange :=
    MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
      (s := Set.univ) (f := Real.exp) (f' := Real.exp)
      MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      Real.exp_injective.injOn g
  rw [Set.image_univ, Real.range_exp] at hchange
  have hg : MeasureTheory.IntegrableOn g (Set.Ioi 0) := by
    simpa [g, mul_comm] using
      (Complex.GammaIntegral_convergent (s := s) hs)
  have hweighted := hchange.mp hg
  rw [MeasureTheory.integrableOn_univ] at hweighted
  apply hweighted.congr
  filter_upwards with x
  exact (abs_exp_smul_gammaEulerIntegrand s x)

/-- The full real-axis logarithmic integral is Euler's Gamma integral. -/
theorem integral_gammaLogKernel_real_eq_Gamma (s : ℂ) (hs : 0 < s.re) :
    (∫ x : ℝ, gammaLogKernel s x) = Complex.Gamma s := by
  let g : ℝ → ℂ := fun y =>
    (Real.exp (-y) : ℂ) * (y : ℂ) ^ (s - 1)
  have hchange :=
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      (s := Set.univ) (f := Real.exp) (f' := Real.exp)
      MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      Real.exp_injective.injOn g
  rw [Set.image_univ, Real.range_exp] at hchange
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral]
  calc
    (∫ x : ℝ, gammaLogKernel s x) =
        ∫ x : ℝ, |Real.exp x| • g (Real.exp x) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      exact (abs_exp_smul_gammaEulerIntegrand s x).symm
    _ = ∫ y in Set.Ioi (0 : ℝ), g y := by
      simpa using hchange.symm
    _ = ∫ y in Set.Ioi (0 : ℝ),
        (Real.exp (-y) : ℂ) * (y : ℂ) ^ (s - 1) := rfl

/-- Exact modulus of the logarithmic Gamma kernel on a horizontal line. -/
theorem norm_gammaLogKernel (s : ℂ) (x y : ℝ) :
    ‖gammaLogKernel s ((x : ℂ) + y * I)‖ =
      Real.exp
        (s.re * x - s.im * y - Real.exp x * Real.cos y) := by
  unfold gammaLogKernel
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.exp_re, zero_mul, mul_zero,
    add_zero, zero_add, sub_zero]
  ring

/-- Cauchy's theorem on the finite logarithmic rectangle. -/
theorem integral_boundary_rect_gammaLogKernel
    (s : ℂ) (R eta : ℝ) :
    (∫ x : ℝ in -R..R, gammaLogKernel s x) -
        (∫ x : ℝ in -R..R, gammaLogKernel s (x + eta * I)) +
      I • (∫ y : ℝ in 0..eta, gammaLogKernel s (R + y * I)) -
      I • (∫ y : ℝ in 0..eta, gammaLogKernel s (-R + y * I)) = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (gammaLogKernel s) (-R : ℂ) ((R : ℂ) + eta * I)
    (differentiable_gammaLogKernel s).differentiableOn
  simpa using h

private theorem neg_im_mul_le_abs_im_mul_eta
    (s : ℂ) {eta y : ℝ}
    (hy : y ∈ Set.Icc 0 eta) :
    -s.im * y ≤ |s.im| * eta := by
  calc
    -s.im * y ≤ |s.im| * y :=
      mul_le_mul_of_nonneg_right (neg_le_abs s.im) hy.1
    _ ≤ |s.im| * eta :=
      mul_le_mul_of_nonneg_left hy.2 (abs_nonneg s.im)

/-- Uniform pointwise bound on the right vertical side of the logarithmic
rectangle. -/
theorem norm_gammaLogKernel_right_le
    (s : ℂ) {eta y : ℝ}
    (heta0 : 0 ≤ eta) (hetaPi : eta ≤ Real.pi / 2)
    (hy : y ∈ Set.Icc 0 eta) (R : ℝ) :
    ‖gammaLogKernel s ((R : ℂ) + y * I)‖ ≤
      Real.exp
        (s.re * R + |s.im| * eta - Real.exp R * Real.cos eta) := by
  rw [norm_gammaLogKernel]
  apply Real.exp_le_exp.mpr
  have him := neg_im_mul_le_abs_im_mul_eta s hy
  have hcos : Real.cos eta ≤ Real.cos y := by
    exact Real.cos_le_cos_of_nonneg_of_le_pi hy.1
      (by linarith [Real.pi_pos]) hy.2
  have hdecay := mul_le_mul_of_nonneg_left hcos (Real.exp_pos R).le
  linarith

/-- Uniform pointwise bound on the left vertical side. -/
theorem norm_gammaLogKernel_left_le
    (s : ℂ) {eta y : ℝ}
    (_heta0 : 0 ≤ eta) (hetaPi : eta ≤ Real.pi / 2)
    (hy : y ∈ Set.Icc 0 eta) (R : ℝ) :
    ‖gammaLogKernel s ((-R : ℂ) + y * I)‖ ≤
      Real.exp (-s.re * R + |s.im| * eta) := by
  rw [show (-R : ℂ) = ((-R : ℝ) : ℂ) by norm_num,
    norm_gammaLogKernel]
  apply Real.exp_le_exp.mpr
  have him := neg_im_mul_le_abs_im_mul_eta s hy
  have hcos : 0 ≤ Real.cos y :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      ((neg_nonpos.mpr (div_nonneg Real.pi_pos.le (by norm_num))).trans hy.1)
      (hy.2.trans hetaPi)
  have hdecay : 0 ≤ Real.exp (-R) * Real.cos y :=
    mul_nonneg (Real.exp_pos _).le hcos
  nlinarith

/-- The right vertical side is bounded by its uniform pointwise envelope times
its length. -/
theorem norm_integral_gammaLogKernel_right_le
    (s : ℂ) {eta : ℝ}
    (heta0 : 0 ≤ eta) (hetaPi : eta ≤ Real.pi / 2) (R : ℝ) :
    ‖∫ y : ℝ in 0..eta, gammaLogKernel s (R + y * I)‖ ≤
      Real.exp
          (s.re * R + |s.im| * eta - Real.exp R * Real.cos eta) * eta := by
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun y : ℝ => gammaLogKernel s (R + y * I))
    (a := 0) (b := eta)
    (C := Real.exp
      (s.re * R + |s.im| * eta - Real.exp R * Real.cos eta))
    (fun y hy => by
      rw [Set.uIoc_of_le heta0] at hy
      exact norm_gammaLogKernel_right_le s heta0 hetaPi
        ⟨hy.1.le, hy.2⟩ R)
  simpa [abs_of_nonneg heta0] using hbound

/-- The left vertical side is bounded by its uniform pointwise envelope times
its length. -/
theorem norm_integral_gammaLogKernel_left_le
    (s : ℂ) {eta : ℝ}
    (heta0 : 0 ≤ eta) (hetaPi : eta ≤ Real.pi / 2) (R : ℝ) :
    ‖∫ y : ℝ in 0..eta, gammaLogKernel s (-R + y * I)‖ ≤
      Real.exp (-s.re * R + |s.im| * eta) * eta := by
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun y : ℝ => gammaLogKernel s (-R + y * I))
    (a := 0) (b := eta)
    (C := Real.exp (-s.re * R + |s.im| * eta))
    (fun y hy => by
      rw [Set.uIoc_of_le heta0] at hy
      exact norm_gammaLogKernel_left_le s heta0 hetaPi
        ⟨hy.1.le, hy.2⟩ R)
  simpa [abs_of_nonneg heta0] using hbound

/-- If `re s > 0`, the left vertical side vanishes as the logarithmic
rectangle expands. -/
theorem tendsto_integral_gammaLogKernel_left_atTop
    (s : ℂ) {eta : ℝ}
    (heta0 : 0 ≤ eta) (hetaPi : eta ≤ Real.pi / 2)
    (hs : 0 < s.re) :
    Filter.Tendsto
      (fun R : ℝ =>
        ∫ y : ℝ in 0..eta, gammaLogKernel s (-R + y * I))
      Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun R =>
    norm_integral_gammaLogKernel_left_le s heta0 hetaPi R) ?_
  have hexponent :
    Filter.Tendsto (fun R : ℝ => -s.re * R + |s.im| * eta)
        Filter.atTop Filter.atBot :=
    Filter.tendsto_atBot_add_const_right Filter.atTop (|s.im| * eta)
      (Filter.tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hs))
  simpa using (Real.tendsto_exp_atBot.comp hexponent).mul_const eta

/-- Below the upper endpoint `pi / 2`, the right vertical side vanishes: the
factor `exp (-exp R * cos eta)` dominates every real exponential in `R`. -/
theorem tendsto_integral_gammaLogKernel_right_atTop
    (s : ℂ) {eta : ℝ}
    (heta0 : 0 ≤ eta) (hetaPi : eta < Real.pi / 2) :
    Filter.Tendsto
      (fun R : ℝ =>
        ∫ y : ℝ in 0..eta, gammaLogKernel s (R + y * I))
      Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun R =>
    norm_integral_gammaLogKernel_right_le s heta0 hetaPi.le R) ?_
  have hcos : 0 < Real.cos eta :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hetaPi⟩
  have hcore :
      Filter.Tendsto
        (fun R : ℝ =>
          (Real.exp R) ^ s.re *
            Real.exp (-Real.cos eta * Real.exp R))
        Filter.atTop (nhds 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      s.re (Real.cos eta) hcos).comp Real.tendsto_exp_atTop
  have hscaled := hcore.mul_const (Real.exp (|s.im| * eta) * eta)
  have hscaled0 :
      Filter.Tendsto
        (fun R : ℝ =>
          ((Real.exp R) ^ s.re *
            Real.exp (-Real.cos eta * Real.exp R)) *
              (Real.exp (|s.im| * eta) * eta))
        Filter.atTop (nhds 0) := by
    simpa using hscaled
  convert hscaled0 using 1
  funext R
  rw [← Real.exp_mul]
  rw [show s.re * R + |s.im| * eta - Real.exp R * Real.cos eta =
      (R * s.re + -Real.cos eta * Real.exp R) + |s.im| * eta by ring,
    Real.exp_add]
  rw [show R * s.re + -Real.cos eta * Real.exp R =
      R * s.re + -(Real.cos eta * Real.exp R) by ring,
    Real.exp_add]
  ring

/-- The two horizontal truncations in the logarithmic rectangle have the same
limit: their difference is exactly the sum of the two vanishing vertical
sides. -/
theorem tendsto_sub_integral_gammaLogKernel_horizontal_atTop
    (s : ℂ) {eta : ℝ}
    (heta0 : 0 ≤ eta) (hetaPi : eta < Real.pi / 2)
    (hs : 0 < s.re) :
    Filter.Tendsto
      (fun R : ℝ =>
        (∫ x : ℝ in -R..R, gammaLogKernel s x) -
          ∫ x : ℝ in -R..R, gammaLogKernel s (x + eta * I))
      Filter.atTop (nhds 0) := by
  have heq (R : ℝ) :
      (∫ x : ℝ in -R..R, gammaLogKernel s x) -
          (∫ x : ℝ in -R..R, gammaLogKernel s (x + eta * I)) =
        -(I • (∫ y : ℝ in 0..eta,
          gammaLogKernel s (R + y * I))) +
        I • (∫ y : ℝ in 0..eta,
          gammaLogKernel s (-R + y * I)) := by
    have hrect := integral_boundary_rect_gammaLogKernel s R eta
    rw [smul_eq_mul, smul_eq_mul]
    rw [smul_eq_mul, smul_eq_mul] at hrect
    linear_combination hrect
  have hright :=
    (tendsto_integral_gammaLogKernel_right_atTop s heta0 hetaPi).const_smul I
  have hleft :=
    (tendsto_integral_gammaLogKernel_left_atTop s heta0 hetaPi.le hs).const_smul I
  have hlim :
      Filter.Tendsto
        (fun R : ℝ =>
          -(I • (∫ y : ℝ in 0..eta,
            gammaLogKernel s (R + y * I))) +
          I • (∫ y : ℝ in 0..eta,
            gammaLogKernel s (-R + y * I)))
        Filter.atTop (nhds 0) := by
    simpa using hright.neg.add hleft
  exact hlim.congr fun R => (heq R).symm

/-- The real envelope `exp (sigma*x - c*exp x)` is integrable for positive
`sigma` and `c`.  Translation by `log c` reduces it to the real-axis Gamma
kernel. -/
theorem integrable_gammaLogEnvelope
    (sigma c : ℝ) (hsigma : 0 < sigma) (hc : 0 < c) :
    MeasureTheory.Integrable
      (fun x : ℝ => Real.exp (sigma * x - c * Real.exp x)) := by
  have hkernel := integrable_gammaLogKernel_real (sigma : ℂ) (by simpa using hsigma)
  have hbase : MeasureTheory.Integrable
      (fun x : ℝ => Real.exp (sigma * x - Real.exp x)) := by
    apply hkernel.norm.congr
    filter_upwards with x
    simpa using norm_gammaLogKernel (sigma : ℂ) x 0
  have htranslated := hbase.comp_add_right (Real.log c)
  have hscaled := htranslated.mul_const (Real.exp (-sigma * Real.log c))
  apply hscaled.congr
  filter_upwards with x
  rw [← Real.exp_add]
  congr 1
  rw [Real.exp_add, Real.exp_log hc]
  ring

private theorem gammaLogKernel_ofReal (sigma x : ℝ) :
    gammaLogKernel (sigma : ℂ) x =
      (Real.exp (sigma * x - Real.exp x) : ℂ) := by
  unfold gammaLogKernel
  rw [← Complex.ofReal_exp]
  congr 1
  simp

/-- Exact evaluation of the real envelope after scaling the Euler variable by
`c`. -/
theorem integral_gammaLogEnvelope_eq_real_Gamma
    (sigma c : ℝ) (hsigma : 0 < sigma) (hc : 0 < c) :
    (∫ x : ℝ, Real.exp (sigma * x - c * Real.exp x)) =
      c ^ (-sigma) * Real.Gamma sigma := by
  have hbaseComplex :
      (∫ x : ℝ, (Real.exp (sigma * x - Real.exp x) : ℂ)) =
        (Real.Gamma sigma : ℂ) := by
    calc
      (∫ x : ℝ, (Real.exp (sigma * x - Real.exp x) : ℂ)) =
          ∫ x : ℝ, gammaLogKernel (sigma : ℂ) x := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        exact (gammaLogKernel_ofReal sigma x).symm
      _ = Complex.Gamma (sigma : ℂ) :=
        integral_gammaLogKernel_real_eq_Gamma (sigma : ℂ) (by simpa using hsigma)
      _ = (Real.Gamma sigma : ℂ) := Complex.Gamma_ofReal sigma
  have hbase :
      (∫ x : ℝ, Real.exp (sigma * x - Real.exp x)) =
        Real.Gamma sigma := by
    norm_cast at hbaseComplex
  calc
    (∫ x : ℝ, Real.exp (sigma * x - c * Real.exp x)) =
        ∫ x : ℝ,
          Real.exp (sigma * (x + Real.log c) - Real.exp (x + Real.log c)) *
            Real.exp (-sigma * Real.log c) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      rw [← Real.exp_add]
      congr 1
      rw [Real.exp_add, Real.exp_log hc]
      ring
    _ = (∫ x : ℝ,
          Real.exp (sigma * (x + Real.log c) - Real.exp (x + Real.log c))) *
            Real.exp (-sigma * Real.log c) := by
      rw [MeasureTheory.integral_mul_const]
    _ = (∫ x : ℝ, Real.exp (sigma * x - Real.exp x)) *
          Real.exp (-sigma * Real.log c) := by
      have htranslate :
          (∫ x : ℝ,
            Real.exp (sigma * (x + Real.log c) - Real.exp (x + Real.log c))) =
          ∫ x : ℝ, Real.exp (sigma * x - Real.exp x) :=
        MeasureTheory.integral_add_right_eq_self
          (fun u : ℝ => Real.exp (sigma * u - Real.exp u)) (Real.log c)
      rw [htranslate]
    _ = c ^ (-sigma) * Real.Gamma sigma := by
      rw [hbase, Real.rpow_def_of_pos hc]
      ring

/-- Every horizontal logarithmic Gamma kernel below angle `pi / 2` is
integrable. -/
theorem integrable_gammaLogKernel_horizontal
    (s : ℂ) {eta : ℝ}
    (heta0 : 0 ≤ eta) (hetaPi : eta < Real.pi / 2)
    (hs : 0 < s.re) :
    MeasureTheory.Integrable
      (fun x : ℝ => gammaLogKernel s (x + eta * I)) := by
  have hcos : 0 < Real.cos eta :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hetaPi⟩
  have henv := integrable_gammaLogEnvelope s.re (Real.cos eta) hs hcos
  have hmajor := henv.mul_const (Real.exp (-s.im * eta))
  apply hmajor.mono'
  · exact ((differentiable_gammaLogKernel s).continuous.comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards with x
    rw [norm_gammaLogKernel, ← Real.exp_add]
    apply le_of_eq
    congr 1
    ring

/-- Cauchy's rectangle identity and the vanishing vertical sides identify the
two full horizontal integrals. -/
theorem integral_gammaLogKernel_eq_integral_shift
    (s : ℂ) {eta : ℝ}
    (heta0 : 0 ≤ eta) (hetaPi : eta < Real.pi / 2)
    (hs : 0 < s.re) :
    (∫ x : ℝ, gammaLogKernel s x) =
      ∫ x : ℝ, gammaLogKernel s (x + eta * I) := by
  have hbase := integrable_gammaLogKernel_real s hs
  have hshift := integrable_gammaLogKernel_horizontal s heta0 hetaPi hs
  have hbaseLim := MeasureTheory.intervalIntegral_tendsto_integral hbase
    Filter.tendsto_neg_atTop_atBot Filter.tendsto_id
  have hshiftLim := MeasureTheory.intervalIntegral_tendsto_integral hshift
    Filter.tendsto_neg_atTop_atBot Filter.tendsto_id
  have hsubLim := hbaseLim.sub hshiftLim
  have hzero :=
    tendsto_sub_integral_gammaLogKernel_horizontal_atTop
      s heta0 hetaPi hs
  exact sub_eq_zero.mp (tendsto_nhds_unique hsubLim hzero)

/-- The rotated horizontal logarithmic integral still equals `Gamma s`. -/
theorem integral_gammaLogKernel_shift_eq_Gamma
    (s : ℂ) {eta : ℝ}
    (heta0 : 0 ≤ eta) (hetaPi : eta < Real.pi / 2)
    (hs : 0 < s.re) :
    (∫ x : ℝ, gammaLogKernel s (x + eta * I)) =
      Complex.Gamma s := by
  rw [← integral_gammaLogKernel_eq_integral_shift s heta0 hetaPi hs]
  exact integral_gammaLogKernel_real_eq_Gamma s hs

private theorem norm_Gamma_le_real_Gamma_mul_cos_rpow_mul_exp_neg_im
    (s : ℂ) {eta : ℝ}
    (heta0 : 0 ≤ eta) (hetaPi : eta < Real.pi / 2)
    (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤
      Real.Gamma s.re * (Real.cos eta) ^ (-s.re) *
        Real.exp (-eta * s.im) := by
  rw [← integral_gammaLogKernel_shift_eq_Gamma s heta0 hetaPi hs]
  have hcos : 0 < Real.cos eta :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hetaPi⟩
  calc
    ‖∫ x : ℝ, gammaLogKernel s (x + eta * I)‖ ≤
        ∫ x : ℝ, ‖gammaLogKernel s (x + eta * I)‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ x : ℝ,
        Real.exp (-eta * s.im) *
          Real.exp (s.re * x - Real.cos eta * Real.exp x) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      rw [norm_gammaLogKernel, ← Real.exp_add]
      congr 1
      ring
    _ = Real.exp (-eta * s.im) *
        (∫ x : ℝ,
          Real.exp (s.re * x - Real.cos eta * Real.exp x)) := by
      rw [MeasureTheory.integral_const_mul]
    _ = Real.Gamma s.re * (Real.cos eta) ^ (-s.re) *
        Real.exp (-eta * s.im) := by
      rw [integral_gammaLogEnvelope_eq_real_Gamma
        s.re (Real.cos eta) hs hcos]
      ring

/-- Rotating in the direction of the sign of `im s` gives the symmetric
Gamma-ray bound with exponential decay in `|im s|`. -/
theorem norm_Gamma_le_real_Gamma_mul_cos_rpow_mul_exp_neg_abs_im
    (s : ℂ) {eta : ℝ}
    (heta0 : 0 ≤ eta) (hetaPi : eta < Real.pi / 2)
    (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤
      Real.Gamma s.re * (Real.cos eta) ^ (-s.re) *
        Real.exp (-eta * |s.im|) := by
  by_cases him : 0 ≤ s.im
  · simpa [abs_of_nonneg him] using
      norm_Gamma_le_real_Gamma_mul_cos_rpow_mul_exp_neg_im
        s heta0 hetaPi hs
  · have him' : s.im ≤ 0 := le_of_not_ge him
    have h := norm_Gamma_le_real_Gamma_mul_cos_rpow_mul_exp_neg_im
      (starRingEnd ℂ s) heta0 hetaPi (by simpa using hs)
    simpa [Complex.Gamma_conj, abs_of_nonpos him'] using h

end HardyTheorem
