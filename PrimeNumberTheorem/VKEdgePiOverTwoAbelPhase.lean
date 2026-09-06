import PrimeNumberTheorem.VKEdgePiOverTwoAbelDual
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

open Complex Filter MeasureTheory Set Topology

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- The logarithmically normalized real PNT error attached to a zeta point. -/
def normalizedPsiError (rho : ℂ) (y : ℝ) : ℝ :=
  ‖rho‖ * (chebyshevPsi (Real.exp y) - Real.exp y) *
    Real.exp (-rho.re * y)

/-- The phase which turns the residue at `rho` into a positive real number. -/
def zeroResiduePhase (rho : ℂ) : ℝ :=
  rho.arg + Real.pi

/-- A real Fourier character with an arbitrary phase. -/
def realPhaseCos (phase lambda y : ℝ) : ℝ :=
  Real.cos (phase - lambda * y)

/-- A real Fourier character with the residue-normalizing phase. -/
def phaseCos (rho : ℂ) (lambda y : ℝ) : ℝ :=
  realPhaseCos (zeroResiduePhase rho) lambda y

/-- The sign-preserving two-frequency certificate at a zeta ordinate. -/
def sharpenedPsiAbelKernel (rho : ℂ) (gamma : ℝ) (k : ℕ) (y : ℝ) : ℝ :=
  missingOddHarmonicKernel k
    (zeroResiduePhase rho - gamma * y)

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

/-- A power-scale PNT error bound gives absolute integrability of the
logarithmic-coordinate Laplace--Fourier integrand. -/
theorem integrableOn_logarithmicPsiError_exp_of_power_error
    {beta lambda a : ℝ}
    (herror : PsiPowerErrorBound beta) (ha : 0 < a) :
    IntegrableOn
      (fun y : ℝ =>
        ((chebyshevPsi (Real.exp y) - Real.exp y : ℝ) : ℂ) *
          Complex.exp
            (-(((beta + a : ℝ) : ℂ) + I * (lambda : ℂ)) * (y : ℂ)))
      (Set.Ioi 0) := by
  let s : ℂ := ((beta + a : ℝ) : ℂ) + I * (lambda : ℂ)
  let g : ℝ → ℂ := fun x =>
    ((chebyshevPsi x - x : ℝ) : ℂ) *
      (x : ℂ) ^ (-(s + 1))
  have hs : beta < s.re := by
    simp [s]
    linarith
  have hmell :=
    mellinConvergent_psiErrorAboveOneComplex_neg_of_power_error herror hs
  rw [MellinConvergent] at hmell
  have hmellTail :
      IntegrableOn
        (fun x : ℝ =>
          (x : ℂ) ^ ((-s) - 1) • psiErrorAboveOneComplex x)
        (Set.Ioi 1) :=
    hmell.mono_set (by
      intro x hx
      exact zero_lt_one.trans (Set.mem_Ioi.mp hx))
  have hg : IntegrableOn g (Set.Ioi 1) := by
    refine (integrableOn_congr_fun ?_ measurableSet_Ioi).mp hmellTail
    intro x hx
    have hx1 : 1 ≤ x := (Set.mem_Ioi.mp hx).le
    simp only [g, psiErrorAboveOneComplex, psiErrorAboveOne,
      Set.indicator_apply, Set.mem_Ici, hx1, if_true, smul_eq_mul]
    rw [show -s - 1 = -(s + 1) by ring]
    ring
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
    hchange.mp hg
  refine (integrableOn_congr_fun ?_ measurableSet_Ioi).mp htrans
  intro y _hy
  simp only [abs_of_pos (Real.exp_pos y), g, Complex.real_smul]
  calc
    (Real.exp y : ℂ) *
        (((chebyshevPsi (Real.exp y) - Real.exp y : ℝ) : ℂ) *
          (Real.exp y : ℂ) ^ (-(s + 1))) =
        ((chebyshevPsi (Real.exp y) - Real.exp y : ℝ) : ℂ) *
          ((Real.exp y : ℂ) *
            (Real.exp y : ℂ) ^ (-(s + 1))) := by ring
    _ = ((chebyshevPsi (Real.exp y) - Real.exp y : ℝ) : ℂ) *
        Complex.exp (-s * (y : ℂ)) := by
      rw [exp_mul_cpow_neg_add_one]
    _ = ((chebyshevPsi (Real.exp y) - Real.exp y : ℝ) : ℂ) *
        Complex.exp
          (-(((beta + a : ℝ) : ℂ) + I * (lambda : ℂ)) *
            (y : ℂ)) := by rfl

/-- The chosen phase makes the normalized residue at a nonzero point equal
to the positive multiplicity. -/
theorem exp_zeroResiduePhase_mul_residue
    {rho : ℂ} {m : ℕ} (hrho0 : rho ≠ 0) :
    Complex.exp (((zeroResiduePhase rho : ℝ) : ℂ) * I) *
        (-(m : ℂ) * (‖rho‖ : ℂ) / rho) =
      (m : ℂ) := by
  have hnorm0 : (‖rho‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hrho0)
  have hphase :
      Complex.exp (((zeroResiduePhase rho : ℝ) : ℂ) * I) =
        -rho / (‖rho‖ : ℂ) := by
    rw [zeroResiduePhase]
    rw [show
      (((rho.arg + Real.pi : ℝ) : ℂ) * I) =
        ((rho.arg : ℝ) : ℂ) * I + (Real.pi : ℂ) * I by
          push_cast
          ring]
    rw [Complex.exp_add, Complex.exp_pi_mul_I]
    have hpolar := Complex.norm_mul_exp_arg_mul_I rho
    rw [eq_div_iff hnorm0]
    calc
      (Complex.exp (((rho.arg : ℝ) : ℂ) * I) * (-1)) *
          (‖rho‖ : ℂ) =
          -((‖rho‖ : ℂ) *
            Complex.exp (((rho.arg : ℝ) : ℂ) * I)) := by ring
      _ = -rho := by rw [hpolar]
  rw [hphase]
  field_simp [hrho0, hnorm0]

private theorem phasedPsiIntegrand_re
    (rho : ℂ) (phase lambda a y : ℝ) :
    (Complex.exp (((phase : ℝ) : ℂ) * I) *
        (‖rho‖ : ℂ) *
        (((chebyshevPsi (Real.exp y) - Real.exp y : ℝ) : ℂ) *
          Complex.exp
            (-(((rho.re + a : ℝ) : ℂ) + I * (lambda : ℂ)) *
              (y : ℂ)))).re =
      Real.exp (-a * y) *
        (normalizedPsiError rho y *
          realPhaseCos phase lambda y) := by
  have hexp :
      Complex.exp
          (-(((rho.re + a : ℝ) : ℂ) + I * (lambda : ℂ)) *
            (y : ℂ)) =
        (Real.exp (-a * y) : ℂ) *
          (Real.exp (-rho.re * y) : ℂ) *
            Complex.exp (((-lambda * y : ℝ) : ℂ) * I) := by
    rw [show (Real.exp (-a * y) : ℂ) =
        Complex.exp ((-a * y : ℝ) : ℂ) by simp,
      show (Real.exp (-rho.re * y) : ℂ) =
        Complex.exp ((-rho.re * y : ℝ) : ℂ) by simp,
      ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    apply Complex.ext
    · simp
      ring
    · simp
  have hphaseExp :
      Complex.exp (((phase : ℝ) : ℂ) * I) *
          Complex.exp (((-lambda * y : ℝ) : ℂ) * I) =
        Complex.exp (((phase - lambda * y : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp]
  rw [show
      Complex.exp (((phase : ℝ) : ℂ) * I) *
          (‖rho‖ : ℂ) *
          (((chebyshevPsi (Real.exp y) - Real.exp y : ℝ) : ℂ) *
            ((Real.exp (-a * y) : ℂ) *
              (Real.exp (-rho.re * y) : ℂ) *
                Complex.exp (((-lambda * y : ℝ) : ℂ) * I))) =
        (((‖rho‖ *
          (chebyshevPsi (Real.exp y) - Real.exp y) *
          Real.exp (-a * y) * Real.exp (-rho.re * y) : ℝ) : ℂ) *
            Complex.exp (((phase - lambda * y : ℝ) : ℂ) * I)) by
      rw [← hphaseExp]
      push_cast
      ring]
  rw [Complex.exp_mul_I]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re,
    Complex.sin_ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero,
    zero_mul, sub_self]
  dsimp only [normalizedPsiError, realPhaseCos]
  ring

/-- The real phased integrand used by the dual certificate is integrable
whenever the power-scale PNT error bound supplies the complex Mellin
integrability. -/
theorem integrableOn_exp_mul_normalizedPsiError_mul_realPhaseCos
    {rho : ℂ} {phase lambda a : ℝ}
    (herror : PsiPowerErrorBound rho.re) (ha : 0 < a) :
    IntegrableOn
      (fun y =>
        Real.exp (-a * y) *
          (normalizedPsiError rho y *
            realPhaseCos phase lambda y))
      (Set.Ioi 0) := by
  let F : ℝ → ℂ := fun y =>
    Complex.exp (((phase : ℝ) : ℂ) * I) *
      (‖rho‖ : ℂ) *
      (((chebyshevPsi (Real.exp y) - Real.exp y : ℝ) : ℂ) *
        Complex.exp
          (-(((rho.re + a : ℝ) : ℂ) + I * (lambda : ℂ)) *
            (y : ℂ)))
  have hbase :=
    integrableOn_logarithmicPsiError_exp_of_power_error
      (beta := rho.re) (lambda := lambda) herror ha
  have hFint : IntegrableOn F (Set.Ioi 0) := by
    change Integrable (fun y : ℝ => F y) (volume.restrict (Set.Ioi 0))
    simpa only [F, mul_assoc] using
      (hbase.const_mul (‖rho‖ : ℂ)).const_mul
        (Complex.exp (((phase : ℝ) : ℂ) * I))
  refine (integrableOn_congr_fun ?_ measurableSet_Ioi).mp hFint.re
  intro y _hy
  exact phasedPsiIntegrand_re rho phase lambda a y

/-- Testing the normalized real PNT error against an arbitrarily phased
cosine is exactly the real part of the corresponding complex Abel
coefficient. -/
theorem realAbelMean_normalizedPsiError_mul_realPhaseCos
    {rho : ℂ} {phase lambda a : ℝ}
    (herror : PsiPowerErrorBound rho.re) (ha : 0 < a) :
    realAbelMean
        (fun y =>
          normalizedPsiError rho y *
            realPhaseCos phase lambda y) a =
      (Complex.exp (((phase : ℝ) : ℂ) * I) *
          ((‖rho‖ : ℂ) *
            psiAbelCoefficient rho.re lambda a)).re := by
  let u : ℂ :=
    Complex.exp (((phase : ℝ) : ℂ) * I)
  let G : ℝ → ℂ := fun y =>
    ((chebyshevPsi (Real.exp y) - Real.exp y : ℝ) : ℂ) *
      Complex.exp
        (-(((rho.re + a : ℝ) : ℂ) + I * (lambda : ℂ)) *
          (y : ℂ))
  let F : ℝ → ℂ := fun y =>
    u * (‖rho‖ : ℂ) * G y
  have hbase :=
    integrableOn_logarithmicPsiError_exp_of_power_error
      (beta := rho.re) (lambda := lambda) herror ha
  have hGint : IntegrableOn G (Set.Ioi 0) := by
    simpa only [G] using hbase
  have hFint : IntegrableOn F (Set.Ioi 0) := by
    change Integrable (fun y : ℝ => F y) (volume.restrict (Set.Ioi 0))
    simpa only [F, mul_assoc] using
      (hGint.const_mul (‖rho‖ : ℂ)).const_mul u
  rw [realAbelMean, psiAbelCoefficient]
  change
    a * ∫ y : ℝ in Set.Ioi 0,
      Real.exp (-a * y) *
        (normalizedPsiError rho y * realPhaseCos phase lambda y) =
      (u * ((‖rho‖ : ℂ) *
        ((a : ℂ) * ∫ y : ℝ in Set.Ioi 0, G y))).re
  have hFIntegral :
      (∫ y : ℝ in Set.Ioi 0, F y) =
        u * (‖rho‖ : ℂ) * ∫ y : ℝ in Set.Ioi 0, G y := by
    dsimp only [F]
    simpa only [mul_assoc] using
      (MeasureTheory.integral_const_mul
        (μ := volume.restrict (Set.Ioi 0))
        (u * (‖rho‖ : ℂ)) G)
  rw [show
      u * ((‖rho‖ : ℂ) *
        ((a : ℂ) * ∫ y : ℝ in Set.Ioi 0, G y)) =
        (a : ℂ) * ∫ y : ℝ in Set.Ioi 0, F y by
      rw [hFIntegral]
      ring]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [show
      (∫ y : ℝ in Set.Ioi 0, F y).re =
        ∫ y : ℝ in Set.Ioi 0, (F y).re by
      exact (integral_re hFint).symm]
  apply congrArg (fun z : ℝ => a * z)
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with y
  symm
  simpa only [F, G, u] using
    phasedPsiIntegrand_re rho phase lambda a y

/-- Residue-normalized specialization of the arbitrary-phase identity. -/
theorem realAbelMean_normalizedPsiError_mul_phaseCos
    {rho : ℂ} {lambda a : ℝ}
    (herror : PsiPowerErrorBound rho.re) (ha : 0 < a) :
    realAbelMean
        (fun y =>
          normalizedPsiError rho y * phaseCos rho lambda y) a =
      (Complex.exp (((zeroResiduePhase rho : ℝ) : ℂ) * I) *
          ((‖rho‖ : ℂ) *
            psiAbelCoefficient rho.re lambda a)).re := by
  simpa only [phaseCos] using
    (realAbelMean_normalizedPsiError_mul_realPhaseCos
      (rho := rho) (phase := zeroResiduePhase rho)
      (lambda := lambda) herror ha)

/-- At a positive-ordinate zeta zero, the residue-normalized real Abel
coefficient tends to the analytic multiplicity. -/
theorem tendsto_targetPhaseAbelMean_of_zeta_zero
    {rho : ℂ} {m : ℕ}
    (hrhoRe0 : 0 ≤ rho.re) (hrhoRe1 : rho.re < 1)
    (hrhoIm : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (horder : analyticOrderAt riemannZeta rho = m)
    (herror : PsiPowerErrorBound rho.re) :
    Tendsto
      (realAbelMean
        (fun y =>
          normalizedPsiError rho y *
            phaseCos rho rho.im y))
      (𝓝[>] 0) (𝓝 (m : ℝ)) := by
  have hrho0 : rho ≠ 0 := by
    intro hrho
    subst rho
    norm_num at hrhoIm
  have hcoeff :=
    tendsto_psiAbelCoefficient_of_zeta_zero
      hrhoRe0 hrhoRe1 hrhoIm hzero horder herror
  have hphase :
      Tendsto
        (fun a : ℝ =>
          Complex.exp (((zeroResiduePhase rho : ℝ) : ℂ) * I) *
            ((‖rho‖ : ℂ) *
              psiAbelCoefficient rho.re rho.im a))
        (𝓝[>] 0) (𝓝 (m : ℂ)) := by
    have hmul :
        Tendsto
          (fun a : ℝ =>
            Complex.exp (((zeroResiduePhase rho : ℝ) : ℂ) * I) *
              ((‖rho‖ : ℂ) *
                psiAbelCoefficient rho.re rho.im a))
          (𝓝[>] 0)
          (𝓝 (Complex.exp
            (((zeroResiduePhase rho : ℝ) : ℂ) * I) *
              (-(m : ℂ) * (‖rho‖ : ℂ) / rho))) :=
      tendsto_const_nhds.mul hcoeff
    rw [exp_zeroResiduePhase_mul_residue hrho0] at hmul
    exact hmul
  have hre :
      Tendsto
        (fun a : ℝ =>
          (Complex.exp (((zeroResiduePhase rho : ℝ) : ℂ) * I) *
            ((‖rho‖ : ℂ) *
              psiAbelCoefficient rho.re rho.im a)).re)
        (𝓝[>] 0) (𝓝 (m : ℝ)) := by
    simpa [Function.comp_def] using
      Complex.continuous_re.continuousAt.tendsto.comp hphase
  apply hre.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  symm
  exact
    realAbelMean_normalizedPsiError_mul_phaseCos herror ha

/-- At a nonzero point on the same vertical line, every phased real Abel
coefficient vanishes. -/
theorem tendsto_realPhaseAbelMean_of_zeta_ne_zero
    {rho : ℂ} {lambda phase : ℝ}
    (hrhoRe0 : 0 ≤ rho.re) (hrhoRe1 : rho.re < 1)
    (hlambda : 0 < lambda)
    (hzeta : riemannZeta ((rho.re : ℂ) + I * lambda) ≠ 0)
    (herror : PsiPowerErrorBound rho.re) :
    Tendsto
      (realAbelMean
        (fun y =>
          normalizedPsiError rho y *
            realPhaseCos phase lambda y))
      (𝓝[>] 0) (𝓝 0) := by
  have hcoeff :=
    tendsto_psiAbelCoefficient_of_zeta_ne_zero
      hrhoRe0 hrhoRe1 hlambda hzeta herror
  have hphase :
      Tendsto
        (fun a : ℝ =>
          Complex.exp (((phase : ℝ) : ℂ) * I) *
            ((‖rho‖ : ℂ) *
              psiAbelCoefficient rho.re lambda a))
        (𝓝[>] 0) (𝓝 0) := by
    simpa using
      tendsto_const_nhds.mul (tendsto_const_nhds.mul hcoeff)
  have hre :
      Tendsto
        (fun a : ℝ =>
          (Complex.exp (((phase : ℝ) : ℂ) * I) *
            ((‖rho‖ : ℂ) *
              psiAbelCoefficient rho.re lambda a)).re)
        (𝓝[>] 0) (𝓝 0) := by
    simpa [Function.comp_def, Complex.zero_re] using
      Complex.continuous_re.continuousAt.tendsto.comp hphase
  apply hre.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  symm
  exact
    realAbelMean_normalizedPsiError_mul_realPhaseCos herror ha

/-- The zeta-specific kernel is the target phase minus its normalized odd
harmonic. -/
theorem sharpenedPsiAbelKernel_eq_two_phases
    (rho : ℂ) (gamma : ℝ) (k : ℕ) (y : ℝ) :
    sharpenedPsiAbelKernel rho gamma k y =
      phaseCos rho gamma y -
        ((-1 : ℝ) ^ k) *
          (1 / (2 * ((2 * k + 1 : ℕ) : ℝ))) *
            realPhaseCos
              (((2 * k + 1 : ℕ) : ℝ) * zeroResiduePhase rho)
              (((2 * k + 1 : ℕ) : ℝ) * gamma) y := by
  simp only [sharpenedPsiAbelKernel, missingOddHarmonicKernel,
    phaseCos, realPhaseCos]
  congr 1
  ring_nf

private theorem missingOddHarmonicKernel_periodic (k : ℕ) :
    Function.Periodic (missingOddHarmonicKernel k) (2 * Real.pi) := by
  intro theta
  simp only [missingOddHarmonicKernel]
  rw [Real.cos_add_two_pi]
  rw [show
      (((2 * k + 1 : ℕ) : ℝ) * (theta + 2 * Real.pi)) =
        ((2 * k + 1 : ℕ) : ℝ) * theta +
          (2 * k + 1 : ℕ) * (2 * Real.pi) by
      push_cast
      ring]
  rw [Real.cos_add_nat_mul_two_pi]

/-- The Abel `L¹` mean of the residue-phased certificate is its exact
strictly improved periodic denominator. -/
theorem tendsto_abs_sharpenedPsiAbelKernel
    {rho : ℂ} {gamma : ℝ} {k : ℕ} (hgamma : 0 < gamma) :
    Tendsto
      (realAbelMean
        (fun y => |sharpenedPsiAbelKernel rho gamma k y|))
      (𝓝[>] 0)
      (𝓝 (sharpenedMissingHarmonicDenominator k)) := by
  let T : ℝ := 2 * Real.pi / gamma
  let f : ℝ → ℝ := fun theta => |missingOddHarmonicKernel k theta|
  let q : ℝ → ℝ := fun y =>
    f (zeroResiduePhase rho - gamma * y)
  have hT : 0 < T := by
    dsimp only [T]
    positivity
  have hfper : Function.Periodic f (2 * Real.pi) := by
    simpa only [f, Function.comp_def] using
      (missingOddHarmonicKernel_periodic k).comp
        (fun x : ℝ => |x|)
  have hfcont : Continuous f := by
    dsimp only [f]
    apply Continuous.abs
    unfold missingOddHarmonicKernel
    fun_prop
  have hqper : Function.Periodic q T := by
    intro y
    dsimp only [q, T]
    have htheta :
        zeroResiduePhase rho -
            gamma * (y + 2 * Real.pi / gamma) =
          (zeroResiduePhase rho - gamma * y) - 2 * Real.pi := by
      field_simp [hgamma.ne']
      ring
    rw [htheta]
    exact hfper.sub_eq _
  have hqcont : Continuous q := by
    dsimp only [q]
    fun_prop
  have hshift :
      (∫ theta in
          zeroResiduePhase rho - 2 * Real.pi..
            zeroResiduePhase rho, f theta) =
        ∫ theta in (0 : ℝ)..2 * Real.pi, f theta := by
    convert hfper.intervalIntegral_add_eq
      (zeroResiduePhase rho - 2 * Real.pi) 0 using 1 <;> ring
  have hbase :
      (∫ theta in (0 : ℝ)..2 * Real.pi, f theta) =
        4 - 2 / (((2 * k + 1 : ℕ) : ℝ) ^ 2) := by
    simpa only [f] using integral_abs_missingOddHarmonicKernel k
  have hsubst :=
    intervalIntegral.integral_comp_add_mul
      (f := f) (a := (0 : ℝ)) (b := T)
      (c := -gamma) (d := zeroResiduePhase rho)
      (neg_ne_zero.mpr hgamma.ne')
  have hend :
      zeroResiduePhase rho + -gamma * T =
        zeroResiduePhase rho - 2 * Real.pi := by
    dsimp only [T]
    field_simp [hgamma.ne']
    ring
  have hqIntegral :
      (∫ y in (0 : ℝ)..T, q y) =
        gamma⁻¹ *
          (4 - 2 / (((2 * k + 1 : ℕ) : ℝ) ^ 2)) := by
    dsimp only [q]
    rw [show
        (fun y : ℝ =>
          f (zeroResiduePhase rho - gamma * y)) =
        (fun y : ℝ =>
          f (zeroResiduePhase rho + -gamma * y)) by
        funext y
        ring]
    rw [hsubst]
    simp only [mul_zero, add_zero, smul_eq_mul]
    rw [hend, intervalIntegral.integral_symm, hshift, hbase]
    rw [inv_neg]
    ring
  have haverage :
      (1 / T) * ∫ y in (0 : ℝ)..T, q y =
        sharpenedMissingHarmonicDenominator k := by
    rw [hqIntegral]
    dsimp only [T, sharpenedMissingHarmonicDenominator]
    have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp [hgamma.ne', hpi0]
    ring
  have hlimit :=
    tendsto_realAbelMean_of_continuous_periodic hT hqper hqcont
  rw [haverage] at hlimit
  simpa only [q, f, sharpenedPsiAbelKernel] using hlimit

/-- If the selected odd harmonic is not a zeta zero, the full
sign-preserving two-frequency test of the actual PNT error retains exactly
the target zero's multiplicity in the Abel limit. -/
theorem tendsto_sharpenedPsiAbelMean_of_missing
    {rho : ℂ} {m : ℕ} {k : ℕ}
    (hrhoRe0 : 0 ≤ rho.re) (hrhoRe1 : rho.re < 1)
    (hrhoIm : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (horder : analyticOrderAt riemannZeta rho = m)
    (hmissing :
      riemannZeta
        (oddHarmonicPoint rho.re rho.im k) ≠ 0)
    (herror : PsiPowerErrorBound rho.re) :
    Tendsto
      (realAbelMean
        (fun y =>
          normalizedPsiError rho y *
            sharpenedPsiAbelKernel rho rho.im k y))
      (𝓝[>] 0) (𝓝 (m : ℝ)) := by
  let n : ℕ := 2 * k + 1
  let c : ℝ := ((-1 : ℝ) ^ k) *
    (1 / (2 * (n : ℝ)))
  have hnPos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  have htarget :=
    tendsto_targetPhaseAbelMean_of_zeta_zero
      hrhoRe0 hrhoRe1 hrhoIm hzero horder herror
  have hmissingPoint :
      riemannZeta
        ((rho.re : ℂ) + I * (((n : ℝ) * rho.im : ℝ) : ℂ)) ≠ 0 := by
    simpa only [oddHarmonicPoint, n] using hmissing
  have hmissingLimit :=
    tendsto_realPhaseAbelMean_of_zeta_ne_zero
      (rho := rho)
      (lambda := (n : ℝ) * rho.im)
      (phase := (n : ℝ) * zeroResiduePhase rho)
      hrhoRe0 hrhoRe1
      (mul_pos hnPos hrhoIm)
      hmissingPoint herror
  have hlinear :
      ∀ a : ℝ, 0 < a →
        realAbelMean
            (fun y =>
              normalizedPsiError rho y *
                sharpenedPsiAbelKernel rho rho.im k y) a =
          realAbelMean
              (fun y =>
                normalizedPsiError rho y *
                  phaseCos rho rho.im y) a -
            c * realAbelMean
              (fun y =>
                normalizedPsiError rho y *
                  realPhaseCos
                    ((n : ℝ) * zeroResiduePhase rho)
                    ((n : ℝ) * rho.im) y) a := by
    intro a ha
    have hintTarget :=
      integrableOn_exp_mul_normalizedPsiError_mul_realPhaseCos
        (rho := rho) (phase := zeroResiduePhase rho)
        (lambda := rho.im) herror ha
    have hintMissing :=
      integrableOn_exp_mul_normalizedPsiError_mul_realPhaseCos
        (rho := rho)
        (phase := (n : ℝ) * zeroResiduePhase rho)
        (lambda := (n : ℝ) * rho.im) herror ha
    rw [realAbelMean, realAbelMean, realAbelMean]
    have hintegrand :
        (fun y : ℝ =>
          Real.exp (-a * y) *
            (normalizedPsiError rho y *
              sharpenedPsiAbelKernel rho rho.im k y)) =
          fun y : ℝ =>
            Real.exp (-a * y) *
                (normalizedPsiError rho y *
                  phaseCos rho rho.im y) -
              c * (Real.exp (-a * y) *
                (normalizedPsiError rho y *
                  realPhaseCos
                    ((n : ℝ) * zeroResiduePhase rho)
                    ((n : ℝ) * rho.im) y)) := by
      funext y
      rw [sharpenedPsiAbelKernel_eq_two_phases]
      dsimp only [n, c]
      ring
    rw [hintegrand]
    simp only [phaseCos]
    rw [MeasureTheory.integral_sub hintTarget
      (hintMissing.const_mul c)]
    rw [MeasureTheory.integral_const_mul]
    ring
  have hcMissing :
      Tendsto
        (fun a : ℝ =>
          c * realAbelMean
            (fun y =>
              normalizedPsiError rho y *
                realPhaseCos
                  ((n : ℝ) * zeroResiduePhase rho)
                  ((n : ℝ) * rho.im) y) a)
        (𝓝[>] 0) (𝓝 0) := by
    simpa using
      (show Tendsto (fun _ : ℝ => c) (𝓝[>] 0) (𝓝 c) from
        tendsto_const_nhds).mul hmissingLimit
  have hcombined := htarget.sub hcMissing
  have hcombined' :
      Tendsto
        (fun a : ℝ =>
          realAbelMean
              (fun y =>
                normalizedPsiError rho y *
                  phaseCos rho rho.im y) a -
            c * realAbelMean
              (fun y =>
                normalizedPsiError rho y *
                  realPhaseCos
                    ((n : ℝ) * zeroResiduePhase rho)
                    ((n : ℝ) * rho.im) y) a)
        (𝓝[>] 0) (𝓝 (m : ℝ)) := by
    simpa only [sub_zero] using hcombined
  apply hcombined'.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  simpa only [mul_zero, sub_zero] using (hlinear a ha).symm

/-- The exponentially weighted product of the normalized PNT error and the
two-frequency certificate is integrable. -/
theorem integrableOn_exp_mul_normalizedPsiError_mul_sharpenedKernel
    {rho : ℂ} {k : ℕ} {a : ℝ}
    (herror : PsiPowerErrorBound rho.re) (ha : 0 < a) :
    IntegrableOn
      (fun y =>
        Real.exp (-a * y) *
          (normalizedPsiError rho y *
            sharpenedPsiAbelKernel rho rho.im k y))
      (Set.Ioi 0) := by
  let n : ℕ := 2 * k + 1
  let c : ℝ := ((-1 : ℝ) ^ k) *
    (1 / (2 * (n : ℝ)))
  have hintTarget :=
    integrableOn_exp_mul_normalizedPsiError_mul_realPhaseCos
      (rho := rho) (phase := zeroResiduePhase rho)
      (lambda := rho.im) herror ha
  have hintMissing :=
    integrableOn_exp_mul_normalizedPsiError_mul_realPhaseCos
      (rho := rho)
      (phase := (n : ℝ) * zeroResiduePhase rho)
      (lambda := (n : ℝ) * rho.im) herror ha
  have hsum :=
    hintTarget.sub (hintMissing.const_mul c)
  refine (integrableOn_congr_fun ?_ measurableSet_Ioi).mpr hsum
  intro y _hy
  change
    Real.exp (-a * y) *
        (normalizedPsiError rho y *
          sharpenedPsiAbelKernel rho rho.im k y) =
      Real.exp (-a * y) *
          (normalizedPsiError rho y *
            realPhaseCos (zeroResiduePhase rho) rho.im y) -
        c * (Real.exp (-a * y) *
          (normalizedPsiError rho y *
            realPhaseCos
              ((n : ℝ) * zeroResiduePhase rho)
              ((n : ℝ) * rho.im) y))
  rw [sharpenedPsiAbelKernel_eq_two_phases]
  dsimp only [n, c, phaseCos]
  ring

theorem abs_sharpenedPsiAbelKernel_le_two
    (rho : ℂ) (gamma : ℝ) (k : ℕ) (y : ℝ) :
    |sharpenedPsiAbelKernel rho gamma k y| ≤ 2 := by
  let n : ℕ := 2 * k + 1
  have hn : (1 : ℝ) ≤ n := by
    exact_mod_cast (show 1 ≤ n by omega)
  have hcoeff :
      |((-1 : ℝ) ^ k) * (1 / (2 * (n : ℝ)))| ≤ 1 := by
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      one_mul, abs_of_nonneg (by positivity)]
    rw [div_le_one (by positivity)]
    nlinarith
  unfold sharpenedPsiAbelKernel missingOddHarmonicKernel
  calc
    |Real.cos (zeroResiduePhase rho - gamma * y) -
        ((-1 : ℝ) ^ k) *
          (1 / (2 * (((2 * k + 1 : ℕ) : ℝ)))) *
            Real.cos
              ((((2 * k + 1 : ℕ) : ℝ) *
                (zeroResiduePhase rho - gamma * y)))| ≤
        |Real.cos (zeroResiduePhase rho - gamma * y)| +
          |((-1 : ℝ) ^ k) *
            (1 / (2 * (((2 * k + 1 : ℕ) : ℝ)))) *
              Real.cos
                ((((2 * k + 1 : ℕ) : ℝ) *
                  (zeroResiduePhase rho - gamma * y)))| :=
      abs_sub _ _
    _ ≤ 1 + 1 := by
      gcongr
      · exact Real.abs_cos_le_one _
      · rw [abs_mul]
        exact mul_le_one₀
          (by simpa only [n] using hcoeff)
          (abs_nonneg _)
          (Real.abs_cos_le_one _)
    _ = 2 := by norm_num

/-- The absolute certificate is integrable against every positive
exponential weight. -/
theorem integrableOn_exp_mul_abs_sharpenedPsiAbelKernel
    {rho : ℂ} {gamma : ℝ} {k : ℕ} {a : ℝ} (ha : 0 < a) :
    IntegrableOn
      (fun y =>
        Real.exp (-a * y) *
          |sharpenedPsiAbelKernel rho gamma k y|)
      (Set.Ioi 0) := by
  have hexp :
      IntegrableOn (fun y : ℝ => Real.exp (-a * y)) (Set.Ioi 0) := by
    simpa only [neg_mul] using
      integrableOn_exp_mul_Ioi (a := -a) (neg_neg_of_pos ha) 0
  have hcont :
      Continuous
        (fun y : ℝ =>
          Real.exp (-a * y) *
            |sharpenedPsiAbelKernel rho gamma k y|) := by
    unfold sharpenedPsiAbelKernel missingOddHarmonicKernel
    fun_prop
  apply (hexp.const_mul 2).mono'
  · exact hcont.aestronglyMeasurable
  · filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _), abs_abs]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left
        (abs_sharpenedPsiAbelKernel_le_two rho gamma k y)
        (Real.exp_pos _).le

/-- Every eventual bound for the normalized PNT error is at least the
strictly improved missing-harmonic lower bound, multiplied by the target
zero's analytic multiplicity. -/
theorem mul_sharpenedMissingHarmonicLowerBound_le_of_tail_bound
    {rho : ℂ} {m k : ℕ} {K Y : ℝ}
    (hrhoRe0 : 0 ≤ rho.re) (hrhoRe1 : rho.re < 1)
    (hrhoIm : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (horder : analyticOrderAt riemannZeta rho = m)
    (hmissing :
      riemannZeta
        (oddHarmonicPoint rho.re rho.im k) ≠ 0)
    (herror : PsiPowerErrorBound rho.re)
    (hK : 0 ≤ K) (hY : 0 ≤ Y)
    (hbound :
      ∀ y ∈ Set.Ioi Y, |normalizedPsiError rho y| ≤ K) :
    (m : ℝ) * sharpenedMissingHarmonicLowerBound k ≤ K := by
  let q : ℝ → ℝ := sharpenedPsiAbelKernel rho rho.im k
  have hint :
      ∀ a : ℝ, 0 < a →
        IntegrableOn
          (fun y =>
            Real.exp (-a * y) *
              (normalizedPsiError rho y * q y))
          (Set.Ioi 0) := by
    intro a ha
    simpa only [q] using
      integrableOn_exp_mul_normalizedPsiError_mul_sharpenedKernel
        (rho := rho) (k := k) herror ha
  have hprefix :
      IntegrableOn
        (fun y => normalizedPsiError rho y * q y)
        (Set.Ioc 0 Y) := by
    have hweighted :
        IntegrableOn
          (fun y =>
            Real.exp (-(1 : ℝ) * y) *
              (normalizedPsiError rho y * q y))
          (Set.Ioc 0 Y) :=
      (hint 1 zero_lt_one).mono_set
        (show Set.Ioc (0 : ℝ) Y ⊆ Set.Ioi 0 from
          Set.Ioc_subset_Ioi_self)
    have hmul :=
      hweighted.mul_continuousOn_of_subset
        Real.continuous_exp.continuousOn
        measurableSet_Ioc isCompact_Icc Set.Ioc_subset_Icc_self
    refine (integrableOn_congr_fun ?_ measurableSet_Ioc).mp hmul
    intro y _hy
    dsimp only
    calc
      Real.exp (-(1 : ℝ) * y) *
          (normalizedPsiError rho y * q y) * Real.exp y =
          (Real.exp (-(1 : ℝ) * y) * Real.exp y) *
            (normalizedPsiError rho y * q y) := by ring
      _ = normalizedPsiError rho y * q y := by
        rw [← Real.exp_add]
        ring_nf
        simp
  have hqint :
      ∀ a : ℝ, 0 < a →
        IntegrableOn
          (fun y => Real.exp (-a * y) * |q y|)
          (Set.Ioi 0) := by
    intro a ha
    simpa only [q] using
      integrableOn_exp_mul_abs_sharpenedPsiAbelKernel
        (rho := rho) (gamma := rho.im) (k := k) ha
  have hlim :=
    tendsto_sharpenedPsiAbelMean_of_missing
      hrhoRe0 hrhoRe1 hrhoIm hzero horder hmissing herror
  have hqlim :=
    tendsto_abs_sharpenedPsiAbelKernel
      (rho := rho) (gamma := rho.im) (k := k) hrhoIm
  have hineq :
      |(m : ℝ)| ≤
        K * sharpenedMissingHarmonicDenominator k :=
    abs_limit_realAbelMean_mul_le_of_tail_bound
      hK hY
      (by simpa only [q] using hbound)
      hprefix hint hqint
      (by simpa only [q] using hlim)
      (by simpa only [q] using hqlim)
  have hm0 : (0 : ℝ) ≤ m := by positivity
  rw [abs_of_nonneg hm0] at hineq
  have hdenPos := sharpenedMissingHarmonicDenominator_pos k
  simpa only [sharpenedMissingHarmonicLowerBound,
    div_eq_mul_inv, one_mul] using
      (div_le_iff₀ hdenPos).2 hineq

/-- A tail bound for the logarithmically normalized error is itself enough
to produce the power-scale PNT error bound needed by the Mellin boundary
argument. -/
theorem psiPowerErrorBound_of_normalizedPsiError_tail_bound
    {rho : ℂ} {K Y : ℝ} (hrho0 : rho ≠ 0)
    (hbound :
      ∀ y ∈ Set.Ioi Y, |normalizedPsiError rho y| ≤ K) :
    PsiPowerErrorBound rho.re := by
  have hnormPos : (0 : ℝ) < ‖rho‖ := norm_pos_iff.mpr hrho0
  have hK : 0 ≤ K := by
    have hsample := hbound (Y + 1) (by simp)
    exact (abs_nonneg _).trans hsample
  apply psiPowerErrorBound_of_pointwise
    (C := K / ‖rho‖)
    (X := max 1 (Real.exp (Y + 1)))
  intro x hx
  have hx1 : 1 ≤ x := (le_max_left 1 (Real.exp (Y + 1))).trans hx
  have hxPos : 0 < x := zero_lt_one.trans_le hx1
  have hExpY : Real.exp (Y + 1) ≤ x :=
    (le_max_right 1 (Real.exp (Y + 1))).trans hx
  have hy : Y < Real.log x := by
    have : Y + 1 ≤ Real.log x :=
      (Real.le_log_iff_exp_le hxPos).2 hExpY
    linarith
  have hb := hbound (Real.log x) hy
  rw [normalizedPsiError, Real.exp_log hxPos] at hb
  rw [abs_mul, abs_mul, abs_of_nonneg (norm_nonneg rho),
    abs_of_pos (Real.exp_pos _)] at hb
  have hpowPos : 0 < x ^ rho.re :=
    Real.rpow_pos_of_pos hxPos _
  have hscale :
      Real.exp (-rho.re * Real.log x) =
        (x ^ rho.re)⁻¹ := by
    calc
      Real.exp (-rho.re * Real.log x) =
          Real.exp (-(Real.log x * rho.re)) := by
        congr 1
        ring
      _ = (Real.exp (Real.log x * rho.re))⁻¹ :=
        Real.exp_neg _
      _ = (x ^ rho.re)⁻¹ := by
        rw [Real.rpow_def_of_pos hxPos]
  rw [hscale] at hb
  have hmul :
      ‖rho‖ * |chebyshevPsi x - x| ≤
        K * x ^ rho.re := by
    calc
      ‖rho‖ * |chebyshevPsi x - x| =
          (‖rho‖ * |chebyshevPsi x - x| *
            (x ^ rho.re)⁻¹) * (x ^ rho.re) := by
        field_simp [hpowPos.ne']
      _ ≤ K * x ^ rho.re :=
        mul_le_mul_of_nonneg_right hb hpowPos.le
  calc
    |chebyshevPsi x - x| ≤
        (K * x ^ rho.re) / ‖rho‖ :=
      (le_div_iff₀ hnormPos).2 (by simpa [mul_comm] using hmul)
    _ = (K / ‖rho‖) * x ^ rho.re := by ring

/-- A strict constant halfway between `pi/2` and the exact
missing-harmonic lower bound. -/
def strictPiOverTwoOscillationConstant (k : ℕ) : ℝ :=
  (Real.pi / 2 + sharpenedMissingHarmonicLowerBound k) / 2

theorem pi_div_two_lt_strictPiOverTwoOscillationConstant (k : ℕ) :
    Real.pi / 2 < strictPiOverTwoOscillationConstant k := by
  have hgap := pi_div_two_lt_sharpenedMissingHarmonicLowerBound k
  unfold strictPiOverTwoOscillationConstant
  linarith

theorem strictPiOverTwoOscillationConstant_lt_lowerBound (k : ℕ) :
    strictPiOverTwoOscillationConstant k <
      sharpenedMissingHarmonicLowerBound k := by
  have hgap := pi_div_two_lt_sharpenedMissingHarmonicLowerBound k
  unfold strictPiOverTwoOscillationConstant
  linarith

/-- Carlson supplies a missing odd harmonic, and the actual PNT error then
exceeds a fixed constant strictly larger than `pi/2` at arbitrarily large
logarithmic scales.  Multiplicity only strengthens the lower bound. -/
theorem exists_far_normalizedPsiError_gt_pi_div_two_of_zeta_zero
    {rho : ℂ} {m : ℕ} {sigma : ℝ}
    (hrhoRe1 : rho.re < 1) (hrhoIm : 0 < rho.im)
    (hsigmaHalf : 1 / 2 < sigma)
    (hsigmaRho : sigma < rho.re)
    (hzero : riemannZeta rho = 0)
    (horder : analyticOrderAt riemannZeta rho = m)
    (hm : 1 ≤ m) :
    ∃ k : ℕ,
      riemannZeta
          (oddHarmonicPoint rho.re rho.im k) ≠ 0 ∧
      Real.pi / 2 < strictPiOverTwoOscillationConstant k ∧
      ∀ Y : ℝ, 0 ≤ Y →
        ∃ y : ℝ, Y ≤ y ∧
          (m : ℝ) * strictPiOverTwoOscillationConstant k <
            |normalizedPsiError rho y| := by
  have hrhoRe0 : 0 ≤ rho.re := by
    linarith
  have hrho0 : rho ≠ 0 := by
    intro hrho
    subst rho
    norm_num at hrhoIm
  rcases
      exists_missing_oddHarmonic_with_strict_gap_of_carlson
        hrhoRe1 hrhoIm hsigmaHalf hsigmaRho with
    ⟨k, hmissing, _hOldGap⟩
  refine ⟨k, hmissing,
    pi_div_two_lt_strictPiOverTwoOscillationConstant k, ?_⟩
  intro Y hY
  by_contra hExists
  push_neg at hExists
  let K : ℝ :=
    (m : ℝ) * strictPiOverTwoOscillationConstant k
  have hmPos : (0 : ℝ) < m := by exact_mod_cast hm
  have hconstantPos :
      0 < strictPiOverTwoOscillationConstant k :=
    Real.pi_div_two_pos.trans
      (pi_div_two_lt_strictPiOverTwoOscillationConstant k)
  have hK : 0 ≤ K := (mul_pos hmPos hconstantPos).le
  have htail :
      ∀ y ∈ Set.Ioi Y, |normalizedPsiError rho y| ≤ K := by
    intro y hy
    exact hExists y hy.le
  have herror :
      PsiPowerErrorBound rho.re :=
    psiPowerErrorBound_of_normalizedPsiError_tail_bound
      hrho0 htail
  have hlower :
      (m : ℝ) * sharpenedMissingHarmonicLowerBound k ≤ K :=
    mul_sharpenedMissingHarmonicLowerBound_le_of_tail_bound
      hrhoRe0 hrhoRe1 hrhoIm hzero horder hmissing herror
      hK hY htail
  have hstrict :
      K < (m : ℝ) * sharpenedMissingHarmonicLowerBound k := by
    dsimp only [K]
    exact mul_lt_mul_of_pos_left
      (strictPiOverTwoOscillationConstant_lt_lowerBound k)
      hmPos
  exact (not_lt_of_ge hlower) hstrict

/-- The logarithmic-scale theorem rewritten directly as a PNT error
oscillation statement.  The coefficient multiplying `x ^ rho.re / ‖rho‖`
is strictly larger than `pi / 2`. -/
theorem exists_far_psiError_gt_pi_div_two_of_zeta_zero
    {rho : ℂ} {m : ℕ} {sigma : ℝ}
    (hrhoRe1 : rho.re < 1) (hrhoIm : 0 < rho.im)
    (hsigmaHalf : 1 / 2 < sigma)
    (hsigmaRho : sigma < rho.re)
    (hzero : riemannZeta rho = 0)
    (horder : analyticOrderAt riemannZeta rho = m)
    (hm : 1 ≤ m) :
    ∃ k : ℕ,
      riemannZeta
          (oddHarmonicPoint rho.re rho.im k) ≠ 0 ∧
      Real.pi / 2 < strictPiOverTwoOscillationConstant k ∧
      ∀ X : ℝ, 1 ≤ X →
        ∃ x : ℝ, X ≤ x ∧
          (m : ℝ) * strictPiOverTwoOscillationConstant k *
              (x ^ rho.re / ‖rho‖) <
            |chebyshevPsi x - x| := by
  rcases
      exists_far_normalizedPsiError_gt_pi_div_two_of_zeta_zero
        hrhoRe1 hrhoIm hsigmaHalf hsigmaRho
        hzero horder hm with
    ⟨k, hmissing, hconstant, hfar⟩
  refine ⟨k, hmissing, hconstant, ?_⟩
  intro X hX
  have hXPos : 0 < X := zero_lt_one.trans_le hX
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  rcases hfar (Real.log X) hlogX with ⟨y, hy, hnormalized⟩
  refine ⟨Real.exp y, (Real.log_le_iff_le_exp hXPos).mp hy, ?_⟩
  have hrho0 : rho ≠ 0 := by
    intro hrho
    subst rho
    norm_num at hrhoIm
  have hnormPos : (0 : ℝ) < ‖rho‖ := norm_pos_iff.mpr hrho0
  rw [normalizedPsiError, abs_mul, abs_mul,
    abs_of_nonneg (norm_nonneg rho),
    abs_of_pos (Real.exp_pos _)] at hnormalized
  have hxpow :
      (Real.exp y) ^ rho.re =
        Real.exp (rho.re * y) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos y), Real.log_exp]
    congr 1
    ring
  have hexpCancel :
      Real.exp (-rho.re * y) *
          Real.exp (rho.re * y) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  have hscaled :
      (m : ℝ) * strictPiOverTwoOscillationConstant k *
          ((Real.exp y) ^ rho.re) <
        ‖rho‖ * |chebyshevPsi (Real.exp y) - Real.exp y| := by
    rw [hxpow]
    calc
      (m : ℝ) * strictPiOverTwoOscillationConstant k *
            Real.exp (rho.re * y) <
          (‖rho‖ *
              |chebyshevPsi (Real.exp y) - Real.exp y| *
              Real.exp (-rho.re * y)) *
            Real.exp (rho.re * y) :=
        mul_lt_mul_of_pos_right hnormalized
          (Real.exp_pos (rho.re * y))
      _ = ‖rho‖ *
          |chebyshevPsi (Real.exp y) - Real.exp y| := by
        calc
          (‖rho‖ *
                |chebyshevPsi (Real.exp y) - Real.exp y| *
                Real.exp (-rho.re * y)) *
              Real.exp (rho.re * y) =
            (‖rho‖ *
                |chebyshevPsi (Real.exp y) - Real.exp y|) *
              (Real.exp (-rho.re * y) *
                Real.exp (rho.re * y)) := by ring
          _ = ‖rho‖ *
              |chebyshevPsi (Real.exp y) - Real.exp y| := by
            rw [hexpCancel]
            ring
  have hdiv :
      ((m : ℝ) * strictPiOverTwoOscillationConstant k *
          ((Real.exp y) ^ rho.re)) / ‖rho‖ <
        |chebyshevPsi (Real.exp y) - Real.exp y| :=
    (div_lt_iff₀ hnormPos).2 (by
      simpa [mul_comm] using hscaled)
  calc
    (m : ℝ) * strictPiOverTwoOscillationConstant k *
          ((Real.exp y) ^ rho.re / ‖rho‖) =
        ((m : ℝ) * strictPiOverTwoOscillationConstant k *
          ((Real.exp y) ^ rho.re)) / ‖rho‖ := by ring
    _ < |chebyshevPsi (Real.exp y) - Real.exp y| := hdiv

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
