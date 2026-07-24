import PrimeNumberTheorem.VKEdgePiOverTwoAbelBoundary
import Mathlib.MeasureTheory.Function.JacobianOneDim

open Complex Filter MeasureTheory Set Topology

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- The Abel-regularized Fourier coefficient of the normalized logarithmic
PNT error, before multiplying by the norm of a distinguished zero. -/
def psiAbelCoefficient (beta lambda a : ℝ) : ℂ :=
  (a : ℂ) *
    ∫ y : ℝ in Set.Ioi 0,
      ((chebyshevPsi (Real.exp y) - Real.exp y : ℝ) : ℂ) *
        Complex.exp
          (-(((beta + a : ℝ) : ℂ) + I * (lambda : ℂ)) * (y : ℂ))

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

/-- Logarithmic coordinates turn the cutoff Mellin integral into the
one-sided Laplace-Fourier integral of the PNT error.  The proof uses the
measurable one-dimensional Jacobian theorem, so it does not require
continuity of the step function `chebyshevPsi`. -/
lemma integral_logarithmicPsiError_eq_mellin
    (s : ℂ) :
    (∫ y : ℝ in Set.Ioi 0,
        ((chebyshevPsi (Real.exp y) - Real.exp y : ℝ) : ℂ) *
          Complex.exp (-s * (y : ℂ))) =
      mellin psiErrorAboveOneComplex (-s) := by
  let g : ℝ → ℂ := fun x =>
    ((chebyshevPsi x - x : ℝ) : ℂ) *
      (x : ℂ) ^ (-(s + 1))
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
        fun y : ℝ =>
          ((chebyshevPsi (Real.exp y) - Real.exp y : ℝ) : ℂ) *
            Complex.exp (-s * (y : ℂ)) := by
    funext y
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
  rw [mellin_psiErrorAboveOneComplex_neg_eq_integral]
  change (∫ y : ℝ in Set.Ioi 0, _) = ∫ x : ℝ in Set.Ioi 1, g x
  rw [← hintegrand]
  exact hchange.symm

/-- Exact identification of the Abel coefficient with the regularized
logarithmic-derivative Mellin model. -/
theorem psiAbelCoefficient_eq_regularizedNegLogDerivModel
    {beta lambda a : ℝ} (hbeta0 : 0 ≤ beta) (ha : 0 < a) :
    psiAbelCoefficient beta lambda a =
      (a : ℂ) /
          ((beta + a : ℝ) + I * lambda) *
        regularizedNegLogDerivModel
          ((beta + a : ℝ) + I * lambda) := by
  let s : ℂ := ((beta + a : ℝ) : ℂ) + I * (lambda : ℂ)
  have hs0 : s ≠ 0 := by
    apply ne_zero_of_re_pos
    dsimp [s]
    simp
    linarith
  rw [psiAbelCoefficient]
  rw [show (((beta + a : ℝ) : ℂ) + I * (lambda : ℂ)) = s by rfl]
  rw [integral_logarithmicPsiError_eq_mellin s]
  simp only [regularizedNegLogDerivModel]
  change
    (a : ℂ) * mellin psiErrorAboveOneComplex (-s) =
      (a : ℂ) / s * (s * mellin psiErrorAboveOneComplex (-s))
  field_simp [hs0]

/-- At a positive-ordinate zeta zero, the actual Abel coefficient of the
logarithmically normalized PNT error has the expected residue
`-m * ‖rho‖ / rho`. -/
theorem tendsto_psiAbelCoefficient_of_zeta_zero
    {rho : ℂ} {m : ℕ}
    (hrhoRe0 : 0 ≤ rho.re) (hrhoRe1 : rho.re < 1)
    (hrhoIm : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (horder : analyticOrderAt riemannZeta rho = m)
    (herror : PsiPowerErrorBound rho.re) :
    Tendsto
      (fun a : ℝ =>
        (‖rho‖ : ℂ) * psiAbelCoefficient rho.re rho.im a)
      (𝓝[>] 0)
      (𝓝 (-(m : ℂ) * (‖rho‖ : ℂ) / rho)) := by
  have hrho0 : rho ≠ 0 := by
    intro h
    subst rho
    norm_num at hrhoIm
  have hboundary :=
    tendsto_atRight_mul_regularizedNegLogDerivModel_of_zeta_zero
      hrhoRe0 hrhoRe1 hrhoIm hzero horder herror
  have hpath :
      Tendsto (fun a : ℝ => rho + (a : ℂ))
        (𝓝[>] 0) (𝓝 rho) := by
    have hcont : ContinuousAt (fun a : ℝ => rho + (a : ℂ)) 0 := by
      fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hfactor :
      Tendsto
        (fun a : ℝ => (‖rho‖ : ℂ) / (rho + (a : ℂ)))
        (𝓝[>] 0) (𝓝 ((‖rho‖ : ℂ) / rho)) := by
    exact tendsto_const_nhds.div hpath hrho0
  have hproduct :
      Tendsto
        (fun a : ℝ =>
          ((‖rho‖ : ℂ) / (rho + (a : ℂ))) *
            ((a : ℂ) *
              regularizedNegLogDerivModel (rho + (a : ℂ))))
        (𝓝[>] 0)
        (𝓝 ((‖rho‖ : ℂ) / rho * (-(m : ℂ)))) :=
    hfactor.mul hboundary
  have hlimit :
      (‖rho‖ : ℂ) / rho * (-(m : ℂ)) =
        -(m : ℂ) * (‖rho‖ : ℂ) / rho := by ring
  rw [← hlimit]
  apply hproduct.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  have haPos : 0 < a := ha
  have hEq :=
    psiAbelCoefficient_eq_regularizedNegLogDerivModel
      (beta := rho.re) (lambda := rho.im) hrhoRe0 haPos
  have hs :
      (((rho.re + a : ℝ) : ℂ) + I * (rho.im : ℂ)) =
        rho + (a : ℂ) := by
    apply Complex.ext
    · simp
    · simp
  rw [hEq, hs]
  ring

/-- At a nonzero point on the same vertical boundary, the actual Abel
coefficient of the logarithmically normalized PNT error vanishes. -/
theorem tendsto_psiAbelCoefficient_of_zeta_ne_zero
    {beta gamma : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (hgamma : 0 < gamma)
    (hzeta : riemannZeta ((beta : ℂ) + I * gamma) ≠ 0)
    (herror : PsiPowerErrorBound beta) :
    Tendsto
      (fun a : ℝ =>
        psiAbelCoefficient beta gamma a)
      (𝓝[>] 0) (𝓝 0) := by
  let rho : ℂ := (beta : ℂ) + I * gamma
  have hrho0 : rho ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp [rho] at him
    linarith
  have hboundary :=
    tendsto_atRight_mul_regularizedNegLogDerivModel_of_zeta_ne_zero
      hbeta0 hbeta1 hgamma hzeta herror
  have hpath :
      Tendsto (fun a : ℝ => rho + (a : ℂ))
        (𝓝[>] 0) (𝓝 rho) := by
    have hcont : ContinuousAt (fun a : ℝ => rho + (a : ℂ)) 0 := by
      fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hfactor :
      Tendsto
        (fun a : ℝ => ((rho + (a : ℂ))⁻¹))
        (𝓝[>] 0) (𝓝 rho⁻¹) :=
    hpath.inv₀ hrho0
  have hproduct :
      Tendsto
        (fun a : ℝ =>
          (rho + (a : ℂ))⁻¹ *
            ((a : ℂ) *
              regularizedNegLogDerivModel (rho + (a : ℂ))))
        (𝓝[>] 0) (𝓝 0) := by
    simpa using hfactor.mul hboundary
  apply hproduct.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  have haPos : 0 < a := ha
  have hEq :=
    psiAbelCoefficient_eq_regularizedNegLogDerivModel
      (beta := beta) (lambda := gamma) hbeta0 haPos
  have hs :
      (((beta + a : ℝ) : ℂ) + I * (gamma : ℂ)) =
        rho + (a : ℂ) := by
    simp [rho]
    ring
  rw [hEq, hs]
  ring

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
