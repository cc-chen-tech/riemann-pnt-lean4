import Mathlib.Analysis.MellinInversion

open Complex MeasureTheory Set

namespace MathlibAux

/-!
# Mellin kernels in logarithmic coordinates

The Mellin-to-Fourier identity uses the substitution `x = exp (-u)`.  This
file exposes the corresponding integrability transfer, which is internal to
Mathlib's proof of Mellin inversion but is also needed when applying
Plancherel to completed L-functions.
-/

/-- The logarithmic-coordinate form of a Mellin integrand on the vertical
line with real part `sigma`. -/
noncomputable def logMellinKernel {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (f : ℝ → E) (sigma u : ℝ) : E :=
  Real.exp (-sigma * u) • f (Real.exp (-u))

private theorem rexp_neg_deriv :
    ∀ x ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt (Real.exp ∘ Neg.neg) (-Real.exp (-x)) Set.univ x :=
  fun x _ => mul_neg_one (Real.exp (-x)) ▸
    ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt

private theorem rexp_neg_image :
    (Real.exp ∘ Neg.neg) '' (Set.univ : Set ℝ) = Set.Ioi 0 := by
  rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective,
    Set.image_univ, Real.range_exp]

private theorem rexp_neg_injOn :
    (Set.univ : Set ℝ).InjOn (Real.exp ∘ Neg.neg) :=
  Real.exp_injective.injOn.comp neg_injective.injOn
    (Set.univ.mapsTo_univ _)

private theorem rexp_cexp_real_line {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (x sigma : ℝ) (v : E) :
    Real.exp (-x) •
        Complex.exp (-x) ^ ((sigma : ℂ) - 1) • v =
      Complex.exp (-(sigma : ℂ) * x) • v := by
  change (Real.exp (-x) : ℂ) • _ = _ • v
  rw [← smul_assoc, smul_eq_mul]
  push_cast
  conv in Complex.exp _ * _ => lhs; rw [← cpow_one (Complex.exp _)]
  rw [← cpow_add _ _ (Complex.exp_ne_zero _),
    cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos]) (by simpa using Real.pi_nonneg)]
  ring_nf

/-- Mellin convergence on a real vertical line implies integrability of the
corresponding logarithmic-coordinate Fourier kernel. -/
theorem integrable_logMellinKernel_of_mellinConvergent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (f : ℝ → E) (sigma : ℝ)
    (hf : MellinConvergent f (sigma : ℂ)) :
    Integrable (logMellinKernel f sigma) := by
  rw [MellinConvergent, ← rexp_neg_image,
    integrableOn_image_iff_integrableOn_abs_deriv_smul
      MeasurableSet.univ rexp_neg_deriv rexp_neg_injOn] at hf
  have hcomplex : Integrable (fun x : ℝ =>
      Complex.exp (-(sigma : ℂ) * x) • f (Real.exp (-x))) := by
    simpa [rexp_cexp_real_line] using hf
  norm_cast at hcomplex

end MathlibAux
