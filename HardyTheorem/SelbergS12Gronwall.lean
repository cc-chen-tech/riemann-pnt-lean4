import HardyTheorem.SelbergS12RightLine
import Mathlib.Analysis.ODE.Gronwall

open Complex Set

namespace HardyTheorem

/-!
# Selberg S12: horizontal propagation by Grönwall

The reciprocal of zeta is propagated from an absolutely convergent point on
the right to the one-line.  The path is parametrized from right to left, so
the two minus signs in differentiating `1 / ζ` cancel.
-/

noncomputable def selbergS12HorizontalPoint (σ t x : ℝ) : ℂ :=
  (((σ - x : ℝ) : ℂ) + I * t)

noncomputable def selbergS12ReciprocalAlong (σ t x : ℝ) : ℂ :=
  (riemannZeta (selbergS12HorizontalPoint σ t x))⁻¹

@[simp] theorem selbergS12HorizontalPoint_re (σ t x : ℝ) :
    (selbergS12HorizontalPoint σ t x).re = σ - x := by
  simp [selbergS12HorizontalPoint]

@[simp] theorem selbergS12HorizontalPoint_im (σ t x : ℝ) :
    (selbergS12HorizontalPoint σ t x).im = t := by
  simp [selbergS12HorizontalPoint]

/-- Exact derivative of `1 / ζ` along the right-to-left horizontal segment. -/
theorem hasDerivAt_selbergS12ReciprocalAlong
    {σ t x : ℝ}
    (hpoint : selbergS12HorizontalPoint σ t x ≠ 1)
    (hzeta : riemannZeta (selbergS12HorizontalPoint σ t x) ≠ 0) :
    HasDerivAt (selbergS12ReciprocalAlong σ t)
      (logDeriv riemannZeta (selbergS12HorizontalPoint σ t x) *
        selbergS12ReciprocalAlong σ t x) x := by
  let p : ℂ → ℂ := fun z => (σ : ℂ) - z + I * t
  have hp : HasDerivAt p (-1) (x : ℂ) := by
    simpa [p] using
      ((hasDerivAt_const (x : ℂ) (σ : ℂ)).sub (hasDerivAt_id (x : ℂ))).add_const
        (I * (t : ℂ))
  have hp_eq : p (x : ℂ) = selbergS12HorizontalPoint σ t x := by
    simp [p, selbergS12HorizontalPoint]
  have hz : HasDerivAt (fun z : ℂ => riemannZeta (p z))
      (deriv riemannZeta (p (x : ℂ)) * (-1)) (x : ℂ) :=
    (differentiableAt_riemannZeta (hp_eq ▸ hpoint)).hasDerivAt.comp (x : ℂ) hp
  have hinv := hz.inv (hp_eq ▸ hzeta)
  have hreal := hinv.comp_ofReal
  convert hreal using 1
  · funext y
    simp [selbergS12ReciprocalAlong, selbergS12HorizontalPoint, p]
  · simp only [selbergS12ReciprocalAlong, selbergS12HorizontalPoint, hp_eq,
      logDeriv_apply]
    field_simp [hzeta]

/-- If the logarithmic derivative is bounded by `K` on a horizontal segment,
then the reciprocal of zeta grows by at most `exp (K * ℓ)` along that segment. -/
theorem norm_selbergS12ReciprocalAlong_le_mul_exp
    {σ t ℓ K δ : ℝ}
    (hℓ : 0 ≤ ℓ)
    (hsafe : ∀ x ∈ Icc (0 : ℝ) ℓ,
      selbergS12HorizontalPoint σ t x ≠ 1 ∧
        riemannZeta (selbergS12HorizontalPoint σ t x) ≠ 0)
    (hlog : ∀ x ∈ Icc (0 : ℝ) ℓ,
      ‖logDeriv riemannZeta (selbergS12HorizontalPoint σ t x)‖ ≤ K)
    (hzero : ‖selbergS12ReciprocalAlong σ t 0‖ ≤ δ) :
    ‖selbergS12ReciprocalAlong σ t ℓ‖ ≤ δ * Real.exp (K * ℓ) := by
  let f : ℝ → ℂ := selbergS12ReciprocalAlong σ t
  let f' : ℝ → ℂ := fun x =>
    logDeriv riemannZeta (selbergS12HorizontalPoint σ t x) * f x
  have hderiv : ∀ x ∈ Icc (0 : ℝ) ℓ, HasDerivAt f (f' x) x := by
    intro x hx
    exact hasDerivAt_selbergS12ReciprocalAlong (hsafe x hx).1 (hsafe x hx).2
  have hcont : ContinuousOn f (Icc (0 : ℝ) ℓ) := by
    intro x hx
    exact (hderiv x hx).continuousAt.continuousWithinAt
  have hbound : ∀ x ∈ Ico (0 : ℝ) ℓ, ‖f' x‖ ≤ K * ‖f x‖ := by
    intro x hx
    rw [show f' x = logDeriv riemannZeta
      (selbergS12HorizontalPoint σ t x) * f x by rfl, norm_mul]
    exact mul_le_mul_of_nonneg_right (hlog x ⟨hx.1, hx.2.le⟩) (norm_nonneg _)
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le
    (δ := δ) (K := K) (ε := 0)
    hcont
    (fun x hx => (hderiv x ⟨hx.1, hx.2.le⟩).hasDerivWithinAt)
    hzero
    (fun x hx => by simpa using hbound x hx)
    ℓ ⟨hℓ, le_rfl⟩
  simpa [f, gronwallBound_ε0] using hg

end HardyTheorem
