import Mathlib.Analysis.MellinTransform

open Complex MeasureTheory Set

namespace MathlibAux

/-!
# Uniform bounds for Mellin transforms on closed vertical strips

Absolute convergence at the two real endpoints dominates every Mellin
integrand whose real part lies between them.  The estimate is uniform in the
imaginary part and is the analytic input needed for Gaussian contour kernels.
-/

/-- The sum of the two endpoint Mellin-integrand norms. -/
noncomputable def mellinEndpointMajorant
    (f : ℝ → ℂ) (a b t : ℝ) : ℝ :=
  ‖(t : ℂ) ^ ((a : ℂ) - 1) * f t‖ +
    ‖(t : ℂ) ^ ((b : ℂ) - 1) * f t‖

/-- Absolute convergence at the two real endpoints gives a uniform bound on
the Mellin transform throughout the intervening closed vertical strip. -/
theorem exists_norm_mellin_le_on_reIcc
    {f : ℝ → ℂ} {a b : ℝ}
    (ha : MellinConvergent f (a : ℂ))
    (hb : MellinConvergent f (b : ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ,
      a ≤ s.re → s.re ≤ b → ‖mellin f s‖ ≤ C := by
  let g : ℝ → ℝ := mellinEndpointMajorant f a b
  have ha' : IntegrableOn
      (fun t : ℝ ↦ (t : ℂ) ^ ((a : ℂ) - 1) * f t)
      (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul] using ha
  have hb' : IntegrableOn
      (fun t : ℝ ↦ (t : ℂ) ^ ((b : ℂ) - 1) * f t)
      (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul] using hb
  have hg : IntegrableOn g (Ioi 0) := by
    exact ha'.norm.add hb'.norm
  refine ⟨∫ t : ℝ in Ioi 0, g t, integral_nonneg (fun t ↦ by
    exact add_nonneg (norm_nonneg _) (norm_nonneg _)), ?_⟩
  intro s hsa hsb
  rw [mellin]
  apply MeasureTheory.norm_integral_le_of_norm_le hg
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  have hpow : t ^ (s.re - 1) ≤
      t ^ (a - 1) + t ^ (b - 1) := by
    by_cases ht1 : t ≤ 1
    · exact (Real.rpow_le_rpow_of_exponent_ge ht0 ht1 (by linarith)).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg ht0.le _))
    · have h1t : 1 ≤ t := le_of_not_ge ht1
      exact (Real.rpow_le_rpow_of_exponent_le h1t (by linarith)).trans
        (le_add_of_nonneg_left (Real.rpow_nonneg ht0.le _))
  simp only [norm_smul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht0,
    sub_re, ofReal_re, one_re, g, mellinEndpointMajorant]
  simpa [add_mul] using
    mul_le_mul_of_nonneg_right hpow (norm_nonneg (f t))

end MathlibAux
