import MathlibAux.MellinVerticalStripBound
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

open Complex MeasureTheory Set

namespace MathlibAux

/-!
# Gamma bounds on positive closed vertical strips

Euler's absolutely convergent integral bounds Gamma by its real argument.
The Mellin endpoint majorant then yields a bound uniform in imaginary part
on any closed strip in the positive half-plane. No Stirling estimate or
assumed spectral bound is used.
-/

theorem norm_Gamma_le_Gamma_re {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Complex.GammaIntegral, Real.Gamma_eq_integral hz]
  apply norm_integral_le_of_norm_le (Real.GammaIntegral_convergent hz)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos (-x)).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.sub_re, Complex.one_re, le_refl]

private theorem gamma_eq_mellin {z : ℂ} (hz : 0 < z.re) :
    Complex.Gamma z = mellin (fun x : ℝ ↦ (Real.exp (-x) : ℂ)) z := by
  rw [Complex.Gamma_eq_integral hz, Complex.GammaIntegral, mellin]
  simp only [smul_eq_mul, mul_comm]

theorem exists_norm_Gamma_le_on_positive_reIcc {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖Complex.Gamma z‖ ≤ C := by
  have hma : MellinConvergent (fun x : ℝ ↦ (Real.exp (-x) : ℂ)) (a : ℂ) := by
    simpa only [MellinConvergent, smul_eq_mul, mul_comm] using
      (Complex.GammaIntegral_convergent (by simpa using ha : 0 < (a : ℂ).re))
  have hmb : MellinConvergent (fun x : ℝ ↦ (Real.exp (-x) : ℂ)) (b : ℂ) := by
    simpa only [MellinConvergent, smul_eq_mul, mul_comm] using
      (Complex.GammaIntegral_convergent (by simpa using hb : 0 < (b : ℂ).re))
  obtain ⟨C, hC, hbound⟩ := exists_norm_mellin_le_on_reIcc hma hmb
  refine ⟨C, hC, ?_⟩
  intro z haz hzb
  rw [gamma_eq_mellin (ha.trans_le haz)]
  exact hbound z haz hzb

theorem exists_norm_Gammaℝ_le_on_positive_reIcc {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖Complex.Gammaℝ z‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_Gamma_le_on_positive_reIcc
    (show 0 < a / 2 by linarith) (show 0 < b / 2 by linarith)
  refine ⟨Real.pi ^ (-a / 2) * C, mul_nonneg (Real.rpow_nonneg Real.pi_pos.le _) hC, ?_⟩
  intro z haz hzb
  have hzhalf : (z / (2 : ℂ)).re = z.re / 2 := by simp
  have hzneg : (-z / (2 : ℂ)).re = -z.re / 2 := by simp
  have hg : ‖Complex.Gamma (z / 2)‖ ≤ C :=
    hbound _ (by rw [hzhalf]; linarith) (by rw [hzhalf]; linarith)
  have hp : Real.pi ^ (-z.re / 2) ≤ Real.pi ^ (-a / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [Real.two_le_pi]) (by linarith)
  rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, hzneg]
  exact mul_le_mul hp hg (norm_nonneg _) (Real.rpow_nonneg Real.pi_pos.le _)

end MathlibAux
