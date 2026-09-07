import PrimeNumberTheorem.MWKFCubicAFEWeightLimit

open Complex Set
open scoped Interval Topology

namespace PrimeNumberTheorem.MWKFCubic

/-!
# The actual real-product Mellin kernel and its residue

The numerator is holomorphic on Re z > -1/2, not asserted entire. Its
normalization at zero is one. Thus crossing zero contributes exactly one
after division by 2πi. This file proves the finite rectangle identity;
infinite-height horizontal-edge limits are a separate obligation.
-/

noncomputable def cubicAFEWeightMellinNumerator (t P : ℝ) (z : ℂ) : ℂ :=
  cubicAFEKernelG t z * cubicAFEGammaProduct t z / cubicAFEGammaProduct t 0 *
    Complex.exp (-z * (Real.log P : ℂ))

noncomputable def cubicAFEWeightMellinKernel (t P : ℝ) (z : ℂ) : ℂ :=
  cubicAFEScalar t z * Complex.exp (-z * (Real.log P : ℂ))

noncomputable def cubicAFEWeightMellinRemainder (t P : ℝ) (z : ℂ) : ℂ :=
  dslope (cubicAFEWeightMellinNumerator t P) 0 z

theorem differentiableOn_cubicAFEWeightMellinNumerator (t P : ℝ) :
    DifferentiableOn ℂ (cubicAFEWeightMellinNumerator t P)
      {z : ℂ | -1 / 2 < z.re} := by
  intro z hz
  have hc (w : ℂ) (hw : w.re = 1 / 2) :
      DifferentiableAt ℂ (fun z : ℂ ↦ Gammaℝ (w + z)) z := by
    have hi := (differentiable_Gammaℝ_inv (w + z)).comp z
      (differentiableAt_const w |>.add differentiableAt_id)
    have hn : (Gammaℝ (w + z))⁻¹ ≠ 0 := by
      apply inv_ne_zero
      apply Gammaℝ_ne_zero_of_re_pos
      simp only [Complex.add_re, hw]
      change -1 / 2 < z.re at hz
      linarith
    have hii : DifferentiableAt ℂ (fun z : ℂ ↦ ((Gammaℝ (w + z))⁻¹)⁻¹) z := hi.inv hn
    simpa only [inv_inv] using hii
  have hs := hc (cubicCriticalPoint t) (by simp [cubicCriticalPoint])
  have hu := hc (1 - cubicCriticalPoint t) (by norm_num [cubicCriticalPoint])
  have hk : DifferentiableAt ℂ (cubicAFEKernelG t) z := by
    unfold cubicAFEKernelG cubicAFEPoleCanceller
    fun_prop
  have he : DifferentiableAt ℂ (fun z : ℂ ↦ Complex.exp (-z * (Real.log P : ℂ))) z := by
    fun_prop
  exact (((hk.mul (hs.mul hu)).div_const _).mul he).differentiableWithinAt

theorem cubicAFEWeightMellinNumerator_zero (t P : ℝ) :
    cubicAFEWeightMellinNumerator t P 0 = 1 := by
  simp [cubicAFEWeightMellinNumerator, cubicAFEKernelG_zero,
    cubicAFEGammaProduct_zero_ne]

theorem cubicAFEWeightMellinKernel_eq_div (t P : ℝ) (z : ℂ) :
    cubicAFEWeightMellinKernel t P z = cubicAFEWeightMellinNumerator t P z / z := by
  unfold cubicAFEWeightMellinKernel cubicAFEWeightMellinNumerator cubicAFEScalar
  ring

theorem differentiableOn_cubicAFEWeightMellinRemainder (t P : ℝ) :
    DifferentiableOn ℂ (cubicAFEWeightMellinRemainder t P)
      {z : ℂ | -1 / 2 < z.re} := by
  apply (Complex.differentiableOn_dslope ?_).2
    (differentiableOn_cubicAFEWeightMellinNumerator t P)
  exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)

theorem cubicAFEWeightMellinKernel_eq_remainder_add (t P : ℝ) {z : ℂ} (hz : z ≠ 0) :
    cubicAFEWeightMellinKernel t P z = cubicAFEWeightMellinRemainder t P z + z⁻¹ := by
  rw [cubicAFEWeightMellinKernel_eq_div]
  unfold cubicAFEWeightMellinRemainder
  rw [dslope_of_ne _ hz]
  simp only [slope_def_module, sub_zero, smul_eq_mul, cubicAFEWeightMellinNumerator_zero]
  field_simp [hz]
  ring

/-- No gamma pole is crossed: the rectangle stays in Re z > -1/2. -/
theorem boundaryRectIntegral_cubicAFEWeightMellinKernel (t P : ℝ) {x0 x1 y0 y1 : ℝ}
    (hxhalf : -1 / 2 < x0) (hx0 : x0 < 0) (hx1 : 0 < x1)
    (hy0 : y0 < 0) (hy1 : 0 < y1) :
    MathlibAux.boundaryRectIntegral (cubicAFEWeightMellinKernel t P) x0 x1 y0 y1 =
      2 * Real.pi * I := by
  classical
  let model : ℂ → ℂ := fun z ↦ cubicAFEWeightMellinRemainder t P z +
    ∑ p ∈ ({0} : Finset ℂ), (z - p)⁻¹ * (1 : ℂ)
  have hg : DifferentiableOn ℂ (cubicAFEWeightMellinRemainder t P)
      ([[x0, x1]] ×ℂ [[y0, y1]]) := by
    apply (differentiableOn_cubicAFEWeightMellinRemainder t P).mono
    intro z hz
    rw [mem_reProdIm, uIcc_of_le (le_of_lt (lt_trans hx0 hx1))] at hz
    exact lt_of_lt_of_le hxhalf hz.1.1
  have hpole : x0 < (0 : ℂ).re ∧ (0 : ℂ).re < x1 ∧
      y0 < (0 : ℂ).im ∧ (0 : ℂ).im < y1 := by
    simpa using And.intro hx0 (And.intro hx1 (And.intro hy0 hy1))
  have hm := MathlibAux.boundaryRectIntegral_eq_finite_simple_pole_residue_sum_of_differentiableOn
    (g := cubicAFEWeightMellinRemainder t P)
    (x0 := x0) (x1 := x1) (y0 := y0) (y1 := y1)
    ({0} : Finset ℂ) (fun _ ↦ (1 : ℂ)) hg (by simpa using hpole)
  have hb : MathlibAux.boundaryRectIntegral (cubicAFEWeightMellinKernel t P) x0 x1 y0 y1 =
      MathlibAux.boundaryRectIntegral model x0 x1 y0 y1 := by
    apply MathlibAux.boundaryRectIntegral_congr_of_eqOn_boundary
    intro z _ hzboundary
    have hz : z ≠ 0 := by
      intro hz
      subst z
      exact hzboundary hpole
    rw [cubicAFEWeightMellinKernel_eq_remainder_add t P hz]
    simp [model]
  rw [hb]
  simpa [model] using hm

end PrimeNumberTheorem.MWKFCubic
