import MathlibAux.BoundaryRectResidue
import Mathlib.Analysis.Complex.RemovableSingularity

open Complex Set MeasureTheory Filter
open scoped Interval Topology

namespace MathlibAux

/-! The rectangle derivative formula is proved by removing the first two
Taylor terms. The double principal part has the single-valued primitive
`-1/z`; no general meromorphic residue proposition is assumed. -/

private theorem integral_affine_inv_sq (v q : ℂ) (a b : ℝ)
    (hne : ∀ t ∈ [[a, b]], v + t * q ≠ 0) :
    (∫ t : ℝ in a..b, q / (v + t * q) ^ 2) =
      -(v + b * q)⁻¹ + (v + a * q)⁻¹ := by
  have hd : ∀ t ∈ [[a, b]], HasDerivAt
      (fun t : ℝ => -(v + t * q)⁻¹) (q / (v + t * q) ^ 2) t := by
    intro t ht
    have h := (((hasDerivAt_id (t : ℂ)).mul_const q).const_add v).inv (hne t ht)
    simpa [neg_div] using h.neg.comp_ofReal
  have hc : ContinuousOn (fun t : ℝ => q / (v + t * q) ^ 2) [[a, b]] := by
    apply continuousOn_const.div
      ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn.pow 2)
    exact fun t ht => pow_ne_zero 2 (hne t ht)
  simpa [sub_eq_add_neg] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable

private theorem edge_ne_zero_horizontal {y : ℝ} (hy : y ≠ 0) (x : ℝ) :
    (x : ℂ) + y * I ≠ 0 := by
  intro h
  exact hy (by simpa using congrArg Complex.im h)

private theorem edge_ne_zero_vertical {x : ℝ} (hx : x ≠ 0) (y : ℝ) :
    (x : ℂ) + y * I ≠ 0 := by
  intro h
  exact hx (by simpa using congrArg Complex.re h)

private theorem boundaryRectIntegral_inv_sq {a b c d : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    boundaryRectIntegral (fun z : ℂ => 1 / z ^ 2) a b c d = 0 := by
  have hhor (y : ℝ) (hy : y ≠ 0) := integral_affine_inv_sq (y * I) 1 a b
    (fun t _ => by simpa [add_comm] using edge_ne_zero_horizontal hy t)
  have hver (x : ℝ) (hx : x ≠ 0) := integral_affine_inv_sq x I c d
    (fun t _ => edge_ne_zero_vertical hx t)
  have hv (x : ℝ) (hx : x ≠ 0) :
      I * (∫ t : ℝ in c..d, 1 / ((x : ℂ) + t * I) ^ 2) =
        -((x : ℂ) + d * I)⁻¹ + ((x : ℂ) + c * I)⁻¹ := by
    rw [← intervalIntegral.integral_const_mul]
    simpa only [mul_one_div] using hver x hx
  unfold boundaryRectIntegral
  simp only [smul_eq_mul]
  rw [show (∫ t : ℝ in a..b, 1 / ((t : ℂ) + c * I) ^ 2) =
      -((b : ℂ) + c * I)⁻¹ + ((a : ℂ) + c * I)⁻¹ by
        simpa [add_comm] using hhor c hc,
    show (∫ t : ℝ in a..b, 1 / ((t : ℂ) + d * I) ^ 2) =
      -((b : ℂ) + d * I)⁻¹ + ((a : ℂ) + d * I)⁻¹ by
        simpa [add_comm] using hhor d hd,
    hv b hb, hv a ha]
  ring

/-- Cauchy's derivative formula on an arbitrary positively oriented rectangle
containing zero strictly. The numerator need not vanish at zero. -/
theorem boundaryRectIntegral_div_sq {f : ℂ → ℂ} {a b c d : ℝ}
    (hf : DifferentiableOn ℂ f ([[a, b]] ×ℂ [[c, d]]))
    (ha : a < 0) (hb : 0 < b) (hc : c < 0) (hd : 0 < d) :
    boundaryRectIntegral (fun w => f w / w ^ 2) a b c d =
      (2 * Real.pi * I) * deriv f 0 := by
  have hnhds : ([[a, b]] ×ℂ [[c, d]]) ∈ 𝓝 (0 : ℂ) := by
    rw [← mem_interior_iff_mem_nhds, interior_reProdIm,
      uIcc_of_le (ha.trans hb).le, uIcc_of_le (hc.trans hd).le,
      interior_Icc, interior_Icc, mem_reProdIm]
    exact ⟨⟨ha, hb⟩, hc, hd⟩
  let g := dslope (dslope f 0) 0
  have hg : DifferentiableOn ℂ g ([[a, b]] ×ℂ [[c, d]]) :=
    (Complex.differentiableOn_dslope hnhds).mpr
      ((Complex.differentiableOn_dslope hnhds).mpr hf)
  let A : ℂ → ℂ := fun z => g z + z⁻¹ * deriv f 0
  let B : ℂ → ℂ := fun z => (1 / z ^ 2) * f 0
  have heq : boundaryRectIntegral (fun w => f w / w ^ 2) a b c d =
      boundaryRectIntegral (fun w => A w + B w) a b c d := by
    apply boundaryRectIntegral_congr_of_eqOn_boundary
    intro z _ hz
    have hzne : z ≠ 0 := by
      intro h; subst z; exact hz ⟨ha, hb, hc, hd⟩
    simp only [A, B, g, dslope_of_ne _ hzne, dslope_same, slope,
      sub_zero, smul_eq_mul, vsub_eq_sub]
    field_simp
    ring
  have hgc := boundaryRectIntervalIntegrable_of_continuousOn hg.continuousOn
  have hh (y : ℝ) (hy : y ≠ 0) :
      Continuous (fun x : ℝ => ((x : ℂ) + y * I)⁻¹) :=
    (Complex.continuous_ofReal.add (continuous_const.mul continuous_const)).inv₀
      (edge_ne_zero_horizontal hy)
  have hv (x : ℝ) (hx : x ≠ 0) :
      Continuous (fun y : ℝ => ((x : ℂ) + y * I)⁻¹) :=
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).inv₀
      (edge_ne_zero_vertical hx)
  have hAh (y : ℝ) (hy : y ≠ 0) :
      IntervalIntegrable (fun x : ℝ => ((x : ℂ) + y * I)⁻¹ * deriv f 0)
        volume a b := ((hh y hy).mul continuous_const).intervalIntegrable a b
  have hAv (x : ℝ) (hx : x ≠ 0) :
      IntervalIntegrable (fun y : ℝ => ((x : ℂ) + y * I)⁻¹ * deriv f 0)
        volume c d := ((hv x hx).mul continuous_const).intervalIntegrable c d
  have hBh (y : ℝ) (hy : y ≠ 0) :
      IntervalIntegrable (fun x : ℝ => B ((x : ℂ) + y * I)) volume a b := by
    have hC : Continuous (fun x : ℝ => (((x : ℂ) + y * I)⁻¹) ^ 2 * f 0) :=
      ((hh y hy).pow 2).mul continuous_const
    simpa only [B, one_div, inv_pow] using
      hC.intervalIntegrable (μ := volume) a b
  have hBv (x : ℝ) (hx : x ≠ 0) :
      IntervalIntegrable (fun y : ℝ => B ((x : ℂ) + y * I)) volume c d := by
    have hC : Continuous (fun y : ℝ => (((x : ℂ) + y * I)⁻¹) ^ 2 * f 0) :=
      ((hv x hx).pow 2).mul continuous_const
    simpa only [B, one_div, inv_pow] using
      hC.intervalIntegrable (μ := volume) c d
  rw [heq, boundaryRectIntegral_add A B a b c d
    (hgc.1.add (hAh c hc.ne)) (hBh c hc.ne)
    (hgc.2.1.add (hAh d hd.ne')) (hBh d hd.ne')
    (hgc.2.2.1.add (hAv b hb.ne')) (hBv b hb.ne')
    (hgc.2.2.2.add (hAv a ha.ne)) (hBv a ha.ne)]
  have hA : boundaryRectIntegral A a b c d = (2 * Real.pi * I) * deriv f 0 := by
    simpa only [A, sub_zero] using
      boundaryRectIntegral_eq_simple_pole_residue_of_differentiableOn
        (p := 0) (a := deriv f 0) hg ha hb hc hd
  rw [hA, show boundaryRectIntegral B a b c d = 0 by
    rw [show B = fun z : ℂ => (1 / z ^ 2) * f 0 from rfl,
      boundaryRectIntegral_mul_const,
      boundaryRectIntegral_inv_sq ha.ne hb.ne' hc.ne hd.ne', zero_mul], add_zero]

end MathlibAux
