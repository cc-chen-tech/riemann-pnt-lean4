import PrimeNumberTheorem.NontrivialZeroMultiplicity

open Complex Filter

namespace PrimeNumberTheorem
namespace RiemannVonMangoldt

theorem differentiable_completedZeta :
    Differentiable ℂ RiemannHypothesis.completedZeta := by
  unfold RiemannHypothesis.completedZeta
  have hhalf : Differentiable ℂ (fun _ : ℂ => (1 / 2 : ℂ)) :=
    differentiable_const _
  have hid : Differentiable ℂ (fun z : ℂ => z) := differentiable_id
  have hsub : Differentiable ℂ (fun z : ℂ => z - 1) :=
    differentiable_id.sub (differentiable_const _)
  exact ((((hhalf.mul hid).mul hsub).mul differentiable_completedZeta₀).sub
    (hhalf.mul hsub)).add (hhalf.mul hid)

lemma completedZeta_eventuallyEq_factorization {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    RiemannHypothesis.completedZeta =ᶠ[nhds s]
      fun z : ℂ => (1 / 2) * z * (z - 1) * completedRiemannZeta z := by
  filter_upwards [eventually_ne_nhds hs0, eventually_ne_nhds hs1] with z hz0 hz1
  have hclear :
      z * (z - 1) * completedRiemannZeta z =
        z * (z - 1) * completedRiemannZeta₀ z - (z - 1) + z := by
    rw [completedRiemannZeta_eq]
    field_simp [hz0, sub_ne_zero.mpr hz1, sub_ne_zero.mpr hz1.symm]
    ring
  rw [RiemannHypothesis.completedZeta]
  calc
    (1 / 2) * z * (z - 1) * completedRiemannZeta₀ z -
          (1 / 2) * (z - 1) + (1 / 2) * z =
        (1 / 2) *
          (z * (z - 1) * completedRiemannZeta₀ z - (z - 1) + z) := by
      ring
    _ = (1 / 2) * (z * (z - 1) * completedRiemannZeta z) := by
      rw [← hclear]
    _ = (1 / 2) * z * (z - 1) * completedRiemannZeta z := by
      ring

private lemma ne_zero_of_pos_re {s : ℂ} (hsre : 0 < s.re) : s ≠ 0 := by
  intro hs
  have hre := congrArg Complex.re hs
  simp at hre
  linarith

private lemma ne_one_of_re_lt_one {s : ℂ} (hsre : s.re < 1) : s ≠ 1 := by
  intro hs
  have hre := congrArg Complex.re hs
  simp at hre
  linarith

theorem completedZeta_eq_zero_iff_riemannZeta_eq_zero_of_mem_criticalStrip
    {s : ℂ} (hsre : 0 < s.re) (hsre' : s.re < 1) :
    RiemannHypothesis.completedZeta s = 0 ↔ riemannZeta s = 0 := by
  have hs0 := ne_zero_of_pos_re hsre
  have hs1 := ne_one_of_re_lt_one hsre'
  have hGamma : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hsre
  have hfactor :=
    (completedZeta_eventuallyEq_factorization hs0 hs1).self_of_nhds
  have hpref : (1 / 2 : ℂ) * s * (s - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hs0) (sub_ne_zero.mpr hs1)
  rw [hfactor, riemannZeta_def_of_ne_zero hs0, mul_eq_zero]
  simp only [hpref, false_or]
  simp [hGamma]

theorem analyticOrderAt_completedZeta_eq_riemannZeta_of_mem_criticalStrip
    {s : ℂ} (hsre : 0 < s.re) (hsre' : s.re < 1) :
    analyticOrderAt RiemannHypothesis.completedZeta s =
      analyticOrderAt riemannZeta s := by
  have hs0 := ne_zero_of_pos_re hsre
  have hs1 := ne_one_of_re_lt_one hsre'
  have hhalf : AnalyticAt ℂ (fun _ : ℂ => (1 / 2 : ℂ)) s := by fun_prop
  have hid : AnalyticAt ℂ (fun z : ℂ => z) s := by fun_prop
  have hsub : AnalyticAt ℂ (fun z : ℂ => z - 1) s := by fun_prop
  have hcompleted0 : AnalyticAt ℂ completedRiemannZeta₀ s :=
    differentiable_completedZeta₀.analyticAt s
  have hone_div : AnalyticAt ℂ (fun z : ℂ => 1 / z) s :=
    analyticAt_const.div analyticAt_id hs0
  have hone_sub_div : AnalyticAt ℂ (fun z : ℂ => 1 / (1 - z)) s :=
    analyticAt_const.div (analyticAt_const.sub analyticAt_id)
      (sub_ne_zero.mpr hs1.symm)
  have hcompleted : AnalyticAt ℂ completedRiemannZeta s := by
    apply ((hcompleted0.sub hone_div).sub hone_sub_div).congr
    filter_upwards [] with z
    exact (completedRiemannZeta_eq z).symm
  have hxi := analyticOrderAt_congr
    (completedZeta_eventuallyEq_factorization hs0 hs1)
  have hxiOrder :
      analyticOrderAt RiemannHypothesis.completedZeta s =
        analyticOrderAt completedRiemannZeta s := by
    rw [hxi]
    change analyticOrderAt
      (((fun _ : ℂ => (1 / 2 : ℂ)) * (fun z : ℂ => z) *
        (fun z : ℂ => z - 1)) * completedRiemannZeta) s =
        analyticOrderAt completedRiemannZeta s
    rw [analyticOrderAt_mul (hhalf.mul hid |>.mul hsub) hcompleted,
      analyticOrderAt_mul (hhalf.mul hid) hsub,
      analyticOrderAt_mul hhalf hid]
    rw [hhalf.analyticOrderAt_eq_zero.mpr (by norm_num),
      hid.analyticOrderAt_eq_zero.mpr hs0,
      hsub.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hs1)]
    simp
  have hgamma : AnalyticAt ℂ (fun z : ℂ => (Gammaℝ z)⁻¹) s :=
    differentiable_Gammaℝ_inv.analyticAt s
  have hgamma_ne : (Gammaℝ s)⁻¹ ≠ 0 :=
    inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hsre)
  have hzeta_completed : riemannZeta =ᶠ[nhds s]
      fun z : ℂ => completedRiemannZeta z * (Gammaℝ z)⁻¹ := by
    filter_upwards [eventually_ne_nhds hs0] with z hz
    rw [riemannZeta_def_of_ne_zero hz, div_eq_mul_inv]
  have hzetaOrder :
      analyticOrderAt riemannZeta s =
        analyticOrderAt completedRiemannZeta s := by
    calc
      analyticOrderAt riemannZeta s =
          analyticOrderAt
            (fun z : ℂ => completedRiemannZeta z * (Gammaℝ z)⁻¹) s :=
        analyticOrderAt_congr hzeta_completed
      _ = analyticOrderAt completedRiemannZeta s +
            analyticOrderAt (fun z : ℂ => (Gammaℝ z)⁻¹) s :=
        analyticOrderAt_mul hcompleted hgamma
      _ = analyticOrderAt completedRiemannZeta s + 0 := by
        rw [hgamma.analyticOrderAt_eq_zero.mpr hgamma_ne]
      _ = analyticOrderAt completedRiemannZeta s := add_zero _
  exact hxiOrder.trans hzetaOrder.symm

theorem analyticOrderNatAt_completedZeta_eq_riemannZeta_of_mem_criticalStrip
    {s : ℂ} (hsre : 0 < s.re) (hsre' : s.re < 1) :
    analyticOrderNatAt RiemannHypothesis.completedZeta s =
      analyticOrderNatAt riemannZeta s :=
  congrArg ENat.toNat
    (analyticOrderAt_completedZeta_eq_riemannZeta_of_mem_criticalStrip
      hsre hsre')

theorem completedZeta_ne_zero_of_re_eq_one_of_im_ne_zero
    {s : ℂ} (hsre : s.re = 1) (hsim : s.im ≠ 0) :
    RiemannHypothesis.completedZeta s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro hs
    have hre := congrArg Complex.re hs
    simp [hsre] at hre
  have hs1 : s ≠ 1 := by
    intro hs
    apply hsim
    have him := congrArg Complex.im hs
    simpa using him
  have hsrePos : 0 < s.re := by linarith
  have hGamma : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hsrePos
  have hzeta : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re hsre.ge
  have hcompleted : completedRiemannZeta s ≠ 0 := by
    intro hzero
    apply hzeta
    rw [riemannZeta_def_of_ne_zero hs0, hzero]
    simp
  rw [(completedZeta_eventuallyEq_factorization hs0 hs1).self_of_nhds]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) hs0) (sub_ne_zero.mpr hs1))
    hcompleted

theorem completedZeta_ne_zero_of_re_eq_zero_of_im_ne_zero
    {s : ℂ} (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    RiemannHypothesis.completedZeta s ≠ 0 := by
  have hwre : (1 - s).re = 1 := by
    simp [Complex.sub_re, hsre]
  have hwim : (1 - s).im ≠ 0 := by
    simpa using hsim
  rw [RiemannHypothesis.functional_equation s]
  exact completedZeta_ne_zero_of_re_eq_one_of_im_ne_zero hwre hwim

end RiemannVonMangoldt
end PrimeNumberTheorem
