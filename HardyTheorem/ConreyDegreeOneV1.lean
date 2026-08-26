import HardyTheorem.ConreyDegreeOneEta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import ZeroFreeRegion.MeromorphicAux

/-!
# Conrey's degree-one V1 factor

This file introduces the actual degree-one `V₁` used before the mollifier is
attached in Conrey's equation (40).  On the critical strip it proves the exact
factorization `eta = H * V₁`, then transfers zeros and analytic multiplicities
through the nonvanishing archimedean factor `H`.
-/

open Complex Filter Set Topology
open PrimeNumberTheorem.RiemannVonMangoldt

namespace HardyTheorem

/-- Conrey's archimedean factor `H(s) = 1/2 s(s-1) Gamma_R(s)`. -/
noncomputable def conreyH (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) * Gammaℝ s

/-- The degree-one `V₁` satisfying `eta = H * V₁` on the critical strip. -/
noncomputable def conreyDegreeOneV1 (g g0 g1 L : ℝ) (s : ℂ) : ℂ :=
  ((g : ℂ) + I * (g0 : ℂ)) * riemannZeta s +
    ((g1 / L : ℝ) : ℂ) *
      (deriv riemannZeta s +
        (deriv conreyH s / conreyH s) * riemannZeta s)

private theorem ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : s ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

private theorem ne_one_of_re_lt_one {s : ℂ} (hs : s.re < 1) : s ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

private theorem analyticAt_conreyH_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ conreyH s := by
  have hpowDiff : Differentiable ℂ
      (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) :=
    (differentiable_id.neg.div_const (2 : ℂ)).const_cpow
      (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hpow : AnalyticAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s :=
    hpowDiff.analyticAt s
  let U : Set ℂ := {z | 0 < z.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const continuous_re
  have hgammaDiff : DifferentiableOn ℂ (fun z : ℂ => Gamma (z / 2)) U := by
    intro z hz
    have hpoles : ∀ m : ℕ, z / 2 ≠ -(m : ℂ) := by
      intro m h
      have hre := congrArg Complex.re h
      norm_num at hre
      have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      dsimp [U] at hz
      linarith
    exact ((Complex.differentiableAt_Gamma (z / 2) hpoles).comp z
      (differentiableAt_id.div_const 2)).differentiableWithinAt
  have hgamma : AnalyticAt ℂ (fun z : ℂ => Gamma (z / 2)) s :=
    hgammaDiff.analyticOnNhd hUopen s hs
  have hgammaR : AnalyticAt ℂ Gammaℝ s := by
    change AnalyticAt ℂ
      (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Gamma (z / 2)) s
    exact hpow.mul hgamma
  exact (((analyticAt_const.mul analyticAt_id).mul
    (analyticAt_id.sub analyticAt_const)).mul hgammaR)

theorem conreyH_ne_zero_of_re_pos_of_ne_one {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    conreyH s ≠ 0 := by
  have hsne0 := ne_zero_of_re_pos hs0
  unfold conreyH
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) hsne0)
      (sub_ne_zero.mpr hs1))
    (Gammaℝ_ne_zero_of_re_pos hs0)

theorem conreyH_ne_zero_of_mem_criticalStrip {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    conreyH s ≠ 0 :=
  conreyH_ne_zero_of_re_pos_of_ne_one hs0 (ne_one_of_re_lt_one hs1)

theorem completedZeta_eq_conreyH_mul_riemannZeta_of_re_pos_of_ne_one {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    RiemannHypothesis.completedZeta s = conreyH s * riemannZeta s := by
  have hsne0 := ne_zero_of_re_pos hs0
  have hgamma := Gammaℝ_ne_zero_of_re_pos hs0
  rw [(completedZeta_eventuallyEq_factorization hsne0 hs1).self_of_nhds,
    riemannZeta_def_of_ne_zero hsne0]
  unfold conreyH
  field_simp [hgamma]

theorem completedZeta_eq_conreyH_mul_riemannZeta {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    RiemannHypothesis.completedZeta s = conreyH s * riemannZeta s :=
  completedZeta_eq_conreyH_mul_riemannZeta_of_re_pos_of_ne_one
    hs0 (ne_one_of_re_lt_one hs1)

private theorem completedZeta_eventuallyEq_conreyH_mul_riemannZeta_of_re_pos_of_ne_one
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    RiemannHypothesis.completedZeta =ᶠ[nhds s]
      fun z => conreyH z * riemannZeta z := by
  let U : Set ℂ := {z | 0 < z.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const continuous_re
  filter_upwards [hUopen.mem_nhds hs0, eventually_ne_nhds hs1] with z hz0 hz1
  exact completedZeta_eq_conreyH_mul_riemannZeta_of_re_pos_of_ne_one hz0 hz1

private theorem deriv_completedZeta_eq_conreyH_mul_riemannZeta_of_re_pos_of_ne_one
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    deriv RiemannHypothesis.completedZeta s =
      deriv conreyH s * riemannZeta s +
        conreyH s * deriv riemannZeta s := by
  have hH := analyticAt_conreyH_of_re_pos hs0
  have hzeta := ZeroFreeRegion.analyticOnNhd_riemannZeta_ne_one s
    hs1
  calc
    deriv RiemannHypothesis.completedZeta s =
        deriv (fun z => conreyH z * riemannZeta z) s :=
      (completedZeta_eventuallyEq_conreyH_mul_riemannZeta_of_re_pos_of_ne_one
        hs0 hs1).deriv_eq
    _ = deriv conreyH s * riemannZeta s +
        conreyH s * deriv riemannZeta s := by
      rw [deriv_fun_mul hH.differentiableAt hzeta.differentiableAt]

theorem conreyDegreeOneEta_eq_conreyH_mul_conreyDegreeOneV1_of_re_pos_of_ne_one
    {g g0 g1 L : ℝ} {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    conreyDegreeOneEta g g0 g1 L s =
      conreyH s * conreyDegreeOneV1 g g0 g1 L s := by
  have hxi := completedZeta_eq_conreyH_mul_riemannZeta_of_re_pos_of_ne_one hs0 hs1
  have hxideriv :=
    deriv_completedZeta_eq_conreyH_mul_riemannZeta_of_re_pos_of_ne_one hs0 hs1
  have hHne := conreyH_ne_zero_of_re_pos_of_ne_one hs0 hs1
  unfold conreyDegreeOneEta conreyDegreeOneV1
  rw [hxi, hxideriv]
  field_simp [hHne]
  ring

theorem conreyDegreeOneEta_eq_conreyH_mul_conreyDegreeOneV1
    {g g0 g1 L : ℝ} {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    conreyDegreeOneEta g g0 g1 L s =
      conreyH s * conreyDegreeOneV1 g g0 g1 L s :=
  conreyDegreeOneEta_eq_conreyH_mul_conreyDegreeOneV1_of_re_pos_of_ne_one
    hs0 (ne_one_of_re_lt_one hs1)

theorem conreyDegreeOneEta_eq_zero_iff_conreyDegreeOneV1_eq_zero
    {g g0 g1 L : ℝ} {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    conreyDegreeOneEta g g0 g1 L s = 0 ↔
      conreyDegreeOneV1 g g0 g1 L s = 0 := by
  rw [conreyDegreeOneEta_eq_conreyH_mul_conreyDegreeOneV1 hs0 hs1,
    mul_eq_zero]
  exact or_iff_right (conreyH_ne_zero_of_mem_criticalStrip hs0 hs1)

theorem analyticAt_conreyDegreeOneV1_of_re_pos_of_ne_one
    {g g0 g1 L : ℝ} {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    AnalyticAt ℂ (conreyDegreeOneV1 g g0 g1 L) s := by
  have hH := analyticAt_conreyH_of_re_pos hs0
  have hHne := conreyH_ne_zero_of_re_pos_of_ne_one hs0 hs1
  have hzeta := ZeroFreeRegion.analyticOnNhd_riemannZeta_ne_one s
    hs1
  have hlogH : AnalyticAt ℂ (fun z => deriv conreyH z / conreyH z) s :=
    hH.deriv.div hH hHne
  exact (analyticAt_const.mul hzeta).add
    (analyticAt_const.mul (hzeta.deriv.add (hlogH.mul hzeta)))

private theorem conreyDegreeOneEta_eventuallyEq_conreyH_mul_conreyDegreeOneV1_of_re_pos_of_ne_one
    {g g0 g1 L : ℝ} {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    conreyDegreeOneEta g g0 g1 L =ᶠ[nhds s]
      fun z => conreyH z * conreyDegreeOneV1 g g0 g1 L z := by
  let U : Set ℂ := {z | 0 < z.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const continuous_re
  filter_upwards [hUopen.mem_nhds hs0, eventually_ne_nhds hs1] with z hz0 hz1
  exact conreyDegreeOneEta_eq_conreyH_mul_conreyDegreeOneV1_of_re_pos_of_ne_one
    hz0 hz1

theorem analyticOrderAt_conreyDegreeOneEta_eq_conreyDegreeOneV1_of_re_pos_of_ne_one
    {g g0 g1 L : ℝ} {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    analyticOrderAt (conreyDegreeOneEta g g0 g1 L) s =
      analyticOrderAt (conreyDegreeOneV1 g g0 g1 L) s := by
  have hH := analyticAt_conreyH_of_re_pos hs0
  have hHne := conreyH_ne_zero_of_re_pos_of_ne_one hs0 hs1
  have hV := analyticAt_conreyDegreeOneV1_of_re_pos_of_ne_one
    (g := g) (g0 := g0) (g1 := g1) (L := L) hs0 hs1
  rw [analyticOrderAt_congr
      (conreyDegreeOneEta_eventuallyEq_conreyH_mul_conreyDegreeOneV1_of_re_pos_of_ne_one
        hs0 hs1)]
  change analyticOrderAt
      (conreyH * conreyDegreeOneV1 g g0 g1 L) s = _
  rw [analyticOrderAt_mul hH hV,
    hH.analyticOrderAt_eq_zero.mpr hHne, zero_add]

theorem analyticOrderNatAt_conreyDegreeOneEta_eq_conreyDegreeOneV1
    {g g0 g1 L : ℝ} {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    analyticOrderNatAt (conreyDegreeOneEta g g0 g1 L) s =
      analyticOrderNatAt (conreyDegreeOneV1 g g0 g1 L) s := by
  unfold analyticOrderNatAt
  rw [analyticOrderAt_conreyDegreeOneEta_eq_conreyDegreeOneV1_of_re_pos_of_ne_one
    hs0 (ne_one_of_re_lt_one hs1)]

end HardyTheorem
