import HardyTheorem.ConreyDegreeOneV1
import PrimeNumberTheorem.ExplicitFormulaAux

/-!
# Nontriviality and finite order of Conrey's degree-one factor

The leading coefficient condition `g != 0` prevents Conrey's entire auxiliary
function `eta` from vanishing identically.  We witness this at a positive good
height on the critical line: completed zeta is real and nonzero there, so the
real part of `eta` is the nonzero quantity `g * xi`.

This removes the formerly explicit finite-order hypothesis from the local
multiplicity form of equation (35).
-/

open Complex Set
open PrimeNumberTheorem.RiemannVonMangoldt

namespace HardyTheorem

/-- Conrey's degree-one auxiliary function is entire. -/
theorem analyticOnNhd_conreyDegreeOneEta (g g0 g1 L : ℝ) :
    AnalyticOnNhd ℂ (conreyDegreeOneEta g g0 g1 L) Set.univ := by
  intro s hs
  have hxi : AnalyticAt ℂ RiemannHypothesis.completedZeta s :=
    differentiable_completedZeta.analyticAt s
  unfold conreyDegreeOneEta
  exact ((analyticAt_const.mul hxi).add
    ((analyticAt_const.mul analyticAt_const).mul hxi)).add
      (analyticAt_const.mul hxi.deriv)

/-- If the leading real coefficient is nonzero, `eta` is nonzero somewhere.
The witness is a critical-line point at a positive good height. -/
theorem exists_conreyDegreeOneEta_ne_zero_of_g_ne_zero
    {g g0 g1 L : ℝ} (hg : g ≠ 0) :
    ∃ s : ℂ, conreyDegreeOneEta g g0 g1 L s ≠ 0 := by
  obtain ⟨T, hT2, hT3, hgood⟩ :=
    PrimeNumberTheorem.ExplicitFormulaAux.exists_goodHeight_Ioo 2
  have hTpos : 0 < T := by linarith
  have hs0 : 0 < (conreyCriticalPoint T).re := by
    rw [conreyCriticalPoint_re]
    norm_num
  have hs1 : (conreyCriticalPoint T).re < 1 := by
    rw [conreyCriticalPoint_re]
    norm_num
  have hzeta : riemannZeta (conreyCriticalPoint T) ≠ 0 := by
    intro hzero
    have hnontrivial :
        RiemannHypothesis.IsNontrivialZero (conreyCriticalPoint T) :=
      ⟨hzero, hs0, hs1⟩
    exact (hgood (conreyCriticalPoint T) hnontrivial) (by
      rw [conreyCriticalPoint_im, abs_of_pos hTpos])
  have hxi :
      RiemannHypothesis.completedZeta (conreyCriticalPoint T) ≠ 0 := by
    rw [completedZeta_eq_conreyH_mul_riemannZeta hs0 hs1]
    exact mul_ne_zero (conreyH_ne_zero_of_mem_criticalStrip hs0 hs1) hzeta
  have hxiIm :
      (RiemannHypothesis.completedZeta (conreyCriticalPoint T)).im = 0 := by
    have h := congrArg Complex.im (completedZeta_eq_conj_on_criticalLine T)
    have hneg :
        (RiemannHypothesis.completedZeta (conreyCriticalPoint T)).im =
          -(RiemannHypothesis.completedZeta (conreyCriticalPoint T)).im := by
      simpa using h
    linarith
  have hxiRe :
      (RiemannHypothesis.completedZeta (conreyCriticalPoint T)).re ≠ 0 := by
    intro hre
    apply hxi
    apply Complex.ext
    · simpa using hre
    · simpa using hxiIm
  refine ⟨conreyCriticalPoint T, ?_⟩
  intro heta
  have hetaRe :
      (conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint T)).re ≠ 0 := by
    rw [conreyDegreeOneEta_re_on_criticalLine]
    exact mul_ne_zero hg hxiRe
  exact hetaRe (by simpa using congrArg Complex.re heta)

/-- A nonzero leading coefficient makes every local analytic order of the
entire auxiliary function finite. -/
theorem analyticOrderAt_conreyDegreeOneEta_ne_top_of_g_ne_zero
    {g g0 g1 L : ℝ} (hg : g ≠ 0) (s : ℂ) :
    analyticOrderAt (conreyDegreeOneEta g g0 g1 L) s ≠ ⊤ := by
  have hanalytic := analyticOnNhd_conreyDegreeOneEta g g0 g1 L
  obtain ⟨z, hz⟩ := exists_conreyDegreeOneEta_ne_zero_of_g_ne_zero
    (g0 := g0) (g1 := g1) (L := L) hg
  have hzorder :
      analyticOrderAt (conreyDegreeOneEta g g0 g1 L) z ≠ ⊤ := by
    rw [(hanalytic z (by simp)).analyticOrderAt_eq_zero.mpr hz]
    exact ENat.natCast_ne_top 0
  exact hanalytic.analyticOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (by simp) (by simp) hzorder

/-- On the analytic half-plane of `V1`, nontriviality of `eta` transfers
through the nonvanishing archimedean factor `H`. -/
theorem analyticOrderAt_conreyDegreeOneV1_ne_top_of_g_ne_zero
    {g g0 g1 L : ℝ} (hg : g ≠ 0) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    analyticOrderAt (conreyDegreeOneV1 g g0 g1 L) s ≠ ⊤ := by
  rw [← analyticOrderAt_conreyDegreeOneEta_eq_conreyDegreeOneV1_of_re_pos_of_ne_one
    hs0 hs1]
  exact analyticOrderAt_conreyDegreeOneEta_ne_top_of_g_ne_zero hg s

end HardyTheorem
