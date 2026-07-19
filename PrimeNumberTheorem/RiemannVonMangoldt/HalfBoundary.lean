import PrimeNumberTheorem.RiemannVonMangoldt.RectangleCount
import PrimeNumberTheorem.RiemannVonMangoldt.CompletedZetaSymmetry
import PrimeNumberTheorem.RiemannVonMangoldt.ZetaArgumentBound

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Interval ComplexConjugate

namespace PrimeNumberTheorem
namespace RiemannVonMangoldt

private noncomputable def completedZetaHalfBoundaryPhaseAt
    (right U T : ℝ) : ℝ :=
  (∫ sigma in (1 / 2 : ℝ)..right,
      logDeriv RiemannHypothesis.completedZeta
        ((sigma : ℂ) + (U : ℂ) * I)).im -
    (∫ sigma in (1 / 2 : ℝ)..right,
      logDeriv RiemannHypothesis.completedZeta
        ((sigma : ℂ) + (T : ℂ) * I)).im +
      (∫ t in U..T,
        logDeriv RiemannHypothesis.completedZeta
          ((right : ℂ) + (t : ℂ) * I)).re

/-- The completed-zeta phase on the half boundary from the critical line to
the absolutely convergent line `Re(s)=2`. -/
noncomputable def completedZetaHalfBoundaryPhase (U T : ℝ) : ℝ :=
  completedZetaHalfBoundaryPhaseAt 2 U T

private theorem completedZeta_ne_zero_on_good_horizontal
    {T sigma : ℝ} (hT : 0 < T)
    (hgood : ExplicitFormulaAux.goodHeight T)
    (hsigma : sigma ∈ Set.Icc (0 : ℝ) 1) :
    RiemannHypothesis.completedZeta ((sigma : ℂ) + (T : ℂ) * I) ≠ 0 := by
  have hzeta : riemannZeta ((sigma : ℂ) + (T : ℂ) * I) ≠ 0 :=
    by simpa [mul_comm] using
      (ExplicitFormulaResidues.riemannZeta_ne_zero_on_goodHeight_horizontal
        (σ := sigma) hT (abs_of_pos hT) hgood)
  by_cases hs0 : sigma = 0
  · apply completedZeta_ne_zero_of_re_eq_zero_of_im_ne_zero
    · simp [hs0]
    · simp [hT.ne']
  by_cases hs1 : sigma = 1
  · apply completedZeta_ne_zero_of_re_eq_one_of_im_ne_zero
    · simp [hs1]
    · simp [hT.ne']
  apply (completedZeta_eq_zero_iff_riemannZeta_eq_zero_of_mem_criticalStrip
    (by simpa using lt_of_le_of_ne hsigma.1 (Ne.symm hs0))
    (by simpa using lt_of_le_of_ne hsigma.2 hs1)).not.mpr
  exact hzeta

private theorem completedZeta_ne_zero_of_one_le_re_of_im_ne_zero
    {s : ℂ} (hre : 1 ≤ s.re) (him : s.im ≠ 0) :
    RiemannHypothesis.completedZeta s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    apply him
    simpa using congrArg Complex.im h
  have hs1 : s ≠ 1 := by
    intro h
    apply him
    simpa using congrArg Complex.im h
  have hzeta : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re hre
  have hcompleted : completedRiemannZeta s ≠ 0 := by
    intro h
    apply hzeta
    rw [riemannZeta_def_of_ne_zero hs0, h]
    simp
  rw [(completedZeta_eventuallyEq_factorization hs0 hs1).self_of_nhds]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) hs0) (sub_ne_zero.mpr hs1))
    hcompleted

private theorem analyticAt_logDeriv_completedZeta_of_ne_zero
    {s : ℂ} (hs : RiemannHypothesis.completedZeta s ≠ 0) :
    AnalyticAt ℂ (logDeriv RiemannHypothesis.completedZeta) s :=
  ZeroFreeRegion.analyticAt_logDeriv_of_analyticAt_ne_zero
    (differentiable_completedZeta.analyticAt s) hs

private theorem horizontal_intervalIntegrable_criticalStrip
    {T a b : ℝ} (hT : 0 < T)
    (hgood : ExplicitFormulaAux.goodHeight T)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    IntervalIntegrable
      (fun sigma : ℝ => logDeriv RiemannHypothesis.completedZeta
        ((sigma : ℂ) + (T : ℂ) * I)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro sigma hsigma
  rw [Set.uIcc_of_le hab] at hsigma
  have hzero := completedZeta_ne_zero_on_good_horizontal hT hgood
    ⟨ha.trans hsigma.1, hsigma.2.trans hb⟩
  have hmap : ContinuousAt
      (fun r : ℝ => ((r : ℂ) + (T : ℂ) * I)) sigma := by fun_prop
  exact ((analyticAt_logDeriv_completedZeta_of_ne_zero hzero).continuousAt.comp_of_eq
    hmap rfl).continuousWithinAt

private theorem vertical_intervalIntegrable_one
    {U T : ℝ} (hU : 0 < U) (hUT : U ≤ T) :
    IntervalIntegrable
      (fun t : ℝ => logDeriv RiemannHypothesis.completedZeta
        ((1 : ℂ) + (t : ℂ) * I)) volume U T := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  rw [Set.uIcc_of_le hUT] at ht
  have ht0 : t ≠ 0 := ne_of_gt (hU.trans_le ht.1)
  have hzero := completedZeta_ne_zero_of_one_le_re_of_im_ne_zero
    (s := (1 : ℂ) + (t : ℂ) * I) (by simp) (by simpa using ht0)
  have hmap : ContinuousAt
      (fun r : ℝ => ((1 : ℂ) + (r : ℂ) * I)) t := by fun_prop
  exact ((analyticAt_logDeriv_completedZeta_of_ne_zero hzero).continuousAt.comp_of_eq
    hmap rfl).continuousWithinAt

private theorem horizontal_integral_fold
    {T : ℝ} (hT : 0 < T)
    (hgood : ExplicitFormulaAux.goodHeight T) :
    (∫ sigma in (0 : ℝ)..1,
      logDeriv RiemannHypothesis.completedZeta
        ((sigma : ℂ) + (T : ℂ) * I)) =
      2 * I * ((∫ sigma in (1 / 2 : ℝ)..1,
        logDeriv RiemannHypothesis.completedZeta
          ((sigma : ℂ) + (T : ℂ) * I)).im : ℂ) := by
  let F : ℝ → ℂ := fun sigma =>
    logDeriv RiemannHypothesis.completedZeta
      ((sigma : ℂ) + (T : ℂ) * I)
  have hleftInt : IntervalIntegrable F volume 0 (1 / 2 : ℝ) :=
    horizontal_intervalIntegrable_criticalStrip hT hgood
      (by norm_num) (by norm_num) (by norm_num)
  have hrightInt : IntervalIntegrable F volume (1 / 2 : ℝ) 1 :=
    horizontal_intervalIntegrable_criticalStrip hT hgood
      (by norm_num) (by norm_num) (by norm_num)
  have hleft : (∫ sigma in (0 : ℝ)..(1 / 2 : ℝ), F sigma) =
      -conj (∫ sigma in (1 / 2 : ℝ)..1, F sigma) := by
    calc
      (∫ sigma in (0 : ℝ)..(1 / 2 : ℝ), F sigma) =
          ∫ sigma in (1 / 2 : ℝ)..1, F (1 - sigma) := by
        have hsub := intervalIntegral.integral_comp_sub_left F 1
          (a := (1 / 2 : ℝ)) (b := 1)
        convert hsub.symm using 1 <;> norm_num
      _ = ∫ sigma in (1 / 2 : ℝ)..1, -conj (F sigma) := by
        apply intervalIntegral.integral_congr
        intro sigma _hsigma
        dsimp [F]
        have hsym := logDeriv_completedZeta_one_sub_conj
          ((sigma : ℂ) + (T : ℂ) * I)
        convert hsym using 1 <;> simp [map_add, map_mul] <;> ring
      _ = -conj (∫ sigma in (1 / 2 : ℝ)..1, F sigma) := by
        rw [intervalIntegral.integral_neg]
        congr 1
        exact Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm
          hrightInt
  rw [← intervalIntegral.integral_add_adjacent_intervals hleftInt hrightInt,
    hleft]
  calc
    -conj (∫ sigma in (1 / 2 : ℝ)..1, F sigma) +
          ∫ sigma in (1 / 2 : ℝ)..1, F sigma =
        (∫ sigma in (1 / 2 : ℝ)..1, F sigma) -
          conj (∫ sigma in (1 / 2 : ℝ)..1, F sigma) := by ring
    _ = (2 * ((∫ sigma in (1 / 2 : ℝ)..1, F sigma).im : ℂ)) * I := by
      convert Complex.sub_conj (∫ sigma in (1 / 2 : ℝ)..1, F sigma) using 1 <;>
        push_cast <;> ring
    _ = 2 * I * ((∫ sigma in (1 / 2 : ℝ)..1,
        logDeriv RiemannHypothesis.completedZeta
          ((sigma : ℂ) + (T : ℂ) * I)).im : ℂ) := by
      simp [F]
      ring

private theorem vertical_integral_fold
    {U T : ℝ} (hU : 0 < U) (hUT : U ≤ T) :
    (∫ t in U..T, logDeriv RiemannHypothesis.completedZeta ((t : ℂ) * I)) =
      -conj (∫ t in U..T,
        logDeriv RiemannHypothesis.completedZeta ((1 : ℂ) + (t : ℂ) * I)) := by
  let F : ℝ → ℂ := fun t =>
    logDeriv RiemannHypothesis.completedZeta ((1 : ℂ) + (t : ℂ) * I)
  have hrightInt : IntervalIntegrable F volume U T :=
    vertical_intervalIntegrable_one hU hUT
  calc
    (∫ t in U..T, logDeriv RiemannHypothesis.completedZeta ((t : ℂ) * I)) =
        ∫ t in U..T, -conj (F t) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      dsimp [F]
      have hsym := logDeriv_completedZeta_one_sub_conj
        ((1 : ℂ) + (t : ℂ) * I)
      convert hsym using 1 <;> simp [map_add, map_mul] <;> ring
    _ = -conj (∫ t in U..T, F t) := by
      rw [intervalIntegral.integral_neg]
      congr 1
      exact Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm
        hrightInt

private theorem boundaryRectIntegral_completedZeta_im_eq_two_mul_halfPhase_one
    {U T : ℝ} (hU : 0 < U) (hUT : U ≤ T)
    (hUgood : ExplicitFormulaAux.goodHeight U)
    (hTgood : ExplicitFormulaAux.goodHeight T) :
    (MathlibAux.boundaryRectIntegral
      (logDeriv RiemannHypothesis.completedZeta) 0 1 U T).im =
        2 * completedZetaHalfBoundaryPhaseAt 1 U T := by
  have hbottom := horizontal_integral_fold hU hUgood
  have htop := horizontal_integral_fold (hU.trans_le hUT) hTgood
  have hleft := vertical_integral_fold hU hUT
  simp only [MathlibAux.boundaryRectIntegral, smul_eq_mul]
  simp only [Complex.ofReal_zero, zero_add]
  rw [hbottom, htop, hleft]
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, add_zero,
    sub_zero, Complex.neg_im, Complex.conj_im, neg_neg, Complex.conj_re]
  simp [completedZetaHalfBoundaryPhaseAt]
  ring

private theorem pi_mul_zeroCount_sub_eq_halfPhase_one
    {U T : ℝ} (hU : 0 < U) (hUT : U < T)
    (hUgood : ExplicitFormulaAux.goodHeight U)
    (hTgood : ExplicitFormulaAux.goodHeight T) :
    Real.pi * ((riemannZeroCount T - riemannZeroCount U : ℕ) : ℝ) =
      completedZetaHalfBoundaryPhaseAt 1 U T := by
  have hcount := boundaryRectIntegral_logDeriv_completedZeta_eq_zeroCount_sub
    hU hUT hUgood hTgood
  have him := congrArg Complex.im hcount
  rw [boundaryRectIntegral_completedZeta_im_eq_two_mul_halfPhase_one
    hU hUT.le hUgood hTgood] at him
  norm_num at him ⊢
  linarith

private theorem logDeriv_completedZeta_differentiableOn_right_rectangle
    {U T : ℝ} (hU : 0 < U) (hUT : U ≤ T) :
    DifferentiableOn ℂ (logDeriv RiemannHypothesis.completedZeta)
      ([[(1 : ℝ), 2]] ×ℂ [[U, T]]) := by
  intro s hs
  rw [Complex.mem_reProdIm, Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2),
    Set.uIcc_of_le hUT] at hs
  have him : s.im ≠ 0 := ne_of_gt (hU.trans_le hs.2.1)
  exact (analyticAt_logDeriv_completedZeta_of_ne_zero
    (completedZeta_ne_zero_of_one_le_re_of_im_ne_zero hs.1.1 him)).differentiableAt.differentiableWithinAt

private theorem horizontal_intervalIntegrable_right
    {t a b : ℝ} (ht : 0 < t)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable
      (fun sigma : ℝ => logDeriv RiemannHypothesis.completedZeta
        ((sigma : ℂ) + (t : ℂ) * I)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro sigma hsigma
  rw [Set.uIcc_of_le hab] at hsigma
  have hzero := completedZeta_ne_zero_of_one_le_re_of_im_ne_zero
    (s := (sigma : ℂ) + (t : ℂ) * I) (by simpa using ha.trans hsigma.1)
      (by simpa using ht.ne')
  have hmap : ContinuousAt
      (fun r : ℝ => ((r : ℂ) + (t : ℂ) * I)) sigma := by fun_prop
  exact ((analyticAt_logDeriv_completedZeta_of_ne_zero hzero).continuousAt.comp_of_eq
    hmap rfl).continuousWithinAt

private theorem halfPhase_one_eq_halfPhase_two
    {U T : ℝ} (hU : 0 < U) (hUT : U ≤ T)
    (hUgood : ExplicitFormulaAux.goodHeight U)
    (hTgood : ExplicitFormulaAux.goodHeight T) :
    completedZetaHalfBoundaryPhaseAt 1 U T =
      completedZetaHalfBoundaryPhaseAt 2 U T := by
  have hzero := MathlibAux.boundaryRectIntegral_eq_zero_of_differentiableOn
    (logDeriv RiemannHypothesis.completedZeta) 1 2 U T
      (logDeriv_completedZeta_differentiableOn_right_rectangle hU hUT)
  have him := congrArg Complex.im hzero
  have hUleft : IntervalIntegrable
      (fun sigma : ℝ => logDeriv RiemannHypothesis.completedZeta
        ((sigma : ℂ) + (U : ℂ) * I)) volume (1 / 2 : ℝ) 1 :=
    horizontal_intervalIntegrable_criticalStrip hU
    hUgood
    (by norm_num) (by norm_num) (by norm_num)
  have hTleft : IntervalIntegrable
      (fun sigma : ℝ => logDeriv RiemannHypothesis.completedZeta
        ((sigma : ℂ) + (T : ℂ) * I)) volume (1 / 2 : ℝ) 1 :=
    horizontal_intervalIntegrable_criticalStrip (hU.trans_le hUT)
    hTgood
    (by norm_num) (by norm_num) (by norm_num)
  have hUright : IntervalIntegrable
      (fun sigma : ℝ => logDeriv RiemannHypothesis.completedZeta
        ((sigma : ℂ) + (U : ℂ) * I)) volume 1 2 :=
    horizontal_intervalIntegrable_right hU
    (by norm_num) (by norm_num : (1 : ℝ) ≤ 2)
  have hTright : IntervalIntegrable
      (fun sigma : ℝ => logDeriv RiemannHypothesis.completedZeta
        ((sigma : ℂ) + (T : ℂ) * I)) volume 1 2 :=
    horizontal_intervalIntegrable_right (hU.trans_le hUT)
    (by norm_num) (by norm_num : (1 : ℝ) ≤ 2)
  have hUjoin := intervalIntegral.integral_add_adjacent_intervals hUleft hUright
  have hTjoin := intervalIntegral.integral_add_adjacent_intervals hTleft hTright
  simp only [MathlibAux.boundaryRectIntegral, smul_eq_mul] at him
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, add_zero, sub_zero, Complex.zero_im] at him
  simp only [completedZetaHalfBoundaryPhaseAt]
  rw [← hUjoin, ← hTjoin]
  simp only [Complex.add_im, Complex.sub_im] at *
  linarith

/-- The argument principle count equals the completed-zeta half-boundary phase
with the right edge moved to `Re(s)=2`. -/
theorem pi_mul_zeroCount_sub_eq_completedZetaHalfBoundaryPhase
    {U T : ℝ} (hU : 4 ≤ U) (hUT : U < T)
    (hUgood : ExplicitFormulaAux.goodHeight U)
    (hTgood : ExplicitFormulaAux.goodHeight T) :
    Real.pi * ((riemannZeroCount T - riemannZeroCount U : ℕ) : ℝ) =
      completedZetaHalfBoundaryPhase U T := by
  rw [completedZetaHalfBoundaryPhase,
    ← halfPhase_one_eq_halfPhase_two (by linarith) hUT.le hUgood hTgood]
  exact pi_mul_zeroCount_sub_eq_halfPhase_one (by linarith) hUT hUgood hTgood

end RiemannVonMangoldt
end PrimeNumberTheorem
