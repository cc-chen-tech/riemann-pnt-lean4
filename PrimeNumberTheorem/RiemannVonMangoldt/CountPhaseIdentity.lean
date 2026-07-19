import PrimeNumberTheorem.RiemannVonMangoldt.RightVerticalZetaArgument
import PrimeNumberTheorem.RiemannVonMangoldt.GammaDecomposition
import PrimeNumberTheorem.RiemannVonMangoldt.GammaMainTerm

open Complex MeasureTheory Set Topology
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace RiemannVonMangoldt

private noncomputable def archimedeanLogDeriv (s : ℂ) : ℂ :=
  1 / s + 1 / (s - 1) - Complex.log Real.pi / 2 +
    Complex.digamma (s / 2) / 2

private theorem logDeriv_completedZeta_eq_archimedean_add_zeta
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hzeta : riemannZeta s ≠ 0) :
    logDeriv RiemannHypothesis.completedZeta s =
      archimedeanLogDeriv s + logDeriv riemannZeta s := by
  rw [logDeriv_completedZeta_eq_zeta_add_gamma hs0 hs1 hzeta]
  rfl

private theorem analyticAt_Gamma_of_pos_re {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ Complex.Gamma z := by
  rw [analyticAt_iff_eventually_differentiableAt]
  have hopen : IsOpen {w : ℂ | 0 < w.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hz] with w hw
  apply Complex.differentiableAt_Gamma
  intro m hzero
  have hre := congrArg Complex.re hzero
  simp at hre
  linarith

private theorem analyticAt_digamma_of_pos_re {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ Complex.digamma z := by
  have hGamma := analyticAt_Gamma_of_pos_re hz
  rw [Complex.digamma_def]
  exact hGamma.deriv.div hGamma (Complex.Gamma_ne_zero_of_re_pos hz)

private theorem differentiableAt_archimedeanLogDeriv
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hre : 0 < s.re) :
    DifferentiableAt ℂ archimedeanLogDeriv s := by
  have hhalfRe : (s / 2).re = s.re / 2 := by simp
  have hhalf : 0 < (s / 2).re := by linarith
  have hdig : DifferentiableAt ℂ (fun z : ℂ => Complex.digamma (z / 2)) s :=
    (analyticAt_digamma_of_pos_re hhalf).differentiableAt.comp s
      (differentiableAt_id.div_const 2)
  have hfirst : DifferentiableAt ℂ (fun z : ℂ => 1 / z) s :=
    (differentiableAt_const (c := (1 : ℂ))).div differentiableAt_id hs0
  have hsecond : DifferentiableAt ℂ (fun z : ℂ => 1 / (z - 1)) s :=
    (differentiableAt_const (c := (1 : ℂ))).div (differentiableAt_id.sub_const 1)
      (sub_ne_zero.mpr hs1)
  unfold archimedeanLogDeriv
  exact ((hfirst.add hsecond).sub
    (differentiableAt_const (c := Complex.log Real.pi / 2))).add
      (hdig.div_const 2)

private theorem differentiableOn_archimedeanLogDeriv_rectangle
    {U T : ℝ} (hU : 0 < U) (hUT : U ≤ T) :
    DifferentiableOn ℂ archimedeanLogDeriv
      ([[(1 / 2 : ℝ), 2]] ×ℂ [[U, T]]) := by
  intro s hs
  rw [Complex.mem_reProdIm,
    Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2),
    Set.uIcc_of_le hUT] at hs
  have him : s.im ≠ 0 := ne_of_gt (hU.trans_le hs.2.1)
  have hs0 : s ≠ 0 := by
    intro h
    apply him
    simpa using congrArg Complex.im h
  have hs1 : s ≠ 1 := by
    intro h
    apply him
    simpa using congrArg Complex.im h
  exact (differentiableAt_archimedeanLogDeriv hs0 hs1 (by linarith [hs.1.1])).differentiableWithinAt

private theorem archimedeanLogDeriv_criticalLine_re
    {t : ℝ} (ht : t ≠ 0) :
    (archimedeanLogDeriv ((1 / 2 : ℂ) + (t : ℂ) * I)).re =
      HardyTheorem.verticalGammaPhaseVelocity t := by
  have helem :
      (1 / ((1 / 2 : ℂ) + (t : ℂ) * I) +
        1 / (((1 / 2 : ℂ) + (t : ℂ) * I) - 1)).re = 0 := by
    have htSq : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
    norm_num [Complex.div_re, Complex.normSq_apply]
    field_simp [htSq]
    ring
  rw [show archimedeanLogDeriv ((1 / 2 : ℂ) + (t : ℂ) * I) =
      (1 / ((1 / 2 : ℂ) + (t : ℂ) * I) +
        1 / (((1 / 2 : ℂ) + (t : ℂ) * I) - 1)) +
      (-Complex.log Real.pi / 2 +
        Complex.digamma (((1 / 2 : ℂ) + (t : ℂ) * I) / 2) / 2) by
    simp only [archimedeanLogDeriv]
    ring]
  rw [Complex.add_re, helem, zero_add]
  have harg : (((1 / 2 : ℂ) + (t : ℂ) * I) / 2) =
      (1 / 4 : ℂ) + I * t / 2 := by
    apply Complex.ext <;> norm_num
  rw [harg]
  simp [HardyTheorem.verticalGammaPhaseVelocity, Complex.log_re,
    Complex.norm_real, abs_of_pos Real.pi_pos]
  ring

private theorem continuous_verticalGammaPhaseVelocity :
    Continuous HardyTheorem.verticalGammaPhaseVelocity := by
  rw [continuous_iff_continuousAt]
  intro t
  let z : ℝ → ℂ := fun x => (1 / 4 : ℂ) + I * x / 2
  have hzre : 0 < (z t).re := by
    dsimp [z]
    norm_num
  have hzcont : ContinuousAt z t := by
    dsimp [z]
    fun_prop
  have hdig := (analyticAt_digamma_of_pos_re hzre).continuousAt.comp hzcont
  change ContinuousAt
    (fun x : ℝ => (Complex.digamma (z x)).re / 2 - Real.log Real.pi / 2) t
  exact ((Complex.continuous_re.continuousAt.comp hdig).div_const 2).sub_const _

private theorem integral_verticalGammaPhaseVelocity_eq_phase_sub
    {U T : ℝ} (_hUT : U ≤ T) :
    (∫ t in U..T, HardyTheorem.verticalGammaPhaseVelocity t) =
      HardyTheorem.verticalGammaUnwrappedPhase T -
        HardyTheorem.verticalGammaUnwrappedPhase U := by
  have hleft := continuous_verticalGammaPhaseVelocity.intervalIntegrable
    (a := (1 : ℝ)) (b := U) (μ := volume)
  have hright := continuous_verticalGammaPhaseVelocity.intervalIntegrable
    (a := U) (b := T) (μ := volume)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
  rw [HardyTheorem.verticalGammaUnwrappedPhase,
    HardyTheorem.verticalGammaUnwrappedPhase, ← hadd]
  ring

private noncomputable def archimedeanHalfBoundaryPhase (U T : ℝ) : ℝ :=
  (∫ sigma in (1 / 2 : ℝ)..2,
      archimedeanLogDeriv ((sigma : ℂ) + (U : ℂ) * I)).im -
    (∫ sigma in (1 / 2 : ℝ)..2,
      archimedeanLogDeriv ((sigma : ℂ) + (T : ℂ) * I)).im +
      (∫ t in U..T,
        archimedeanLogDeriv ((2 : ℂ) + (t : ℂ) * I)).re

private theorem archimedeanHalfBoundaryPhase_eq_gammaPhase_sub
    {U T : ℝ} (hU : 0 < U) (hUT : U ≤ T) :
    archimedeanHalfBoundaryPhase U T =
      HardyTheorem.verticalGammaUnwrappedPhase T -
        HardyTheorem.verticalGammaUnwrappedPhase U := by
  have hzero := MathlibAux.boundaryRectIntegral_eq_zero_of_differentiableOn
    archimedeanLogDeriv (1 / 2 : ℝ) 2 U T
      (differentiableOn_archimedeanLogDeriv_rectangle hU hUT)
  have him := congrArg Complex.im hzero
  simp only [MathlibAux.boundaryRectIntegral, smul_eq_mul,
    Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, Complex.zero_im] at him
  have hleft :
      (∫ t in U..T,
        (archimedeanLogDeriv ((1 / 2 : ℂ) + (t : ℂ) * I)).re) =
        ∫ t in U..T, HardyTheorem.verticalGammaPhaseVelocity t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hUT] at ht
    exact archimedeanLogDeriv_criticalLine_re
      (ne_of_gt (hU.trans_le ht.1))
  have harchInt : IntervalIntegrable
      (fun t : ℝ => archimedeanLogDeriv
        ((1 / 2 : ℂ) + (t : ℂ) * I)) volume U T := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hUT] at ht
    have ht0 : t ≠ 0 := ne_of_gt (hU.trans_le ht.1)
    have hs0 : (1 / 2 : ℂ) + (t : ℂ) * I ≠ 0 := by
      intro hs
      apply ht0
      simpa using congrArg Complex.im hs
    have hs1 : (1 / 2 : ℂ) + (t : ℂ) * I ≠ 1 := by
      intro hs
      apply ht0
      simpa using congrArg Complex.im hs
    have hmap : ContinuousAt
        (fun r : ℝ => (1 / 2 : ℂ) + (r : ℂ) * I) t := by
      fun_prop
    exact ((differentiableAt_archimedeanLogDeriv hs0 hs1 (by norm_num)).continuousAt.comp_of_eq
      hmap rfl).continuousWithinAt
  have hleftMap := Complex.reCLM.intervalIntegral_comp_comm harchInt
  have hleftIntegral :
      (∫ t in U..T,
        archimedeanLogDeriv ((1 / 2 : ℂ) + (t : ℂ) * I)).re =
        ∫ t in U..T,
          (archimedeanLogDeriv ((1 / 2 : ℂ) + (t : ℂ) * I)).re := by
    simpa using hleftMap.symm
  norm_num at him
  rw [hleftIntegral, hleft,
    integral_verticalGammaPhaseVelocity_eq_phase_sub hUT] at him
  simp only [archimedeanHalfBoundaryPhase]
  linarith

private theorem intervalIntegrable_archimedean_horizontal
    {T : ℝ} (hT : 0 < T) : IntervalIntegrable
    (fun sigma : ℝ => archimedeanLogDeriv
      ((sigma : ℂ) + (T : ℂ) * I)) volume (1 / 2 : ℝ) 2 := by
  apply ContinuousOn.intervalIntegrable
  intro sigma hsigma
  rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hsigma
  let s : ℂ := (sigma : ℂ) + (T : ℂ) * I
  have him : s.im ≠ 0 := by simp [s, hT.ne']
  have hs0 : s ≠ 0 := by
    intro h
    exact him (by simpa using congrArg Complex.im h)
  have hs1 : s ≠ 1 := by
    intro h
    exact him (by simpa using congrArg Complex.im h)
  have hmap : ContinuousAt
      (fun r : ℝ => ((r : ℂ) + (T : ℂ) * I)) sigma := by fun_prop
  exact ((differentiableAt_archimedeanLogDeriv hs0 hs1
    (by simp [s]; linarith [hsigma.1])).continuousAt.comp_of_eq
      hmap rfl).continuousWithinAt

private theorem intervalIntegrable_zeta_horizontal
    {T : ℝ} (hT : 0 < T)
    (hgood : ExplicitFormulaAux.goodHeight T) : IntervalIntegrable
    (fun sigma : ℝ => logDeriv riemannZeta
      ((sigma : ℂ) + (T : ℂ) * I)) volume (1 / 2 : ℝ) 2 := by
  apply ContinuousOn.intervalIntegrable
  intro sigma _hsigma
  have hzeta : riemannZeta ((sigma : ℂ) + (T : ℂ) * I) ≠ 0 := by
    simpa [mul_comm] using
      (ExplicitFormulaResidues.riemannZeta_ne_zero_on_goodHeight_horizontal
        (σ := sigma) hT (abs_of_pos hT) hgood)
  have hs1 : (sigma : ℂ) + (T : ℂ) * I ≠ 1 := by
    intro hs
    have him := congrArg Complex.im hs
    simp at him
    linarith
  have hmap : ContinuousAt
      (fun r : ℝ => ((r : ℂ) + (T : ℂ) * I)) sigma := by fun_prop
  exact ((ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_of_ne_one_of_ne_zero
    _ hs1 hzeta).continuousAt.comp_of_eq hmap rfl).continuousWithinAt

private theorem intervalIntegrable_archimedean_right
    {U T : ℝ} (hU : 0 < U) (hUT : U ≤ T) : IntervalIntegrable
    (fun t : ℝ => archimedeanLogDeriv
      ((2 : ℂ) + (t : ℂ) * I)) volume U T := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  rw [Set.uIcc_of_le hUT] at ht
  have ht0 : t ≠ 0 := ne_of_gt (hU.trans_le ht.1)
  have hmap : ContinuousAt
      (fun r : ℝ => ((2 : ℂ) + (r : ℂ) * I)) t := by fun_prop
  exact ((differentiableAt_archimedeanLogDeriv
    (by intro hs; have := congrArg Complex.re hs; norm_num at this)
    (by intro hs; have := congrArg Complex.re hs; norm_num at this)
    (by norm_num)).continuousAt.comp_of_eq hmap rfl).continuousWithinAt

private theorem intervalIntegrable_zeta_right
    {U T : ℝ} (_hU : 0 < U) (_hUT : U ≤ T) : IntervalIntegrable
    (fun t : ℝ => logDeriv riemannZeta
      ((2 : ℂ) + (t : ℂ) * I)) volume U T := by
  apply ContinuousOn.intervalIntegrable
  intro t _ht
  have hs1 : (2 : ℂ) + (t : ℂ) * I ≠ 1 := by
    intro hs
    have := congrArg Complex.re hs
    norm_num at this
  have hzeta : riemannZeta ((2 : ℂ) + (t : ℂ) * I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by norm_num)
  have hmap : ContinuousAt
      (fun r : ℝ => ((2 : ℂ) + (r : ℂ) * I)) t := by fun_prop
  exact ((ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_of_ne_one_of_ne_zero
    _ hs1 hzeta).continuousAt.comp_of_eq hmap rfl).continuousWithinAt

private theorem horizontal_completed_eq_archimedean_add_zeta
    {T : ℝ} (hT : 0 < T)
    (hgood : ExplicitFormulaAux.goodHeight T) :
    (∫ sigma in (1 / 2 : ℝ)..2,
      logDeriv RiemannHypothesis.completedZeta
        ((sigma : ℂ) + (T : ℂ) * I)) =
      (∫ sigma in (1 / 2 : ℝ)..2,
        archimedeanLogDeriv ((sigma : ℂ) + (T : ℂ) * I)) +
      ∫ sigma in (1 / 2 : ℝ)..2,
        logDeriv riemannZeta ((sigma : ℂ) + (T : ℂ) * I) := by
  rw [← intervalIntegral.integral_add
    (intervalIntegrable_archimedean_horizontal hT)
    (intervalIntegrable_zeta_horizontal hT hgood)]
  apply intervalIntegral.integral_congr
  intro sigma _hsigma
  have hzeta : riemannZeta ((sigma : ℂ) + (T : ℂ) * I) ≠ 0 := by
    simpa [mul_comm] using
      (ExplicitFormulaResidues.riemannZeta_ne_zero_on_goodHeight_horizontal
        (σ := sigma) hT (abs_of_pos hT) hgood)
  apply logDeriv_completedZeta_eq_archimedean_add_zeta
  · intro hs
    have := congrArg Complex.im hs
    simp at this
    linarith
  · intro hs
    have := congrArg Complex.im hs
    simp at this
    linarith
  · exact hzeta

private theorem right_completed_eq_archimedean_add_zeta
    {U T : ℝ} (hU : 0 < U) (hUT : U ≤ T) :
    (∫ t in U..T, logDeriv RiemannHypothesis.completedZeta
      ((2 : ℂ) + (t : ℂ) * I)) =
      (∫ t in U..T,
        archimedeanLogDeriv ((2 : ℂ) + (t : ℂ) * I)) +
      ∫ t in U..T,
        logDeriv riemannZeta ((2 : ℂ) + (t : ℂ) * I) := by
  rw [← intervalIntegral.integral_add
    (intervalIntegrable_archimedean_right hU hUT)
    (intervalIntegrable_zeta_right hU hUT)]
  apply intervalIntegral.integral_congr
  intro t _ht
  apply logDeriv_completedZeta_eq_archimedean_add_zeta
  · intro hs
    have := congrArg Complex.re hs
    norm_num at this
  · intro hs
    have := congrArg Complex.re hs
    norm_num at this
  · exact riemannZeta_ne_zero_of_one_le_re (by norm_num)

/-- The zeta-only phase contribution on the upper, lower, and right edges of
the half counting rectangle. -/
noncomputable def zetaHalfPathArgument (U T : ℝ) : ℝ :=
  zetaHorizontalArgumentVariation U - zetaHorizontalArgumentVariation T +
    zetaRightVerticalArgumentVariation U T

private theorem completedZetaHalfBoundaryPhase_eq_archimedean_add_zeta
    {U T : ℝ} (hU : 0 < U) (hUT : U ≤ T)
    (hUgood : ExplicitFormulaAux.goodHeight U)
    (hTgood : ExplicitFormulaAux.goodHeight T) :
    completedZetaHalfBoundaryPhase U T =
      archimedeanHalfBoundaryPhase U T + zetaHalfPathArgument U T := by
  have hUedge := horizontal_completed_eq_archimedean_add_zeta hU hUgood
  have hTedge := horizontal_completed_eq_archimedean_add_zeta
    (hU.trans_le hUT) hTgood
  have hRedge := right_completed_eq_archimedean_add_zeta hU hUT
  have hUim := Complex.imCLM.intervalIntegral_comp_comm
    (intervalIntegrable_zeta_horizontal hU hUgood)
  have hTim := Complex.imCLM.intervalIntegral_comp_comm
    (intervalIntegrable_zeta_horizontal (hU.trans_le hUT) hTgood)
  have hRre := Complex.reCLM.intervalIntegral_comp_comm
    (intervalIntegrable_zeta_right hU hUT)
  rw [completedZetaHalfBoundaryPhase_apply, hUedge, hTedge, hRedge]
  simp only [Complex.add_im, Complex.add_re]
  simp only [archimedeanHalfBoundaryPhase, zetaHalfPathArgument,
    zetaHorizontalArgumentVariation, zetaRightVerticalArgumentVariation]
  have hUim' :
      (∫ sigma in (1 / 2 : ℝ)..2,
        logDeriv riemannZeta ((sigma : ℂ) + (U : ℂ) * I)).im =
      ∫ sigma in (1 / 2 : ℝ)..2,
        (logDeriv riemannZeta ((sigma : ℂ) + I * U)).im := by
    calc
      _ = ∫ sigma in (1 / 2 : ℝ)..2,
          (logDeriv riemannZeta
            ((sigma : ℂ) + (U : ℂ) * I)).im := by
        simpa using hUim.symm
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro sigma _
        simp [mul_comm]
  have hTim' :
      (∫ sigma in (1 / 2 : ℝ)..2,
        logDeriv riemannZeta ((sigma : ℂ) + (T : ℂ) * I)).im =
      ∫ sigma in (1 / 2 : ℝ)..2,
        (logDeriv riemannZeta ((sigma : ℂ) + I * T)).im := by
    calc
      _ = ∫ sigma in (1 / 2 : ℝ)..2,
          (logDeriv riemannZeta
            ((sigma : ℂ) + (T : ℂ) * I)).im := by
        simpa using hTim.symm
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro sigma _
        simp [mul_comm]
  have hRre' :
      (∫ t in U..T,
        logDeriv riemannZeta ((2 : ℂ) + (t : ℂ) * I)).re =
      ∫ t in U..T,
        (logDeriv riemannZeta ((2 : ℂ) + (t : ℂ) * I)).re := by
    simpa using hRre.symm
  rw [hUim', hTim', hRre']
  ring

/-- The exact good-height count identity: the zero-count increment is the sum
of the Gamma phase increment and a zeta-only half-boundary argument. -/
theorem riemannZeroCount_sub_eq_gammaPhase_add_zetaHalfPathArgument
    {U T : ℝ} (hU : 4 ≤ U) (hUT : U < T)
    (hUgood : ExplicitFormulaAux.goodHeight U)
    (hTgood : ExplicitFormulaAux.goodHeight T) :
    Real.pi * ((riemannZeroCount T - riemannZeroCount U : ℕ) : ℝ) =
      HardyTheorem.verticalGammaUnwrappedPhase T -
        HardyTheorem.verticalGammaUnwrappedPhase U +
      zetaHalfPathArgument U T := by
  calc
    _ = completedZetaHalfBoundaryPhase U T :=
      pi_mul_zeroCount_sub_eq_completedZetaHalfBoundaryPhase
        hU hUT hUgood hTgood
    _ = archimedeanHalfBoundaryPhase U T + zetaHalfPathArgument U T :=
      completedZetaHalfBoundaryPhase_eq_archimedean_add_zeta
        (by linarith) hUT.le hUgood hTgood
    _ = _ := by
      rw [archimedeanHalfBoundaryPhase_eq_gammaPhase_sub
        (by linarith) hUT.le]

/-- The zeta-only contribution in the exact count identity is logarithmic at
good heights. -/
theorem exists_abs_zetaHalfPathArgument_le_log :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U T : ℝ, 4 ≤ U → 4 ≤ T →
      ExplicitFormulaAux.goodHeight U →
      ExplicitFormulaAux.goodHeight T →
      |zetaHalfPathArgument U T| ≤
        C * (1 + Real.log (U + 5) + Real.log (T + 5)) := by
  rcases exists_abs_zetaHorizontalArgumentVariation_le_log with
    ⟨C0, hC0, hhorizontal⟩
  refine ⟨2 * C0 + Real.pi, by positivity, ?_⟩
  intro U T hU hT hUgood hTgood
  have hUhor := hhorizontal U hU hUgood
  have hThor := hhorizontal T hT hTgood
  have hright := abs_zetaRightVerticalArgumentVariation_le_pi U T
  have hlogU : 0 ≤ Real.log (U + 5) :=
    Real.log_nonneg (by linarith)
  have hlogT : 0 ≤ Real.log (T + 5) :=
    Real.log_nonneg (by linarith)
  rw [zetaHalfPathArgument]
  calc
    |zetaHorizontalArgumentVariation U -
          zetaHorizontalArgumentVariation T +
        zetaRightVerticalArgumentVariation U T| ≤
        |zetaHorizontalArgumentVariation U| +
          |zetaHorizontalArgumentVariation T| +
          |zetaRightVerticalArgumentVariation U T| := by
      calc
        _ ≤ |zetaHorizontalArgumentVariation U -
              zetaHorizontalArgumentVariation T| +
            |zetaRightVerticalArgumentVariation U T| := abs_add_le _ _
        _ ≤ (|zetaHorizontalArgumentVariation U| +
              |zetaHorizontalArgumentVariation T|) +
            |zetaRightVerticalArgumentVariation U T| := by
          gcongr
          exact abs_sub _ _
    _ ≤ C0 * (1 + Real.log (U + 5)) +
          C0 * (1 + Real.log (T + 5)) + Real.pi := by
      gcongr
    _ ≤ (2 * C0 + Real.pi) *
          (1 + Real.log (U + 5) + Real.log (T + 5)) := by
      nlinarith [Real.pi_pos.le]

end RiemannVonMangoldt
end PrimeNumberTheorem
