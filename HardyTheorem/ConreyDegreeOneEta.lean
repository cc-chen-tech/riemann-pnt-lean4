import PrimeNumberTheorem.RiemannVonMangoldt.CompletedZetaSymmetry

open Complex Filter
open scoped ComplexConjugate
open PrimeNumberTheorem.RiemannVonMangoldt

namespace HardyTheorem

/-!
# Conrey's degree-one eta function on the critical line

For the degree-one choice in Conrey's 1989 argument, the coefficient of
`xi` beyond the leading real coefficient is purely imaginary, while the
coefficient of `xi'` is real.  On the critical line `xi` is real and `xi'`
is purely imaginary.  Consequently `Re eta = g * xi`; if this real part
vanishes while `eta` itself does not, then `xi = 0` and `xi' != 0`, so the
corresponding zeta zero is simple.  This is the implication used in equation
(42) of the paper.
-/

/-- The point `1/2 + it` on the critical line. -/
noncomputable def conreyCriticalPoint (t : ℝ) : ℂ :=
  (1 / 2 : ℂ) + I * (t : ℂ)

@[simp] theorem conreyCriticalPoint_re (t : ℝ) :
    (conreyCriticalPoint t).re = 1 / 2 := by
  simp [conreyCriticalPoint]

@[simp] theorem conreyCriticalPoint_im (t : ℝ) :
    (conreyCriticalPoint t).im = t := by
  simp [conreyCriticalPoint]

private theorem one_sub_conreyCriticalPoint (t : ℝ) :
    1 - conreyCriticalPoint t = conj (conreyCriticalPoint t) := by
  apply Complex.ext
  · norm_num [conreyCriticalPoint]
  · simp [conreyCriticalPoint]

/-- Completed zeta is real-valued on the critical line. -/
theorem completedZeta_eq_conj_on_criticalLine (t : ℝ) :
    RiemannHypothesis.completedZeta (conreyCriticalPoint t) =
      conj (RiemannHypothesis.completedZeta (conreyCriticalPoint t)) := by
  calc
    RiemannHypothesis.completedZeta (conreyCriticalPoint t) =
        RiemannHypothesis.completedZeta (1 - conreyCriticalPoint t) :=
      RiemannHypothesis.functional_equation (conreyCriticalPoint t)
    _ = RiemannHypothesis.completedZeta (conj (conreyCriticalPoint t)) := by
      rw [one_sub_conreyCriticalPoint]
    _ = conj (RiemannHypothesis.completedZeta (conreyCriticalPoint t)) :=
      PrimeNumberTheorem.RiemannVonMangoldt.completedZeta_conj
        (conreyCriticalPoint t)

private theorem deriv_completedZeta_conj (s : ℂ) :
    deriv RiemannHypothesis.completedZeta (conj s) =
      conj (deriv RiemannHypothesis.completedZeta s) := by
  let xi := RiemannHypothesis.completedZeta
  have hfun : (conj ∘ xi ∘ conj) = xi := by
    funext z
    simpa [xi, Function.comp_def] using
      congrArg conj
        (PrimeNumberTheorem.RiemannVonMangoldt.completedZeta_conj z)
  have hder := congrArg deriv hfun
  rw [deriv_conj_conj] at hder
  have h := congrFun hder (conj s)
  simpa [xi, Function.comp_def] using h.symm

private theorem deriv_completedZeta_one_sub (s : ℂ) :
    deriv RiemannHypothesis.completedZeta (1 - s) =
      -deriv RiemannHypothesis.completedZeta s := by
  let xi := RiemannHypothesis.completedZeta
  have hfun : (fun z : ℂ => xi (1 - z)) = xi := by
    funext z
    exact (RiemannHypothesis.functional_equation z).symm
  have hleft : HasDerivAt (fun z : ℂ => xi (1 - z))
      (-deriv xi (1 - s)) s := by
    have hinner : HasDerivAt (fun z : ℂ => 1 - z) (-1) s := by
      convert (hasDerivAt_const s (1 : ℂ)).sub (hasDerivAt_id' s) using 1 <;>
        all_goals (first | rfl | ring)
    have houter : HasDerivAt xi (deriv xi (1 - s)) (1 - s) :=
      PrimeNumberTheorem.RiemannVonMangoldt.differentiable_completedZeta
        |>.differentiableAt.hasDerivAt
    convert houter.comp s hinner using 1 <;>
      all_goals (first | rfl | ring)
  have heq : deriv (fun z : ℂ => xi (1 - z)) s = deriv xi s := by
    rw [hfun]
  rw [hleft.deriv] at heq
  change -deriv xi (1 - s) = deriv xi s at heq
  change deriv xi (1 - s) = -deriv xi s
  linear_combination -heq

/-- The derivative of completed zeta is purely imaginary on the critical
line, written as the exact conjugation identity needed below. -/
theorem conj_deriv_completedZeta_eq_neg_on_criticalLine (t : ℝ) :
    conj (deriv RiemannHypothesis.completedZeta (conreyCriticalPoint t)) =
      -deriv RiemannHypothesis.completedZeta (conreyCriticalPoint t) := by
  calc
    conj (deriv RiemannHypothesis.completedZeta (conreyCriticalPoint t)) =
        deriv RiemannHypothesis.completedZeta
          (conj (conreyCriticalPoint t)) :=
      (deriv_completedZeta_conj (conreyCriticalPoint t)).symm
    _ = deriv RiemannHypothesis.completedZeta
          (1 - conreyCriticalPoint t) := by
      rw [one_sub_conreyCriticalPoint]
    _ = -deriv RiemannHypothesis.completedZeta (conreyCriticalPoint t) :=
      deriv_completedZeta_one_sub (conreyCriticalPoint t)

/-- Conrey's degree-one auxiliary function, with the parity conditions on
its coefficients built into the definition: `g` and `g1/L` are real and the
additional zeroth-order coefficient is `i*g0`. -/
noncomputable def conreyDegreeOneEta (g g0 g1 L : ℝ) (s : ℂ) : ℂ :=
  (g : ℂ) * RiemannHypothesis.completedZeta s +
    I * (g0 : ℂ) * RiemannHypothesis.completedZeta s +
    ((g1 / L : ℝ) : ℂ) * deriv RiemannHypothesis.completedZeta s

/-- Conrey's degree-one auxiliary function is analytic everywhere. -/
theorem analyticAt_conreyDegreeOneEta (g g0 g1 L : ℝ) (s : ℂ) :
    AnalyticAt ℂ (conreyDegreeOneEta g g0 g1 L) s := by
  have hxi : AnalyticAt ℂ RiemannHypothesis.completedZeta s :=
    differentiable_completedZeta.analyticAt s
  have hxideriv : AnalyticAt ℂ (deriv RiemannHypothesis.completedZeta) s :=
    hxi.deriv
  exact ((analyticAt_const.mul hxi).add
    ((analyticAt_const.mul analyticAt_const).mul hxi)).add
      (analyticAt_const.mul hxideriv)

/-- At a finite order-`m` zero on the critical line, the restriction of
Conrey's `eta` has the exact local form
`(I * (t - tau)) ^ m * h(1/2 + I*t)`, where the regular factor is analytic
and remains nonzero on a real neighborhood of `tau`. -/
theorem exists_conreyDegreeOneEta_vertical_order_factor
    {g g0 g1 L tau : ℝ} {m : ℕ}
    (horder :
      analyticOrderAt (conreyDegreeOneEta g g0 g1 L)
        (conreyCriticalPoint tau) = m) :
    ∃ h : ℂ → ℂ,
      AnalyticAt ℂ h (conreyCriticalPoint tau) ∧
      h (conreyCriticalPoint tau) ≠ 0 ∧
      (∀ᶠ t in nhds tau, h (conreyCriticalPoint t) ≠ 0) ∧
      (∀ᶠ t in nhds tau,
        conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t) =
          (I * ((t - tau : ℝ) : ℂ)) ^ m *
            h (conreyCriticalPoint t)) := by
  have heta := analyticAt_conreyDegreeOneEta g g0 g1 L
    (conreyCriticalPoint tau)
  rcases heta.analyticOrderAt_eq_natCast.mp horder with
    ⟨h, hhanalytic, hhne, hfactor⟩
  have hcriticalContinuous : Continuous conreyCriticalPoint := by
    unfold conreyCriticalPoint
    fun_prop
  have hcriticalTendsto :
      Tendsto conreyCriticalPoint (nhds tau)
        (nhds (conreyCriticalPoint tau)) :=
    hcriticalContinuous.continuousAt
  have hhneReal :
      ∀ᶠ t in nhds tau, h (conreyCriticalPoint t) ≠ 0 :=
    hcriticalTendsto.eventually
      (hhanalytic.continuousAt.eventually_ne hhne)
  have hfactorReal :
      ∀ᶠ t in nhds tau,
        conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t) =
          (I * ((t - tau : ℝ) : ℂ)) ^ m *
            h (conreyCriticalPoint t) := by
    filter_upwards [hcriticalTendsto.eventually hfactor] with t ht
    have hdisplacement :
        conreyCriticalPoint t - conreyCriticalPoint tau =
          I * ((t - tau : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [conreyCriticalPoint]
    simpa [hdisplacement] using ht
  exact ⟨h, hhanalytic, hhne, hhneReal, hfactorReal⟩

/-- On the critical line, the real part of Conrey's degree-one `eta` is
exactly the leading real coefficient times `xi`. -/
theorem conreyDegreeOneEta_re_on_criticalLine (g g0 g1 L t : ℝ) :
    (conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t)).re =
      g * (RiemannHypothesis.completedZeta (conreyCriticalPoint t)).re := by
  have hxiIm :
      (RiemannHypothesis.completedZeta (conreyCriticalPoint t)).im = 0 := by
    have h := congrArg Complex.im (completedZeta_eq_conj_on_criticalLine t)
    have hneg :
        (RiemannHypothesis.completedZeta (conreyCriticalPoint t)).im =
          -(RiemannHypothesis.completedZeta (conreyCriticalPoint t)).im := by
      simpa using h
    linarith
  have hderivRe :
      (deriv RiemannHypothesis.completedZeta (conreyCriticalPoint t)).re = 0 := by
    have h := congrArg Complex.re
      (conj_deriv_completedZeta_eq_neg_on_criticalLine t)
    have hneg :
        (deriv RiemannHypothesis.completedZeta
          (conreyCriticalPoint t)).re =
          -(deriv RiemannHypothesis.completedZeta
            (conreyCriticalPoint t)).re := by
      simpa using h
    linarith
  simp [conreyDegreeOneEta, Complex.mul_re, hxiIm, hderivRe]

/-- A nonzero degree-one `eta` crossing with zero real part gives a simple
zeta zero on the critical line.  This is Conrey's equation (42), separated
from the later argument-variation and mollified mean-square estimates. -/
theorem conreyDegreeOneEta_simple_zero_of_re_eq_zero_of_ne_zero
    {g g0 g1 L t : ℝ} (hg : g ≠ 0)
    (hre : (conreyDegreeOneEta g g0 g1 L
      (conreyCriticalPoint t)).re = 0)
    (hne : conreyDegreeOneEta g g0 g1 L
      (conreyCriticalPoint t) ≠ 0) :
    riemannZeta (conreyCriticalPoint t) = 0 ∧
      analyticOrderNatAt riemannZeta (conreyCriticalPoint t) = 1 := by
  let s := conreyCriticalPoint t
  have hxiRe : (RiemannHypothesis.completedZeta s).re = 0 := by
    rw [conreyDegreeOneEta_re_on_criticalLine] at hre
    exact (mul_eq_zero.mp hre).resolve_left hg
  have hxiIm : (RiemannHypothesis.completedZeta s).im = 0 := by
    have h := congrArg Complex.im (completedZeta_eq_conj_on_criticalLine t)
    have hneg :
        (RiemannHypothesis.completedZeta (conreyCriticalPoint t)).im =
          -(RiemannHypothesis.completedZeta (conreyCriticalPoint t)).im := by
      simpa using h
    change (RiemannHypothesis.completedZeta s).im = 0
    dsimp [s]
    linarith
  have hxi : RiemannHypothesis.completedZeta s = 0 := by
    apply Complex.ext <;> simp [hxiRe, hxiIm]
  have hderiv : deriv RiemannHypothesis.completedZeta s ≠ 0 := by
    intro hd
    apply hne
    simp [conreyDegreeOneEta, s, hxi, hd]
  have hsre : s.re = 1 / 2 := by simp [s]
  have hsrePos : 0 < s.re := by rw [hsre]; norm_num
  have hsreLt : s.re < 1 := by rw [hsre]; norm_num
  have hzeta : riemannZeta s = 0 :=
    (completedZeta_eq_zero_iff_riemannZeta_eq_zero_of_mem_criticalStrip
      hsrePos hsreLt).mp hxi
  have horderXi : analyticOrderNatAt RiemannHypothesis.completedZeta s = 1 := by
    have hanalytic : AnalyticAt ℂ RiemannHypothesis.completedZeta s :=
      differentiable_completedZeta.analyticAt s
    have horderRaw :
        analyticOrderAt RiemannHypothesis.completedZeta s = 1 :=
      hanalytic.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hxi hderiv
    unfold analyticOrderNatAt
    rw [horderRaw]
    rfl
  have horder : analyticOrderNatAt riemannZeta s = 1 := by
    rw [← analyticOrderNatAt_completedZeta_eq_riemannZeta_of_mem_criticalStrip
      hsrePos hsreLt]
    exact horderXi
  exact ⟨by simpa [s] using hzeta, by simpa [s] using horder⟩

end HardyTheorem
