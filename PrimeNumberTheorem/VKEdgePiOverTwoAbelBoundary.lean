import PrimeNumberTheorem.ExplicitFormulaResidues
import PrimeNumberTheorem.VKEdgePiOverTwoCarlson
import ZeroFreeRegion.MeromorphicAux

open Complex Filter Set Topology

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- Under a power-scale bound at `beta`, the Mellin model agrees with the
regularized logarithmic derivative throughout the upper part of the open
half-plane `Re s > beta`.

The upper-half-plane restriction removes the pole at `1` from the
continuation domain while retaining every positive-ordinate zeta zero used by
the Abel argument. -/
theorem regularizedNegLogDerivModel_eq_neg_logDeriv_sub_pole_of_power_error
    {beta : ℝ} (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (herror : PsiPowerErrorBound beta) {s : ℂ}
    (hbetaS : beta < s.re) (hSIm : 0 < s.im) :
    regularizedNegLogDerivModel s =
      -logDeriv riemannZeta s - s / (s - 1) := by
  let U : Set ℂ := {z : ℂ | beta < z.re} ∩ {z : ℂ | 0 < z.im}
  let Q : ℂ → ℂ := ZeroFreeRegion.riemannZetaPoleUnitAtOne
  let H : ℂ → ℂ := fun z => -(1 + logDeriv Q z)
  have hUOpen : IsOpen U := by
    exact
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt continuous_const Complex.continuous_im)
  have hUPreconnected : IsPreconnected U := by
    exact
      ((convex_halfSpace_re_gt beta).inter
        (convex_halfSpace_im_gt 0)).isPreconnected
  have hQ : AnalyticOnNhd ℂ Q U := by
    intro z hz
    exact
      ZeroFreeRegion.analyticOnNhd_riemannZetaPoleUnitAtOne_re_gt hbeta0
        z hz.1
  have hZetaNe : ∀ z ∈ U, riemannZeta z ≠ 0 := by
    intro z hz
    by_cases hz1 : z.re < 1
    · exact
        ZeroFreeRegion.psiPowerErrorBound_excludes_riemannZeta_zero_right
          hbeta0 hbeta1 herror z hz.1 hz1
    · exact riemannZeta_ne_zero_of_one_le_re (le_of_not_gt hz1)
  have hQNe : ∀ z ∈ U, Q z ≠ 0 := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      subst z
      simpa using hz.2
    have hz1 : z ≠ 1 := by
      intro h
      subst z
      simpa using hz.2
    rw [show Q z = ZeroFreeRegion.riemannZetaPoleUnitAtOne z by rfl,
      ZeroFreeRegion.riemannZetaPoleUnitAtOne_eq_sub_one_mul_riemannZeta
        hz0 hz1]
    exact mul_ne_zero (sub_ne_zero.mpr hz1) (hZetaNe z hz)
  have hModel : AnalyticOnNhd ℂ regularizedNegLogDerivModel U := by
    apply
      (differentiableOn_regularizedNegLogDerivModel_of_psi_power_error
        herror).mono ?_ |>.analyticOnNhd hUOpen
    intro z hz
    exact hz.1
  have hH : AnalyticOnNhd ℂ H U := by
    intro z hz
    have hlog : AnalyticAt ℂ (logDeriv Q) z :=
      (hQ z hz).deriv.div (hQ z hz) (hQNe z hz)
    exact (analyticAt_const.add hlog).neg
  let x : ℂ := (max beta 1 + 1 : ℝ) + I
  have hxU : x ∈ U := by
    change beta < x.re ∧ 0 < x.im
    constructor
    · simpa [x] using
        (show beta < max beta 1 + 1 by
          linarith [le_max_left beta 1])
    · simp [x]
  have hxOverlap : 1 < x.re := by
    simpa [x] using
      (show 1 < max beta 1 + 1 by
        linarith [le_max_right beta 1])
  have hLocal :
      regularizedNegLogDerivModel =ᶠ[𝓝 x] H := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hImOpen : IsOpen {z : ℂ | 0 < z.im} :=
      isOpen_lt continuous_const Complex.continuous_im
    filter_upwards [hopen.mem_nhds hxOverlap,
      hImOpen.mem_nhds hxU.2] with z hz hzIm
    have hzQ : Q z ≠ 0 := by
      apply hQNe z
      exact ⟨hbeta1.trans hz, hzIm⟩
    have hODE :=
      ZeroFreeRegion.deriv_riemannZetaPoleUnitAtOne_eq_mellin_coefficient_mul
        hz
    have hODE' :
        deriv Q z =
          -(1 + regularizedNegLogDerivModel z) * Q z := by
      simpa [Q, regularizedNegLogDerivModel] using hODE
    symm
    calc
      H z = -(1 + deriv Q z / Q z) := by
        simp only [H, logDeriv_apply]
      _ = -(1 + (-(1 + regularizedNegLogDerivModel z) * Q z) / Q z) := by
        rw [hODE']
      _ = regularizedNegLogDerivModel z := by
        field_simp [hzQ]
        ring
  have hEq : Set.EqOn regularizedNegLogDerivModel H U :=
    hModel.eqOn_of_preconnected_of_eventuallyEq
      hH hUPreconnected hxU hLocal
  have hsU : s ∈ U := ⟨hbetaS, hSIm⟩
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hSIm
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at hSIm
  have hunit :
      Q s = (s - 1) * riemannZeta s := by
    exact
      ZeroFreeRegion.riemannZetaPoleUnitAtOne_eq_sub_one_mul_riemannZeta
        hs0 hs1
  have hunitEventually :
      Q =ᶠ[𝓝 s] fun z : ℂ => (z - 1) * riemannZeta z := by
    filter_upwards [eventually_ne_nhds hs0, eventually_ne_nhds hs1]
      with z hz0 hz1
    exact
      ZeroFreeRegion.riemannZetaPoleUnitAtOne_eq_sub_one_mul_riemannZeta
        hz0 hz1
  have hleft : DifferentiableAt ℂ (fun z : ℂ => z - 1) s :=
    differentiableAt_id.sub (differentiableAt_const (1 : ℂ))
  have hright : DifferentiableAt ℂ riemannZeta s :=
    differentiableAt_riemannZeta hs1
  have hderiv :
      deriv Q s =
        riemannZeta s + (s - 1) * deriv riemannZeta s := by
    calc
      deriv Q s =
          deriv (fun z : ℂ => (z - 1) * riemannZeta z) s :=
        hunitEventually.deriv_eq
      _ = deriv (fun z : ℂ => z - 1) s * riemannZeta s +
          (s - 1) * deriv riemannZeta s := by
        simpa only [Pi.mul_apply] using deriv_mul hleft hright
      _ = riemannZeta s + (s - 1) * deriv riemannZeta s := by
        simp
  have hzeta : riemannZeta s ≠ 0 := hZetaNe s hsU
  rw [hEq hsU]
  simp only [H, logDeriv_apply]
  rw [hderiv, hunit]
  field_simp [hzeta, sub_ne_zero.mpr hs1]
  ring

/-- A positive real displacement approaches a complex point through its
punctured neighborhood. -/
private lemma tendsto_add_ofReal_nhdsGT_nhdsNE (rho : ℂ) :
    Tendsto (fun a : ℝ => rho + (a : ℂ)) (𝓝[>] 0) (𝓝[≠] rho) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hcont : ContinuousAt (fun a : ℝ => rho + (a : ℂ)) 0 := by
      fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with a ha
    have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
    have hne : rho + (a : ℂ) ≠ rho := by
      intro h
      apply ha0
      apply add_left_cancel (a := rho)
      simpa using h
    simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hne

/-- At a positive-ordinate zeta zero, the right-boundary Abel coefficient of
the regularized Mellin model is exactly minus the analytic multiplicity. -/
theorem tendsto_atRight_mul_regularizedNegLogDerivModel_of_zeta_zero
    {rho : ℂ} {n : ℕ}
    (hrhoRe0 : 0 ≤ rho.re) (hrhoRe1 : rho.re < 1)
    (hrhoIm : 0 < rho.im)
    (_hzero : riemannZeta rho = 0)
    (horder : analyticOrderAt riemannZeta rho = n)
    (herror : PsiPowerErrorBound rho.re) :
    Tendsto
      (fun a : ℝ =>
        (a : ℂ) * regularizedNegLogDerivModel (rho + (a : ℂ)))
      (𝓝[>] 0) (𝓝 (-(n : ℂ))) := by
  let p : ℝ → ℂ := fun a => rho + (a : ℂ)
  have hpath : Tendsto p (𝓝[>] 0) (𝓝[≠] rho) := by
    simpa [p] using tendsto_add_ofReal_nhdsGT_nhdsNE rho
  have hprincipal :=
    (ExplicitFormulaResidues.tendsto_sub_mul_neg_logDeriv_riemannZeta_of_order_eq_nat
        (by
          intro h
          subst rho
          norm_num at hrhoIm)
        horder).comp hpath
  have ha :
      Tendsto (fun a : ℝ => (a : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have hcont : ContinuousAt (fun a : ℝ => (a : ℂ)) 0 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hrho1 : rho ≠ 1 := by
    intro h
    subst rho
    norm_num at hrhoIm
  have hpoleCont :
      ContinuousAt (fun z : ℂ => -(z / (z - 1))) rho := by
    exact
      (continuousAt_id.div
        (continuousAt_id.sub continuousAt_const)
        (sub_ne_zero.mpr hrho1)).neg
  have hpole :
      Tendsto (fun a : ℝ => -(p a / (p a - 1)))
        (𝓝[>] 0) (𝓝 (-(rho / (rho - 1)))) :=
    hpoleCont.tendsto.comp
      (by
        have hcont : ContinuousAt p 0 := by fun_prop
        simpa [p] using hcont.tendsto.mono_left nhdsWithin_le_nhds)
  have hregular :
      Tendsto
        (fun a : ℝ => (a : ℂ) * (-(p a / (p a - 1))))
        (𝓝[>] 0) (𝓝 0) := by
    simpa using ha.mul hpole
  have hsum :
      Tendsto
        (fun a : ℝ =>
          (p a - rho) * (-logDeriv riemannZeta (p a)) +
            (a : ℂ) * (-(p a / (p a - 1))))
        (𝓝[>] 0) (𝓝 (-(n : ℂ))) := by
    simpa using hprincipal.add hregular
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with a haPos
  have haPos' : 0 < a := haPos
  have hEq :=
    regularizedNegLogDerivModel_eq_neg_logDeriv_sub_pole_of_power_error
      hrhoRe0 hrhoRe1 herror
      (s := p a)
      (by simp [p]; linarith)
      (by simpa [p] using hrhoIm)
  simp only [p] at hEq ⊢
  rw [hEq]
  have haCast :
      rho + (a : ℂ) - rho = (a : ℂ) := by ring
  rw [haCast]
  ring

/-- At a nonzero point on the same vertical boundary, the right-boundary
Abel coefficient of the regularized Mellin model vanishes. -/
theorem tendsto_atRight_mul_regularizedNegLogDerivModel_of_zeta_ne_zero
    {beta gamma : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (hgamma : 0 < gamma)
    (hzeta :
      riemannZeta ((beta : ℂ) + I * gamma) ≠ 0)
    (herror : PsiPowerErrorBound beta) :
    Tendsto
      (fun a : ℝ =>
        (a : ℂ) *
          regularizedNegLogDerivModel
            ((beta : ℂ) + I * gamma + (a : ℂ)))
      (𝓝[>] 0) (𝓝 0) := by
  let rho : ℂ := (beta : ℂ) + I * gamma
  let p : ℝ → ℂ := fun a => rho + (a : ℂ)
  have hrho1 : rho ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp [rho] at him
    linarith
  have hlog :
      AnalyticAt ℂ (logDeriv riemannZeta) rho :=
    (ZeroFreeRegion.analyticOnNhd_riemannZeta_ne_one rho hrho1).deriv.div
      (ZeroFreeRegion.analyticOnNhd_riemannZeta_ne_one rho hrho1) hzeta
  have hR :
      ContinuousAt
        (fun z : ℂ => -logDeriv riemannZeta z - z / (z - 1)) rho := by
    exact hlog.continuousAt.neg.sub
      (continuousAt_id.div
        (continuousAt_id.sub continuousAt_const)
        (sub_ne_zero.mpr hrho1))
  have hpath :
      Tendsto p (𝓝[>] 0) (𝓝 rho) := by
    have hcont : ContinuousAt p 0 := by fun_prop
    simpa [p] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hbounded :
      Tendsto
        (fun a : ℝ =>
          -logDeriv riemannZeta (p a) - p a / (p a - 1))
        (𝓝[>] 0)
        (𝓝 (-logDeriv riemannZeta rho - rho / (rho - 1))) :=
    hR.tendsto.comp hpath
  have ha :
      Tendsto (fun a : ℝ => (a : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have hcont : ContinuousAt (fun a : ℝ => (a : ℂ)) 0 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hproduct :
      Tendsto
        (fun a : ℝ =>
          (a : ℂ) *
            (-logDeriv riemannZeta (p a) - p a / (p a - 1)))
        (𝓝[>] 0) (𝓝 0) := by
    simpa using ha.mul hbounded
  apply hproduct.congr'
  filter_upwards [self_mem_nhdsWithin] with a haPos
  have haPos' : 0 < a := haPos
  have hEq :=
    regularizedNegLogDerivModel_eq_neg_logDeriv_sub_pole_of_power_error
      hbeta0 hbeta1 herror
      (s := p a)
      (by simp [p, rho]; linarith)
      (by simp [p, rho]; exact hgamma)
  simp only [p, rho] at hEq ⊢
  rw [hEq]

/-- Carlson's sublinear zero density and the Mellin boundary calculation
produce, in one statement, a target coefficient equal to minus the analytic
multiplicity and a missing odd-harmonic coefficient equal to zero.  The same
odd harmonic carries the strict dual-certificate gap above `pi / 2`. -/
theorem exists_missing_oddHarmonic_with_abel_coefficients_of_carlson
    {beta gamma sigma : ℝ} {m : ℕ}
    (hbeta1 : beta < 1) (hgamma : 0 < gamma)
    (hsigmaHalf : 1 / 2 < sigma) (hsigmaBeta : sigma < beta)
    (hzero : riemannZeta ((beta : ℂ) + I * gamma) = 0)
    (horder :
      analyticOrderAt riemannZeta ((beta : ℂ) + I * gamma) = m)
    (herror : PsiPowerErrorBound beta) :
    ∃ k : ℕ,
      riemannZeta (oddHarmonicPoint beta gamma k) ≠ 0 ∧
      Real.pi / 2 < missingHarmonicLowerBound (2 * k + 1) ∧
      Tendsto
        (fun a : ℝ =>
          (a : ℂ) *
            regularizedNegLogDerivModel
              ((beta : ℂ) + I * gamma + (a : ℂ)))
        (𝓝[>] 0) (𝓝 (-(m : ℂ))) ∧
      Tendsto
        (fun a : ℝ =>
          (a : ℂ) *
            regularizedNegLogDerivModel
              (oddHarmonicPoint beta gamma k + (a : ℂ)))
        (𝓝[>] 0) (𝓝 0) := by
  have hbeta0 : 0 ≤ beta := by
    linarith
  rcases
      exists_missing_oddHarmonic_with_strict_gap_of_carlson
        hbeta1 hgamma hsigmaHalf hsigmaBeta with
    ⟨k, hkMissing, hkGap⟩
  have htarget :=
    tendsto_atRight_mul_regularizedNegLogDerivModel_of_zeta_zero
      (rho := (beta : ℂ) + I * gamma)
      (n := m)
      (by simpa using hbeta0)
      (by simpa using hbeta1)
      (by simpa using hgamma)
      hzero horder
      (by simpa using herror)
  have hoddPos :
      0 < ((2 * k + 1 : ℕ) : ℝ) * gamma := by
    exact mul_pos (by positivity) hgamma
  have hmissing :=
    tendsto_atRight_mul_regularizedNegLogDerivModel_of_zeta_ne_zero
      (beta := beta)
      (gamma := ((2 * k + 1 : ℕ) : ℝ) * gamma)
      hbeta0 hbeta1 hoddPos
      (by simpa [oddHarmonicPoint] using hkMissing)
      herror
  refine ⟨k, hkMissing, hkGap, htarget, ?_⟩
  simpa [oddHarmonicPoint] using hmissing

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
