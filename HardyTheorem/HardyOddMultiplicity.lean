import HardyTheorem.AnalyticSignChange
import HardyTheorem.HardyIntegralBasics
import PrimeNumberTheorem.NontrivialZeroMultiplicity

open Complex Filter Set Topology

namespace HardyTheorem

/-- The real restriction of the completed zeta function to the critical line. -/
noncomputable def criticalLineCompletedRiemannZeta (t : ℝ) : ℝ :=
  (completedRiemannZeta ((1 / 2 : ℂ) + I * t)).re

private noncomputable def criticalLineCompletedRiemannZetaComplex (z : ℂ) : ℂ :=
  completedRiemannZeta ((1 / 2 : ℂ) + I * z)

private lemma criticalLinePoint_ne_zero (t : ℝ) :
    (1 / 2 : ℂ) + I * t ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre

private lemma criticalLinePoint_ne_one (t : ℝ) :
    (1 / 2 : ℂ) + I * t ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre

private lemma analyticAt_completedRiemannZeta_criticalLine (t : ℝ) :
    AnalyticAt ℂ completedRiemannZeta ((1 / 2 : ℂ) + I * t) := by
  let s := (1 / 2 : ℂ) + I * t
  have hs0 : s ≠ 0 := by simpa [s] using criticalLinePoint_ne_zero t
  have hs1 : s ≠ 1 := by simpa [s] using criticalLinePoint_ne_one t
  have hcompleted0 : AnalyticAt ℂ completedRiemannZeta₀ s :=
    differentiable_completedZeta₀.analyticAt s
  have hone_div : AnalyticAt ℂ (fun z : ℂ => 1 / z) s :=
    analyticAt_const.div analyticAt_id hs0
  have hone_sub_div : AnalyticAt ℂ (fun z : ℂ => 1 / (1 - z)) s :=
    analyticAt_const.div (analyticAt_const.sub analyticAt_id)
      (sub_ne_zero.mpr hs1.symm)
  apply ((hcompleted0.sub hone_div).sub hone_sub_div).congr
  filter_upwards [] with z
  exact (completedRiemannZeta_eq z).symm

private lemma analyticAt_criticalLineCompletedRiemannZetaComplex (t : ℝ) :
    AnalyticAt ℂ criticalLineCompletedRiemannZetaComplex (t : ℂ) := by
  change AnalyticAt ℂ
    (completedRiemannZeta ∘ fun z : ℂ => (1 / 2 : ℂ) + I * z) (t : ℂ)
  have hg : AnalyticAt ℂ (fun z : ℂ => (1 / 2 : ℂ) + I * z) (t : ℂ) := by
    fun_prop
  exact AnalyticAt.comp
    (g := completedRiemannZeta)
    (f := fun z : ℂ => (1 / 2 : ℂ) + I * z)
    (x := (t : ℂ))
    (analyticAt_completedRiemannZeta_criticalLine t) hg

/-- The completed zeta function restricted to the real critical-line
parameter is real analytic. -/
theorem analyticAt_criticalLineCompletedRiemannZeta (t : ℝ) :
    AnalyticAt ℝ criticalLineCompletedRiemannZeta t := by
  change AnalyticAt ℝ
    (fun x : ℝ => (criticalLineCompletedRiemannZetaComplex (x : ℂ)).re) t
  exact (analyticAt_criticalLineCompletedRiemannZetaComplex t).re_ofReal

/-- Hardy's `Z` function is the real completed zeta value divided by the
strictly positive real-Gamma norm. -/
theorem hardyZ_eq_criticalLineCompletedRiemannZeta_div_norm (t : ℝ) :
    hardyZ t = criticalLineCompletedRiemannZeta t /
      ‖Gammaℝ ((1 / 2 : ℂ) + I * t)‖ := by
  let s := (0.5 : ℂ) + I * t
  have hs_eq : s = (1 / 2 : ℂ) + I * t := by
    simp [s]
    norm_num
  have hs0 : s ≠ 0 := by
    intro h0
    simp [s, Complex.ext_iff] at h0
    norm_num at h0
  have h_internal :
      hardyZ t = (completedRiemannZeta s).re / ‖Gammaℝ s‖ := by
    have h_def :
        hardyZ t = (riemannZeta s).re * Real.cos (thetaPhase t) -
          (riemannZeta s).im * Real.sin (thetaPhase t) := by
      simp [hardyZ, s]
    rw [h_def]
    have h_zeta : riemannZeta s = completedRiemannZeta s / Gammaℝ s := by
      rw [riemannZeta_def_of_ne_zero hs0]
    rw [h_zeta]
    have h_gamma_ne : Gammaℝ s ≠ 0 := by
      apply Gammaℝ_ne_zero_of_re_pos
      simp [s]
      norm_num
    have h_normSq : Complex.normSq (Gammaℝ s) = ‖Gammaℝ s‖ ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
    have h_gamma :
        (Gammaℝ s).re = ‖Gammaℝ s‖ * Real.cos (thetaPhase t) ∧
          (Gammaℝ s).im = ‖Gammaℝ s‖ * Real.sin (thetaPhase t) := by
      rw [hs_eq]
      exact Gammaℝ_re_im_arg t
    simp [Complex.div_re, Complex.div_im, h_gamma.1, h_gamma.2, h_normSq]
    field_simp [h_gamma_ne]
    ring_nf
    have h_trig :
        (completedRiemannZeta s).re * Real.cos (thetaPhase t) ^ 2 +
            (completedRiemannZeta s).re * Real.sin (thetaPhase t) ^ 2 =
          (completedRiemannZeta s).re := by
      calc
        (completedRiemannZeta s).re * Real.cos (thetaPhase t) ^ 2 +
            (completedRiemannZeta s).re * Real.sin (thetaPhase t) ^ 2 =
            (completedRiemannZeta s).re *
              (Real.cos (thetaPhase t) ^ 2 + Real.sin (thetaPhase t) ^ 2) := by
                ring
        _ = (completedRiemannZeta s).re := by rw [Real.cos_sq_add_sin_sq]; ring
    ring_nf at h_trig ⊢
    exact h_trig
  rw [hs_eq] at h_internal
  simpa [criticalLineCompletedRiemannZeta] using h_internal

/-- On the critical line, zeta and completed zeta have the same analytic
order because the real Gamma factor is analytic and nonvanishing. -/
private lemma analyticOrderAt_riemannZeta_eq_completedRiemannZeta_criticalLine
    (t : ℝ) :
    analyticOrderAt riemannZeta ((1 / 2 : ℂ) + I * t) =
      analyticOrderAt completedRiemannZeta ((1 / 2 : ℂ) + I * t) := by
  let s := (1 / 2 : ℂ) + I * t
  have hs0 : s ≠ 0 := by simpa [s] using criticalLinePoint_ne_zero t
  have hs1 : s ≠ 1 := by simpa [s] using criticalLinePoint_ne_one t
  have hcompleted : AnalyticAt ℂ completedRiemannZeta s := by
    simpa [s] using analyticAt_completedRiemannZeta_criticalLine t
  have hgamma : AnalyticAt ℂ (fun z : ℂ => (Gammaℝ z)⁻¹) s :=
    differentiable_Gammaℝ_inv.analyticAt s
  have hgamma_ne : (Gammaℝ s)⁻¹ ≠ 0 :=
    inv_ne_zero (Gammaℝ_ne_zero_of_re_pos (by simp [s]))
  have hzeta_completed : riemannZeta =ᶠ[nhds s]
      fun z : ℂ => completedRiemannZeta z * (Gammaℝ z)⁻¹ := by
    filter_upwards [eventually_ne_nhds hs0] with z hz
    rw [riemannZeta_def_of_ne_zero hz, div_eq_mul_inv]
  calc
    analyticOrderAt riemannZeta s =
        analyticOrderAt (fun z : ℂ =>
          completedRiemannZeta z * (Gammaℝ z)⁻¹) s :=
      analyticOrderAt_congr hzeta_completed
    _ = analyticOrderAt completedRiemannZeta s +
          analyticOrderAt (fun z : ℂ => (Gammaℝ z)⁻¹) s :=
      analyticOrderAt_mul hcompleted hgamma
    _ = analyticOrderAt completedRiemannZeta s + 0 := by
      rw [hgamma.analyticOrderAt_eq_zero.mpr hgamma_ne]
    _ = analyticOrderAt completedRiemannZeta s := add_zero _

private lemma analyticOrderAt_criticalLineCompletedRiemannZetaComplex_eq
    (t : ℝ) :
    analyticOrderAt criticalLineCompletedRiemannZetaComplex (t : ℂ) =
      analyticOrderAt completedRiemannZeta ((1 / 2 : ℂ) + I * t) := by
  let g : ℂ → ℂ := fun z => (1 / 2 : ℂ) + I * z
  have hg : AnalyticAt ℂ g (t : ℂ) := by
    dsimp [g]
    fun_prop
  have hg' : deriv g (t : ℂ) ≠ 0 := by
    have hderiv : deriv g (t : ℂ) = I := by
      dsimp [g]
      convert ((hasDerivAt_const (t : ℂ) (1 / 2 : ℂ)).add
        ((hasDerivAt_const (t : ℂ) I).mul (hasDerivAt_id (t : ℂ)))).deriv using 1
      all_goals simp
    rw [hderiv]
    exact I_ne_zero
  change analyticOrderAt (completedRiemannZeta ∘ g) (t : ℂ) =
    analyticOrderAt completedRiemannZeta (g (t : ℂ))
  exact analyticOrderAt_comp_of_deriv_ne_zero
    (f := completedRiemannZeta) hg hg'

private lemma criticalLineCompletedRiemannZetaComplex_real (x : ℝ) :
    ∃ r : ℝ, criticalLineCompletedRiemannZetaComplex (x : ℂ) = (r : ℂ) := by
  simpa [criticalLineCompletedRiemannZetaComplex] using
    completedRiemannZeta_critical_line_real x

/-- Restricting the completed zeta function to the real critical-line
parameter preserves its natural analytic order. -/
theorem analyticOrderNatAt_criticalLineCompletedRiemannZeta_eq_riemannZeta
    (t : ℝ) :
    analyticOrderNatAt criticalLineCompletedRiemannZeta t =
      analyticOrderNatAt riemannZeta ((1 / 2 : ℂ) + I * t) := by
  let F : ℂ → ℂ := criticalLineCompletedRiemannZetaComplex
  let f : ℝ → ℝ := criticalLineCompletedRiemannZeta
  let n := analyticOrderNatAt F (t : ℂ)
  have hF : AnalyticAt ℂ F (t : ℂ) :=
    analyticAt_criticalLineCompletedRiemannZetaComplex t
  have hs1 : (1 / 2 : ℂ) + I * t ≠ 1 := criticalLinePoint_ne_one t
  have hFfinite : analyticOrderAt F (t : ℂ) ≠ ⊤ := by
    rw [show analyticOrderAt F (t : ℂ) =
      analyticOrderAt riemannZeta ((1 / 2 : ℂ) + I * t) by
        rw [analyticOrderAt_criticalLineCompletedRiemannZetaComplex_eq]
        exact (analyticOrderAt_riemannZeta_eq_completedRiemannZeta_criticalLine t).symm]
    exact ZeroFreeRegion.analyticOrderAt_riemannZeta_ne_top_of_ne_one hs1
  obtain ⟨g, hg, hgt, hfactor⟩ :=
    (hF.analyticOrderNatAt_eq_iff hFfinite).mp rfl
  let gr : ℝ → ℝ := fun x => (g (x : ℂ)).re
  have hgr : AnalyticAt ℝ gr t := by
    dsimp [gr]
    exact hg.re_ofReal
  have hy : Tendsto (fun k : ℕ => t + (1 / (k + 1 : ℝ))) atTop (nhds t) :=
    by simpa using
      (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun k : ℕ => t + (1 / (k + 1 : ℝ))) atTop (nhds (t + 0)))
  have hyC : Tendsto (fun k : ℕ => ((t + (1 / (k + 1 : ℝ)) : ℝ) : ℂ))
      atTop (nhds (t : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hy
  have hfactor_seq := Filter.EventuallyEq.comp_tendsto hfactor hyC
  have hg_im_seq : ∀ᶠ k : ℕ in atTop,
      (g ((t + (1 / (k + 1 : ℝ)) : ℝ) : ℂ)).im = 0 := by
    filter_upwards [hfactor_seq] with k hk
    let y : ℝ := t + 1 / (k + 1 : ℝ)
    have hyt : y ≠ t := by
      dsimp [y]
      have hpos : 0 < (1 / (k + 1 : ℝ)) := by positivity
      linarith
    obtain ⟨r, hr⟩ := criticalLineCompletedRiemannZetaComplex_real y
    change F (y : ℂ) = ((y : ℂ) - (t : ℂ)) ^ n * g (y : ℂ) at hk
    have hsub : (y : ℂ) - (t : ℂ) ≠ 0 := by
      apply sub_ne_zero.mpr
      exact_mod_cast hyt
    have hpow_real : (((y : ℂ) - (t : ℂ)) ^ n) = (((y - t) ^ n : ℝ) : ℂ) := by
      push_cast
      rfl
    have hprod : (((y : ℂ) - (t : ℂ)) ^ n) * g (y : ℂ) = (r : ℂ) := by
      exact hk.symm.trans hr
    rw [hpow_real] at hprod
    have him := congrArg Complex.im hprod
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero] at him
    exact (mul_eq_zero.mp him).resolve_left
      (pow_ne_zero _ (sub_ne_zero.mpr hyt))
  have hg_im_t : (g (t : ℂ)).im = 0 := by
    have hlim : Tendsto
        (fun k : ℕ => (g ((t + (1 / (k + 1 : ℝ)) : ℝ) : ℂ)).im)
        atTop (nhds (g (t : ℂ)).im) :=
      Complex.continuous_im.continuousAt.tendsto.comp
        (hg.continuousAt.tendsto.comp hyC)
    have hzero : Tendsto
        (fun k : ℕ => (g ((t + (1 / (k + 1 : ℝ)) : ℝ) : ℂ)).im)
        atTop (nhds 0) :=
      tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hg_im_seq)
    exact tendsto_nhds_unique hlim hzero
  have hgrt : gr t ≠ 0 := by
    intro hre
    apply hgt
    apply Complex.ext
    · exact hre
    · exact hg_im_t
  have hfactor_real : ∀ᶠ x : ℝ in nhds t,
      f x = (x - t) ^ n * gr x := by
    have hfactor' := Filter.EventuallyEq.comp_tendsto hfactor
      Complex.continuous_ofReal.continuousAt.tendsto
    filter_upwards [hfactor'] with x hx
    change F (x : ℂ) = ((x : ℂ) - (t : ℂ)) ^ n * g (x : ℂ) at hx
    have hre := congrArg Complex.re hx
    have hbase : (x : ℂ) - (t : ℂ) = ((x - t : ℝ) : ℂ) := by
      push_cast
      rfl
    have hp : (((x : ℂ) - (t : ℂ)) ^ n) = (((x - t) ^ n : ℝ) : ℂ) := by
      rw [hbase]
      norm_cast
    have hp_re : (((x : ℂ) - (t : ℂ)) ^ n).re = (x - t) ^ n := by
      simpa only [Complex.ofReal_re] using congrArg Complex.re hp
    have hp_im : (((x : ℂ) - (t : ℂ)) ^ n).im = 0 := by
      simpa only [Complex.ofReal_im] using congrArg Complex.im hp
    rw [Complex.mul_re, hp_re, hp_im, zero_mul, sub_zero] at hre
    simpa [F, f, gr, criticalLineCompletedRiemannZeta,
      criticalLineCompletedRiemannZetaComplex] using hre
  have hf : AnalyticAt ℝ f t := analyticAt_criticalLineCompletedRiemannZeta t
  have hreal_order : analyticOrderAt f t = (n : ℕ∞) :=
    hf.analyticOrderAt_eq_natCast.mpr ⟨gr, hgr, hgrt, by simpa [smul_eq_mul] using hfactor_real⟩
  have hreal_nat : analyticOrderNatAt f t = n := by
    simp [analyticOrderNatAt, hreal_order]
  calc
    analyticOrderNatAt criticalLineCompletedRiemannZeta t = n := hreal_nat
    _ = analyticOrderNatAt F (t : ℂ) := rfl
    _ = analyticOrderNatAt riemannZeta ((1 / 2 : ℂ) + I * t) := by
      unfold analyticOrderNatAt
      rw [show analyticOrderAt F (t : ℂ) =
        analyticOrderAt riemannZeta ((1 / 2 : ℂ) + I * t) by
          rw [analyticOrderAt_criticalLineCompletedRiemannZetaComplex_eq]
          exact (analyticOrderAt_riemannZeta_eq_completedRiemannZeta_criticalLine t).symm]

/-- A genuine local sign change of Hardy's `Z` function forces the
corresponding critical-line zeta zero to have odd analytic multiplicity. -/
theorem odd_analyticOrderNatAt_riemannZeta_of_hardyZ_local_sign_change
    {t : ℝ}
    (hleft : ∀ ε > 0, ∃ x ∈ Set.Ioo (t - ε) t, hardyZ x < 0)
    (hright : ∀ ε > 0, ∃ x ∈ Set.Ioo t (t + ε), 0 < hardyZ x) :
    Odd (analyticOrderNatAt riemannZeta ((1 / 2 : ℂ) + I * t)) := by
  have hleft' : ∀ ε > 0, ∃ x ∈ Set.Ioo (t - ε) t,
      criticalLineCompletedRiemannZeta x < 0 := by
    intro ε hε
    obtain ⟨x, hx, hxneg⟩ := hleft ε hε
    refine ⟨x, hx, ?_⟩
    rw [hardyZ_eq_criticalLineCompletedRiemannZeta_div_norm] at hxneg
    have hnorm : 0 < ‖Gammaℝ ((1 / 2 : ℂ) + I * x)‖ :=
      norm_pos_iff.mpr (Gammaℝ_ne_zero_of_re_pos (by simp))
    by_contra hnot
    exact (not_lt_of_ge (div_nonneg (le_of_not_gt hnot) hnorm.le)) hxneg
  have hright' : ∀ ε > 0, ∃ x ∈ Set.Ioo t (t + ε),
      0 < criticalLineCompletedRiemannZeta x := by
    intro ε hε
    obtain ⟨x, hx, hxpos⟩ := hright ε hε
    refine ⟨x, hx, ?_⟩
    rw [hardyZ_eq_criticalLineCompletedRiemannZeta_div_norm] at hxpos
    have hnorm : 0 < ‖Gammaℝ ((1 / 2 : ℂ) + I * x)‖ :=
      norm_pos_iff.mpr (Gammaℝ_ne_zero_of_re_pos (by simp))
    exact (div_pos_iff_of_pos_right hnorm).mp hxpos
  have hfinite : analyticOrderAt criticalLineCompletedRiemannZeta t ≠ ⊤ := by
    intro htop
    have hzero := analyticOrderAt_eq_top.mp htop
    rw [Metric.eventually_nhds_iff] at hzero
    obtain ⟨ε, hε, hzero⟩ := hzero
    obtain ⟨x, hx, hxpos⟩ := hright' ε hε
    have hdist : dist x t < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.1, hx.2]
    rw [hzero hdist] at hxpos
    exact lt_irrefl 0 hxpos
  rw [← analyticOrderNatAt_criticalLineCompletedRiemannZeta_eq_riemannZeta t]
  exact odd_analyticOrderNatAt_of_local_sign_change
    (analyticAt_criticalLineCompletedRiemannZeta t) hfinite hleft' hright'

/-- A local sign change of Hardy's `Z` function in the reverse orientation
also forces odd zeta multiplicity. -/
theorem odd_analyticOrderNatAt_riemannZeta_of_hardyZ_reverse_local_sign_change
    {t : ℝ}
    (hleft : ∀ ε > 0, ∃ x ∈ Set.Ioo (t - ε) t, 0 < hardyZ x)
    (hright : ∀ ε > 0, ∃ x ∈ Set.Ioo t (t + ε), hardyZ x < 0) :
    Odd (analyticOrderNatAt riemannZeta ((1 / 2 : ℂ) + I * t)) := by
  have hleft' : ∀ ε > 0, ∃ x ∈ Set.Ioo (t - ε) t,
      0 < criticalLineCompletedRiemannZeta x := by
    intro ε hε
    obtain ⟨x, hx, hxpos⟩ := hleft ε hε
    refine ⟨x, hx, ?_⟩
    rw [hardyZ_eq_criticalLineCompletedRiemannZeta_div_norm] at hxpos
    have hnorm : 0 < ‖Gammaℝ ((1 / 2 : ℂ) + I * x)‖ :=
      norm_pos_iff.mpr (Gammaℝ_ne_zero_of_re_pos (by simp))
    exact (div_pos_iff_of_pos_right hnorm).mp hxpos
  have hright' : ∀ ε > 0, ∃ x ∈ Set.Ioo t (t + ε),
      criticalLineCompletedRiemannZeta x < 0 := by
    intro ε hε
    obtain ⟨x, hx, hxneg⟩ := hright ε hε
    refine ⟨x, hx, ?_⟩
    rw [hardyZ_eq_criticalLineCompletedRiemannZeta_div_norm] at hxneg
    have hnorm : 0 < ‖Gammaℝ ((1 / 2 : ℂ) + I * x)‖ :=
      norm_pos_iff.mpr (Gammaℝ_ne_zero_of_re_pos (by simp))
    by_contra hnot
    exact (not_lt_of_ge (div_nonneg (le_of_not_gt hnot) hnorm.le)) hxneg
  have hfinite : analyticOrderAt criticalLineCompletedRiemannZeta t ≠ ⊤ := by
    intro htop
    have hzero := analyticOrderAt_eq_top.mp htop
    rw [Metric.eventually_nhds_iff] at hzero
    obtain ⟨ε, hε, hzero⟩ := hzero
    obtain ⟨x, hx, hxneg⟩ := hright' ε hε
    have hdist : dist x t < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.1, hx.2]
    rw [hzero hdist] at hxneg
    exact lt_irrefl 0 hxneg
  rw [← analyticOrderNatAt_criticalLineCompletedRiemannZeta_eq_riemannZeta t]
  exact odd_analyticOrderNatAt_of_reverse_local_sign_change
    (analyticAt_criticalLineCompletedRiemannZeta t) hfinite hleft' hright'

end HardyTheorem
