import ZeroFreeRegion.MeromorphicAux

open Complex Filter MeromorphicOn Topology

namespace PrimeNumberTheorem

/-- In the open critical strip, multiplying the completed zeta function by
the reciprocal real Gamma factor does not change its analytic order. -/
private lemma analyticOrderAt_riemannZeta_eq_completedRiemannZeta
    {s : ℂ} (hsre : 0 < s.re) (hsre' : s.re < 1) :
    analyticOrderAt riemannZeta s = analyticOrderAt completedRiemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro hs
    have hre := congrArg Complex.re hs
    simp at hre
    linarith
  have hs1 : s ≠ 1 := by
    intro hs
    have hre := congrArg Complex.re hs
    simp at hre
    linarith
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
  have hgamma : AnalyticAt ℂ (fun z : ℂ => (Gammaℝ z)⁻¹) s :=
    differentiable_Gammaℝ_inv.analyticAt s
  have hgamma_ne : (Gammaℝ s)⁻¹ ≠ 0 :=
    inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hsre)
  have hzeta_completed : riemannZeta =ᶠ[𝓝 s]
      fun z : ℂ => completedRiemannZeta z * (Gammaℝ z)⁻¹ := by
    filter_upwards [eventually_ne_nhds hs0] with z hz
    rw [riemannZeta_def_of_ne_zero hz, div_eq_mul_inv]
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

/-- Functional-equation symmetry preserves the multiplicity of a nontrivial
Riemann-zeta zero. -/
theorem analyticOrderNatAt_riemannZeta_one_sub_of_nontrivialZero
    {ρ : ℂ} (hρ : RiemannHypothesis.IsNontrivialZero ρ) :
    analyticOrderNatAt riemannZeta (1 - ρ) =
      analyticOrderNatAt riemannZeta ρ := by
  obtain ⟨_hzero, hρre, hρre'⟩ := hρ
  have hone_re : 0 < (1 - ρ).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hone_re' : (1 - ρ).re < 1 := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  let g : ℂ → ℂ := fun z => 1 - z
  have hg : AnalyticAt ℂ g ρ := by
    dsimp [g]
    fun_prop
  have hg_deriv : deriv g ρ ≠ 0 := by
    dsimp [g]
    rw [show deriv (fun z : ℂ => 1 - z) ρ = -1 by
      convert ((hasDerivAt_const ρ 1).sub (hasDerivAt_id ρ)).deriv using 1
      all_goals simp]
    exact neg_ne_zero.mpr one_ne_zero
  have hcomp :
      analyticOrderAt (completedRiemannZeta ∘ g) ρ =
        analyticOrderAt completedRiemannZeta (g ρ) :=
    analyticOrderAt_comp_of_deriv_ne_zero hg hg_deriv
  have hfunctional : completedRiemannZeta ∘ g = completedRiemannZeta := by
    funext z
    exact completedRiemannZeta_one_sub z
  have hcompleted_symm :
      analyticOrderAt completedRiemannZeta (1 - ρ) =
        analyticOrderAt completedRiemannZeta ρ := by
    calc
      analyticOrderAt completedRiemannZeta (1 - ρ) =
          analyticOrderAt (completedRiemannZeta ∘ g) ρ := by
        simpa [g] using hcomp.symm
      _ = analyticOrderAt completedRiemannZeta ρ := by rw [hfunctional]
  have horder :
      analyticOrderAt riemannZeta (1 - ρ) =
        analyticOrderAt riemannZeta ρ := by
    rw [analyticOrderAt_riemannZeta_eq_completedRiemannZeta hone_re hone_re',
      analyticOrderAt_riemannZeta_eq_completedRiemannZeta hρre hρre']
    exact hcompleted_symm
  exact congrArg ENat.toNat horder

/-- Above a positive height cutoff, one multiplicity-weighted zero term is
bounded by its multiplicity times `x / T`. -/
theorem norm_multiplicity_zero_contribution_le_div_height
    {x T : ℝ} {ρ : ℂ} (hx : 1 < x) (hT : 0 < T)
    (hρ : RiemannHypothesis.IsNontrivialZero ρ) (hheight : T < |ρ.im|) :
    ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
      (analyticOrderNatAt riemannZeta ρ : ℝ) * x / T := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hxpow : x ^ ρ.re ≤ x := by
    calc
      x ^ ρ.re ≤ x ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx.le hρ.2.2.le
      _ = x := Real.rpow_one x
  have himnorm : |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
  have hTnorm : T ≤ ‖ρ‖ := (hheight.trans_le himnorm).le
  have hm_nonneg : 0 ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) :=
    Nat.cast_nonneg _
  have hnum_nonneg :
      0 ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) * x :=
    mul_nonneg hm_nonneg hxpos.le
  rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
  have hm_norm : ‖(analyticOrderNatAt riemannZeta ρ : ℂ)‖ =
      (analyticOrderNatAt riemannZeta ρ : ℝ) := by simp
  rw [hm_norm]
  calc
    (analyticOrderNatAt riemannZeta ρ : ℝ) * x ^ ρ.re / ‖ρ‖ ≤
        (analyticOrderNatAt riemannZeta ρ : ℝ) * x / ‖ρ‖ := by
      apply div_le_div_of_nonneg_right _ (norm_nonneg ρ)
      exact mul_le_mul_of_nonneg_left hxpow hm_nonneg
    _ ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) * x / T :=
      div_le_div_of_nonneg_left hnum_nonneg hT hTnorm

/-- On a closed disk containing a nontrivial zero, the zeta divisor records
exactly that zero's natural analytic multiplicity. -/
theorem divisor_riemannZeta_closedBall_eq_analyticOrderNatAt_of_nontrivialZero
    {c ρ : ℂ} {R : ℝ} (hρ : RiemannHypothesis.IsNontrivialZero ρ)
    (hmem : ρ ∈ Metric.closedBall c R) :
    MeromorphicOn.divisor riemannZeta (Metric.closedBall c R) ρ =
      (analyticOrderNatAt riemannZeta ρ : ℤ) := by
  have hρ1 : ρ ≠ 1 := by
    intro hone
    have hre := congrArg Complex.re hone
    simp at hre
    linarith [hρ.2.2]
  have hanalytic : AnalyticAt ℂ riemannZeta ρ :=
    ZeroFreeRegion.analyticOnNhd_riemannZeta_ne_one ρ hρ1
  rw [MeromorphicOn.divisor_apply
    (ZeroFreeRegion.meromorphicOn_riemannZeta_closedBall c R) hmem,
    hanalytic.meromorphicOrderAt_eq]
  have horder :=
    ZeroFreeRegion.analyticOrderNatAt_riemannZeta_eq_analyticOrderAt_of_ne_one hρ1
  rw [← horder]
  simp

/-- The total analytic multiplicity of a finite family of nontrivial zeros in
a pole-free closed disk is bounded by the disk's zeta-divisor mass. -/
theorem sum_analyticOrderNatAt_riemannZeta_le_finsum_divisor_closedBall
    {c : ℂ} {R : ℝ} (S : Finset ℂ)
    (havoid : ∀ z : ℂ, z ∈ Metric.closedBall c R → z ≠ 1)
    (hS : ∀ ρ ∈ S,
      RiemannHypothesis.IsNontrivialZero ρ ∧ ρ ∈ Metric.closedBall c R) :
    (∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
      ∑ᶠ u, (MeromorphicOn.divisor riemannZeta
        (Metric.closedBall c R) u : ℝ) := by
  classical
  let D := MeromorphicOn.divisor riemannZeta (Metric.closedBall c R)
  have hanalytic : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall c R) := by
    intro z hz
    exact ZeroFreeRegion.analyticOnNhd_riemannZeta_ne_one z (havoid z hz)
  have hD_nonneg : 0 ≤ D := hanalytic.divisor_nonneg
  have hD_finite : D.support.Finite :=
    D.finiteSupport (isCompact_closedBall c R)
  have hS_subset : S ⊆ hD_finite.toFinset := by
    intro ρ hρS
    apply hD_finite.mem_toFinset.mpr
    have hρ := (hS ρ hρS).1
    have hρ1 : ρ ≠ 1 := by
      intro hone
      have hre := congrArg Complex.re hone
      simp at hre
      linarith [hρ.2.2]
    have hmult_pos : 0 < analyticOrderNatAt riemannZeta ρ :=
      ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero hρ1 hρ.1
    have hD_eq : D ρ = (analyticOrderNatAt riemannZeta ρ : ℤ) := by
      dsimp [D]
      exact divisor_riemannZeta_closedBall_eq_analyticOrderNatAt_of_nontrivialZero
        hρ (hS ρ hρS).2
    simp only [Function.mem_support]
    rw [hD_eq]
    exact_mod_cast hmult_pos.ne'
  have hcast_support :
      (fun u : ℂ => (D u : ℝ)).support ⊆ hD_finite.toFinset := by
    intro u hu
    apply hD_finite.mem_toFinset.mpr
    simp only [Function.mem_support] at hu ⊢
    exact_mod_cast hu
  calc
    (∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℝ)) =
        ∑ ρ ∈ S, (D ρ : ℝ) := by
      apply Finset.sum_congr rfl
      intro ρ hρS
      rw [divisor_riemannZeta_closedBall_eq_analyticOrderNatAt_of_nontrivialZero
        (hS ρ hρS).1 (hS ρ hρS).2]
      norm_cast
    _ ≤ ∑ u ∈ hD_finite.toFinset, (D u : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hS_subset
      intro u _hu _huS
      exact_mod_cast hD_nonneg u
    _ = ∑ᶠ u, (D u : ℝ) :=
      (finsum_eq_sum_of_support_subset _ hcast_support).symm
    _ = ∑ᶠ u, (MeromorphicOn.divisor riemannZeta
          (Metric.closedBall c R) u : ℝ) := by rfl

end PrimeNumberTheorem
