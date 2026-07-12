/-
Copyright (c) 2026 Riemann PNT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import PrimeNumberTheorem
import ZeroFreeRegion.MeromorphicAux

open Complex Filter Topology

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

/-- The meromorphic integrand shifted in the classical von Mangoldt explicit
formula. -/
noncomputable def explicitFormulaIntegrand (x : ℝ) (s : ℂ) : ℂ :=
  -logDeriv riemannZeta s * (x : ℂ) ^ s / s

/-- For positive `x`, the concrete integrand used in the von Mangoldt
explicit formula is meromorphic on the whole complex plane. -/
theorem meromorphic_explicitFormulaIntegrand
    {x : ℝ} (hx : 0 < x) :
    Meromorphic (explicitFormulaIntegrand x) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  intro s
  have hlog :
      MeromorphicAt (fun z : ℂ => -logDeriv riemannZeta z) s :=
    ZeroFreeRegion.meromorphicOn_neg_logDeriv_riemannZeta_closedBall s 0 s (by simp)
  have hpow_diff : Differentiable ℂ (fun z : ℂ => (x : ℂ) ^ z) :=
    (differentiable_id : Differentiable ℂ (fun z : ℂ => z)).const_cpow
      (Or.inl hx0)
  have hpow : MeromorphicAt (fun z : ℂ => (x : ℂ) ^ z) s :=
    (hpow_diff.analyticAt s).meromorphicAt
  have hid : MeromorphicAt (fun z : ℂ => z) s :=
    analyticAt_id.meromorphicAt
  change MeromorphicAt
    ((fun z : ℂ => -logDeriv riemannZeta z) *
      (fun z : ℂ => (x : ℂ) ^ z) / fun z : ℂ => z) s
  exact (hlog.mul hpow).div hid

/-- Away from the kernel pole `0`, the zeta pole `1`, and the zeros of zeta,
the concrete explicit-formula integrand is analytic. -/
theorem analyticAt_explicitFormulaIntegrand_of_ne_zero_of_ne_one_of_zeta_ne_zero
    {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hzeta : riemannZeta s ≠ 0) :
    AnalyticAt ℂ (explicitFormulaIntegrand x) s := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hlog : AnalyticAt ℂ (fun z : ℂ => -logDeriv riemannZeta z) s :=
    (ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_of_ne_one_of_ne_zero
      s hs1 hzeta).neg
  have hpow_diff : Differentiable ℂ (fun z : ℂ => (x : ℂ) ^ z) :=
    (differentiable_id : Differentiable ℂ (fun z : ℂ => z)).const_cpow
      (Or.inl hx0)
  have hpow : AnalyticAt ℂ (fun z : ℂ => (x : ℂ) ^ z) s :=
    hpow_diff.analyticAt s
  change AnalyticAt ℂ
    ((fun z : ℂ => -logDeriv riemannZeta z) *
      (fun z : ℂ => (x : ℂ) ^ z) / fun z : ℂ => z) s
  exact (hlog.mul hpow).div analyticAt_id hs0

/-- On every compact set, the concrete explicit-formula integrand is analytic
away from a finite set of pole candidates.  The candidates are the kernel
pole `0` together with the support of the zeta divisor on the compact set, so
they include the zeta pole at `1` and every zeta zero in the set. -/
theorem exists_finite_explicitFormulaIntegrand_pole_candidates
    {x : ℝ} (hx : 0 < x) {K : Set ℂ} (hK : IsCompact K) :
    ∃ poles : Finset ℂ,
      ∀ s ∈ K, s ∉ poles → AnalyticAt ℂ (explicitFormulaIntegrand x) s := by
  classical
  have hzeta_meromorphic : MeromorphicOn riemannZeta K := by
    intro s _hs
    by_cases hs1 : s = 1
    · subst s
      exact ZeroFreeRegion.meromorphicAt_riemannZeta_one
    · exact ZeroFreeRegion.meromorphicAt_riemannZeta_of_ne_one s hs1
  let D := MeromorphicOn.divisor riemannZeta K
  have hDfinite : D.support.Finite := D.finiteSupport hK
  let poles : Finset ℂ := hDfinite.toFinset ∪ {0}
  refine ⟨poles, ?_⟩
  intro s hsK hs_not_mem
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    apply hs_not_mem
    simp [poles]
  have hs_not_support : s ∉ D.support := by
    intro hs
    apply hs_not_mem
    simp [poles, hDfinite.mem_toFinset, hs]
  have hDzero : D s = 0 := Function.notMem_support.mp hs_not_support
  have hs1 : s ≠ 1 := by
    intro hs
    subst s
    have hDone : D (1 : ℂ) = (-1 : ℤ) := by
      simpa [D] using
        ZeroFreeRegion.divisor_riemannZeta_pole_one hsK hzeta_meromorphic
    rw [hDzero] at hDone
    norm_num at hDone
  have hzeta : riemannZeta s ≠ 0 := by
    intro hzeta_zero
    have han : AnalyticAt ℂ riemannZeta s :=
      ZeroFreeRegion.analyticOnNhd_riemannZeta_ne_one s hs1
    have hpos : 0 < analyticOrderNatAt riemannZeta s :=
      ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero hs1 hzeta_zero
    have horder :
        analyticOrderAt riemannZeta s =
          (analyticOrderNatAt riemannZeta s : ℕ∞) :=
      (ZeroFreeRegion.analyticOrderNatAt_riemannZeta_eq_analyticOrderAt_of_ne_one
        hs1).symm
    have hDvalue : D s = (analyticOrderNatAt riemannZeta s : ℤ) := by
      rw [MeromorphicOn.divisor_apply hzeta_meromorphic hsK,
        han.meromorphicOrderAt_eq, horder]
      simp
    rw [hDzero] at hDvalue
    have hnat_zero : analyticOrderNatAt riemannZeta s = 0 := by
      exact_mod_cast hDvalue.symm
    exact (Nat.ne_of_gt hpos) hnat_zero
  exact
    analyticAt_explicitFormulaIntegrand_of_ne_zero_of_ne_one_of_zeta_ne_zero
      hx hs0 hs1 hzeta

/-- The signed logarithmic derivative of zeta has principal coefficient `1`
at the pole of zeta at `s = 1`. -/
theorem tendsto_sub_one_mul_neg_logDeriv_riemannZeta :
    Tendsto (fun s : ℂ => (s - 1) * (-logDeriv riemannZeta s))
      (𝓝[≠] (1 : ℂ)) (𝓝 1) := by
  have hsub : Tendsto (fun s : ℂ => s - 1) (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    have hcont : ContinuousAt (fun s : ℂ => s - 1) 1 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hregular :
      Tendsto (fun s : ℂ => logDeriv ZeroFreeRegion.riemannZetaPoleUnitAtOne s)
        (𝓝[≠] (1 : ℂ))
        (𝓝 (logDeriv ZeroFreeRegion.riemannZetaPoleUnitAtOne 1)) :=
    ZeroFreeRegion.analyticAt_logDeriv_riemannZetaPoleUnitAtOne.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hproduct :
      Tendsto
        (fun s : ℂ => (s - 1) *
          logDeriv ZeroFreeRegion.riemannZetaPoleUnitAtOne s)
        (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    simpa using hsub.mul hregular
  have hrhs :
      Tendsto
        (fun s : ℂ => 1 - (s - 1) *
          logDeriv ZeroFreeRegion.riemannZetaPoleUnitAtOne s)
        (𝓝[≠] (1 : ℂ)) (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hproduct
  have heq :
      (fun s : ℂ => (s - 1) * (-logDeriv riemannZeta s))
        =ᶠ[𝓝[≠] (1 : ℂ)]
      (fun s : ℂ => 1 - (s - 1) *
        logDeriv ZeroFreeRegion.riemannZetaPoleUnitAtOne s) := by
    filter_upwards
      [ZeroFreeRegion.eventuallyEq_logDeriv_riemannZeta_simplePoleAtOne,
        self_mem_nhdsWithin]
      with s hlog hs
    have hs_ne : s - 1 ≠ 0 :=
      sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hs)
    rw [hlog]
    field_simp [hs_ne]
    ring
  exact hrhs.congr' heq.symm

/-- The explicit-formula integrand has residue `x` at the pole `s = 1`. -/
theorem tendsto_sub_one_mul_explicitFormulaIntegrand_one
    {x : ℝ} (hx : 0 < x) :
    Tendsto (fun s : ℂ => (s - 1) * explicitFormulaIntegrand x s)
      (𝓝[≠] (1 : ℂ)) (𝓝 (x : ℂ)) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hweight :
      Tendsto (fun s : ℂ => (x : ℂ) ^ s / s)
        (𝓝[≠] (1 : ℂ)) (𝓝 (x : ℂ)) := by
    have hcont : ContinuousAt (fun s : ℂ => (x : ℂ) ^ s / s) 1 :=
      (continuousAt_const_cpow hx0).div continuousAt_id one_ne_zero
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hmul := tendsto_sub_one_mul_neg_logDeriv_riemannZeta.mul hweight
  convert hmul using 1
  · funext s
    simp only [explicitFormulaIntegrand]
    ring
  · ring_nf

/-- Subtracting the principal part `x / (s - 1)` leaves an analytic germ at
the zeta pole `s = 1`. -/
theorem exists_analyticAt_eventuallyEq_explicitFormulaIntegrand_sub_principalPart_one
    {x : ℝ} (hx : 0 < x) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 1 ∧
      (fun z : ℂ => explicitFormulaIntegrand x z - (z - 1)⁻¹ * (x : ℂ))
        =ᶠ[𝓝[≠] (1 : ℂ)] G := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  let weight : ℂ → ℂ := fun z => (x : ℂ) ^ z / z
  have hpow_diff : Differentiable ℂ (fun z : ℂ => (x : ℂ) ^ z) :=
    (differentiable_id : Differentiable ℂ (fun z : ℂ => z)).const_cpow
      (Or.inl hx0)
  have hweight_diff : DifferentiableOn ℂ weight ({(0 : ℂ)}ᶜ : Set ℂ) := by
    intro z hz
    have hz0 : z ≠ 0 := by simpa using hz
    exact ((hpow_diff z).div differentiableAt_id hz0).differentiableWithinAt
  have hone_mem : (1 : ℂ) ∈ ({(0 : ℂ)}ᶜ : Set ℂ) := by norm_num
  have hzero_nhds : ({(0 : ℂ)}ᶜ : Set ℂ) ∈ 𝓝 (1 : ℂ) :=
    isOpen_compl_singleton.mem_nhds hone_mem
  have hweight_analytic : AnalyticAt ℂ weight 1 :=
    (hweight_diff.analyticOnNhd isOpen_compl_singleton) 1 hone_mem
  have hdslope_diff :
      DifferentiableOn ℂ (dslope weight 1) ({(0 : ℂ)}ᶜ : Set ℂ) :=
    (Complex.differentiableOn_dslope hzero_nhds).2 hweight_diff
  have hdslope_analytic : AnalyticAt ℂ (dslope weight 1) 1 :=
    (hdslope_diff.analyticOnNhd isOpen_compl_singleton) 1 hone_mem
  let G : ℂ → ℂ := fun z =>
    dslope weight 1 z -
      logDeriv ZeroFreeRegion.riemannZetaPoleUnitAtOne z * weight z
  have hG : AnalyticAt ℂ G 1 :=
    hdslope_analytic.sub
      (ZeroFreeRegion.analyticAt_logDeriv_riemannZetaPoleUnitAtOne.mul
        hweight_analytic)
  refine ⟨G, hG, ?_⟩
  filter_upwards
    [ZeroFreeRegion.eventuallyEq_logDeriv_riemannZeta_simplePoleAtOne,
      self_mem_nhdsWithin,
      (eventually_ne_nhds (by norm_num : (1 : ℂ) ≠ 0)).filter_mono
        nhdsWithin_le_nhds]
    with z hlog hz1 hz0
  have hz_ne_one : z ≠ 1 := Set.mem_compl_singleton_iff.mp hz1
  have hsolve :
      -logDeriv riemannZeta z =
        (z - 1)⁻¹ - logDeriv ZeroFreeRegion.riemannZetaPoleUnitAtOne z := by
    rw [hlog]
    ring
  have hweight_one : weight 1 = (x : ℂ) := by
    simp [weight]
  rw [show explicitFormulaIntegrand x z =
      -logDeriv riemannZeta z * weight z by
    simp only [explicitFormulaIntegrand, weight]
    ring]
  simp only [G]
  change (-logDeriv riemannZeta z) * weight z -
      (z - 1)⁻¹ * (x : ℂ) = _
  rw [hsolve, dslope_of_ne weight hz_ne_one]
  simp only [slope, vsub_eq_sub, smul_eq_mul]
  rw [hweight_one]
  ring

/-- At a finite-order zeta zero `ρ` away from the pole, the principal
coefficient of `-ζ'/ζ` is minus the zero multiplicity. -/
theorem tendsto_sub_mul_neg_logDeriv_riemannZeta_of_order_eq_nat
    {ρ : ℂ} {n : ℕ} (hρ1 : ρ ≠ 1)
    (horder : analyticOrderAt riemannZeta ρ = n) :
    Tendsto (fun s : ℂ => (s - ρ) * (-logDeriv riemannZeta s))
      (𝓝[≠] ρ) (𝓝 (-(n : ℂ))) := by
  rcases
      ZeroFreeRegion.exists_eventuallyEq_neg_logDeriv_riemannZeta_add_order_mul_inv_of_order_eq_nat
        hρ1 horder with ⟨g, hg, hg_ne, hsep⟩
  have hg_log : AnalyticAt ℂ (logDeriv g) ρ :=
    hg.deriv.div hg hg_ne
  have hsub : Tendsto (fun s : ℂ => s - ρ) (𝓝[≠] ρ) (𝓝 0) := by
    have hcont : ContinuousAt (fun s : ℂ => s - ρ) ρ := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hregular :
      Tendsto (fun s : ℂ => -logDeriv g s) (𝓝[≠] ρ)
        (𝓝 (-logDeriv g ρ)) :=
    hg_log.continuousAt.neg.tendsto.mono_left nhdsWithin_le_nhds
  have hproduct :
      Tendsto (fun s : ℂ => (s - ρ) * (-logDeriv g s))
        (𝓝[≠] ρ) (𝓝 0) := by
    simpa using hsub.mul hregular
  have hrhs :
      Tendsto (fun s : ℂ => (s - ρ) * (-logDeriv g s) - (n : ℂ))
        (𝓝[≠] ρ) (𝓝 (-(n : ℂ))) := by
    simpa using hproduct.sub tendsto_const_nhds
  have heq :
      (fun s : ℂ => (s - ρ) * (-logDeriv riemannZeta s))
        =ᶠ[𝓝[≠] ρ]
      (fun s : ℂ => (s - ρ) * (-logDeriv g s) - (n : ℂ)) := by
    filter_upwards [hsep, self_mem_nhdsWithin] with s hs hsρ
    have hs_ne : s - ρ ≠ 0 :=
      sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hsρ)
    have hsolve :
        -logDeriv riemannZeta s =
          -logDeriv g s - (n : ℂ) * (s - ρ)⁻¹ := by
      exact eq_sub_of_add_eq hs
    rw [hsolve]
    field_simp [hs_ne]
  exact hrhs.congr' heq.symm

/-- At a finite-order zeta zero away from `0` and `1`, subtracting the actual
simple principal part of the explicit-formula integrand leaves an analytic
germ.  This is stronger than the residue limit: it is the local decomposition
needed to assemble all poles inside one contour. -/
theorem exists_analyticAt_eventuallyEq_explicitFormulaIntegrand_sub_principalPart_of_order_eq_nat
    {x : ℝ} (hx : 0 < x) {ρ : ℂ} {n : ℕ}
    (hρ1 : ρ ≠ 1) (hρ0 : ρ ≠ 0)
    (horder : analyticOrderAt riemannZeta ρ = n) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G ρ ∧
      (fun z : ℂ => explicitFormulaIntegrand x z -
        (z - ρ)⁻¹ * (-(n : ℂ) * (x : ℂ) ^ ρ / ρ)) =ᶠ[𝓝[≠] ρ] G := by
  rcases
      ZeroFreeRegion.exists_eventuallyEq_neg_logDeriv_riemannZeta_add_order_mul_inv_of_order_eq_nat
        hρ1 horder with ⟨g, hg, hg_ne, hsep⟩
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  let weight : ℂ → ℂ := fun z => (x : ℂ) ^ z / z
  have hpow_diff : Differentiable ℂ (fun z : ℂ => (x : ℂ) ^ z) :=
    (differentiable_id : Differentiable ℂ (fun z : ℂ => z)).const_cpow
      (Or.inl hx0)
  have hweight_diff : DifferentiableOn ℂ weight ({(0 : ℂ)}ᶜ : Set ℂ) := by
    intro z hz
    have hz0 : z ≠ 0 := by simpa using hz
    exact ((hpow_diff z).div differentiableAt_id hz0).differentiableWithinAt
  have hρmem : ρ ∈ ({(0 : ℂ)}ᶜ : Set ℂ) := by simpa using hρ0
  have hzero_nhds : ({(0 : ℂ)}ᶜ : Set ℂ) ∈ 𝓝 ρ :=
    isOpen_compl_singleton.mem_nhds hρmem
  have hweight_analytic : AnalyticAt ℂ weight ρ :=
    (hweight_diff.analyticOnNhd isOpen_compl_singleton) ρ hρmem
  have hdslope_diff :
      DifferentiableOn ℂ (dslope weight ρ) ({(0 : ℂ)}ᶜ : Set ℂ) :=
    (Complex.differentiableOn_dslope hzero_nhds).2 hweight_diff
  have hdslope_analytic : AnalyticAt ℂ (dslope weight ρ) ρ :=
    (hdslope_diff.analyticOnNhd isOpen_compl_singleton) ρ hρmem
  have hg_log : AnalyticAt ℂ (logDeriv g) ρ :=
    hg.deriv.div hg hg_ne
  let G : ℂ → ℂ := fun z =>
    -logDeriv g z * weight z - (n : ℂ) * dslope weight ρ z
  have hG : AnalyticAt ℂ G ρ := by
    exact (hg_log.neg.mul hweight_analytic).sub
      (analyticAt_const.mul hdslope_analytic)
  refine ⟨G, hG, ?_⟩
  filter_upwards [hsep, self_mem_nhdsWithin,
      (eventually_ne_nhds hρ0).filter_mono nhdsWithin_le_nhds]
    with z hz hzρ hz0
  have hz_ne_ρ : z ≠ ρ := Set.mem_compl_singleton_iff.mp hzρ
  have hsolve :
      -logDeriv riemannZeta z =
        -logDeriv g z - (n : ℂ) * (z - ρ)⁻¹ :=
    eq_sub_of_add_eq hz
  simp only [explicitFormulaIntegrand, G, weight]
  rw [hsolve, dslope_of_ne weight hz_ne_ρ]
  simp only [slope, vsub_eq_sub, smul_eq_mul, weight]
  field_simp [hz0, hρ0, hz_ne_ρ]
  ring

/-- At a zeta zero of multiplicity `n`, the explicit-formula integrand has
residue `-n * x^ρ / ρ`. -/
theorem tendsto_sub_mul_explicitFormulaIntegrand_of_order_eq_nat
    {x : ℝ} (hx : 0 < x) {ρ : ℂ} {n : ℕ}
    (hρ1 : ρ ≠ 1) (hρ0 : ρ ≠ 0)
    (horder : analyticOrderAt riemannZeta ρ = n) :
    Tendsto (fun s : ℂ => (s - ρ) * explicitFormulaIntegrand x s)
      (𝓝[≠] ρ) (𝓝 (-(n : ℂ) * (x : ℂ) ^ ρ / ρ)) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hweight :
      Tendsto (fun s : ℂ => (x : ℂ) ^ s / s)
        (𝓝[≠] ρ) (𝓝 ((x : ℂ) ^ ρ / ρ)) := by
    have hcont : ContinuousAt (fun s : ℂ => (x : ℂ) ^ s / s) ρ :=
      (continuousAt_const_cpow hx0).div continuousAt_id hρ0
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hprincipal :=
    (tendsto_sub_mul_neg_logDeriv_riemannZeta_of_order_eq_nat hρ1 horder).mul hweight
  convert hprincipal using 1
  · funext s
    simp only [explicitFormulaIntegrand]
    ring
  · ring_nf

/-- Automatic multiplicity form at any actual zeta zero away from `0` and the
pole `1`. -/
theorem tendsto_sub_mul_explicitFormulaIntegrand_of_zero
    {x : ℝ} (hx : 0 < x) {ρ : ℂ}
    (hρ1 : ρ ≠ 1) (hρ0 : ρ ≠ 0) (hzero : riemannZeta ρ = 0) :
    Tendsto (fun s : ℂ => (s - ρ) * explicitFormulaIntegrand x s)
      (𝓝[≠] ρ)
      (𝓝 (-(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ)) := by
  have _hpositive : 0 < analyticOrderNatAt riemannZeta ρ :=
    ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero hρ1 hzero
  apply tendsto_sub_mul_explicitFormulaIntegrand_of_order_eq_nat hx hρ1 hρ0
  exact
    (ZeroFreeRegion.analyticOrderNatAt_riemannZeta_eq_analyticOrderAt_of_ne_one
      hρ1).symm

/-- Every nontrivial zeta zero contributes its actual analytic multiplicity
times `-x^ρ/ρ` to the explicit-formula residue sum. -/
theorem tendsto_sub_mul_explicitFormulaIntegrand_of_nontrivialZero
    {x : ℝ} (hx : 0 < x) {ρ : ℂ}
    (hρ : RiemannHypothesis.IsNontrivialZero ρ) :
    Tendsto (fun s : ℂ => (s - ρ) * explicitFormulaIntegrand x s)
      (𝓝[≠] ρ)
      (𝓝 (-(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ)) := by
  have hρ1 : ρ ≠ 1 := by
    intro h
    have hre := hρ.2.2
    rw [h] at hre
    norm_num at hre
  have hρ0 : ρ ≠ 0 := by
    intro h
    have hre := hρ.2.1
    rw [h] at hre
    norm_num at hre
  exact tendsto_sub_mul_explicitFormulaIntegrand_of_zero hx hρ1 hρ0 hρ.1

/-- Every trivial zero `-2(n+1)` contributes its actual analytic
multiplicity times `-x^ρ/ρ`. -/
theorem tendsto_sub_mul_explicitFormulaIntegrand_trivialZero
    {x : ℝ} (hx : 0 < x) (n : ℕ) :
    let ρ : ℂ := -2 * ((n : ℂ) + 1)
    Tendsto (fun s : ℂ => (s - ρ) * explicitFormulaIntegrand x s)
      (𝓝[≠] ρ)
      (𝓝 (-(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ)) := by
  let ρ : ℂ := -2 * ((n : ℂ) + 1)
  have hρ1 : ρ ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [ρ] at hre
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hρ0 : ρ ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [ρ] at hre
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hzero : riemannZeta ρ = 0 := by
    simpa [ρ] using riemannZeta_neg_two_mul_nat_add_one n
  exact tendsto_sub_mul_explicitFormulaIntegrand_of_zero hx hρ1 hρ0 hzero

/-- The explicit-formula integrand has residue
`-ζ'(0) / ζ(0)` at the kernel pole `s = 0`. -/
theorem tendsto_mul_explicitFormulaIntegrand_zero
    {x : ℝ} (hx : 0 < x) :
    Tendsto (fun s : ℂ => s * explicitFormulaIntegrand x s)
      (𝓝[≠] (0 : ℂ))
      (𝓝 (-deriv riemannZeta 0 / riemannZeta 0)) := by
  have hzeta0 : riemannZeta (0 : ℂ) ≠ 0 := by
    rw [riemannZeta_zero]
    norm_num
  have hlog :
      Tendsto (fun s : ℂ => -logDeriv riemannZeta s)
        (𝓝[≠] (0 : ℂ)) (𝓝 (-logDeriv riemannZeta 0)) := by
    exact
      (ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_of_ne_one_of_ne_zero
        (z := (0 : ℂ)) (by norm_num) hzeta0).continuousAt.neg.tendsto.mono_left
          nhdsWithin_le_nhds
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hpow :
      Tendsto (fun s : ℂ => (x : ℂ) ^ s)
        (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
    have hcont : ContinuousAt (fun s : ℂ => (x : ℂ) ^ s) 0 :=
      continuousAt_const_cpow hx0
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hmul := hlog.mul hpow
  have heq :
      (fun s : ℂ => s * explicitFormulaIntegrand x s)
        =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun s : ℂ => -logDeriv riemannZeta s * (x : ℂ) ^ s) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : s ≠ 0 := Set.mem_compl_singleton_iff.mp hs
    simp only [explicitFormulaIntegrand]
    field_simp [hs0]
  convert hmul.congr' heq.symm using 1
  simp only [logDeriv_apply, mul_one]
  rw [neg_div]

/-- Subtracting the kernel principal part at `s = 0` leaves an analytic germ.
The coefficient is the constant term `-ζ'(0) / ζ(0)` from the explicit
formula. -/
theorem exists_analyticAt_eventuallyEq_explicitFormulaIntegrand_sub_principalPart_zero
    {x : ℝ} (hx : 0 < x) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧
      (fun z : ℂ => explicitFormulaIntegrand x z - z⁻¹ *
        (-deriv riemannZeta 0 / riemannZeta 0)) =ᶠ[𝓝[≠] (0 : ℂ)] G := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hzeta0 : riemannZeta (0 : ℂ) ≠ 0 := by
    rw [riemannZeta_zero]
    norm_num
  let core : ℂ → ℂ := fun z => -logDeriv riemannZeta z * (x : ℂ) ^ z
  have hpow_diff : Differentiable ℂ (fun z : ℂ => (x : ℂ) ^ z) :=
    (differentiable_id : Differentiable ℂ (fun z : ℂ => z)).const_cpow
      (Or.inl hx0)
  have hcore_analytic : AnalyticAt ℂ core 0 := by
    exact
      (ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_of_ne_one_of_ne_zero
        0 (by norm_num) hzeta0).neg.mul (hpow_diff.analyticAt 0)
  let U : Set ℂ := {z | AnalyticAt ℂ core z}
  have hU_open : IsOpen U := by
    simpa [U] using (isOpen_analyticAt ℂ core)
  have hU_mem : U ∈ 𝓝 (0 : ℂ) := hU_open.mem_nhds hcore_analytic
  have hcore_diff : DifferentiableOn ℂ core U := by
    intro z hz
    exact hz.differentiableAt.differentiableWithinAt
  have hdslope_diff : DifferentiableOn ℂ (dslope core 0) U :=
    (Complex.differentiableOn_dslope hU_mem).2 hcore_diff
  have hdslope_analytic : AnalyticAt ℂ (dslope core 0) 0 :=
    (hdslope_diff.analyticOnNhd hU_open) 0 hcore_analytic
  have hcore_zero : core 0 = -deriv riemannZeta 0 / riemannZeta 0 := by
    simp only [core, logDeriv_apply, cpow_zero, mul_one]
    ring
  refine ⟨dslope core 0, hdslope_analytic, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz0
  have hz_ne_zero : z ≠ 0 := Set.mem_compl_singleton_iff.mp hz0
  simp only [explicitFormulaIntegrand]
  change core z / z - z⁻¹ * (-deriv riemannZeta 0 / riemannZeta 0) = _
  rw [dslope_of_ne core hz_ne_zero]
  simp only [slope, vsub_eq_sub, smul_eq_mul]
  rw [hcore_zero]
  field_simp [hz_ne_zero]
  ring

/-- On every compact set, all principal parts of the concrete explicit-formula
integrand can be subtracted simultaneously.  After correcting the finitely
many removable center values with `toMeromorphicNFOn`, the resulting single
global remainder is analytic on the whole compact set. -/
theorem exists_finite_explicitFormulaIntegrand_analytic_regularized_remainder
    {x : ℝ} (hx : 0 < x) {K : Set ℂ} (hK : IsCompact K) :
    ∃ (poles : Finset ℂ) (residue : ℂ → ℂ),
      (∀ p ∈ poles, p = 0 ∨ p ∈ K) ∧
      (∀ p ∈ poles, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p, residue p =
        if p = 1 then (x : ℂ)
        else if p = 0 then -deriv riemannZeta 0 / riemannZeta 0
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p) ∧
      (∀ z, z ∈ K → z ∉ poles →
        toMeromorphicNFOn
          (fun w : ℂ => explicitFormulaIntegrand x w -
            ∑ p ∈ poles, (w - p)⁻¹ * residue p) K z =
          explicitFormulaIntegrand x z -
            ∑ p ∈ poles, (z - p)⁻¹ * residue p) ∧
      AnalyticOnNhd ℂ
        (toMeromorphicNFOn
          (fun z : ℂ => explicitFormulaIntegrand x z -
            ∑ p ∈ poles, (z - p)⁻¹ * residue p) K) K := by
  classical
  have hzeta_meromorphic : MeromorphicOn riemannZeta K := by
    intro s _hs
    by_cases hs1 : s = 1
    · subst s
      exact ZeroFreeRegion.meromorphicAt_riemannZeta_one
    · exact ZeroFreeRegion.meromorphicAt_riemannZeta_of_ne_one s hs1
  let D := MeromorphicOn.divisor riemannZeta K
  have hDfinite : D.support.Finite := D.finiteSupport hK
  let poles : Finset ℂ := hDfinite.toFinset ∪ {0}
  let residue : ℂ → ℂ := fun p =>
    if p = 1 then (x : ℂ)
    else if p = 0 then -deriv riemannZeta 0 / riemannZeta 0
    else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p
  let raw : ℂ → ℂ := fun z =>
    explicitFormulaIntegrand x z -
      ∑ p ∈ poles, (z - p)⁻¹ * residue p
  have hintegrand_meromorphic :
      MeromorphicOn (explicitFormulaIntegrand x) K := by
    intro z _hz
    exact meromorphic_explicitFormulaIntegrand hx z
  have hprincipal_meromorphic :
      MeromorphicOn
        (fun z : ℂ => ∑ p ∈ poles, (z - p)⁻¹ * residue p) K := by
    apply MeromorphicOn.fun_sum
    intro p z _hz
    exact
      (((MeromorphicAt.id z).sub (MeromorphicAt.const p z)).inv.mul
        (MeromorphicAt.const (residue p) z))
  have hraw_meromorphic : MeromorphicOn raw K := by
    simpa [raw] using hintegrand_meromorphic.sub hprincipal_meromorphic
  have hpoles_mem : ∀ p ∈ poles, p = 0 ∨ p ∈ K := by
    intro p hp
    simp only [poles, Finset.mem_union, hDfinite.mem_toFinset,
      Finset.mem_singleton] at hp
    rcases hp with hp | hp
    · exact Or.inr (D.supportWithinDomain hp)
    · exact Or.inl hp
  have hpoles_classify :
      ∀ p ∈ poles, p = 0 ∨ p = 1 ∨ riemannZeta p = 0 := by
    intro p hp
    by_cases hp0 : p = 0
    · exact Or.inl hp0
    right
    by_cases hp1 : p = 1
    · exact Or.inl hp1
    right
    have hp_support : p ∈ D.support := by
      have hp' := hp
      simp only [poles, Finset.mem_union, hDfinite.mem_toFinset,
        Finset.mem_singleton] at hp'
      exact hp'.resolve_right hp0
    have hpK : p ∈ K := D.supportWithinDomain hp_support
    have hDne : D p ≠ 0 := Function.mem_support.mp hp_support
    have han : AnalyticAt ℂ riemannZeta p :=
      ZeroFreeRegion.analyticOnNhd_riemannZeta_ne_one p hp1
    by_contra hzeta_ne
    have horder_zero : analyticOrderAt riemannZeta p = 0 :=
      han.analyticOrderAt_eq_zero.mpr hzeta_ne
    have hDzero : D p = 0 := by
      rw [MeromorphicOn.divisor_apply hzeta_meromorphic hpK,
        han.meromorphicOrderAt_eq, horder_zero]
      simp
    exact hDne hDzero
  have hraw_analytic_off :
      ∀ s, s ∈ K → s ∉ poles → AnalyticAt ℂ raw s := by
    intro s hsK hs_pole
    have hs0 : s ≠ 0 := by
      intro hs
      subst s
      apply hs_pole
      simp [poles]
    have hs_not_support : s ∉ D.support := by
      intro hs
      apply hs_pole
      simp [poles, hDfinite.mem_toFinset, hs]
    have hDzero : D s = 0 := Function.notMem_support.mp hs_not_support
    have hs1 : s ≠ 1 := by
      intro hs
      subst s
      have hDone : D (1 : ℂ) = (-1 : ℤ) := by
        simpa [D] using
          ZeroFreeRegion.divisor_riemannZeta_pole_one hsK hzeta_meromorphic
      rw [hDzero] at hDone
      norm_num at hDone
    have hzeta : riemannZeta s ≠ 0 := by
      intro hzeta_zero
      have han : AnalyticAt ℂ riemannZeta s :=
        ZeroFreeRegion.analyticOnNhd_riemannZeta_ne_one s hs1
      have hpos : 0 < analyticOrderNatAt riemannZeta s :=
        ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero hs1 hzeta_zero
      have horder :
          analyticOrderAt riemannZeta s =
            (analyticOrderNatAt riemannZeta s : ℕ∞) :=
        (ZeroFreeRegion.analyticOrderNatAt_riemannZeta_eq_analyticOrderAt_of_ne_one
          hs1).symm
      have hDvalue : D s = (analyticOrderNatAt riemannZeta s : ℤ) := by
        rw [MeromorphicOn.divisor_apply hzeta_meromorphic hsK,
          han.meromorphicOrderAt_eq, horder]
        simp
      rw [hDzero] at hDvalue
      have hnat_zero : analyticOrderNatAt riemannZeta s = 0 := by
        exact_mod_cast hDvalue.symm
      exact (Nat.ne_of_gt hpos) hnat_zero
    have hintegrand : AnalyticAt ℂ (explicitFormulaIntegrand x) s :=
      analyticAt_explicitFormulaIntegrand_of_ne_zero_of_ne_one_of_zeta_ne_zero
        hx hs0 hs1 hzeta
    have hsum : AnalyticAt ℂ
        (fun z : ℂ => ∑ p ∈ poles, (z - p)⁻¹ * residue p) s := by
      apply Finset.analyticAt_fun_sum
      intro p hp
      have hps : p ≠ s := by
        intro h
        subst p
        exact hs_pole hp
      exact
        ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hps.symm)).mul
          analyticAt_const
    simpa [raw] using hintegrand.sub hsum
  have hregular :
      AnalyticOnNhd ℂ (toMeromorphicNFOn raw K) K := by
    apply
      ZeroFreeRegion.analyticOnNhd_toMeromorphicNFOn_of_locally_eventuallyEq_analyticAt
        hraw_meromorphic
    intro s hsK
    by_cases hs_pole : s ∈ poles
    · have hown :
          ∃ G : ℂ → ℂ, AnalyticAt ℂ G s ∧
            (fun z : ℂ => explicitFormulaIntegrand x z -
              (z - s)⁻¹ * residue s) =ᶠ[𝓝[≠] s] G := by
        by_cases hs1 : s = 1
        · subst s
          simpa [residue] using
            exists_analyticAt_eventuallyEq_explicitFormulaIntegrand_sub_principalPart_one hx
        · by_cases hs0 : s = 0
          · subst s
            simpa [residue] using
              exists_analyticAt_eventuallyEq_explicitFormulaIntegrand_sub_principalPart_zero hx
          · have hs_support : s ∈ D.support := by
              have hs := hs_pole
              simp only [poles, Finset.mem_union, hDfinite.mem_toFinset,
                Finset.mem_singleton] at hs
              exact hs.resolve_right hs0
            have hDne : D s ≠ 0 := Function.mem_support.mp hs_support
            have han : AnalyticAt ℂ riemannZeta s :=
              ZeroFreeRegion.analyticOnNhd_riemannZeta_ne_one s hs1
            have hzeta : riemannZeta s = 0 := by
              by_contra hzeta_ne
              have horder_zero : analyticOrderAt riemannZeta s = 0 :=
                han.analyticOrderAt_eq_zero.mpr hzeta_ne
              have hDzero : D s = 0 := by
                rw [MeromorphicOn.divisor_apply hzeta_meromorphic hsK,
                  han.meromorphicOrderAt_eq, horder_zero]
                simp
              exact hDne hDzero
            have horder :
                analyticOrderAt riemannZeta s =
                  analyticOrderNatAt riemannZeta s :=
              (ZeroFreeRegion.analyticOrderNatAt_riemannZeta_eq_analyticOrderAt_of_ne_one
                hs1).symm
            simpa [residue, hs1, hs0] using
              exists_analyticAt_eventuallyEq_explicitFormulaIntegrand_sub_principalPart_of_order_eq_nat
                hx hs1 hs0 horder
      rcases hown with ⟨G, hG, hlocal⟩
      let Gregular : ℂ → ℂ := fun z =>
        G z - ∑ p ∈ poles.erase s, (z - p)⁻¹ * residue p
      have hsum : AnalyticAt ℂ
          (fun z : ℂ => ∑ p ∈ poles.erase s, (z - p)⁻¹ * residue p) s := by
        apply Finset.analyticAt_fun_sum
        intro p hp
        have hps : p ≠ s := Finset.ne_of_mem_erase hp
        exact
          ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hps.symm)).mul
            analyticAt_const
      refine ⟨Gregular, hG.sub hsum, ?_⟩
      filter_upwards [hlocal] with z hz
      dsimp [raw, Gregular]
      rw [← Finset.sum_erase_add _ _ hs_pole]
      have hz' : explicitFormulaIntegrand x z =
          G z + (z - s)⁻¹ * residue s :=
        sub_eq_iff_eq_add.mp hz
      rw [hz']
      ring
    · exact ⟨raw, hraw_analytic_off s hsK hs_pole, Filter.EventuallyEq.rfl⟩
  have hoff_eq : ∀ z, z ∈ K → z ∉ poles →
      toMeromorphicNFOn raw K z = raw z := by
    intro z hzK hz_pole
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hraw_meromorphic hzK]
    rw [toMeromorphicNFAt_eq_self.2
      (hraw_analytic_off z hzK hz_pole).meromorphicNFAt]
  refine ⟨poles, residue, hpoles_mem, hpoles_classify, ?_, ?_, ?_⟩
  · intro p
    rfl
  · simpa [raw] using hoff_eq
  · simpa [raw] using hregular

end ExplicitFormulaResidues
end PrimeNumberTheorem
