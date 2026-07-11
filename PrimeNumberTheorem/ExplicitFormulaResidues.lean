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

end ExplicitFormulaResidues
end PrimeNumberTheorem
