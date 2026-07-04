/-
# Meromorphic Auxiliaries for the Riemann Zeta Function on a Closed Ball

## Overview

This file establishes basic meromorphic properties of `riemannZeta` needed by both:
- chain A (Borel–Carathéodory zero-free-region path)
- chain B (rectangle-integral residue counting)

## Verified results

1. `meromorphicAt_riemannZeta_of_ne_one` — ζ is meromorphic at every point ≠ 1.
2. `meromorphicAt_riemannZeta_one` — ζ is meromorphic at its pole.
3. `meromorphicOn_riemannZeta_closedBall` — ζ is meromorphic on any closed ball.

## Dependencies

- Mathlib (`riemannZeta`, complex analysis, meromorphic API)
- RiemannExplorer (`differentiableAt_riemannZeta`)
-/

import Mathlib
import RiemannExplorer
import ZeroFreeRegion

open Complex BigOperators Filter Nat Topology MeasureTheory Asymptotics
open scoped ArithmeticFunction LSeries.notation
open MeromorphicAt MeromorphicOn Metric Real

namespace ZeroFreeRegion

/-- ζ is differentiable on the open set {z | z ≠ 1}. -/
lemma differentiableOn_riemannZeta_ne_one :
    DifferentiableOn ℂ riemannZeta ({z : ℂ | z ≠ 1} : Set ℂ) := by
  intro z hz
  exact (differentiableAt_riemannZeta hz).differentiableWithinAt

/-- ζ is analytic on the open set {z | z ≠ 1}. -/
lemma analyticOnNhd_riemannZeta_ne_one :
    AnalyticOnNhd ℂ riemannZeta ({z : ℂ | z ≠ 1} : Set ℂ) :=
  differentiableOn_riemannZeta_ne_one.analyticOnNhd isOpen_compl_singleton

/-- ζ is meromorphic at every point `s ≠ 1`. -/
lemma meromorphicAt_riemannZeta_of_ne_one (s : ℂ) (hs : s ≠ 1) :
    MeromorphicAt riemannZeta s :=
  (analyticOnNhd_riemannZeta_ne_one s hs).meromorphicAt

/-- The analytic regular part in the local decomposition of ζ at `s = 1`. -/
noncomputable def riemannZetaRegularAtOne (s : ℂ) : ℂ :=
  (completedRiemannZeta₀ s - 1 / s) * (Gammaℝ s)⁻¹

/-- The nonzero analytic unit in the local simple-pole decomposition of ζ at
`s = 1`.

On a punctured neighborhood of `1`,
`ζ(s) = (s - 1)⁻¹ * riemannZetaPoleUnitAtOne(s)`. -/
noncomputable def riemannZetaPoleUnitAtOne (s : ℂ) : ℂ :=
  (s - 1) * riemannZetaRegularAtOne s + (Gammaℝ s)⁻¹

/-- The analytic local model for the reciprocal of ζ at its pole `1`.

On a punctured neighborhood of `1`, this agrees with `1 / ζ(s)`.
The model has the correct value at the center, unlike Mathlib's global
`riemannZeta` value at the pole. -/
noncomputable def riemannZetaReciprocalModelAtOne (s : ℂ) : ℂ :=
  (s - 1) * (riemannZetaPoleUnitAtOne s)⁻¹

/-- The regular part in the local decomposition of ζ at `1` is analytic. -/
lemma analyticAt_riemannZetaRegularAtOne :
    AnalyticAt ℂ riemannZetaRegularAtOne 1 := by
  have hcompleted : AnalyticAt ℂ completedRiemannZeta₀ 1 :=
    differentiable_completedZeta₀.analyticAt 1
  have hone_div : AnalyticAt ℂ (fun s : ℂ => 1 / s) 1 := by
    exact (analyticAt_const.div analyticAt_id one_ne_zero)
  have hgamma_inv : AnalyticAt ℂ (fun s : ℂ => (Gammaℝ s)⁻¹) 1 :=
    differentiable_Gammaℝ_inv.analyticAt 1
  exact ((hcompleted.sub hone_div).mul hgamma_inv)

/-- The pole unit in the local decomposition of ζ at `1` is analytic. -/
lemma analyticAt_riemannZetaPoleUnitAtOne :
    AnalyticAt ℂ riemannZetaPoleUnitAtOne 1 := by
  have hgamma_inv : AnalyticAt ℂ (fun s : ℂ => (Gammaℝ s)⁻¹) 1 :=
    differentiable_Gammaℝ_inv.analyticAt 1
  unfold riemannZetaPoleUnitAtOne
  exact ((analyticAt_id.sub analyticAt_const).mul
    analyticAt_riemannZetaRegularAtOne).add hgamma_inv

lemma riemannZetaPoleUnitAtOne_one :
    riemannZetaPoleUnitAtOne 1 = 1 := by
  simp [riemannZetaPoleUnitAtOne]

/-- The pole unit is nonzero near `1`. -/
lemma eventually_ne_zero_riemannZetaPoleUnitAtOne :
    ∀ᶠ s in 𝓝 (1 : ℂ), riemannZetaPoleUnitAtOne s ≠ 0 :=
  analyticAt_riemannZetaPoleUnitAtOne.continuousAt.eventually_ne
    (by rw [riemannZetaPoleUnitAtOne_one]; exact one_ne_zero)

/-- Local decomposition of ζ at `1` as a regular analytic part plus a simple
pole term. -/
lemma eventuallyEq_riemannZeta_regular_add_poleAtOne :
    (fun s : ℂ =>
      riemannZetaRegularAtOne s + (s - 1)⁻¹ * (Gammaℝ s)⁻¹)
      =ᶠ[𝓝[≠] (1 : ℂ)] riemannZeta := by
  filter_upwards [eventually_ne_nhdsWithin one_ne_zero, self_mem_nhdsWithin] with s hs0 _hs1
  simp only [riemannZetaRegularAtOne]
  rw [riemannZeta_def_of_ne_zero hs0, completedRiemannZeta_eq, div_eq_mul_inv]
  have hden : (1 - s) = -(s - 1) := by ring
  rw [hden]
  simp [div_eq_mul_inv]
  have hinv : (s - 1)⁻¹ = - (1 - s)⁻¹ := by
    have hlin : (s - 1) = -(1 - s) := by ring
    rw [hlin, inv_neg]
  rw [hinv]
  ring

/-- ζ is meromorphic at `1`.

The proof rewrites ζ on a punctured neighborhood of `1` as the sum of an
analytic regular part and the simple pole term
`(s - 1)⁻¹ * (Gammaℝ s)⁻¹`. -/
lemma meromorphicAt_riemannZeta_one :
    MeromorphicAt riemannZeta 1 := by
  let pole : ℂ → ℂ := fun s =>
    (s - 1)⁻¹ * (Gammaℝ s)⁻¹
  have hgamma_inv : AnalyticAt ℂ (fun s : ℂ => (Gammaℝ s)⁻¹) 1 :=
    differentiable_Gammaℝ_inv.analyticAt 1
  have hsub : MeromorphicAt (fun s : ℂ => s - 1) 1 :=
    (analyticAt_id.sub analyticAt_const).meromorphicAt
  have hpole : MeromorphicAt pole 1 := by
    exact hsub.inv.mul hgamma_inv.meromorphicAt
  have hsum :
      MeromorphicAt
        (fun s : ℂ => riemannZetaRegularAtOne s + pole s) 1 :=
    analyticAt_riemannZetaRegularAtOne.meromorphicAt.add hpole
  exact hsum.congr eventuallyEq_riemannZeta_regular_add_poleAtOne

/-- Local simple-pole normal form for ζ at `1`. -/
lemma eventuallyEq_riemannZeta_simplePoleAtOne :
    (fun s : ℂ =>
      (s - 1) ^ (-1 : ℤ) • riemannZetaPoleUnitAtOne s)
      =ᶠ[𝓝[≠] (1 : ℂ)] riemannZeta := by
  filter_upwards [eventuallyEq_riemannZeta_regular_add_poleAtOne,
    self_mem_nhdsWithin] with s hζ hs1
  rw [← hζ]
  have hs1' : s ≠ 1 := Set.mem_compl_singleton_iff.mp hs1
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1'
  simp only [riemannZetaPoleUnitAtOne, smul_eq_mul, zpow_neg, zpow_one]
  rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hsub, one_mul]

/-- ζ is nonzero in a punctured neighborhood of its pole `1`. -/
lemma eventually_ne_zero_riemannZeta_nhdsNE_one :
    ∀ᶠ s in 𝓝[≠] (1 : ℂ), riemannZeta s ≠ 0 := by
  filter_upwards [eventuallyEq_riemannZeta_simplePoleAtOne,
    self_mem_nhdsWithin,
    eventually_ne_zero_riemannZetaPoleUnitAtOne.filter_mono nhdsWithin_le_nhds]
    with s hζ hs1 hunit
  rw [← hζ]
  have hs1' : s ≠ 1 := Set.mem_compl_singleton_iff.mp hs1
  exact smul_ne_zero (zpow_ne_zero _ (sub_ne_zero.mpr hs1')) hunit

/-- Reciprocal local model: near the pole, `1 / ζ(s)` is `(s-1)` times
the inverse pole unit. -/
lemma eventuallyEq_inv_riemannZeta_simpleZeroAtOne :
    (fun s : ℂ => (riemannZeta s)⁻¹)
      =ᶠ[𝓝[≠] (1 : ℂ)]
      riemannZetaReciprocalModelAtOne := by
  filter_upwards [eventuallyEq_riemannZeta_simplePoleAtOne,
    self_mem_nhdsWithin] with s hζ hs1
  have hs1' : s ≠ 1 := Set.mem_compl_singleton_iff.mp hs1
  rw [← hζ]
  simp only [riemannZetaReciprocalModelAtOne, smul_eq_mul, zpow_neg, zpow_one]
  rw [mul_inv_rev, inv_inv]
  ring

/-- The reciprocal local model is analytic at `1`. -/
lemma analyticAt_riemannZetaReciprocalModelAtOne :
    AnalyticAt ℂ riemannZetaReciprocalModelAtOne 1 := by
  unfold riemannZetaReciprocalModelAtOne
  exact (analyticAt_id.sub analyticAt_const).mul
    (analyticAt_riemannZetaPoleUnitAtOne.inv
      (by rw [riemannZetaPoleUnitAtOne_one]; exact one_ne_zero))

/-- The reciprocal local model vanishes at `1`. -/
lemma riemannZetaReciprocalModelAtOne_one :
    riemannZetaReciprocalModelAtOne 1 = 0 := by
  simp [riemannZetaReciprocalModelAtOne]

/-- The reciprocal local model has a simple zero at `1`. -/
lemma deriv_riemannZetaReciprocalModelAtOne_one :
    deriv riemannZetaReciprocalModelAtOne 1 = 1 := by
  unfold riemannZetaReciprocalModelAtOne
  have hleft : DifferentiableAt ℂ (fun s : ℂ => s - 1) 1 :=
    differentiableAt_id.sub (differentiableAt_const (1 : ℂ))
  have hright :
      DifferentiableAt ℂ (fun s : ℂ => (riemannZetaPoleUnitAtOne s)⁻¹) 1 :=
    analyticAt_riemannZetaPoleUnitAtOne.differentiableAt.inv
      (by rw [riemannZetaPoleUnitAtOne_one]; exact one_ne_zero)
  change deriv ((fun s : ℂ => s - 1) *
      fun s : ℂ => (riemannZetaPoleUnitAtOne s)⁻¹) 1 = 1
  rw [deriv_mul hleft hright]
  simp [riemannZetaPoleUnitAtOne_one]

/-- The reciprocal local model has logarithmic residue `1` at its simple zero. -/
lemma tendsto_mul_logDeriv_riemannZetaReciprocalModelAtOne :
    Tendsto
      (fun w : ℂ =>
        (w - 1) * logDeriv riemannZetaReciprocalModelAtOne w)
      (𝓝[≠] (1 : ℂ)) (𝓝 1) :=
  analyticAt_riemannZetaReciprocalModelAtOne.tendsto_mul_logDeriv_simple_zero
    riemannZetaReciprocalModelAtOne_one
    (by rw [deriv_riemannZetaReciprocalModelAtOne_one]; exact one_ne_zero)

/-- The logarithmic derivative of `1 / ζ` agrees with that of the reciprocal
local model in a punctured neighborhood of the pole. -/
lemma eventuallyEq_logDeriv_inv_riemannZeta_reciprocalModelAtOne :
    (fun s : ℂ => logDeriv (fun z : ℂ => (riemannZeta z)⁻¹) s)
      =ᶠ[𝓝[≠] (1 : ℂ)]
    (fun s : ℂ => logDeriv riemannZetaReciprocalModelAtOne s) := by
  have hval :
      (fun s : ℂ => (riemannZeta s)⁻¹)
        =ᶠ[𝓝[≠] (1 : ℂ)] riemannZetaReciprocalModelAtOne :=
    eventuallyEq_inv_riemannZeta_simpleZeroAtOne
  have hderiv := hval.nhdsNE_deriv
  filter_upwards [hval, hderiv] with s hs hds
  simp [logDeriv_apply, hs, hds]

/-- The reciprocal of ζ has logarithmic residue `1` at the pole of ζ. -/
lemma tendsto_mul_logDeriv_inv_riemannZeta_simpleZeroAtOne :
    Tendsto
      (fun w : ℂ =>
        (w - 1) * logDeriv (fun z : ℂ => (riemannZeta z)⁻¹) w)
      (𝓝[≠] (1 : ℂ)) (𝓝 1) := by
  refine tendsto_mul_logDeriv_riemannZetaReciprocalModelAtOne.congr' ?_
  filter_upwards [eventuallyEq_logDeriv_inv_riemannZeta_reciprocalModelAtOne]
    with s hs
  simp [hs]

/-- In a punctured neighborhood of `1`, the logarithmic derivative of
`1 / ζ` is the negative of the logarithmic derivative of ζ. -/
lemma eventuallyEq_logDeriv_inv_riemannZeta :
    (fun s : ℂ => logDeriv (fun z : ℂ => (riemannZeta z)⁻¹) s)
      =ᶠ[𝓝[≠] (1 : ℂ)]
    (fun s : ℂ => -logDeriv riemannZeta s) := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_ne_zero_riemannZeta_nhdsNE_one] with s hs1 _hζ
  have hs1' : s ≠ 1 := Set.mem_compl_singleton_iff.mp hs1
  have hpow :=
    logDeriv_fun_zpow (f := riemannZeta) (x := s)
      (differentiableAt_riemannZeta hs1') (-1)
  simpa [zpow_neg, zpow_one] using hpow

/-- The logarithmic derivative of ζ has logarithmic residue `-1` at the
simple pole `s = 1`.

Equivalently, `(s - 1) * ζ'(s) / ζ(s)` tends to `-1` as `s → 1` away from
the pole.  This is the local principal-part input needed before applying
Borel-Carathéodory/Jensen estimates to `ζ'/ζ`. -/
lemma tendsto_mul_logDeriv_riemannZeta_simplePoleAtOne :
    Tendsto (fun w : ℂ => (w - 1) * logDeriv riemannZeta w)
      (𝓝[≠] (1 : ℂ)) (𝓝 (-1 : ℂ)) := by
  have hneg :
      Tendsto
        (fun w : ℂ =>
          -((w - 1) * logDeriv (fun z : ℂ => (riemannZeta z)⁻¹) w))
        (𝓝[≠] (1 : ℂ)) (𝓝 (-1 : ℂ)) := by
    simpa using tendsto_mul_logDeriv_inv_riemannZeta_simpleZeroAtOne.neg
  refine hneg.congr' ?_
  filter_upwards [eventuallyEq_logDeriv_inv_riemannZeta] with s hs
  rw [hs]
  ring

/-- Local boundedness of the normalized logarithmic derivative at the zeta pole.

This is a direct norm-bound corollary of
`tendsto_mul_logDeriv_riemannZeta_simplePoleAtOne`; it packages the
principal-part limit into a shape that later Borel-Carathéodory/Jensen estimates
can consume. -/
lemma eventually_norm_mul_logDeriv_riemannZeta_le_two :
    ∀ᶠ s in 𝓝[≠] (1 : ℂ),
      ‖(s - 1) * logDeriv riemannZeta s‖ ≤ 2 := by
  have hnorm :
      Tendsto
        (fun s : ℂ => ‖(s - 1) * logDeriv riemannZeta s‖)
        (𝓝[≠] (1 : ℂ)) (𝓝 (1 : ℝ)) := by
    simpa using tendsto_mul_logDeriv_riemannZeta_simplePoleAtOne.norm
  exact hnorm.eventually (eventually_le_nhds (by norm_num : (1 : ℝ) < 2))

/-- Flexible local boundedness of the normalized logarithmic derivative.

Since `(s - 1) * logDeriv riemannZeta s` tends to `-1`, its norm is eventually
less than any real constant strictly larger than `1`. -/
lemma eventually_norm_mul_logDeriv_riemannZeta_lt_const
    (C : ℝ) (hC : 1 < C) :
    ∀ᶠ s in 𝓝[≠] (1 : ℂ),
      ‖(s - 1) * logDeriv riemannZeta s‖ < C := by
  have hnorm :
      Tendsto
        (fun s : ℂ => ‖(s - 1) * logDeriv riemannZeta s‖)
        (𝓝[≠] (1 : ℂ)) (𝓝 (1 : ℝ)) := by
    simpa using tendsto_mul_logDeriv_riemannZeta_simplePoleAtOne.norm
  exact hnorm.eventually (eventually_lt_nhds hC)

/-- Local pole-order norm bound for the zeta logarithmic derivative.

Near `1` away from the pole,
`logDeriv riemannZeta` is bounded by a constant multiple of `1 / ‖s - 1‖`.
This is still only a local bound; it is not the global vertical-strip growth
estimate needed for the quantitative zero-free region. -/
lemma eventually_norm_logDeriv_riemannZeta_le_two_div_norm_sub_one :
    ∀ᶠ s in 𝓝[≠] (1 : ℂ),
      ‖logDeriv riemannZeta s‖ ≤ 2 / ‖s - 1‖ := by
  filter_upwards [eventually_norm_mul_logDeriv_riemannZeta_le_two,
    self_mem_nhdsWithin] with s hbound hs1
  have hs_ne : s - 1 ≠ 0 :=
    sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hs1)
  have hnorm_pos : 0 < ‖s - 1‖ := norm_pos_iff.mpr hs_ne
  have hmul : ‖logDeriv riemannZeta s‖ * ‖s - 1‖ ≤ 2 := by
    have hmul' : ‖s - 1‖ * ‖logDeriv riemannZeta s‖ ≤ 2 := by
      simpa [norm_mul] using hbound
    simpa [mul_comm] using hmul'
  exact (le_div_iff₀ hnorm_pos).mpr hmul

/-- Flexible local pole-order norm bound for the zeta logarithmic derivative.

For every constant `C > 1`, the logarithmic derivative is eventually bounded by
`C / ‖s - 1‖` near the pole. -/
lemma eventually_norm_logDeriv_riemannZeta_lt_const_div_norm_sub_one
    (C : ℝ) (hC : 1 < C) :
    ∀ᶠ s in 𝓝[≠] (1 : ℂ),
      ‖logDeriv riemannZeta s‖ < C / ‖s - 1‖ := by
  filter_upwards [eventually_norm_mul_logDeriv_riemannZeta_lt_const C hC,
    self_mem_nhdsWithin] with s hbound hs1
  have hs_ne : s - 1 ≠ 0 :=
    sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hs1)
  have hnorm_pos : 0 < ‖s - 1‖ := norm_pos_iff.mpr hs_ne
  have hmul : ‖logDeriv riemannZeta s‖ * ‖s - 1‖ < C := by
    have hmul' : ‖s - 1‖ * ‖logDeriv riemannZeta s‖ < C := by
      simpa [norm_mul] using hbound
    simpa [mul_comm] using hmul'
  exact (lt_div_iff₀ hnorm_pos).mpr hmul

/-- Eventual pole-order bound near `1` in explicit quotient notation `ζ'/ζ`. -/
lemma eventually_norm_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one :
    ∀ᶠ s in 𝓝[≠] (1 : ℂ),
      ‖deriv riemannZeta s / riemannZeta s‖ ≤ 2 / ‖s - 1‖ := by
  filter_upwards [eventually_norm_logDeriv_riemannZeta_le_two_div_norm_sub_one]
    with s hs
  simpa [logDeriv_apply] using hs

/-- Flexible eventual pole-order bound near `1` in explicit quotient notation
`ζ'/ζ`. -/
lemma eventually_norm_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one
    (C : ℝ) (hC : 1 < C) :
    ∀ᶠ s in 𝓝[≠] (1 : ℂ),
      ‖deriv riemannZeta s / riemannZeta s‖ < C / ‖s - 1‖ := by
  filter_upwards [eventually_norm_logDeriv_riemannZeta_lt_const_div_norm_sub_one C hC]
    with s hs
  simpa [logDeriv_apply] using hs

/-- Eventual pole-order bound near `1` for the signed quotient `-ζ'/ζ`. -/
lemma eventually_norm_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one :
    ∀ᶠ s in 𝓝[≠] (1 : ℂ),
      ‖-deriv riemannZeta s / riemannZeta s‖ ≤ 2 / ‖s - 1‖ := by
  filter_upwards [eventually_norm_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one]
    with s hs
  calc
    ‖-deriv riemannZeta s / riemannZeta s‖ =
        ‖deriv riemannZeta s / riemannZeta s‖ := by
          rw [neg_div, norm_neg]
    _ ≤ 2 / ‖s - 1‖ := hs

/-- Flexible eventual pole-order bound near `1` for the signed quotient
`-ζ'/ζ`. -/
lemma eventually_norm_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one
    (C : ℝ) (hC : 1 < C) :
    ∀ᶠ s in 𝓝[≠] (1 : ℂ),
      ‖-deriv riemannZeta s / riemannZeta s‖ < C / ‖s - 1‖ := by
  filter_upwards [eventually_norm_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one C hC]
    with s hs
  calc
    ‖-deriv riemannZeta s / riemannZeta s‖ =
        ‖deriv riemannZeta s / riemannZeta s‖ := by
          rw [neg_div, norm_neg]
    _ < C / ‖s - 1‖ := hs

/-- Eventual real-part pole-order bound near `1` for the signed quotient
`-ζ'/ζ`. -/
lemma eventually_abs_re_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one :
    ∀ᶠ s in 𝓝[≠] (1 : ℂ),
      |(-deriv riemannZeta s / riemannZeta s).re| ≤ 2 / ‖s - 1‖ := by
  filter_upwards
    [eventually_norm_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one]
    with s hs
  exact le_trans (abs_re_le_norm (-deriv riemannZeta s / riemannZeta s)) hs

/-- Flexible eventual real-part pole-order bound near `1` for the signed
quotient `-ζ'/ζ`. -/
lemma eventually_abs_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one
    (C : ℝ) (hC : 1 < C) :
    ∀ᶠ s in 𝓝[≠] (1 : ℂ),
      |(-deriv riemannZeta s / riemannZeta s).re| < C / ‖s - 1‖ := by
  filter_upwards
    [eventually_norm_logDeriv_riemannZeta_lt_const_div_norm_sub_one C hC]
    with s hs
  calc
    |(-deriv riemannZeta s / riemannZeta s).re| ≤
        ‖-deriv riemannZeta s / riemannZeta s‖ :=
          abs_re_le_norm (-deriv riemannZeta s / riemannZeta s)
    _ = ‖logDeriv riemannZeta s‖ := by
      rw [logDeriv_apply, neg_div, norm_neg]
    _ < C / ‖s - 1‖ := hs

/-- Flexible eventual one-sided real-part pole-order bound near `1` for
`-ζ'/ζ`. -/
lemma eventually_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one
    (C : ℝ) (hC : 1 < C) :
    ∀ᶠ s in 𝓝[≠] (1 : ℂ),
      (-deriv riemannZeta s / riemannZeta s).re < C / ‖s - 1‖ := by
  filter_upwards
    [eventually_abs_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one C hC]
    with s hs
  exact lt_of_le_of_lt (le_abs_self _) hs

/-- Punctured-ball form of the local pole-order norm bound for the zeta
logarithmic derivative.

This is often easier to use in later disk estimates than the raw
`eventually` form: inside a sufficiently small punctured ball around `1`,
`logDeriv riemannZeta` is bounded by `2 / ‖s - 1‖`. -/
lemma exists_punctured_ball_norm_logDeriv_riemannZeta_le_two_div_norm_sub_one :
    ∃ r > 0, ∀ s : ℂ, s ≠ 1 → dist s 1 < r →
      ‖logDeriv riemannZeta s‖ ≤ 2 / ‖s - 1‖ := by
  have hmem :
      {s : ℂ | ‖logDeriv riemannZeta s‖ ≤ 2 / ‖s - 1‖}
        ∈ 𝓝[{1}ᶜ] (1 : ℂ) :=
    eventually_norm_logDeriv_riemannZeta_le_two_div_norm_sub_one
  rcases Metric.mem_nhdsWithin_iff.mp hmem with ⟨r, hr_pos, hr_sub⟩
  refine ⟨r, hr_pos, ?_⟩
  intro s hs_ne hs_dist
  exact hr_sub ⟨by simpa [Metric.mem_ball] using hs_dist,
    Set.mem_compl_singleton_iff.mpr hs_ne⟩

/-- Closed punctured-ball form of the same local pole-order norm bound.

The radius is obtained by shrinking the open-ball radius.  This is convenient
for later estimates on compact closed disks around the pole. -/
lemma exists_punctured_closedBall_norm_logDeriv_riemannZeta_le_two_div_norm_sub_one :
    ∃ r > 0, ∀ s : ℂ, s ≠ 1 → dist s 1 ≤ r →
      ‖logDeriv riemannZeta s‖ ≤ 2 / ‖s - 1‖ := by
  rcases exists_punctured_ball_norm_logDeriv_riemannZeta_le_two_div_norm_sub_one
    with ⟨r, hr_pos, hball⟩
  refine ⟨r / 2, half_pos hr_pos, ?_⟩
  intro s hs_ne hs_dist
  exact hball s hs_ne (lt_of_le_of_lt hs_dist (half_lt_self hr_pos))

/-- Closed punctured-ball pole-order bound in the explicit quotient notation
`ζ'/ζ`.  This is the form used by later quantitative zero-free estimates. -/
lemma exists_punctured_closedBall_norm_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one :
    ∃ r > 0, ∀ s : ℂ, s ≠ 1 → dist s 1 ≤ r →
      ‖deriv riemannZeta s / riemannZeta s‖ ≤ 2 / ‖s - 1‖ := by
  rcases exists_punctured_closedBall_norm_logDeriv_riemannZeta_le_two_div_norm_sub_one
    with ⟨r, hr_pos, hbound⟩
  refine ⟨r, hr_pos, ?_⟩
  intro s hs_ne hs_dist
  simpa [logDeriv_apply] using hbound s hs_ne hs_dist

/-- Closed punctured-ball flexible pole-order bound in quotient notation
`ζ'/ζ`. -/
lemma exists_punctured_closedBall_norm_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one
    (C : ℝ) (hC : 1 < C) :
    ∃ r > 0, ∀ s : ℂ, s ≠ 1 → dist s 1 ≤ r →
      ‖deriv riemannZeta s / riemannZeta s‖ < C / ‖s - 1‖ := by
  have hmem :
      {s : ℂ | ‖deriv riemannZeta s / riemannZeta s‖ <
          C / ‖s - 1‖} ∈ 𝓝[{1}ᶜ] (1 : ℂ) :=
    eventually_norm_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one C hC
  rcases Metric.mem_nhdsWithin_iff.mp hmem with ⟨r, hr_pos, hr_sub⟩
  refine ⟨r / 2, half_pos hr_pos, ?_⟩
  intro s hs_ne hs_dist
  exact hr_sub ⟨by
    exact lt_of_le_of_lt hs_dist (half_lt_self hr_pos),
    Set.mem_compl_singleton_iff.mpr hs_ne⟩

/-- Closed punctured-ball pole-order bound for the negative logarithmic
derivative `-ζ'/ζ`, matching the sign convention of the 3-4-1 inequality. -/
lemma exists_punctured_closedBall_norm_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one :
    ∃ r > 0, ∀ s : ℂ, s ≠ 1 → dist s 1 ≤ r →
      ‖-deriv riemannZeta s / riemannZeta s‖ ≤ 2 / ‖s - 1‖ := by
  rcases exists_punctured_closedBall_norm_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one
    with ⟨r, hr_pos, hbound⟩
  refine ⟨r, hr_pos, ?_⟩
  intro s hs_ne hs_dist
  calc
    ‖-deriv riemannZeta s / riemannZeta s‖ =
        ‖deriv riemannZeta s / riemannZeta s‖ := by
          rw [neg_div, norm_neg]
    _ ≤ 2 / ‖s - 1‖ := hbound s hs_ne hs_dist

/-- Closed punctured-ball flexible pole-order bound for `-ζ'/ζ`. -/
lemma exists_punctured_closedBall_norm_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one
    (C : ℝ) (hC : 1 < C) :
    ∃ r > 0, ∀ s : ℂ, s ≠ 1 → dist s 1 ≤ r →
      ‖-deriv riemannZeta s / riemannZeta s‖ < C / ‖s - 1‖ := by
  rcases exists_punctured_closedBall_norm_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one
      C hC with ⟨r, hr_pos, hbound⟩
  refine ⟨r, hr_pos, ?_⟩
  intro s hs_ne hs_dist
  calc
    ‖-deriv riemannZeta s / riemannZeta s‖ =
        ‖deriv riemannZeta s / riemannZeta s‖ := by
          rw [neg_div, norm_neg]
    _ < C / ‖s - 1‖ := hbound s hs_ne hs_dist

/-- Closed punctured-ball real-part pole-order bound for `-ζ'/ζ`. -/
lemma exists_punctured_closedBall_abs_re_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one :
    ∃ r > 0, ∀ s : ℂ, s ≠ 1 → dist s 1 ≤ r →
      |(-deriv riemannZeta s / riemannZeta s).re| ≤ 2 / ‖s - 1‖ := by
  rcases exists_punctured_closedBall_norm_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one
    with ⟨r, hr_pos, hbound⟩
  refine ⟨r, hr_pos, ?_⟩
  intro s hs_ne hs_dist
  exact le_trans (abs_re_le_norm (-deriv riemannZeta s / riemannZeta s))
    (hbound s hs_ne hs_dist)

/-- Closed punctured-ball real-part pole-order bound for `-ζ'/ζ`, with any
constant `C > 1`. -/
lemma exists_punctured_closedBall_abs_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one
    (C : ℝ) (hC : 1 < C) :
    ∃ r > 0, ∀ s : ℂ, s ≠ 1 → dist s 1 ≤ r →
      |(-deriv riemannZeta s / riemannZeta s).re| < C / ‖s - 1‖ := by
  have hmem :
      {s : ℂ | |(-deriv riemannZeta s / riemannZeta s).re| <
          C / ‖s - 1‖} ∈ 𝓝[{1}ᶜ] (1 : ℂ) :=
    eventually_abs_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one C hC
  rcases Metric.mem_nhdsWithin_iff.mp hmem with ⟨r, hr_pos, hr_sub⟩
  refine ⟨r / 2, half_pos hr_pos, ?_⟩
  intro s hs_ne hs_dist
  exact hr_sub ⟨by
    exact lt_of_le_of_lt hs_dist (half_lt_self hr_pos),
    Set.mem_compl_singleton_iff.mpr hs_ne⟩

/-- Closed punctured-ball one-sided real-part pole-order bound for `-ζ'/ζ`,
with any constant `C > 1`. -/
lemma exists_punctured_closedBall_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one
    (C : ℝ) (hC : 1 < C) :
    ∃ r > 0, ∀ s : ℂ, s ≠ 1 → dist s 1 ≤ r →
      (-deriv riemannZeta s / riemannZeta s).re < C / ‖s - 1‖ := by
  rcases exists_punctured_closedBall_abs_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one
      C hC with ⟨r, hr_pos, hbound⟩
  refine ⟨r, hr_pos, ?_⟩
  intro s hs_ne hs_dist
  exact lt_of_le_of_lt (le_abs_self _) (hbound s hs_ne hs_dist)

/-- Real-axis specialization of the local pole-order norm bound for `-ζ'/ζ`
with the concrete constant `2`.

For real `σ > 1` sufficiently close to `1`, this rewrites the complex local
bound `‖-ζ'/ζ(s)‖ ≤ 2 / ‖s - 1‖` as `‖-ζ'/ζ(σ)‖ ≤ 2 / (σ - 1)`. -/
lemma exists_rightNeighborhood_norm_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_sub_one :
    ∃ d : ℝ, 0 < d ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 1 + d →
      ‖-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖ ≤ 2 / (σ - 1) := by
  rcases exists_punctured_closedBall_norm_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one
    with ⟨r, hr_pos, hbound⟩
  refine ⟨r, hr_pos, ?_⟩
  intro σ hσ_gt hσ_le
  have hσ_ne_one : σ ≠ 1 := ne_of_gt hσ_gt
  have hs_ne : (σ : ℂ) ≠ 1 := by
    intro hs
    exact hσ_ne_one (by simpa using congrArg Complex.re hs)
  have hdist : dist (σ : ℂ) (1 : ℂ) ≤ r := by
    have hdist_eq : dist (σ : ℂ) (1 : ℂ) = |σ - 1| := by
      simpa using Complex.isometry_ofReal.dist_eq σ 1
    have habs_eq : |σ - 1| = σ - 1 := abs_of_nonneg (sub_nonneg.mpr hσ_gt.le)
    rw [hdist_eq, habs_eq]
    linarith
  have hnorm_eq : ‖(σ : ℂ) - 1‖ = σ - 1 := by
    have hnorm_eq_abs : ‖(σ : ℂ) - 1‖ = |σ - 1| := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
      simpa using (RCLike.norm_ofReal (K := ℂ) (σ - 1))
    rw [hnorm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hσ_gt.le)]
  simpa [hnorm_eq] using hbound (σ : ℂ) hs_ne hdist

/-- Real-axis specialization of the local pole-order real-part bound for
`-ζ'/ζ` with the concrete constant `2`. -/
lemma exists_rightNeighborhood_abs_re_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_sub_one :
    ∃ d : ℝ, 0 < d ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 1 + d →
      |(-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re| ≤ 2 / (σ - 1) := by
  rcases exists_rightNeighborhood_norm_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_sub_one
    with ⟨d, hd_pos, hbound⟩
  refine ⟨d, hd_pos, ?_⟩
  intro σ hσ_gt hσ_le
  exact le_trans (abs_re_le_norm (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)))
    (hbound σ hσ_gt hσ_le)

/-- Real-axis one-sided specialization of the local real-part bound for
`-ζ'/ζ` with the concrete constant `2`. -/
lemma exists_rightNeighborhood_re_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_sub_one :
    ∃ d : ℝ, 0 < d ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 1 + d →
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 2 / (σ - 1) := by
  rcases exists_rightNeighborhood_abs_re_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_sub_one
    with ⟨d, hd_pos, hbound⟩
  refine ⟨d, hd_pos, ?_⟩
  intro σ hσ_gt hσ_le
  exact le_trans (le_abs_self _) (hbound σ hσ_gt hσ_le)

/-- The concrete real-axis local bound in the exact shape needed for the
`hreal` input of the 3-4-1 high-height assembly.

If a future choice of `σOf t` stays inside a sufficiently small right
neighborhood of `1`, then the real-axis term is bounded by
`2 / (σOf t - 1)`. -/
lemma exists_rightNeighborhood_hreal_two_div_sub_one (T0 : ℝ) :
    ∃ d : ℝ, 0 < d ∧ ∀ σOf : ℝ → ℝ,
      (∀ t : ℝ, T0 ≤ |t| → 1 < σOf t) →
      (∀ t : ℝ, T0 ≤ |t| → σOf t ≤ 1 + d) →
      ∀ t : ℝ, T0 ≤ |t| → 1 < σOf t → σOf t ≤ 2 →
        (-deriv riemannZeta (σOf t : ℂ) / riemannZeta (σOf t : ℂ)).re ≤
          2 / (σOf t - 1) := by
  rcases exists_rightNeighborhood_re_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_sub_one
    with ⟨d, hd_pos, hbound⟩
  refine ⟨d, hd_pos, ?_⟩
  intro σOf hσ_gt hσ_near t ht _hgt _hle
  exact hbound (σOf t) (hσ_gt t ht) (hσ_near t ht)

/-- Real-axis specialization of the local pole-order norm bound for `-ζ'/ζ`.

For every `C > 1`, the bound `‖-ζ'/ζ(σ)‖ < C / (σ - 1)` holds for real
`σ > 1` sufficiently close to `1`.  This is the norm-level input underlying the
real-part estimates used in the de la Vallée Poussin 3-4-1 argument. -/
lemma exists_rightNeighborhood_norm_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_sub_one
    (C : ℝ) (hC : 1 < C) :
    ∃ d : ℝ, 0 < d ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 1 + d →
      ‖-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖ < C / (σ - 1) := by
  rcases exists_punctured_closedBall_norm_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one
      C hC with ⟨r, hr_pos, hbound⟩
  refine ⟨r, hr_pos, ?_⟩
  intro σ hσ_gt hσ_le
  have hσ_ne_one : σ ≠ 1 := ne_of_gt hσ_gt
  have hs_ne : (σ : ℂ) ≠ 1 := by
    intro hs
    exact hσ_ne_one (by simpa using congrArg Complex.re hs)
  have hdist : dist (σ : ℂ) (1 : ℂ) ≤ r := by
    have hdist_eq : dist (σ : ℂ) (1 : ℂ) = |σ - 1| := by
      simpa using Complex.isometry_ofReal.dist_eq σ 1
    have habs_eq : |σ - 1| = σ - 1 := abs_of_nonneg (sub_nonneg.mpr hσ_gt.le)
    rw [hdist_eq, habs_eq]
    linarith
  have hnorm_eq : ‖(σ : ℂ) - 1‖ = σ - 1 := by
    have hnorm_eq_abs : ‖(σ : ℂ) - 1‖ = |σ - 1| := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
      simpa using (RCLike.norm_ofReal (K := ℂ) (σ - 1))
    rw [hnorm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hσ_gt.le)]
  simpa [hnorm_eq] using hbound (σ : ℂ) hs_ne hdist

/-- Real-axis specialization of the local pole-order real-part bound for
`-ζ'/ζ`.

For every `C > 1`, the bound `|Re(-ζ'/ζ)(σ)| < C / (σ - 1)` holds for
real `σ > 1` sufficiently close to `1`.  This is a convenient form for the
real-axis term in the de la Vallée Poussin 3-4-1 argument. -/
lemma exists_rightNeighborhood_abs_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_sub_one
    (C : ℝ) (hC : 1 < C) :
    ∃ d : ℝ, 0 < d ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 1 + d →
      |(-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re| < C / (σ - 1) := by
  rcases exists_punctured_closedBall_abs_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one
      C hC with ⟨r, hr_pos, hbound⟩
  refine ⟨r, hr_pos, ?_⟩
  intro σ hσ_gt hσ_le
  have hσ_ne_one : σ ≠ 1 := ne_of_gt hσ_gt
  have hs_ne : (σ : ℂ) ≠ 1 := by
    intro hs
    exact hσ_ne_one (by simpa using congrArg Complex.re hs)
  have hdist : dist (σ : ℂ) (1 : ℂ) ≤ r := by
    have hdist_eq : dist (σ : ℂ) (1 : ℂ) = |σ - 1| := by
      simpa using Complex.isometry_ofReal.dist_eq σ 1
    have habs_eq : |σ - 1| = σ - 1 := abs_of_nonneg (sub_nonneg.mpr hσ_gt.le)
    rw [hdist_eq, habs_eq]
    linarith
  have hnorm_eq : ‖(σ : ℂ) - 1‖ = σ - 1 := by
    have hnorm_eq_abs : ‖(σ : ℂ) - 1‖ = |σ - 1| := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
      simpa using (RCLike.norm_ofReal (K := ℂ) (σ - 1))
    rw [hnorm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hσ_gt.le)]
  simpa [hnorm_eq] using hbound (σ : ℂ) hs_ne hdist

/-- Real-axis one-sided specialization of the local pole-order real-part bound
for `-ζ'/ζ`. -/
lemma exists_rightNeighborhood_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_sub_one
    (C : ℝ) (hC : 1 < C) :
    ∃ d : ℝ, 0 < d ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 1 + d →
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re < C / (σ - 1) := by
  rcases exists_rightNeighborhood_abs_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_sub_one
      C hC with ⟨d, hd_pos, hbound⟩
  refine ⟨d, hd_pos, ?_⟩
  intro σ hσ_gt hσ_le
  exact lt_of_le_of_lt (le_abs_self _) (hbound σ hσ_gt hσ_le)

/-- Flexible real-axis local bound in the exact shape needed for the `hreal`
input of the 3-4-1 high-height assembly.

For every `C > 1`, if a future choice of `σOf t` stays inside a sufficiently
small right neighborhood of `1`, then the real-axis term is bounded by
`C / (σOf t - 1)`. -/
lemma exists_rightNeighborhood_hreal_const_div_sub_one (C : ℝ) (hC : 1 < C)
    (T0 : ℝ) :
    ∃ d : ℝ, 0 < d ∧ ∀ σOf : ℝ → ℝ,
      (∀ t : ℝ, T0 ≤ |t| → 1 < σOf t) →
      (∀ t : ℝ, T0 ≤ |t| → σOf t ≤ 1 + d) →
      ∀ t : ℝ, T0 ≤ |t| → 1 < σOf t → σOf t ≤ 2 →
        (-deriv riemannZeta (σOf t : ℂ) / riemannZeta (σOf t : ℂ)).re ≤
          C / (σOf t - 1) := by
  rcases exists_rightNeighborhood_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_sub_one
      C hC with ⟨d, hd_pos, hbound⟩
  refine ⟨d, hd_pos, ?_⟩
  intro σOf hσ_gt hσ_near t ht _hgt _hle
  exact le_of_lt (hbound (σOf t) (hσ_gt t ht) (hσ_near t ht))

/-- Concrete real-axis `hreal` bound for the standard choice
`σOf t = 1 + a / log |t|`.

The smallness condition `a ≤ d * log 2` is exactly what ensures that this
standard choice remains inside the local right neighborhood supplied by the
pole estimate. -/
lemma exists_sigmaOf_log_hreal_two_div_sub_one (T0 : ℝ) (hT0 : 2 ≤ T0) :
    ∃ d : ℝ, 0 < d ∧ ∀ a : ℝ, 0 < a → a ≤ Real.log 2 →
      a ≤ d * Real.log 2 →
      ∀ t : ℝ, T0 ≤ |t| →
        (-deriv riemannZeta ((1 + a / Real.log |t| : ℝ) : ℂ) /
            riemannZeta ((1 + a / Real.log |t| : ℝ) : ℂ)).re ≤
          2 / ((1 + a / Real.log |t|) - 1) := by
  rcases exists_rightNeighborhood_hreal_two_div_sub_one T0 with
    ⟨d, hd_pos, hreal⟩
  refine ⟨d, hd_pos, ?_⟩
  intro a ha_pos ha_le_log2 ha_le_near t ht
  let σOf : ℝ → ℝ := fun u => 1 + a / Real.log |u|
  have hσ_gt : ∀ u : ℝ, T0 ≤ |u| → 1 < σOf u :=
    fun u hu => sigmaOf_log_gt_one hT0 ha_pos hu
  have hσ_near : ∀ u : ℝ, T0 ≤ |u| → σOf u ≤ 1 + d :=
    fun u hu => sigmaOf_log_le_one_add hT0 ha_le_near hd_pos.le hu
  have hσ_le : σOf t ≤ 2 :=
    sigmaOf_log_le_two hT0 ha_le_log2 ht
  have hbound := hreal σOf hσ_gt hσ_near t ht (hσ_gt t ht) hσ_le
  simpa [σOf] using hbound

/-- Flexible real-axis `hreal` bound for the standard choice
`σOf t = 1 + a / log |t|`. -/
lemma exists_sigmaOf_log_hreal_const_div_sub_one (C : ℝ) (hC : 1 < C)
    (T0 : ℝ) (hT0 : 2 ≤ T0) :
    ∃ d : ℝ, 0 < d ∧ ∀ a : ℝ, 0 < a → a ≤ Real.log 2 →
      a ≤ d * Real.log 2 →
      ∀ t : ℝ, T0 ≤ |t| →
        (-deriv riemannZeta ((1 + a / Real.log |t| : ℝ) : ℂ) /
            riemannZeta ((1 + a / Real.log |t| : ℝ) : ℂ)).re ≤
          C / ((1 + a / Real.log |t|) - 1) := by
  rcases exists_rightNeighborhood_hreal_const_div_sub_one C hC T0 with
    ⟨d, hd_pos, hreal⟩
  refine ⟨d, hd_pos, ?_⟩
  intro a ha_pos ha_le_log2 ha_le_near t ht
  let σOf : ℝ → ℝ := fun u => 1 + a / Real.log |u|
  have hσ_gt : ∀ u : ℝ, T0 ≤ |u| → 1 < σOf u :=
    fun u hu => sigmaOf_log_gt_one hT0 ha_pos hu
  have hσ_near : ∀ u : ℝ, T0 ≤ |u| → σOf u ≤ 1 + d :=
    fun u hu => sigmaOf_log_le_one_add hT0 ha_le_near hd_pos.le hu
  have hσ_le : σOf t ≤ 2 :=
    sigmaOf_log_le_two hT0 ha_le_log2 ht
  have hbound := hreal σOf hσ_gt hσ_near t ht (hσ_gt t ht) hσ_le
  simpa [σOf] using hbound

/-- Algebraic normalization for the standard high-height choice
`σ = 1 + a / log |t|`.

This rewrites the local pole denominator into the vertical-height scale used in
the quantitative zero-free-region argument. -/
lemma const_div_sigmaOf_log_sub_one_eq_mul_log_div (C : ℝ)
    {T0 a t : ℝ} (hT0 : 2 ≤ T0) (ha : a ≠ 0) (ht : T0 ≤ |t|) :
    C / ((1 + a / Real.log |t|) - 1) = C * Real.log |t| / a := by
  have hlog_pos : 0 < Real.log |t| := log_abs_pos_of_two_le (hT0.trans ht)
  have hlog_ne : Real.log |t| ≠ 0 := ne_of_gt hlog_pos
  have hden : ((1 + a / Real.log |t|) - 1) = a / Real.log |t| := by ring
  rw [hden]
  field_simp [ha, hlog_ne]

/-- Concrete real-axis `hreal` bound for
`σOf t = 1 + a / log |t|`, normalized as an `O(log |t|)` estimate. -/
lemma exists_sigmaOf_log_hreal_two_mul_log_div (T0 : ℝ) (hT0 : 2 ≤ T0) :
    ∃ d : ℝ, 0 < d ∧ ∀ a : ℝ, 0 < a → a ≤ Real.log 2 →
      a ≤ d * Real.log 2 →
      ∀ t : ℝ, T0 ≤ |t| →
        (-deriv riemannZeta ((1 + a / Real.log |t| : ℝ) : ℂ) /
            riemannZeta ((1 + a / Real.log |t| : ℝ) : ℂ)).re ≤
          2 * Real.log |t| / a := by
  rcases exists_sigmaOf_log_hreal_two_div_sub_one T0 hT0 with
    ⟨d, hd_pos, hreal⟩
  refine ⟨d, hd_pos, ?_⟩
  intro a ha_pos ha_le_log2 ha_le_near t ht
  have hbound := hreal a ha_pos ha_le_log2 ha_le_near t ht
  calc
    (-deriv riemannZeta ((1 + a / Real.log |t| : ℝ) : ℂ) /
        riemannZeta ((1 + a / Real.log |t| : ℝ) : ℂ)).re
        ≤ 2 / ((1 + a / Real.log |t|) - 1) := hbound
    _ = 2 * Real.log |t| / a :=
        const_div_sigmaOf_log_sub_one_eq_mul_log_div 2 hT0
          (ne_of_gt ha_pos) ht

/-- Flexible real-axis `hreal` bound for
`σOf t = 1 + a / log |t|`, normalized as an `O(log |t|)` estimate. -/
lemma exists_sigmaOf_log_hreal_const_mul_log_div (C : ℝ) (hC : 1 < C)
    (T0 : ℝ) (hT0 : 2 ≤ T0) :
    ∃ d : ℝ, 0 < d ∧ ∀ a : ℝ, 0 < a → a ≤ Real.log 2 →
      a ≤ d * Real.log 2 →
      ∀ t : ℝ, T0 ≤ |t| →
        (-deriv riemannZeta ((1 + a / Real.log |t| : ℝ) : ℂ) /
            riemannZeta ((1 + a / Real.log |t| : ℝ) : ℂ)).re ≤
          C * Real.log |t| / a := by
  rcases exists_sigmaOf_log_hreal_const_div_sub_one C hC T0 hT0 with
    ⟨d, hd_pos, hreal⟩
  refine ⟨d, hd_pos, ?_⟩
  intro a ha_pos ha_le_log2 ha_le_near t ht
  have hbound := hreal a ha_pos ha_le_log2 ha_le_near t ht
  calc
    (-deriv riemannZeta ((1 + a / Real.log |t| : ℝ) : ℂ) /
        riemannZeta ((1 + a / Real.log |t| : ℝ) : ℂ)).re
        ≤ C / ((1 + a / Real.log |t|) - 1) := hbound
    _ = C * Real.log |t| / a :=
        const_div_sigmaOf_log_sub_one_eq_mul_log_div C hT0
          (ne_of_gt ha_pos) ht

/-- Weak `σ + 2it` norm bound obtained from the absolutely convergent
von Mangoldt L-series.

This uses `norm_logDeriv_riemannZeta_le_real_neg_deriv_div` to reduce the
vertical value to the real-axis logarithmic derivative at the same real part.
The price is the factor `1/a`, so this is not yet the sharp vertical-strip
estimate needed to close the classical zero-free region. -/
lemma exists_sigmaOf_log_two_t_norm_bound_const_mul_log_div
    (C : ℝ) (hC : 1 < C) (T0 : ℝ) (hT0 : 2 ≤ T0) :
    ∃ d : ℝ, 0 < d ∧ ∀ a : ℝ, 0 < a → a ≤ Real.log 2 →
      a ≤ d * Real.log 2 →
      ∀ t : ℝ, T0 ≤ |t| →
        ‖logDeriv riemannZeta
          ((1 + a / Real.log |t| : ℝ) + 2 * I * t)‖ ≤
          C * Real.log |t| / a := by
  rcases exists_sigmaOf_log_hreal_const_mul_log_div C hC T0 hT0 with
    ⟨d, hd_pos, hreal⟩
  refine ⟨d, hd_pos, ?_⟩
  intro a ha_pos ha_le_log2 ha_le_near t ht
  let σ : ℝ := 1 + a / Real.log |t|
  let z : ℂ := (σ : ℂ) + 2 * I * t
  have hz_re : z.re = σ := by simp [z]
  have hσ_gt : 1 < σ := sigmaOf_log_gt_one hT0 ha_pos ht
  have hz_gt : 1 < z.re := by simpa [hz_re] using hσ_gt
  have hnorm := norm_logDeriv_riemannZeta_le_real_neg_deriv_div z hz_gt
  have hreal_bound := hreal a ha_pos ha_le_log2 ha_le_near t ht
  calc
    ‖logDeriv riemannZeta z‖
        ≤ (-deriv riemannZeta (z.re : ℂ) /
          riemannZeta (z.re : ℂ)).re := hnorm
    _ = (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re := by
      rw [hz_re]
    _ ≤ C * Real.log |t| / a := by
      simpa [σ] using hreal_bound

/-- Weak `σ + 2it` real-part bound obtained from the half-plane L-series norm
bound.

This is directly shaped like the third term in the 3-4-1 inequality, but the
coefficient is `C/a` rather than a height-independent constant.  It records the
honest boundary of what follows from absolute convergence alone. -/
lemma exists_sigmaOf_log_two_t_bound_const_mul_log_div
    (C : ℝ) (hC : 1 < C) (T0 : ℝ) (hT0 : 2 ≤ T0) :
    ∃ d : ℝ, 0 < d ∧ ∀ a : ℝ, 0 < a → a ≤ Real.log 2 →
      a ≤ d * Real.log 2 →
      ∀ t : ℝ, T0 ≤ |t| →
        (-deriv riemannZeta
          ((1 + a / Real.log |t| : ℝ) + 2 * I * t) /
          riemannZeta ((1 + a / Real.log |t| : ℝ) + 2 * I * t)).re ≤
          C * Real.log |t| / a := by
  rcases exists_sigmaOf_log_two_t_norm_bound_const_mul_log_div C hC T0 hT0 with
    ⟨d, hd_pos, hnorm⟩
  refine ⟨d, hd_pos, ?_⟩
  intro a ha_pos ha_le_log2 ha_le_near t ht
  let z : ℂ := (1 + a / Real.log |t| : ℝ) + 2 * I * t
  calc
    (-deriv riemannZeta z / riemannZeta z).re
        ≤ ‖-deriv riemannZeta z / riemannZeta z‖ := Complex.re_le_norm _
    _ = ‖logDeriv riemannZeta z‖ :=
      norm_neg_deriv_div_riemannZeta_eq_norm_logDeriv z
    _ ≤ C * Real.log |t| / a :=
      hnorm a ha_pos ha_le_log2 ha_le_near t ht

/-- Weak moving-strip norm bound to the right of the standard high-height
choice `1 + a / log |t|`.

The proof still uses the absolutely convergent half-plane L-series, so it keeps
the expected `1/a` loss.  It upgrades the point estimate above from
`σ = 1 + a / log |t|` to every `σ` to its right in the strip. -/
lemma exists_sigma_ge_sigmaOf_log_norm_bound_const_mul_log_div
    (C : ℝ) (hC : 1 < C) (T0 : ℝ) (hT0 : 2 ≤ T0) :
    ∃ d : ℝ, 0 < d ∧ ∀ a : ℝ, 0 < a → a ≤ Real.log 2 →
      a ≤ d * Real.log 2 →
      ∀ σ t : ℝ, T0 ≤ |t| →
        1 + a / Real.log |t| ≤ σ → σ ≤ 2 →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          C * Real.log |t| / a := by
  rcases exists_sigmaOf_log_hreal_const_mul_log_div C hC T0 hT0 with
    ⟨d, hd_pos, hreal⟩
  refine ⟨d, hd_pos, ?_⟩
  intro a ha_pos ha_le_log2 ha_le_near σ t ht hσ_lower _hσ_le
  let σ0 : ℝ := 1 + a / Real.log |t|
  let z : ℂ := (σ : ℂ) + I * t
  have hz_re : z.re = σ := by simp [z]
  have hσ0_gt : 1 < σ0 := by
    simpa [σ0] using sigmaOf_log_gt_one hT0 ha_pos ht
  have hz_gt : 1 < z.re := by
    rw [hz_re]
    exact lt_of_lt_of_le hσ0_gt hσ_lower
  have hnorm := norm_logDeriv_riemannZeta_le_real_neg_deriv_div z hz_gt
  have hanti :
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤
      (-deriv riemannZeta (σ0 : ℂ) / riemannZeta (σ0 : ℂ)).re := by
    simpa [σ0] using log_deriv_zeta_antitone hσ0_gt hσ_lower
  have hreal_bound :
      (-deriv riemannZeta (σ0 : ℂ) / riemannZeta (σ0 : ℂ)).re ≤
        C * Real.log |t| / a := by
    simpa [σ0] using hreal a ha_pos ha_le_log2 ha_le_near t ht
  calc
    ‖logDeriv riemannZeta z‖
        ≤ (-deriv riemannZeta (z.re : ℂ) / riemannZeta (z.re : ℂ)).re := hnorm
    _ = (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re := by
      rw [hz_re]
    _ ≤ (-deriv riemannZeta (σ0 : ℂ) / riemannZeta (σ0 : ℂ)).re := hanti
    _ ≤ C * Real.log |t| / a := hreal_bound

/-- Weak moving-strip real-part bound to the right of the standard high-height
choice `1 + a / log |t|`.

This is the real-part version shaped for the 3-4-1 inequality.  It records the
same honest `1/a` loss as the norm statement. -/
lemma exists_sigma_ge_sigmaOf_log_re_neg_deriv_div_bound_const_mul_log_div
    (C : ℝ) (hC : 1 < C) (T0 : ℝ) (hT0 : 2 ≤ T0) :
    ∃ d : ℝ, 0 < d ∧ ∀ a : ℝ, 0 < a → a ≤ Real.log 2 →
      a ≤ d * Real.log 2 →
      ∀ σ t : ℝ, T0 ≤ |t| →
        1 + a / Real.log |t| ≤ σ → σ ≤ 2 →
        (-deriv riemannZeta ((σ : ℂ) + I * t) /
            riemannZeta ((σ : ℂ) + I * t)).re ≤
          C * Real.log |t| / a := by
  rcases exists_sigma_ge_sigmaOf_log_norm_bound_const_mul_log_div C hC T0 hT0 with
    ⟨d, hd_pos, hnorm⟩
  refine ⟨d, hd_pos, ?_⟩
  intro a ha_pos ha_le_log2 ha_le_near σ t ht hσ_lower hσ_le
  let z : ℂ := (σ : ℂ) + I * t
  calc
    (-deriv riemannZeta z / riemannZeta z).re
        ≤ ‖-deriv riemannZeta z / riemannZeta z‖ := Complex.re_le_norm _
    _ = ‖logDeriv riemannZeta z‖ :=
      norm_neg_deriv_div_riemannZeta_eq_norm_logDeriv z
    _ ≤ C * Real.log |t| / a := by
      simpa [z] using hnorm a ha_pos ha_le_log2 ha_le_near σ t ht
        hσ_lower hσ_le

/-- Weak moving-strip norm bound with an arbitrary imaginary coordinate.

The height parameter `t` only controls the logarithmic scale and the lower
edge `1 + a / log |t|`; the point being estimated may have imaginary part
`u`.  This is useful for feeding both `σ+it` and `σ+2it` terms from the same
high-height scale. -/
lemma exists_sigma_ge_sigmaOf_log_any_im_norm_bound_const_mul_log_div
    (C : ℝ) (hC : 1 < C) (T0 : ℝ) (hT0 : 2 ≤ T0) :
    ∃ d : ℝ, 0 < d ∧ ∀ a : ℝ, 0 < a → a ≤ Real.log 2 →
      a ≤ d * Real.log 2 →
      ∀ σ t u : ℝ, T0 ≤ |t| →
        1 + a / Real.log |t| ≤ σ → σ ≤ 2 →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * u)‖ ≤
          C * Real.log |t| / a := by
  rcases exists_sigmaOf_log_hreal_const_mul_log_div C hC T0 hT0 with
    ⟨d, hd_pos, hreal⟩
  refine ⟨d, hd_pos, ?_⟩
  intro a ha_pos ha_le_log2 ha_le_near σ t u ht hσ_lower _hσ_le
  let σ0 : ℝ := 1 + a / Real.log |t|
  let z : ℂ := (σ : ℂ) + I * u
  have hz_re : z.re = σ := by simp [z]
  have hσ0_gt : 1 < σ0 := by
    simpa [σ0] using sigmaOf_log_gt_one hT0 ha_pos ht
  have hz_gt : 1 < z.re := by
    rw [hz_re]
    exact lt_of_lt_of_le hσ0_gt hσ_lower
  have hnorm := norm_logDeriv_riemannZeta_le_real_neg_deriv_div z hz_gt
  have hanti :
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤
      (-deriv riemannZeta (σ0 : ℂ) / riemannZeta (σ0 : ℂ)).re := by
    simpa [σ0] using log_deriv_zeta_antitone hσ0_gt hσ_lower
  have hreal_bound :
      (-deriv riemannZeta (σ0 : ℂ) / riemannZeta (σ0 : ℂ)).re ≤
        C * Real.log |t| / a := by
    simpa [σ0] using hreal a ha_pos ha_le_log2 ha_le_near t ht
  calc
    ‖logDeriv riemannZeta z‖
        ≤ (-deriv riemannZeta (z.re : ℂ) / riemannZeta (z.re : ℂ)).re := hnorm
    _ = (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re := by
      rw [hz_re]
    _ ≤ (-deriv riemannZeta (σ0 : ℂ) / riemannZeta (σ0 : ℂ)).re := hanti
    _ ≤ C * Real.log |t| / a := hreal_bound

/-- Weak moving-strip real-part bound with an arbitrary imaginary coordinate.

This is the `-ζ'/ζ` real-part form of
`exists_sigma_ge_sigmaOf_log_any_im_norm_bound_const_mul_log_div`. -/
lemma exists_sigma_ge_sigmaOf_log_any_im_re_neg_deriv_div_bound_const_mul_log_div
    (C : ℝ) (hC : 1 < C) (T0 : ℝ) (hT0 : 2 ≤ T0) :
    ∃ d : ℝ, 0 < d ∧ ∀ a : ℝ, 0 < a → a ≤ Real.log 2 →
      a ≤ d * Real.log 2 →
      ∀ σ t u : ℝ, T0 ≤ |t| →
        1 + a / Real.log |t| ≤ σ → σ ≤ 2 →
        (-deriv riemannZeta ((σ : ℂ) + I * u) /
            riemannZeta ((σ : ℂ) + I * u)).re ≤
          C * Real.log |t| / a := by
  rcases exists_sigma_ge_sigmaOf_log_any_im_norm_bound_const_mul_log_div
      C hC T0 hT0 with
    ⟨d, hd_pos, hnorm⟩
  refine ⟨d, hd_pos, ?_⟩
  intro a ha_pos ha_le_log2 ha_le_near σ t u ht hσ_lower hσ_le
  let z : ℂ := (σ : ℂ) + I * u
  calc
    (-deriv riemannZeta z / riemannZeta z).re
        ≤ ‖-deriv riemannZeta z / riemannZeta z‖ := Complex.re_le_norm _
    _ = ‖logDeriv riemannZeta z‖ :=
      norm_neg_deriv_div_riemannZeta_eq_norm_logDeriv z
    _ ≤ C * Real.log |t| / a := by
      simpa [z] using hnorm a ha_pos ha_le_log2 ha_le_near σ t u ht
        hσ_lower hσ_le

/-- Weak moving-strip norm bound specialized to the `σ + 2it` point appearing
in the third term of the 3-4-1 inequality. -/
lemma exists_sigma_ge_sigmaOf_log_two_t_norm_bound_const_mul_log_div
    (C : ℝ) (hC : 1 < C) (T0 : ℝ) (hT0 : 2 ≤ T0) :
    ∃ d : ℝ, 0 < d ∧ ∀ a : ℝ, 0 < a → a ≤ Real.log 2 →
      a ≤ d * Real.log 2 →
      ∀ σ t : ℝ, T0 ≤ |t| →
        1 + a / Real.log |t| ≤ σ → σ ≤ 2 →
        ‖logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖ ≤
          C * Real.log |t| / a := by
  rcases exists_sigma_ge_sigmaOf_log_any_im_norm_bound_const_mul_log_div
      C hC T0 hT0 with
    ⟨d, hd_pos, hnorm⟩
  refine ⟨d, hd_pos, ?_⟩
  intro a ha_pos ha_le_log2 ha_le_near σ t ht hσ_lower hσ_le
  have hbound := hnorm a ha_pos ha_le_log2 ha_le_near σ t (2 * t)
    ht hσ_lower hσ_le
  simpa [mul_assoc, mul_left_comm, mul_comm] using hbound

/-- Weak moving-strip real-part bound specialized to the `σ + 2it` point
appearing in the third term of the 3-4-1 inequality. -/
lemma exists_sigma_ge_sigmaOf_log_two_t_re_neg_deriv_div_bound_const_mul_log_div
    (C : ℝ) (hC : 1 < C) (T0 : ℝ) (hT0 : 2 ≤ T0) :
    ∃ d : ℝ, 0 < d ∧ ∀ a : ℝ, 0 < a → a ≤ Real.log 2 →
      a ≤ d * Real.log 2 →
      ∀ σ t : ℝ, T0 ≤ |t| →
        1 + a / Real.log |t| ≤ σ → σ ≤ 2 →
        (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
            riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤
          C * Real.log |t| / a := by
  rcases exists_sigma_ge_sigmaOf_log_any_im_re_neg_deriv_div_bound_const_mul_log_div
      C hC T0 hT0 with
    ⟨d, hd_pos, hbound⟩
  refine ⟨d, hd_pos, ?_⟩
  intro a ha_pos ha_le_log2 ha_le_near σ t ht hσ_lower hσ_le
  have h := hbound a ha_pos ha_le_log2 ha_le_near σ t (2 * t)
    ht hσ_lower hσ_le
  simpa [mul_assoc, mul_left_comm, mul_comm] using h

/-- Weak moving-strip `σ + 2it` norm bound in standard `B * log |t|`
form, with `B` allowed to depend on the fixed moving-strip parameter `a`.

This is still the absolute-convergence estimate: the generated constant is
`B = C/a`, so the theorem does not close the classical zero-free-region margin. -/
lemma exists_sigma_ge_sigmaOf_log_two_t_norm_bound_log_scale
    (C : ℝ) (hC : 1 < C) (T0 : ℝ) (hT0 : 2 ≤ T0) :
    ∃ d : ℝ, 0 < d ∧ ∀ a : ℝ, 0 < a → a ≤ Real.log 2 →
      a ≤ d * Real.log 2 →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ σ t : ℝ, T0 ≤ |t| →
        1 + a / Real.log |t| ≤ σ → σ ≤ 2 →
        ‖logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖ ≤
          B * Real.log |t| := by
  rcases exists_sigma_ge_sigmaOf_log_two_t_norm_bound_const_mul_log_div
      C hC T0 hT0 with
    ⟨d, hd_pos, hnorm⟩
  refine ⟨d, hd_pos, ?_⟩
  intro a ha_pos ha_le_log2 ha_le_near
  refine ⟨C / a, div_nonneg (by linarith [hC]) (le_of_lt ha_pos), ?_⟩
  intro σ t ht hσ_lower hσ_le
  calc
    ‖logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖
        ≤ C * Real.log |t| / a :=
          hnorm a ha_pos ha_le_log2 ha_le_near σ t ht hσ_lower hσ_le
    _ = (C / a) * Real.log |t| := by ring

/-- Weak moving-strip `σ + 2it` real-part bound in standard `B * log |t|`
form, with `B` allowed to depend on the fixed moving-strip parameter `a`. -/
lemma exists_sigma_ge_sigmaOf_log_two_t_re_neg_deriv_div_bound_log_scale
    (C : ℝ) (hC : 1 < C) (T0 : ℝ) (hT0 : 2 ≤ T0) :
    ∃ d : ℝ, 0 < d ∧ ∀ a : ℝ, 0 < a → a ≤ Real.log 2 →
      a ≤ d * Real.log 2 →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ σ t : ℝ, T0 ≤ |t| →
        1 + a / Real.log |t| ≤ σ → σ ≤ 2 →
        (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
            riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤
          B * Real.log |t| := by
  rcases exists_sigma_ge_sigmaOf_log_two_t_re_neg_deriv_div_bound_const_mul_log_div
      C hC T0 hT0 with
    ⟨d, hd_pos, hbound⟩
  refine ⟨d, hd_pos, ?_⟩
  intro a ha_pos ha_le_log2 ha_le_near
  refine ⟨C / a, div_nonneg (by linarith [hC]) (le_of_lt ha_pos), ?_⟩
  intro σ t ht hσ_lower hσ_le
  calc
    (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
        riemannZeta ((σ : ℂ) + 2 * I * t)).re
        ≤ C * Real.log |t| / a :=
          hbound a ha_pos ha_le_log2 ha_le_near σ t ht hσ_lower hσ_le
    _ = (C / a) * Real.log |t| := by ring

/-- Weak arbitrary-imaginary-coordinate moving-strip norm bound in standard
`B * log |t|` form, with `B` allowed to depend on the fixed moving-strip
parameter `a`.

The point being estimated has imaginary coordinate `u`; the height parameter
`t` controls both the lower edge `1 + a / log |t|` and the logarithmic scale. -/
lemma exists_sigma_ge_sigmaOf_log_any_im_norm_bound_log_scale
    (C : ℝ) (hC : 1 < C) (T0 : ℝ) (hT0 : 2 ≤ T0) :
    ∃ d : ℝ, 0 < d ∧ ∀ a : ℝ, 0 < a → a ≤ Real.log 2 →
      a ≤ d * Real.log 2 →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ σ t u : ℝ, T0 ≤ |t| →
        1 + a / Real.log |t| ≤ σ → σ ≤ 2 →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * u)‖ ≤
          B * Real.log |t| := by
  rcases exists_sigma_ge_sigmaOf_log_any_im_norm_bound_const_mul_log_div
      C hC T0 hT0 with
    ⟨d, hd_pos, hnorm⟩
  refine ⟨d, hd_pos, ?_⟩
  intro a ha_pos ha_le_log2 ha_le_near
  refine ⟨C / a, div_nonneg (by linarith [hC]) (le_of_lt ha_pos), ?_⟩
  intro σ t u ht hσ_lower hσ_le
  calc
    ‖logDeriv riemannZeta ((σ : ℂ) + I * u)‖
        ≤ C * Real.log |t| / a :=
          hnorm a ha_pos ha_le_log2 ha_le_near σ t u ht hσ_lower hσ_le
    _ = (C / a) * Real.log |t| := by ring

/-- Weak arbitrary-imaginary-coordinate moving-strip real-part bound in
standard `B * log |t|` form. -/
lemma exists_sigma_ge_sigmaOf_log_any_im_re_neg_deriv_div_bound_log_scale
    (C : ℝ) (hC : 1 < C) (T0 : ℝ) (hT0 : 2 ≤ T0) :
    ∃ d : ℝ, 0 < d ∧ ∀ a : ℝ, 0 < a → a ≤ Real.log 2 →
      a ≤ d * Real.log 2 →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ σ t u : ℝ, T0 ≤ |t| →
        1 + a / Real.log |t| ≤ σ → σ ≤ 2 →
        (-deriv riemannZeta ((σ : ℂ) + I * u) /
            riemannZeta ((σ : ℂ) + I * u)).re ≤
          B * Real.log |t| := by
  rcases exists_sigma_ge_sigmaOf_log_any_im_re_neg_deriv_div_bound_const_mul_log_div
      C hC T0 hT0 with
    ⟨d, hd_pos, hbound⟩
  refine ⟨d, hd_pos, ?_⟩
  intro a ha_pos ha_le_log2 ha_le_near
  refine ⟨C / a, div_nonneg (by linarith [hC]) (le_of_lt ha_pos), ?_⟩
  intro σ t u ht hσ_lower hσ_le
  calc
    (-deriv riemannZeta ((σ : ℂ) + I * u) /
        riemannZeta ((σ : ℂ) + I * u)).re
        ≤ C * Real.log |t| / a :=
          hbound a ha_pos ha_le_log2 ha_le_near σ t u ht hσ_lower hσ_le
    _ = (C / a) * Real.log |t| := by ring

/-- Signed weak moving-strip norm bound to the right of
`1 + a / log |t|`.

This is only a sign-convention wrapper around
`exists_sigma_ge_sigmaOf_log_norm_bound_const_mul_log_div`; it preserves the
same explicit `1/a` loss from absolute convergence. -/
lemma exists_sigma_ge_sigmaOf_log_neg_logDeriv_norm_bound_const_mul_log_div
    (C : ℝ) (hC : 1 < C) (T0 : ℝ) (hT0 : 2 ≤ T0) :
    ∃ d : ℝ, 0 < d ∧ ∀ a : ℝ, 0 < a → a ≤ Real.log 2 →
      a ≤ d * Real.log 2 →
      ∀ σ t : ℝ, T0 ≤ |t| →
        1 + a / Real.log |t| ≤ σ → σ ≤ 2 →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          C * Real.log |t| / a := by
  rcases exists_sigma_ge_sigmaOf_log_norm_bound_const_mul_log_div
      C hC T0 hT0 with
    ⟨d, hd_pos, hnorm⟩
  refine ⟨d, hd_pos, ?_⟩
  intro a ha_pos ha_le_log2 ha_le_near σ t ht hσ_lower hσ_le
  calc
    ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖
        = ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := norm_neg _
    _ ≤ C * Real.log |t| / a :=
        hnorm a ha_pos ha_le_log2 ha_le_near σ t ht hσ_lower hσ_le

/-- Signed weak moving-strip norm bound with an arbitrary imaginary
coordinate.  The height parameter `t` still controls the lower edge and the
scale, exactly as in the unsigned `any_im` theorem. -/
lemma exists_sigma_ge_sigmaOf_log_any_im_neg_logDeriv_norm_bound_const_mul_log_div
    (C : ℝ) (hC : 1 < C) (T0 : ℝ) (hT0 : 2 ≤ T0) :
    ∃ d : ℝ, 0 < d ∧ ∀ a : ℝ, 0 < a → a ≤ Real.log 2 →
      a ≤ d * Real.log 2 →
      ∀ σ t u : ℝ, T0 ≤ |t| →
        1 + a / Real.log |t| ≤ σ → σ ≤ 2 →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * u)‖ ≤
          C * Real.log |t| / a := by
  rcases exists_sigma_ge_sigmaOf_log_any_im_norm_bound_const_mul_log_div
      C hC T0 hT0 with
    ⟨d, hd_pos, hnorm⟩
  refine ⟨d, hd_pos, ?_⟩
  intro a ha_pos ha_le_log2 ha_le_near σ t u ht hσ_lower hσ_le
  calc
    ‖-logDeriv riemannZeta ((σ : ℂ) + I * u)‖
        = ‖logDeriv riemannZeta ((σ : ℂ) + I * u)‖ := norm_neg _
    _ ≤ C * Real.log |t| / a :=
        hnorm a ha_pos ha_le_log2 ha_le_near σ t u ht hσ_lower hσ_le

/-- Signed weak moving-strip norm bound specialized to the `σ + 2it` point
in the third term of the 3-4-1 inequality. -/
lemma exists_sigma_ge_sigmaOf_log_two_t_neg_logDeriv_norm_bound_const_mul_log_div
    (C : ℝ) (hC : 1 < C) (T0 : ℝ) (hT0 : 2 ≤ T0) :
    ∃ d : ℝ, 0 < d ∧ ∀ a : ℝ, 0 < a → a ≤ Real.log 2 →
      a ≤ d * Real.log 2 →
      ∀ σ t : ℝ, T0 ≤ |t| →
        1 + a / Real.log |t| ≤ σ → σ ≤ 2 →
        ‖-logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖ ≤
          C * Real.log |t| / a := by
  rcases exists_sigma_ge_sigmaOf_log_any_im_neg_logDeriv_norm_bound_const_mul_log_div
      C hC T0 hT0 with
    ⟨d, hd_pos, hnorm⟩
  refine ⟨d, hd_pos, ?_⟩
  intro a ha_pos ha_le_log2 ha_le_near σ t ht hσ_lower hσ_le
  have hbound := hnorm a ha_pos ha_le_log2 ha_le_near σ t (2 * t)
    ht hσ_lower hσ_le
  simpa [mul_assoc, mul_left_comm, mul_comm] using hbound

/-- Signed weak arbitrary-imaginary-coordinate moving-strip norm bound in
standard `B * log |t|` form, with `B = C/a`. -/
lemma exists_sigma_ge_sigmaOf_log_any_im_neg_logDeriv_norm_bound_log_scale
    (C : ℝ) (hC : 1 < C) (T0 : ℝ) (hT0 : 2 ≤ T0) :
    ∃ d : ℝ, 0 < d ∧ ∀ a : ℝ, 0 < a → a ≤ Real.log 2 →
      a ≤ d * Real.log 2 →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ σ t u : ℝ, T0 ≤ |t| →
        1 + a / Real.log |t| ≤ σ → σ ≤ 2 →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * u)‖ ≤
          B * Real.log |t| := by
  rcases exists_sigma_ge_sigmaOf_log_any_im_neg_logDeriv_norm_bound_const_mul_log_div
      C hC T0 hT0 with
    ⟨d, hd_pos, hnorm⟩
  refine ⟨d, hd_pos, ?_⟩
  intro a ha_pos ha_le_log2 ha_le_near
  refine ⟨C / a, div_nonneg (by linarith [hC]) (le_of_lt ha_pos), ?_⟩
  intro σ t u ht hσ_lower hσ_le
  calc
    ‖-logDeriv riemannZeta ((σ : ℂ) + I * u)‖
        ≤ C * Real.log |t| / a :=
          hnorm a ha_pos ha_le_log2 ha_le_near σ t u ht hσ_lower hσ_le
    _ = (C / a) * Real.log |t| := by ring

/-- Signed weak `σ + 2it` moving-strip norm bound in standard
`B * log |t|` form, with `B = C/a`. -/
lemma exists_sigma_ge_sigmaOf_log_two_t_neg_logDeriv_norm_bound_log_scale
    (C : ℝ) (hC : 1 < C) (T0 : ℝ) (hT0 : 2 ≤ T0) :
    ∃ d : ℝ, 0 < d ∧ ∀ a : ℝ, 0 < a → a ≤ Real.log 2 →
      a ≤ d * Real.log 2 →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ σ t : ℝ, T0 ≤ |t| →
        1 + a / Real.log |t| ≤ σ → σ ≤ 2 →
        ‖-logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖ ≤
          B * Real.log |t| := by
  rcases exists_sigma_ge_sigmaOf_log_two_t_neg_logDeriv_norm_bound_const_mul_log_div
      C hC T0 hT0 with
    ⟨d, hd_pos, hnorm⟩
  refine ⟨d, hd_pos, ?_⟩
  intro a ha_pos ha_le_log2 ha_le_near
  refine ⟨C / a, div_nonneg (by linarith [hC]) (le_of_lt ha_pos), ?_⟩
  intro σ t ht hσ_lower hσ_le
  calc
    ‖-logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖
        ≤ C * Real.log |t| / a :=
          hnorm a ha_pos ha_le_log2 ha_le_near σ t ht hσ_lower hσ_le
    _ = (C / a) * Real.log |t| := by ring

/-- Weak moving-strip package controlling both shifted real-part terms
`σ+it` and `σ+2it` with the same `B * log |t|` coefficient.

This is still the absolute-convergence package, so `B` depends on the fixed
choice of `a`.  The theorem is useful as an honest comparison point for the
future zeta-specific shifted estimates, which must produce constants
independent of this `1/a` loss. -/
lemma exists_sigma_ge_sigmaOf_log_shift_pair_re_neg_deriv_div_bound_log_scale
    (C : ℝ) (hC : 1 < C) (T0 : ℝ) (hT0 : 2 ≤ T0) :
    ∃ d : ℝ, 0 < d ∧ ∀ a : ℝ, 0 < a → a ≤ Real.log 2 →
      a ≤ d * Real.log 2 →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ σ t : ℝ, T0 ≤ |t| →
        1 + a / Real.log |t| ≤ σ → σ ≤ 2 →
          (-deriv riemannZeta ((σ : ℂ) + I * t) /
              riemannZeta ((σ : ℂ) + I * t)).re ≤
            B * Real.log |t| ∧
          (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
              riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤
            B * Real.log |t| := by
  rcases exists_sigma_ge_sigmaOf_log_any_im_re_neg_deriv_div_bound_log_scale
      C hC T0 hT0 with
    ⟨d, hd_pos, hbound⟩
  refine ⟨d, hd_pos, ?_⟩
  intro a ha_pos ha_le_log2 ha_le_near
  rcases hbound a ha_pos ha_le_log2 ha_le_near with ⟨B, hB, hany⟩
  refine ⟨B, hB, ?_⟩
  intro σ t ht hσ_lower hσ_le
  constructor
  · exact hany σ t t ht hσ_lower hσ_le
  · have htwo := hany σ t (2 * t) ht hσ_lower hσ_le
    simpa [mul_assoc, mul_left_comm, mul_comm] using htwo

/-- Classical zero-free-region closure for the standard high-height choice
`σ(t) = 1 + a / log |t|`.

This packages the already-proved real-axis pole input, the elementary side
conditions for `σ(t)`, and the compact bounded-height patch.  The remaining
analytic inputs are exactly the two shifted logarithmic-derivative estimates
and the real-variable negativity margin. -/
lemma exists_sigmaOf_log_classical_zero_free_region_of_log_deriv_bounds
    (C : ℝ) (hC : 1 < C) (T0 : ℝ) (hT0 : 2 ≤ T0)
    {c : ℝ} (hc_pos : 0 < c) :
    ∃ d : ℝ, 0 < d ∧ ∀ a : ℝ, 0 < a → a ≤ Real.log 2 →
      a ≤ d * Real.log 2 →
      ∀ (zeroBound : ℝ → ℝ → ℝ) (twoBound : ℝ → ℝ),
        (∀ β t : ℝ, T0 ≤ |t| → β < 1 →
          β ≥ 1 - c / Real.log |t| →
          0 < (1 + a / Real.log |t|) - β →
          riemannZeta ((β : ℂ) + I * t) = 0 →
          (-deriv riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t) /
            riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t)).re ≤
              zeroBound β t) →
        (∀ t : ℝ, T0 ≤ |t| →
          (-deriv riemannZeta
              ((1 + a / Real.log |t| : ℝ) + 2 * I * t) /
            riemannZeta ((1 + a / Real.log |t| : ℝ) + 2 * I * t)).re ≤
              twoBound t) →
        (∀ β t : ℝ, T0 ≤ |t| → β < 1 →
          β ≥ 1 - c / Real.log |t| →
          3 * (C * Real.log |t| / a) + 4 * zeroBound β t +
            twoBound t < 0) →
        classical_zero_free_region := by
  rcases exists_sigmaOf_log_hreal_const_mul_log_div C hC T0 hT0 with
    ⟨d, hd_pos, hreal⟩
  refine ⟨d, hd_pos, ?_⟩
  intro a ha_pos ha_le_log2 ha_le_near zeroBound twoBound hzero htwo hmargin
  let σOf : ℝ → ℝ := fun t => 1 + a / Real.log |t|
  refine classical_zero_free_region_of_log_deriv_bounds
    (T0 := T0) (c := c) (σOf := σOf)
    (realBound := fun t => C * Real.log |t| / a)
    (twoBound := twoBound) (zeroBound := zeroBound)
    hT0 hc_pos ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t ht
    exact sigmaOf_log_gt_one hT0 ha_pos ht
  · intro t ht
    exact sigmaOf_log_le_two hT0 ha_le_log2 ht
  · intro β t ht hβ_lt hβ
    exact sigmaOf_log_sub_pos hT0 ha_pos ht hβ_lt
  · intro t ht _hgt _hle
    simpa [σOf] using hreal a ha_pos ha_le_log2 ha_le_near t ht
  · intro β t ht _hgt _hle hβ_lt hβ hsub hζ
    simpa [σOf] using hzero β t ht hβ_lt hβ hsub hζ
  · intro t ht _hgt _hle
    simpa [σOf] using htwo t ht
  · intro β t ht hβ_lt hβ
    exact hmargin β t ht hβ_lt hβ

/-- Classical zero-free-region closure for the standard `σ = 1 + a/log |t|`
choice with the usual shifted logarithmic-derivative bound shapes.

Compared with
`exists_sigmaOf_log_classical_zero_free_region_of_log_deriv_bounds`, this
lemma also discharges the final real-variable margin by
`three_four_one_sigmaOf_log_margin`.  The remaining inputs are the two
zeta-specific shifted estimates and the constant inequality
`3*C/a + 4*Czero + Ctwo < 4/(a+c)`. -/
lemma exists_sigmaOf_log_classical_zero_free_region_of_shift_bounds
    (C : ℝ) (hC : 1 < C) (T0 : ℝ) (hT0 : 2 ≤ T0)
    {c : ℝ} (hc_pos : 0 < c) :
    ∃ d : ℝ, 0 < d ∧ ∀ a : ℝ, 0 < a → a ≤ Real.log 2 →
      a ≤ d * Real.log 2 →
      ∀ Czero Ctwo : ℝ,
        (3 * C / a + 4 * Czero + Ctwo < 4 / (a + c)) →
        (∀ β t : ℝ, T0 ≤ |t| → β < 1 →
          β ≥ 1 - c / Real.log |t| →
          0 < (1 + a / Real.log |t|) - β →
          riemannZeta ((β : ℂ) + I * t) = 0 →
          (-deriv riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t) /
            riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t)).re ≤
              -1 / ((1 + a / Real.log |t|) - β) +
                Czero * Real.log |t|) →
        (∀ t : ℝ, T0 ≤ |t| →
          (-deriv riemannZeta
              ((1 + a / Real.log |t| : ℝ) + 2 * I * t) /
            riemannZeta ((1 + a / Real.log |t| : ℝ) + 2 * I * t)).re ≤
              Ctwo * Real.log |t|) →
        classical_zero_free_region := by
  rcases exists_sigmaOf_log_classical_zero_free_region_of_log_deriv_bounds
      C hC T0 hT0 hc_pos with ⟨d, hd_pos, hclosure⟩
  refine ⟨d, hd_pos, ?_⟩
  intro a ha_pos ha_le_log2 ha_le_near Czero Ctwo hconst hzero htwo
  refine hclosure a ha_pos ha_le_log2 ha_le_near
    (fun β t =>
      -1 / ((1 + a / Real.log |t|) - β) + Czero * Real.log |t|)
    (fun t => Ctwo * Real.log |t|) ?_ ?_ ?_
  · exact hzero
  · exact htwo
  · intro β t ht hβ_lt hβ
    exact three_four_one_sigmaOf_log_margin hT0 ha_pos hc_pos ht hβ_lt hβ hconst

/-- High-level conditional closure of the classical zero-free region from the
two zeta-specific shifted logarithmic-derivative estimates.

This theorem consumes:

* the local pole input already proved in this file;
* the pure real-variable constant selection
  `exists_sigmaOf_log_margin_constants`;
* the verified 3-4-1 high-height contradiction and compact bounded-height
  patch.

The remaining hypotheses are exactly the two analytic shifted estimates:
the zero-height estimate with the `-1/(σ-β)` contribution, and the
`σ+2it` estimate. -/
lemma classical_zero_free_region_of_sigma_log_shift_estimates
    (C Czero Ctwo T0 : ℝ) (hC : 1 < C) (hC_lt : C < 4 / 3)
    (hK : 0 ≤ 4 * Czero + Ctwo) (hT0 : 2 ≤ T0)
    (hzero :
      ∀ a c β t : ℝ, 0 < a → 0 < c → a ≤ Real.log 2 →
        T0 ≤ |t| → β < 1 →
        β ≥ 1 - c / Real.log |t| →
        0 < (1 + a / Real.log |t|) - β →
        riemannZeta ((β : ℂ) + I * t) = 0 →
        (-deriv riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t) /
          riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t)).re ≤
            -1 / ((1 + a / Real.log |t|) - β) +
              Czero * Real.log |t|)
    (htwo :
      ∀ a t : ℝ, 0 < a → a ≤ Real.log 2 → T0 ≤ |t| →
        (-deriv riemannZeta
            ((1 + a / Real.log |t| : ℝ) + 2 * I * t) /
          riemannZeta ((1 + a / Real.log |t| : ℝ) + 2 * I * t)).re ≤
            Ctwo * Real.log |t|) :
    classical_zero_free_region := by
  rcases exists_sigmaOf_log_hreal_const_mul_log_div C hC T0 hT0 with
    ⟨d, hd_pos, hreal⟩
  rcases exists_sigmaOf_log_margin_constants (C := C)
      (K := 4 * Czero + Ctwo) (d := d) hC hC_lt hK hd_pos with
    ⟨a, c, ha_pos, hc_pos, ha_le_log2, ha_le_near, hconst⟩
  let σOf : ℝ → ℝ := fun t => 1 + a / Real.log |t|
  refine classical_zero_free_region_of_log_deriv_bounds
    (T0 := T0) (c := c) (σOf := σOf)
    (realBound := fun t => C * Real.log |t| / a)
    (zeroBound := fun β t =>
      -1 / ((1 + a / Real.log |t|) - β) + Czero * Real.log |t|)
    (twoBound := fun t => Ctwo * Real.log |t|)
    hT0 hc_pos ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t ht
    exact sigmaOf_log_gt_one hT0 ha_pos ht
  · intro t ht
    exact sigmaOf_log_le_two hT0 ha_le_log2 ht
  · intro β t ht hβ_lt _hβ
    exact sigmaOf_log_sub_pos hT0 ha_pos ht hβ_lt
  · intro t ht _hgt _hle
    simpa [σOf] using hreal a ha_pos ha_le_log2 ha_le_near t ht
  · intro β t ht _hgt _hle hβ_lt hβ hsub hζ
    simpa [σOf] using
      hzero a c β t ha_pos hc_pos ha_le_log2 ht hβ_lt hβ hsub hζ
  · intro t ht _hgt _hle
    simpa [σOf] using htwo a t ha_pos ha_le_log2 ht
  · intro β t ht hβ_lt hβ
    have hconst' : 3 * C / a + 4 * Czero + Ctwo < 4 / (a + c) := by
      simpa [add_assoc] using hconst
    exact three_four_one_sigmaOf_log_margin hT0 ha_pos hc_pos ht hβ_lt hβ
      hconst'

/-- Nonnegative-constant wrapper for
`classical_zero_free_region_of_sigma_log_shift_estimates`.

This is the caller-facing version when the two shifted logarithmic-derivative
coefficients are known individually nonnegative, rather than already packaged
as `0 <= 4*Czero + Ctwo`. -/
lemma classical_zero_free_region_of_sigma_log_shift_estimates_nonneg_constants
    (C Czero Ctwo T0 : ℝ) (hC : 1 < C) (hC_lt : C < 4 / 3)
    (hCzero : 0 ≤ Czero) (hCtwo : 0 ≤ Ctwo) (hT0 : 2 ≤ T0)
    (hzero :
      ∀ a c β t : ℝ, 0 < a → 0 < c → a ≤ Real.log 2 →
        T0 ≤ |t| → β < 1 →
        β ≥ 1 - c / Real.log |t| →
        0 < (1 + a / Real.log |t|) - β →
        riemannZeta ((β : ℂ) + I * t) = 0 →
        (-deriv riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t) /
          riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t)).re ≤
            -1 / ((1 + a / Real.log |t|) - β) +
              Czero * Real.log |t|)
    (htwo :
      ∀ a t : ℝ, 0 < a → a ≤ Real.log 2 → T0 ≤ |t| →
        (-deriv riemannZeta
            ((1 + a / Real.log |t| : ℝ) + 2 * I * t) /
          riemannZeta ((1 + a / Real.log |t| : ℝ) + 2 * I * t)).re ≤
            Ctwo * Real.log |t|) :
    classical_zero_free_region :=
  classical_zero_free_region_of_sigma_log_shift_estimates
    C Czero Ctwo T0 hC hC_lt (by nlinarith) hT0 hzero htwo

/-- Existential wrapper for the nonnegative shifted-estimate closure.

This is the general coefficient version of the remaining analytic input:
some real-axis coefficient `C` with `1 < C < 4/3`, nonnegative shifted
coefficients `Czero,Ctwo`, and a height cutoff `T0 >= 2` suffice once the two
shifted logarithmic-derivative estimates are proved. -/
lemma classical_zero_free_region_of_exists_sigma_log_shift_estimates_nonneg_constants
    (h :
      ∃ C Czero Ctwo T0 : ℝ,
        1 < C ∧ C < 4 / 3 ∧ 0 ≤ Czero ∧ 0 ≤ Ctwo ∧ 2 ≤ T0 ∧
        (∀ a c β t : ℝ, 0 < a → 0 < c → a ≤ Real.log 2 →
          T0 ≤ |t| → β < 1 →
          β ≥ 1 - c / Real.log |t| →
          0 < (1 + a / Real.log |t|) - β →
          riemannZeta ((β : ℂ) + I * t) = 0 →
          (-deriv riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t) /
            riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t)).re ≤
              -1 / ((1 + a / Real.log |t|) - β) +
                Czero * Real.log |t|) ∧
        (∀ a t : ℝ, 0 < a → a ≤ Real.log 2 → T0 ≤ |t| →
          (-deriv riemannZeta
              ((1 + a / Real.log |t| : ℝ) + 2 * I * t) /
            riemannZeta ((1 + a / Real.log |t| : ℝ) + 2 * I * t)).re ≤
              Ctwo * Real.log |t|)) :
    classical_zero_free_region := by
  rcases h with
    ⟨C, Czero, Ctwo, T0, hC, hC_lt, hCzero, hCtwo, hT0, hzero, htwo⟩
  exact
    classical_zero_free_region_of_sigma_log_shift_estimates_nonneg_constants
      C Czero Ctwo T0 hC hC_lt hCzero hCtwo hT0 hzero htwo

/-- Concrete version of
`classical_zero_free_region_of_sigma_log_shift_estimates` using the fixed
real-axis coefficient `5/4`.

The local pole input allows every coefficient `C > 1`; choosing `5/4` keeps
the strict `C < 4/3` margin needed by the 3-4-1 constant selection. -/
lemma classical_zero_free_region_of_sigma_log_shift_estimates_five_fourths
    (Czero Ctwo T0 : ℝ) (hK : 0 ≤ 4 * Czero + Ctwo) (hT0 : 2 ≤ T0)
    (hzero :
      ∀ a c β t : ℝ, 0 < a → 0 < c → a ≤ Real.log 2 →
        T0 ≤ |t| → β < 1 →
        β ≥ 1 - c / Real.log |t| →
        0 < (1 + a / Real.log |t|) - β →
        riemannZeta ((β : ℂ) + I * t) = 0 →
        (-deriv riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t) /
          riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t)).re ≤
            -1 / ((1 + a / Real.log |t|) - β) +
              Czero * Real.log |t|)
    (htwo :
      ∀ a t : ℝ, 0 < a → a ≤ Real.log 2 → T0 ≤ |t| →
        (-deriv riemannZeta
            ((1 + a / Real.log |t| : ℝ) + 2 * I * t) /
          riemannZeta ((1 + a / Real.log |t| : ℝ) + 2 * I * t)).re ≤
            Ctwo * Real.log |t|) :
    classical_zero_free_region :=
  classical_zero_free_region_of_sigma_log_shift_estimates
    (5 / 4) Czero Ctwo T0
    (by norm_num) (by norm_num) hK hT0 hzero htwo

/-- Nonnegative-constant wrapper for the fixed `5/4` real-axis coefficient. -/
lemma classical_zero_free_region_of_sigma_log_shift_estimates_five_fourths_nonneg_constants
    (Czero Ctwo T0 : ℝ) (hCzero : 0 ≤ Czero) (hCtwo : 0 ≤ Ctwo)
    (hT0 : 2 ≤ T0)
    (hzero :
      ∀ a c β t : ℝ, 0 < a → 0 < c → a ≤ Real.log 2 →
        T0 ≤ |t| → β < 1 →
        β ≥ 1 - c / Real.log |t| →
        0 < (1 + a / Real.log |t|) - β →
        riemannZeta ((β : ℂ) + I * t) = 0 →
        (-deriv riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t) /
          riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t)).re ≤
            -1 / ((1 + a / Real.log |t|) - β) +
              Czero * Real.log |t|)
    (htwo :
      ∀ a t : ℝ, 0 < a → a ≤ Real.log 2 → T0 ≤ |t| →
        (-deriv riemannZeta
            ((1 + a / Real.log |t| : ℝ) + 2 * I * t) /
          riemannZeta ((1 + a / Real.log |t| : ℝ) + 2 * I * t)).re ≤
            Ctwo * Real.log |t|) :
    classical_zero_free_region :=
  classical_zero_free_region_of_sigma_log_shift_estimates_five_fourths
    Czero Ctwo T0 (by nlinarith) hT0 hzero htwo

/-- Existential wrapper for the fixed `5/4` nonnegative shifted-estimate
closure.

This packages the remaining shifted-estimate input as the existence of
nonnegative constants `Czero,Ctwo` and a high-height cutoff `T0 >= 2`. -/
lemma classical_zero_free_region_of_exists_sigma_log_shift_estimates_five_fourths_nonneg_constants
    (h :
      ∃ Czero Ctwo T0 : ℝ, 0 ≤ Czero ∧ 0 ≤ Ctwo ∧ 2 ≤ T0 ∧
        (∀ a c β t : ℝ, 0 < a → 0 < c → a ≤ Real.log 2 →
          T0 ≤ |t| → β < 1 →
          β ≥ 1 - c / Real.log |t| →
          0 < (1 + a / Real.log |t|) - β →
          riemannZeta ((β : ℂ) + I * t) = 0 →
          (-deriv riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t) /
            riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t)).re ≤
              -1 / ((1 + a / Real.log |t|) - β) +
                Czero * Real.log |t|) ∧
        (∀ a t : ℝ, 0 < a → a ≤ Real.log 2 → T0 ≤ |t| →
          (-deriv riemannZeta
              ((1 + a / Real.log |t| : ℝ) + 2 * I * t) /
            riemannZeta ((1 + a / Real.log |t| : ℝ) + 2 * I * t)).re ≤
              Ctwo * Real.log |t|)) :
    classical_zero_free_region := by
  rcases h with ⟨Czero, Ctwo, T0, hCzero, hCtwo, hT0, hzero, htwo⟩
  exact
    classical_zero_free_region_of_sigma_log_shift_estimates_five_fourths_nonneg_constants
      Czero Ctwo T0 hCzero hCtwo hT0 hzero htwo

/-- Same-constant version of the shifted-estimate closure.

If both shifted logarithmic-derivative estimates are available with the same
nonnegative logarithmic coefficient `B`, then the classical zero-free-region
target follows. -/
lemma classical_zero_free_region_of_sigma_log_shift_estimates_same_const
    (B T0 : ℝ) (hB : 0 ≤ B) (hT0 : 2 ≤ T0)
    (hzero :
      ∀ a c β t : ℝ, 0 < a → 0 < c → a ≤ Real.log 2 →
        T0 ≤ |t| → β < 1 →
        β ≥ 1 - c / Real.log |t| →
        0 < (1 + a / Real.log |t|) - β →
        riemannZeta ((β : ℂ) + I * t) = 0 →
        (-deriv riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t) /
          riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t)).re ≤
            -1 / ((1 + a / Real.log |t|) - β) +
              B * Real.log |t|)
    (htwo :
      ∀ a t : ℝ, 0 < a → a ≤ Real.log 2 → T0 ≤ |t| →
        (-deriv riemannZeta
            ((1 + a / Real.log |t| : ℝ) + 2 * I * t) /
          riemannZeta ((1 + a / Real.log |t| : ℝ) + 2 * I * t)).re ≤
            B * Real.log |t|) :
    classical_zero_free_region := by
  refine classical_zero_free_region_of_sigma_log_shift_estimates_five_fourths
    B B T0 ?_ hT0 hzero htwo
  nlinarith

/-- Existential high-height same-constant shifted-estimate closure.

This packages the common situation where both shifted logarithmic-derivative
estimates are proved only above some sufficiently large height.  The compact
patching already built into `classical_zero_free_region_of_sigma_log_shift_estimates_same_const`
handles the bounded-height range. -/
lemma classical_zero_free_region_of_exists_sigma_log_shift_estimates_same_const_high_height
    (h :
      ∃ B T0 : ℝ, 0 ≤ B ∧ 2 ≤ T0 ∧
        (∀ a c β t : ℝ, 0 < a → 0 < c → a ≤ Real.log 2 →
          T0 ≤ |t| → β < 1 →
          β ≥ 1 - c / Real.log |t| →
          0 < (1 + a / Real.log |t|) - β →
          riemannZeta ((β : ℂ) + I * t) = 0 →
          (-deriv riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t) /
            riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t)).re ≤
              -1 / ((1 + a / Real.log |t|) - β) +
                B * Real.log |t|) ∧
        (∀ a t : ℝ, 0 < a → a ≤ Real.log 2 → T0 ≤ |t| →
          (-deriv riemannZeta
              ((1 + a / Real.log |t| : ℝ) + 2 * I * t) /
            riemannZeta ((1 + a / Real.log |t| : ℝ) + 2 * I * t)).re ≤
              B * Real.log |t|)) :
    classical_zero_free_region := by
  rcases h with ⟨B, T0, hB, hT0, hzero, htwo⟩
  exact classical_zero_free_region_of_sigma_log_shift_estimates_same_const
    B T0 hB hT0 hzero htwo

/-- Height-`2` same-constant shifted-estimate closure.

This is the caller-facing form matching the height cutoff in
`classical_zero_free_region`: once the two shifted logarithmic-derivative
estimates hold for all `|t| >= 2` with one nonnegative logarithmic coefficient
`B`, the classical zero-free-region target follows. -/
lemma classical_zero_free_region_of_sigma_log_shift_estimates_same_const_at_two
    (B : ℝ) (hB : 0 ≤ B)
    (hzero :
      ∀ a c β t : ℝ, 0 < a → 0 < c → a ≤ Real.log 2 →
        2 ≤ |t| → β < 1 →
        β ≥ 1 - c / Real.log |t| →
        0 < (1 + a / Real.log |t|) - β →
        riemannZeta ((β : ℂ) + I * t) = 0 →
        (-deriv riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t) /
          riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t)).re ≤
            -1 / ((1 + a / Real.log |t|) - β) +
              B * Real.log |t|)
    (htwo :
      ∀ a t : ℝ, 0 < a → a ≤ Real.log 2 → 2 ≤ |t| →
        (-deriv riemannZeta
            ((1 + a / Real.log |t| : ℝ) + 2 * I * t) /
          riemannZeta ((1 + a / Real.log |t| : ℝ) + 2 * I * t)).re ≤
            B * Real.log |t|) :
    classical_zero_free_region :=
  classical_zero_free_region_of_sigma_log_shift_estimates_same_const
    B 2 hB (by norm_num) hzero htwo

/-- Existential same-constant shifted-estimate closure at height `2`.

This packages the remaining quantitative zero-free-region analytic gap into a
single input: prove that one nonnegative logarithmic coefficient `B` controls
both shifted logarithmic-derivative estimates for all `|t| >= 2`. -/
lemma classical_zero_free_region_of_exists_sigma_log_shift_estimates_same_const
    (h :
      ∃ B : ℝ, 0 ≤ B ∧
        (∀ a c β t : ℝ, 0 < a → 0 < c → a ≤ Real.log 2 →
          2 ≤ |t| → β < 1 →
          β ≥ 1 - c / Real.log |t| →
          0 < (1 + a / Real.log |t|) - β →
          riemannZeta ((β : ℂ) + I * t) = 0 →
          (-deriv riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t) /
            riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t)).re ≤
              -1 / ((1 + a / Real.log |t|) - β) +
                B * Real.log |t|) ∧
        (∀ a t : ℝ, 0 < a → a ≤ Real.log 2 → 2 ≤ |t| →
          (-deriv riemannZeta
              ((1 + a / Real.log |t| : ℝ) + 2 * I * t) /
            riemannZeta ((1 + a / Real.log |t| : ℝ) + 2 * I * t)).re ≤
              B * Real.log |t|)) :
    classical_zero_free_region := by
  rcases h with ⟨B, hB, hzero, htwo⟩
  exact classical_zero_free_region_of_sigma_log_shift_estimates_same_const_at_two
    B hB hzero htwo

/-- Close the classical zero-free-region target from a complex regular-part
logarithmic-derivative estimate and the corresponding `σ + 2it` estimate.

The hypothesis `hregular` is the Borel-Carathéodory/Jensen-style analytic
input: near a zero `ρ` at the same height as `s`, the singular contribution
`-1 / (s.re - ρ.re)` is subtracted from `Re(-ζ'/ζ)(s)`, leaving an
`O(log |Im s|)` regular part.  This lemma verifies that such a complex-shaped
estimate feeds the already proved same-constant shifted-estimate closure. -/
lemma classical_zero_free_region_of_regular_part_bound_and_two_t_bound
    (B : ℝ) (hB : 0 ≤ B)
    (hregular :
      ∀ s ρ : ℂ, 2 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
        riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
        0 < s.re - ρ.re →
        ((-deriv riemannZeta s / riemannZeta s).re +
            1 / (s.re - ρ.re)) ≤ B * Real.log |s.im|)
    (htwo :
      ∀ σ t : ℝ, 2 ≤ |t| → 1 < σ → σ ≤ 2 →
        (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
          riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤
            B * Real.log |t|) :
    classical_zero_free_region := by
  refine classical_zero_free_region_of_sigma_log_shift_estimates_same_const_at_two
    B hB ?_ ?_
  · intro a _c β t ha_pos _hc_pos ha_le_log2 ht hβ_lt _hβ hsub hζ
    let s : ℂ := ((1 + a / Real.log |t| : ℝ) : ℂ) + I * t
    let ρ : ℂ := (β : ℂ) + I * t
    have hs_re : s.re = 1 + a / Real.log |t| := by simp [s]
    have hs_im : s.im = t := by simp [s]
    have hρ_re : ρ.re = β := by simp [ρ]
    have hρ_im : ρ.im = t := by simp [ρ]
    have hs_re_gt : 1 < s.re := by
      rw [hs_re]
      exact sigmaOf_log_gt_one (T0 := 2) (by norm_num) ha_pos ht
    have hs_re_le : s.re ≤ 2 := by
      rw [hs_re]
      exact sigmaOf_log_le_two (T0 := 2) (by norm_num) ha_le_log2 ht
    have hs_re_mem : s.re ∈ Set.Icc 1 2 := ⟨hs_re_gt.le, hs_re_le⟩
    have hs_height : 2 ≤ |s.im| := by
      simpa [hs_im] using ht
    have hρ_im_eq : ρ.im = s.im := by
      simp [hρ_im, hs_im]
    have hρ_re_lt : ρ.re < 1 := by
      simpa [hρ_re] using hβ_lt
    have hsub' : 0 < s.re - ρ.re := by
      simpa [hs_re, hρ_re] using hsub
    have hζρ : riemannZeta ρ = 0 := by
      simpa [ρ] using hζ
    have hreg :=
      hregular s ρ hs_height hs_re_mem hζρ hρ_im_eq hρ_re_lt hsub'
    have hrewrite :
        (-deriv riemannZeta
              ((1 + a / Real.log |t| : ℝ) + I * t) /
            riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t)).re
          + 1 / ((1 + a / Real.log |t|) - β) ≤
            B * Real.log |t| := by
      simpa [s, ρ, hs_re, hs_im, hρ_re] using hreg
    calc
      (-deriv riemannZeta
            ((1 + a / Real.log |t| : ℝ) + I * t) /
          riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t)).re
          =
            ((-deriv riemannZeta
                ((1 + a / Real.log |t| : ℝ) + I * t) /
              riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t)).re
              + 1 / ((1 + a / Real.log |t|) - β))
              - 1 / ((1 + a / Real.log |t|) - β) := by
              ring
      _ ≤ B * Real.log |t| - 1 / ((1 + a / Real.log |t|) - β) := by
              exact sub_le_sub_right hrewrite _
      _ = -1 / ((1 + a / Real.log |t|) - β) + B * Real.log |t| := by
              ring
  · intro a t ha_pos ha_le_log2 ht
    exact htwo (1 + a / Real.log |t|) t ht
      (sigmaOf_log_gt_one (T0 := 2) (by norm_num) ha_pos ht)
      (sigmaOf_log_le_two (T0 := 2) (by norm_num) ha_le_log2 ht)

/-- Existential form of
`classical_zero_free_region_of_regular_part_bound_and_two_t_bound`, packaging
the remaining analytic input as one nonnegative logarithmic coefficient. -/
lemma classical_zero_free_region_of_exists_regular_part_bound_and_two_t_bound
    (h :
      ∃ B : ℝ, 0 ≤ B ∧
        (∀ s ρ : ℂ, 2 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
          riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
          0 < s.re - ρ.re →
          ((-deriv riemannZeta s / riemannZeta s).re +
              1 / (s.re - ρ.re)) ≤ B * Real.log |s.im|) ∧
        (∀ σ t : ℝ, 2 ≤ |t| → 1 < σ → σ ≤ 2 →
          (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
            riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤
              B * Real.log |t|)) :
    classical_zero_free_region := by
  rcases h with ⟨B, hB, hregular, htwo⟩
  exact classical_zero_free_region_of_regular_part_bound_and_two_t_bound
    B hB hregular htwo

/-- Real part of `(s - ρ)⁻¹` when `s` and `ρ` have the same imaginary part.

This is the algebraic bridge between a complex regular-part estimate
`-ζ'/ζ(s) + (s - ρ)⁻¹` and the real-variable singular term
`1 / (s.re - ρ.re)` used in the de la Vallée Poussin contradiction. -/
lemma inv_sub_same_im_re {s ρ : ℂ} (him : ρ.im = s.im)
    (hsub : 0 < s.re - ρ.re) :
    ((s - ρ)⁻¹).re = 1 / (s.re - ρ.re) := by
  have hsub_eq : s - ρ = ((s.re - ρ.re : ℝ) : ℂ) := by
    exact Complex.ext (by simp) (by simp [him])
  have hne : s.re - ρ.re ≠ 0 := ne_of_gt hsub
  rw [hsub_eq]
  rw [Complex.inv_re, Complex.normSq_ofReal]
  field_simp [hne, one_div]
  simp

/-- Convert a signed regular-part norm bound near a zeta zero into the
real-part bound used by the de la Vallee Poussin zero-repulsion argument. -/
lemma re_neg_deriv_div_riemannZeta_add_inv_le_of_regular_part_norm
    {s ρ : ℂ} {M : ℝ}
    (hregular :
      ‖-deriv riemannZeta s / riemannZeta s + (s - ρ)⁻¹‖ ≤ M)
    (him : ρ.im = s.im) (hsub : 0 < s.re - ρ.re) :
    (-deriv riemannZeta s / riemannZeta s).re +
        1 / (s.re - ρ.re) ≤ M := by
  let regularPart : ℂ :=
    -deriv riemannZeta s / riemannZeta s + (s - ρ)⁻¹
  have hregular_norm : ‖regularPart‖ ≤ M := by
    simpa [regularPart] using hregular
  have hregular_re_le :
      regularPart.re ≤ ‖regularPart‖ :=
    le_trans (le_abs_self regularPart.re) (abs_re_le_norm regularPart)
  have hregular_re :
      regularPart.re =
        (-deriv riemannZeta s / riemannZeta s).re +
          1 / (s.re - ρ.re) := by
    simp [regularPart, inv_sub_same_im_re him hsub]
  calc
    (-deriv riemannZeta s / riemannZeta s).re +
        1 / (s.re - ρ.re)
        = regularPart.re := hregular_re.symm
    _ ≤ ‖regularPart‖ := hregular_re_le
    _ ≤ M := hregular_norm

/-- Multiplicity-aware version of
`re_neg_deriv_div_riemannZeta_add_inv_le_of_regular_part_norm`.

If a local argument isolates `n (s-rho)^{-1}` with `n >= 1`, the same norm
bound still implies the weaker unit-principal real-part inequality needed in
the zero-free-region contradiction. -/
lemma re_neg_deriv_div_riemannZeta_add_inv_le_of_multiplicity_regular_part_norm
    {s ρ : ℂ} {n : ℕ} {M : ℝ}
    (hregular :
      ‖-deriv riemannZeta s / riemannZeta s +
          (n : ℂ) * (s - ρ)⁻¹‖ ≤ M)
    (hn : 0 < n) (him : ρ.im = s.im)
    (hsub : 0 < s.re - ρ.re) :
    (-deriv riemannZeta s / riemannZeta s).re +
        1 / (s.re - ρ.re) ≤ M := by
  let regularPart : ℂ :=
    -deriv riemannZeta s / riemannZeta s + (n : ℂ) * (s - ρ)⁻¹
  have hregular_norm : ‖regularPart‖ ≤ M := by
    simpa [regularPart] using hregular
  have hregular_re_le :
      regularPart.re ≤ ‖regularPart‖ :=
    le_trans (le_abs_self regularPart.re) (abs_re_le_norm regularPart)
  have hinv_re : ((s - ρ)⁻¹).re = 1 / (s.re - ρ.re) :=
    inv_sub_same_im_re him hsub
  have hregular_re :
      regularPart.re =
        (-deriv riemannZeta s / riemannZeta s).re +
          (n : ℝ) * (1 / (s.re - ρ.re)) := by
    simp [regularPart, hinv_re]
  have hunit_le_mult :
      1 / (s.re - ρ.re) ≤ (n : ℝ) * (1 / (s.re - ρ.re)) := by
    have hnonneg : 0 ≤ 1 / (s.re - ρ.re) := by
      positivity
    have hn_one : (1 : ℝ) ≤ n := by
      exact_mod_cast Nat.succ_le_iff.mpr hn
    simpa using mul_le_mul_of_nonneg_right hn_one hnonneg
  calc
    (-deriv riemannZeta s / riemannZeta s).re +
        1 / (s.re - ρ.re)
        ≤ regularPart.re := by
          rw [hregular_re]
          linarith
    _ ≤ ‖regularPart‖ := hregular_re_le
    _ ≤ M := hregular_norm

/-- Signed `-logDeriv zeta` notation form of
`re_neg_deriv_div_riemannZeta_add_inv_le_of_regular_part_norm`. -/
lemma re_neg_logDeriv_riemannZeta_add_inv_le_of_regular_part_norm
    {s ρ : ℂ} {M : ℝ}
    (hregular : ‖-logDeriv riemannZeta s + (s - ρ)⁻¹‖ ≤ M)
    (him : ρ.im = s.im) (hsub : 0 < s.re - ρ.re) :
    (-deriv riemannZeta s / riemannZeta s).re +
        1 / (s.re - ρ.re) ≤ M :=
  re_neg_deriv_div_riemannZeta_add_inv_le_of_regular_part_norm
    (by simpa [neg_logDeriv_riemannZeta_eq_neg_deriv_div] using hregular)
    him hsub

/-- Multiplicity-aware signed `-logDeriv zeta` notation form of the
regular-part norm to real-part bridge. -/
lemma re_neg_logDeriv_riemannZeta_add_inv_le_of_multiplicity_regular_part_norm
    {s ρ : ℂ} {n : ℕ} {M : ℝ}
    (hregular :
      ‖-logDeriv riemannZeta s + (n : ℂ) * (s - ρ)⁻¹‖ ≤ M)
    (hn : 0 < n) (him : ρ.im = s.im)
    (hsub : 0 < s.re - ρ.re) :
    (-deriv riemannZeta s / riemannZeta s).re +
        1 / (s.re - ρ.re) ≤ M :=
  re_neg_deriv_div_riemannZeta_add_inv_le_of_multiplicity_regular_part_norm
    (by simpa [neg_logDeriv_riemannZeta_eq_neg_deriv_div] using hregular)
    hn him hsub

/-- Coordinate form of the signed regular-part bridge at `s = sigma + i t`
and a same-height zero candidate `rho = beta + i t`. -/
lemma re_neg_logDeriv_riemannZeta_sigma_it_add_inv_le_of_regular_part_norm
    {σ β t M : ℝ}
    (hregular :
      ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
          (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤ M)
    (hsub : 0 < σ - β) :
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re +
      1 / (σ - β) ≤ M := by
  let s : ℂ := (σ : ℂ) + I * t
  let ρ : ℂ := (β : ℂ) + I * t
  have hρ_im_eq : ρ.im = s.im := by simp [ρ, s]
  have hsub' : 0 < s.re - ρ.re := by simpa [s, ρ] using hsub
  have hinv :
      (((σ - β : ℝ) : ℂ)⁻¹) = (s - ρ)⁻¹ := by
    have hsub_eq : s - ρ = ((σ - β : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [s, ρ]
    rw [← hsub_eq]
  have hregular' :
      ‖-logDeriv riemannZeta s + (s - ρ)⁻¹‖ ≤ M := by
    calc
      ‖-logDeriv riemannZeta s + (s - ρ)⁻¹‖
          = ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
              (((σ - β : ℝ) : ℂ)⁻¹)‖ := by
              rw [← hinv]
      _ ≤ M := hregular
  have h :=
    re_neg_logDeriv_riemannZeta_add_inv_le_of_regular_part_norm
      hregular' hρ_im_eq hsub'
  simpa [s, ρ] using h

/-- Multiplicity-aware coordinate form of the signed regular-part bridge at
`s = sigma + i t` and `rho = beta + i t`. -/
lemma re_neg_logDeriv_riemannZeta_sigma_it_add_inv_le_of_multiplicity_regular_part_norm
    {σ β t M : ℝ} {n : ℕ}
    (hregular :
      ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
          (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤ M)
    (hn : 0 < n) (hsub : 0 < σ - β) :
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re +
      1 / (σ - β) ≤ M := by
  let s : ℂ := (σ : ℂ) + I * t
  let ρ : ℂ := (β : ℂ) + I * t
  have hρ_im_eq : ρ.im = s.im := by simp [ρ, s]
  have hsub' : 0 < s.re - ρ.re := by simpa [s, ρ] using hsub
  have hinv :
      (((σ - β : ℝ) : ℂ)⁻¹) = (s - ρ)⁻¹ := by
    have hsub_eq : s - ρ = ((σ - β : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [s, ρ]
    rw [← hsub_eq]
  have hregular' :
      ‖-logDeriv riemannZeta s + (n : ℂ) * (s - ρ)⁻¹‖ ≤ M := by
    calc
      ‖-logDeriv riemannZeta s + (n : ℂ) * (s - ρ)⁻¹‖
          = ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
              (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖ := by
              rw [← hinv]
      _ ≤ M := hregular
  have h :=
    re_neg_logDeriv_riemannZeta_add_inv_le_of_multiplicity_regular_part_norm
      hregular' hn hρ_im_eq hsub'
  simpa [s, ρ] using h

/-- Coordinate bridge for the common `C * (1 + log |t|)` local regular-part
bound, normalized to a pure logarithmic bound at heights `|t| >= 3`. -/
lemma re_neg_logDeriv_riemannZeta_sigma_it_add_inv_le_of_regular_part_norm_one_add_log
    {σ β t C : ℝ}
    (hC : 0 ≤ C) (ht : 3 ≤ |t|)
    (hregular :
      ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
          (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
        C * (1 + Real.log |t|))
    (hsub : 0 < σ - β) :
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re +
      1 / (σ - β) ≤ (2 * C) * Real.log |t| := by
  have hbase :=
    re_neg_logDeriv_riemannZeta_sigma_it_add_inv_le_of_regular_part_norm
      hregular hsub
  have hlog_ge_one : 1 ≤ Real.log |t| :=
    (log_abs_gt_one_of_three_le ht).le
  have hC_le : C ≤ C * Real.log |t| := by
    calc
      C = C * 1 := by ring
      _ ≤ C * Real.log |t| := mul_le_mul_of_nonneg_left hlog_ge_one hC
  calc
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re +
      1 / (σ - β)
        ≤ C * (1 + Real.log |t|) := hbase
    _ = C + C * Real.log |t| := by ring
    _ ≤ (2 * C) * Real.log |t| := by nlinarith

/-- Multiplicity-aware coordinate bridge for the common
`C * (1 + log |t|)` local regular-part bound. -/
lemma re_neg_logDeriv_riemannZeta_sigma_it_add_inv_le_of_multiplicity_regular_part_norm_one_add_log
    {σ β t C : ℝ} {n : ℕ}
    (hC : 0 ≤ C) (ht : 3 ≤ |t|)
    (hregular :
      ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
          (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
        C * (1 + Real.log |t|))
    (hn : 0 < n) (hsub : 0 < σ - β) :
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re +
      1 / (σ - β) ≤ (2 * C) * Real.log |t| := by
  have hbase :=
    re_neg_logDeriv_riemannZeta_sigma_it_add_inv_le_of_multiplicity_regular_part_norm
      hregular hn hsub
  have hlog_ge_one : 1 ≤ Real.log |t| :=
    (log_abs_gt_one_of_three_le ht).le
  have hC_le : C ≤ C * Real.log |t| := by
    calc
      C = C * 1 := by ring
      _ ≤ C * Real.log |t| := mul_le_mul_of_nonneg_left hlog_ge_one hC
  calc
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re +
      1 / (σ - β)
        ≤ C * (1 + Real.log |t|) := hbase
    _ = C + C * Real.log |t| := by ring
    _ ≤ (2 * C) * Real.log |t| := by nlinarith

/-- Close the classical zero-free-region target from a norm bound on the
complex regular part of `-ζ'/ζ` near a zero and the corresponding `σ + 2it`
estimate.

This is the form closest to the output of a future Borel-Carathéodory/Jensen
argument: the analytic input bounds the norm of
`-ζ'/ζ(s) + (s - ρ)⁻¹`; this lemma converts that norm estimate into the
real-part regular estimate consumed by
`classical_zero_free_region_of_regular_part_bound_and_two_t_bound`. -/
lemma classical_zero_free_region_of_regular_part_norm_bound_and_two_t_bound
    (B : ℝ) (hB : 0 ≤ B)
    (hregular :
      ∀ s ρ : ℂ, 2 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
        riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
        0 < s.re - ρ.re →
        ‖-deriv riemannZeta s / riemannZeta s + (s - ρ)⁻¹‖ ≤
          B * Real.log |s.im|)
    (htwo :
      ∀ σ t : ℝ, 2 ≤ |t| → 1 < σ → σ ≤ 2 →
        (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
          riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤
            B * Real.log |t|) :
    classical_zero_free_region := by
  refine classical_zero_free_region_of_regular_part_bound_and_two_t_bound
    B hB ?_ htwo
  intro s ρ hs_height hs_re_mem hζρ hρ_im_eq hρ_re_lt hsub
  exact
    re_neg_deriv_div_riemannZeta_add_inv_le_of_regular_part_norm
      (hregular s ρ hs_height hs_re_mem hζρ hρ_im_eq hρ_re_lt hsub)
      hρ_im_eq hsub

/-- Multiplicity-aware regular-part zero-free closure.

Future local arguments naturally isolate
`-ζ'/ζ(s) + n (s - ρ)⁻¹`, where `n` is the zero multiplicity.  Since
`n ≥ 1`, this still supplies the unit-principal-part real inequality consumed
by `classical_zero_free_region_of_regular_part_bound_and_two_t_bound`. -/
lemma classical_zero_free_region_of_exists_multiplicity_regular_part_norm_bound_and_two_t_bound
    (B : ℝ) (hB : 0 ≤ B)
    (hregular :
      ∀ s ρ : ℂ, 2 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
        riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
        0 < s.re - ρ.re →
        ∃ n : ℕ, 0 < n ∧
          ‖-deriv riemannZeta s / riemannZeta s + (n : ℂ) * (s - ρ)⁻¹‖ ≤
            B * Real.log |s.im|)
    (htwo :
      ∀ σ t : ℝ, 2 ≤ |t| → 1 < σ → σ ≤ 2 →
        (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
          riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤
            B * Real.log |t|) :
    classical_zero_free_region := by
  refine classical_zero_free_region_of_regular_part_bound_and_two_t_bound
    B hB ?_ htwo
  intro s ρ hs_height hs_re_mem hζρ hρ_im_eq hρ_re_lt hsub
  rcases hregular s ρ hs_height hs_re_mem hζρ hρ_im_eq hρ_re_lt hsub with
    ⟨n, hn_pos, hn_bound⟩
  exact
    re_neg_deriv_div_riemannZeta_add_inv_le_of_multiplicity_regular_part_norm
      hn_bound hn_pos hρ_im_eq hsub

/-- Existential norm-bound form of the regular-part zero-free closure. -/
lemma classical_zero_free_region_of_exists_regular_part_norm_bound_and_two_t_bound
    (h :
      ∃ B : ℝ, 0 ≤ B ∧
        (∀ s ρ : ℂ, 2 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
          riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
          0 < s.re - ρ.re →
          ‖-deriv riemannZeta s / riemannZeta s + (s - ρ)⁻¹‖ ≤
            B * Real.log |s.im|) ∧
        (∀ σ t : ℝ, 2 ≤ |t| → 1 < σ → σ ≤ 2 →
          (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
            riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤
              B * Real.log |t|)) :
    classical_zero_free_region := by
  rcases h with ⟨B, hB, hregular, htwo⟩
  exact classical_zero_free_region_of_regular_part_norm_bound_and_two_t_bound
    B hB hregular htwo

/-- Logarithmic-derivative notation form of the norm-bound regular-part
closure.

Future Borel/Jensen arguments naturally produce estimates for `logDeriv ζ`.
This wrapper rewrites those estimates into the quotient notation
`-ζ'/ζ` used by the 3-4-1 machinery. -/
lemma classical_zero_free_region_of_neg_logDeriv_regular_part_norm_bound_and_two_t_bound
    (B : ℝ) (hB : 0 ≤ B)
    (hregular :
      ∀ s ρ : ℂ, 2 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
        riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
        0 < s.re - ρ.re →
        ‖-logDeriv riemannZeta s + (s - ρ)⁻¹‖ ≤ B * Real.log |s.im|)
    (htwo :
      ∀ σ t : ℝ, 2 ≤ |t| → 1 < σ → σ ≤ 2 →
        (-logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤
          B * Real.log |t|) :
    classical_zero_free_region := by
  refine classical_zero_free_region_of_regular_part_norm_bound_and_two_t_bound
    B hB ?_ ?_
  · intro s ρ hs_height hs_re_mem hζρ hρ_im_eq hρ_re_lt hsub
    simpa [neg_logDeriv_riemannZeta_eq_neg_deriv_div] using
      hregular s ρ hs_height hs_re_mem hζρ hρ_im_eq hρ_re_lt hsub
  · intro σ t ht hσ_gt hσ_le
    simpa [neg_logDeriv_riemannZeta_eq_neg_deriv_div] using
      htwo σ t ht hσ_gt hσ_le

/-- Multiplicity-aware `-logDeriv ζ` notation form of the regular-part
zero-free closure. -/
lemma classical_zero_free_region_of_exists_multiplicity_neg_logDeriv_regular_part_norm_bound_and_two_t_bound
    (B : ℝ) (hB : 0 ≤ B)
    (hregular :
      ∀ s ρ : ℂ, 2 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
        riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
        0 < s.re - ρ.re →
        ∃ n : ℕ, 0 < n ∧
          ‖-logDeriv riemannZeta s + (n : ℂ) * (s - ρ)⁻¹‖ ≤
            B * Real.log |s.im|)
    (htwo :
      ∀ σ t : ℝ, 2 ≤ |t| → 1 < σ → σ ≤ 2 →
        (-logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤
          B * Real.log |t|) :
    classical_zero_free_region := by
  refine classical_zero_free_region_of_exists_multiplicity_regular_part_norm_bound_and_two_t_bound
    B hB ?_ ?_
  · intro s ρ hs_height hs_re_mem hζρ hρ_im_eq hρ_re_lt hsub
    rcases hregular s ρ hs_height hs_re_mem hζρ hρ_im_eq hρ_re_lt hsub with
      ⟨n, hn_pos, hn_bound⟩
    exact ⟨n, hn_pos, by
      simpa [neg_logDeriv_riemannZeta_eq_neg_deriv_div] using hn_bound⟩
  · intro σ t ht hσ_gt hσ_le
    simpa [neg_logDeriv_riemannZeta_eq_neg_deriv_div] using
      htwo σ t ht hσ_gt hσ_le

/-- Existential logarithmic-derivative notation form of the norm-bound
regular-part closure. -/
lemma classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_bound_and_two_t_bound
    (h :
      ∃ B : ℝ, 0 ≤ B ∧
        (∀ s ρ : ℂ, 2 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
          riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
          0 < s.re - ρ.re →
          ‖-logDeriv riemannZeta s + (s - ρ)⁻¹‖ ≤ B * Real.log |s.im|) ∧
        (∀ σ t : ℝ, 2 ≤ |t| → 1 < σ → σ ≤ 2 →
          (-logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤
            B * Real.log |t|)) :
    classical_zero_free_region := by
  rcases h with ⟨B, hB, hregular, htwo⟩
  exact classical_zero_free_region_of_neg_logDeriv_regular_part_norm_bound_and_two_t_bound
    B hB hregular htwo

/-- Two-coefficient version of the `-logDeriv ζ` norm-bound regular-part
closure.

The remaining analytic estimates may naturally come with different
nonnegative logarithmic coefficients.  This lemma verifies that the zero-free
region chain only needs their maximum. -/
lemma classical_zero_free_region_of_neg_logDeriv_regular_part_norm_bounds
    (Bregular Btwo : ℝ) (hBregular : 0 ≤ Bregular) (_hBtwo : 0 ≤ Btwo)
    (hregular :
      ∀ s ρ : ℂ, 2 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
        riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
        0 < s.re - ρ.re →
        ‖-logDeriv riemannZeta s + (s - ρ)⁻¹‖ ≤
          Bregular * Real.log |s.im|)
    (htwo :
      ∀ σ t : ℝ, 2 ≤ |t| → 1 < σ → σ ≤ 2 →
        (-logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤
          Btwo * Real.log |t|) :
    classical_zero_free_region := by
  refine classical_zero_free_region_of_neg_logDeriv_regular_part_norm_bound_and_two_t_bound
    (max Bregular Btwo) (le_max_of_le_left hBregular) ?_ ?_
  · intro s ρ hs_height hs_re_mem hζρ hρ_im_eq hρ_re_lt hsub
    have hlog_nonneg : 0 ≤ Real.log |s.im| :=
      (log_abs_pos_of_two_le hs_height).le
    exact le_trans
      (hregular s ρ hs_height hs_re_mem hζρ hρ_im_eq hρ_re_lt hsub)
      (mul_le_mul_of_nonneg_right (le_max_left Bregular Btwo) hlog_nonneg)
  · intro σ t ht hσ_gt hσ_le
    have hlog_nonneg : 0 ≤ Real.log |t| :=
      (log_abs_pos_of_two_le ht).le
    exact le_trans (htwo σ t ht hσ_gt hσ_le)
      (mul_le_mul_of_nonneg_right (le_max_right Bregular Btwo) hlog_nonneg)

/-- Existential two-coefficient version of the `-logDeriv ζ` norm-bound
regular-part closure. -/
lemma classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_bounds
    (h :
      ∃ Bregular Btwo : ℝ, 0 ≤ Bregular ∧ 0 ≤ Btwo ∧
        (∀ s ρ : ℂ, 2 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
          riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
          0 < s.re - ρ.re →
          ‖-logDeriv riemannZeta s + (s - ρ)⁻¹‖ ≤
            Bregular * Real.log |s.im|) ∧
        (∀ σ t : ℝ, 2 ≤ |t| → 1 < σ → σ ≤ 2 →
          (-logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤
            Btwo * Real.log |t|)) :
    classical_zero_free_region := by
  rcases h with ⟨Bregular, Btwo, hBregular, hBtwo, hregular, htwo⟩
  exact classical_zero_free_region_of_neg_logDeriv_regular_part_norm_bounds
    Bregular Btwo hBregular hBtwo hregular htwo

/-- Fully norm-bound version of the `-logDeriv ζ` regular-part closure.

Both remaining analytic inputs are allowed to be norm estimates: one for the
regular part near a zero, and one for the `σ + 2it` shifted logarithmic
derivative.  Real-part bounds are obtained by `Re(z) <= ||z||`. -/
lemma classical_zero_free_region_of_neg_logDeriv_regular_part_norm_and_two_t_norm_bounds
    (Bregular Btwo : ℝ) (hBregular : 0 ≤ Bregular) (hBtwo : 0 ≤ Btwo)
    (hregular :
      ∀ s ρ : ℂ, 2 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
        riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
        0 < s.re - ρ.re →
        ‖-logDeriv riemannZeta s + (s - ρ)⁻¹‖ ≤
          Bregular * Real.log |s.im|)
    (htwo :
      ∀ σ t : ℝ, 2 ≤ |t| → 1 < σ → σ ≤ 2 →
        ‖-logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖ ≤
          Btwo * Real.log |t|) :
    classical_zero_free_region := by
  refine classical_zero_free_region_of_neg_logDeriv_regular_part_norm_bounds
    Bregular Btwo hBregular hBtwo hregular ?_
  intro σ t ht hσ_gt hσ_le
  exact le_trans
    (le_trans
      (le_abs_self
        ((-logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)).re))
      (abs_re_le_norm (-logDeriv riemannZeta ((σ : ℂ) + 2 * I * t))))
    (htwo σ t ht hσ_gt hσ_le)

/-- Existential fully norm-bound version of the `-logDeriv ζ` regular-part
closure. -/
lemma classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_and_two_t_norm_bounds
    (h :
      ∃ Bregular Btwo : ℝ, 0 ≤ Bregular ∧ 0 ≤ Btwo ∧
        (∀ s ρ : ℂ, 2 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
          riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
          0 < s.re - ρ.re →
          ‖-logDeriv riemannZeta s + (s - ρ)⁻¹‖ ≤
            Bregular * Real.log |s.im|) ∧
        (∀ σ t : ℝ, 2 ≤ |t| → 1 < σ → σ ≤ 2 →
          ‖-logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖ ≤
            Btwo * Real.log |t|)) :
    classical_zero_free_region := by
  rcases h with ⟨Bregular, Btwo, hBregular, hBtwo, hregular, htwo⟩
  exact classical_zero_free_region_of_neg_logDeriv_regular_part_norm_and_two_t_norm_bounds
    Bregular Btwo hBregular hBtwo hregular htwo

/-- Logarithmic comparison used when a vertical-strip estimate is applied at
height `2t` but the zero-free-region target is stated in terms of `log |t|`. -/
lemma log_abs_two_mul_le_two_log_abs {t : ℝ} (ht : 2 ≤ |t|) :
    Real.log |(2 : ℝ) * t| ≤ 2 * Real.log |t| := by
  have ht_pos : 0 < |t| := lt_of_lt_of_le (by norm_num) ht
  have hlog_two_le : Real.log 2 ≤ Real.log |t| :=
    Real.log_le_log (by norm_num) ht
  calc
    Real.log |(2 : ℝ) * t| = Real.log (2 * |t|) := by
      simp [abs_mul]
    _ = Real.log 2 + Real.log |t| := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt ht_pos)]
    _ ≤ 2 * Real.log |t| := by
      linarith

/-- Closure from a zero-candidate regular-part norm estimate and a vertical-strip
norm estimate for `-logDeriv ζ`.

The vertical estimate is stated for all `z` with `1 <= Re z <= 2` and
`|Im z| >= 2`; this wrapper specializes it to the `σ+2it` point needed by the
3-4-1 combination, paying only a factor of `2` in the logarithmic coefficient. -/
lemma classical_zero_free_region_of_neg_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound
    (Bregular Bvertical : ℝ)
    (hBregular : 0 ≤ Bregular) (hBvertical : 0 ≤ Bvertical)
    (hregular :
      ∀ s ρ : ℂ, 2 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
        riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
        0 < s.re - ρ.re →
        ‖-logDeriv riemannZeta s + (s - ρ)⁻¹‖ ≤
          Bregular * Real.log |s.im|)
    (hvertical :
      ∀ z : ℂ, 2 ≤ |z.im| → z.re ∈ Set.Icc 1 2 →
        ‖-logDeriv riemannZeta z‖ ≤ Bvertical * Real.log |z.im|) :
    classical_zero_free_region := by
  refine
    classical_zero_free_region_of_neg_logDeriv_regular_part_norm_and_two_t_norm_bounds
      Bregular (2 * Bvertical) hBregular (by nlinarith) hregular ?_
  intro σ t ht hσ_gt hσ_le
  let z : ℂ := (σ : ℂ) + 2 * I * t
  have hz_re_mem : z.re ∈ Set.Icc 1 2 := by
    simp [z, hσ_gt.le, hσ_le]
  have hz_height : 2 ≤ |z.im| := by
    have hz_im_abs : |z.im| = |(2 : ℝ) * t| := by
      simp [z, abs_mul]
    have htwo_abs : |(2 : ℝ) * t| = 2 * |t| := by
      rw [abs_mul]
      norm_num
    rw [hz_im_abs, htwo_abs]
    have ht_nonneg : 0 ≤ |t| := abs_nonneg t
    nlinarith
  have hlog :
      Real.log |z.im| ≤ 2 * Real.log |t| := by
    have hz_im_abs : |z.im| = |(2 : ℝ) * t| := by
      simp [z, abs_mul]
    rw [hz_im_abs]
    exact log_abs_two_mul_le_two_log_abs ht
  have hbound := hvertical z hz_height hz_re_mem
  calc
    ‖-logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖
        = ‖-logDeriv riemannZeta z‖ := by simp [z]
    _ ≤ Bvertical * Real.log |z.im| := hbound
    _ ≤ Bvertical * (2 * Real.log |t|) :=
        mul_le_mul_of_nonneg_left hlog hBvertical
    _ = (2 * Bvertical) * Real.log |t| := by ring

/-- Existential version of
`classical_zero_free_region_of_neg_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound`. -/
lemma classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound
    (h :
      ∃ Bregular Bvertical : ℝ, 0 ≤ Bregular ∧ 0 ≤ Bvertical ∧
        (∀ s ρ : ℂ, 2 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
          riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
          0 < s.re - ρ.re →
          ‖-logDeriv riemannZeta s + (s - ρ)⁻¹‖ ≤
            Bregular * Real.log |s.im|) ∧
        (∀ z : ℂ, 2 ≤ |z.im| → z.re ∈ Set.Icc 1 2 →
          ‖-logDeriv riemannZeta z‖ ≤ Bvertical * Real.log |z.im|)) :
    classical_zero_free_region := by
  rcases h with ⟨Bregular, Bvertical, hBregular, hBvertical, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_neg_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound
      Bregular Bvertical hBregular hBvertical hregular hvertical

/-- Sign-convention wrapper for the regular-part/vertical-strip closure.

Local zero estimates are often stated as
`logDeriv ζ(s) - (s - ρ)⁻¹ = O(log |Im s|)`.  The 3-4-1 chain uses the
equivalent signed form `-logDeriv ζ(s) + (s - ρ)⁻¹`; this lemma performs only
that sign conversion, together with the harmless norm equality
`||-logDeriv ζ|| = ||logDeriv ζ||` for the vertical estimate. -/
lemma classical_zero_free_region_of_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound
    (Bregular Bvertical : ℝ)
    (hBregular : 0 ≤ Bregular) (hBvertical : 0 ≤ Bvertical)
    (hregular :
      ∀ s ρ : ℂ, 2 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
        riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
        0 < s.re - ρ.re →
        ‖logDeriv riemannZeta s - (s - ρ)⁻¹‖ ≤
          Bregular * Real.log |s.im|)
    (hvertical :
      ∀ z : ℂ, 2 ≤ |z.im| → z.re ∈ Set.Icc 1 2 →
        ‖logDeriv riemannZeta z‖ ≤ Bvertical * Real.log |z.im|) :
    classical_zero_free_region := by
  refine
    classical_zero_free_region_of_neg_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound
      Bregular Bvertical hBregular hBvertical ?_ ?_
  · intro s ρ hs_height hs_re_mem hζρ hρ_im_eq hρ_re_lt hsub
    calc
      ‖-logDeriv riemannZeta s + (s - ρ)⁻¹‖
          = ‖-(logDeriv riemannZeta s - (s - ρ)⁻¹)‖ := by ring_nf
      _ = ‖logDeriv riemannZeta s - (s - ρ)⁻¹‖ := norm_neg _
      _ ≤ Bregular * Real.log |s.im| :=
          hregular s ρ hs_height hs_re_mem hζρ hρ_im_eq hρ_re_lt hsub
  · intro z hz_height hz_re_mem
    calc
      ‖-logDeriv riemannZeta z‖ = ‖logDeriv riemannZeta z‖ := norm_neg _
      _ ≤ Bvertical * Real.log |z.im| := hvertical z hz_height hz_re_mem

/-- Existential sign-convention wrapper for the regular-part/vertical-strip
closure. -/
lemma classical_zero_free_region_of_exists_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound
    (h :
      ∃ Bregular Bvertical : ℝ, 0 ≤ Bregular ∧ 0 ≤ Bvertical ∧
        (∀ s ρ : ℂ, 2 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
          riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
          0 < s.re - ρ.re →
          ‖logDeriv riemannZeta s - (s - ρ)⁻¹‖ ≤
            Bregular * Real.log |s.im|) ∧
        (∀ z : ℂ, 2 ≤ |z.im| → z.re ∈ Set.Icc 1 2 →
          ‖logDeriv riemannZeta z‖ ≤ Bvertical * Real.log |z.im|)) :
    classical_zero_free_region := by
  rcases h with ⟨Bregular, Bvertical, hBregular, hBvertical, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound
      Bregular Bvertical hBregular hBvertical hregular hvertical

/-- High-height version of the positive `logDeriv ζ` regular-part/vertical-strip
closure.

Future Borel-Carathéodory or Jensen estimates are usually proved only above a
sufficiently large height.  This wrapper accepts the two remaining analytic
inputs only on `T0 <= |Im|`, then uses the already verified compact patch to
fill the bounded-height gap in the final classical zero-free-region target. -/
lemma classical_zero_free_region_of_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height
    (T0 Bregular Bvertical : ℝ)
    (hT0 : 2 ≤ T0) (hBregular : 0 ≤ Bregular)
    (hBvertical : 0 ≤ Bvertical)
    (hregular :
      ∀ s ρ : ℂ, T0 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
        riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
        0 < s.re - ρ.re →
        ‖logDeriv riemannZeta s - (s - ρ)⁻¹‖ ≤
          Bregular * Real.log |s.im|)
    (hvertical :
      ∀ z : ℂ, T0 ≤ |z.im| → z.re ∈ Set.Icc 1 2 →
        ‖logDeriv riemannZeta z‖ ≤ Bvertical * Real.log |z.im|) :
    classical_zero_free_region := by
  let B : ℝ := max Bregular (2 * Bvertical)
  have hB : 0 ≤ B := le_trans hBregular (le_max_left Bregular (2 * Bvertical))
  refine classical_zero_free_region_of_sigma_log_shift_estimates_same_const
    B T0 hB hT0 ?_ ?_
  · intro a c β t ha_pos _hc_pos ha_le_log2 ht hβ_lt _hβ hsub hζ
    let s : ℂ := ((1 + a / Real.log |t| : ℝ) : ℂ) + I * t
    let ρ : ℂ := (β : ℂ) + I * t
    have hs_re : s.re = 1 + a / Real.log |t| := by simp [s]
    have hs_im : s.im = t := by simp [s]
    have hρ_re : ρ.re = β := by simp [ρ]
    have hρ_im : ρ.im = t := by simp [ρ]
    have hs_re_gt : 1 < s.re := by
      rw [hs_re]
      exact sigmaOf_log_gt_one hT0 ha_pos ht
    have hs_re_le : s.re ≤ 2 := by
      rw [hs_re]
      exact sigmaOf_log_le_two hT0 ha_le_log2 ht
    have hs_re_mem : s.re ∈ Set.Icc 1 2 := ⟨hs_re_gt.le, hs_re_le⟩
    have hs_height : T0 ≤ |s.im| := by
      simpa [hs_im] using ht
    have hρ_im_eq : ρ.im = s.im := by
      simp [hρ_im, hs_im]
    have hρ_re_lt : ρ.re < 1 := by
      simpa [hρ_re] using hβ_lt
    have hsub' : 0 < s.re - ρ.re := by
      simpa [hs_re, hρ_re] using hsub
    have hζρ : riemannZeta ρ = 0 := by
      simpa [ρ] using hζ
    have hreg_pos :=
      hregular s ρ hs_height hs_re_mem hζρ hρ_im_eq hρ_re_lt hsub'
    have hreg_signed :
        ‖-logDeriv riemannZeta s + (s - ρ)⁻¹‖ ≤
          Bregular * Real.log |s.im| := by
      calc
        ‖-logDeriv riemannZeta s + (s - ρ)⁻¹‖
            = ‖-(logDeriv riemannZeta s - (s - ρ)⁻¹)‖ := by ring_nf
        _ = ‖logDeriv riemannZeta s - (s - ρ)⁻¹‖ := norm_neg _
        _ ≤ Bregular * Real.log |s.im| := hreg_pos
    have hreg_re :
        (-deriv riemannZeta s / riemannZeta s).re +
            1 / (s.re - ρ.re) ≤
          Bregular * Real.log |s.im| :=
      re_neg_logDeriv_riemannZeta_add_inv_le_of_regular_part_norm
        hreg_signed hρ_im_eq hsub'
    have hlog_nonneg : 0 ≤ Real.log |t| :=
      (log_abs_pos_of_two_le (hT0.trans ht)).le
    have hBregular_le_B : Bregular ≤ B := le_max_left Bregular (2 * Bvertical)
    have hrewrite :
        (-deriv riemannZeta
              ((1 + a / Real.log |t| : ℝ) + I * t) /
            riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t)).re
          + 1 / ((1 + a / Real.log |t|) - β) ≤
            B * Real.log |t| := by
      calc
        (-deriv riemannZeta
              ((1 + a / Real.log |t| : ℝ) + I * t) /
            riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t)).re
          + 1 / ((1 + a / Real.log |t|) - β)
            ≤ Bregular * Real.log |t| := by
              simpa [s, ρ, hs_re, hs_im, hρ_re] using hreg_re
        _ ≤ B * Real.log |t| :=
              mul_le_mul_of_nonneg_right hBregular_le_B hlog_nonneg
    calc
      (-deriv riemannZeta
            ((1 + a / Real.log |t| : ℝ) + I * t) /
          riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t)).re
          =
            ((-deriv riemannZeta
                ((1 + a / Real.log |t| : ℝ) + I * t) /
              riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t)).re
              + 1 / ((1 + a / Real.log |t|) - β))
              - 1 / ((1 + a / Real.log |t|) - β) := by
              ring
      _ ≤ B * Real.log |t| - 1 / ((1 + a / Real.log |t|) - β) := by
              exact sub_le_sub_right hrewrite _
      _ = -1 / ((1 + a / Real.log |t|) - β) + B * Real.log |t| := by
              ring
  · intro a t ha_pos ha_le_log2 ht
    let z : ℂ := ((1 + a / Real.log |t| : ℝ) : ℂ) + 2 * I * t
    have hz_re_mem : z.re ∈ Set.Icc 1 2 := by
      have hz_re : z.re = 1 + a / Real.log |t| := by simp [z]
      exact ⟨by
        rw [hz_re]
        exact (sigmaOf_log_gt_one hT0 ha_pos ht).le,
        by
          rw [hz_re]
          exact sigmaOf_log_le_two hT0 ha_le_log2 ht⟩
    have hz_height : T0 ≤ |z.im| := by
      have hz_im_abs : |z.im| = |(2 : ℝ) * t| := by
        simp [z, abs_mul]
      have htwo_abs : |(2 : ℝ) * t| = 2 * |t| := by
        rw [abs_mul]
        norm_num
      rw [hz_im_abs, htwo_abs]
      have ht_nonneg : 0 ≤ |t| := abs_nonneg t
      nlinarith
    have hlog :
        Real.log |z.im| ≤ 2 * Real.log |t| := by
      have hz_im_abs : |z.im| = |(2 : ℝ) * t| := by
        simp [z, abs_mul]
      rw [hz_im_abs]
      exact log_abs_two_mul_le_two_log_abs (hT0.trans ht)
    have hlog_nonneg : 0 ≤ Real.log |t| :=
      (log_abs_pos_of_two_le (hT0.trans ht)).le
    have htwoB_le : 2 * Bvertical ≤ B := le_max_right Bregular (2 * Bvertical)
    have hbound := hvertical z hz_height hz_re_mem
    have hnorm_bound :
        ‖logDeriv riemannZeta z‖ ≤ B * Real.log |t| := by
      calc
        ‖logDeriv riemannZeta z‖
            ≤ Bvertical * Real.log |z.im| := hbound
        _ ≤ Bvertical * (2 * Real.log |t|) :=
            mul_le_mul_of_nonneg_left hlog hBvertical
        _ = (2 * Bvertical) * Real.log |t| := by ring
        _ ≤ B * Real.log |t| :=
            mul_le_mul_of_nonneg_right htwoB_le hlog_nonneg
    calc
      (-deriv riemannZeta
          ((1 + a / Real.log |t| : ℝ) + 2 * I * t) /
        riemannZeta ((1 + a / Real.log |t| : ℝ) + 2 * I * t)).re
          ≤ ‖-deriv riemannZeta z / riemannZeta z‖ := by
            have hle :
                (-deriv riemannZeta z / riemannZeta z).re ≤
                  ‖-deriv riemannZeta z / riemannZeta z‖ :=
              le_trans (le_abs_self _) (abs_re_le_norm _)
            simpa [z] using hle
      _ = ‖logDeriv riemannZeta z‖ :=
          norm_neg_deriv_div_riemannZeta_eq_norm_logDeriv z
      _ ≤ B * Real.log |t| := hnorm_bound

/-- High-height closure with a multiplicity-weighted regular part.

This is the multiplicity-aware version of
`classical_zero_free_region_of_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height`.
The local analytic input may isolate `n/(s - rho)` for any positive
multiplicity `n`; the proof only needs the weaker unit-principal real-part
inequality, which follows from `n >= 1`. -/
lemma classical_zero_free_region_of_multiplicity_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height
    (T0 Bregular Bvertical : ℝ)
    (hT0 : 2 ≤ T0) (hBregular : 0 ≤ Bregular)
    (hBvertical : 0 ≤ Bvertical)
    (hregular :
      ∀ s ρ : ℂ, T0 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
        riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
        0 < s.re - ρ.re →
        ∃ n : ℕ, 0 < n ∧
          ‖logDeriv riemannZeta s - (n : ℂ) * (s - ρ)⁻¹‖ ≤
            Bregular * Real.log |s.im|)
    (hvertical :
      ∀ z : ℂ, T0 ≤ |z.im| → z.re ∈ Set.Icc 1 2 →
        ‖logDeriv riemannZeta z‖ ≤ Bvertical * Real.log |z.im|) :
    classical_zero_free_region := by
  let B : ℝ := max Bregular (2 * Bvertical)
  have hB : 0 ≤ B := le_trans hBregular (le_max_left Bregular (2 * Bvertical))
  refine classical_zero_free_region_of_sigma_log_shift_estimates_same_const
    B T0 hB hT0 ?_ ?_
  · intro a c β t ha_pos _hc_pos ha_le_log2 ht hβ_lt _hβ hsub hζ
    let s : ℂ := ((1 + a / Real.log |t| : ℝ) : ℂ) + I * t
    let ρ : ℂ := (β : ℂ) + I * t
    have hs_re : s.re = 1 + a / Real.log |t| := by simp [s]
    have hs_im : s.im = t := by simp [s]
    have hρ_re : ρ.re = β := by simp [ρ]
    have hρ_im : ρ.im = t := by simp [ρ]
    have hs_re_gt : 1 < s.re := by
      rw [hs_re]
      exact sigmaOf_log_gt_one hT0 ha_pos ht
    have hs_re_le : s.re ≤ 2 := by
      rw [hs_re]
      exact sigmaOf_log_le_two hT0 ha_le_log2 ht
    have hs_re_mem : s.re ∈ Set.Icc 1 2 := ⟨hs_re_gt.le, hs_re_le⟩
    have hs_height : T0 ≤ |s.im| := by
      simpa [hs_im] using ht
    have hρ_im_eq : ρ.im = s.im := by
      simp [hρ_im, hs_im]
    have hρ_re_lt : ρ.re < 1 := by
      simpa [hρ_re] using hβ_lt
    have hsub' : 0 < s.re - ρ.re := by
      simpa [hs_re, hρ_re] using hsub
    have hζρ : riemannZeta ρ = 0 := by
      simpa [ρ] using hζ
    rcases hregular s ρ hs_height hs_re_mem hζρ hρ_im_eq hρ_re_lt hsub' with
      ⟨n, hn_pos, hreg_pos⟩
    have hreg_signed :
        ‖-logDeriv riemannZeta s + (n : ℂ) * (s - ρ)⁻¹‖ ≤
          Bregular * Real.log |s.im| := by
      calc
        ‖-logDeriv riemannZeta s + (n : ℂ) * (s - ρ)⁻¹‖
            = ‖-(logDeriv riemannZeta s - (n : ℂ) * (s - ρ)⁻¹)‖ := by
              ring_nf
        _ = ‖logDeriv riemannZeta s - (n : ℂ) * (s - ρ)⁻¹‖ := norm_neg _
        _ ≤ Bregular * Real.log |s.im| := hreg_pos
    have hreg_re :
        (-deriv riemannZeta s / riemannZeta s).re +
            1 / (s.re - ρ.re) ≤
          Bregular * Real.log |s.im| :=
      re_neg_logDeriv_riemannZeta_add_inv_le_of_multiplicity_regular_part_norm
        hreg_signed hn_pos hρ_im_eq hsub'
    have hlog_nonneg : 0 ≤ Real.log |t| :=
      (log_abs_pos_of_two_le (hT0.trans ht)).le
    have hBregular_le_B : Bregular ≤ B := le_max_left Bregular (2 * Bvertical)
    have hrewrite :
        (-deriv riemannZeta
              ((1 + a / Real.log |t| : ℝ) + I * t) /
            riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t)).re
          + 1 / ((1 + a / Real.log |t|) - β) ≤
            B * Real.log |t| := by
      calc
        (-deriv riemannZeta
              ((1 + a / Real.log |t| : ℝ) + I * t) /
            riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t)).re
          + 1 / ((1 + a / Real.log |t|) - β)
            ≤ Bregular * Real.log |t| := by
              simpa [s, ρ, hs_re, hs_im, hρ_re] using hreg_re
        _ ≤ B * Real.log |t| :=
              mul_le_mul_of_nonneg_right hBregular_le_B hlog_nonneg
    calc
      (-deriv riemannZeta
            ((1 + a / Real.log |t| : ℝ) + I * t) /
          riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t)).re
          =
            ((-deriv riemannZeta
                ((1 + a / Real.log |t| : ℝ) + I * t) /
              riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t)).re
              + 1 / ((1 + a / Real.log |t|) - β))
              - 1 / ((1 + a / Real.log |t|) - β) := by
              ring
      _ ≤ B * Real.log |t| - 1 / ((1 + a / Real.log |t|) - β) := by
              exact sub_le_sub_right hrewrite _
      _ = -1 / ((1 + a / Real.log |t|) - β) + B * Real.log |t| := by
              ring
  · intro a t ha_pos ha_le_log2 ht
    let z : ℂ := ((1 + a / Real.log |t| : ℝ) : ℂ) + 2 * I * t
    have hz_re_mem : z.re ∈ Set.Icc 1 2 := by
      have hz_re : z.re = 1 + a / Real.log |t| := by simp [z]
      exact ⟨by
        rw [hz_re]
        exact (sigmaOf_log_gt_one hT0 ha_pos ht).le,
        by
          rw [hz_re]
          exact sigmaOf_log_le_two hT0 ha_le_log2 ht⟩
    have hz_height : T0 ≤ |z.im| := by
      have hz_im_abs : |z.im| = |(2 : ℝ) * t| := by
        simp [z, abs_mul]
      have htwo_abs : |(2 : ℝ) * t| = 2 * |t| := by
        rw [abs_mul]
        norm_num
      rw [hz_im_abs, htwo_abs]
      have ht_nonneg : 0 ≤ |t| := abs_nonneg t
      nlinarith
    have hlog :
        Real.log |z.im| ≤ 2 * Real.log |t| := by
      have hz_im_abs : |z.im| = |(2 : ℝ) * t| := by
        simp [z, abs_mul]
      rw [hz_im_abs]
      exact log_abs_two_mul_le_two_log_abs (hT0.trans ht)
    have hlog_nonneg : 0 ≤ Real.log |t| :=
      (log_abs_pos_of_two_le (hT0.trans ht)).le
    have htwoB_le : 2 * Bvertical ≤ B := le_max_right Bregular (2 * Bvertical)
    have hbound := hvertical z hz_height hz_re_mem
    have hnorm_bound :
        ‖logDeriv riemannZeta z‖ ≤ B * Real.log |t| := by
      calc
        ‖logDeriv riemannZeta z‖
            ≤ Bvertical * Real.log |z.im| := hbound
        _ ≤ Bvertical * (2 * Real.log |t|) :=
            mul_le_mul_of_nonneg_left hlog hBvertical
        _ = (2 * Bvertical) * Real.log |t| := by ring
        _ ≤ B * Real.log |t| :=
            mul_le_mul_of_nonneg_right htwoB_le hlog_nonneg
    calc
      (-deriv riemannZeta
          ((1 + a / Real.log |t| : ℝ) + 2 * I * t) /
        riemannZeta ((1 + a / Real.log |t| : ℝ) + 2 * I * t)).re
          ≤ ‖-deriv riemannZeta z / riemannZeta z‖ := by
            have hle :
                (-deriv riemannZeta z / riemannZeta z).re ≤
                  ‖-deriv riemannZeta z / riemannZeta z‖ :=
              le_trans (le_abs_self _) (abs_re_le_norm _)
            simpa [z] using hle
      _ = ‖logDeriv riemannZeta z‖ :=
          norm_neg_deriv_div_riemannZeta_eq_norm_logDeriv z
      _ ≤ B * Real.log |t| := hnorm_bound

/-- Existential high-height version of the multiplicity-aware positive
`logDeriv ζ` regular-part/vertical-strip closure. -/
lemma classical_zero_free_region_of_exists_multiplicity_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height
    (T0 : ℝ) (hT0 : 2 ≤ T0)
    (h :
      ∃ Bregular Bvertical : ℝ, 0 ≤ Bregular ∧ 0 ≤ Bvertical ∧
        (∀ s ρ : ℂ, T0 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
          riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
          0 < s.re - ρ.re →
          ∃ n : ℕ, 0 < n ∧
            ‖logDeriv riemannZeta s - (n : ℂ) * (s - ρ)⁻¹‖ ≤
              Bregular * Real.log |s.im|) ∧
        (∀ z : ℂ, T0 ≤ |z.im| → z.re ∈ Set.Icc 1 2 →
          ‖logDeriv riemannZeta z‖ ≤ Bvertical * Real.log |z.im|)) :
    classical_zero_free_region := by
  rcases h with ⟨Bregular, Bvertical, hBregular, hBvertical, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_multiplicity_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height
      T0 Bregular Bvertical hT0 hBregular hBvertical hregular hvertical

/-- Coordinate high-height version of the multiplicity-aware positive
`logDeriv ζ` regular-part/vertical-strip closure.

This is the same input as
`classical_zero_free_region_of_multiplicity_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height`,
but stated in the real variables `sigma`, `beta`, and `t`. -/
lemma classical_zero_free_region_of_re_im_multiplicity_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height
    (T0 Bregular Bvertical : ℝ)
    (hT0 : 2 ≤ T0) (hBregular : 0 ≤ Bregular)
    (hBvertical : 0 ≤ Bvertical)
    (hregular :
      ∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
        0 < σ - β →
        ∃ n : ℕ, 0 < n ∧
          ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
              (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
            Bregular * Real.log |t|)
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          Bvertical * Real.log |t|) :
    classical_zero_free_region := by
  refine
    classical_zero_free_region_of_multiplicity_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height
      T0 Bregular Bvertical hT0 hBregular hBvertical ?_ ?_
  · intro s ρ hs_height hs_re_mem hζρ hρ_im_eq hρ_re_lt hsub
    have hs_decomp : ((s.re : ℂ) + I * s.im) = s := by
      apply Complex.ext <;> simp
    have hρ_decomp : ((ρ.re : ℂ) + I * s.im) = ρ := by
      apply Complex.ext
      · simp
      · simp [hρ_im_eq]
    have hinv :
        ((s.re : ℂ) - (ρ.re : ℂ))⁻¹ = (s - ρ)⁻¹ := by
      have hsub_eq : s - ρ = ((s.re : ℂ) - (ρ.re : ℂ)) := by
        apply Complex.ext
        · simp
        · simp [hρ_im_eq]
      rw [← hsub_eq]
    have hζ_coord :
        riemannZeta ((ρ.re : ℂ) + I * s.im) = 0 := by
      simpa [hρ_decomp] using hζρ
    rcases hregular s.re ρ.re s.im hs_height hs_re_mem hζ_coord hρ_re_lt hsub with
      ⟨n, hn_pos, hbound⟩
    refine ⟨n, hn_pos, ?_⟩
    have harg :
        logDeriv riemannZeta ((s.re : ℂ) + I * s.im) =
          logDeriv riemannZeta s := by
      rw [hs_decomp]
    simpa [harg, hinv] using hbound
  · intro z hz_height hz_re_mem
    have hz_decomp : ((z.re : ℂ) + I * z.im) = z := by
      apply Complex.ext <;> simp
    have h := hvertical z.re z.im hz_height hz_re_mem
    simpa [hz_decomp] using h

/-- Existential coordinate high-height version of the multiplicity-aware
positive `logDeriv ζ` regular-part/vertical-strip closure. -/
lemma classical_zero_free_region_of_exists_re_im_multiplicity_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height
    (h :
      ∃ T0 Bregular Bvertical : ℝ, 2 ≤ T0 ∧
        0 ≤ Bregular ∧ 0 ≤ Bvertical ∧
        (∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
          0 < σ - β →
          ∃ n : ℕ, 0 < n ∧
            ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
                (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
              Bregular * Real.log |t|) ∧
        (∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
            Bvertical * Real.log |t|)) :
    classical_zero_free_region := by
  rcases h with
    ⟨T0, Bregular, Bvertical, hT0, hBregular, hBvertical, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_re_im_multiplicity_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height
      T0 Bregular Bvertical hT0 hBregular hBvertical hregular hvertical

/-- Coordinate multiplicity-aware high-height closure from a single
`C * (1 + log |t|)` bound. -/
lemma classical_zero_free_region_of_re_im_multiplicity_logDeriv_regular_part_norm_one_add_log_bound_high_height
    (T0 C : ℝ) (hT0 : 3 ≤ T0) (hC : 0 ≤ C)
    (hregular :
      ∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
        0 < σ - β →
        ∃ n : ℕ, 0 < n ∧
          ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
              (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
            C * (1 + Real.log |t|))
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          C * (1 + Real.log |t|)) :
    classical_zero_free_region := by
  have hT0_two : 2 ≤ T0 := by linarith
  refine
    classical_zero_free_region_of_re_im_multiplicity_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height
      T0 (2 * C) (2 * C) hT0_two (by nlinarith) (by nlinarith) ?_ ?_
  · intro σ β t ht hσ hζ hβ hsub
    have hlog_ge_one : 1 ≤ Real.log |t| :=
      (log_abs_gt_one_of_three_le (hT0.trans ht)).le
    have hC_le : C ≤ C * Real.log |t| := by
      calc
        C = C * 1 := by ring
        _ ≤ C * Real.log |t| := mul_le_mul_of_nonneg_left hlog_ge_one hC
    rcases hregular σ β t ht hσ hζ hβ hsub with ⟨n, hn_pos, hbound⟩
    refine ⟨n, hn_pos, ?_⟩
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
          (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖
          ≤ C * (1 + Real.log |t|) := hbound
      _ = C + C * Real.log |t| := by ring
      _ ≤ (2 * C) * Real.log |t| := by nlinarith
  · intro σ t ht hσ
    have hlog_ge_one : 1 ≤ Real.log |t| :=
      (log_abs_gt_one_of_three_le (hT0.trans ht)).le
    have hC_le : C ≤ C * Real.log |t| := by
      calc
        C = C * 1 := by ring
        _ ≤ C * Real.log |t| := mul_le_mul_of_nonneg_left hlog_ge_one hC
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖
          ≤ C * (1 + Real.log |t|) := hvertical σ t ht hσ
      _ = C + C * Real.log |t| := by ring
      _ ≤ (2 * C) * Real.log |t| := by nlinarith

/-- Coordinate multiplicity-aware high-height closure from separate
`Cregular * (1 + log |t|)` and `Cvertical * (1 + log |t|)` bounds. -/
lemma classical_zero_free_region_of_re_im_multiplicity_logDeriv_regular_part_norm_one_add_log_bounds_high_height
    (T0 Cregular Cvertical : ℝ) (hT0 : 3 ≤ T0)
    (hCregular : 0 ≤ Cregular) (hCvertical : 0 ≤ Cvertical)
    (hregular :
      ∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
        0 < σ - β →
        ∃ n : ℕ, 0 < n ∧
          ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
              (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
            Cregular * (1 + Real.log |t|))
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          Cvertical * (1 + Real.log |t|)) :
    classical_zero_free_region := by
  have hT0_two : 2 ≤ T0 := by linarith
  refine
    classical_zero_free_region_of_re_im_multiplicity_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height
      T0 (2 * Cregular) (2 * Cvertical) hT0_two (by nlinarith) (by nlinarith) ?_ ?_
  · intro σ β t ht hσ hζ hβ hsub
    have hlog_ge_one : 1 ≤ Real.log |t| :=
      (log_abs_gt_one_of_three_le (hT0.trans ht)).le
    have hC_le : Cregular ≤ Cregular * Real.log |t| := by
      calc
        Cregular = Cregular * 1 := by ring
        _ ≤ Cregular * Real.log |t| :=
            mul_le_mul_of_nonneg_left hlog_ge_one hCregular
    rcases hregular σ β t ht hσ hζ hβ hsub with ⟨n, hn_pos, hbound⟩
    refine ⟨n, hn_pos, ?_⟩
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
          (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖
          ≤ Cregular * (1 + Real.log |t|) := hbound
      _ = Cregular + Cregular * Real.log |t| := by ring
      _ ≤ (2 * Cregular) * Real.log |t| := by nlinarith
  · intro σ t ht hσ
    have hlog_ge_one : 1 ≤ Real.log |t| :=
      (log_abs_gt_one_of_three_le (hT0.trans ht)).le
    have hC_le : Cvertical ≤ Cvertical * Real.log |t| := by
      calc
        Cvertical = Cvertical * 1 := by ring
        _ ≤ Cvertical * Real.log |t| :=
            mul_le_mul_of_nonneg_left hlog_ge_one hCvertical
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖
          ≤ Cvertical * (1 + Real.log |t|) := hvertical σ t ht hσ
      _ = Cvertical + Cvertical * Real.log |t| := by ring
      _ ≤ (2 * Cvertical) * Real.log |t| := by nlinarith

/-- Existential coordinate multiplicity-aware high-height closure from a
single `C * (1 + log |t|)` bound. -/
lemma classical_zero_free_region_of_exists_re_im_multiplicity_logDeriv_regular_part_norm_one_add_log_bound_high_height
    (h :
      ∃ T0 C : ℝ, 3 ≤ T0 ∧ 0 ≤ C ∧
        (∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
          0 < σ - β →
          ∃ n : ℕ, 0 < n ∧
            ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
                (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
              C * (1 + Real.log |t|)) ∧
        (∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
            C * (1 + Real.log |t|))) :
    classical_zero_free_region := by
  rcases h with ⟨T0, C, hT0, hC, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_re_im_multiplicity_logDeriv_regular_part_norm_one_add_log_bound_high_height
      T0 C hT0 hC hregular hvertical

/-- Existential coordinate multiplicity-aware high-height closure from
separate `Cregular * (1 + log |t|)` and `Cvertical * (1 + log |t|)` bounds. -/
lemma classical_zero_free_region_of_exists_re_im_multiplicity_logDeriv_regular_part_norm_one_add_log_bounds_high_height
    (h :
      ∃ T0 Cregular Cvertical : ℝ, 3 ≤ T0 ∧
        0 ≤ Cregular ∧ 0 ≤ Cvertical ∧
        (∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
          0 < σ - β →
          ∃ n : ℕ, 0 < n ∧
            ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
                (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
              Cregular * (1 + Real.log |t|)) ∧
        (∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
            Cvertical * (1 + Real.log |t|))) :
    classical_zero_free_region := by
  rcases h with
    ⟨T0, Cregular, Cvertical, hT0, hCregular, hCvertical, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_re_im_multiplicity_logDeriv_regular_part_norm_one_add_log_bounds_high_height
      T0 Cregular Cvertical hT0 hCregular hCvertical hregular hvertical

/-- Signed coordinate multiplicity-aware high-height closure from a single
`C * (1 + log |t|)` bound. -/
lemma classical_zero_free_region_of_re_im_multiplicity_neg_logDeriv_regular_part_norm_one_add_log_bound_high_height
    (T0 C : ℝ) (hT0 : 3 ≤ T0) (hC : 0 ≤ C)
    (hregular :
      ∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
        0 < σ - β →
        ∃ n : ℕ, 0 < n ∧
          ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
              (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
            C * (1 + Real.log |t|))
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          C * (1 + Real.log |t|)) :
    classical_zero_free_region := by
  refine
    classical_zero_free_region_of_re_im_multiplicity_logDeriv_regular_part_norm_one_add_log_bound_high_height
      T0 C hT0 hC ?_ ?_
  · intro σ β t ht hσ hζ hβ hsub
    rcases hregular σ β t ht hσ hζ hβ hsub with ⟨n, hn_pos, hbound⟩
    refine ⟨n, hn_pos, ?_⟩
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
          (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖
          = ‖-(-logDeriv riemannZeta ((σ : ℂ) + I * t) +
              (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹))‖ := by ring_nf
      _ = ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
            (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖ := norm_neg _
      _ ≤ C * (1 + Real.log |t|) := hbound
  · intro σ t ht hσ
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖
          = ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := (norm_neg _).symm
      _ ≤ C * (1 + Real.log |t|) := hvertical σ t ht hσ

/-- Signed coordinate multiplicity-aware high-height closure from separate
`Cregular * (1 + log |t|)` and `Cvertical * (1 + log |t|)` bounds. -/
lemma classical_zero_free_region_of_re_im_multiplicity_neg_logDeriv_regular_part_norm_one_add_log_bounds_high_height
    (T0 Cregular Cvertical : ℝ) (hT0 : 3 ≤ T0)
    (hCregular : 0 ≤ Cregular) (hCvertical : 0 ≤ Cvertical)
    (hregular :
      ∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
        0 < σ - β →
        ∃ n : ℕ, 0 < n ∧
          ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
              (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
            Cregular * (1 + Real.log |t|))
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          Cvertical * (1 + Real.log |t|)) :
    classical_zero_free_region := by
  refine
    classical_zero_free_region_of_re_im_multiplicity_logDeriv_regular_part_norm_one_add_log_bounds_high_height
      T0 Cregular Cvertical hT0 hCregular hCvertical ?_ ?_
  · intro σ β t ht hσ hζ hβ hsub
    rcases hregular σ β t ht hσ hζ hβ hsub with ⟨n, hn_pos, hbound⟩
    refine ⟨n, hn_pos, ?_⟩
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
          (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖
          = ‖-(-logDeriv riemannZeta ((σ : ℂ) + I * t) +
              (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹))‖ := by ring_nf
      _ = ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
            (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖ := norm_neg _
      _ ≤ Cregular * (1 + Real.log |t|) := hbound
  · intro σ t ht hσ
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖
          = ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := (norm_neg _).symm
      _ ≤ Cvertical * (1 + Real.log |t|) := hvertical σ t ht hσ

/-- Existential signed coordinate multiplicity-aware high-height closure from
a single `C * (1 + log |t|)` bound. -/
lemma classical_zero_free_region_of_exists_re_im_multiplicity_neg_logDeriv_regular_part_norm_one_add_log_bound_high_height
    (h :
      ∃ T0 C : ℝ, 3 ≤ T0 ∧ 0 ≤ C ∧
        (∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
          0 < σ - β →
          ∃ n : ℕ, 0 < n ∧
            ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
                (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
              C * (1 + Real.log |t|)) ∧
        (∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
            C * (1 + Real.log |t|))) :
    classical_zero_free_region := by
  rcases h with ⟨T0, C, hT0, hC, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_re_im_multiplicity_neg_logDeriv_regular_part_norm_one_add_log_bound_high_height
      T0 C hT0 hC hregular hvertical

/-- Existential signed coordinate multiplicity-aware high-height closure from
separate `Cregular * (1 + log |t|)` and `Cvertical * (1 + log |t|)` bounds. -/
lemma classical_zero_free_region_of_exists_re_im_multiplicity_neg_logDeriv_regular_part_norm_one_add_log_bounds_high_height
    (h :
      ∃ T0 Cregular Cvertical : ℝ, 3 ≤ T0 ∧
        0 ≤ Cregular ∧ 0 ≤ Cvertical ∧
        (∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
          0 < σ - β →
          ∃ n : ℕ, 0 < n ∧
            ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
                (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
              Cregular * (1 + Real.log |t|)) ∧
        (∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
            Cvertical * (1 + Real.log |t|))) :
    classical_zero_free_region := by
  rcases h with
    ⟨T0, Cregular, Cvertical, hT0, hCregular, hCvertical, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_re_im_multiplicity_neg_logDeriv_regular_part_norm_one_add_log_bounds_high_height
      T0 Cregular Cvertical hT0 hCregular hCvertical hregular hvertical

/-- Existential high-height version of the positive `logDeriv ζ`
regular-part/vertical-strip closure. -/
lemma classical_zero_free_region_of_exists_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height
    (T0 : ℝ) (hT0 : 2 ≤ T0)
    (h :
      ∃ Bregular Bvertical : ℝ, 0 ≤ Bregular ∧ 0 ≤ Bvertical ∧
        (∀ s ρ : ℂ, T0 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
          riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
          0 < s.re - ρ.re →
          ‖logDeriv riemannZeta s - (s - ρ)⁻¹‖ ≤
            Bregular * Real.log |s.im|) ∧
        (∀ z : ℂ, T0 ≤ |z.im| → z.re ∈ Set.Icc 1 2 →
          ‖logDeriv riemannZeta z‖ ≤ Bvertical * Real.log |z.im|)) :
    classical_zero_free_region := by
  rcases h with ⟨Bregular, Bvertical, hBregular, hBvertical, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height
      T0 Bregular Bvertical hT0 hBregular hBvertical hregular hvertical

/-- High-height closure from affine logarithmic bounds.

The analytic estimates produced by Borel-Carathéodory/Jensen arguments often
have the shape `A + B * log |Im|`.  Above height `3`, `1 <= log |Im|`, so the
additive constant is absorbed into the logarithmic coefficient.  This wrapper
then feeds the normalized estimates into
`classical_zero_free_region_of_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height`. -/
lemma classical_zero_free_region_of_logDeriv_regular_part_norm_affine_log_bound_and_vertical_logDeriv_norm_affine_log_bound_high_height
    (T0 Aregular Bregular Avertical Bvertical : ℝ)
    (hT0 : 3 ≤ T0)
    (hAregular : 0 ≤ Aregular) (hBregular : 0 ≤ Bregular)
    (hAvertical : 0 ≤ Avertical) (hBvertical : 0 ≤ Bvertical)
    (hregular :
      ∀ s ρ : ℂ, T0 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
        riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
        0 < s.re - ρ.re →
        ‖logDeriv riemannZeta s - (s - ρ)⁻¹‖ ≤
          Aregular + Bregular * Real.log |s.im|)
    (hvertical :
      ∀ z : ℂ, T0 ≤ |z.im| → z.re ∈ Set.Icc 1 2 →
        ‖logDeriv riemannZeta z‖ ≤ Avertical + Bvertical * Real.log |z.im|) :
    classical_zero_free_region := by
  have hT0_two : 2 ≤ T0 := by linarith
  refine
    classical_zero_free_region_of_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height
      T0 (Aregular + Bregular) (Avertical + Bvertical) hT0_two
      (by linarith) (by linarith) ?_ ?_
  · intro s ρ hs_height hs_re_mem hζρ hρ_im hρ_re hsub
    have hlog_ge_one : 1 ≤ Real.log |s.im| :=
      (log_abs_gt_one_of_three_le (hT0.trans hs_height)).le
    have hA_le : Aregular ≤ Aregular * Real.log |s.im| := by
      calc
        Aregular = Aregular * 1 := by ring
        _ ≤ Aregular * Real.log |s.im| :=
            mul_le_mul_of_nonneg_left hlog_ge_one hAregular
    calc
      ‖logDeriv riemannZeta s - (s - ρ)⁻¹‖
          ≤ Aregular + Bregular * Real.log |s.im| :=
            hregular s ρ hs_height hs_re_mem hζρ hρ_im hρ_re hsub
      _ ≤ Aregular * Real.log |s.im| +
            Bregular * Real.log |s.im| := by
            linarith
      _ = (Aregular + Bregular) * Real.log |s.im| := by ring
  · intro z hz_height hz_re_mem
    have hlog_ge_one : 1 ≤ Real.log |z.im| :=
      (log_abs_gt_one_of_three_le (hT0.trans hz_height)).le
    have hA_le : Avertical ≤ Avertical * Real.log |z.im| := by
      calc
        Avertical = Avertical * 1 := by ring
        _ ≤ Avertical * Real.log |z.im| :=
            mul_le_mul_of_nonneg_left hlog_ge_one hAvertical
    calc
      ‖logDeriv riemannZeta z‖
          ≤ Avertical + Bvertical * Real.log |z.im| :=
            hvertical z hz_height hz_re_mem
      _ ≤ Avertical * Real.log |z.im| +
            Bvertical * Real.log |z.im| := by
            linarith
      _ = (Avertical + Bvertical) * Real.log |z.im| := by ring

/-- Coordinate version of the high-height affine-log closure.

This is the same analytic input as
`classical_zero_free_region_of_logDeriv_regular_part_norm_affine_log_bound_and_vertical_logDeriv_norm_affine_log_bound_high_height`,
but stated in the real variables `sigma`, `beta`, and `t`.  It is often the
most convenient shape for estimates proved by hand from Borel-Carathéodory or
Jensen arguments. -/
lemma classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_affine_bounds_high_height
    (T0 Aregular Bregular Avertical Bvertical : ℝ)
    (hT0 : 3 ≤ T0)
    (hAregular : 0 ≤ Aregular) (hBregular : 0 ≤ Bregular)
    (hAvertical : 0 ≤ Avertical) (hBvertical : 0 ≤ Bvertical)
    (hregular :
      ∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
        0 < σ - β →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
            (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
          Aregular + Bregular * Real.log |t|)
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          Avertical + Bvertical * Real.log |t|) :
    classical_zero_free_region := by
  refine
    classical_zero_free_region_of_logDeriv_regular_part_norm_affine_log_bound_and_vertical_logDeriv_norm_affine_log_bound_high_height
      T0 Aregular Bregular Avertical Bvertical hT0 hAregular hBregular
      hAvertical hBvertical ?_ ?_
  · intro s ρ hs_height hs_re_mem hζρ hρ_im_eq hρ_re_lt hsub
    have hs_decomp : ((s.re : ℂ) + I * s.im) = s := by
      apply Complex.ext <;> simp
    have hρ_decomp : ((ρ.re : ℂ) + I * s.im) = ρ := by
      apply Complex.ext
      · simp
      · simp [hρ_im_eq]
    have hinv :
        (((s.re - ρ.re : ℝ) : ℂ)⁻¹) = (s - ρ)⁻¹ := by
      have hsub_eq : s - ρ = ((s.re - ρ.re : ℝ) : ℂ) := by
        apply Complex.ext
        · simp
        · simp [hρ_im_eq]
      rw [hsub_eq]
    have hζ_coord :
        riemannZeta ((ρ.re : ℂ) + I * s.im) = 0 := by
      simpa [hρ_decomp] using hζρ
    have h :=
      hregular s.re ρ.re s.im hs_height hs_re_mem hζ_coord hρ_re_lt hsub
    have harg :
        logDeriv riemannZeta ((s.re : ℂ) + I * s.im) =
          logDeriv riemannZeta s := by
      rw [hs_decomp]
    rwa [harg, hinv] at h
  · intro z hz_height hz_re_mem
    have hz_decomp : ((z.re : ℂ) + I * z.im) = z := by
      apply Complex.ext <;> simp
    have h := hvertical z.re z.im hz_height hz_re_mem
    simpa [hz_decomp] using h

/-- Existential coordinate version of the high-height affine-log closure. -/
lemma classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_affine_bounds_high_height
    (h :
      ∃ T0 Aregular Bregular Avertical Bvertical : ℝ,
        3 ≤ T0 ∧
        0 ≤ Aregular ∧ 0 ≤ Bregular ∧
        0 ≤ Avertical ∧ 0 ≤ Bvertical ∧
        (∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
          0 < σ - β →
          ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
              (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
            Aregular + Bregular * Real.log |t|) ∧
        (∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
            Avertical + Bvertical * Real.log |t|)) :
    classical_zero_free_region := by
  rcases h with
    ⟨T0, Aregular, Bregular, Avertical, Bvertical, hT0,
      hAregular, hBregular, hAvertical, hBvertical, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_affine_bounds_high_height
      T0 Aregular Bregular Avertical Bvertical hT0 hAregular hBregular
      hAvertical hBvertical hregular hvertical

/-- Signed coordinate version of the high-height affine-log closure.

This is the `-logDeriv ζ` counterpart of
`classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_affine_bounds_high_height`,
with estimates stated in the real variables `σ`, `β`, and `t`. -/
lemma classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_affine_bounds_high_height
    (T0 Aregular Bregular Avertical Bvertical : ℝ)
    (hT0 : 3 ≤ T0)
    (hAregular : 0 ≤ Aregular) (hBregular : 0 ≤ Bregular)
    (hAvertical : 0 ≤ Avertical) (hBvertical : 0 ≤ Bvertical)
    (hregular :
      ∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
        0 < σ - β →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
            (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
          Aregular + Bregular * Real.log |t|)
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          Avertical + Bvertical * Real.log |t|) :
    classical_zero_free_region := by
  refine
    classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_affine_bounds_high_height
      T0 Aregular Bregular Avertical Bvertical hT0 hAregular hBregular
      hAvertical hBvertical ?_ ?_
  · intro σ β t ht hσ hζ hβ hsub
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
          (((σ - β : ℝ) : ℂ)⁻¹)‖
          = ‖-(-logDeriv riemannZeta ((σ : ℂ) + I * t) +
              (((σ - β : ℝ) : ℂ)⁻¹))‖ := by ring_nf
      _ = ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
            (((σ - β : ℝ) : ℂ)⁻¹)‖ := norm_neg _
      _ ≤ Aregular + Bregular * Real.log |t| :=
          hregular σ β t ht hσ hζ hβ hsub
  · intro σ t ht hσ
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖
          = ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := (norm_neg _).symm
      _ ≤ Avertical + Bvertical * Real.log |t| := hvertical σ t ht hσ

/-- Existential signed coordinate version of the high-height affine-log
closure. -/
lemma classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_affine_bounds_high_height
    (h :
      ∃ T0 Aregular Bregular Avertical Bvertical : ℝ,
        3 ≤ T0 ∧
        0 ≤ Aregular ∧ 0 ≤ Bregular ∧
        0 ≤ Avertical ∧ 0 ≤ Bvertical ∧
        (∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
          0 < σ - β →
          ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
              (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
            Aregular + Bregular * Real.log |t|) ∧
        (∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
            Avertical + Bvertical * Real.log |t|)) :
    classical_zero_free_region := by
  rcases h with
    ⟨T0, Aregular, Bregular, Avertical, Bvertical, hT0,
      hAregular, hBregular, hAvertical, hBvertical, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_affine_bounds_high_height
      T0 Aregular Bregular Avertical Bvertical hT0 hAregular hBregular
      hAvertical hBvertical hregular hvertical

/-- Coordinate high-height closure from a single `C * (1 + log |t|)` bound.

This is a convenience layer for the common big-O style output of analytic
estimates: the same nonnegative constant controls the regular-part estimate and
the vertical-strip logarithmic-derivative estimate. -/
lemma classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_one_add_log_bound_high_height
    (T0 C : ℝ) (hT0 : 3 ≤ T0) (hC : 0 ≤ C)
    (hregular :
      ∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
        0 < σ - β →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
            (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
          C * (1 + Real.log |t|))
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          C * (1 + Real.log |t|)) :
    classical_zero_free_region := by
  refine
    classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_affine_bounds_high_height
      T0 C C C C hT0 hC hC hC hC ?_ ?_
  · intro σ β t ht hσ hζ hβ hsub
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
          (((σ - β : ℝ) : ℂ)⁻¹)‖
          ≤ C * (1 + Real.log |t|) :=
            hregular σ β t ht hσ hζ hβ hsub
      _ = C + C * Real.log |t| := by ring
  · intro σ t ht hσ
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖
          ≤ C * (1 + Real.log |t|) := hvertical σ t ht hσ
      _ = C + C * Real.log |t| := by ring

/-- Coordinate high-height closure from separate
`Cregular * (1 + log |t|)` and `Cvertical * (1 + log |t|)` bounds. -/
lemma classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_one_add_log_bounds_high_height
    (T0 Cregular Cvertical : ℝ) (hT0 : 3 ≤ T0)
    (hCregular : 0 ≤ Cregular) (hCvertical : 0 ≤ Cvertical)
    (hregular :
      ∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
        0 < σ - β →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
            (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
          Cregular * (1 + Real.log |t|))
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          Cvertical * (1 + Real.log |t|)) :
    classical_zero_free_region := by
  refine
    classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_affine_bounds_high_height
      T0 Cregular Cregular Cvertical Cvertical hT0 hCregular hCregular
      hCvertical hCvertical ?_ ?_
  · intro σ β t ht hσ hζ hβ hsub
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
          (((σ - β : ℝ) : ℂ)⁻¹)‖
          ≤ Cregular * (1 + Real.log |t|) :=
            hregular σ β t ht hσ hζ hβ hsub
      _ = Cregular + Cregular * Real.log |t| := by ring
  · intro σ t ht hσ
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖
          ≤ Cvertical * (1 + Real.log |t|) :=
            hvertical σ t ht hσ
      _ = Cvertical + Cvertical * Real.log |t| := by ring

/-- Existential coordinate high-height closure from a single
`C * (1 + log |t|)` bound. -/
lemma classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_one_add_log_bound_high_height
    (h :
      ∃ T0 C : ℝ, 3 ≤ T0 ∧ 0 ≤ C ∧
        (∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
          0 < σ - β →
          ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
              (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
            C * (1 + Real.log |t|)) ∧
        (∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
            C * (1 + Real.log |t|))) :
    classical_zero_free_region := by
  rcases h with ⟨T0, C, hT0, hC, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_one_add_log_bound_high_height
      T0 C hT0 hC hregular hvertical

/-- Existential coordinate high-height closure from separate
`Cregular * (1 + log |t|)` and `Cvertical * (1 + log |t|)` bounds. -/
lemma classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_one_add_log_bounds_high_height
    (h :
      ∃ T0 Cregular Cvertical : ℝ, 3 ≤ T0 ∧
        0 ≤ Cregular ∧ 0 ≤ Cvertical ∧
        (∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
          0 < σ - β →
          ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
              (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
            Cregular * (1 + Real.log |t|)) ∧
        (∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
            Cvertical * (1 + Real.log |t|))) :
    classical_zero_free_region := by
  rcases h with
    ⟨T0, Cregular, Cvertical, hT0, hCregular, hCvertical, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_one_add_log_bounds_high_height
      T0 Cregular Cvertical hT0 hCregular hCvertical hregular hvertical

/-- Signed coordinate high-height closure from a single
`C * (1 + log |t|)` bound.

This is the `-logDeriv ζ` counterpart of
`classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_one_add_log_bound_high_height`. -/
lemma classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_one_add_log_bound_high_height
    (T0 C : ℝ) (hT0 : 3 ≤ T0) (hC : 0 ≤ C)
    (hregular :
      ∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
        0 < σ - β →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
            (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
          C * (1 + Real.log |t|))
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          C * (1 + Real.log |t|)) :
    classical_zero_free_region := by
  refine
    classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_one_add_log_bound_high_height
      T0 C hT0 hC ?_ ?_
  · intro σ β t ht hσ hζ hβ hsub
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
          (((σ - β : ℝ) : ℂ)⁻¹)‖
          = ‖-(-logDeriv riemannZeta ((σ : ℂ) + I * t) +
              (((σ - β : ℝ) : ℂ)⁻¹))‖ := by ring_nf
      _ = ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
            (((σ - β : ℝ) : ℂ)⁻¹)‖ := norm_neg _
      _ ≤ C * (1 + Real.log |t|) :=
          hregular σ β t ht hσ hζ hβ hsub
  · intro σ t ht hσ
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖
          = ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := (norm_neg _).symm
      _ ≤ C * (1 + Real.log |t|) := hvertical σ t ht hσ

/-- Signed coordinate high-height closure from separate
`Cregular * (1 + log |t|)` and `Cvertical * (1 + log |t|)` bounds. -/
lemma classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_one_add_log_bounds_high_height
    (T0 Cregular Cvertical : ℝ) (hT0 : 3 ≤ T0)
    (hCregular : 0 ≤ Cregular) (hCvertical : 0 ≤ Cvertical)
    (hregular :
      ∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
        0 < σ - β →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
            (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
          Cregular * (1 + Real.log |t|))
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          Cvertical * (1 + Real.log |t|)) :
    classical_zero_free_region := by
  refine
    classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_one_add_log_bounds_high_height
      T0 Cregular Cvertical hT0 hCregular hCvertical ?_ ?_
  · intro σ β t ht hσ hζ hβ hsub
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
          (((σ - β : ℝ) : ℂ)⁻¹)‖
          = ‖-(-logDeriv riemannZeta ((σ : ℂ) + I * t) +
              (((σ - β : ℝ) : ℂ)⁻¹))‖ := by ring_nf
      _ = ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
            (((σ - β : ℝ) : ℂ)⁻¹)‖ := norm_neg _
      _ ≤ Cregular * (1 + Real.log |t|) :=
          hregular σ β t ht hσ hζ hβ hsub
  · intro σ t ht hσ
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖
          = ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := (norm_neg _).symm
      _ ≤ Cvertical * (1 + Real.log |t|) := hvertical σ t ht hσ

/-- Existential signed coordinate high-height closure from a single
`C * (1 + log |t|)` bound. -/
lemma classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_one_add_log_bound_high_height
    (h :
      ∃ T0 C : ℝ, 3 ≤ T0 ∧ 0 ≤ C ∧
        (∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
          0 < σ - β →
          ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
              (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
            C * (1 + Real.log |t|)) ∧
        (∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
            C * (1 + Real.log |t|))) :
    classical_zero_free_region := by
  rcases h with ⟨T0, C, hT0, hC, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_one_add_log_bound_high_height
      T0 C hT0 hC hregular hvertical

/-- Existential signed coordinate high-height closure from separate
`Cregular * (1 + log |t|)` and `Cvertical * (1 + log |t|)` bounds. -/
lemma classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_one_add_log_bounds_high_height
    (h :
      ∃ T0 Cregular Cvertical : ℝ, 3 ≤ T0 ∧
        0 ≤ Cregular ∧ 0 ≤ Cvertical ∧
        (∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
          0 < σ - β →
          ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
              (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
            Cregular * (1 + Real.log |t|)) ∧
        (∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
            Cvertical * (1 + Real.log |t|))) :
    classical_zero_free_region := by
  rcases h with
    ⟨T0, Cregular, Cvertical, hT0, hCregular, hCvertical, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_one_add_log_bounds_high_height
      T0 Cregular Cvertical hT0 hCregular hCvertical hregular hvertical

/-- Above height `3`, `log(|t| + 3)` is controlled by `2 log |t|`. -/
lemma log_abs_add_three_le_two_log_abs {t : ℝ} (ht : 3 ≤ |t|) :
    Real.log (|t| + 3) ≤ 2 * Real.log |t| := by
  have ht_pos : 0 < |t| := by linarith
  have hsum_pos : 0 < |t| + 3 := by linarith
  have hsum_le : |t| + 3 ≤ 2 * |t| := by linarith
  have hlog_le : Real.log (|t| + 3) ≤ Real.log (2 * |t|) :=
    Real.log_le_log hsum_pos hsum_le
  have hlog_mul : Real.log (2 * |t|) = Real.log 2 + Real.log |t| := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt ht_pos)]
  have hlog_two_le : Real.log 2 ≤ Real.log |t| :=
    Real.log_le_log (by norm_num) (by linarith : (2 : ℝ) ≤ |t|)
  calc
    Real.log (|t| + 3) ≤ Real.log (2 * |t|) := hlog_le
    _ = Real.log 2 + Real.log |t| := hlog_mul
    _ ≤ 2 * Real.log |t| := by linarith

/-- Standalone normalization of a future vertical-strip log-derivative
estimate already stated in the safe height scale `A + B * log(|t| + 3)`.

This is the objective-shaped handoff for the next hard analytic input: once a
high-height estimate on `1 <= sigma <= 2` is known in the common
`log(|t| + 3)` scale, this theorem converts it into the exact
`C * log |t|` form used by the quantitative zero-free-region chain.  It does
not prove the missing zeta-specific growth estimate. -/
lemma exists_re_im_logDeriv_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height
    (T0 A B : ℝ) (hT0 : 3 ≤ T0) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          A + B * Real.log (|t| + 3)) :
    ∃ C T0' : ℝ, 0 ≤ C ∧ 3 ≤ T0' ∧
      ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → T0' ≤ |t| →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          C * Real.log |t| := by
  refine ⟨A + 2 * B, T0, add_nonneg hA (mul_nonneg (by norm_num) hB),
    hT0, ?_⟩
  intro σ t hσ_left hσ_right ht
  have hσ_mem : σ ∈ Set.Icc 1 2 := ⟨hσ_left, hσ_right⟩
  have ht3 : 3 ≤ |t| := hT0.trans ht
  have hlog_ge_one : 1 ≤ Real.log |t| :=
    (log_abs_gt_one_of_three_le ht3).le
  have hA_le : A ≤ A * Real.log |t| := by
    calc
      A = A * 1 := by ring
      _ ≤ A * Real.log |t| :=
          mul_le_mul_of_nonneg_left hlog_ge_one hA
  have hlog_abs : Real.log (|t| + 3) ≤ 2 * Real.log |t| :=
    log_abs_add_three_le_two_log_abs ht3
  calc
    ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖
        ≤ A + B * Real.log (|t| + 3) :=
          hvertical σ t ht hσ_mem
    _ ≤ A * Real.log |t| + B * (2 * Real.log |t|) := by
          exact add_le_add hA_le (mul_le_mul_of_nonneg_left hlog_abs hB)
    _ = (A + 2 * B) * Real.log |t| := by ring

/-- Multiplicative version of
`exists_re_im_logDeriv_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height`. -/
lemma exists_re_im_logDeriv_vertical_log_bound_of_log_abs_add_three_bound_high_height
    (T0 C : ℝ) (hT0 : 3 ≤ T0) (hC : 0 ≤ C)
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          C * Real.log (|t| + 3)) :
    ∃ C' T0' : ℝ, 0 ≤ C' ∧ 3 ≤ T0' ∧
      ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → T0' ≤ |t| →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          C' * Real.log |t| := by
  refine
    exists_re_im_logDeriv_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height
      T0 0 C hT0 (by norm_num) hC ?_
  intro σ t ht hσ
  simpa using hvertical σ t ht hσ

/-- Signed standalone normalization of a future `-logDeriv ζ` estimate in the
safe height scale `A + B * log(|t| + 3)`. -/
lemma exists_re_im_neg_logDeriv_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height
    (T0 A B : ℝ) (hT0 : 3 ≤ T0) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          A + B * Real.log (|t| + 3)) :
    ∃ C T0' : ℝ, 0 ≤ C ∧ 3 ≤ T0' ∧
      ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → T0' ≤ |t| →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          C * Real.log |t| := by
  have hvertical_pos :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          A + B * Real.log (|t| + 3) := by
    intro σ t ht hσ
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖
          = ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := (norm_neg _).symm
      _ ≤ A + B * Real.log (|t| + 3) := hvertical σ t ht hσ
  rcases
      exists_re_im_logDeriv_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height
        T0 A B hT0 hA hB hvertical_pos with
    ⟨C, T0', hC, hT0', hbound⟩
  refine ⟨C, T0', hC, hT0', ?_⟩
  intro σ t hσ_left hσ_right ht
  calc
    ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖
        = ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := norm_neg _
    _ ≤ C * Real.log |t| := hbound σ t hσ_left hσ_right ht

/-- Multiplicative signed version of
`exists_re_im_neg_logDeriv_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height`. -/
lemma exists_re_im_neg_logDeriv_vertical_log_bound_of_log_abs_add_three_bound_high_height
    (T0 C : ℝ) (hT0 : 3 ≤ T0) (hC : 0 ≤ C)
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          C * Real.log (|t| + 3)) :
    ∃ C' T0' : ℝ, 0 ≤ C' ∧ 3 ≤ T0' ∧
      ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → T0' ≤ |t| →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          C' * Real.log |t| := by
  refine
    exists_re_im_neg_logDeriv_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height
      T0 0 C hT0 (by norm_num) hC ?_
  intro σ t ht hσ
  simpa using hvertical σ t ht hσ

/-- Real-part quotient version of
`exists_re_im_logDeriv_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height`. -/
lemma exists_re_neg_deriv_div_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height
    (T0 A B : ℝ) (hT0 : 3 ≤ T0) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          A + B * Real.log (|t| + 3)) :
    ∃ C T0' : ℝ, 0 ≤ C ∧ 3 ≤ T0' ∧
      ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → T0' ≤ |t| →
        (-deriv riemannZeta ((σ : ℂ) + I * t) /
            riemannZeta ((σ : ℂ) + I * t)).re ≤
          C * Real.log |t| := by
  rcases
      exists_re_im_logDeriv_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height
        T0 A B hT0 hA hB hvertical with
    ⟨C, T0', hC, hT0', hnorm⟩
  refine ⟨C, T0', hC, hT0', ?_⟩
  intro σ t hσ_left hσ_right ht
  let z : ℂ := (σ : ℂ) + I * t
  calc
    (-deriv riemannZeta z / riemannZeta z).re
        ≤ ‖-deriv riemannZeta z / riemannZeta z‖ := Complex.re_le_norm _
    _ = ‖logDeriv riemannZeta z‖ :=
        norm_neg_deriv_div_riemannZeta_eq_norm_logDeriv z
    _ ≤ C * Real.log |t| := by
        simpa [z] using hnorm σ t hσ_left hσ_right ht

/-- Signed-norm real-part quotient version of
`exists_re_neg_deriv_div_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height`. -/
lemma exists_re_neg_deriv_div_vertical_log_bound_of_neg_affine_log_abs_add_three_bound_high_height
    (T0 A B : ℝ) (hT0 : 3 ≤ T0) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          A + B * Real.log (|t| + 3)) :
    ∃ C T0' : ℝ, 0 ≤ C ∧ 3 ≤ T0' ∧
      ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → T0' ≤ |t| →
        (-deriv riemannZeta ((σ : ℂ) + I * t) /
            riemannZeta ((σ : ℂ) + I * t)).re ≤
          C * Real.log |t| := by
  rcases
      exists_re_im_neg_logDeriv_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height
        T0 A B hT0 hA hB hvertical with
    ⟨C, T0', hC, hT0', hnorm⟩
  refine ⟨C, T0', hC, hT0', ?_⟩
  intro σ t hσ_left hσ_right ht
  let z : ℂ := (σ : ℂ) + I * t
  calc
    (-deriv riemannZeta z / riemannZeta z).re
        ≤ ‖-deriv riemannZeta z / riemannZeta z‖ := Complex.re_le_norm _
    _ = ‖logDeriv riemannZeta z‖ :=
        norm_neg_deriv_div_riemannZeta_eq_norm_logDeriv z
    _ = ‖-logDeriv riemannZeta z‖ := (norm_neg _).symm
    _ ≤ C * Real.log |t| := by
        simpa [z] using hnorm σ t hσ_left hσ_right ht

/-- Coordinate bridge from a `C * log (|t| + 3)` local regular-part bound to a
pure logarithmic real-part bound at heights `|t| >= 3`. -/
lemma re_neg_logDeriv_riemannZeta_sigma_it_add_inv_le_of_regular_part_norm_log_abs_add_three
    {σ β t C : ℝ}
    (hC : 0 ≤ C) (ht : 3 ≤ |t|)
    (hregular :
      ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
          (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
        C * Real.log (|t| + 3))
    (hsub : 0 < σ - β) :
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re +
      1 / (σ - β) ≤ (2 * C) * Real.log |t| := by
  have hbase :=
    re_neg_logDeriv_riemannZeta_sigma_it_add_inv_le_of_regular_part_norm
      hregular hsub
  have hlog := log_abs_add_three_le_two_log_abs ht
  calc
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re +
      1 / (σ - β)
        ≤ C * Real.log (|t| + 3) := hbase
    _ ≤ C * (2 * Real.log |t|) :=
        mul_le_mul_of_nonneg_left hlog hC
    _ = (2 * C) * Real.log |t| := by ring

/-- Multiplicity-aware coordinate bridge from a `C * log (|t| + 3)` local
regular-part bound to a pure logarithmic real-part bound. -/
lemma re_neg_logDeriv_riemannZeta_sigma_it_add_inv_le_of_multiplicity_regular_part_norm_log_abs_add_three
    {σ β t C : ℝ} {n : ℕ}
    (hC : 0 ≤ C) (ht : 3 ≤ |t|)
    (hregular :
      ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
          (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
        C * Real.log (|t| + 3))
    (hn : 0 < n) (hsub : 0 < σ - β) :
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re +
      1 / (σ - β) ≤ (2 * C) * Real.log |t| := by
  have hbase :=
    re_neg_logDeriv_riemannZeta_sigma_it_add_inv_le_of_multiplicity_regular_part_norm
      hregular hn hsub
  have hlog := log_abs_add_three_le_two_log_abs ht
  calc
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re +
      1 / (σ - β)
        ≤ C * Real.log (|t| + 3) := hbase
    _ ≤ C * (2 * Real.log |t|) :=
        mul_le_mul_of_nonneg_left hlog hC
    _ = (2 * C) * Real.log |t| := by ring

/-- Fixed-margin high-height vertical logarithmic bound in the exact
`C * log |t|` scale.

This is the strongest statement currently available from the absolute
convergence half-plane alone: for each fixed `ε > 0`, the estimate holds on
`1 + ε <= σ`.  It deliberately does not reach the boundary strip
`1 <= σ <= 2`, which remains the hard analytic input for the classical
zero-free region. -/
lemma exists_norm_logDeriv_riemannZeta_sigma_it_le_log_abs_of_fixed_margin
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 3 ≤ T0 ∧
      ∀ σ t : ℝ, 1 + ε ≤ σ → σ ≤ 2 → T0 ≤ |t| →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          C * Real.log |t| := by
  rcases exists_norm_logDeriv_riemannZeta_sigma_it_le_log_abs_add_three_of_one_add_le
      hε with ⟨C, hC, hbound⟩
  refine ⟨2 * C, 3, mul_nonneg (by norm_num) hC, by norm_num, ?_⟩
  intro σ t hσ _hσ_le ht
  have hlog := log_abs_add_three_le_two_log_abs ht
  calc
    ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖
        ≤ C * Real.log (|t| + 3) := hbound σ t hσ
    _ ≤ C * (2 * Real.log |t|) :=
        mul_le_mul_of_nonneg_left hlog hC
    _ = (2 * C) * Real.log |t| := by ring

/-- Signed fixed-margin high-height vertical logarithmic bound in the exact
`C * log |t|` scale. -/
lemma exists_norm_neg_logDeriv_riemannZeta_sigma_it_le_log_abs_of_fixed_margin
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 3 ≤ T0 ∧
      ∀ σ t : ℝ, 1 + ε ≤ σ → σ ≤ 2 → T0 ≤ |t| →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          C * Real.log |t| := by
  rcases exists_norm_logDeriv_riemannZeta_sigma_it_le_log_abs_of_fixed_margin
      hε with ⟨C, T0, hC, hT0, hbound⟩
  refine ⟨C, T0, hC, hT0, ?_⟩
  intro σ t hσ hσ_le ht
  calc
    ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖
        = ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := norm_neg _
    _ ≤ C * Real.log |t| := hbound σ t hσ hσ_le ht

/-- Fixed-margin high-height logarithmic bound for the shifted third
3-4-1 point `σ + 2it`, again in the exact `C * log |t|` scale.

Like `exists_norm_logDeriv_riemannZeta_sigma_it_le_log_abs_of_fixed_margin`,
this is a fixed-margin result and not the missing boundary-strip estimate. -/
lemma exists_norm_logDeriv_riemannZeta_sigma_two_it_le_log_abs_of_fixed_margin
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 3 ≤ T0 ∧
      ∀ σ t : ℝ, 1 + ε ≤ σ → σ ≤ 2 → T0 ≤ |t| →
        ‖logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖ ≤
          C * Real.log |t| := by
  rcases exists_norm_logDeriv_riemannZeta_sigma_two_it_le_log_abs_add_three_of_one_add_le
      hε with ⟨C, hC, hbound⟩
  refine ⟨2 * C, 3, mul_nonneg (by norm_num) hC, by norm_num, ?_⟩
  intro σ t hσ _hσ_le ht
  have hlog := log_abs_add_three_le_two_log_abs ht
  calc
    ‖logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖
        ≤ C * Real.log (|t| + 3) := hbound σ t hσ
    _ ≤ C * (2 * Real.log |t|) :=
        mul_le_mul_of_nonneg_left hlog hC
    _ = (2 * C) * Real.log |t| := by ring

/-- Signed fixed-margin high-height logarithmic bound for the shifted third
3-4-1 point `σ + 2it`. -/
lemma exists_norm_neg_logDeriv_riemannZeta_sigma_two_it_le_log_abs_of_fixed_margin
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 3 ≤ T0 ∧
      ∀ σ t : ℝ, 1 + ε ≤ σ → σ ≤ 2 → T0 ≤ |t| →
        ‖-logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖ ≤
          C * Real.log |t| := by
  rcases exists_norm_logDeriv_riemannZeta_sigma_two_it_le_log_abs_of_fixed_margin
      hε with ⟨C, T0, hC, hT0, hbound⟩
  refine ⟨C, T0, hC, hT0, ?_⟩
  intro σ t hσ hσ_le ht
  calc
    ‖-logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖
        = ‖logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖ := norm_neg _
    _ ≤ C * Real.log |t| := hbound σ t hσ hσ_le ht

/-- On the strip `1 <= σ <= 2`, `‖σ + it‖` is bounded by `|t| + 2`. -/
lemma norm_sigma_add_I_mul_le_abs_add_two {σ t : ℝ}
    (hσ : σ ∈ Set.Icc 1 2) :
    ‖((σ : ℂ) + I * (t : ℂ))‖ ≤ |t| + 2 := by
  have hnorm :
      ‖((σ : ℂ) + I * (t : ℂ))‖ ≤ ‖(σ : ℂ)‖ + ‖I * (t : ℂ)‖ :=
    norm_add_le _ _
  have hσ_norm : ‖(σ : ℂ)‖ = |σ| := by
    simp
  have hIt_norm : ‖I * (t : ℂ)‖ = |t| := by
    rw [norm_mul, Complex.norm_I]
    simp
  have hσ_abs_le : |σ| ≤ 2 := by
    rw [abs_of_nonneg (by linarith [hσ.1])]
    exact hσ.2
  calc
      ‖((σ : ℂ) + I * (t : ℂ))‖
          ≤ ‖(σ : ℂ)‖ + ‖I * (t : ℂ)‖ := hnorm
      _ = |σ| + |t| := by rw [hσ_norm, hIt_norm]
      _ ≤ 2 + |t| := by nlinarith [hσ_abs_le]
      _ = |t| + 2 := by ring

/-- The imaginary-height logarithm is bounded by the full complex-height
logarithm.  This is the direction needed when a Borel estimate has already
been normalized to `log |t|` but an existing high-height closure expects
`log(‖σ+it‖+3)`. -/
lemma log_abs_le_log_norm_sigma_add_I_mul_add_three {σ t : ℝ}
    (ht : 0 < |t|) :
    Real.log |t| ≤
      Real.log (‖((σ : ℂ) + I * (t : ℂ))‖ + 3) := by
  have hle_norm : |t| ≤ ‖((σ : ℂ) + I * (t : ℂ))‖ := by
    simpa using Complex.abs_im_le_norm ((σ : ℂ) + I * (t : ℂ))
  have hle : |t| ≤ ‖((σ : ℂ) + I * (t : ℂ))‖ + 3 := by
    nlinarith
  exact Real.log_le_log ht hle

/-- Above height `5`, `log(‖σ + it‖ + 3)` is controlled by
`2 log |t|` uniformly for `1 <= σ <= 2`. -/
lemma log_norm_sigma_add_I_mul_add_three_le_two_log_abs {σ t : ℝ}
    (hσ : σ ∈ Set.Icc 1 2) (ht : 5 ≤ |t|) :
    Real.log (‖((σ : ℂ) + I * (t : ℂ))‖ + 3) ≤
      2 * Real.log |t| := by
  have hnorm_le :
      ‖((σ : ℂ) + I * (t : ℂ))‖ ≤ |t| + 2 :=
    norm_sigma_add_I_mul_le_abs_add_two hσ
  have ht_pos : 0 < |t| := by linarith
  have hleft_pos : 0 < ‖((σ : ℂ) + I * (t : ℂ))‖ + 3 := by positivity
  have hsum_le :
      ‖((σ : ℂ) + I * (t : ℂ))‖ + 3 ≤ 2 * |t| := by
    calc
      ‖((σ : ℂ) + I * (t : ℂ))‖ + 3
          ≤ (|t| + 2) + 3 := by nlinarith [hnorm_le]
      _ ≤ 2 * |t| := by linarith
  have hlog_le :
      Real.log (‖((σ : ℂ) + I * (t : ℂ))‖ + 3) ≤
        Real.log (2 * |t|) :=
    Real.log_le_log hleft_pos hsum_le
  have hlog_mul : Real.log (2 * |t|) = Real.log 2 + Real.log |t| := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt ht_pos)]
  have hlog_two_le : Real.log 2 ≤ Real.log |t| :=
    Real.log_le_log (by norm_num) (by linarith : (2 : ℝ) ≤ |t|)
  calc
    Real.log (‖((σ : ℂ) + I * (t : ℂ))‖ + 3)
        ≤ Real.log (2 * |t|) := hlog_le
    _ = Real.log 2 + Real.log |t| := hlog_mul
    _ ≤ 2 * Real.log |t| := by linarith

/-- Variant of `log_norm_sigma_add_I_mul_add_three_le_two_log_abs` for the
right-shifted centers used by local Borel-Carathéodory disks.  The wider
`1 <= σ <= 3` strip costs only raising the safe height from `5` to `6`. -/
lemma log_norm_sigma_add_I_mul_add_three_le_two_log_abs_of_re_le_three {σ t : ℝ}
    (hσ : σ ∈ Set.Icc 1 3) (ht : 6 ≤ |t|) :
    Real.log (‖((σ : ℂ) + I * (t : ℂ))‖ + 3) ≤
      2 * Real.log |t| := by
  have hnorm :
      ‖((σ : ℂ) + I * (t : ℂ))‖ ≤ ‖(σ : ℂ)‖ + ‖I * (t : ℂ)‖ :=
    norm_add_le _ _
  have hσ_norm : ‖(σ : ℂ)‖ = |σ| := by
    simp
  have hIt_norm : ‖I * (t : ℂ)‖ = |t| := by
    rw [norm_mul, Complex.norm_I]
    simp
  have hσ_abs_le : |σ| ≤ 3 := by
    rw [abs_of_nonneg (by linarith [hσ.1])]
    exact hσ.2
  have hnorm_le : ‖((σ : ℂ) + I * (t : ℂ))‖ ≤ |t| + 3 := by
    calc
      ‖((σ : ℂ) + I * (t : ℂ))‖
          ≤ ‖(σ : ℂ)‖ + ‖I * (t : ℂ)‖ := hnorm
      _ = |σ| + |t| := by rw [hσ_norm, hIt_norm]
      _ ≤ 3 + |t| := by nlinarith [hσ_abs_le]
      _ = |t| + 3 := by ring
  have ht_pos : 0 < |t| := by linarith
  have hleft_pos : 0 < ‖((σ : ℂ) + I * (t : ℂ))‖ + 3 := by positivity
  have hsum_le :
      ‖((σ : ℂ) + I * (t : ℂ))‖ + 3 ≤ 2 * |t| := by
    calc
      ‖((σ : ℂ) + I * (t : ℂ))‖ + 3
          ≤ (|t| + 3) + 3 := by nlinarith [hnorm_le]
      _ ≤ 2 * |t| := by linarith
  have hlog_le :
      Real.log (‖((σ : ℂ) + I * (t : ℂ))‖ + 3) ≤
        Real.log (2 * |t|) :=
    Real.log_le_log hleft_pos hsum_le
  have hlog_mul : Real.log (2 * |t|) = Real.log 2 + Real.log |t| := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt ht_pos)]
  have hlog_two_le : Real.log 2 ≤ Real.log |t| :=
    Real.log_le_log (by norm_num) (by linarith : (2 : ℝ) ≤ |t|)
  calc
    Real.log (‖((σ : ℂ) + I * (t : ℂ))‖ + 3)
        ≤ Real.log (2 * |t|) := hlog_le
    _ = Real.log 2 + Real.log |t| := hlog_mul
    _ ≤ 2 * Real.log |t| := by linarith

/-- Complex-variable form of the full-height logarithmic comparison. -/
lemma log_norm_add_three_le_two_log_abs_im {s : ℂ}
    (hs_re : s.re ∈ Set.Icc 1 2) (hs_height : 5 ≤ |s.im|) :
    Real.log (‖s‖ + 3) ≤ 2 * Real.log |s.im| := by
  have hs_decomp : ((s.re : ℂ) + I * (s.im : ℂ)) = s := by
    apply Complex.ext <;> simp
  simpa [hs_decomp] using
    log_norm_sigma_add_I_mul_add_three_le_two_log_abs
      (σ := s.re) (t := s.im) hs_re hs_height

/-- Standalone normalization of a future vertical-strip log-derivative estimate.

If a high-height estimate for `logDeriv ζ` on `1 <= σ <= 2` is available in
the natural Borel/Jensen scale `A + B * log(‖σ+it‖ + 3)`, then above the same
height it has the exact classical scale `C * log |t|`.  This theorem does not
prove the missing zeta-specific growth estimate; it removes the remaining
constant and height-scale bookkeeping once that estimate is supplied. -/
lemma exists_re_im_logDeriv_vertical_log_bound_of_affine_log_norm_add_three_bound_high_height
    (T0 A B : ℝ) (hT0 : 5 ≤ T0) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          A + B * Real.log (‖((σ : ℂ) + I * t)‖ + 3)) :
    ∃ C T0' : ℝ, 0 ≤ C ∧ 5 ≤ T0' ∧
      ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → T0' ≤ |t| →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          C * Real.log |t| := by
  refine ⟨A + 2 * B, T0, add_nonneg hA (mul_nonneg (by norm_num) hB),
    hT0, ?_⟩
  intro σ t hσ_left hσ_right ht
  have hσ_mem : σ ∈ Set.Icc 1 2 := ⟨hσ_left, hσ_right⟩
  have ht5 : 5 ≤ |t| := hT0.trans ht
  have hlog_ge_one : 1 ≤ Real.log |t| := by
    exact (log_abs_gt_one_of_three_le (by linarith : 3 ≤ |t|)).le
  have hA_le : A ≤ A * Real.log |t| := by
    calc
      A = A * 1 := by ring
      _ ≤ A * Real.log |t| :=
          mul_le_mul_of_nonneg_left hlog_ge_one hA
  have hlog_norm :
      Real.log (‖((σ : ℂ) + I * t)‖ + 3) ≤ 2 * Real.log |t| := by
    simpa using
      log_norm_sigma_add_I_mul_add_three_le_two_log_abs
        (σ := σ) (t := t) hσ_mem ht5
  calc
    ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖
        ≤ A + B * Real.log (‖((σ : ℂ) + I * t)‖ + 3) :=
          hvertical σ t ht hσ_mem
    _ ≤ A * Real.log |t| + B * (2 * Real.log |t|) := by
          exact add_le_add hA_le (mul_le_mul_of_nonneg_left hlog_norm hB)
    _ = (A + 2 * B) * Real.log |t| := by ring

/-- Multiplicative full-height version of
`exists_re_im_logDeriv_vertical_log_bound_of_affine_log_norm_add_three_bound_high_height`. -/
lemma exists_re_im_logDeriv_vertical_log_bound_of_log_norm_add_three_bound_high_height
    (T0 C : ℝ) (hT0 : 5 ≤ T0) (hC : 0 ≤ C)
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          C * Real.log (‖((σ : ℂ) + I * t)‖ + 3)) :
    ∃ C' T0' : ℝ, 0 ≤ C' ∧ 5 ≤ T0' ∧
      ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → T0' ≤ |t| →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          C' * Real.log |t| := by
  refine
    exists_re_im_logDeriv_vertical_log_bound_of_affine_log_norm_add_three_bound_high_height
      T0 0 C hT0 (by norm_num) hC ?_
  intro σ t ht hσ
  simpa using hvertical σ t ht hσ

/-- Signed standalone normalization of a future vertical-strip
`-logDeriv ζ` estimate.

This is the same bookkeeping as
`exists_re_im_logDeriv_vertical_log_bound_of_affine_log_norm_add_three_bound_high_height`,
but in the sign convention used by the 3-4-1 inequality.  It does not prove
the missing zeta-specific growth estimate. -/
lemma exists_re_im_neg_logDeriv_vertical_log_bound_of_affine_log_norm_add_three_bound_high_height
    (T0 A B : ℝ) (hT0 : 5 ≤ T0) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          A + B * Real.log (‖((σ : ℂ) + I * t)‖ + 3)) :
    ∃ C T0' : ℝ, 0 ≤ C ∧ 5 ≤ T0' ∧
      ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → T0' ≤ |t| →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          C * Real.log |t| := by
  have hvertical_pos :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          A + B * Real.log (‖((σ : ℂ) + I * t)‖ + 3) := by
    intro σ t ht hσ
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖
          = ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := (norm_neg _).symm
      _ ≤ A + B * Real.log (‖((σ : ℂ) + I * t)‖ + 3) :=
          hvertical σ t ht hσ
  rcases
      exists_re_im_logDeriv_vertical_log_bound_of_affine_log_norm_add_three_bound_high_height
        T0 A B hT0 hA hB hvertical_pos
    with ⟨C, T0', hC, hT0', hbound⟩
  refine ⟨C, T0', hC, hT0', ?_⟩
  intro σ t hσ_left hσ_right ht
  calc
    ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖
        = ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := norm_neg _
    _ ≤ C * Real.log |t| := hbound σ t hσ_left hσ_right ht

/-- Multiplicative full-height signed version of
`exists_re_im_neg_logDeriv_vertical_log_bound_of_affine_log_norm_add_three_bound_high_height`. -/
lemma exists_re_im_neg_logDeriv_vertical_log_bound_of_log_norm_add_three_bound_high_height
    (T0 C : ℝ) (hT0 : 5 ≤ T0) (hC : 0 ≤ C)
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          C * Real.log (‖((σ : ℂ) + I * t)‖ + 3)) :
    ∃ C' T0' : ℝ, 0 ≤ C' ∧ 5 ≤ T0' ∧
      ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → T0' ≤ |t| →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          C' * Real.log |t| := by
  refine
    exists_re_im_neg_logDeriv_vertical_log_bound_of_affine_log_norm_add_three_bound_high_height
      T0 0 C hT0 (by norm_num) hC ?_
  intro σ t ht hσ
  simpa using hvertical σ t ht hσ

/-- Real-part quotient form of
`exists_re_im_logDeriv_vertical_log_bound_of_affine_log_norm_add_three_bound_high_height`.

This theorem is the direct bridge from a future Borel/Jensen-style norm growth
estimate for `logDeriv zeta` to the `Re(-zeta'/zeta)` convention consumed by
the 3-4-1 zero-free-region route. -/
lemma exists_re_neg_deriv_div_vertical_log_bound_of_affine_log_norm_add_three_bound_high_height
    (T0 A B : ℝ) (hT0 : 5 ≤ T0) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          A + B * Real.log (‖((σ : ℂ) + I * t)‖ + 3)) :
    ∃ C T0' : ℝ, 0 ≤ C ∧ 5 ≤ T0' ∧
      ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → T0' ≤ |t| →
        (-deriv riemannZeta ((σ : ℂ) + I * t) /
            riemannZeta ((σ : ℂ) + I * t)).re ≤
          C * Real.log |t| := by
  rcases
      exists_re_im_logDeriv_vertical_log_bound_of_affine_log_norm_add_three_bound_high_height
        T0 A B hT0 hA hB hvertical with
    ⟨C, T0', hC, hT0', hnorm⟩
  refine ⟨C, T0', hC, hT0', ?_⟩
  intro σ t hσ_left hσ_right ht
  let z : ℂ := (σ : ℂ) + I * t
  calc
    (-deriv riemannZeta z / riemannZeta z).re
        ≤ ‖-deriv riemannZeta z / riemannZeta z‖ := Complex.re_le_norm _
    _ = ‖logDeriv riemannZeta z‖ :=
        norm_neg_deriv_div_riemannZeta_eq_norm_logDeriv z
    _ ≤ C * Real.log |t| := by
        simpa [z] using hnorm σ t hσ_left hσ_right ht

/-- Signed-norm version of
`exists_re_neg_deriv_div_vertical_log_bound_of_affine_log_norm_add_three_bound_high_height`. -/
lemma exists_re_neg_deriv_div_vertical_log_bound_of_neg_affine_log_norm_add_three_bound_high_height
    (T0 A B : ℝ) (hT0 : 5 ≤ T0) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          A + B * Real.log (‖((σ : ℂ) + I * t)‖ + 3)) :
    ∃ C T0' : ℝ, 0 ≤ C ∧ 5 ≤ T0' ∧
      ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → T0' ≤ |t| →
        (-deriv riemannZeta ((σ : ℂ) + I * t) /
            riemannZeta ((σ : ℂ) + I * t)).re ≤
          C * Real.log |t| := by
  rcases
      exists_re_im_neg_logDeriv_vertical_log_bound_of_affine_log_norm_add_three_bound_high_height
        T0 A B hT0 hA hB hvertical with
    ⟨C, T0', hC, hT0', hnorm⟩
  refine ⟨C, T0', hC, hT0', ?_⟩
  intro σ t hσ_left hσ_right ht
  let z : ℂ := (σ : ℂ) + I * t
  calc
    (-deriv riemannZeta z / riemannZeta z).re
        ≤ ‖-deriv riemannZeta z / riemannZeta z‖ := Complex.re_le_norm _
    _ = ‖logDeriv riemannZeta z‖ :=
        norm_neg_deriv_div_riemannZeta_eq_norm_logDeriv z
    _ = ‖-logDeriv riemannZeta z‖ := (norm_neg _).symm
    _ ≤ C * Real.log |t| := by
        simpa [z] using hnorm σ t hσ_left hσ_right ht

/-- Coordinate high-height closure from a single `C * log(|t| + 3)` bound.

This shape is common in analytic estimates because it is harmless at small
height.  Above height `3`, `log(|t| + 3) <= 2 log |t|`, so the estimate feeds
the affine-log coordinate closure. -/
lemma classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_log_abs_add_three_bound_high_height
    (T0 C : ℝ) (hT0 : 3 ≤ T0) (hC : 0 ≤ C)
    (hregular :
      ∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
        0 < σ - β →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
            (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
          C * Real.log (|t| + 3))
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          C * Real.log (|t| + 3)) :
    classical_zero_free_region := by
  refine
    classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_affine_bounds_high_height
      T0 0 (2 * C) 0 (2 * C) hT0 (by norm_num) (by nlinarith)
      (by norm_num) (by nlinarith) ?_ ?_
  · intro σ β t ht hσ hζ hβ hsub
    have hlog := log_abs_add_three_le_two_log_abs (hT0.trans ht)
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
          (((σ - β : ℝ) : ℂ)⁻¹)‖
          ≤ C * Real.log (|t| + 3) :=
            hregular σ β t ht hσ hζ hβ hsub
      _ ≤ C * (2 * Real.log |t|) :=
            mul_le_mul_of_nonneg_left hlog hC
      _ = 0 + (2 * C) * Real.log |t| := by ring
  · intro σ t ht hσ
    have hlog := log_abs_add_three_le_two_log_abs (hT0.trans ht)
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖
          ≤ C * Real.log (|t| + 3) := hvertical σ t ht hσ
      _ ≤ C * (2 * Real.log |t|) :=
            mul_le_mul_of_nonneg_left hlog hC
      _ = 0 + (2 * C) * Real.log |t| := by ring

/-- Coordinate high-height closure from separate
`Cregular * log(|t| + 3)` and `Cvertical * log(|t| + 3)` bounds.

This avoids forcing the regular-part and vertical-strip estimates to share
one coefficient; each estimate is normalized separately to the affine-log
interface. -/
lemma classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_log_abs_add_three_bounds_high_height
    (T0 Cregular Cvertical : ℝ) (hT0 : 3 ≤ T0)
    (hCregular : 0 ≤ Cregular) (hCvertical : 0 ≤ Cvertical)
    (hregular :
      ∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
        0 < σ - β →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
            (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
          Cregular * Real.log (|t| + 3))
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          Cvertical * Real.log (|t| + 3)) :
    classical_zero_free_region := by
  refine
    classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_affine_bounds_high_height
      T0 0 (2 * Cregular) 0 (2 * Cvertical) hT0 (by norm_num)
      (by nlinarith) (by norm_num) (by nlinarith) ?_ ?_
  · intro σ β t ht hσ hζ hβ hsub
    have hlog := log_abs_add_three_le_two_log_abs (hT0.trans ht)
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
          (((σ - β : ℝ) : ℂ)⁻¹)‖
          ≤ Cregular * Real.log (|t| + 3) :=
            hregular σ β t ht hσ hζ hβ hsub
      _ ≤ Cregular * (2 * Real.log |t|) :=
            mul_le_mul_of_nonneg_left hlog hCregular
      _ = 0 + (2 * Cregular) * Real.log |t| := by ring
  · intro σ t ht hσ
    have hlog := log_abs_add_three_le_two_log_abs (hT0.trans ht)
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖
          ≤ Cvertical * Real.log (|t| + 3) := hvertical σ t ht hσ
      _ ≤ Cvertical * (2 * Real.log |t|) :=
            mul_le_mul_of_nonneg_left hlog hCvertical
      _ = 0 + (2 * Cvertical) * Real.log |t| := by ring

/-- Coordinate high-height closure from affine safe-height logarithmic bounds
`A + B * log(|t| + 3)`.

This is the `log(|t| + 3)` counterpart of
`classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_affine_bounds_high_height`.
It keeps additive constants in the future analytic estimates, then absorbs the
height scale into the exact `log |t|` affine interface above height `3`. -/
lemma classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_affine_log_abs_add_three_bounds_high_height
    (T0 Aregular Bregular Avertical Bvertical : ℝ) (hT0 : 3 ≤ T0)
    (hAregular : 0 ≤ Aregular) (hBregular : 0 ≤ Bregular)
    (hAvertical : 0 ≤ Avertical) (hBvertical : 0 ≤ Bvertical)
    (hregular :
      ∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
        0 < σ - β →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
            (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
          Aregular + Bregular * Real.log (|t| + 3))
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          Avertical + Bvertical * Real.log (|t| + 3)) :
    classical_zero_free_region := by
  refine
    classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_affine_bounds_high_height
      T0 Aregular (2 * Bregular) Avertical (2 * Bvertical) hT0
      hAregular (by nlinarith) hAvertical (by nlinarith) ?_ ?_
  · intro σ β t ht hσ hζ hβ hsub
    have hlog := log_abs_add_three_le_two_log_abs (hT0.trans ht)
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
          (((σ - β : ℝ) : ℂ)⁻¹)‖
          ≤ Aregular + Bregular * Real.log (|t| + 3) :=
            hregular σ β t ht hσ hζ hβ hsub
      _ ≤ Aregular + Bregular * (2 * Real.log |t|) :=
            add_le_add (le_refl Aregular)
              (mul_le_mul_of_nonneg_left hlog hBregular)
      _ = Aregular + (2 * Bregular) * Real.log |t| := by ring
  · intro σ t ht hσ
    have hlog := log_abs_add_three_le_two_log_abs (hT0.trans ht)
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖
          ≤ Avertical + Bvertical * Real.log (|t| + 3) :=
            hvertical σ t ht hσ
      _ ≤ Avertical + Bvertical * (2 * Real.log |t|) :=
            add_le_add (le_refl Avertical)
              (mul_le_mul_of_nonneg_left hlog hBvertical)
      _ = Avertical + (2 * Bvertical) * Real.log |t| := by ring

/-- Existential coordinate high-height closure from affine safe-height
logarithmic bounds `A + B * log(|t| + 3)`. -/
lemma classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_affine_log_abs_add_three_bounds_high_height
    (h :
      ∃ T0 Aregular Bregular Avertical Bvertical : ℝ, 3 ≤ T0 ∧
        0 ≤ Aregular ∧ 0 ≤ Bregular ∧ 0 ≤ Avertical ∧ 0 ≤ Bvertical ∧
        (∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
          0 < σ - β →
          ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
              (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
            Aregular + Bregular * Real.log (|t| + 3)) ∧
        (∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
            Avertical + Bvertical * Real.log (|t| + 3))) :
    classical_zero_free_region := by
  rcases h with
    ⟨T0, Aregular, Bregular, Avertical, Bvertical, hT0, hAregular,
      hBregular, hAvertical, hBvertical, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_affine_log_abs_add_three_bounds_high_height
      T0 Aregular Bregular Avertical Bvertical hT0 hAregular hBregular
      hAvertical hBvertical hregular hvertical

/-- Existential coordinate high-height closure from a single
`C * log(|t| + 3)` bound. -/
lemma classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_log_abs_add_three_bound_high_height
    (h :
      ∃ T0 C : ℝ, 3 ≤ T0 ∧ 0 ≤ C ∧
        (∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
          0 < σ - β →
          ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
              (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
            C * Real.log (|t| + 3)) ∧
        (∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
            C * Real.log (|t| + 3))) :
    classical_zero_free_region := by
  rcases h with ⟨T0, C, hT0, hC, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_log_abs_add_three_bound_high_height
      T0 C hT0 hC hregular hvertical

/-- Existential coordinate high-height closure from separate
`Cregular * log(|t| + 3)` and `Cvertical * log(|t| + 3)` bounds. -/
lemma classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_log_abs_add_three_bounds_high_height
    (h :
      ∃ T0 Cregular Cvertical : ℝ, 3 ≤ T0 ∧
        0 ≤ Cregular ∧ 0 ≤ Cvertical ∧
        (∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
          0 < σ - β →
          ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
              (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
            Cregular * Real.log (|t| + 3)) ∧
        (∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
            Cvertical * Real.log (|t| + 3))) :
    classical_zero_free_region := by
  rcases h with
    ⟨T0, Cregular, Cvertical, hT0, hCregular, hCvertical, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_log_abs_add_three_bounds_high_height
      T0 Cregular Cvertical hT0 hCregular hCvertical hregular hvertical

/-- Signed coordinate high-height closure from separate
`Cregular * log(|t| + 3)` and `Cvertical * log(|t| + 3)` bounds.

This is the `-logDeriv ζ` counterpart of
`classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_log_abs_add_three_bounds_high_height`. -/
lemma classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_log_abs_add_three_bounds_high_height
    (T0 Cregular Cvertical : ℝ) (hT0 : 3 ≤ T0)
    (hCregular : 0 ≤ Cregular) (hCvertical : 0 ≤ Cvertical)
    (hregular :
      ∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
        0 < σ - β →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
            (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
          Cregular * Real.log (|t| + 3))
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          Cvertical * Real.log (|t| + 3)) :
    classical_zero_free_region := by
  refine
    classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_log_abs_add_three_bounds_high_height
      T0 Cregular Cvertical hT0 hCregular hCvertical ?_ ?_
  · intro σ β t ht hσ hζ hβ hsub
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
          (((σ - β : ℝ) : ℂ)⁻¹)‖
          = ‖-(-logDeriv riemannZeta ((σ : ℂ) + I * t) +
              (((σ - β : ℝ) : ℂ)⁻¹))‖ := by ring_nf
      _ = ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
            (((σ - β : ℝ) : ℂ)⁻¹)‖ := norm_neg _
      _ ≤ Cregular * Real.log (|t| + 3) :=
          hregular σ β t ht hσ hζ hβ hsub
  · intro σ t ht hσ
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖
          = ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := (norm_neg _).symm
      _ ≤ Cvertical * Real.log (|t| + 3) := hvertical σ t ht hσ

/-- Signed coordinate high-height closure from affine safe-height logarithmic
bounds in the `-logDeriv ζ` convention. -/
lemma classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_affine_log_abs_add_three_bounds_high_height
    (T0 Aregular Bregular Avertical Bvertical : ℝ) (hT0 : 3 ≤ T0)
    (hAregular : 0 ≤ Aregular) (hBregular : 0 ≤ Bregular)
    (hAvertical : 0 ≤ Avertical) (hBvertical : 0 ≤ Bvertical)
    (hregular :
      ∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
        0 < σ - β →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
            (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
          Aregular + Bregular * Real.log (|t| + 3))
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          Avertical + Bvertical * Real.log (|t| + 3)) :
    classical_zero_free_region := by
  refine
    classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_affine_log_abs_add_three_bounds_high_height
      T0 Aregular Bregular Avertical Bvertical hT0 hAregular hBregular
      hAvertical hBvertical ?_ ?_
  · intro σ β t ht hσ hζ hβ hsub
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
          (((σ - β : ℝ) : ℂ)⁻¹)‖
          = ‖-(-logDeriv riemannZeta ((σ : ℂ) + I * t) +
              (((σ - β : ℝ) : ℂ)⁻¹))‖ := by ring_nf
      _ = ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
            (((σ - β : ℝ) : ℂ)⁻¹)‖ := norm_neg _
      _ ≤ Aregular + Bregular * Real.log (|t| + 3) :=
          hregular σ β t ht hσ hζ hβ hsub
  · intro σ t ht hσ
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖
          = ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := (norm_neg _).symm
      _ ≤ Avertical + Bvertical * Real.log (|t| + 3) :=
          hvertical σ t ht hσ

/-- Existential signed coordinate high-height closure from affine safe-height
logarithmic bounds in the `-logDeriv ζ` convention. -/
lemma classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_affine_log_abs_add_three_bounds_high_height
    (h :
      ∃ T0 Aregular Bregular Avertical Bvertical : ℝ, 3 ≤ T0 ∧
        0 ≤ Aregular ∧ 0 ≤ Bregular ∧ 0 ≤ Avertical ∧ 0 ≤ Bvertical ∧
        (∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
          0 < σ - β →
          ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
              (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
            Aregular + Bregular * Real.log (|t| + 3)) ∧
        (∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
            Avertical + Bvertical * Real.log (|t| + 3))) :
    classical_zero_free_region := by
  rcases h with
    ⟨T0, Aregular, Bregular, Avertical, Bvertical, hT0, hAregular,
      hBregular, hAvertical, hBvertical, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_affine_log_abs_add_three_bounds_high_height
      T0 Aregular Bregular Avertical Bvertical hT0 hAregular hBregular
      hAvertical hBvertical hregular hvertical

/-- Existential signed coordinate high-height closure from separate
`Cregular * log(|t| + 3)` and `Cvertical * log(|t| + 3)` bounds. -/
lemma classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_log_abs_add_three_bounds_high_height
    (h :
      ∃ T0 Cregular Cvertical : ℝ, 3 ≤ T0 ∧
        0 ≤ Cregular ∧ 0 ≤ Cvertical ∧
        (∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
          0 < σ - β →
          ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
              (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
            Cregular * Real.log (|t| + 3)) ∧
        (∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
            Cvertical * Real.log (|t| + 3))) :
    classical_zero_free_region := by
  rcases h with
    ⟨T0, Cregular, Cvertical, hT0, hCregular, hCvertical, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_log_abs_add_three_bounds_high_height
      T0 Cregular Cvertical hT0 hCregular hCvertical hregular hvertical

/-- Signed coordinate high-height closure from a single
`C * log(|t| + 3)` bound. -/
lemma classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_log_abs_add_three_bound_high_height
    (T0 C : ℝ) (hT0 : 3 ≤ T0) (hC : 0 ≤ C)
    (hregular :
      ∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
        0 < σ - β →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
            (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
          C * Real.log (|t| + 3))
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          C * Real.log (|t| + 3)) :
    classical_zero_free_region :=
  classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_log_abs_add_three_bounds_high_height
    T0 C C hT0 hC hC hregular hvertical

/-- Existential signed coordinate high-height closure from a single
`C * log(|t| + 3)` bound. -/
lemma classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_log_abs_add_three_bound_high_height
    (h :
      ∃ T0 C : ℝ, 3 ≤ T0 ∧ 0 ≤ C ∧
        (∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
          0 < σ - β →
          ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
              (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
            C * Real.log (|t| + 3)) ∧
        (∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
            C * Real.log (|t| + 3))) :
    classical_zero_free_region := by
  rcases h with ⟨T0, C, hT0, hC, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_log_abs_add_three_bound_high_height
      T0 C hT0 hC hregular hvertical

/-- Coordinate high-height closure from separate
`Cregular * log(‖σ+it‖ + 3)` and `Cvertical * log(‖σ+it‖ + 3)` bounds.

This accepts estimates stated in terms of the full complex height.  On the
strip `1 <= σ <= 2` and above height `5`, that logarithm is absorbed into
`2 log |t|`. -/
lemma classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height
    (T0 Cregular Cvertical : ℝ) (hT0 : 5 ≤ T0)
    (hCregular : 0 ≤ Cregular) (hCvertical : 0 ≤ Cvertical)
    (hregular :
      ∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
        0 < σ - β →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
            (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
          Cregular * Real.log (‖((σ : ℂ) + I * t)‖ + 3))
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          Cvertical * Real.log (‖((σ : ℂ) + I * t)‖ + 3)) :
    classical_zero_free_region := by
  refine
    classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_affine_bounds_high_height
      T0 0 (2 * Cregular) 0 (2 * Cvertical) (by linarith)
      (by norm_num) (by nlinarith) (by norm_num) (by nlinarith) ?_ ?_
  · intro σ β t ht hσ hζ hβ hsub
    have hlog :=
      log_norm_sigma_add_I_mul_add_three_le_two_log_abs hσ (hT0.trans ht)
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
          (((σ - β : ℝ) : ℂ)⁻¹)‖
          ≤ Cregular * Real.log (‖((σ : ℂ) + I * t)‖ + 3) :=
            hregular σ β t ht hσ hζ hβ hsub
      _ ≤ Cregular * (2 * Real.log |t|) :=
            mul_le_mul_of_nonneg_left hlog hCregular
      _ = 0 + (2 * Cregular) * Real.log |t| := by ring
  · intro σ t ht hσ
    have hlog :=
      log_norm_sigma_add_I_mul_add_three_le_two_log_abs hσ (hT0.trans ht)
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖
          ≤ Cvertical * Real.log (‖((σ : ℂ) + I * t)‖ + 3) :=
            hvertical σ t ht hσ
      _ ≤ Cvertical * (2 * Real.log |t|) :=
            mul_le_mul_of_nonneg_left hlog hCvertical
      _ = 0 + (2 * Cvertical) * Real.log |t| := by ring

/-- Existential coordinate high-height closure from separate
`Cregular * log(‖σ+it‖ + 3)` and `Cvertical * log(‖σ+it‖ + 3)` bounds. -/
lemma classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height
    (h :
      ∃ T0 Cregular Cvertical : ℝ, 5 ≤ T0 ∧
        0 ≤ Cregular ∧ 0 ≤ Cvertical ∧
        (∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
          0 < σ - β →
          ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
              (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
            Cregular * Real.log (‖((σ : ℂ) + I * t)‖ + 3)) ∧
        (∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
            Cvertical * Real.log (‖((σ : ℂ) + I * t)‖ + 3))) :
    classical_zero_free_region := by
  rcases h with
    ⟨T0, Cregular, Cvertical, hT0, hCregular, hCvertical, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height
      T0 Cregular Cvertical hT0 hCregular hCvertical hregular hvertical

/-- Coordinate multiplicity-aware high-height closure from separate
`Cregular * log(‖σ+it‖ + 3)` and `Cvertical * log(‖σ+it‖ + 3)` bounds. -/
lemma classical_zero_free_region_of_re_im_multiplicity_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height
    (T0 Cregular Cvertical : ℝ) (hT0 : 5 ≤ T0)
    (hCregular : 0 ≤ Cregular) (hCvertical : 0 ≤ Cvertical)
    (hregular :
      ∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
        0 < σ - β →
        ∃ n : ℕ, 0 < n ∧
          ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
              (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
            Cregular * Real.log (‖((σ : ℂ) + I * t)‖ + 3))
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          Cvertical * Real.log (‖((σ : ℂ) + I * t)‖ + 3)) :
    classical_zero_free_region := by
  refine
    classical_zero_free_region_of_re_im_multiplicity_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height
      T0 (2 * Cregular) (2 * Cvertical) (by linarith) (by nlinarith)
      (by nlinarith) ?_ ?_
  · intro σ β t ht hσ hζ hβ hsub
    have hlog :=
      log_norm_sigma_add_I_mul_add_three_le_two_log_abs hσ (hT0.trans ht)
    rcases hregular σ β t ht hσ hζ hβ hsub with ⟨n, hn_pos, hbound⟩
    refine ⟨n, hn_pos, ?_⟩
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
          (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖
          ≤ Cregular * Real.log (‖((σ : ℂ) + I * t)‖ + 3) := hbound
      _ ≤ Cregular * (2 * Real.log |t|) :=
            mul_le_mul_of_nonneg_left hlog hCregular
      _ = (2 * Cregular) * Real.log |t| := by ring
  · intro σ t ht hσ
    have hlog :=
      log_norm_sigma_add_I_mul_add_three_le_two_log_abs hσ (hT0.trans ht)
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖
          ≤ Cvertical * Real.log (‖((σ : ℂ) + I * t)‖ + 3) :=
            hvertical σ t ht hσ
      _ ≤ Cvertical * (2 * Real.log |t|) :=
            mul_le_mul_of_nonneg_left hlog hCvertical
      _ = (2 * Cvertical) * Real.log |t| := by ring

/-- Coordinate multiplicity-aware high-height closure from one
`C * log(‖σ+it‖ + 3)` bound. -/
lemma classical_zero_free_region_of_re_im_multiplicity_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height
    (T0 C : ℝ) (hT0 : 5 ≤ T0) (hC : 0 ≤ C)
    (hregular :
      ∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
        0 < σ - β →
        ∃ n : ℕ, 0 < n ∧
          ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
              (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
            C * Real.log (‖((σ : ℂ) + I * t)‖ + 3))
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          C * Real.log (‖((σ : ℂ) + I * t)‖ + 3)) :
    classical_zero_free_region :=
  classical_zero_free_region_of_re_im_multiplicity_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height
    T0 C C hT0 hC hC hregular hvertical

/-- Existential coordinate multiplicity-aware high-height closure from
separate `Cregular * log(‖σ+it‖ + 3)` and `Cvertical * log(‖σ+it‖ + 3)` bounds. -/
lemma classical_zero_free_region_of_exists_re_im_multiplicity_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height
    (h :
      ∃ T0 Cregular Cvertical : ℝ, 5 ≤ T0 ∧
        0 ≤ Cregular ∧ 0 ≤ Cvertical ∧
        (∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
          0 < σ - β →
          ∃ n : ℕ, 0 < n ∧
            ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
                (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
              Cregular * Real.log (‖((σ : ℂ) + I * t)‖ + 3)) ∧
        (∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
            Cvertical * Real.log (‖((σ : ℂ) + I * t)‖ + 3))) :
    classical_zero_free_region := by
  rcases h with
    ⟨T0, Cregular, Cvertical, hT0, hCregular, hCvertical, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_re_im_multiplicity_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height
      T0 Cregular Cvertical hT0 hCregular hCvertical hregular hvertical

/-- Existential coordinate multiplicity-aware high-height closure from one
`C * log(‖σ+it‖ + 3)` bound. -/
lemma classical_zero_free_region_of_exists_re_im_multiplicity_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height
    (h :
      ∃ T0 C : ℝ, 5 ≤ T0 ∧ 0 ≤ C ∧
        (∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
          0 < σ - β →
          ∃ n : ℕ, 0 < n ∧
            ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
                (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
              C * Real.log (‖((σ : ℂ) + I * t)‖ + 3)) ∧
        (∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
            C * Real.log (‖((σ : ℂ) + I * t)‖ + 3))) :
    classical_zero_free_region := by
  rcases h with ⟨T0, C, hT0, hC, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_re_im_multiplicity_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height
      T0 C hT0 hC hregular hvertical

/-- Signed coordinate multiplicity-aware high-height closure from separate
`Cregular * log(‖σ+it‖ + 3)` and `Cvertical * log(‖σ+it‖ + 3)` bounds. -/
lemma classical_zero_free_region_of_re_im_multiplicity_neg_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height
    (T0 Cregular Cvertical : ℝ) (hT0 : 5 ≤ T0)
    (hCregular : 0 ≤ Cregular) (hCvertical : 0 ≤ Cvertical)
    (hregular :
      ∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
        0 < σ - β →
        ∃ n : ℕ, 0 < n ∧
          ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
              (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
            Cregular * Real.log (‖((σ : ℂ) + I * t)‖ + 3))
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          Cvertical * Real.log (‖((σ : ℂ) + I * t)‖ + 3)) :
    classical_zero_free_region := by
  refine
    classical_zero_free_region_of_re_im_multiplicity_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height
      T0 Cregular Cvertical hT0 hCregular hCvertical ?_ ?_
  · intro σ β t ht hσ hζ hβ hsub
    rcases hregular σ β t ht hσ hζ hβ hsub with ⟨n, hn_pos, hbound⟩
    refine ⟨n, hn_pos, ?_⟩
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
          (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖
          = ‖-(-logDeriv riemannZeta ((σ : ℂ) + I * t) +
              (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹))‖ := by ring_nf
      _ = ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
            (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖ := norm_neg _
      _ ≤ Cregular * Real.log (‖((σ : ℂ) + I * t)‖ + 3) := hbound
  · intro σ t ht hσ
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖
          = ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := (norm_neg _).symm
      _ ≤ Cvertical * Real.log (‖((σ : ℂ) + I * t)‖ + 3) :=
          hvertical σ t ht hσ

/-- Signed coordinate multiplicity-aware high-height closure from one
`C * log(‖σ+it‖ + 3)` bound. -/
lemma classical_zero_free_region_of_re_im_multiplicity_neg_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height
    (T0 C : ℝ) (hT0 : 5 ≤ T0) (hC : 0 ≤ C)
    (hregular :
      ∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
        0 < σ - β →
        ∃ n : ℕ, 0 < n ∧
          ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
              (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
            C * Real.log (‖((σ : ℂ) + I * t)‖ + 3))
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          C * Real.log (‖((σ : ℂ) + I * t)‖ + 3)) :
    classical_zero_free_region :=
  classical_zero_free_region_of_re_im_multiplicity_neg_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height
    T0 C C hT0 hC hC hregular hvertical

/-- Existential signed coordinate multiplicity-aware high-height closure from
separate `Cregular * log(‖σ+it‖ + 3)` and `Cvertical * log(‖σ+it‖ + 3)` bounds. -/
lemma classical_zero_free_region_of_exists_re_im_multiplicity_neg_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height
    (h :
      ∃ T0 Cregular Cvertical : ℝ, 5 ≤ T0 ∧
        0 ≤ Cregular ∧ 0 ≤ Cvertical ∧
        (∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
          0 < σ - β →
          ∃ n : ℕ, 0 < n ∧
            ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
                (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
              Cregular * Real.log (‖((σ : ℂ) + I * t)‖ + 3)) ∧
        (∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
            Cvertical * Real.log (‖((σ : ℂ) + I * t)‖ + 3))) :
    classical_zero_free_region := by
  rcases h with
    ⟨T0, Cregular, Cvertical, hT0, hCregular, hCvertical, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_re_im_multiplicity_neg_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height
      T0 Cregular Cvertical hT0 hCregular hCvertical hregular hvertical

/-- Existential signed coordinate multiplicity-aware high-height closure from
one `C * log(‖σ+it‖ + 3)` bound. -/
lemma classical_zero_free_region_of_exists_re_im_multiplicity_neg_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height
    (h :
      ∃ T0 C : ℝ, 5 ≤ T0 ∧ 0 ≤ C ∧
        (∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
          0 < σ - β →
          ∃ n : ℕ, 0 < n ∧
            ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
                (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
              C * Real.log (‖((σ : ℂ) + I * t)‖ + 3)) ∧
        (∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
            C * Real.log (‖((σ : ℂ) + I * t)‖ + 3))) :
    classical_zero_free_region := by
  rcases h with ⟨T0, C, hT0, hC, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_re_im_multiplicity_neg_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height
      T0 C hT0 hC hregular hvertical

/-- Signed coordinate high-height closure from separate
`Cregular * log(‖σ+it‖ + 3)` and `Cvertical * log(‖σ+it‖ + 3)` bounds.

This is the coordinate version of the signed full-height handoff, matching the
`-logDeriv ζ` sign convention used by the 3-4-1 inequality. -/
lemma classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height
    (T0 Cregular Cvertical : ℝ) (hT0 : 5 ≤ T0)
    (hCregular : 0 ≤ Cregular) (hCvertical : 0 ≤ Cvertical)
    (hregular :
      ∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
        0 < σ - β →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
            (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
          Cregular * Real.log (‖((σ : ℂ) + I * t)‖ + 3))
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          Cvertical * Real.log (‖((σ : ℂ) + I * t)‖ + 3)) :
    classical_zero_free_region := by
  refine
    classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height
      T0 Cregular Cvertical hT0 hCregular hCvertical ?_ ?_
  · intro σ β t ht hσ hζ hβ hsub
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
          (((σ - β : ℝ) : ℂ)⁻¹)‖
          = ‖-(-logDeriv riemannZeta ((σ : ℂ) + I * t) +
              (((σ - β : ℝ) : ℂ)⁻¹))‖ := by ring_nf
      _ = ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
            (((σ - β : ℝ) : ℂ)⁻¹)‖ := norm_neg _
      _ ≤ Cregular * Real.log (‖((σ : ℂ) + I * t)‖ + 3) :=
          hregular σ β t ht hσ hζ hβ hsub
  · intro σ t ht hσ
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖
          = ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := (norm_neg _).symm
      _ ≤ Cvertical * Real.log (‖((σ : ℂ) + I * t)‖ + 3) :=
          hvertical σ t ht hσ

/-- Existential signed coordinate high-height closure from separate
`Cregular * log(‖σ+it‖ + 3)` and `Cvertical * log(‖σ+it‖ + 3)` bounds. -/
lemma classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height
    (h :
      ∃ T0 Cregular Cvertical : ℝ, 5 ≤ T0 ∧
        0 ≤ Cregular ∧ 0 ≤ Cvertical ∧
        (∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
          0 < σ - β →
          ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
              (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
            Cregular * Real.log (‖((σ : ℂ) + I * t)‖ + 3)) ∧
        (∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
            Cvertical * Real.log (‖((σ : ℂ) + I * t)‖ + 3))) :
    classical_zero_free_region := by
  rcases h with
    ⟨T0, Cregular, Cvertical, hT0, hCregular, hCvertical, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height
      T0 Cregular Cvertical hT0 hCregular hCvertical hregular hvertical

/-- Signed coordinate high-height closure from a single
`C * log(‖σ+it‖ + 3)` bound for both remaining log-derivative estimates. -/
lemma classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height
    (T0 C : ℝ) (hT0 : 5 ≤ T0) (hC : 0 ≤ C)
    (hregular :
      ∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
        0 < σ - β →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
            (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
          C * Real.log (‖((σ : ℂ) + I * t)‖ + 3))
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          C * Real.log (‖((σ : ℂ) + I * t)‖ + 3)) :
    classical_zero_free_region :=
  classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height
    T0 C C hT0 hC hC hregular hvertical

/-- Existential signed coordinate high-height closure from a single
`C * log(‖σ+it‖ + 3)` bound for both remaining log-derivative estimates. -/
lemma classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height
    (h :
      ∃ T0 C : ℝ, 5 ≤ T0 ∧ 0 ≤ C ∧
        (∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
          0 < σ - β →
          ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
              (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
            C * Real.log (‖((σ : ℂ) + I * t)‖ + 3)) ∧
        (∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
            C * Real.log (‖((σ : ℂ) + I * t)‖ + 3))) :
    classical_zero_free_region := by
  rcases h with ⟨T0, C, hT0, hC, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height
      T0 C hT0 hC hregular hvertical

/-- Complex-variable high-height closure from separate
`Cregular * log(‖s‖ + 3)` and `Cvertical * log(‖z‖ + 3)` bounds.

This is the form closest to many Borel-Carathéodory/Jensen outputs: the
regular-part estimate is stated for complex variables `s, ρ`, while the
vertical estimate is stated for an arbitrary `z` in the same vertical strip. -/
lemma classical_zero_free_region_of_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height
    (T0 Cregular Cvertical : ℝ) (hT0 : 5 ≤ T0)
    (hCregular : 0 ≤ Cregular) (hCvertical : 0 ≤ Cvertical)
    (hregular :
      ∀ s ρ : ℂ, T0 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
        riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
        0 < s.re - ρ.re →
        ‖logDeriv riemannZeta s - (s - ρ)⁻¹‖ ≤
          Cregular * Real.log (‖s‖ + 3))
    (hvertical :
      ∀ z : ℂ, T0 ≤ |z.im| → z.re ∈ Set.Icc 1 2 →
        ‖logDeriv riemannZeta z‖ ≤
          Cvertical * Real.log (‖z‖ + 3)) :
    classical_zero_free_region := by
  refine
    classical_zero_free_region_of_logDeriv_regular_part_norm_affine_log_bound_and_vertical_logDeriv_norm_affine_log_bound_high_height
      T0 0 (2 * Cregular) 0 (2 * Cvertical) (by linarith)
      (by norm_num) (by nlinarith) (by norm_num) (by nlinarith) ?_ ?_
  · intro s ρ hs_height hs_re_mem hζρ hρ_im_eq hρ_re_lt hsub
    have hlog := log_norm_add_three_le_two_log_abs_im hs_re_mem
      (hT0.trans hs_height)
    calc
      ‖logDeriv riemannZeta s - (s - ρ)⁻¹‖
          ≤ Cregular * Real.log (‖s‖ + 3) :=
            hregular s ρ hs_height hs_re_mem hζρ hρ_im_eq hρ_re_lt hsub
      _ ≤ Cregular * (2 * Real.log |s.im|) :=
            mul_le_mul_of_nonneg_left hlog hCregular
      _ = 0 + (2 * Cregular) * Real.log |s.im| := by ring
  · intro z hz_height hz_re_mem
    have hlog := log_norm_add_three_le_two_log_abs_im hz_re_mem
      (hT0.trans hz_height)
    calc
      ‖logDeriv riemannZeta z‖
          ≤ Cvertical * Real.log (‖z‖ + 3) :=
            hvertical z hz_height hz_re_mem
      _ ≤ Cvertical * (2 * Real.log |z.im|) :=
            mul_le_mul_of_nonneg_left hlog hCvertical
      _ = 0 + (2 * Cvertical) * Real.log |z.im| := by ring

/-- Existential complex-variable high-height closure from separate
`Cregular * log(‖s‖ + 3)` and `Cvertical * log(‖z‖ + 3)` bounds. -/
lemma classical_zero_free_region_of_exists_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height
    (h :
      ∃ T0 Cregular Cvertical : ℝ, 5 ≤ T0 ∧
        0 ≤ Cregular ∧ 0 ≤ Cvertical ∧
        (∀ s ρ : ℂ, T0 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
          riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
          0 < s.re - ρ.re →
          ‖logDeriv riemannZeta s - (s - ρ)⁻¹‖ ≤
            Cregular * Real.log (‖s‖ + 3)) ∧
        (∀ z : ℂ, T0 ≤ |z.im| → z.re ∈ Set.Icc 1 2 →
          ‖logDeriv riemannZeta z‖ ≤
            Cvertical * Real.log (‖z‖ + 3))) :
    classical_zero_free_region := by
  rcases h with
    ⟨T0, Cregular, Cvertical, hT0, hCregular, hCvertical, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height
      T0 Cregular Cvertical hT0 hCregular hCvertical hregular hvertical

/-- Complex-variable high-height closure from a single
`C * log(‖s‖ + 3)` / `C * log(‖z‖ + 3)` bound for both remaining estimates. -/
lemma classical_zero_free_region_of_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height
    (T0 C : ℝ) (hT0 : 5 ≤ T0) (hC : 0 ≤ C)
    (hregular :
      ∀ s ρ : ℂ, T0 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
        riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
        0 < s.re - ρ.re →
        ‖logDeriv riemannZeta s - (s - ρ)⁻¹‖ ≤
          C * Real.log (‖s‖ + 3))
    (hvertical :
      ∀ z : ℂ, T0 ≤ |z.im| → z.re ∈ Set.Icc 1 2 →
        ‖logDeriv riemannZeta z‖ ≤
          C * Real.log (‖z‖ + 3)) :
    classical_zero_free_region :=
  classical_zero_free_region_of_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height
    T0 C C hT0 hC hC hregular hvertical

/-- Existential complex-variable high-height closure from a single
full-height logarithmic constant for both remaining estimates. -/
lemma classical_zero_free_region_of_exists_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height
    (h :
      ∃ T0 C : ℝ, 5 ≤ T0 ∧ 0 ≤ C ∧
        (∀ s ρ : ℂ, T0 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
          riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
          0 < s.re - ρ.re →
          ‖logDeriv riemannZeta s - (s - ρ)⁻¹‖ ≤
            C * Real.log (‖s‖ + 3)) ∧
        (∀ z : ℂ, T0 ≤ |z.im| → z.re ∈ Set.Icc 1 2 →
          ‖logDeriv riemannZeta z‖ ≤
            C * Real.log (‖z‖ + 3))) :
    classical_zero_free_region := by
  rcases h with ⟨T0, C, hT0, hC, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height
      T0 C hT0 hC hregular hvertical

/-- Complex-variable high-height closure from affine full-height logarithmic
bounds.

This accepts estimates of the shape `A + B * log(‖s‖ + 3)` directly on
complex variables.  Above height `5`, the full-height logarithm is absorbed
into the affine `log |Im|` closure. -/
lemma classical_zero_free_region_of_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height
    (T0 Aregular Bregular Avertical Bvertical : ℝ)
    (hT0 : 5 ≤ T0)
    (hAregular : 0 ≤ Aregular) (hBregular : 0 ≤ Bregular)
    (hAvertical : 0 ≤ Avertical) (hBvertical : 0 ≤ Bvertical)
    (hregular :
      ∀ s ρ : ℂ, T0 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
        riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
        0 < s.re - ρ.re →
        ‖logDeriv riemannZeta s - (s - ρ)⁻¹‖ ≤
          Aregular + Bregular * Real.log (‖s‖ + 3))
    (hvertical :
      ∀ z : ℂ, T0 ≤ |z.im| → z.re ∈ Set.Icc 1 2 →
        ‖logDeriv riemannZeta z‖ ≤
          Avertical + Bvertical * Real.log (‖z‖ + 3)) :
    classical_zero_free_region := by
  refine
    classical_zero_free_region_of_logDeriv_regular_part_norm_affine_log_bound_and_vertical_logDeriv_norm_affine_log_bound_high_height
      T0 Aregular (2 * Bregular) Avertical (2 * Bvertical)
      (by linarith) hAregular (by nlinarith) hAvertical
      (by nlinarith) ?_ ?_
  · intro s ρ hs_height hs_re_mem hζρ hρ_im_eq hρ_re_lt hsub
    have hlog := log_norm_add_three_le_two_log_abs_im hs_re_mem
      (hT0.trans hs_height)
    calc
      ‖logDeriv riemannZeta s - (s - ρ)⁻¹‖
          ≤ Aregular + Bregular * Real.log (‖s‖ + 3) :=
            hregular s ρ hs_height hs_re_mem hζρ hρ_im_eq hρ_re_lt hsub
      _ ≤ Aregular + Bregular * (2 * Real.log |s.im|) := by
            have hmul :=
              mul_le_mul_of_nonneg_left hlog hBregular
            nlinarith
      _ = Aregular + (2 * Bregular) * Real.log |s.im| := by ring
  · intro z hz_height hz_re_mem
    have hlog := log_norm_add_three_le_two_log_abs_im hz_re_mem
      (hT0.trans hz_height)
    calc
      ‖logDeriv riemannZeta z‖
          ≤ Avertical + Bvertical * Real.log (‖z‖ + 3) :=
            hvertical z hz_height hz_re_mem
      _ ≤ Avertical + Bvertical * (2 * Real.log |z.im|) := by
            have hmul :=
              mul_le_mul_of_nonneg_left hlog hBvertical
            nlinarith
      _ = Avertical + (2 * Bvertical) * Real.log |z.im| := by ring

/-- Existential complex-variable high-height closure from affine full-height
logarithmic bounds. -/
lemma classical_zero_free_region_of_exists_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height
    (h :
      ∃ T0 Aregular Bregular Avertical Bvertical : ℝ,
        5 ≤ T0 ∧
        0 ≤ Aregular ∧ 0 ≤ Bregular ∧
        0 ≤ Avertical ∧ 0 ≤ Bvertical ∧
        (∀ s ρ : ℂ, T0 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
          riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
          0 < s.re - ρ.re →
          ‖logDeriv riemannZeta s - (s - ρ)⁻¹‖ ≤
            Aregular + Bregular * Real.log (‖s‖ + 3)) ∧
        (∀ z : ℂ, T0 ≤ |z.im| → z.re ∈ Set.Icc 1 2 →
          ‖logDeriv riemannZeta z‖ ≤
            Avertical + Bvertical * Real.log (‖z‖ + 3))) :
    classical_zero_free_region := by
  rcases h with
    ⟨T0, Aregular, Bregular, Avertical, Bvertical, hT0,
      hAregular, hBregular, hAvertical, hBvertical, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height
      T0 Aregular Bregular Avertical Bvertical hT0 hAregular hBregular
      hAvertical hBvertical hregular hvertical

/-- Signed complex-variable high-height closure from affine full-height
logarithmic bounds.

This is the same handoff as
`classical_zero_free_region_of_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height`,
but in the `-logDeriv ζ` sign convention used by the 3-4-1 inequality and
the signed Borel wrappers. -/
lemma classical_zero_free_region_of_neg_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height
    (T0 Aregular Bregular Avertical Bvertical : ℝ)
    (hT0 : 5 ≤ T0)
    (hAregular : 0 ≤ Aregular) (hBregular : 0 ≤ Bregular)
    (hAvertical : 0 ≤ Avertical) (hBvertical : 0 ≤ Bvertical)
    (hregular :
      ∀ s ρ : ℂ, T0 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
        riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
        0 < s.re - ρ.re →
        ‖-logDeriv riemannZeta s + (s - ρ)⁻¹‖ ≤
          Aregular + Bregular * Real.log (‖s‖ + 3))
    (hvertical :
      ∀ z : ℂ, T0 ≤ |z.im| → z.re ∈ Set.Icc 1 2 →
        ‖-logDeriv riemannZeta z‖ ≤
          Avertical + Bvertical * Real.log (‖z‖ + 3)) :
    classical_zero_free_region := by
  refine
    classical_zero_free_region_of_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height
      T0 Aregular Bregular Avertical Bvertical hT0 hAregular hBregular
      hAvertical hBvertical ?_ ?_
  · intro s ρ hs_height hs_re_mem hζρ hρ_im_eq hρ_re_lt hsub
    calc
      ‖logDeriv riemannZeta s - (s - ρ)⁻¹‖
          = ‖-(-logDeriv riemannZeta s + (s - ρ)⁻¹)‖ := by ring_nf
      _ = ‖-logDeriv riemannZeta s + (s - ρ)⁻¹‖ := norm_neg _
      _ ≤ Aregular + Bregular * Real.log (‖s‖ + 3) :=
          hregular s ρ hs_height hs_re_mem hζρ hρ_im_eq hρ_re_lt hsub
  · intro z hz_height hz_re_mem
    calc
      ‖logDeriv riemannZeta z‖ = ‖-logDeriv riemannZeta z‖ := (norm_neg _).symm
      _ ≤ Avertical + Bvertical * Real.log (‖z‖ + 3) :=
          hvertical z hz_height hz_re_mem

/-- Existential signed complex-variable high-height closure from affine
full-height logarithmic bounds. -/
lemma classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height
    (h :
      ∃ T0 Aregular Bregular Avertical Bvertical : ℝ,
        5 ≤ T0 ∧
        0 ≤ Aregular ∧ 0 ≤ Bregular ∧
        0 ≤ Avertical ∧ 0 ≤ Bvertical ∧
        (∀ s ρ : ℂ, T0 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
          riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
          0 < s.re - ρ.re →
          ‖-logDeriv riemannZeta s + (s - ρ)⁻¹‖ ≤
            Aregular + Bregular * Real.log (‖s‖ + 3)) ∧
        (∀ z : ℂ, T0 ≤ |z.im| → z.re ∈ Set.Icc 1 2 →
          ‖-logDeriv riemannZeta z‖ ≤
            Avertical + Bvertical * Real.log (‖z‖ + 3))) :
    classical_zero_free_region := by
  rcases h with
    ⟨T0, Aregular, Bregular, Avertical, Bvertical, hT0,
      hAregular, hBregular, hAvertical, hBvertical, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_neg_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height
      T0 Aregular Bregular Avertical Bvertical hT0 hAregular hBregular
      hAvertical hBvertical hregular hvertical

/-- Signed coordinate high-height closure from affine full-height logarithmic
bounds.

This is the real-coordinate form of
`classical_zero_free_region_of_neg_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height`,
for estimates stated directly in variables `σ`, `β`, and `t`. -/
lemma classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height
    (T0 Aregular Bregular Avertical Bvertical : ℝ)
    (hT0 : 5 ≤ T0)
    (hAregular : 0 ≤ Aregular) (hBregular : 0 ≤ Bregular)
    (hAvertical : 0 ≤ Avertical) (hBvertical : 0 ≤ Bvertical)
    (hregular :
      ∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
        0 < σ - β →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
            (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
          Aregular + Bregular * Real.log (‖((σ : ℂ) + I * t)‖ + 3))
    (hvertical :
      ∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          Avertical + Bvertical * Real.log (‖((σ : ℂ) + I * t)‖ + 3)) :
    classical_zero_free_region := by
  refine
    classical_zero_free_region_of_neg_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height
      T0 Aregular Bregular Avertical Bvertical hT0 hAregular hBregular
      hAvertical hBvertical ?_ ?_
  · intro s ρ hs_height hs_re_mem hζρ hρ_im_eq hρ_re_lt hsub
    have hs_decomp : ((s.re : ℂ) + I * s.im) = s := by
      apply Complex.ext <;> simp
    have hρ_decomp : ((ρ.re : ℂ) + I * s.im) = ρ := by
      apply Complex.ext
      · simp
      · simp [hρ_im_eq]
    have hinv :
        (((s.re - ρ.re : ℝ) : ℂ)⁻¹) = (s - ρ)⁻¹ := by
      have hsub_eq : s - ρ = ((s.re - ρ.re : ℝ) : ℂ) := by
        apply Complex.ext
        · simp
        · simp [hρ_im_eq]
      rw [hsub_eq]
    have hζ_coord :
        riemannZeta ((ρ.re : ℂ) + I * s.im) = 0 := by
      simpa [hρ_decomp] using hζρ
    have h :=
      hregular s.re ρ.re s.im hs_height hs_re_mem hζ_coord hρ_re_lt hsub
    have harg :
        -logDeriv riemannZeta ((s.re : ℂ) + I * s.im) +
            (((s.re - ρ.re : ℝ) : ℂ)⁻¹) =
          -logDeriv riemannZeta s + (s - ρ)⁻¹ := by
      rw [hs_decomp, hinv]
    rwa [harg, hs_decomp] at h
  · intro z hz_height hz_re_mem
    have hz_decomp : ((z.re : ℂ) + I * z.im) = z := by
      apply Complex.ext <;> simp
    have h := hvertical z.re z.im hz_height hz_re_mem
    simpa [hz_decomp] using h

/-- Existential signed coordinate high-height closure from affine full-height
logarithmic bounds. -/
lemma classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height
    (h :
      ∃ T0 Aregular Bregular Avertical Bvertical : ℝ,
        5 ≤ T0 ∧
        0 ≤ Aregular ∧ 0 ≤ Bregular ∧
        0 ≤ Avertical ∧ 0 ≤ Bvertical ∧
        (∀ σ β t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          riemannZeta ((β : ℂ) + I * t) = 0 → β < 1 →
          0 < σ - β →
          ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
              (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
            Aregular + Bregular * Real.log (‖((σ : ℂ) + I * t)‖ + 3)) ∧
        (∀ σ t : ℝ, T0 ≤ |t| → σ ∈ Set.Icc 1 2 →
          ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
            Avertical + Bvertical * Real.log (‖((σ : ℂ) + I * t)‖ + 3))) :
    classical_zero_free_region := by
  rcases h with
    ⟨T0, Aregular, Bregular, Avertical, Bvertical, hT0,
      hAregular, hBregular, hAvertical, hBvertical, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height
      T0 Aregular Bregular Avertical Bvertical hT0 hAregular hBregular
      hAvertical hBvertical hregular hvertical

/-- Signed complex-variable high-height closure from multiplicative
full-height logarithmic bounds.

This is the `-logDeriv ζ` counterpart of
`classical_zero_free_region_of_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height`.
It is the simplest handoff when the remaining Borel/Jensen estimates are
already stated as `C * log(‖s‖ + 3)` bounds. -/
lemma classical_zero_free_region_of_neg_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height
    (T0 Cregular Cvertical : ℝ) (hT0 : 5 ≤ T0)
    (hCregular : 0 ≤ Cregular) (hCvertical : 0 ≤ Cvertical)
    (hregular :
      ∀ s ρ : ℂ, T0 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
        riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
        0 < s.re - ρ.re →
        ‖-logDeriv riemannZeta s + (s - ρ)⁻¹‖ ≤
          Cregular * Real.log (‖s‖ + 3))
    (hvertical :
      ∀ z : ℂ, T0 ≤ |z.im| → z.re ∈ Set.Icc 1 2 →
        ‖-logDeriv riemannZeta z‖ ≤
          Cvertical * Real.log (‖z‖ + 3)) :
    classical_zero_free_region := by
  refine
    classical_zero_free_region_of_neg_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height
      T0 0 Cregular 0 Cvertical hT0 (by norm_num) hCregular
      (by norm_num) hCvertical ?_ ?_
  · intro s ρ hs_height hs_re_mem hζρ hρ_im_eq hρ_re_lt hsub
    simpa using
      hregular s ρ hs_height hs_re_mem hζρ hρ_im_eq hρ_re_lt hsub
  · intro z hz_height hz_re_mem
    simpa using hvertical z hz_height hz_re_mem

/-- Existential signed complex-variable high-height closure from multiplicative
full-height logarithmic bounds. -/
lemma classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height
    (h :
      ∃ T0 Cregular Cvertical : ℝ, 5 ≤ T0 ∧
        0 ≤ Cregular ∧ 0 ≤ Cvertical ∧
        (∀ s ρ : ℂ, T0 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
          riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
          0 < s.re - ρ.re →
          ‖-logDeriv riemannZeta s + (s - ρ)⁻¹‖ ≤
            Cregular * Real.log (‖s‖ + 3)) ∧
        (∀ z : ℂ, T0 ≤ |z.im| → z.re ∈ Set.Icc 1 2 →
          ‖-logDeriv riemannZeta z‖ ≤
            Cvertical * Real.log (‖z‖ + 3))) :
    classical_zero_free_region := by
  rcases h with
    ⟨T0, Cregular, Cvertical, hT0, hCregular, hCvertical, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_neg_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height
      T0 Cregular Cvertical hT0 hCregular hCvertical hregular hvertical

/-- Signed complex-variable high-height closure from a single
full-height logarithmic constant for both remaining estimates. -/
lemma classical_zero_free_region_of_neg_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height
    (T0 C : ℝ) (hT0 : 5 ≤ T0) (hC : 0 ≤ C)
    (hregular :
      ∀ s ρ : ℂ, T0 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
        riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
        0 < s.re - ρ.re →
        ‖-logDeriv riemannZeta s + (s - ρ)⁻¹‖ ≤
          C * Real.log (‖s‖ + 3))
    (hvertical :
      ∀ z : ℂ, T0 ≤ |z.im| → z.re ∈ Set.Icc 1 2 →
        ‖-logDeriv riemannZeta z‖ ≤
          C * Real.log (‖z‖ + 3)) :
    classical_zero_free_region :=
  classical_zero_free_region_of_neg_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height
    T0 C C hT0 hC hC hregular hvertical

/-- Existential signed complex-variable high-height closure from a single
full-height logarithmic constant for both remaining estimates. -/
lemma classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height
    (h :
      ∃ T0 C : ℝ, 5 ≤ T0 ∧ 0 ≤ C ∧
        (∀ s ρ : ℂ, T0 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
          riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
          0 < s.re - ρ.re →
          ‖-logDeriv riemannZeta s + (s - ρ)⁻¹‖ ≤
            C * Real.log (‖s‖ + 3)) ∧
        (∀ z : ℂ, T0 ≤ |z.im| → z.re ∈ Set.Icc 1 2 →
          ‖-logDeriv riemannZeta z‖ ≤
            C * Real.log (‖z‖ + 3))) :
    classical_zero_free_region := by
  rcases h with ⟨T0, C, hT0, hC, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_neg_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height
      T0 C hT0 hC hregular hvertical

/-- Existential high-height closure from affine logarithmic bounds. -/
lemma classical_zero_free_region_of_exists_logDeriv_regular_part_norm_affine_log_bound_and_vertical_logDeriv_norm_affine_log_bound_high_height
    (h :
      ∃ T0 Aregular Bregular Avertical Bvertical : ℝ,
        3 ≤ T0 ∧
        0 ≤ Aregular ∧ 0 ≤ Bregular ∧
        0 ≤ Avertical ∧ 0 ≤ Bvertical ∧
        (∀ s ρ : ℂ, T0 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
          riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
          0 < s.re - ρ.re →
          ‖logDeriv riemannZeta s - (s - ρ)⁻¹‖ ≤
            Aregular + Bregular * Real.log |s.im|) ∧
        (∀ z : ℂ, T0 ≤ |z.im| → z.re ∈ Set.Icc 1 2 →
          ‖logDeriv riemannZeta z‖ ≤
            Avertical + Bvertical * Real.log |z.im|)) :
    classical_zero_free_region := by
  rcases h with
    ⟨T0, Aregular, Bregular, Avertical, Bvertical, hT0,
      hAregular, hBregular, hAvertical, hBvertical, hregular, hvertical⟩
  exact
    classical_zero_free_region_of_logDeriv_regular_part_norm_affine_log_bound_and_vertical_logDeriv_norm_affine_log_bound_high_height
      T0 Aregular Bregular Avertical Bvertical hT0 hAregular hBregular
      hAvertical hBvertical hregular hvertical

/-- ζ has a simple pole at `1`, expressed as meromorphic order `-1`. -/
lemma meromorphicOrderAt_riemannZeta_one :
    meromorphicOrderAt riemannZeta (1 : ℂ) = (-1 : ℤ) := by
  rw [meromorphicOrderAt_eq_int_iff meromorphicAt_riemannZeta_one]
  refine ⟨riemannZetaPoleUnitAtOne, analyticAt_riemannZetaPoleUnitAtOne, ?_,
    eventuallyEq_riemannZeta_simplePoleAtOne.symm⟩
  rw [riemannZetaPoleUnitAtOne_one]
  exact one_ne_zero

/-- Divisor value of ζ at its pole `1` on any meromorphic domain containing
`1`. -/
lemma divisor_riemannZeta_pole_one {U : Set ℂ}
    (hU : (1 : ℂ) ∈ U) (hζ : MeromorphicOn riemannZeta U) :
    MeromorphicOn.divisor riemannZeta U (1 : ℂ) = (-1 : ℤ) := by
  rw [MeromorphicOn.divisor_apply hζ hU, meromorphicOrderAt_riemannZeta_one]
  exact WithTop.untop₀_coe (-1 : ℤ)

/-- ζ is meromorphic on any closed ball `closedBall c R`, restricted to the
points where ζ is analytic (i.e. s ≠ 1). -/
lemma meromorphicOn_riemannZeta_closedBall_of_ne_one (c : ℂ) (R : ℝ) :
    MeromorphicOn riemannZeta (closedBall c R \ {1}) := by
  intro s hs
  -- hs : s ∈ (closedBall c R \ {1})
  rcases hs with ⟨hs_ball, hs_ne⟩
  -- s ≠ 1, so ζ is meromorphicAt s.
  exact meromorphicAt_riemannZeta_of_ne_one s hs_ne

/-- ζ is meromorphic on any closed ball. -/
lemma meromorphicOn_riemannZeta_closedBall (c : ℂ) (R : ℝ) :
    MeromorphicOn riemannZeta (closedBall c R) := by
  intro s _hs
  by_cases hs : s = 1
  · subst hs
    exact meromorphicAt_riemannZeta_one
  · exact meromorphicAt_riemannZeta_of_ne_one s hs

/-- Jensen formula specialized to ζ on a closed ball. -/
lemma jensen_circleAverage_log_norm_riemannZeta_closedBall
    {c : ℂ} {R : ℝ} (hR : R ≠ 0) :
    circleAverage (Real.log ‖riemannZeta ·‖) c R
      = ∑ᶠ u, divisor riemannZeta (closedBall c |R|) u *
          Real.log (R * ‖c - u‖⁻¹)
        + divisor riemannZeta (closedBall c |R|) c * Real.log R
        + Real.log ‖meromorphicTrailingCoeffAt riemannZeta c‖ :=
  jensen_circleAverage_log_norm hR
    (meromorphicOn_riemannZeta_closedBall c |R|)

/-- The logarithmic derivative of ζ is meromorphic at the pole `1`. -/
lemma meromorphicAt_logDeriv_riemannZeta_one :
    MeromorphicAt (logDeriv riemannZeta) (1 : ℂ) :=
  meromorphicAt_riemannZeta_one.deriv.div meromorphicAt_riemannZeta_one

/-- The signed logarithmic derivative of ζ is meromorphic at the pole `1`. -/
lemma meromorphicAt_neg_logDeriv_riemannZeta_one :
    MeromorphicAt (fun z : ℂ => -logDeriv riemannZeta z) (1 : ℂ) :=
  meromorphicAt_logDeriv_riemannZeta_one.neg

/-- The logarithmic derivative of ζ is meromorphic on every closed ball. -/
lemma meromorphicOn_logDeriv_riemannZeta_closedBall (c : ℂ) (R : ℝ) :
    MeromorphicOn (logDeriv riemannZeta) (closedBall c R) :=
  (meromorphicOn_riemannZeta_closedBall c R).logDeriv

/-- The signed logarithmic derivative of ζ is meromorphic on every closed
ball. -/
lemma meromorphicOn_neg_logDeriv_riemannZeta_closedBall (c : ℂ) (R : ℝ) :
    MeromorphicOn (fun z : ℂ => -logDeriv riemannZeta z) (closedBall c R) :=
  (meromorphicOn_logDeriv_riemannZeta_closedBall c R).neg

/-- A simple analytic zero admits the local unit factorization
`f z = (z - x) * g z` on the punctured neighborhood of the zero.

This is the local algebraic input for separating the principal part of a
logarithmic derivative near a simple zero. -/
lemma exists_eventuallyEq_sub_mul_unit_of_analyticAt_zero_deriv_ne_zero
    {f : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) (hfx : f x = 0) (hf' : deriv f x ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g x ∧ g x ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] x, f z = (z - x) * g z := by
  have horder : meromorphicOrderAt f x = (1 : WithTop ℤ) := by
    rw [hf.meromorphicOrderAt_eq,
      hf.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hfx hf']
    simp
  rcases (meromorphicOrderAt_eq_int_iff hf.meromorphicAt).1 horder with
    ⟨g, hg, hg_ne, hfg⟩
  refine ⟨g, hg, hg_ne, ?_⟩
  filter_upwards [hfg] with z hz
  simpa using hz

/-- Near a simple analytic zero, subtracting the principal logarithmic pole
leaves the logarithmic derivative of the local analytic unit.

This is the local equality behind the future estimate
`logDeriv ζ(s) - (s - ρ)⁻¹ = O(log |Im ρ|)` near a simple zero `ρ`; the
global height bound for that regular part is a separate analytic estimate. -/
lemma exists_eventuallyEq_logDeriv_sub_inv_of_analyticAt_zero_deriv_ne_zero
    {f : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) (hfx : f x = 0) (hf' : deriv f x ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g x ∧ g x ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] x, logDeriv f z - (z - x)⁻¹ = logDeriv g z := by
  rcases exists_eventuallyEq_sub_mul_unit_of_analyticAt_zero_deriv_ne_zero
      hf hfx hf' with ⟨g, hg, hg_ne, hfg⟩
  refine ⟨g, hg, hg_ne, ?_⟩
  have hfg_deriv :
      deriv f =ᶠ[𝓝[≠] x] deriv (fun z : ℂ => (z - x) * g z) :=
    Filter.EventuallyEq.nhdsNE_deriv hfg
  have hg_ne_eventually : ∀ᶠ z in 𝓝[≠] x, g z ≠ 0 :=
    (hg.continuousAt.tendsto.eventually_ne hg_ne).filter_mono
      nhdsWithin_le_nhds
  have hg_diff_eventually : ∀ᶠ z in 𝓝[≠] x, DifferentiableAt ℂ g z :=
    (hg.eventually_analyticAt.mono fun _ hz => hz.differentiableAt).filter_mono
      nhdsWithin_le_nhds
  have hz_ne : ∀ᶠ z in 𝓝[≠] x, z ≠ x :=
    self_mem_nhdsWithin
  filter_upwards [hfg, hfg_deriv, hg_ne_eventually, hg_diff_eventually, hz_ne] with
    z hfgz hderivz hgz hgdiffz hz
  have hlog_factor :
      logDeriv f z = logDeriv (fun w : ℂ => (w - x) * g w) z := by
    simp [logDeriv_apply, hderivz, hfgz]
  have hmul :
      logDeriv (fun w : ℂ => (w - x) * g w) z =
        logDeriv (fun w : ℂ => w - x) z + logDeriv g z := by
    rw [logDeriv_mul]
    · simpa using sub_ne_zero.mpr hz
    · exact hgz
    · fun_prop
    · exact hgdiffz
  have hlinear : logDeriv (fun w : ℂ => w - x) z = (z - x)⁻¹ := by
    simp [logDeriv_apply]
  rw [hlog_factor, hmul, hlinear]
  abel

/-- Signed form of the simple-zero logarithmic-derivative decomposition.  This
is the sign convention used by the de la Vallée Poussin `-ζ'/ζ` estimates. -/
lemma exists_eventuallyEq_neg_logDeriv_add_inv_of_analyticAt_zero_deriv_ne_zero
    {f : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) (hfx : f x = 0) (hf' : deriv f x ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g x ∧ g x ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] x, -logDeriv f z + (z - x)⁻¹ = -logDeriv g z := by
  rcases exists_eventuallyEq_logDeriv_sub_inv_of_analyticAt_zero_deriv_ne_zero
      hf hfx hf' with ⟨g, hg, hg_ne, hfg⟩
  refine ⟨g, hg, hg_ne, ?_⟩
  filter_upwards [hfg] with z hz
  rw [← hz]
  abel

/-- Zeta-specific simple-zero principal-part separation for `logDeriv ζ`.

The hypotheses intentionally include the simple-zero condition
`deriv riemannZeta ρ ≠ 0`; multiple zeros require the corresponding
multiplicity-weighted principal part and are not claimed here. -/
lemma exists_eventuallyEq_logDeriv_riemannZeta_sub_inv_of_simple_zero
    {ρ : ℂ} (hρ1 : ρ ≠ 1) (hzero : riemannZeta ρ = 0)
    (hsimple : deriv riemannZeta ρ ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] ρ,
        logDeriv riemannZeta z - (z - ρ)⁻¹ = logDeriv g z :=
  exists_eventuallyEq_logDeriv_sub_inv_of_analyticAt_zero_deriv_ne_zero
    (analyticOnNhd_riemannZeta_ne_one ρ hρ1) hzero hsimple

/-- Signed zeta-specific simple-zero principal-part separation, matching the
`-ζ'/ζ + (s-ρ)⁻¹` regular-part shape used by the zero-free-region bridge. -/
lemma exists_eventuallyEq_neg_logDeriv_riemannZeta_add_inv_of_simple_zero
    {ρ : ℂ} (hρ1 : ρ ≠ 1) (hzero : riemannZeta ρ = 0)
    (hsimple : deriv riemannZeta ρ ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] ρ,
        -logDeriv riemannZeta z + (z - ρ)⁻¹ = -logDeriv g z :=
  exists_eventuallyEq_neg_logDeriv_add_inv_of_analyticAt_zero_deriv_ne_zero
    (analyticOnNhd_riemannZeta_ne_one ρ hρ1) hzero hsimple

/-- Local logarithmic-derivative principal-part separation at an analytic point
of finite natural order `n`.

For a zero of multiplicity `n`, this is the multiplicity-weighted form
`logDeriv f z - n/(z-x) = logDeriv g z`.  It also covers the nonzero case
`n = 0`, where the principal part vanishes. -/
lemma exists_eventuallyEq_logDeriv_sub_order_mul_inv_of_analyticAt_order_eq_nat
    {f : ℂ → ℂ} {x : ℂ} {n : ℕ}
    (hf : AnalyticAt ℂ f x) (horder : analyticOrderAt f x = n) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g x ∧ g x ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] x,
        logDeriv f z - (n : ℂ) * (z - x)⁻¹ = logDeriv g z := by
  have hmer : meromorphicOrderAt f x = ((n : ℤ) : WithTop ℤ) := by
    rw [hf.meromorphicOrderAt_eq, horder]
    simp
  rcases (meromorphicOrderAt_eq_int_iff hf.meromorphicAt).1 hmer with
    ⟨g, hg, hg_ne, hfg⟩
  refine ⟨g, hg, hg_ne, ?_⟩
  have hfg' : ∀ᶠ z in 𝓝[≠] x, f z = (z - x) ^ n * g z := by
    filter_upwards [hfg] with z hz
    simpa [zpow_natCast] using hz
  have hfg_deriv :
      deriv f =ᶠ[𝓝[≠] x] deriv (fun z : ℂ => (z - x) ^ n * g z) :=
    Filter.EventuallyEq.nhdsNE_deriv hfg'
  have hg_ne_eventually : ∀ᶠ z in 𝓝[≠] x, g z ≠ 0 :=
    (hg.continuousAt.tendsto.eventually_ne hg_ne).filter_mono
      nhdsWithin_le_nhds
  have hg_diff_eventually : ∀ᶠ z in 𝓝[≠] x, DifferentiableAt ℂ g z :=
    (hg.eventually_analyticAt.mono fun _ hz => hz.differentiableAt).filter_mono
      nhdsWithin_le_nhds
  have hz_ne : ∀ᶠ z in 𝓝[≠] x, z ≠ x :=
    self_mem_nhdsWithin
  filter_upwards [hfg', hfg_deriv, hg_ne_eventually, hg_diff_eventually, hz_ne] with
    z hfgz hderivz hgz hgdiffz hz
  have hpow_ne : (z - x) ^ n ≠ 0 :=
    pow_ne_zero _ (sub_ne_zero.mpr hz)
  have hlog_factor :
      logDeriv f z = logDeriv (fun w : ℂ => (w - x) ^ n * g w) z := by
    simp [logDeriv_apply, hderivz, hfgz]
  have hmul :
      logDeriv (fun w : ℂ => (w - x) ^ n * g w) z =
        logDeriv (fun w : ℂ => (w - x) ^ n) z + logDeriv g z := by
    rw [logDeriv_mul]
    · exact hpow_ne
    · exact hgz
    · fun_prop
    · exact hgdiffz
  have hpow :
      logDeriv (fun w : ℂ => (w - x) ^ n) z =
        (n : ℂ) * (z - x)⁻¹ := by
    rw [logDeriv_fun_pow]
    · simp [logDeriv_apply]
    · fun_prop
  rw [hlog_factor, hmul, hpow]
  abel

/-- Signed multiplicity-weighted principal-part separation. -/
lemma exists_eventuallyEq_neg_logDeriv_add_order_mul_inv_of_analyticAt_order_eq_nat
    {f : ℂ → ℂ} {x : ℂ} {n : ℕ}
    (hf : AnalyticAt ℂ f x) (horder : analyticOrderAt f x = n) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g x ∧ g x ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] x,
        -logDeriv f z + (n : ℂ) * (z - x)⁻¹ = -logDeriv g z := by
  rcases exists_eventuallyEq_logDeriv_sub_order_mul_inv_of_analyticAt_order_eq_nat
      hf horder with ⟨g, hg, hg_ne, hfg⟩
  refine ⟨g, hg, hg_ne, ?_⟩
  filter_upwards [hfg] with z hz
  rw [← hz]
  abel

/-- Zeta-specific multiplicity-weighted principal-part separation for
`logDeriv ζ` at any finite-order point away from the pole. -/
lemma exists_eventuallyEq_logDeriv_riemannZeta_sub_order_mul_inv_of_order_eq_nat
    {ρ : ℂ} {n : ℕ} (hρ1 : ρ ≠ 1)
    (horder : analyticOrderAt riemannZeta ρ = n) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] ρ,
        logDeriv riemannZeta z - (n : ℂ) * (z - ρ)⁻¹ = logDeriv g z :=
  exists_eventuallyEq_logDeriv_sub_order_mul_inv_of_analyticAt_order_eq_nat
    (analyticOnNhd_riemannZeta_ne_one ρ hρ1) horder

/-- Signed zeta-specific multiplicity-weighted principal-part separation,
matching `-ζ'/ζ + n/(s-ρ)`. -/
lemma exists_eventuallyEq_neg_logDeriv_riemannZeta_add_order_mul_inv_of_order_eq_nat
    {ρ : ℂ} {n : ℕ} (hρ1 : ρ ≠ 1)
    (horder : analyticOrderAt riemannZeta ρ = n) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] ρ,
        -logDeriv riemannZeta z + (n : ℂ) * (z - ρ)⁻¹ = -logDeriv g z :=
  exists_eventuallyEq_neg_logDeriv_add_order_mul_inv_of_analyticAt_order_eq_nat
    (analyticOnNhd_riemannZeta_ne_one ρ hρ1) horder

/-- Convert an eventually-equal regular part for `logDeriv f` into an explicit
punctured-ball norm bound.

The analytic work is isolated in the two hypotheses: `hsep` separates the
multiplicity-weighted principal part on a punctured neighborhood, and `hbound`
bounds the remaining regular part there. -/
lemma exists_punctured_ball_norm_logDeriv_sub_order_mul_inv_le_of_eventuallyEq
    {f regular : ℂ → ℂ} {x : ℂ} {n : ℕ} {M : ℝ}
    (hsep : ∀ᶠ z in 𝓝[≠] x,
      logDeriv f z - (n : ℂ) * (z - x)⁻¹ = regular z)
    (hbound : ∀ᶠ z in 𝓝[≠] x, ‖regular z‖ ≤ M) :
    ∃ r > 0, ∀ z : ℂ, z ≠ x → dist z x < r →
      ‖logDeriv f z - (n : ℂ) * (z - x)⁻¹‖ ≤ M := by
  have hmem :
      {z : ℂ | ‖logDeriv f z - (n : ℂ) * (z - x)⁻¹‖ ≤ M} ∈ 𝓝[{x}ᶜ] x := by
    filter_upwards [hsep, hbound] with z hsepz hboundz
    simpa [hsepz] using hboundz
  rcases Metric.mem_nhdsWithin_iff.mp hmem with ⟨r, hr_pos, hr_sub⟩
  refine ⟨r, hr_pos, ?_⟩
  intro z hz_ne hz_dist
  exact hr_sub ⟨by simpa [Metric.mem_ball] using hz_dist,
    Set.mem_compl_singleton_iff.mpr hz_ne⟩

/-- Closed punctured-ball version of
`exists_punctured_ball_norm_logDeriv_sub_order_mul_inv_le_of_eventuallyEq`. -/
lemma exists_punctured_closedBall_norm_logDeriv_sub_order_mul_inv_le_of_eventuallyEq
    {f regular : ℂ → ℂ} {x : ℂ} {n : ℕ} {M : ℝ}
    (hsep : ∀ᶠ z in 𝓝[≠] x,
      logDeriv f z - (n : ℂ) * (z - x)⁻¹ = regular z)
    (hbound : ∀ᶠ z in 𝓝[≠] x, ‖regular z‖ ≤ M) :
    ∃ r > 0, ∀ z : ℂ, z ≠ x → dist z x ≤ r →
      ‖logDeriv f z - (n : ℂ) * (z - x)⁻¹‖ ≤ M := by
  rcases exists_punctured_ball_norm_logDeriv_sub_order_mul_inv_le_of_eventuallyEq
      hsep hbound with ⟨r, hr_pos, hball⟩
  refine ⟨r / 2, half_pos hr_pos, ?_⟩
  intro z hz_ne hz_dist
  exact hball z hz_ne (lt_of_le_of_lt hz_dist (half_lt_self hr_pos))

/-- Signed version of
`exists_punctured_ball_norm_logDeriv_sub_order_mul_inv_le_of_eventuallyEq`,
for the `-logDeriv f + n/(z-x)` convention. -/
lemma exists_punctured_ball_norm_neg_logDeriv_add_order_mul_inv_le_of_eventuallyEq
    {f regular : ℂ → ℂ} {x : ℂ} {n : ℕ} {M : ℝ}
    (hsep : ∀ᶠ z in 𝓝[≠] x,
      -logDeriv f z + (n : ℂ) * (z - x)⁻¹ = regular z)
    (hbound : ∀ᶠ z in 𝓝[≠] x, ‖regular z‖ ≤ M) :
    ∃ r > 0, ∀ z : ℂ, z ≠ x → dist z x < r →
      ‖-logDeriv f z + (n : ℂ) * (z - x)⁻¹‖ ≤ M := by
  have hmem :
      {z : ℂ | ‖-logDeriv f z + (n : ℂ) * (z - x)⁻¹‖ ≤ M} ∈ 𝓝[{x}ᶜ] x := by
    filter_upwards [hsep, hbound] with z hsepz hboundz
    simpa [hsepz] using hboundz
  rcases Metric.mem_nhdsWithin_iff.mp hmem with ⟨r, hr_pos, hr_sub⟩
  refine ⟨r, hr_pos, ?_⟩
  intro z hz_ne hz_dist
  exact hr_sub ⟨by simpa [Metric.mem_ball] using hz_dist,
    Set.mem_compl_singleton_iff.mpr hz_ne⟩

/-- Closed punctured-ball signed regular-part norm bridge. -/
lemma exists_punctured_closedBall_norm_neg_logDeriv_add_order_mul_inv_le_of_eventuallyEq
    {f regular : ℂ → ℂ} {x : ℂ} {n : ℕ} {M : ℝ}
    (hsep : ∀ᶠ z in 𝓝[≠] x,
      -logDeriv f z + (n : ℂ) * (z - x)⁻¹ = regular z)
    (hbound : ∀ᶠ z in 𝓝[≠] x, ‖regular z‖ ≤ M) :
    ∃ r > 0, ∀ z : ℂ, z ≠ x → dist z x ≤ r →
      ‖-logDeriv f z + (n : ℂ) * (z - x)⁻¹‖ ≤ M := by
  rcases exists_punctured_ball_norm_neg_logDeriv_add_order_mul_inv_le_of_eventuallyEq
      hsep hbound with ⟨r, hr_pos, hball⟩
  refine ⟨r / 2, half_pos hr_pos, ?_⟩
  intro z hz_ne hz_dist
  exact hball z hz_ne (lt_of_le_of_lt hz_dist (half_lt_self hr_pos))

/-- Combine `analyticOrderAt f x = n` with an eventual bound on the logarithmic
derivative of the local analytic unit, producing an explicit punctured-ball
bound for `logDeriv f - n/(z-x)`. -/
lemma exists_punctured_ball_norm_logDeriv_sub_order_mul_inv_le_of_analyticAt_order_eq_nat
    {f : ℂ → ℂ} {x : ℂ} {n : ℕ} {M : ℝ}
    (hf : AnalyticAt ℂ f x) (horder : analyticOrderAt f x = n)
    (hregularBound :
      ∀ g : ℂ → ℂ, AnalyticAt ℂ g x → g x ≠ 0 →
        ∀ᶠ z in 𝓝[≠] x, ‖logDeriv g z‖ ≤ M) :
    ∃ r > 0, ∀ z : ℂ, z ≠ x → dist z x < r →
      ‖logDeriv f z - (n : ℂ) * (z - x)⁻¹‖ ≤ M := by
  rcases exists_eventuallyEq_logDeriv_sub_order_mul_inv_of_analyticAt_order_eq_nat
      hf horder with ⟨g, hg, hg_ne, hsep⟩
  exact exists_punctured_ball_norm_logDeriv_sub_order_mul_inv_le_of_eventuallyEq
    hsep (hregularBound g hg hg_ne)

/-- Closed-ball version of
`exists_punctured_ball_norm_logDeriv_sub_order_mul_inv_le_of_analyticAt_order_eq_nat`. -/
lemma exists_punctured_closedBall_norm_logDeriv_sub_order_mul_inv_le_of_analyticAt_order_eq_nat
    {f : ℂ → ℂ} {x : ℂ} {n : ℕ} {M : ℝ}
    (hf : AnalyticAt ℂ f x) (horder : analyticOrderAt f x = n)
    (hregularBound :
      ∀ g : ℂ → ℂ, AnalyticAt ℂ g x → g x ≠ 0 →
        ∀ᶠ z in 𝓝[≠] x, ‖logDeriv g z‖ ≤ M) :
    ∃ r > 0, ∀ z : ℂ, z ≠ x → dist z x ≤ r →
      ‖logDeriv f z - (n : ℂ) * (z - x)⁻¹‖ ≤ M := by
  rcases exists_eventuallyEq_logDeriv_sub_order_mul_inv_of_analyticAt_order_eq_nat
      hf horder with ⟨g, hg, hg_ne, hsep⟩
  exact exists_punctured_closedBall_norm_logDeriv_sub_order_mul_inv_le_of_eventuallyEq
    hsep (hregularBound g hg hg_ne)

/-- Signed version of
`exists_punctured_ball_norm_logDeriv_sub_order_mul_inv_le_of_analyticAt_order_eq_nat`. -/
lemma exists_punctured_ball_norm_neg_logDeriv_add_order_mul_inv_le_of_analyticAt_order_eq_nat
    {f : ℂ → ℂ} {x : ℂ} {n : ℕ} {M : ℝ}
    (hf : AnalyticAt ℂ f x) (horder : analyticOrderAt f x = n)
    (hregularBound :
      ∀ g : ℂ → ℂ, AnalyticAt ℂ g x → g x ≠ 0 →
        ∀ᶠ z in 𝓝[≠] x, ‖-logDeriv g z‖ ≤ M) :
    ∃ r > 0, ∀ z : ℂ, z ≠ x → dist z x < r →
      ‖-logDeriv f z + (n : ℂ) * (z - x)⁻¹‖ ≤ M := by
  rcases exists_eventuallyEq_neg_logDeriv_add_order_mul_inv_of_analyticAt_order_eq_nat
      hf horder with ⟨g, hg, hg_ne, hsep⟩
  exact exists_punctured_ball_norm_neg_logDeriv_add_order_mul_inv_le_of_eventuallyEq
    hsep (hregularBound g hg hg_ne)

/-- Closed-ball signed version of
`exists_punctured_ball_norm_neg_logDeriv_add_order_mul_inv_le_of_analyticAt_order_eq_nat`. -/
lemma exists_punctured_closedBall_norm_neg_logDeriv_add_order_mul_inv_le_of_analyticAt_order_eq_nat
    {f : ℂ → ℂ} {x : ℂ} {n : ℕ} {M : ℝ}
    (hf : AnalyticAt ℂ f x) (horder : analyticOrderAt f x = n)
    (hregularBound :
      ∀ g : ℂ → ℂ, AnalyticAt ℂ g x → g x ≠ 0 →
        ∀ᶠ z in 𝓝[≠] x, ‖-logDeriv g z‖ ≤ M) :
    ∃ r > 0, ∀ z : ℂ, z ≠ x → dist z x ≤ r →
      ‖-logDeriv f z + (n : ℂ) * (z - x)⁻¹‖ ≤ M := by
  rcases exists_eventuallyEq_neg_logDeriv_add_order_mul_inv_of_analyticAt_order_eq_nat
      hf horder with ⟨g, hg, hg_ne, hsep⟩
  exact exists_punctured_closedBall_norm_neg_logDeriv_add_order_mul_inv_le_of_eventuallyEq
    hsep (hregularBound g hg hg_ne)

/-- Zeta-specific version of
`exists_punctured_ball_norm_logDeriv_sub_order_mul_inv_le_of_analyticAt_order_eq_nat`. -/
lemma exists_punctured_ball_norm_logDeriv_riemannZeta_sub_order_mul_inv_le_of_order_eq_nat
    {ρ : ℂ} {n : ℕ} {M : ℝ} (hρ1 : ρ ≠ 1)
    (horder : analyticOrderAt riemannZeta ρ = n)
    (hregularBound :
      ∀ g : ℂ → ℂ, AnalyticAt ℂ g ρ → g ρ ≠ 0 →
        ∀ᶠ z in 𝓝[≠] ρ, ‖logDeriv g z‖ ≤ M) :
    ∃ r > 0, ∀ z : ℂ, z ≠ ρ → dist z ρ < r →
      ‖logDeriv riemannZeta z - (n : ℂ) * (z - ρ)⁻¹‖ ≤ M :=
  exists_punctured_ball_norm_logDeriv_sub_order_mul_inv_le_of_analyticAt_order_eq_nat
    (f := riemannZeta) (x := ρ) (n := n) (M := M)
    (analyticOnNhd_riemannZeta_ne_one ρ hρ1) horder hregularBound

/-- Closed-ball zeta-specific regular-part norm bridge. -/
lemma exists_punctured_closedBall_norm_logDeriv_riemannZeta_sub_order_mul_inv_le_of_order_eq_nat
    {ρ : ℂ} {n : ℕ} {M : ℝ} (hρ1 : ρ ≠ 1)
    (horder : analyticOrderAt riemannZeta ρ = n)
    (hregularBound :
      ∀ g : ℂ → ℂ, AnalyticAt ℂ g ρ → g ρ ≠ 0 →
        ∀ᶠ z in 𝓝[≠] ρ, ‖logDeriv g z‖ ≤ M) :
    ∃ r > 0, ∀ z : ℂ, z ≠ ρ → dist z ρ ≤ r →
      ‖logDeriv riemannZeta z - (n : ℂ) * (z - ρ)⁻¹‖ ≤ M :=
  exists_punctured_closedBall_norm_logDeriv_sub_order_mul_inv_le_of_analyticAt_order_eq_nat
    (f := riemannZeta) (x := ρ) (n := n) (M := M)
    (analyticOnNhd_riemannZeta_ne_one ρ hρ1) horder hregularBound

/-- Signed zeta-specific regular-part norm bridge. -/
lemma exists_punctured_ball_norm_neg_logDeriv_riemannZeta_add_order_mul_inv_le_of_order_eq_nat
    {ρ : ℂ} {n : ℕ} {M : ℝ} (hρ1 : ρ ≠ 1)
    (horder : analyticOrderAt riemannZeta ρ = n)
    (hregularBound :
      ∀ g : ℂ → ℂ, AnalyticAt ℂ g ρ → g ρ ≠ 0 →
        ∀ᶠ z in 𝓝[≠] ρ, ‖-logDeriv g z‖ ≤ M) :
    ∃ r > 0, ∀ z : ℂ, z ≠ ρ → dist z ρ < r →
      ‖-logDeriv riemannZeta z + (n : ℂ) * (z - ρ)⁻¹‖ ≤ M :=
  exists_punctured_ball_norm_neg_logDeriv_add_order_mul_inv_le_of_analyticAt_order_eq_nat
    (f := riemannZeta) (x := ρ) (n := n) (M := M)
    (analyticOnNhd_riemannZeta_ne_one ρ hρ1) horder hregularBound

/-- Closed-ball signed zeta-specific regular-part norm bridge. -/
lemma exists_punctured_closedBall_norm_neg_logDeriv_riemannZeta_add_order_mul_inv_le_of_order_eq_nat
    {ρ : ℂ} {n : ℕ} {M : ℝ} (hρ1 : ρ ≠ 1)
    (horder : analyticOrderAt riemannZeta ρ = n)
    (hregularBound :
      ∀ g : ℂ → ℂ, AnalyticAt ℂ g ρ → g ρ ≠ 0 →
        ∀ᶠ z in 𝓝[≠] ρ, ‖-logDeriv g z‖ ≤ M) :
    ∃ r > 0, ∀ z : ℂ, z ≠ ρ → dist z ρ ≤ r →
      ‖-logDeriv riemannZeta z + (n : ℂ) * (z - ρ)⁻¹‖ ≤ M :=
  exists_punctured_closedBall_norm_neg_logDeriv_add_order_mul_inv_le_of_analyticAt_order_eq_nat
    (f := riemannZeta) (x := ρ) (n := n) (M := M)
    (analyticOnNhd_riemannZeta_ne_one ρ hρ1) horder hregularBound

/-- If `f` is analytic and nonzero at `z`, then its logarithmic derivative is
analytic at `z`. -/
lemma analyticAt_logDeriv_of_analyticAt_ne_zero {f : ℂ → ℂ} {z : ℂ}
    (han : AnalyticAt ℂ f z) (hne : f z ≠ 0) :
    AnalyticAt ℂ (logDeriv f) z :=
  han.deriv.div han hne

/-- Zeta-specific wrapper for analyticity of the logarithmic derivative from
analyticity and nonvanishing of ζ. -/
lemma analyticAt_logDeriv_riemannZeta_of_analyticAt_ne_zero {z : ℂ}
    (han : AnalyticAt ℂ riemannZeta z) (hne : riemannZeta z ≠ 0) :
    AnalyticAt ℂ (logDeriv riemannZeta) z :=
  analyticAt_logDeriv_of_analyticAt_ne_zero han hne

/-- Away from the pole, if ζ is nonzero at `z`, then `logDeriv ζ` is analytic
at `z`. -/
lemma analyticAt_logDeriv_riemannZeta_of_ne_one_of_ne_zero
    (z : ℂ) (hz1 : z ≠ 1) (hne : riemannZeta z ≠ 0) :
    AnalyticAt ℂ (logDeriv riemannZeta) z :=
  analyticAt_logDeriv_riemannZeta_of_analyticAt_ne_zero
    (analyticOnNhd_riemannZeta_ne_one z hz1) hne

/-- On the closed right half-plane, away from the pole, `logDeriv ζ` is
analytic; zeta nonvanishing is supplied by Mathlib's boundary nonvanishing
theorem. -/
lemma analyticAt_logDeriv_riemannZeta_of_one_le_re_of_ne_one
    {z : ℂ} (hre : 1 ≤ z.re) (hz1 : z ≠ 1) :
    AnalyticAt ℂ (logDeriv riemannZeta) z :=
  analyticAt_logDeriv_riemannZeta_of_ne_one_of_ne_zero z hz1
    (riemannZeta_ne_zero_of_one_le_re hre)

/-- Pointwise closed-ball wrapper: if ζ is analytic and nonzero at every point
of the ball, then `logDeriv ζ` is analytic at every point of the ball. -/
lemma analyticAt_logDeriv_riemannZeta_closedBall_of_ne_one_of_ne_zero
    (c : ℂ) (R : ℝ)
    (h1 : ∀ u ∈ closedBall c R, u ≠ 1)
    (hne : ∀ u ∈ closedBall c R, riemannZeta u ≠ 0) :
    ∀ u ∈ closedBall c R, AnalyticAt ℂ (logDeriv riemannZeta) u := by
  intro u hu
  exact analyticAt_logDeriv_riemannZeta_of_ne_one_of_ne_zero u
    (h1 u hu) (hne u hu)

/-- Pointwise closed-ball wrapper on the right half-plane: if every point in
the ball has real part at least `1` and avoids the pole, then `logDeriv ζ` is
analytic at every point of the ball. -/
lemma analyticAt_logDeriv_riemannZeta_closedBall_of_one_le_re_of_ne_one
    (c : ℂ) (R : ℝ)
    (hre : ∀ u ∈ closedBall c R, 1 ≤ u.re)
    (h1 : ∀ u ∈ closedBall c R, u ≠ 1) :
    ∀ u ∈ closedBall c R, AnalyticAt ℂ (logDeriv riemannZeta) u := by
  intro u hu
  exact analyticAt_logDeriv_riemannZeta_of_one_le_re_of_ne_one
    (hre u hu) (h1 u hu)

/-- Disk-geometric analyticity wrapper for `logDeriv ζ` on a closed disk
centered at `σ + I*t`.  The numeric hypotheses put the disk in `Re >= 1`
and keep it a positive height away from the pole. -/
lemma analyticAt_logDeriv_riemannZeta_closedBall_sigma_it_of_disk_right_half
    {σ t R H : ℝ}
    (hσ : 1 + R ≤ σ) (hHpos : 0 < H) (hH : H + R ≤ |t|) :
    ∀ u ∈ closedBall ((σ : ℂ) + I * t) R,
      AnalyticAt ℂ (logDeriv riemannZeta) u :=
  analyticAt_logDeriv_riemannZeta_closedBall_of_one_le_re_of_ne_one
    ((σ : ℂ) + I * t) R
    (fun u hu =>
      closedBall_sigma_it_one_le_re_of_add_le
        (z := u) (σ := σ) (t := t) (R := R) hu hσ)
    (fun u hu =>
      closedBall_sigma_it_ne_one_of_height_add_le
        (z := u) (σ := σ) (t := t) (R := R) (H := H) hu hHpos hH)

/-- Differentiability of `logDeriv ζ` on a closed `σ + I*t` disk in the
right half-plane and away from the pole. -/
lemma differentiableOn_logDeriv_riemannZeta_closedBall_sigma_it_of_disk_right_half
    {σ t R H : ℝ}
    (hσ : 1 + R ≤ σ) (hHpos : 0 < H) (hH : H + R ≤ |t|) :
    DifferentiableOn ℂ (logDeriv riemannZeta)
      (closedBall ((σ : ℂ) + I * t) R) := by
  intro u hu
  exact (analyticAt_logDeriv_riemannZeta_closedBall_sigma_it_of_disk_right_half
    hσ hHpos hH u hu).differentiableWithinAt

/-- Signed differentiability of `-logDeriv ζ` on a closed `σ + I*t` disk in
the right half-plane and away from the pole. -/
lemma differentiableOn_neg_logDeriv_riemannZeta_closedBall_sigma_it_of_disk_right_half
    {σ t R H : ℝ}
    (hσ : 1 + R ≤ σ) (hHpos : 0 < H) (hH : H + R ≤ |t|) :
    DifferentiableOn ℂ (fun z : ℂ => -logDeriv riemannZeta z)
      (closedBall ((σ : ℂ) + I * t) R) := by
  simpa only [Pi.neg_apply] using
    (differentiableOn_logDeriv_riemannZeta_closedBall_sigma_it_of_disk_right_half
      (σ := σ) (t := t) (R := R) (H := H) hσ hHpos hH).neg

/-- Differentiability of the zero-centered translate
`z ↦ logDeriv ζ (z + (σ + I*t))` on the local open disk used by centered
Borel-Caratheodory wrappers. -/
lemma differentiableOn_logDeriv_riemannZeta_comp_add_sigma_it_ball_of_disk_right_half
    {σ t R H : ℝ}
    (hσ : 1 + R ≤ σ) (hHpos : 0 < H) (hH : H + R ≤ |t|) :
    DifferentiableOn ℂ
      (fun z : ℂ => logDeriv riemannZeta (z + ((σ : ℂ) + I * t)))
      (ball 0 R) := by
  intro z hz
  let c : ℂ := (σ : ℂ) + I * t
  have hzc : z + c ∈ closedBall c R := by
    simpa [c, Metric.mem_closedBall, dist_eq_norm, add_comm, add_left_comm,
      add_assoc] using Metric.ball_subset_closedBall hz
  exact
    ((analyticAt_logDeriv_riemannZeta_closedBall_sigma_it_of_disk_right_half
      (σ := σ) (t := t) (R := R) (H := H) hσ hHpos hH
      (z + c) hzc).differentiableAt.comp z
        (differentiableAt_id.add (differentiableAt_const c))).differentiableWithinAt

/-- Signed translated differentiability wrapper for the centered local disk. -/
lemma differentiableOn_neg_logDeriv_riemannZeta_comp_add_sigma_it_ball_of_disk_right_half
    {σ t R H : ℝ}
    (hσ : 1 + R ≤ σ) (hHpos : 0 < H) (hH : H + R ≤ |t|) :
    DifferentiableOn ℂ
      (fun z : ℂ => -logDeriv riemannZeta (z + ((σ : ℂ) + I * t)))
      (ball 0 R) := by
  simpa only [Pi.neg_apply] using
    (differentiableOn_logDeriv_riemannZeta_comp_add_sigma_it_ball_of_disk_right_half
      (σ := σ) (t := t) (R := R) (H := H) hσ hHpos hH).neg

/-- Direct Borel-Carathéodory wrapper for `logDeriv ζ` on a `σ + I*t` disk
whose geometry places it in the right half-plane and away from the pole.  The
only analytic input left is the real-part bound on that local disk. -/
lemma borelCaratheodory_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le
    {M R σ t H : ℝ} {z : ℂ}
    (hM : 0 < M) (hσ : 1 + R ≤ σ) (hHpos : 0 < H) (hH : H + R ≤ |t|)
    (hlog : ∀ w : ℂ, w ∈ ball ((σ : ℂ) + I * t) R →
      (logDeriv riemannZeta w).re ≤ M)
    (hR : 0 < R) (hz : z ∈ ball ((σ : ℂ) + I * t) R) :
    ‖logDeriv riemannZeta z‖ ≤
      2 * M * ‖z - ((σ : ℂ) + I * t)‖ /
          (R - ‖z - ((σ : ℂ) + I * t)‖) +
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ *
          (R + ‖z - ((σ : ℂ) + I * t)‖) /
          (R - ‖z - ((σ : ℂ) + I * t)‖) := by
  have hdiff : DifferentiableOn ℂ (logDeriv riemannZeta)
      (ball ((σ : ℂ) + I * t) R) := by
    exact (differentiableOn_logDeriv_riemannZeta_closedBall_sigma_it_of_disk_right_half
      (σ := σ) (t := t) (R := R) (H := H) hσ hHpos hH).mono
        Metric.ball_subset_closedBall
  have hmaps : Set.MapsTo (logDeriv riemannZeta)
      (ball ((σ : ℂ) + I * t) R) {w | w.re ≤ M} := by
    intro w hw
    exact hlog w hw
  exact borelCaratheodory_centered hM hdiff hmaps hR hz

/-- Direct oscillation Borel-Carathéodory wrapper for `logDeriv ζ` on a
`σ + I*t` disk with right-half-plane geometry. -/
lemma borelCaratheodory_sub_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le
    {M R σ t H : ℝ} {z : ℂ}
    (hM : 0 < M) (hσ : 1 + R ≤ σ) (hHpos : 0 < H) (hH : H + R ≤ |t|)
    (hlog : ∀ w : ℂ, w ∈ ball ((σ : ℂ) + I * t) R →
      (logDeriv riemannZeta w -
        logDeriv riemannZeta ((σ : ℂ) + I * t)).re ≤ M)
    (hR : 0 < R) (hz : z ∈ ball ((σ : ℂ) + I * t) R) :
    ‖logDeriv riemannZeta z -
        logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
      2 * M * ‖z - ((σ : ℂ) + I * t)‖ /
        (R - ‖z - ((σ : ℂ) + I * t)‖) := by
  have hdiff : DifferentiableOn ℂ (logDeriv riemannZeta)
      (ball ((σ : ℂ) + I * t) R) := by
    exact (differentiableOn_logDeriv_riemannZeta_closedBall_sigma_it_of_disk_right_half
      (σ := σ) (t := t) (R := R) (H := H) hσ hHpos hH).mono
        Metric.ball_subset_closedBall
  have hmaps : Set.MapsTo
      (fun w => logDeriv riemannZeta w -
        logDeriv riemannZeta ((σ : ℂ) + I * t))
      (ball ((σ : ℂ) + I * t) R) {w | w.re ≤ M} := by
    intro w hw
    exact hlog w hw
  exact borelCaratheodory_sub_centered hM hdiff hmaps hR hz

/-- Direct Borel-Carathéodory wrapper for `-logDeriv ζ` on a `σ + I*t` disk
whose geometry places it in the right half-plane and away from the pole. -/
lemma borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le
    {M R σ t H : ℝ} {z : ℂ}
    (hM : 0 < M) (hσ : 1 + R ≤ σ) (hHpos : 0 < H) (hH : H + R ≤ |t|)
    (hlog : ∀ w : ℂ, w ∈ ball ((σ : ℂ) + I * t) R →
      (-logDeriv riemannZeta w).re ≤ M)
    (hR : 0 < R) (hz : z ∈ ball ((σ : ℂ) + I * t) R) :
    ‖-logDeriv riemannZeta z‖ ≤
      2 * M * ‖z - ((σ : ℂ) + I * t)‖ /
          (R - ‖z - ((σ : ℂ) + I * t)‖) +
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ *
          (R + ‖z - ((σ : ℂ) + I * t)‖) /
          (R - ‖z - ((σ : ℂ) + I * t)‖) := by
  have hdiff : DifferentiableOn ℂ (fun w : ℂ => -logDeriv riemannZeta w)
      (ball ((σ : ℂ) + I * t) R) := by
    exact (differentiableOn_neg_logDeriv_riemannZeta_closedBall_sigma_it_of_disk_right_half
      (σ := σ) (t := t) (R := R) (H := H) hσ hHpos hH).mono
        Metric.ball_subset_closedBall
  have hmaps : Set.MapsTo (fun w : ℂ => -logDeriv riemannZeta w)
      (ball ((σ : ℂ) + I * t) R) {w | w.re ≤ M} := by
    intro w hw
    exact hlog w hw
  exact borelCaratheodory_centered hM hdiff hmaps hR hz

/-- Direct oscillation Borel-Carathéodory wrapper for `-logDeriv ζ` on a
`σ + I*t` disk with right-half-plane geometry. -/
lemma borelCaratheodory_sub_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le
    {M R σ t H : ℝ} {z : ℂ}
    (hM : 0 < M) (hσ : 1 + R ≤ σ) (hHpos : 0 < H) (hH : H + R ≤ |t|)
    (hlog : ∀ w : ℂ, w ∈ ball ((σ : ℂ) + I * t) R →
      (-logDeriv riemannZeta w -
        -logDeriv riemannZeta ((σ : ℂ) + I * t)).re ≤ M)
    (hR : 0 < R) (hz : z ∈ ball ((σ : ℂ) + I * t) R) :
    ‖-logDeriv riemannZeta z -
        -logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
      2 * M * ‖z - ((σ : ℂ) + I * t)‖ /
        (R - ‖z - ((σ : ℂ) + I * t)‖) := by
  have hdiff : DifferentiableOn ℂ (fun w : ℂ => -logDeriv riemannZeta w)
      (ball ((σ : ℂ) + I * t) R) := by
    exact (differentiableOn_neg_logDeriv_riemannZeta_closedBall_sigma_it_of_disk_right_half
      (σ := σ) (t := t) (R := R) (H := H) hσ hHpos hH).mono
        Metric.ball_subset_closedBall
  have hmaps : Set.MapsTo
      (fun w : ℂ => -logDeriv riemannZeta w -
        -logDeriv riemannZeta ((σ : ℂ) + I * t))
      (ball ((σ : ℂ) + I * t) R) {w | w.re ≤ M} := by
    intro w hw
    exact hlog w hw
  exact borelCaratheodory_sub_centered hM hdiff hmaps hR hz

/-- Direct half-radius Borel-Carathéodory bound for `logDeriv ζ` on a
`σ + I*t` disk whose numeric geometry places it in the right half-plane and
away from the pole. -/
lemma borelCaratheodory_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le_half_radius
    {M R σ t H : ℝ} {z : ℂ}
    (hM : 0 < M) (hσ : 1 + R ≤ σ) (hHpos : 0 < H) (hH : H + R ≤ |t|)
    (hlog : ∀ w : ℂ, w ∈ ball ((σ : ℂ) + I * t) R →
      (logDeriv riemannZeta w).re ≤ M)
    (hR : 0 < R)
    (hz_half : ‖z - ((σ : ℂ) + I * t)‖ ≤ R / 2) :
    ‖logDeriv riemannZeta z‖ ≤
      2 * M + 3 * ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := by
  have hdiff : DifferentiableOn ℂ (logDeriv riemannZeta)
      (ball ((σ : ℂ) + I * t) R) := by
    exact (differentiableOn_logDeriv_riemannZeta_closedBall_sigma_it_of_disk_right_half
      (σ := σ) (t := t) (R := R) (H := H) hσ hHpos hH).mono
        Metric.ball_subset_closedBall
  have hmaps : Set.MapsTo (logDeriv riemannZeta)
      (ball ((σ : ℂ) + I * t) R) {w | w.re ≤ M} := by
    intro w hw
    exact hlog w hw
  exact borelCaratheodory_centered_half_radius_bound
    (f := logDeriv riemannZeta) (c := (σ : ℂ) + I * t)
    hM hdiff hmaps hR hz_half

/-- Direct half-radius oscillation Borel-Carathéodory bound for `logDeriv ζ`
on a `σ + I*t` disk with right-half-plane geometry. -/
lemma borelCaratheodory_sub_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le_half_radius
    {M R σ t H : ℝ} {z : ℂ}
    (hM : 0 < M) (hσ : 1 + R ≤ σ) (hHpos : 0 < H) (hH : H + R ≤ |t|)
    (hlog : ∀ w : ℂ, w ∈ ball ((σ : ℂ) + I * t) R →
      (logDeriv riemannZeta w -
        logDeriv riemannZeta ((σ : ℂ) + I * t)).re ≤ M)
    (hR : 0 < R)
    (hz_half : ‖z - ((σ : ℂ) + I * t)‖ ≤ R / 2) :
    ‖logDeriv riemannZeta z -
        logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤ 2 * M := by
  have hdiff : DifferentiableOn ℂ (logDeriv riemannZeta)
      (ball ((σ : ℂ) + I * t) R) := by
    exact (differentiableOn_logDeriv_riemannZeta_closedBall_sigma_it_of_disk_right_half
      (σ := σ) (t := t) (R := R) (H := H) hσ hHpos hH).mono
        Metric.ball_subset_closedBall
  have hmaps : Set.MapsTo
      (fun w => logDeriv riemannZeta w -
        logDeriv riemannZeta ((σ : ℂ) + I * t))
      (ball ((σ : ℂ) + I * t) R) {w | w.re ≤ M} := by
    intro w hw
    exact hlog w hw
  exact borelCaratheodory_sub_centered_half_radius_bound
    (f := logDeriv riemannZeta) (c := (σ : ℂ) + I * t)
    hM hdiff hmaps hR hz_half

/-- Direct half-radius Borel-Carathéodory bound for `-logDeriv ζ` on a
`σ + I*t` disk whose numeric geometry places it in the right half-plane and
away from the pole. -/
lemma borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le_half_radius
    {M R σ t H : ℝ} {z : ℂ}
    (hM : 0 < M) (hσ : 1 + R ≤ σ) (hHpos : 0 < H) (hH : H + R ≤ |t|)
    (hlog : ∀ w : ℂ, w ∈ ball ((σ : ℂ) + I * t) R →
      (-logDeriv riemannZeta w).re ≤ M)
    (hR : 0 < R)
    (hz_half : ‖z - ((σ : ℂ) + I * t)‖ ≤ R / 2) :
    ‖-logDeriv riemannZeta z‖ ≤
      2 * M + 3 * ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := by
  have hdiff : DifferentiableOn ℂ (fun w : ℂ => -logDeriv riemannZeta w)
      (ball ((σ : ℂ) + I * t) R) := by
    exact (differentiableOn_neg_logDeriv_riemannZeta_closedBall_sigma_it_of_disk_right_half
      (σ := σ) (t := t) (R := R) (H := H) hσ hHpos hH).mono
        Metric.ball_subset_closedBall
  have hmaps : Set.MapsTo (fun w : ℂ => -logDeriv riemannZeta w)
      (ball ((σ : ℂ) + I * t) R) {w | w.re ≤ M} := by
    intro w hw
    exact hlog w hw
  exact borelCaratheodory_centered_half_radius_bound
    (f := fun w : ℂ => -logDeriv riemannZeta w)
    (c := (σ : ℂ) + I * t) hM hdiff hmaps hR hz_half

/-- Direct half-radius oscillation Borel-Carathéodory bound for `-logDeriv ζ`
on a `σ + I*t` disk with right-half-plane geometry. -/
lemma borelCaratheodory_sub_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le_half_radius
    {M R σ t H : ℝ} {z : ℂ}
    (hM : 0 < M) (hσ : 1 + R ≤ σ) (hHpos : 0 < H) (hH : H + R ≤ |t|)
    (hlog : ∀ w : ℂ, w ∈ ball ((σ : ℂ) + I * t) R →
      (-logDeriv riemannZeta w -
        -logDeriv riemannZeta ((σ : ℂ) + I * t)).re ≤ M)
    (hR : 0 < R)
    (hz_half : ‖z - ((σ : ℂ) + I * t)‖ ≤ R / 2) :
    ‖-logDeriv riemannZeta z -
        -logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤ 2 * M := by
  have hdiff : DifferentiableOn ℂ (fun w : ℂ => -logDeriv riemannZeta w)
      (ball ((σ : ℂ) + I * t) R) := by
    exact (differentiableOn_neg_logDeriv_riemannZeta_closedBall_sigma_it_of_disk_right_half
      (σ := σ) (t := t) (R := R) (H := H) hσ hHpos hH).mono
        Metric.ball_subset_closedBall
  have hmaps : Set.MapsTo
      (fun w : ℂ => -logDeriv riemannZeta w -
        -logDeriv riemannZeta ((σ : ℂ) + I * t))
      (ball ((σ : ℂ) + I * t) R) {w | w.re ≤ M} := by
    intro w hw
    exact hlog w hw
  exact borelCaratheodory_sub_centered_half_radius_bound
    (f := fun w : ℂ => -logDeriv riemannZeta w)
    (c := (σ : ℂ) + I * t) hM hdiff hmaps hR hz_half

/-- Direct half-radius Borel-Carathéodory bound for `logDeriv ζ` with an
affine full-height real-part input on the local `σ + I*t` disk. -/
lemma borelCaratheodory_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_affine_re_le_half_radius
    {Are Bre Acenter Bcenter R σ t H : ℝ} {z : ℂ}
    (hM : 0 < Are + Bre * Real.log (‖((σ : ℂ) + I * t)‖ + 3))
    (hσ : 1 + R ≤ σ) (hHpos : 0 < H) (hH : H + R ≤ |t|)
    (hlog : ∀ w : ℂ, w ∈ ball ((σ : ℂ) + I * t) R →
      (logDeriv riemannZeta w).re ≤
        Are + Bre * Real.log (‖((σ : ℂ) + I * t)‖ + 3))
    (hcenter :
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
        Acenter + Bcenter * Real.log (‖((σ : ℂ) + I * t)‖ + 3))
    (hR : 0 < R)
    (hz_half : ‖z - ((σ : ℂ) + I * t)‖ ≤ R / 2) :
    ‖logDeriv riemannZeta z‖ ≤
      (2 * Are + 3 * Acenter) +
        (2 * Bre + 3 * Bcenter) *
          Real.log (‖((σ : ℂ) + I * t)‖ + 3) := by
  let ell : ℝ := Real.log (‖((σ : ℂ) + I * t)‖ + 3)
  let mBound : ℝ := Are + Bre * ell
  have hborel :
      ‖logDeriv riemannZeta z‖ ≤
        2 * mBound + 3 * ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := by
    refine
      borelCaratheodory_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le_half_radius
        (M := mBound) (R := R) (σ := σ) (t := t) (H := H) (z := z)
        ?_ hσ hHpos hH ?_ hR hz_half
    · simpa [mBound, ell] using hM
    · intro w hw
      simpa [mBound, ell] using hlog w hw
  have hcenter_mul :
      3 * ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
        3 * (Acenter + Bcenter * ell) := by
    exact mul_le_mul_of_nonneg_left (by simpa [ell] using hcenter)
      (by norm_num : (0 : ℝ) ≤ 3)
  calc
    ‖logDeriv riemannZeta z‖
        ≤ 2 * mBound + 3 * ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ :=
          hborel
    _ ≤ 2 * mBound + 3 * (Acenter + Bcenter * ell) := by
      nlinarith
    _ = (2 * Are + 3 * Acenter) +
          (2 * Bre + 3 * Bcenter) *
            Real.log (‖((σ : ℂ) + I * t)‖ + 3) := by
      simp [mBound, ell]
      ring

/-- Direct half-radius oscillation Borel-Carathéodory bound for `logDeriv ζ`
with an affine full-height real-part input on the local `σ + I*t` disk. -/
lemma borelCaratheodory_sub_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_affine_re_le_half_radius
    {Are Bre R σ t H : ℝ} {z : ℂ}
    (hM : 0 < Are + Bre * Real.log (‖((σ : ℂ) + I * t)‖ + 3))
    (hσ : 1 + R ≤ σ) (hHpos : 0 < H) (hH : H + R ≤ |t|)
    (hlog : ∀ w : ℂ, w ∈ ball ((σ : ℂ) + I * t) R →
      (logDeriv riemannZeta w -
        logDeriv riemannZeta ((σ : ℂ) + I * t)).re ≤
          Are + Bre * Real.log (‖((σ : ℂ) + I * t)‖ + 3))
    (hR : 0 < R)
    (hz_half : ‖z - ((σ : ℂ) + I * t)‖ ≤ R / 2) :
    ‖logDeriv riemannZeta z -
        logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
      2 * Are + 2 * Bre * Real.log (‖((σ : ℂ) + I * t)‖ + 3) := by
  let ell : ℝ := Real.log (‖((σ : ℂ) + I * t)‖ + 3)
  let mBound : ℝ := Are + Bre * ell
  have hborel :
      ‖logDeriv riemannZeta z -
          logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤ 2 * mBound := by
    refine
      borelCaratheodory_sub_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le_half_radius
        (M := mBound) (R := R) (σ := σ) (t := t) (H := H) (z := z)
        ?_ hσ hHpos hH ?_ hR hz_half
    · simpa [mBound, ell] using hM
    · intro w hw
      simpa [mBound, ell] using hlog w hw
  calc
    ‖logDeriv riemannZeta z -
        logDeriv riemannZeta ((σ : ℂ) + I * t)‖
        ≤ 2 * mBound := hborel
    _ = 2 * Are + 2 * Bre *
          Real.log (‖((σ : ℂ) + I * t)‖ + 3) := by
      simp [mBound, ell]
      ring

/-- Direct half-radius Borel-Carathéodory bound for `-logDeriv ζ` with an
affine full-height real-part input on the local `σ + I*t` disk. -/
lemma borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_affine_re_le_half_radius
    {Are Bre Acenter Bcenter R σ t H : ℝ} {z : ℂ}
    (hM : 0 < Are + Bre * Real.log (‖((σ : ℂ) + I * t)‖ + 3))
    (hσ : 1 + R ≤ σ) (hHpos : 0 < H) (hH : H + R ≤ |t|)
    (hlog : ∀ w : ℂ, w ∈ ball ((σ : ℂ) + I * t) R →
      (-logDeriv riemannZeta w).re ≤
        Are + Bre * Real.log (‖((σ : ℂ) + I * t)‖ + 3))
    (hcenter :
      ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
        Acenter + Bcenter * Real.log (‖((σ : ℂ) + I * t)‖ + 3))
    (hR : 0 < R)
    (hz_half : ‖z - ((σ : ℂ) + I * t)‖ ≤ R / 2) :
    ‖-logDeriv riemannZeta z‖ ≤
      (2 * Are + 3 * Acenter) +
        (2 * Bre + 3 * Bcenter) *
          Real.log (‖((σ : ℂ) + I * t)‖ + 3) := by
  let ell : ℝ := Real.log (‖((σ : ℂ) + I * t)‖ + 3)
  let mBound : ℝ := Are + Bre * ell
  have hborel :
      ‖-logDeriv riemannZeta z‖ ≤
        2 * mBound + 3 * ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := by
    refine
      borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le_half_radius
        (M := mBound) (R := R) (σ := σ) (t := t) (H := H) (z := z)
        ?_ hσ hHpos hH ?_ hR hz_half
    · simpa [mBound, ell] using hM
    · intro w hw
      simpa [mBound, ell] using hlog w hw
  have hcenter_mul :
      3 * ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
        3 * (Acenter + Bcenter * ell) := by
    exact mul_le_mul_of_nonneg_left (by simpa [ell] using hcenter)
      (by norm_num : (0 : ℝ) ≤ 3)
  calc
    ‖-logDeriv riemannZeta z‖
        ≤ 2 * mBound + 3 * ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ :=
          hborel
    _ ≤ 2 * mBound + 3 * (Acenter + Bcenter * ell) := by
      nlinarith
    _ = (2 * Are + 3 * Acenter) +
          (2 * Bre + 3 * Bcenter) *
            Real.log (‖((σ : ℂ) + I * t)‖ + 3) := by
      simp [mBound, ell]
      ring

/-- Direct half-radius oscillation Borel-Carathéodory bound for `-logDeriv ζ`
with an affine full-height real-part input on the local `σ + I*t` disk. -/
lemma borelCaratheodory_sub_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_affine_re_le_half_radius
    {Are Bre R σ t H : ℝ} {z : ℂ}
    (hM : 0 < Are + Bre * Real.log (‖((σ : ℂ) + I * t)‖ + 3))
    (hσ : 1 + R ≤ σ) (hHpos : 0 < H) (hH : H + R ≤ |t|)
    (hlog : ∀ w : ℂ, w ∈ ball ((σ : ℂ) + I * t) R →
      (-logDeriv riemannZeta w -
        -logDeriv riemannZeta ((σ : ℂ) + I * t)).re ≤
          Are + Bre * Real.log (‖((σ : ℂ) + I * t)‖ + 3))
    (hR : 0 < R)
    (hz_half : ‖z - ((σ : ℂ) + I * t)‖ ≤ R / 2) :
    ‖-logDeriv riemannZeta z -
        -logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
      2 * Are + 2 * Bre * Real.log (‖((σ : ℂ) + I * t)‖ + 3) := by
  let ell : ℝ := Real.log (‖((σ : ℂ) + I * t)‖ + 3)
  let mBound : ℝ := Are + Bre * ell
  have hborel :
      ‖-logDeriv riemannZeta z -
          -logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤ 2 * mBound := by
    refine
      borelCaratheodory_sub_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le_half_radius
        (M := mBound) (R := R) (σ := σ) (t := t) (H := H) (z := z)
        ?_ hσ hHpos hH ?_ hR hz_half
    · simpa [mBound, ell] using hM
    · intro w hw
      simpa [mBound, ell] using hlog w hw
  calc
    ‖-logDeriv riemannZeta z -
        -logDeriv riemannZeta ((σ : ℂ) + I * t)‖
        ≤ 2 * mBound := hborel
    _ = 2 * Are + 2 * Bre *
          Real.log (‖((σ : ℂ) + I * t)‖ + 3) := by
      simp [mBound, ell]
      ring

/-- Right-shifted half-radius Borel-Carathéodory transfer for `logDeriv ζ`.
It controls the boundary-near point `σ + I*t` from a disk centered at
`(σ + r) + I*t`; the hypotheses make the radius-`2r` disk stay in `Re ≥ 1`
and away from the pole.  The real-part and center estimates remain explicit
analytic inputs. -/
lemma borelCaratheodory_logDeriv_riemannZeta_sigma_it_right_shift_of_affine_re_le_half_radius
    {Are Bre Acenter Bcenter r H σ t : ℝ}
    (hr : 0 < r) (hσ : 1 + r ≤ σ) (hHpos : 0 < H)
    (hH : H + 2 * r ≤ |t|)
    (hM :
      0 < Are + Bre *
        Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hlog : ∀ w : ℂ,
      w ∈ ball (((σ + r : ℝ) : ℂ) + I * t) (2 * r) →
        (logDeriv riemannZeta w).re ≤
          Are + Bre *
            Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hcenter :
      ‖logDeriv riemannZeta (((σ + r : ℝ) : ℂ) + I * t)‖ ≤
        Acenter + Bcenter *
          Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3)) :
    ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
      (2 * Are + 3 * Acenter) +
        (2 * Bre + 3 * Bcenter) *
          Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3) := by
  have hR : 0 < 2 * r := by nlinarith
  have hσ_center : 1 + 2 * r ≤ σ + r := by nlinarith
  have hz_half :
      ‖((σ : ℂ) + I * t) - (((σ + r : ℝ) : ℂ) + I * t)‖ ≤
        (2 * r) / 2 := by
    have hdiff :
        ((σ : ℂ) + I * t) - (((σ + r : ℝ) : ℂ) + I * t) =
          -(r : ℂ) := by
      rw [Complex.ofReal_add]
      ring
    calc
      ‖((σ : ℂ) + I * t) - (((σ + r : ℝ) : ℂ) + I * t)‖
          = ‖-(r : ℂ)‖ := by rw [hdiff]
      _ = r := by simp [abs_of_pos hr]
      _ ≤ (2 * r) / 2 := by
        rw [show (2 * r) / 2 = r by ring]
  exact
    borelCaratheodory_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_affine_re_le_half_radius
      (Are := Are) (Bre := Bre) (Acenter := Acenter) (Bcenter := Bcenter)
      (R := 2 * r) (σ := σ + r) (t := t) (H := H)
      (z := (σ : ℂ) + I * t) hM hσ_center hHpos hH hlog hcenter hR hz_half

/-- Signed right-shifted half-radius Borel-Carathéodory transfer for
`-logDeriv ζ`.  This is the same geometric handoff as
`borelCaratheodory_logDeriv_riemannZeta_sigma_it_right_shift_of_affine_re_le_half_radius`,
but in the sign convention used by the 3-4-1 inequality. -/
lemma borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_right_shift_of_affine_re_le_half_radius
    {Are Bre Acenter Bcenter r H σ t : ℝ}
    (hr : 0 < r) (hσ : 1 + r ≤ σ) (hHpos : 0 < H)
    (hH : H + 2 * r ≤ |t|)
    (hM :
      0 < Are + Bre *
        Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hlog : ∀ w : ℂ,
      w ∈ ball (((σ + r : ℝ) : ℂ) + I * t) (2 * r) →
        (-logDeriv riemannZeta w).re ≤
          Are + Bre *
            Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hcenter :
      ‖-logDeriv riemannZeta (((σ + r : ℝ) : ℂ) + I * t)‖ ≤
        Acenter + Bcenter *
          Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3)) :
    ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
      (2 * Are + 3 * Acenter) +
        (2 * Bre + 3 * Bcenter) *
          Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3) := by
  have hR : 0 < 2 * r := by nlinarith
  have hσ_center : 1 + 2 * r ≤ σ + r := by nlinarith
  have hz_half :
      ‖((σ : ℂ) + I * t) - (((σ + r : ℝ) : ℂ) + I * t)‖ ≤
        (2 * r) / 2 := by
    have hdiff :
        ((σ : ℂ) + I * t) - (((σ + r : ℝ) : ℂ) + I * t) =
          -(r : ℂ) := by
      rw [Complex.ofReal_add]
      ring
    calc
      ‖((σ : ℂ) + I * t) - (((σ + r : ℝ) : ℂ) + I * t)‖
          = ‖-(r : ℂ)‖ := by rw [hdiff]
      _ = r := by simp [abs_of_pos hr]
      _ ≤ (2 * r) / 2 := by
        rw [show (2 * r) / 2 = r by ring]
  exact
    borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_affine_re_le_half_radius
      (Are := Are) (Bre := Bre) (Acenter := Acenter) (Bcenter := Bcenter)
      (R := 2 * r) (σ := σ + r) (t := t) (H := H)
      (z := (σ : ℂ) + I * t) hM hσ_center hHpos hH hlog hcenter hR hz_half

/-- Right-shifted Borel transfer normalized to the pure `log |t|` scale.
This composes the local right-shifted Borel handoff with the elementary bound
`log(‖(σ+r)+it‖+3) <= 2 log |t|` on `1 <= σ+r <= 3`.  The zeta-specific
real-part and center estimates are still hypotheses. -/
lemma borelCaratheodory_logDeriv_riemannZeta_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius
    {Are Bre Acenter Bcenter r H σ t : ℝ}
    (hr : 0 < r) (hσ : 1 + r ≤ σ) (hσr : σ + r ≤ 3)
    (hHpos : 0 < H) (hH : H + 2 * r ≤ |t|) (ht : 6 ≤ |t|)
    (hA : 0 ≤ 2 * Are + 3 * Acenter)
    (hB : 0 ≤ 2 * Bre + 3 * Bcenter)
    (hM :
      0 < Are + Bre *
        Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hlog : ∀ w : ℂ,
      w ∈ ball (((σ + r : ℝ) : ℂ) + I * t) (2 * r) →
        (logDeriv riemannZeta w).re ≤
          Are + Bre *
            Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hcenter :
      ‖logDeriv riemannZeta (((σ + r : ℝ) : ℂ) + I * t)‖ ≤
        Acenter + Bcenter *
          Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3)) :
    ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
      ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
        Real.log |t| := by
  let A0 : ℝ := 2 * Are + 3 * Acenter
  let B0 : ℝ := 2 * Bre + 3 * Bcenter
  have hbase :
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
        A0 + B0 * Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3) := by
    simpa [A0, B0] using
      borelCaratheodory_logDeriv_riemannZeta_sigma_it_right_shift_of_affine_re_le_half_radius
        (Are := Are) (Bre := Bre) (Acenter := Acenter) (Bcenter := Bcenter)
        (r := r) (H := H) (σ := σ) (t := t)
        hr hσ hHpos hH hM hlog hcenter
  have hcenter_re : σ + r ∈ Set.Icc 1 3 := by
    constructor
    · nlinarith [hr, hσ]
    · exact hσr
  have hlog_norm :
      Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3) ≤
        2 * Real.log |t| := by
    simpa using
      log_norm_sigma_add_I_mul_add_three_le_two_log_abs_of_re_le_three
        (σ := σ + r) (t := t) hcenter_re ht
  have hlog_ge_one : 1 ≤ Real.log |t| :=
    (log_abs_gt_one_of_three_le (by linarith : 3 ≤ |t|)).le
  have hA_le : A0 ≤ A0 * Real.log |t| := by
    calc
      A0 = A0 * 1 := by ring
      _ ≤ A0 * Real.log |t| :=
          mul_le_mul_of_nonneg_left hlog_ge_one (by simpa [A0] using hA)
  calc
    ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖
        ≤ A0 + B0 * Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3) :=
          hbase
    _ ≤ A0 * Real.log |t| + B0 * (2 * Real.log |t|) := by
        exact add_le_add hA_le
          (mul_le_mul_of_nonneg_left hlog_norm (by simpa [B0] using hB))
    _ = ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
        Real.log |t| := by
      simp [A0, B0]
      ring

/-- Signed version of the right-shifted Borel transfer normalized to the pure
`log |t|` scale. -/
lemma borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius
    {Are Bre Acenter Bcenter r H σ t : ℝ}
    (hr : 0 < r) (hσ : 1 + r ≤ σ) (hσr : σ + r ≤ 3)
    (hHpos : 0 < H) (hH : H + 2 * r ≤ |t|) (ht : 6 ≤ |t|)
    (hA : 0 ≤ 2 * Are + 3 * Acenter)
    (hB : 0 ≤ 2 * Bre + 3 * Bcenter)
    (hM :
      0 < Are + Bre *
        Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hlog : ∀ w : ℂ,
      w ∈ ball (((σ + r : ℝ) : ℂ) + I * t) (2 * r) →
        (-logDeriv riemannZeta w).re ≤
          Are + Bre *
            Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hcenter :
      ‖-logDeriv riemannZeta (((σ + r : ℝ) : ℂ) + I * t)‖ ≤
        Acenter + Bcenter *
          Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3)) :
    ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
      ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
        Real.log |t| := by
  let A0 : ℝ := 2 * Are + 3 * Acenter
  let B0 : ℝ := 2 * Bre + 3 * Bcenter
  have hbase :
      ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
        A0 + B0 * Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3) := by
    simpa [A0, B0] using
      borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_right_shift_of_affine_re_le_half_radius
        (Are := Are) (Bre := Bre) (Acenter := Acenter) (Bcenter := Bcenter)
        (r := r) (H := H) (σ := σ) (t := t)
        hr hσ hHpos hH hM hlog hcenter
  have hcenter_re : σ + r ∈ Set.Icc 1 3 := by
    constructor
    · nlinarith [hr, hσ]
    · exact hσr
  have hlog_norm :
      Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3) ≤
        2 * Real.log |t| := by
    simpa using
      log_norm_sigma_add_I_mul_add_three_le_two_log_abs_of_re_le_three
        (σ := σ + r) (t := t) hcenter_re ht
  have hlog_ge_one : 1 ≤ Real.log |t| :=
    (log_abs_gt_one_of_three_le (by linarith : 3 ≤ |t|)).le
  have hA_le : A0 ≤ A0 * Real.log |t| := by
    calc
      A0 = A0 * 1 := by ring
      _ ≤ A0 * Real.log |t| :=
          mul_le_mul_of_nonneg_left hlog_ge_one (by simpa [A0] using hA)
  calc
    ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖
        ≤ A0 + B0 * Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3) :=
          hbase
    _ ≤ A0 * Real.log |t| + B0 * (2 * Real.log |t|) := by
        exact add_le_add hA_le
          (mul_le_mul_of_nonneg_left hlog_norm (by simpa [B0] using hB))
    _ = ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
        Real.log |t| := by
      simp [A0, B0]
      ring

/-- Right-shifted Borel transfer in the full complex-height logarithmic scale.
This is a direct weakening of
`borelCaratheodory_logDeriv_riemannZeta_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius`
using `log |t| <= log(‖σ+it‖+3)`. -/
lemma borelCaratheodory_logDeriv_riemannZeta_sigma_it_right_shift_le_log_norm_of_affine_re_le_half_radius
    {Are Bre Acenter Bcenter r H σ t : ℝ}
    (hr : 0 < r) (hσ : 1 + r ≤ σ) (hσr : σ + r ≤ 3)
    (hHpos : 0 < H) (hH : H + 2 * r ≤ |t|) (ht : 6 ≤ |t|)
    (hA : 0 ≤ 2 * Are + 3 * Acenter)
    (hB : 0 ≤ 2 * Bre + 3 * Bcenter)
    (hM :
      0 < Are + Bre *
        Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hlog : ∀ w : ℂ,
      w ∈ ball (((σ + r : ℝ) : ℂ) + I * t) (2 * r) →
        (logDeriv riemannZeta w).re ≤
          Are + Bre *
            Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hcenter :
      ‖logDeriv riemannZeta (((σ + r : ℝ) : ℂ) + I * t)‖ ≤
        Acenter + Bcenter *
          Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3)) :
    ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
      ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
        Real.log (‖((σ : ℂ) + I * t)‖ + 3) := by
  let C : ℝ := (2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)
  have hbase :
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
        C * Real.log |t| := by
    simpa [C] using
      borelCaratheodory_logDeriv_riemannZeta_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius
        (Are := Are) (Bre := Bre) (Acenter := Acenter) (Bcenter := Bcenter)
        (r := r) (H := H) (σ := σ) (t := t)
        hr hσ hσr hHpos hH ht hA hB hM hlog hcenter
  have hC : 0 ≤ C := by
    simp [C]
    nlinarith [hA, hB]
  have hlog_le :
      Real.log |t| ≤ Real.log (‖((σ : ℂ) + I * t)‖ + 3) :=
    log_abs_le_log_norm_sigma_add_I_mul_add_three (σ := σ) (t := t)
      (by linarith : 0 < |t|)
  calc
    ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖
        ≤ C * Real.log |t| := hbase
    _ ≤ C * Real.log (‖((σ : ℂ) + I * t)‖ + 3) :=
        mul_le_mul_of_nonneg_left hlog_le hC
    _ = ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
        Real.log (‖((σ : ℂ) + I * t)‖ + 3) := by simp [C]

/-- Signed right-shifted Borel transfer in the full complex-height logarithmic
scale. -/
lemma borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_right_shift_le_log_norm_of_affine_re_le_half_radius
    {Are Bre Acenter Bcenter r H σ t : ℝ}
    (hr : 0 < r) (hσ : 1 + r ≤ σ) (hσr : σ + r ≤ 3)
    (hHpos : 0 < H) (hH : H + 2 * r ≤ |t|) (ht : 6 ≤ |t|)
    (hA : 0 ≤ 2 * Are + 3 * Acenter)
    (hB : 0 ≤ 2 * Bre + 3 * Bcenter)
    (hM :
      0 < Are + Bre *
        Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hlog : ∀ w : ℂ,
      w ∈ ball (((σ + r : ℝ) : ℂ) + I * t) (2 * r) →
        (-logDeriv riemannZeta w).re ≤
          Are + Bre *
            Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hcenter :
      ‖-logDeriv riemannZeta (((σ + r : ℝ) : ℂ) + I * t)‖ ≤
        Acenter + Bcenter *
          Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3)) :
    ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
      ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
        Real.log (‖((σ : ℂ) + I * t)‖ + 3) := by
  let C : ℝ := (2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)
  have hbase :
      ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
        C * Real.log |t| := by
    simpa [C] using
      borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius
        (Are := Are) (Bre := Bre) (Acenter := Acenter) (Bcenter := Bcenter)
        (r := r) (H := H) (σ := σ) (t := t)
        hr hσ hσr hHpos hH ht hA hB hM hlog hcenter
  have hC : 0 ≤ C := by
    simp [C]
    nlinarith [hA, hB]
  have hlog_le :
      Real.log |t| ≤ Real.log (‖((σ : ℂ) + I * t)‖ + 3) :=
    log_abs_le_log_norm_sigma_add_I_mul_add_three (σ := σ) (t := t)
      (by linarith : 0 < |t|)
  calc
    ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖
        ≤ C * Real.log |t| := hbase
    _ ≤ C * Real.log (‖((σ : ℂ) + I * t)‖ + 3) :=
        mul_le_mul_of_nonneg_left hlog_le hC
    _ = ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
        Real.log (‖((σ : ℂ) + I * t)‖ + 3) := by simp [C]

/-- Real-part quotient form of the right-shifted Borel transfer for
`logDeriv ζ`.  This is the sign convention consumed by the 3-4-1
zero-free-region route. -/
lemma re_neg_deriv_div_riemannZeta_sigma_it_right_shift_le_log_abs_of_affine_logDeriv_re_le_half_radius
    {Are Bre Acenter Bcenter r H σ t : ℝ}
    (hr : 0 < r) (hσ : 1 + r ≤ σ) (hσr : σ + r ≤ 3)
    (hHpos : 0 < H) (hH : H + 2 * r ≤ |t|) (ht : 6 ≤ |t|)
    (hA : 0 ≤ 2 * Are + 3 * Acenter)
    (hB : 0 ≤ 2 * Bre + 3 * Bcenter)
    (hM :
      0 < Are + Bre *
        Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hlog : ∀ w : ℂ,
      w ∈ ball (((σ + r : ℝ) : ℂ) + I * t) (2 * r) →
        (logDeriv riemannZeta w).re ≤
          Are + Bre *
            Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hcenter :
      ‖logDeriv riemannZeta (((σ + r : ℝ) : ℂ) + I * t)‖ ≤
        Acenter + Bcenter *
          Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3)) :
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re ≤
      ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
        Real.log |t| := by
  let z : ℂ := (σ : ℂ) + I * t
  calc
    (-deriv riemannZeta z / riemannZeta z).re
        ≤ ‖-deriv riemannZeta z / riemannZeta z‖ := Complex.re_le_norm _
    _ = ‖logDeriv riemannZeta z‖ :=
        norm_neg_deriv_div_riemannZeta_eq_norm_logDeriv z
    _ ≤ ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
        Real.log |t| := by
      simpa [z] using
        borelCaratheodory_logDeriv_riemannZeta_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius
          (Are := Are) (Bre := Bre) (Acenter := Acenter) (Bcenter := Bcenter)
          (r := r) (H := H) (σ := σ) (t := t)
          hr hσ hσr hHpos hH ht hA hB hM hlog hcenter

/-- Real-part quotient form of the signed right-shifted Borel transfer for
`-logDeriv ζ`. -/
lemma re_neg_deriv_div_riemannZeta_sigma_it_right_shift_le_log_abs_of_affine_neg_logDeriv_re_le_half_radius
    {Are Bre Acenter Bcenter r H σ t : ℝ}
    (hr : 0 < r) (hσ : 1 + r ≤ σ) (hσr : σ + r ≤ 3)
    (hHpos : 0 < H) (hH : H + 2 * r ≤ |t|) (ht : 6 ≤ |t|)
    (hA : 0 ≤ 2 * Are + 3 * Acenter)
    (hB : 0 ≤ 2 * Bre + 3 * Bcenter)
    (hM :
      0 < Are + Bre *
        Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hlog : ∀ w : ℂ,
      w ∈ ball (((σ + r : ℝ) : ℂ) + I * t) (2 * r) →
        (-logDeriv riemannZeta w).re ≤
          Are + Bre *
            Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hcenter :
      ‖-logDeriv riemannZeta (((σ + r : ℝ) : ℂ) + I * t)‖ ≤
        Acenter + Bcenter *
          Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3)) :
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re ≤
      ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
        Real.log |t| := by
  let z : ℂ := (σ : ℂ) + I * t
  calc
    (-deriv riemannZeta z / riemannZeta z).re
        ≤ ‖-deriv riemannZeta z / riemannZeta z‖ := Complex.re_le_norm _
    _ = ‖logDeriv riemannZeta z‖ :=
        norm_neg_deriv_div_riemannZeta_eq_norm_logDeriv z
    _ = ‖-logDeriv riemannZeta z‖ := (norm_neg _).symm
    _ ≤ ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
        Real.log |t| := by
      simpa [z] using
        borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius
          (Are := Are) (Bre := Bre) (Acenter := Acenter) (Bcenter := Bcenter)
          (r := r) (H := H) (σ := σ) (t := t)
          hr hσ hσr hHpos hH ht hA hB hM hlog hcenter

/-- Real-part quotient form of the right-shifted Borel transfer for
`logDeriv ζ`, in the full complex-height logarithmic scale. -/
lemma re_neg_deriv_div_riemannZeta_sigma_it_right_shift_le_log_norm_of_affine_logDeriv_re_le_half_radius
    {Are Bre Acenter Bcenter r H σ t : ℝ}
    (hr : 0 < r) (hσ : 1 + r ≤ σ) (hσr : σ + r ≤ 3)
    (hHpos : 0 < H) (hH : H + 2 * r ≤ |t|) (ht : 6 ≤ |t|)
    (hA : 0 ≤ 2 * Are + 3 * Acenter)
    (hB : 0 ≤ 2 * Bre + 3 * Bcenter)
    (hM :
      0 < Are + Bre *
        Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hlog : ∀ w : ℂ,
      w ∈ ball (((σ + r : ℝ) : ℂ) + I * t) (2 * r) →
        (logDeriv riemannZeta w).re ≤
          Are + Bre *
            Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hcenter :
      ‖logDeriv riemannZeta (((σ + r : ℝ) : ℂ) + I * t)‖ ≤
        Acenter + Bcenter *
          Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3)) :
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re ≤
      ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
        Real.log (‖((σ : ℂ) + I * t)‖ + 3) := by
  let z : ℂ := (σ : ℂ) + I * t
  calc
    (-deriv riemannZeta z / riemannZeta z).re
        ≤ ‖-deriv riemannZeta z / riemannZeta z‖ := Complex.re_le_norm _
    _ = ‖logDeriv riemannZeta z‖ :=
        norm_neg_deriv_div_riemannZeta_eq_norm_logDeriv z
    _ ≤ ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
        Real.log (‖((σ : ℂ) + I * t)‖ + 3) := by
      simpa [z] using
        borelCaratheodory_logDeriv_riemannZeta_sigma_it_right_shift_le_log_norm_of_affine_re_le_half_radius
          (Are := Are) (Bre := Bre) (Acenter := Acenter) (Bcenter := Bcenter)
          (r := r) (H := H) (σ := σ) (t := t)
          hr hσ hσr hHpos hH ht hA hB hM hlog hcenter

/-- Real-part quotient form of the signed right-shifted Borel transfer for
`-logDeriv ζ`, in the full complex-height logarithmic scale. -/
lemma re_neg_deriv_div_riemannZeta_sigma_it_right_shift_le_log_norm_of_affine_neg_logDeriv_re_le_half_radius
    {Are Bre Acenter Bcenter r H σ t : ℝ}
    (hr : 0 < r) (hσ : 1 + r ≤ σ) (hσr : σ + r ≤ 3)
    (hHpos : 0 < H) (hH : H + 2 * r ≤ |t|) (ht : 6 ≤ |t|)
    (hA : 0 ≤ 2 * Are + 3 * Acenter)
    (hB : 0 ≤ 2 * Bre + 3 * Bcenter)
    (hM :
      0 < Are + Bre *
        Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hlog : ∀ w : ℂ,
      w ∈ ball (((σ + r : ℝ) : ℂ) + I * t) (2 * r) →
        (-logDeriv riemannZeta w).re ≤
          Are + Bre *
            Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hcenter :
      ‖-logDeriv riemannZeta (((σ + r : ℝ) : ℂ) + I * t)‖ ≤
        Acenter + Bcenter *
          Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3)) :
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re ≤
      ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
        Real.log (‖((σ : ℂ) + I * t)‖ + 3) := by
  let z : ℂ := (σ : ℂ) + I * t
  calc
    (-deriv riemannZeta z / riemannZeta z).re
        ≤ ‖-deriv riemannZeta z / riemannZeta z‖ := Complex.re_le_norm _
    _ = ‖logDeriv riemannZeta z‖ :=
        norm_neg_deriv_div_riemannZeta_eq_norm_logDeriv z
    _ = ‖-logDeriv riemannZeta z‖ := (norm_neg _).symm
    _ ≤ ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
        Real.log (‖((σ : ℂ) + I * t)‖ + 3) := by
      simpa [z] using
        borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_right_shift_le_log_norm_of_affine_re_le_half_radius
          (Are := Are) (Bre := Bre) (Acenter := Acenter) (Bcenter := Bcenter)
          (r := r) (H := H) (σ := σ) (t := t)
          hr hσ hσr hHpos hH ht hA hB hM hlog hcenter

/-- Shifted third-term version of the right-shifted Borel quotient bridge.
It controls `Re(-ζ'/ζ)(σ+2it)` in the pure `log |t|` scale from local Borel
hypotheses centered at `(σ+r)+2it`. -/
lemma re_neg_deriv_div_riemannZeta_sigma_two_it_right_shift_le_log_abs_of_affine_logDeriv_re_le_half_radius
    {Are Bre Acenter Bcenter r H σ t : ℝ}
    (hr : 0 < r) (hσ : 1 + r ≤ σ) (hσr : σ + r ≤ 3)
    (hHpos : 0 < H) (hH : H + 2 * r ≤ |2 * t|) (ht : 3 ≤ |t|)
    (hA : 0 ≤ 2 * Are + 3 * Acenter)
    (hB : 0 ≤ 2 * Bre + 3 * Bcenter)
    (hM :
      0 < Are + Bre *
        Real.log (‖(((σ + r : ℝ) : ℂ) + I * ((2 * t : ℝ) : ℂ))‖ + 3))
    (hlog : ∀ w : ℂ,
      w ∈ ball (((σ + r : ℝ) : ℂ) + I * ((2 * t : ℝ) : ℂ)) (2 * r) →
        (logDeriv riemannZeta w).re ≤
          Are + Bre *
            Real.log (‖(((σ + r : ℝ) : ℂ) + I * ((2 * t : ℝ) : ℂ))‖ + 3))
    (hcenter :
      ‖logDeriv riemannZeta (((σ + r : ℝ) : ℂ) + I * ((2 * t : ℝ) : ℂ))‖ ≤
        Acenter + Bcenter *
          Real.log (‖(((σ + r : ℝ) : ℂ) + I * ((2 * t : ℝ) : ℂ))‖ + 3)) :
    (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
        riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤
      2 * ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
        Real.log |t| := by
  let C : ℝ := (2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)
  have hC : 0 ≤ C := by
    exact add_nonneg hA (mul_nonneg (by norm_num) hB)
  have ht_two : 6 ≤ |2 * t| := by
    have htwo_abs : |(2 : ℝ) * t| = 2 * |t| := by simp [abs_mul]
    rw [htwo_abs]
    nlinarith
  have hbase :
      (-deriv riemannZeta ((σ : ℂ) + I * (2 * t)) /
          riemannZeta ((σ : ℂ) + I * (2 * t))).re ≤
        C * Real.log |2 * t| := by
    simpa [C] using
      re_neg_deriv_div_riemannZeta_sigma_it_right_shift_le_log_abs_of_affine_logDeriv_re_le_half_radius
        (Are := Are) (Bre := Bre) (Acenter := Acenter) (Bcenter := Bcenter)
        (r := r) (H := H) (σ := σ) (t := 2 * t)
        hr hσ hσr hHpos hH ht_two hA hB hM hlog hcenter
  have hlog_two : Real.log |2 * t| ≤ 2 * Real.log |t| :=
    log_abs_two_mul_le_two_log_abs (by linarith : 2 ≤ |t|)
  have hpoint : ((σ : ℂ) + 2 * I * t) = ((σ : ℂ) + I * (2 * t)) := by
    norm_num [Complex.ofReal_mul]
    ring
  calc
    (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
        riemannZeta ((σ : ℂ) + 2 * I * t)).re
        = (-deriv riemannZeta ((σ : ℂ) + I * (2 * t)) /
            riemannZeta ((σ : ℂ) + I * (2 * t))).re := by
          rw [hpoint]
    _ ≤ C * Real.log |2 * t| := hbase
    _ ≤ C * (2 * Real.log |t|) :=
        mul_le_mul_of_nonneg_left hlog_two hC
    _ = 2 * ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
        Real.log |t| := by
      simp [C]
      ring

/-- Signed shifted third-term version of the right-shifted Borel quotient
bridge, using local hypotheses for `-logDeriv ζ` at height `2t`. -/
lemma re_neg_deriv_div_riemannZeta_sigma_two_it_right_shift_le_log_abs_of_affine_neg_logDeriv_re_le_half_radius
    {Are Bre Acenter Bcenter r H σ t : ℝ}
    (hr : 0 < r) (hσ : 1 + r ≤ σ) (hσr : σ + r ≤ 3)
    (hHpos : 0 < H) (hH : H + 2 * r ≤ |2 * t|) (ht : 3 ≤ |t|)
    (hA : 0 ≤ 2 * Are + 3 * Acenter)
    (hB : 0 ≤ 2 * Bre + 3 * Bcenter)
    (hM :
      0 < Are + Bre *
        Real.log (‖(((σ + r : ℝ) : ℂ) + I * ((2 * t : ℝ) : ℂ))‖ + 3))
    (hlog : ∀ w : ℂ,
      w ∈ ball (((σ + r : ℝ) : ℂ) + I * ((2 * t : ℝ) : ℂ)) (2 * r) →
        (-logDeriv riemannZeta w).re ≤
          Are + Bre *
            Real.log (‖(((σ + r : ℝ) : ℂ) + I * ((2 * t : ℝ) : ℂ))‖ + 3))
    (hcenter :
      ‖-logDeriv riemannZeta (((σ + r : ℝ) : ℂ) + I * ((2 * t : ℝ) : ℂ))‖ ≤
        Acenter + Bcenter *
          Real.log (‖(((σ + r : ℝ) : ℂ) + I * ((2 * t : ℝ) : ℂ))‖ + 3)) :
    (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
        riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤
      2 * ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
        Real.log |t| := by
  let C : ℝ := (2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)
  have hC : 0 ≤ C := by
    exact add_nonneg hA (mul_nonneg (by norm_num) hB)
  have ht_two : 6 ≤ |2 * t| := by
    have htwo_abs : |(2 : ℝ) * t| = 2 * |t| := by simp [abs_mul]
    rw [htwo_abs]
    nlinarith
  have hbase :
      (-deriv riemannZeta ((σ : ℂ) + I * (2 * t)) /
          riemannZeta ((σ : ℂ) + I * (2 * t))).re ≤
        C * Real.log |2 * t| := by
    simpa [C] using
      re_neg_deriv_div_riemannZeta_sigma_it_right_shift_le_log_abs_of_affine_neg_logDeriv_re_le_half_radius
        (Are := Are) (Bre := Bre) (Acenter := Acenter) (Bcenter := Bcenter)
        (r := r) (H := H) (σ := σ) (t := 2 * t)
        hr hσ hσr hHpos hH ht_two hA hB hM hlog hcenter
  have hlog_two : Real.log |2 * t| ≤ 2 * Real.log |t| :=
    log_abs_two_mul_le_two_log_abs (by linarith : 2 ≤ |t|)
  have hpoint : ((σ : ℂ) + 2 * I * t) = ((σ : ℂ) + I * (2 * t)) := by
    norm_num [Complex.ofReal_mul]
    ring
  calc
    (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
        riemannZeta ((σ : ℂ) + 2 * I * t)).re
        = (-deriv riemannZeta ((σ : ℂ) + I * (2 * t)) /
            riemannZeta ((σ : ℂ) + I * (2 * t))).re := by
          rw [hpoint]
    _ ≤ C * Real.log |2 * t| := hbase
    _ ≤ C * (2 * Real.log |t|) :=
        mul_le_mul_of_nonneg_left hlog_two hC
    _ = 2 * ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
        Real.log |t| := by
      simp [C]
      ring

/-- Shifted third-term right-shifted Borel quotient bridge in the full
complex-height logarithmic scale, using local `logDeriv ζ` hypotheses at
height `2t`. -/
lemma re_neg_deriv_div_riemannZeta_sigma_two_it_right_shift_le_log_norm_of_affine_logDeriv_re_le_half_radius
    {Are Bre Acenter Bcenter r H σ t : ℝ}
    (hr : 0 < r) (hσ : 1 + r ≤ σ) (hσr : σ + r ≤ 3)
    (hHpos : 0 < H) (hH : H + 2 * r ≤ |2 * t|) (ht : 3 ≤ |t|)
    (hA : 0 ≤ 2 * Are + 3 * Acenter)
    (hB : 0 ≤ 2 * Bre + 3 * Bcenter)
    (hM :
      0 < Are + Bre *
        Real.log (‖(((σ + r : ℝ) : ℂ) + I * ((2 * t : ℝ) : ℂ))‖ + 3))
    (hlog : ∀ w : ℂ,
      w ∈ ball (((σ + r : ℝ) : ℂ) + I * ((2 * t : ℝ) : ℂ)) (2 * r) →
        (logDeriv riemannZeta w).re ≤
          Are + Bre *
            Real.log (‖(((σ + r : ℝ) : ℂ) + I * ((2 * t : ℝ) : ℂ))‖ + 3))
    (hcenter :
      ‖logDeriv riemannZeta (((σ + r : ℝ) : ℂ) + I * ((2 * t : ℝ) : ℂ))‖ ≤
        Acenter + Bcenter *
          Real.log (‖(((σ + r : ℝ) : ℂ) + I * ((2 * t : ℝ) : ℂ))‖ + 3)) :
    (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
        riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤
      2 * ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
        Real.log (‖((σ : ℂ) + I * t)‖ + 3) := by
  let C : ℝ := (2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)
  have hC : 0 ≤ 2 * C := by
    have hC0 : 0 ≤ C := add_nonneg hA (mul_nonneg (by norm_num) hB)
    positivity
  have hbase :
      (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
          riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤
        2 * C * Real.log |t| := by
    simpa [C] using
      re_neg_deriv_div_riemannZeta_sigma_two_it_right_shift_le_log_abs_of_affine_logDeriv_re_le_half_radius
        (Are := Are) (Bre := Bre) (Acenter := Acenter) (Bcenter := Bcenter)
        (r := r) (H := H) (σ := σ) (t := t)
        hr hσ hσr hHpos hH ht hA hB hM hlog hcenter
  have hlog_le :
      Real.log |t| ≤ Real.log (‖((σ : ℂ) + I * t)‖ + 3) :=
    log_abs_le_log_norm_sigma_add_I_mul_add_three (σ := σ) (t := t)
      (by linarith : 0 < |t|)
  calc
    (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
        riemannZeta ((σ : ℂ) + 2 * I * t)).re
        ≤ 2 * C * Real.log |t| := hbase
    _ ≤ 2 * C * Real.log (‖((σ : ℂ) + I * t)‖ + 3) :=
        mul_le_mul_of_nonneg_left hlog_le hC
    _ = 2 * ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
        Real.log (‖((σ : ℂ) + I * t)‖ + 3) := by simp [C]

/-- Signed shifted third-term right-shifted Borel quotient bridge in the full
complex-height logarithmic scale, using local `-logDeriv ζ` hypotheses at
height `2t`. -/
lemma re_neg_deriv_div_riemannZeta_sigma_two_it_right_shift_le_log_norm_of_affine_neg_logDeriv_re_le_half_radius
    {Are Bre Acenter Bcenter r H σ t : ℝ}
    (hr : 0 < r) (hσ : 1 + r ≤ σ) (hσr : σ + r ≤ 3)
    (hHpos : 0 < H) (hH : H + 2 * r ≤ |2 * t|) (ht : 3 ≤ |t|)
    (hA : 0 ≤ 2 * Are + 3 * Acenter)
    (hB : 0 ≤ 2 * Bre + 3 * Bcenter)
    (hM :
      0 < Are + Bre *
        Real.log (‖(((σ + r : ℝ) : ℂ) + I * ((2 * t : ℝ) : ℂ))‖ + 3))
    (hlog : ∀ w : ℂ,
      w ∈ ball (((σ + r : ℝ) : ℂ) + I * ((2 * t : ℝ) : ℂ)) (2 * r) →
        (-logDeriv riemannZeta w).re ≤
          Are + Bre *
            Real.log (‖(((σ + r : ℝ) : ℂ) + I * ((2 * t : ℝ) : ℂ))‖ + 3))
    (hcenter :
      ‖-logDeriv riemannZeta (((σ + r : ℝ) : ℂ) + I * ((2 * t : ℝ) : ℂ))‖ ≤
        Acenter + Bcenter *
          Real.log (‖(((σ + r : ℝ) : ℂ) + I * ((2 * t : ℝ) : ℂ))‖ + 3)) :
    (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
        riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤
      2 * ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
        Real.log (‖((σ : ℂ) + I * t)‖ + 3) := by
  let C : ℝ := (2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)
  have hC : 0 ≤ 2 * C := by
    have hC0 : 0 ≤ C := add_nonneg hA (mul_nonneg (by norm_num) hB)
    positivity
  have hbase :
      (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
          riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤
        2 * C * Real.log |t| := by
    simpa [C] using
      re_neg_deriv_div_riemannZeta_sigma_two_it_right_shift_le_log_abs_of_affine_neg_logDeriv_re_le_half_radius
        (Are := Are) (Bre := Bre) (Acenter := Acenter) (Bcenter := Bcenter)
        (r := r) (H := H) (σ := σ) (t := t)
        hr hσ hσr hHpos hH ht hA hB hM hlog hcenter
  have hlog_le :
      Real.log |t| ≤ Real.log (‖((σ : ℂ) + I * t)‖ + 3) :=
    log_abs_le_log_norm_sigma_add_I_mul_add_three (σ := σ) (t := t)
      (by linarith : 0 < |t|)
  calc
    (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
        riemannZeta ((σ : ℂ) + 2 * I * t)).re
        ≤ 2 * C * Real.log |t| := hbase
    _ ≤ 2 * C * Real.log (‖((σ : ℂ) + I * t)‖ + 3) :=
        mul_le_mul_of_nonneg_left hlog_le hC
    _ = 2 * ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
        Real.log (‖((σ : ℂ) + I * t)‖ + 3) := by simp [C]

/-- Right-shifted Borel-Carathéodory transfer for the signed regular part
`-logDeriv ζ(w) + (w-ρ)⁻¹`, normalized to the pure `log |t|` scale.

The differentiability, local real-part bound, and center bound for the regular
part are explicit hypotheses: proving those zeta-specific estimates is the
remaining analytic work. -/
lemma borelCaratheodory_neg_logDeriv_regularPart_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius
    {Are Bre Acenter Bcenter r σ β t : ℝ}
    (hr : 0 < r) (hσ : 1 + r ≤ σ) (hσr : σ + r ≤ 3) (ht : 6 ≤ |t|)
    (hA : 0 ≤ 2 * Are + 3 * Acenter)
    (hB : 0 ≤ 2 * Bre + 3 * Bcenter)
    (hM :
      0 < Are + Bre *
        Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hdiff :
      DifferentiableOn ℂ
        (fun w : ℂ =>
          -logDeriv riemannZeta w + (w - ((β : ℂ) + I * t))⁻¹)
        (ball (((σ + r : ℝ) : ℂ) + I * t) (2 * r)))
    (hlog : ∀ w : ℂ,
      w ∈ ball (((σ + r : ℝ) : ℂ) + I * t) (2 * r) →
        (-logDeriv riemannZeta w + (w - ((β : ℂ) + I * t))⁻¹).re ≤
          Are + Bre *
            Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hcenter :
      ‖-logDeriv riemannZeta (((σ + r : ℝ) : ℂ) + I * t) +
          ((((σ + r : ℝ) : ℂ) + I * t) - ((β : ℂ) + I * t))⁻¹‖ ≤
        Acenter + Bcenter *
          Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3)) :
    ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
        (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
      ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
        Real.log |t| := by
  let center : ℂ := ((σ + r : ℝ) : ℂ) + I * t
  let target : ℂ := (σ : ℂ) + I * t
  let rho : ℂ := (β : ℂ) + I * t
  let f : ℂ → ℂ := fun w : ℂ => -logDeriv riemannZeta w + (w - rho)⁻¹
  let ell : ℝ := Real.log (‖center‖ + 3)
  let M : ℝ := Are + Bre * ell
  let A0 : ℝ := 2 * Are + 3 * Acenter
  let B0 : ℝ := 2 * Bre + 3 * Bcenter
  have hR : 0 < 2 * r := by nlinarith
  have hz_half : ‖target - center‖ ≤ (2 * r) / 2 := by
    have hdiff_center : target - center = -(r : ℂ) := by
      simp [target, center, Complex.ofReal_add]
    calc
      ‖target - center‖ = ‖-(r : ℂ)‖ := by rw [hdiff_center]
      _ = r := by simp [abs_of_pos hr]
      _ ≤ (2 * r) / 2 := by
        rw [show (2 * r) / 2 = r by ring]
  have hborel_raw : ‖f target‖ ≤ 2 * M + 3 * ‖f center‖ := by
    refine
      borelCaratheodory_centered_half_radius_bound
        (f := f) (c := center) (M := M) (R := 2 * r) (z := target)
        ?_ ?_ ?_ hR hz_half
    · simpa [M, ell, center] using hM
    · simpa [f, rho, center] using hdiff
    · intro w hw
      simpa [f, rho, M, ell, center] using hlog w hw
  have hcenter_mul : 3 * ‖f center‖ ≤ 3 * (Acenter + Bcenter * ell) := by
    exact mul_le_mul_of_nonneg_left
      (by simpa [f, rho, center, ell] using hcenter)
      (by norm_num : (0 : ℝ) ≤ 3)
  have hbase : ‖f target‖ ≤ A0 + B0 * ell := by
    calc
      ‖f target‖ ≤ 2 * M + 3 * ‖f center‖ := hborel_raw
      _ ≤ 2 * M + 3 * (Acenter + Bcenter * ell) := by nlinarith
      _ = A0 + B0 * ell := by
        simp [M, A0, B0]
        ring
  have hcenter_re : σ + r ∈ Set.Icc 1 3 := by
    constructor
    · nlinarith [hr, hσ]
    · exact hσr
  have hlog_norm : ell ≤ 2 * Real.log |t| := by
    simpa [ell, center] using
      log_norm_sigma_add_I_mul_add_three_le_two_log_abs_of_re_le_three
        (σ := σ + r) (t := t) hcenter_re ht
  have hlog_ge_one : 1 ≤ Real.log |t| :=
    (log_abs_gt_one_of_three_le (by linarith : 3 ≤ |t|)).le
  have hA_le : A0 ≤ A0 * Real.log |t| := by
    calc
      A0 = A0 * 1 := by ring
      _ ≤ A0 * Real.log |t| :=
          mul_le_mul_of_nonneg_left hlog_ge_one (by simpa [A0] using hA)
  have htarget_sub : target - rho = ((σ - β : ℝ) : ℂ) := by
    simp [target, rho, Complex.ofReal_sub]
  have hnorm :
      ‖f target‖ ≤ (A0 + 2 * B0) * Real.log |t| := by
    calc
      ‖f target‖ ≤ A0 + B0 * ell := hbase
      _ ≤ A0 * Real.log |t| + B0 * (2 * Real.log |t|) := by
        exact add_le_add hA_le
          (mul_le_mul_of_nonneg_left hlog_norm (by simpa [B0] using hB))
      _ = (A0 + 2 * B0) * Real.log |t| := by ring
  simpa [f, target, rho, htarget_sub, A0, B0] using hnorm

/-- Real-part zero-repulsion form of
`borelCaratheodory_neg_logDeriv_regularPart_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius`.

This is the exact zero-term shape used in the high-height 3-4-1 closure:
`Re(-ζ'/ζ)(σ+it) + 1/(σ-β) <= C log |t|`. -/
lemma re_neg_logDeriv_riemannZeta_sigma_it_add_inv_right_shift_le_log_abs_of_affine_regularPart_re_le_half_radius
    {Are Bre Acenter Bcenter r σ β t : ℝ}
    (hr : 0 < r) (hσ : 1 + r ≤ σ) (hσr : σ + r ≤ 3) (ht : 6 ≤ |t|)
    (hA : 0 ≤ 2 * Are + 3 * Acenter)
    (hB : 0 ≤ 2 * Bre + 3 * Bcenter)
    (hM :
      0 < Are + Bre *
        Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hdiff :
      DifferentiableOn ℂ
        (fun w : ℂ =>
          -logDeriv riemannZeta w + (w - ((β : ℂ) + I * t))⁻¹)
        (ball (((σ + r : ℝ) : ℂ) + I * t) (2 * r)))
    (hlog : ∀ w : ℂ,
      w ∈ ball (((σ + r : ℝ) : ℂ) + I * t) (2 * r) →
        (-logDeriv riemannZeta w + (w - ((β : ℂ) + I * t))⁻¹).re ≤
          Are + Bre *
            Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hcenter :
      ‖-logDeriv riemannZeta (((σ + r : ℝ) : ℂ) + I * t) +
          ((((σ + r : ℝ) : ℂ) + I * t) - ((β : ℂ) + I * t))⁻¹‖ ≤
        Acenter + Bcenter *
          Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hsub : 0 < σ - β) :
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re + 1 / (σ - β) ≤
      ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
        Real.log |t| := by
  have hregular :
      ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
          (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
        ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
          Real.log |t| :=
    borelCaratheodory_neg_logDeriv_regularPart_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius
      (Are := Are) (Bre := Bre) (Acenter := Acenter) (Bcenter := Bcenter)
      (r := r) (σ := σ) (β := β) (t := t)
      hr hσ hσr ht hA hB hM hdiff hlog hcenter
  exact
    re_neg_logDeriv_riemannZeta_sigma_it_add_inv_le_of_regular_part_norm
      hregular hsub

/-- Multiplicity-aware right-shifted Borel-Carathéodory transfer for the signed
regular part `-logDeriv ζ(w) + n (w-ρ)⁻¹`, normalized to the pure `log |t|`
scale.  The analytic estimates for this regular part remain explicit
hypotheses. -/
lemma borelCaratheodory_neg_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius
    {Are Bre Acenter Bcenter r σ β t : ℝ} {n : ℕ}
    (hr : 0 < r) (hσ : 1 + r ≤ σ) (hσr : σ + r ≤ 3) (ht : 6 ≤ |t|)
    (hA : 0 ≤ 2 * Are + 3 * Acenter)
    (hB : 0 ≤ 2 * Bre + 3 * Bcenter)
    (hM :
      0 < Are + Bre *
        Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hdiff :
      DifferentiableOn ℂ
        (fun w : ℂ =>
          -logDeriv riemannZeta w +
            (n : ℂ) * (w - ((β : ℂ) + I * t))⁻¹)
        (ball (((σ + r : ℝ) : ℂ) + I * t) (2 * r)))
    (hlog : ∀ w : ℂ,
      w ∈ ball (((σ + r : ℝ) : ℂ) + I * t) (2 * r) →
        (-logDeriv riemannZeta w +
            (n : ℂ) * (w - ((β : ℂ) + I * t))⁻¹).re ≤
          Are + Bre *
            Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hcenter :
      ‖-logDeriv riemannZeta (((σ + r : ℝ) : ℂ) + I * t) +
          (n : ℂ) *
            ((((σ + r : ℝ) : ℂ) + I * t) - ((β : ℂ) + I * t))⁻¹‖ ≤
        Acenter + Bcenter *
          Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3)) :
    ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
        (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
      ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
        Real.log |t| := by
  let center : ℂ := ((σ + r : ℝ) : ℂ) + I * t
  let target : ℂ := (σ : ℂ) + I * t
  let rho : ℂ := (β : ℂ) + I * t
  let f : ℂ → ℂ :=
    fun w : ℂ => -logDeriv riemannZeta w + (n : ℂ) * (w - rho)⁻¹
  let ell : ℝ := Real.log (‖center‖ + 3)
  let M : ℝ := Are + Bre * ell
  let A0 : ℝ := 2 * Are + 3 * Acenter
  let B0 : ℝ := 2 * Bre + 3 * Bcenter
  have hR : 0 < 2 * r := by nlinarith
  have hz_half : ‖target - center‖ ≤ (2 * r) / 2 := by
    have hdiff_center : target - center = -(r : ℂ) := by
      simp [target, center, Complex.ofReal_add]
    calc
      ‖target - center‖ = ‖-(r : ℂ)‖ := by rw [hdiff_center]
      _ = r := by simp [abs_of_pos hr]
      _ ≤ (2 * r) / 2 := by
        rw [show (2 * r) / 2 = r by ring]
  have hborel_raw : ‖f target‖ ≤ 2 * M + 3 * ‖f center‖ := by
    refine
      borelCaratheodory_centered_half_radius_bound
        (f := f) (c := center) (M := M) (R := 2 * r) (z := target)
        ?_ ?_ ?_ hR hz_half
    · simpa [M, ell, center] using hM
    · simpa [f, rho, center] using hdiff
    · intro w hw
      simpa [f, rho, M, ell, center] using hlog w hw
  have hcenter_mul : 3 * ‖f center‖ ≤ 3 * (Acenter + Bcenter * ell) := by
    exact mul_le_mul_of_nonneg_left
      (by simpa [f, rho, center, ell] using hcenter)
      (by norm_num : (0 : ℝ) ≤ 3)
  have hbase : ‖f target‖ ≤ A0 + B0 * ell := by
    calc
      ‖f target‖ ≤ 2 * M + 3 * ‖f center‖ := hborel_raw
      _ ≤ 2 * M + 3 * (Acenter + Bcenter * ell) := by nlinarith
      _ = A0 + B0 * ell := by
        simp [M, A0, B0]
        ring
  have hcenter_re : σ + r ∈ Set.Icc 1 3 := by
    constructor
    · nlinarith [hr, hσ]
    · exact hσr
  have hlog_norm : ell ≤ 2 * Real.log |t| := by
    simpa [ell, center] using
      log_norm_sigma_add_I_mul_add_three_le_two_log_abs_of_re_le_three
        (σ := σ + r) (t := t) hcenter_re ht
  have hlog_ge_one : 1 ≤ Real.log |t| :=
    (log_abs_gt_one_of_three_le (by linarith : 3 ≤ |t|)).le
  have hA_le : A0 ≤ A0 * Real.log |t| := by
    calc
      A0 = A0 * 1 := by ring
      _ ≤ A0 * Real.log |t| :=
          mul_le_mul_of_nonneg_left hlog_ge_one (by simpa [A0] using hA)
  have htarget_sub : target - rho = ((σ - β : ℝ) : ℂ) := by
    simp [target, rho, Complex.ofReal_sub]
  have hnorm :
      ‖f target‖ ≤ (A0 + 2 * B0) * Real.log |t| := by
    calc
      ‖f target‖ ≤ A0 + B0 * ell := hbase
      _ ≤ A0 * Real.log |t| + B0 * (2 * Real.log |t|) := by
        exact add_le_add hA_le
          (mul_le_mul_of_nonneg_left hlog_norm (by simpa [B0] using hB))
      _ = (A0 + 2 * B0) * Real.log |t| := by ring
  simpa [f, target, rho, htarget_sub, A0, B0] using hnorm

/-- Multiplicity-aware zero-repulsion form of
`borelCaratheodory_neg_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius`.
It still concludes the unit-principal estimate because `n >= 1` only makes the
singular real term stronger. -/
lemma re_neg_logDeriv_riemannZeta_sigma_it_add_multiplicity_inv_right_shift_le_log_abs_of_affine_regularPart_re_le_half_radius
    {Are Bre Acenter Bcenter r σ β t : ℝ} {n : ℕ}
    (hr : 0 < r) (hσ : 1 + r ≤ σ) (hσr : σ + r ≤ 3) (ht : 6 ≤ |t|)
    (hA : 0 ≤ 2 * Are + 3 * Acenter)
    (hB : 0 ≤ 2 * Bre + 3 * Bcenter)
    (hM :
      0 < Are + Bre *
        Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hdiff :
      DifferentiableOn ℂ
        (fun w : ℂ =>
          -logDeriv riemannZeta w +
            (n : ℂ) * (w - ((β : ℂ) + I * t))⁻¹)
        (ball (((σ + r : ℝ) : ℂ) + I * t) (2 * r)))
    (hlog : ∀ w : ℂ,
      w ∈ ball (((σ + r : ℝ) : ℂ) + I * t) (2 * r) →
        (-logDeriv riemannZeta w +
            (n : ℂ) * (w - ((β : ℂ) + I * t))⁻¹).re ≤
          Are + Bre *
            Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hcenter :
      ‖-logDeriv riemannZeta (((σ + r : ℝ) : ℂ) + I * t) +
          (n : ℂ) *
            ((((σ + r : ℝ) : ℂ) + I * t) - ((β : ℂ) + I * t))⁻¹‖ ≤
        Acenter + Bcenter *
          Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hn : 0 < n) (hsub : 0 < σ - β) :
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re + 1 / (σ - β) ≤
      ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
        Real.log |t| := by
  have hregular :
      ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
          (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
        ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
          Real.log |t| :=
    borelCaratheodory_neg_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius
      (Are := Are) (Bre := Bre) (Acenter := Acenter) (Bcenter := Bcenter)
      (r := r) (σ := σ) (β := β) (t := t) (n := n)
      hr hσ hσr ht hA hB hM hdiff hlog hcenter
  exact
    re_neg_logDeriv_riemannZeta_sigma_it_add_inv_le_of_multiplicity_regular_part_norm
      hregular hn hsub

/-- Multiplicity-aware right-shifted Borel-Carathéodory transfer for the
positive logarithmic-derivative regular part
`logDeriv ζ(w) - n (w-ρ)⁻¹`, normalized to the pure `log |t|` scale. -/
lemma borelCaratheodory_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius
    {Are Bre Acenter Bcenter r σ β t : ℝ} {n : ℕ}
    (hr : 0 < r) (hσ : 1 + r ≤ σ) (hσr : σ + r ≤ 3) (ht : 6 ≤ |t|)
    (hA : 0 ≤ 2 * Are + 3 * Acenter)
    (hB : 0 ≤ 2 * Bre + 3 * Bcenter)
    (hM :
      0 < Are + Bre *
        Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hdiff :
      DifferentiableOn ℂ
        (fun w : ℂ =>
          logDeriv riemannZeta w -
            (n : ℂ) * (w - ((β : ℂ) + I * t))⁻¹)
        (ball (((σ + r : ℝ) : ℂ) + I * t) (2 * r)))
    (hlog : ∀ w : ℂ,
      w ∈ ball (((σ + r : ℝ) : ℂ) + I * t) (2 * r) →
        (logDeriv riemannZeta w -
            (n : ℂ) * (w - ((β : ℂ) + I * t))⁻¹).re ≤
          Are + Bre *
            Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hcenter :
      ‖logDeriv riemannZeta (((σ + r : ℝ) : ℂ) + I * t) -
          (n : ℂ) *
            ((((σ + r : ℝ) : ℂ) + I * t) - ((β : ℂ) + I * t))⁻¹‖ ≤
        Acenter + Bcenter *
          Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3)) :
    ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
        (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
      ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
        Real.log |t| := by
  let center : ℂ := ((σ + r : ℝ) : ℂ) + I * t
  let target : ℂ := (σ : ℂ) + I * t
  let rho : ℂ := (β : ℂ) + I * t
  let f : ℂ → ℂ :=
    fun w : ℂ => logDeriv riemannZeta w - (n : ℂ) * (w - rho)⁻¹
  let ell : ℝ := Real.log (‖center‖ + 3)
  let M : ℝ := Are + Bre * ell
  let A0 : ℝ := 2 * Are + 3 * Acenter
  let B0 : ℝ := 2 * Bre + 3 * Bcenter
  have hR : 0 < 2 * r := by nlinarith
  have hz_half : ‖target - center‖ ≤ (2 * r) / 2 := by
    have hdiff_center : target - center = -(r : ℂ) := by
      simp [target, center, Complex.ofReal_add]
    calc
      ‖target - center‖ = ‖-(r : ℂ)‖ := by rw [hdiff_center]
      _ = r := by simp [abs_of_pos hr]
      _ ≤ (2 * r) / 2 := by
        rw [show (2 * r) / 2 = r by ring]
  have hborel_raw : ‖f target‖ ≤ 2 * M + 3 * ‖f center‖ := by
    refine
      borelCaratheodory_centered_half_radius_bound
        (f := f) (c := center) (M := M) (R := 2 * r) (z := target)
        ?_ ?_ ?_ hR hz_half
    · simpa [M, ell, center] using hM
    · simpa [f, rho, center] using hdiff
    · intro w hw
      simpa [f, rho, M, ell, center] using hlog w hw
  have hcenter_mul : 3 * ‖f center‖ ≤ 3 * (Acenter + Bcenter * ell) := by
    exact mul_le_mul_of_nonneg_left
      (by simpa [f, rho, center, ell] using hcenter)
      (by norm_num : (0 : ℝ) ≤ 3)
  have hbase : ‖f target‖ ≤ A0 + B0 * ell := by
    calc
      ‖f target‖ ≤ 2 * M + 3 * ‖f center‖ := hborel_raw
      _ ≤ 2 * M + 3 * (Acenter + Bcenter * ell) := by nlinarith
      _ = A0 + B0 * ell := by
        simp [M, A0, B0]
        ring
  have hcenter_re : σ + r ∈ Set.Icc 1 3 := by
    constructor
    · nlinarith [hr, hσ]
    · exact hσr
  have hlog_norm : ell ≤ 2 * Real.log |t| := by
    simpa [ell, center] using
      log_norm_sigma_add_I_mul_add_three_le_two_log_abs_of_re_le_three
        (σ := σ + r) (t := t) hcenter_re ht
  have hlog_ge_one : 1 ≤ Real.log |t| :=
    (log_abs_gt_one_of_three_le (by linarith : 3 ≤ |t|)).le
  have hA_le : A0 ≤ A0 * Real.log |t| := by
    calc
      A0 = A0 * 1 := by ring
      _ ≤ A0 * Real.log |t| :=
          mul_le_mul_of_nonneg_left hlog_ge_one (by simpa [A0] using hA)
  have htarget_sub : target - rho = ((σ - β : ℝ) : ℂ) := by
    simp [target, rho, Complex.ofReal_sub]
  have hnorm :
      ‖f target‖ ≤ (A0 + 2 * B0) * Real.log |t| := by
    calc
      ‖f target‖ ≤ A0 + B0 * ell := hbase
      _ ≤ A0 * Real.log |t| + B0 * (2 * Real.log |t|) := by
        exact add_le_add hA_le
          (mul_le_mul_of_nonneg_left hlog_norm (by simpa [B0] using hB))
      _ = (A0 + 2 * B0) * Real.log |t| := by ring
  simpa [f, target, rho, htarget_sub, A0, B0] using hnorm

/-- Multiplicity-aware signed regular-part Borel transfer in the full
complex-height logarithmic scale. -/
lemma borelCaratheodory_neg_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_norm_of_affine_re_le_half_radius
    {Are Bre Acenter Bcenter r σ β t : ℝ} {n : ℕ}
    (hr : 0 < r) (hσ : 1 + r ≤ σ) (hσr : σ + r ≤ 3) (ht : 6 ≤ |t|)
    (hA : 0 ≤ 2 * Are + 3 * Acenter)
    (hB : 0 ≤ 2 * Bre + 3 * Bcenter)
    (hM :
      0 < Are + Bre *
        Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hdiff :
      DifferentiableOn ℂ
        (fun w : ℂ =>
          -logDeriv riemannZeta w +
            (n : ℂ) * (w - ((β : ℂ) + I * t))⁻¹)
        (ball (((σ + r : ℝ) : ℂ) + I * t) (2 * r)))
    (hlog : ∀ w : ℂ,
      w ∈ ball (((σ + r : ℝ) : ℂ) + I * t) (2 * r) →
        (-logDeriv riemannZeta w +
            (n : ℂ) * (w - ((β : ℂ) + I * t))⁻¹).re ≤
          Are + Bre *
            Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hcenter :
      ‖-logDeriv riemannZeta (((σ + r : ℝ) : ℂ) + I * t) +
          (n : ℂ) *
            ((((σ + r : ℝ) : ℂ) + I * t) - ((β : ℂ) + I * t))⁻¹‖ ≤
        Acenter + Bcenter *
          Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3)) :
    ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
        (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
      ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
        Real.log (‖((σ : ℂ) + I * t)‖ + 3) := by
  let C : ℝ := (2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)
  have hbase :
      ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
          (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
        C * Real.log |t| := by
    simpa [C] using
      borelCaratheodory_neg_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius
        (Are := Are) (Bre := Bre) (Acenter := Acenter) (Bcenter := Bcenter)
        (r := r) (σ := σ) (β := β) (t := t) (n := n)
        hr hσ hσr ht hA hB hM hdiff hlog hcenter
  have hC : 0 ≤ C := by
    simp [C]
    nlinarith [hA, hB]
  have hlog_le :
      Real.log |t| ≤ Real.log (‖((σ : ℂ) + I * t)‖ + 3) :=
    log_abs_le_log_norm_sigma_add_I_mul_add_three (σ := σ) (t := t)
      (by linarith : 0 < |t|)
  calc
    ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
        (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖
        ≤ C * Real.log |t| := hbase
    _ ≤ C * Real.log (‖((σ : ℂ) + I * t)‖ + 3) :=
        mul_le_mul_of_nonneg_left hlog_le hC
    _ = ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
        Real.log (‖((σ : ℂ) + I * t)‖ + 3) := by simp [C]

/-- Multiplicity-aware positive regular-part Borel transfer in the full
complex-height logarithmic scale. -/
lemma borelCaratheodory_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_norm_of_affine_re_le_half_radius
    {Are Bre Acenter Bcenter r σ β t : ℝ} {n : ℕ}
    (hr : 0 < r) (hσ : 1 + r ≤ σ) (hσr : σ + r ≤ 3) (ht : 6 ≤ |t|)
    (hA : 0 ≤ 2 * Are + 3 * Acenter)
    (hB : 0 ≤ 2 * Bre + 3 * Bcenter)
    (hM :
      0 < Are + Bre *
        Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hdiff :
      DifferentiableOn ℂ
        (fun w : ℂ =>
          logDeriv riemannZeta w -
            (n : ℂ) * (w - ((β : ℂ) + I * t))⁻¹)
        (ball (((σ + r : ℝ) : ℂ) + I * t) (2 * r)))
    (hlog : ∀ w : ℂ,
      w ∈ ball (((σ + r : ℝ) : ℂ) + I * t) (2 * r) →
        (logDeriv riemannZeta w -
            (n : ℂ) * (w - ((β : ℂ) + I * t))⁻¹).re ≤
          Are + Bre *
            Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hcenter :
      ‖logDeriv riemannZeta (((σ + r : ℝ) : ℂ) + I * t) -
          (n : ℂ) *
            ((((σ + r : ℝ) : ℂ) + I * t) - ((β : ℂ) + I * t))⁻¹‖ ≤
        Acenter + Bcenter *
          Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3)) :
    ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
        (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
      ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
        Real.log (‖((σ : ℂ) + I * t)‖ + 3) := by
  let C : ℝ := (2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)
  have hbase :
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
          (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
        C * Real.log |t| := by
    simpa [C] using
      borelCaratheodory_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius
        (Are := Are) (Bre := Bre) (Acenter := Acenter) (Bcenter := Bcenter)
        (r := r) (σ := σ) (β := β) (t := t) (n := n)
        hr hσ hσr ht hA hB hM hdiff hlog hcenter
  have hC : 0 ≤ C := by
    simp [C]
    nlinarith [hA, hB]
  have hlog_le :
      Real.log |t| ≤ Real.log (‖((σ : ℂ) + I * t)‖ + 3) :=
    log_abs_le_log_norm_sigma_add_I_mul_add_three (σ := σ) (t := t)
      (by linarith : 0 < |t|)
  calc
    ‖logDeriv riemannZeta ((σ : ℂ) + I * t) -
        (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖
        ≤ C * Real.log |t| := hbase
    _ ≤ C * Real.log (‖((σ : ℂ) + I * t)‖ + 3) :=
        mul_le_mul_of_nonneg_left hlog_le hC
    _ = ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
        Real.log (‖((σ : ℂ) + I * t)‖ + 3) := by simp [C]

/-- Multiplicity-aware zero-repulsion form in the full complex-height
logarithmic scale. -/
lemma re_neg_logDeriv_riemannZeta_sigma_it_add_multiplicity_inv_right_shift_le_log_norm_of_affine_regularPart_re_le_half_radius
    {Are Bre Acenter Bcenter r σ β t : ℝ} {n : ℕ}
    (hr : 0 < r) (hσ : 1 + r ≤ σ) (hσr : σ + r ≤ 3) (ht : 6 ≤ |t|)
    (hA : 0 ≤ 2 * Are + 3 * Acenter)
    (hB : 0 ≤ 2 * Bre + 3 * Bcenter)
    (hM :
      0 < Are + Bre *
        Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hdiff :
      DifferentiableOn ℂ
        (fun w : ℂ =>
          -logDeriv riemannZeta w +
            (n : ℂ) * (w - ((β : ℂ) + I * t))⁻¹)
        (ball (((σ + r : ℝ) : ℂ) + I * t) (2 * r)))
    (hlog : ∀ w : ℂ,
      w ∈ ball (((σ + r : ℝ) : ℂ) + I * t) (2 * r) →
        (-logDeriv riemannZeta w +
            (n : ℂ) * (w - ((β : ℂ) + I * t))⁻¹).re ≤
          Are + Bre *
            Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hcenter :
      ‖-logDeriv riemannZeta (((σ + r : ℝ) : ℂ) + I * t) +
          (n : ℂ) *
            ((((σ + r : ℝ) : ℂ) + I * t) - ((β : ℂ) + I * t))⁻¹‖ ≤
        Acenter + Bcenter *
          Real.log (‖(((σ + r : ℝ) : ℂ) + I * t)‖ + 3))
    (hn : 0 < n) (hsub : 0 < σ - β) :
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re + 1 / (σ - β) ≤
      ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
        Real.log (‖((σ : ℂ) + I * t)‖ + 3) := by
  have hregular :
      ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) +
          (n : ℂ) * (((σ - β : ℝ) : ℂ)⁻¹)‖ ≤
        ((2 * Are + 3 * Acenter) + 2 * (2 * Bre + 3 * Bcenter)) *
          Real.log (‖((σ : ℂ) + I * t)‖ + 3) :=
    borelCaratheodory_neg_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_norm_of_affine_re_le_half_radius
      (Are := Are) (Bre := Bre) (Acenter := Acenter) (Bcenter := Bcenter)
      (r := r) (σ := σ) (β := β) (t := t) (n := n)
      hr hσ hσr ht hA hB hM hdiff hlog hcenter
  exact
    re_neg_logDeriv_riemannZeta_sigma_it_add_inv_le_of_multiplicity_regular_part_norm
      hregular hn hsub

/-- ζ is meromorphic on every project vertical region. -/
lemma meromorphicOn_riemannZeta_verticalRegion (a b H : ℝ) :
    MeromorphicOn riemannZeta (verticalRegion a b H) := by
  intro s _hs
  by_cases hs : s = 1
  · subst hs
    exact meromorphicAt_riemannZeta_one
  · exact meromorphicAt_riemannZeta_of_ne_one s hs

/-- The logarithmic derivative of ζ is meromorphic on every project vertical
region. -/
lemma meromorphicOn_logDeriv_riemannZeta_verticalRegion (a b H : ℝ) :
    MeromorphicOn (logDeriv riemannZeta) (verticalRegion a b H) :=
  (meromorphicOn_riemannZeta_verticalRegion a b H).logDeriv

/-- The signed logarithmic derivative of ζ is meromorphic on every project
vertical region. -/
lemma meromorphicOn_neg_logDeriv_riemannZeta_verticalRegion (a b H : ℝ) :
    MeromorphicOn (fun z : ℂ => -logDeriv riemannZeta z)
      (verticalRegion a b H) :=
  (meromorphicOn_logDeriv_riemannZeta_verticalRegion a b H).neg

/-- ζ is globally meromorphic. -/
lemma meromorphic_riemannZeta :
    Meromorphic riemannZeta := by
  intro s
  by_cases hs : s = 1
  · subst hs
    exact meromorphicAt_riemannZeta_one
  · exact meromorphicAt_riemannZeta_of_ne_one s hs

/-- The logarithmic derivative of ζ is globally meromorphic. -/
lemma meromorphic_logDeriv_riemannZeta :
    Meromorphic (logDeriv riemannZeta) :=
  meromorphic_riemannZeta.deriv.div meromorphic_riemannZeta

/-- The signed logarithmic derivative `-logDeriv ζ` is globally
meromorphic. -/
lemma meromorphic_neg_logDeriv_riemannZeta :
    Meromorphic (fun z : ℂ => -logDeriv riemannZeta z) := by
  simpa only [Pi.neg_apply] using meromorphic_logDeriv_riemannZeta.neg

/-- Translating the input of a global meromorphic function preserves
meromorphicity.

This is the bridge needed to use Mathlib's zero-centered value-distribution
log-counting API on disks centered at arbitrary complex points. -/
lemma meromorphic_comp_add_const {f : ℂ → ℂ}
    (hf : Meromorphic f) (c : ℂ) :
    Meromorphic (fun z : ℂ => f (z + c)) := by
  intro z
  exact MeromorphicAt.comp_analyticAt (hf (z + c))
    (analyticAt_id.add analyticAt_const)

/-- On a positive-height right half-strip, `logDeriv ζ` is differentiable.

The positive-height hypothesis excludes the pole at `1`; the lower real-part
bound `1 <= a` lets Mathlib's nonvanishing theorem for ζ on `Re(s) >= 1`
remove the denominator of the logarithmic derivative. -/
lemma differentiableOn_logDeriv_riemannZeta_verticalRegion_of_one_le_re
    {a b H : ℝ} (ha : 1 ≤ a) (hH : 0 < H) :
    DifferentiableOn ℂ (logDeriv riemannZeta) (verticalRegion a b H) := by
  intro z hz
  have hsubset : verticalRegion a b H ⊆ ({z : ℂ | z ≠ 1} : Set ℂ) := by
    intro w hw
    exact ne_one_of_mem_verticalRegion_of_pos_height hw hH
  have han : AnalyticOnNhd ℂ riemannZeta (verticalRegion a b H) :=
    analyticOnNhd_riemannZeta_ne_one.mono hsubset
  have hzeta_diff : DifferentiableAt ℂ riemannZeta z :=
    (han z hz).differentiableAt
  have hderiv_diff : DifferentiableAt ℂ (deriv riemannZeta) z :=
    (han.deriv z hz).differentiableAt
  have hzeta_ne : riemannZeta z ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (le_trans ha hz.1.1)
  exact (hderiv_diff.div hzeta_diff hzeta_ne).differentiableWithinAt

/-- Borel-Carathéodory for `logDeriv ζ` on a right half-strip, with the
`DifferentiableOn` hypothesis discharged by zeta nonvanishing on `Re(s) >= 1`.

The remaining analytic input is the pointwise real-part bound on
`logDeriv ζ`; this is the estimate future height/growth arguments must supply. -/
lemma borelCaratheodory_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le
    {M R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < M) (ha₀ : 1 ≤ a) (hHpos : 0 < H)
    (hlog : ∀ w : ℂ, w ∈ verticalRegion a b H →
      (logDeriv riemannZeta w).re ≤ M)
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R) (hz : z ∈ Metric.ball ((σ : ℂ) + I * t) R) :
    ‖logDeriv riemannZeta z‖ ≤
      2 * M * ‖z - ((σ : ℂ) + I * t)‖ /
          (R - ‖z - ((σ : ℂ) + I * t)‖) +
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ *
          (R + ‖z - ((σ : ℂ) + I * t)‖) /
          (R - ‖z - ((σ : ℂ) + I * t)‖) :=
  borelCaratheodory_logDeriv_riemannZeta_verticalRegion_of_re_le hM
    (differentiableOn_logDeriv_riemannZeta_verticalRegion_of_one_le_re
      ha₀ hHpos)
    hlog ha hb hH hR hz

/-- Oscillation Borel-Carathéodory for `logDeriv ζ` on a right half-strip,
with differentiability discharged by zeta nonvanishing on `Re(s) >= 1`. -/
lemma borelCaratheodory_sub_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le
    {M R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < M) (ha₀ : 1 ≤ a) (hHpos : 0 < H)
    (hlog : ∀ w : ℂ, w ∈ verticalRegion a b H →
      (logDeriv riemannZeta w -
        logDeriv riemannZeta ((σ : ℂ) + I * t)).re ≤ M)
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R) (hz : z ∈ Metric.ball ((σ : ℂ) + I * t) R) :
    ‖logDeriv riemannZeta z -
        logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
      2 * M * ‖z - ((σ : ℂ) + I * t)‖ /
        (R - ‖z - ((σ : ℂ) + I * t)‖) :=
  borelCaratheodory_sub_logDeriv_riemannZeta_verticalRegion_of_re_le hM
    (differentiableOn_logDeriv_riemannZeta_verticalRegion_of_one_le_re
      ha₀ hHpos)
    hlog ha hb hH hR hz

/-- Half-radius Borel-Carathéodory bound for `logDeriv ζ` on a right
half-strip, with differentiability discharged by zeta nonvanishing on
`Re(s) >= 1`. -/
lemma borelCaratheodory_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le_half_radius
    {M R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < M) (ha₀ : 1 ≤ a) (hHpos : 0 < H)
    (hlog : ∀ w : ℂ, w ∈ verticalRegion a b H →
      (logDeriv riemannZeta w).re ≤ M)
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R)
    (hz_half : ‖z - ((σ : ℂ) + I * t)‖ ≤ R / 2) :
    ‖logDeriv riemannZeta z‖ ≤
      2 * M + 3 * ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := by
  refine borelCaratheodory_centered_verticalRegion_half_radius_bound hM
    (differentiableOn_logDeriv_riemannZeta_verticalRegion_of_one_le_re
      ha₀ hHpos) ?_ ha hb hH hR hz_half
  intro w hw
  exact hlog w hw

/-- Half-radius oscillation Borel-Carathéodory bound for `logDeriv ζ` on a
right half-strip, with differentiability discharged by zeta nonvanishing on
`Re(s) >= 1`. -/
lemma borelCaratheodory_sub_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le_half_radius
    {M R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < M) (ha₀ : 1 ≤ a) (hHpos : 0 < H)
    (hlog : ∀ w : ℂ, w ∈ verticalRegion a b H →
      (logDeriv riemannZeta w -
        logDeriv riemannZeta ((σ : ℂ) + I * t)).re ≤ M)
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R)
    (hz_half : ‖z - ((σ : ℂ) + I * t)‖ ≤ R / 2) :
    ‖logDeriv riemannZeta z -
        logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤ 2 * M := by
  refine borelCaratheodory_sub_centered_verticalRegion_half_radius_bound hM
    (differentiableOn_logDeriv_riemannZeta_verticalRegion_of_one_le_re
      ha₀ hHpos) ?_ ha hb hH hR hz_half
  intro w hw
  exact hlog w hw

/-- Half-radius Borel-Carathéodory bound for `logDeriv ζ` with an affine
full-height logarithmic real-part input.

The raw Borel output is `2*M + 3*‖logDeriv ζ center‖`.  This wrapper accepts
`M = A + B log(‖center‖+3)` and an affine center bound, then normalizes the
result to the same affine full-height scale. -/
lemma borelCaratheodory_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_affine_re_le_half_radius
    {Are Bre Acenter Bcenter R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < Are + Bre * Real.log (‖((σ : ℂ) + I * t)‖ + 3))
    (ha₀ : 1 ≤ a) (hHpos : 0 < H)
    (hlog : ∀ w : ℂ, w ∈ verticalRegion a b H →
      (logDeriv riemannZeta w).re ≤
        Are + Bre * Real.log (‖((σ : ℂ) + I * t)‖ + 3))
    (hcenter :
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
        Acenter + Bcenter * Real.log (‖((σ : ℂ) + I * t)‖ + 3))
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R)
    (hz_half : ‖z - ((σ : ℂ) + I * t)‖ ≤ R / 2) :
    ‖logDeriv riemannZeta z‖ ≤
      (2 * Are + 3 * Acenter) +
        (2 * Bre + 3 * Bcenter) *
          Real.log (‖((σ : ℂ) + I * t)‖ + 3) := by
  let ell : ℝ := Real.log (‖((σ : ℂ) + I * t)‖ + 3)
  let mBound : ℝ := Are + Bre * ell
  have hborel :
      ‖logDeriv riemannZeta z‖ ≤
        2 * mBound + 3 * ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := by
    refine
      borelCaratheodory_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le_half_radius
        (M := mBound) (R := R) (σ := σ) (t := t) (a := a) (b := b)
        (H := H) (z := z) ?_ ha₀ hHpos ?_ ha hb hH hR hz_half
    · simpa [mBound, ell] using hM
    · intro w hw
      simpa [mBound, ell] using hlog w hw
  have hcenter_mul :
      3 * ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
        3 * (Acenter + Bcenter * ell) := by
    exact mul_le_mul_of_nonneg_left (by simpa [ell] using hcenter)
      (by norm_num : (0 : ℝ) ≤ 3)
  calc
    ‖logDeriv riemannZeta z‖
        ≤ 2 * mBound + 3 * ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ :=
          hborel
    _ ≤ 2 * mBound + 3 * (Acenter + Bcenter * ell) := by
      nlinarith
    _ = (2 * Are + 3 * Acenter) +
          (2 * Bre + 3 * Bcenter) *
            Real.log (‖((σ : ℂ) + I * t)‖ + 3) := by
      simp [mBound, ell]
      ring

/-- Half-radius oscillation Borel-Carathéodory bound for `logDeriv ζ` with an
affine full-height logarithmic real-part input. -/
lemma borelCaratheodory_sub_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_affine_re_le_half_radius
    {Are Bre R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < Are + Bre * Real.log (‖((σ : ℂ) + I * t)‖ + 3))
    (ha₀ : 1 ≤ a) (hHpos : 0 < H)
    (hlog : ∀ w : ℂ, w ∈ verticalRegion a b H →
      (logDeriv riemannZeta w -
        logDeriv riemannZeta ((σ : ℂ) + I * t)).re ≤
          Are + Bre * Real.log (‖((σ : ℂ) + I * t)‖ + 3))
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R)
    (hz_half : ‖z - ((σ : ℂ) + I * t)‖ ≤ R / 2) :
    ‖logDeriv riemannZeta z -
        logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
      2 * Are + 2 * Bre * Real.log (‖((σ : ℂ) + I * t)‖ + 3) := by
  let ell : ℝ := Real.log (‖((σ : ℂ) + I * t)‖ + 3)
  let mBound : ℝ := Are + Bre * ell
  have hborel :
      ‖logDeriv riemannZeta z -
          logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤ 2 * mBound := by
    refine
      borelCaratheodory_sub_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le_half_radius
        (M := mBound) (R := R) (σ := σ) (t := t) (a := a) (b := b)
        (H := H) (z := z) ?_ ha₀ hHpos ?_ ha hb hH hR hz_half
    · simpa [mBound, ell] using hM
    · intro w hw
      simpa [mBound, ell] using hlog w hw
  calc
    ‖logDeriv riemannZeta z -
        logDeriv riemannZeta ((σ : ℂ) + I * t)‖
        ≤ 2 * mBound := hborel
    _ = 2 * Are + 2 * Bre *
          Real.log (‖((σ : ℂ) + I * t)‖ + 3) := by
      simp [mBound, ell]
      ring

/-- On a positive-height right half-strip, the signed logarithmic derivative
`-logDeriv ζ` is differentiable. -/
lemma differentiableOn_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re
    {a b H : ℝ} (ha : 1 ≤ a) (hH : 0 < H) :
    DifferentiableOn ℂ (fun z : ℂ => -logDeriv riemannZeta z)
      (verticalRegion a b H) :=
  (differentiableOn_logDeriv_riemannZeta_verticalRegion_of_one_le_re
    ha hH).neg

/-- On any bounded positive-height vertical band in the right half-plane,
`logDeriv ζ` has a finite norm bound.

This is the compact bounded-height patch needed by the zero-free-region chain:
it uses only compactness and the fact that ζ has no zeros on `Re(s) >= 1`.
The hard high-height estimate remains the logarithmic bound uniformly as
`|Im(s)| -> ∞`. -/
lemma exists_norm_logDeriv_riemannZeta_bound_on_compact_vertical_band
    {H T : ℝ} (hH : 0 < H) :
    ∃ C ≥ 0, ∀ z : ℂ, z.re ∈ Set.Icc (1 : ℝ) 2 →
      H ≤ |z.im| → |z.im| ≤ T →
      ‖logDeriv riemannZeta z‖ ≤ C := by
  let K : Set ℂ :=
    Set.Icc (1 : ℝ) 2 ×ℂ (Set.Icc H T ∪ Set.Icc (-T) (-H))
  have hK : IsCompact K := by
    have him : IsCompact (Set.Icc H T ∪ Set.Icc (-T) (-H)) :=
      (isCompact_Icc : IsCompact (Set.Icc H T)).union
        (isCompact_Icc : IsCompact (Set.Icc (-T) (-H)))
    simpa [K] using
      ((isCompact_Icc : IsCompact (Set.Icc (1 : ℝ) 2)).reProdIm him)
  have hKsub : K ⊆ verticalRegion 1 2 H := by
    intro z hz
    change z ∈ Set.Icc (1 : ℝ) 2 ×ℂ
      (Set.Icc H T ∪ Set.Icc (-T) (-H)) at hz
    rw [mem_reProdIm] at hz
    constructor
    · exact hz.1
    · rcases hz.2 with him | him
      · have hnonneg : 0 ≤ z.im := by linarith [hH, him.1]
        simpa [abs_of_nonneg hnonneg] using him.1
      · have hnonpos : z.im ≤ 0 := by linarith [hH, him.2]
        rw [abs_of_nonpos hnonpos]
        linarith [him.2]
  have hcont : ContinuousOn (fun z : ℂ => ‖logDeriv riemannZeta z‖) K := by
    exact ((differentiableOn_logDeriv_riemannZeta_verticalRegion_of_one_le_re
      (a := 1) (b := 2) (H := H) (by norm_num) hH).continuousOn.mono hKsub).norm
  rcases hK.bddAbove_image hcont with ⟨C₀, hC₀⟩
  refine ⟨max C₀ 0, le_max_right C₀ 0, ?_⟩
  intro z hzre hzH hzT
  have hzK : z ∈ K := by
    change z ∈ Set.Icc (1 : ℝ) 2 ×ℂ
      (Set.Icc H T ∪ Set.Icc (-T) (-H))
    rw [mem_reProdIm]
    constructor
    · exact hzre
    · by_cases hnonneg : 0 ≤ z.im
      · left
        constructor
        · simpa [abs_of_nonneg hnonneg] using hzH
        · simpa [abs_of_nonneg hnonneg] using hzT
      · right
        have hnonpos : z.im ≤ 0 := le_of_lt (lt_of_not_ge hnonneg)
        constructor
        · have hlower : -T ≤ z.im := by
            have h := (abs_le.mp hzT).1
            linarith
          exact hlower
        · have hupper : z.im ≤ -H := by
            have h : H ≤ -z.im := by
              simpa [abs_of_nonpos hnonpos] using hzH
            linarith
          exact hupper
  exact (hC₀ ⟨z, hzK, rfl⟩).trans (le_max_left C₀ 0)

/-- Signed compact bounded-height norm bound for `-logDeriv ζ`. -/
lemma exists_norm_neg_logDeriv_riemannZeta_bound_on_compact_vertical_band
    {H T : ℝ} (hH : 0 < H) :
    ∃ C ≥ 0, ∀ z : ℂ, z.re ∈ Set.Icc (1 : ℝ) 2 →
      H ≤ |z.im| → |z.im| ≤ T →
      ‖-logDeriv riemannZeta z‖ ≤ C := by
  rcases exists_norm_logDeriv_riemannZeta_bound_on_compact_vertical_band
      (H := H) (T := T) hH with ⟨C, hC_nonneg, hC⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro z hzre hzH hzT
  simpa using hC z hzre hzH hzT

/-- Coordinate compact bounded-height norm bound for `logDeriv ζ` on
`σ + i t`. -/
lemma exists_norm_logDeriv_riemannZeta_sigma_it_bound_on_compact_vertical_band
    {H T : ℝ} (hH : 0 < H) :
    ∃ C ≥ 0, ∀ σ t : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 →
      H ≤ |t| → |t| ≤ T →
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤ C := by
  rcases exists_norm_logDeriv_riemannZeta_bound_on_compact_vertical_band
      (H := H) (T := T) hH with ⟨C, hC_nonneg, hC⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro σ t hσ htH htT
  exact hC ((σ : ℂ) + I * t) (by simpa using hσ) (by simpa using htH)
    (by simpa using htT)

/-- Signed coordinate compact bounded-height norm bound for `-logDeriv ζ` on
`σ + i t`. -/
lemma exists_norm_neg_logDeriv_riemannZeta_sigma_it_bound_on_compact_vertical_band
    {H T : ℝ} (hH : 0 < H) :
    ∃ C ≥ 0, ∀ σ t : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 →
      H ≤ |t| → |t| ≤ T →
      ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤ C := by
  rcases exists_norm_neg_logDeriv_riemannZeta_bound_on_compact_vertical_band
      (H := H) (T := T) hH with ⟨C, hC_nonneg, hC⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro σ t hσ htH htT
  exact hC ((σ : ℂ) + I * t) (by simpa using hσ) (by simpa using htH)
    (by simpa using htT)

/-- Coordinate compact bounded-height norm bound for `logDeriv ζ` at the
shifted point `σ + 2it`. -/
lemma exists_norm_logDeriv_riemannZeta_sigma_two_it_bound_on_compact_vertical_band
    {H T : ℝ} (hH : 0 < H) :
    ∃ C ≥ 0, ∀ σ t : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 →
      H ≤ |t| → |t| ≤ T →
      ‖logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖ ≤ C := by
  have h2H : 0 < 2 * H := by positivity
  rcases exists_norm_logDeriv_riemannZeta_sigma_it_bound_on_compact_vertical_band
      (H := 2 * H) (T := 2 * T) h2H with ⟨C, hC_nonneg, hC⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro σ t hσ htH htT
  have hheight_lower : 2 * H ≤ |2 * t| := by
    calc
      2 * H ≤ 2 * |t| := by nlinarith
      _ = |2 * t| := by simp [abs_mul]
  have hheight_upper : |2 * t| ≤ 2 * T := by
    calc
      |2 * t| = 2 * |t| := by simp [abs_mul]
      _ ≤ 2 * T := by nlinarith
  have hbound := hC σ (2 * t) hσ hheight_lower hheight_upper
  have hrewrite :
      ((σ : ℂ) + I * (((2 * t : ℝ) : ℂ))) =
        ((σ : ℂ) + 2 * I * t) := by
    norm_num [Complex.ofReal_mul]
    ring
  calc
    ‖logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖
        = ‖logDeriv riemannZeta
            ((σ : ℂ) + I * (((2 * t : ℝ) : ℂ)))‖ := by
          rw [hrewrite]
    _ ≤ C := hbound

/-- Signed coordinate compact bounded-height norm bound for `-logDeriv ζ` at
the shifted point `σ + 2it`. -/
lemma exists_norm_neg_logDeriv_riemannZeta_sigma_two_it_bound_on_compact_vertical_band
    {H T : ℝ} (hH : 0 < H) :
    ∃ C ≥ 0, ∀ σ t : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 →
      H ≤ |t| → |t| ≤ T →
      ‖-logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖ ≤ C := by
  have h2H : 0 < 2 * H := by positivity
  rcases exists_norm_neg_logDeriv_riemannZeta_sigma_it_bound_on_compact_vertical_band
      (H := 2 * H) (T := 2 * T) h2H with ⟨C, hC_nonneg, hC⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro σ t hσ htH htT
  have hheight_lower : 2 * H ≤ |2 * t| := by
    calc
      2 * H ≤ 2 * |t| := by nlinarith
      _ = |2 * t| := by simp [abs_mul]
  have hheight_upper : |2 * t| ≤ 2 * T := by
    calc
      |2 * t| = 2 * |t| := by simp [abs_mul]
      _ ≤ 2 * T := by nlinarith
  have hbound := hC σ (2 * t) hσ hheight_lower hheight_upper
  have hrewrite :
      ((σ : ℂ) + I * (((2 * t : ℝ) : ℂ))) =
        ((σ : ℂ) + 2 * I * t) := by
    norm_num [Complex.ofReal_mul]
    ring
  calc
    ‖-logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖
        = ‖-logDeriv riemannZeta
            ((σ : ℂ) + I * (((2 * t : ℝ) : ℂ)))‖ := by
          rw [hrewrite]
    _ ≤ C := hbound

/-- Compact bounded-height real-part bound for the quotient convention
`-ζ'/ζ` at `σ + it`. -/
lemma exists_re_neg_deriv_div_riemannZeta_sigma_it_bound_on_compact_vertical_band
    {H T : ℝ} (hH : 0 < H) :
    ∃ C ≥ 0, ∀ σ t : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 →
      H ≤ |t| → |t| ≤ T →
      (-deriv riemannZeta ((σ : ℂ) + I * t) /
          riemannZeta ((σ : ℂ) + I * t)).re ≤ C := by
  rcases exists_norm_neg_logDeriv_riemannZeta_sigma_it_bound_on_compact_vertical_band
      (H := H) (T := T) hH with ⟨C, hC_nonneg, hC⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro σ t hσ htH htT
  let z : ℂ := (σ : ℂ) + I * t
  calc
    (-deriv riemannZeta z / riemannZeta z).re
        = (-logDeriv riemannZeta z).re :=
          neg_deriv_div_riemannZeta_re_eq_neg_logDeriv_re z
    _ ≤ ‖-logDeriv riemannZeta z‖ := Complex.re_le_norm _
    _ ≤ C := hC σ t hσ htH htT

/-- Compact bounded-height real-part bound for the quotient convention
`-ζ'/ζ` at the shifted point `σ + 2it`. -/
lemma exists_re_neg_deriv_div_riemannZeta_sigma_two_it_bound_on_compact_vertical_band
    {H T : ℝ} (hH : 0 < H) :
    ∃ C ≥ 0, ∀ σ t : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 →
      H ≤ |t| → |t| ≤ T →
      (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
          riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤ C := by
  rcases exists_norm_neg_logDeriv_riemannZeta_sigma_two_it_bound_on_compact_vertical_band
      (H := H) (T := T) hH with ⟨C, hC_nonneg, hC⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro σ t hσ htH htT
  let z : ℂ := (σ : ℂ) + 2 * I * t
  calc
    (-deriv riemannZeta z / riemannZeta z).re
        = (-logDeriv riemannZeta z).re :=
          neg_deriv_div_riemannZeta_re_eq_neg_logDeriv_re z
    _ ≤ ‖-logDeriv riemannZeta z‖ := Complex.re_le_norm _
    _ ≤ C := hC σ t hσ htH htT

/-- Compact patch from a high-height `B * log |t|` real-part quotient estimate
to an all-height affine `A + B' * log(|t| + 3)` estimate at `σ + it`. -/
lemma exists_re_neg_deriv_div_riemannZeta_sigma_it_affine_log_abs_add_three_bound_of_high_height_log_abs_bound
    {H T0 B : ℝ} (hH : 0 < H) (hHT0 : H ≤ T0) (hB : 0 ≤ B)
    (hhigh :
      ∀ σ t : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 → T0 ≤ |t| →
        (-deriv riemannZeta ((σ : ℂ) + I * t) /
            riemannZeta ((σ : ℂ) + I * t)).re ≤ B * Real.log |t|) :
    ∃ A B' : ℝ, 0 ≤ A ∧ 0 ≤ B' ∧
      ∀ σ t : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 → H ≤ |t| →
        (-deriv riemannZeta ((σ : ℂ) + I * t) /
            riemannZeta ((σ : ℂ) + I * t)).re ≤
          A + B' * Real.log (|t| + 3) := by
  rcases exists_re_neg_deriv_div_riemannZeta_sigma_it_bound_on_compact_vertical_band
      (H := H) (T := T0) hH with ⟨C, hC_nonneg, hC⟩
  refine ⟨C, B, hC_nonneg, hB, ?_⟩
  intro σ t hσ htH
  have hlog_nonneg : 0 ≤ Real.log (|t| + 3) := by
    exact Real.log_nonneg (by linarith [abs_nonneg t])
  by_cases ht_low : |t| ≤ T0
  · have hcompact := hC σ t hσ htH ht_low
    calc
      (-deriv riemannZeta ((σ : ℂ) + I * t) /
          riemannZeta ((σ : ℂ) + I * t)).re ≤ C := hcompact
      _ ≤ C + B * Real.log (|t| + 3) := by
        nlinarith [mul_nonneg hB hlog_nonneg]
  · have ht_high : T0 ≤ |t| := le_of_lt (lt_of_not_ge ht_low)
    have ht_pos : 0 < |t| := by linarith [hH, hHT0, ht_high]
    have hlog_le : Real.log |t| ≤ Real.log (|t| + 3) := by
      exact Real.log_le_log ht_pos (by linarith)
    calc
      (-deriv riemannZeta ((σ : ℂ) + I * t) /
          riemannZeta ((σ : ℂ) + I * t)).re
          ≤ B * Real.log |t| := hhigh σ t hσ ht_high
      _ ≤ B * Real.log (|t| + 3) :=
          mul_le_mul_of_nonneg_left hlog_le hB
      _ ≤ C + B * Real.log (|t| + 3) := by linarith

/-- Compact patch from a high-height `B * log |t|` real-part quotient estimate
to an all-height affine estimate at the shifted point `σ + 2it`. -/
lemma exists_re_neg_deriv_div_riemannZeta_sigma_two_it_affine_log_abs_add_three_bound_of_high_height_log_abs_bound
    {H T0 B : ℝ} (hH : 0 < H) (hHT0 : H ≤ T0) (hB : 0 ≤ B)
    (hhigh :
      ∀ σ t : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 → T0 ≤ |t| →
        (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
            riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤ B * Real.log |t|) :
    ∃ A B' : ℝ, 0 ≤ A ∧ 0 ≤ B' ∧
      ∀ σ t : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 → H ≤ |t| →
        (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
            riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤
          A + B' * Real.log (|t| + 3) := by
  rcases exists_re_neg_deriv_div_riemannZeta_sigma_two_it_bound_on_compact_vertical_band
      (H := H) (T := T0) hH with ⟨C, hC_nonneg, hC⟩
  refine ⟨C, B, hC_nonneg, hB, ?_⟩
  intro σ t hσ htH
  have hlog_nonneg : 0 ≤ Real.log (|t| + 3) := by
    exact Real.log_nonneg (by linarith [abs_nonneg t])
  by_cases ht_low : |t| ≤ T0
  · have hcompact := hC σ t hσ htH ht_low
    calc
      (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
          riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤ C := hcompact
      _ ≤ C + B * Real.log (|t| + 3) := by
        nlinarith [mul_nonneg hB hlog_nonneg]
  · have ht_high : T0 ≤ |t| := le_of_lt (lt_of_not_ge ht_low)
    have ht_pos : 0 < |t| := by linarith [hH, hHT0, ht_high]
    have hlog_le : Real.log |t| ≤ Real.log (|t| + 3) := by
      exact Real.log_le_log ht_pos (by linarith)
    calc
      (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
          riemannZeta ((σ : ℂ) + 2 * I * t)).re
          ≤ B * Real.log |t| := hhigh σ t hσ ht_high
      _ ≤ B * Real.log (|t| + 3) :=
          mul_le_mul_of_nonneg_left hlog_le hB
      _ ≤ C + B * Real.log (|t| + 3) := by linarith

/-- Compact patch preserving the exact `C * log |t|` scale for the real-part
quotient estimate at `σ + it`, provided the patched height starts at
`H >= 3`. -/
lemma exists_re_neg_deriv_div_riemannZeta_sigma_it_log_abs_bound_of_high_height_log_abs_bound
    {H T0 B : ℝ} (hH3 : 3 ≤ H) (hB : 0 ≤ B)
    (hhigh :
      ∀ σ t : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 → T0 ≤ |t| →
        (-deriv riemannZeta ((σ : ℂ) + I * t) /
            riemannZeta ((σ : ℂ) + I * t)).re ≤ B * Real.log |t|) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ σ t : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 → H ≤ |t| →
        (-deriv riemannZeta ((σ : ℂ) + I * t) /
            riemannZeta ((σ : ℂ) + I * t)).re ≤ C * Real.log |t| := by
  have hHpos : 0 < H := by linarith
  rcases exists_re_neg_deriv_div_riemannZeta_sigma_it_bound_on_compact_vertical_band
      (H := H) (T := T0) hHpos with ⟨C₀, hC₀_nonneg, hC₀⟩
  refine ⟨C₀ + B, add_nonneg hC₀_nonneg hB, ?_⟩
  intro σ t hσ htH
  have hlog_ge_one : 1 ≤ Real.log |t| :=
    (log_abs_gt_one_of_three_le (hH3.trans htH)).le
  have hlog_nonneg : 0 ≤ Real.log |t| := by linarith
  by_cases ht_low : |t| ≤ T0
  · have hcompact := hC₀ σ t hσ htH ht_low
    have hC₀_le : C₀ ≤ C₀ * Real.log |t| := by
      calc
        C₀ = C₀ * 1 := by ring
        _ ≤ C₀ * Real.log |t| :=
            mul_le_mul_of_nonneg_left hlog_ge_one hC₀_nonneg
    calc
      (-deriv riemannZeta ((σ : ℂ) + I * t) /
          riemannZeta ((σ : ℂ) + I * t)).re ≤ C₀ := hcompact
      _ ≤ C₀ * Real.log |t| := hC₀_le
      _ ≤ (C₀ + B) * Real.log |t| := by
        nlinarith [mul_nonneg hB hlog_nonneg]
  · have ht_high : T0 ≤ |t| := le_of_lt (lt_of_not_ge ht_low)
    calc
      (-deriv riemannZeta ((σ : ℂ) + I * t) /
          riemannZeta ((σ : ℂ) + I * t)).re
          ≤ B * Real.log |t| := hhigh σ t hσ ht_high
      _ ≤ (C₀ + B) * Real.log |t| := by
        nlinarith [mul_nonneg hC₀_nonneg hlog_nonneg]

/-- Objective-shaped vertical logarithmic bound wrapper for the real-part
quotient convention `Re(-zeta'/zeta)` at `sigma + it`.  This packages the
compact-height patch in the form consumed by the classical zero-free-region
contradiction route, while keeping the high-height analytic estimate explicit
as an input. -/
lemma exists_re_neg_deriv_div_riemannZeta_vertical_log_bound_of_high_height_log_abs_bound
    {T0 B : ℝ} (hB : 0 ≤ B)
    (hhigh :
      ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → T0 ≤ |t| →
        (-deriv riemannZeta ((σ : ℂ) + I * t) /
            riemannZeta ((σ : ℂ) + I * t)).re ≤ B * Real.log |t|) :
    ∃ C T0' : ℝ, 0 ≤ C ∧ 3 ≤ T0' ∧
      ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → T0' ≤ |t| →
        (-deriv riemannZeta ((σ : ℂ) + I * t) /
            riemannZeta ((σ : ℂ) + I * t)).re ≤ C * Real.log |t| := by
  rcases exists_re_neg_deriv_div_riemannZeta_sigma_it_log_abs_bound_of_high_height_log_abs_bound
      (H := 3) (T0 := T0) (B := B) (by norm_num) hB
      (by
        intro σ t hσ ht
        exact hhigh σ t hσ.1 hσ.2 ht) with
    ⟨C, hC_nonneg, hbound⟩
  refine ⟨C, 3, hC_nonneg, by norm_num, ?_⟩
  intro σ t hσ_left hσ_right ht
  exact hbound σ t ⟨hσ_left, hσ_right⟩ ht

/-- Compact patch preserving the exact `C * log |t|` scale for the shifted
real-part quotient estimate at `σ + 2it`, provided `H >= 3`. -/
lemma exists_re_neg_deriv_div_riemannZeta_sigma_two_it_log_abs_bound_of_high_height_log_abs_bound
    {H T0 B : ℝ} (hH3 : 3 ≤ H) (hB : 0 ≤ B)
    (hhigh :
      ∀ σ t : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 → T0 ≤ |t| →
        (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
            riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤ B * Real.log |t|) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ σ t : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 → H ≤ |t| →
        (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
            riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤ C * Real.log |t| := by
  have hHpos : 0 < H := by linarith
  rcases exists_re_neg_deriv_div_riemannZeta_sigma_two_it_bound_on_compact_vertical_band
      (H := H) (T := T0) hHpos with ⟨C₀, hC₀_nonneg, hC₀⟩
  refine ⟨C₀ + B, add_nonneg hC₀_nonneg hB, ?_⟩
  intro σ t hσ htH
  have hlog_ge_one : 1 ≤ Real.log |t| :=
    (log_abs_gt_one_of_three_le (hH3.trans htH)).le
  have hlog_nonneg : 0 ≤ Real.log |t| := by linarith
  by_cases ht_low : |t| ≤ T0
  · have hcompact := hC₀ σ t hσ htH ht_low
    have hC₀_le : C₀ ≤ C₀ * Real.log |t| := by
      calc
        C₀ = C₀ * 1 := by ring
        _ ≤ C₀ * Real.log |t| :=
            mul_le_mul_of_nonneg_left hlog_ge_one hC₀_nonneg
    calc
      (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
          riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤ C₀ := hcompact
      _ ≤ C₀ * Real.log |t| := hC₀_le
      _ ≤ (C₀ + B) * Real.log |t| := by
        nlinarith [mul_nonneg hB hlog_nonneg]
  · have ht_high : T0 ≤ |t| := le_of_lt (lt_of_not_ge ht_low)
    calc
      (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
          riemannZeta ((σ : ℂ) + 2 * I * t)).re
          ≤ B * Real.log |t| := hhigh σ t hσ ht_high
      _ ≤ (C₀ + B) * Real.log |t| := by
        nlinarith [mul_nonneg hC₀_nonneg hlog_nonneg]

/-- Objective-shaped vertical logarithmic bound wrapper for the shifted
real-part quotient convention `Re(-zeta'/zeta)` at `sigma + 2it`.  This is the
shifted input shape used by the 3-4-1 inequality in the quantitative
zero-free-region route. -/
lemma exists_re_neg_deriv_div_riemannZeta_shifted_vertical_log_bound_of_high_height_log_abs_bound
    {T0 B : ℝ} (hB : 0 ≤ B)
    (hhigh :
      ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → T0 ≤ |t| →
        (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
            riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤ B * Real.log |t|) :
    ∃ C T0' : ℝ, 0 ≤ C ∧ 3 ≤ T0' ∧
      ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → T0' ≤ |t| →
        (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
            riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤ C * Real.log |t| := by
  rcases exists_re_neg_deriv_div_riemannZeta_sigma_two_it_log_abs_bound_of_high_height_log_abs_bound
      (H := 3) (T0 := T0) (B := B) (by norm_num) hB
      (by
        intro σ t hσ ht
        exact hhigh σ t hσ.1 hσ.2 ht) with
    ⟨C, hC_nonneg, hbound⟩
  refine ⟨C, 3, hC_nonneg, by norm_num, ?_⟩
  intro σ t hσ_left hσ_right ht
  exact hbound σ t ⟨hσ_left, hσ_right⟩ ht

/-- Norm-to-real-part high-height bridge for the standard vertical point
`sigma + it`.  A future norm estimate for `logDeriv zeta` immediately supplies
the real-part quotient estimate consumed by the 3-4-1 zero-free-region route. -/
lemma exists_re_neg_deriv_div_riemannZeta_vertical_log_bound_of_norm_high_height_log_abs_bound
    {T0 B : ℝ} (hB : 0 ≤ B)
    (hhigh :
      ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → T0 ≤ |t| →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤ B * Real.log |t|) :
    ∃ C T0' : ℝ, 0 ≤ C ∧ 3 ≤ T0' ∧
      ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → T0' ≤ |t| →
        (-deriv riemannZeta ((σ : ℂ) + I * t) /
            riemannZeta ((σ : ℂ) + I * t)).re ≤ C * Real.log |t| := by
  refine
    exists_re_neg_deriv_div_riemannZeta_vertical_log_bound_of_high_height_log_abs_bound
      (T0 := T0) (B := B) hB ?_
  intro σ t hσ_left hσ_right ht
  let z : ℂ := (σ : ℂ) + I * t
  calc
    (-deriv riemannZeta z / riemannZeta z).re
        ≤ ‖-deriv riemannZeta z / riemannZeta z‖ := Complex.re_le_norm _
    _ = ‖logDeriv riemannZeta z‖ :=
        norm_neg_deriv_div_riemannZeta_eq_norm_logDeriv z
    _ ≤ B * Real.log |t| := by
        simpa [z] using hhigh σ t hσ_left hσ_right ht

/-- Shifted norm-to-real-part high-height bridge for the 3-4-1 point
`sigma + 2it`. -/
lemma exists_re_neg_deriv_div_riemannZeta_shifted_vertical_log_bound_of_norm_high_height_log_abs_bound
    {T0 B : ℝ} (hB : 0 ≤ B)
    (hhigh :
      ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → T0 ≤ |t| →
        ‖logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖ ≤ B * Real.log |t|) :
    ∃ C T0' : ℝ, 0 ≤ C ∧ 3 ≤ T0' ∧
      ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → T0' ≤ |t| →
        (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
            riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤ C * Real.log |t| := by
  refine
    exists_re_neg_deriv_div_riemannZeta_shifted_vertical_log_bound_of_high_height_log_abs_bound
      (T0 := T0) (B := B) hB ?_
  intro σ t hσ_left hσ_right ht
  let z : ℂ := (σ : ℂ) + 2 * I * t
  calc
    (-deriv riemannZeta z / riemannZeta z).re
        ≤ ‖-deriv riemannZeta z / riemannZeta z‖ := Complex.re_le_norm _
    _ = ‖logDeriv riemannZeta z‖ :=
        norm_neg_deriv_div_riemannZeta_eq_norm_logDeriv z
    _ ≤ B * Real.log |t| := by
        simpa [z] using hhigh σ t hσ_left hσ_right ht

/-- Compact patch from a high-height `B * log |t|` estimate to an all-height
affine `A + B' * log(|t| + 3)` estimate for `logDeriv ζ`.

The low-height range `H <= |t| <= T0` is supplied by compactness; the high
range uses the provided zeta-specific estimate. -/
lemma exists_norm_logDeriv_riemannZeta_sigma_it_affine_log_abs_add_three_bound_of_high_height_log_abs_bound
    {H T0 B : ℝ} (hH : 0 < H) (hHT0 : H ≤ T0) (hB : 0 ≤ B)
    (hhigh :
      ∀ σ t : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 → T0 ≤ |t| →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤ B * Real.log |t|) :
    ∃ A B' : ℝ, 0 ≤ A ∧ 0 ≤ B' ∧
      ∀ σ t : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 → H ≤ |t| →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          A + B' * Real.log (|t| + 3) := by
  rcases exists_norm_logDeriv_riemannZeta_sigma_it_bound_on_compact_vertical_band
      (H := H) (T := T0) hH with ⟨C, hC_nonneg, hC⟩
  refine ⟨C, B, hC_nonneg, hB, ?_⟩
  intro σ t hσ htH
  have hlog_nonneg : 0 ≤ Real.log (|t| + 3) := by
    exact Real.log_nonneg (by linarith [abs_nonneg t])
  by_cases ht_low : |t| ≤ T0
  · have hcompact := hC σ t hσ htH ht_low
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤ C := hcompact
      _ ≤ C + B * Real.log (|t| + 3) := by
        nlinarith [mul_nonneg hB hlog_nonneg]
  · have ht_high : T0 ≤ |t| := le_of_lt (lt_of_not_ge ht_low)
    have ht_pos : 0 < |t| := by linarith [hH, hHT0, ht_high]
    have hlog_le : Real.log |t| ≤ Real.log (|t| + 3) := by
      exact Real.log_le_log ht_pos (by linarith)
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖
          ≤ B * Real.log |t| := hhigh σ t hσ ht_high
      _ ≤ B * Real.log (|t| + 3) :=
          mul_le_mul_of_nonneg_left hlog_le hB
      _ ≤ C + B * Real.log (|t| + 3) := by linarith

/-- Signed compact patch from a high-height `B * log |t|` estimate to an
all-height affine `A + B' * log(|t| + 3)` estimate for `-logDeriv ζ`. -/
lemma exists_norm_neg_logDeriv_riemannZeta_sigma_it_affine_log_abs_add_three_bound_of_high_height_log_abs_bound
    {H T0 B : ℝ} (hH : 0 < H) (hHT0 : H ≤ T0) (hB : 0 ≤ B)
    (hhigh :
      ∀ σ t : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 → T0 ≤ |t| →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤ B * Real.log |t|) :
    ∃ A B' : ℝ, 0 ≤ A ∧ 0 ≤ B' ∧
      ∀ σ t : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 → H ≤ |t| →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
          A + B' * Real.log (|t| + 3) := by
  rcases exists_norm_neg_logDeriv_riemannZeta_sigma_it_bound_on_compact_vertical_band
      (H := H) (T := T0) hH with ⟨C, hC_nonneg, hC⟩
  refine ⟨C, B, hC_nonneg, hB, ?_⟩
  intro σ t hσ htH
  have hlog_nonneg : 0 ≤ Real.log (|t| + 3) := by
    exact Real.log_nonneg (by linarith [abs_nonneg t])
  by_cases ht_low : |t| ≤ T0
  · have hcompact := hC σ t hσ htH ht_low
    calc
      ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤ C := hcompact
      _ ≤ C + B * Real.log (|t| + 3) := by
        nlinarith [mul_nonneg hB hlog_nonneg]
  · have ht_high : T0 ≤ |t| := le_of_lt (lt_of_not_ge ht_low)
    have ht_pos : 0 < |t| := by linarith [hH, hHT0, ht_high]
    have hlog_le : Real.log |t| ≤ Real.log (|t| + 3) := by
      exact Real.log_le_log ht_pos (by linarith)
    calc
      ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖
          ≤ B * Real.log |t| := hhigh σ t hσ ht_high
      _ ≤ B * Real.log (|t| + 3) :=
          mul_le_mul_of_nonneg_left hlog_le hB
      _ ≤ C + B * Real.log (|t| + 3) := by linarith

/-- Compact patch from a high-height `B * log |t|` estimate to an all-height
affine `A + B' * log(|t| + 3)` estimate for the shifted point `σ + 2it`. -/
lemma exists_norm_logDeriv_riemannZeta_sigma_two_it_affine_log_abs_add_three_bound_of_high_height_log_abs_bound
    {H T0 B : ℝ} (hH : 0 < H) (hHT0 : H ≤ T0) (hB : 0 ≤ B)
    (hhigh :
      ∀ σ t : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 → T0 ≤ |t| →
        ‖logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖ ≤ B * Real.log |t|) :
    ∃ A B' : ℝ, 0 ≤ A ∧ 0 ≤ B' ∧
      ∀ σ t : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 → H ≤ |t| →
        ‖logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖ ≤
          A + B' * Real.log (|t| + 3) := by
  have h2H : 0 < 2 * H := by positivity
  rcases exists_norm_logDeriv_riemannZeta_sigma_it_bound_on_compact_vertical_band
      (H := 2 * H) (T := 2 * T0) h2H with ⟨C, hC_nonneg, hC⟩
  refine ⟨C, B, hC_nonneg, hB, ?_⟩
  intro σ t hσ htH
  have hlog_nonneg : 0 ≤ Real.log (|t| + 3) := by
    exact Real.log_nonneg (by linarith [abs_nonneg t])
  by_cases ht_low : |t| ≤ T0
  · have hheight_lower : 2 * H ≤ |2 * t| := by
      calc
        2 * H ≤ 2 * |t| := by nlinarith
        _ = |2 * t| := by simp [abs_mul]
    have hheight_upper : |2 * t| ≤ 2 * T0 := by
      calc
        |2 * t| = 2 * |t| := by simp [abs_mul]
        _ ≤ 2 * T0 := by nlinarith
    have hcompact := hC σ (2 * t) hσ hheight_lower hheight_upper
    have hrewrite :
        ((σ : ℂ) + I * (((2 * t : ℝ) : ℂ))) =
          ((σ : ℂ) + 2 * I * t) := by
      norm_num [Complex.ofReal_mul]
      ring
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖
          = ‖logDeriv riemannZeta
              ((σ : ℂ) + I * (((2 * t : ℝ) : ℂ)))‖ := by
            rw [hrewrite]
      _ ≤ C := hcompact
      _ ≤ C + B * Real.log (|t| + 3) := by
        nlinarith [mul_nonneg hB hlog_nonneg]
  · have ht_high : T0 ≤ |t| := le_of_lt (lt_of_not_ge ht_low)
    have ht_pos : 0 < |t| := by linarith [hH, hHT0, ht_high]
    have hlog_le : Real.log |t| ≤ Real.log (|t| + 3) := by
      exact Real.log_le_log ht_pos (by linarith)
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖
          ≤ B * Real.log |t| := hhigh σ t hσ ht_high
      _ ≤ B * Real.log (|t| + 3) :=
          mul_le_mul_of_nonneg_left hlog_le hB
      _ ≤ C + B * Real.log (|t| + 3) := by linarith

/-- Signed compact patch from a high-height `B * log |t|` estimate to an
all-height affine estimate for `-logDeriv ζ` at `σ + 2it`. -/
lemma exists_norm_neg_logDeriv_riemannZeta_sigma_two_it_affine_log_abs_add_three_bound_of_high_height_log_abs_bound
    {H T0 B : ℝ} (hH : 0 < H) (hHT0 : H ≤ T0) (hB : 0 ≤ B)
    (hhigh :
      ∀ σ t : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 → T0 ≤ |t| →
        ‖-logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖ ≤
          B * Real.log |t|) :
    ∃ A B' : ℝ, 0 ≤ A ∧ 0 ≤ B' ∧
      ∀ σ t : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 → H ≤ |t| →
        ‖-logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖ ≤
          A + B' * Real.log (|t| + 3) := by
  have h2H : 0 < 2 * H := by positivity
  rcases exists_norm_neg_logDeriv_riemannZeta_sigma_it_bound_on_compact_vertical_band
      (H := 2 * H) (T := 2 * T0) h2H with ⟨C, hC_nonneg, hC⟩
  refine ⟨C, B, hC_nonneg, hB, ?_⟩
  intro σ t hσ htH
  have hlog_nonneg : 0 ≤ Real.log (|t| + 3) := by
    exact Real.log_nonneg (by linarith [abs_nonneg t])
  by_cases ht_low : |t| ≤ T0
  · have hheight_lower : 2 * H ≤ |2 * t| := by
      calc
        2 * H ≤ 2 * |t| := by nlinarith
        _ = |2 * t| := by simp [abs_mul]
    have hheight_upper : |2 * t| ≤ 2 * T0 := by
      calc
        |2 * t| = 2 * |t| := by simp [abs_mul]
        _ ≤ 2 * T0 := by nlinarith
    have hcompact := hC σ (2 * t) hσ hheight_lower hheight_upper
    have hrewrite :
        ((σ : ℂ) + I * (((2 * t : ℝ) : ℂ))) =
          ((σ : ℂ) + 2 * I * t) := by
      norm_num [Complex.ofReal_mul]
      ring
    calc
      ‖-logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖
          = ‖-logDeriv riemannZeta
              ((σ : ℂ) + I * (((2 * t : ℝ) : ℂ)))‖ := by
            rw [hrewrite]
      _ ≤ C := hcompact
      _ ≤ C + B * Real.log (|t| + 3) := by
        nlinarith [mul_nonneg hB hlog_nonneg]
  · have ht_high : T0 ≤ |t| := le_of_lt (lt_of_not_ge ht_low)
    have ht_pos : 0 < |t| := by linarith [hH, hHT0, ht_high]
    have hlog_le : Real.log |t| ≤ Real.log (|t| + 3) := by
      exact Real.log_le_log ht_pos (by linarith)
    calc
      ‖-logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖
          ≤ B * Real.log |t| := hhigh σ t hσ ht_high
      _ ≤ B * Real.log (|t| + 3) :=
          mul_le_mul_of_nonneg_left hlog_le hB
      _ ≤ C + B * Real.log (|t| + 3) := by linarith

/-- Compact patch preserving the exact `C * log |t|` scale for the norm of
`logDeriv ζ` at `σ + it`, provided the patched range starts at `H >= 3`. -/
lemma exists_norm_logDeriv_riemannZeta_sigma_it_log_abs_bound_of_high_height_log_abs_bound
    {H T0 B : ℝ} (hH3 : 3 ≤ H) (hB : 0 ≤ B)
    (hhigh :
      ∀ σ t : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 → T0 ≤ |t| →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤ B * Real.log |t|) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ σ t : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 → H ≤ |t| →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤ C * Real.log |t| := by
  have hHpos : 0 < H := by linarith
  rcases exists_norm_logDeriv_riemannZeta_sigma_it_bound_on_compact_vertical_band
      (H := H) (T := T0) hHpos with ⟨C₀, hC₀_nonneg, hC₀⟩
  refine ⟨C₀ + B, add_nonneg hC₀_nonneg hB, ?_⟩
  intro σ t hσ htH
  have hlog_ge_one : 1 ≤ Real.log |t| :=
    (log_abs_gt_one_of_three_le (hH3.trans htH)).le
  have hlog_nonneg : 0 ≤ Real.log |t| := by linarith
  by_cases ht_low : |t| ≤ T0
  · have hcompact := hC₀ σ t hσ htH ht_low
    have hC₀_le : C₀ ≤ C₀ * Real.log |t| := by
      calc
        C₀ = C₀ * 1 := by ring
        _ ≤ C₀ * Real.log |t| :=
            mul_le_mul_of_nonneg_left hlog_ge_one hC₀_nonneg
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤ C₀ := hcompact
      _ ≤ C₀ * Real.log |t| := hC₀_le
      _ ≤ (C₀ + B) * Real.log |t| := by
        nlinarith [mul_nonneg hB hlog_nonneg]
  · have ht_high : T0 ≤ |t| := le_of_lt (lt_of_not_ge ht_low)
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖
          ≤ B * Real.log |t| := hhigh σ t hσ ht_high
      _ ≤ (C₀ + B) * Real.log |t| := by
        nlinarith [mul_nonneg hC₀_nonneg hlog_nonneg]

/-- Signed compact patch preserving the exact `C * log |t|` scale for
`-logDeriv ζ` at `σ + it`, provided `H >= 3`. -/
lemma exists_norm_neg_logDeriv_riemannZeta_sigma_it_log_abs_bound_of_high_height_log_abs_bound
    {H T0 B : ℝ} (hH3 : 3 ≤ H) (hB : 0 ≤ B)
    (hhigh :
      ∀ σ t : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 → T0 ≤ |t| →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤ B * Real.log |t|) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ σ t : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 → H ≤ |t| →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤ C * Real.log |t| := by
  have hHpos : 0 < H := by linarith
  rcases exists_norm_neg_logDeriv_riemannZeta_sigma_it_bound_on_compact_vertical_band
      (H := H) (T := T0) hHpos with ⟨C₀, hC₀_nonneg, hC₀⟩
  refine ⟨C₀ + B, add_nonneg hC₀_nonneg hB, ?_⟩
  intro σ t hσ htH
  have hlog_ge_one : 1 ≤ Real.log |t| :=
    (log_abs_gt_one_of_three_le (hH3.trans htH)).le
  have hlog_nonneg : 0 ≤ Real.log |t| := by linarith
  by_cases ht_low : |t| ≤ T0
  · have hcompact := hC₀ σ t hσ htH ht_low
    have hC₀_le : C₀ ≤ C₀ * Real.log |t| := by
      calc
        C₀ = C₀ * 1 := by ring
        _ ≤ C₀ * Real.log |t| :=
            mul_le_mul_of_nonneg_left hlog_ge_one hC₀_nonneg
    calc
      ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤ C₀ := hcompact
      _ ≤ C₀ * Real.log |t| := hC₀_le
      _ ≤ (C₀ + B) * Real.log |t| := by
        nlinarith [mul_nonneg hB hlog_nonneg]
  · have ht_high : T0 ≤ |t| := le_of_lt (lt_of_not_ge ht_low)
    calc
      ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖
          ≤ B * Real.log |t| := hhigh σ t hσ ht_high
      _ ≤ (C₀ + B) * Real.log |t| := by
        nlinarith [mul_nonneg hC₀_nonneg hlog_nonneg]

/-- Objective-shaped vertical logarithmic bound wrapper: a future high-height
`B * log |t|` estimate on the boundary strip `1 <= sigma <= 2` patches with the
compact bounded-height theorem to give the standard existential form used by
the quantitative zero-free-region chain.  This theorem packages the shape of
the hard estimate; it does not prove the zeta-specific high-height input. -/
lemma exists_norm_logDeriv_riemannZeta_vertical_log_bound_of_high_height_log_abs_bound
    {T0 B : ℝ} (hB : 0 ≤ B)
    (hhigh :
      ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → T0 ≤ |t| →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤ B * Real.log |t|) :
    ∃ C T0' : ℝ, 0 ≤ C ∧ 3 ≤ T0' ∧
      ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → T0' ≤ |t| →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤ C * Real.log |t| := by
  rcases exists_norm_logDeriv_riemannZeta_sigma_it_log_abs_bound_of_high_height_log_abs_bound
      (H := 3) (T0 := T0) (B := B) (by norm_num) hB
      (by
        intro σ t hσ ht
        exact hhigh σ t hσ.1 hσ.2 ht) with
    ⟨C, hC_nonneg, hbound⟩
  refine ⟨C, 3, hC_nonneg, by norm_num, ?_⟩
  intro σ t hσ_left hσ_right ht
  exact hbound σ t ⟨hσ_left, hσ_right⟩ ht

/-- Signed objective-shaped version of the vertical logarithmic bound wrapper
for `-logDeriv zeta`.  The analytic high-height estimate remains an explicit
input; the theorem only proves the compact-height patching and API shape. -/
lemma exists_norm_neg_logDeriv_riemannZeta_vertical_log_bound_of_high_height_log_abs_bound
    {T0 B : ℝ} (hB : 0 ≤ B)
    (hhigh :
      ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → T0 ≤ |t| →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤ B * Real.log |t|) :
    ∃ C T0' : ℝ, 0 ≤ C ∧ 3 ≤ T0' ∧
      ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → T0' ≤ |t| →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤ C * Real.log |t| := by
  rcases exists_norm_neg_logDeriv_riemannZeta_sigma_it_log_abs_bound_of_high_height_log_abs_bound
      (H := 3) (T0 := T0) (B := B) (by norm_num) hB
      (by
        intro σ t hσ ht
        exact hhigh σ t hσ.1 hσ.2 ht) with
    ⟨C, hC_nonneg, hbound⟩
  refine ⟨C, 3, hC_nonneg, by norm_num, ?_⟩
  intro σ t hσ_left hσ_right ht
  exact hbound σ t ⟨hσ_left, hσ_right⟩ ht

/-- Compact patch preserving the exact `C * log |t|` scale for the norm of
`logDeriv ζ` at `σ + 2it`, provided `H >= 3`. -/
lemma exists_norm_logDeriv_riemannZeta_sigma_two_it_log_abs_bound_of_high_height_log_abs_bound
    {H T0 B : ℝ} (hH3 : 3 ≤ H) (hB : 0 ≤ B)
    (hhigh :
      ∀ σ t : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 → T0 ≤ |t| →
        ‖logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖ ≤ B * Real.log |t|) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ σ t : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 → H ≤ |t| →
        ‖logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖ ≤ C * Real.log |t| := by
  have hHpos : 0 < H := by linarith
  rcases exists_norm_logDeriv_riemannZeta_sigma_two_it_bound_on_compact_vertical_band
      (H := H) (T := T0) hHpos with ⟨C₀, hC₀_nonneg, hC₀⟩
  refine ⟨C₀ + B, add_nonneg hC₀_nonneg hB, ?_⟩
  intro σ t hσ htH
  have hlog_ge_one : 1 ≤ Real.log |t| :=
    (log_abs_gt_one_of_three_le (hH3.trans htH)).le
  have hlog_nonneg : 0 ≤ Real.log |t| := by linarith
  by_cases ht_low : |t| ≤ T0
  · have hcompact := hC₀ σ t hσ htH ht_low
    have hC₀_le : C₀ ≤ C₀ * Real.log |t| := by
      calc
        C₀ = C₀ * 1 := by ring
        _ ≤ C₀ * Real.log |t| :=
            mul_le_mul_of_nonneg_left hlog_ge_one hC₀_nonneg
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖ ≤ C₀ := hcompact
      _ ≤ C₀ * Real.log |t| := hC₀_le
      _ ≤ (C₀ + B) * Real.log |t| := by
        nlinarith [mul_nonneg hB hlog_nonneg]
  · have ht_high : T0 ≤ |t| := le_of_lt (lt_of_not_ge ht_low)
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖
          ≤ B * Real.log |t| := hhigh σ t hσ ht_high
      _ ≤ (C₀ + B) * Real.log |t| := by
        nlinarith [mul_nonneg hC₀_nonneg hlog_nonneg]

/-- Signed compact patch preserving the exact `C * log |t|` scale for
`-logDeriv ζ` at `σ + 2it`, provided `H >= 3`. -/
lemma exists_norm_neg_logDeriv_riemannZeta_sigma_two_it_log_abs_bound_of_high_height_log_abs_bound
    {H T0 B : ℝ} (hH3 : 3 ≤ H) (hB : 0 ≤ B)
    (hhigh :
      ∀ σ t : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 → T0 ≤ |t| →
        ‖-logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖ ≤ B * Real.log |t|) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ σ t : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 → H ≤ |t| →
        ‖-logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖ ≤ C * Real.log |t| := by
  have hHpos : 0 < H := by linarith
  rcases exists_norm_neg_logDeriv_riemannZeta_sigma_two_it_bound_on_compact_vertical_band
      (H := H) (T := T0) hHpos with ⟨C₀, hC₀_nonneg, hC₀⟩
  refine ⟨C₀ + B, add_nonneg hC₀_nonneg hB, ?_⟩
  intro σ t hσ htH
  have hlog_ge_one : 1 ≤ Real.log |t| :=
    (log_abs_gt_one_of_three_le (hH3.trans htH)).le
  have hlog_nonneg : 0 ≤ Real.log |t| := by linarith
  by_cases ht_low : |t| ≤ T0
  · have hcompact := hC₀ σ t hσ htH ht_low
    have hC₀_le : C₀ ≤ C₀ * Real.log |t| := by
      calc
        C₀ = C₀ * 1 := by ring
        _ ≤ C₀ * Real.log |t| :=
            mul_le_mul_of_nonneg_left hlog_ge_one hC₀_nonneg
    calc
      ‖-logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖ ≤ C₀ := hcompact
      _ ≤ C₀ * Real.log |t| := hC₀_le
      _ ≤ (C₀ + B) * Real.log |t| := by
        nlinarith [mul_nonneg hB hlog_nonneg]
  · have ht_high : T0 ≤ |t| := le_of_lt (lt_of_not_ge ht_low)
    calc
      ‖-logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖
          ≤ B * Real.log |t| := hhigh σ t hσ ht_high
      _ ≤ (C₀ + B) * Real.log |t| := by
        nlinarith [mul_nonneg hC₀_nonneg hlog_nonneg]

/-- A future high-height norm estimate at the ordinary vertical point
`sigma + iu` automatically yields the shifted norm estimate at `sigma + 2it`
needed by the 3-4-1 inequality, after absorbing `log |2t| <= 2 log |t|`. -/
lemma exists_norm_logDeriv_riemannZeta_shifted_vertical_log_bound_of_vertical_log_bound
    {T0 B : ℝ} (hB : 0 ≤ B)
    (hhigh :
      ∀ σ u : ℝ, 1 ≤ σ → σ ≤ 2 → T0 ≤ |u| →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * u)‖ ≤ B * Real.log |u|) :
    ∃ C T0' : ℝ, 0 ≤ C ∧ 3 ≤ T0' ∧
      ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → T0' ≤ |t| →
        ‖logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖ ≤ C * Real.log |t| := by
  have hB2 : 0 ≤ 2 * B := by nlinarith
  let T1 : ℝ := max T0 3
  have hshift :
      ∀ σ t : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 → T1 ≤ |t| →
        ‖logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖ ≤
          (2 * B) * Real.log |t| := by
    intro σ t hσ ht
    have hT0_le_abs_t : T0 ≤ |t| := (le_max_left T0 (3 : ℝ)).trans ht
    have hthree_le_abs_t : 3 ≤ |t| := (le_max_right T0 (3 : ℝ)).trans ht
    have htwo_le_abs_t : 2 ≤ |t| := by linarith
    have hT0_le_abs_two_t : T0 ≤ |2 * t| := by
      calc
        T0 ≤ |t| := hT0_le_abs_t
        _ ≤ |2 * t| := by
          rw [abs_mul]
          have ht_nonneg : 0 ≤ |t| := abs_nonneg t
          norm_num
          nlinarith
    have hlog_two : Real.log |2 * t| ≤ 2 * Real.log |t| :=
      log_abs_two_mul_le_two_log_abs htwo_le_abs_t
    have hrewrite :
        ((σ : ℂ) + I * (((2 * t : ℝ) : ℂ))) =
          ((σ : ℂ) + 2 * I * t) := by
      norm_num [Complex.ofReal_mul]
      ring
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖
          = ‖logDeriv riemannZeta
              ((σ : ℂ) + I * (((2 * t : ℝ) : ℂ)))‖ := by
            rw [hrewrite]
      _ ≤ B * Real.log |2 * t| :=
          hhigh σ (2 * t) hσ.1 hσ.2 hT0_le_abs_two_t
      _ ≤ B * (2 * Real.log |t|) :=
          mul_le_mul_of_nonneg_left hlog_two hB
      _ = (2 * B) * Real.log |t| := by ring
  rcases exists_norm_logDeriv_riemannZeta_sigma_two_it_log_abs_bound_of_high_height_log_abs_bound
      (H := 3) (T0 := T1) (B := 2 * B) (by norm_num) hB2 hshift with
    ⟨C, hC_nonneg, hbound⟩
  refine ⟨C, 3, hC_nonneg, by norm_num, ?_⟩
  intro σ t hσ_left hσ_right ht
  exact hbound σ t ⟨hσ_left, hσ_right⟩ ht

/-- Real-part quotient version of
`exists_norm_logDeriv_riemannZeta_shifted_vertical_log_bound_of_vertical_log_bound`. -/
lemma exists_re_neg_deriv_div_riemannZeta_shifted_vertical_log_bound_of_vertical_norm_log_bound
    {T0 B : ℝ} (hB : 0 ≤ B)
    (hhigh :
      ∀ σ u : ℝ, 1 ≤ σ → σ ≤ 2 → T0 ≤ |u| →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * u)‖ ≤ B * Real.log |u|) :
    ∃ C T0' : ℝ, 0 ≤ C ∧ 3 ≤ T0' ∧
      ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → T0' ≤ |t| →
        (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
            riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤ C * Real.log |t| := by
  rcases exists_norm_logDeriv_riemannZeta_shifted_vertical_log_bound_of_vertical_log_bound
      (T0 := T0) (B := B) hB hhigh with
    ⟨C, T0', hC, hT0', hnorm⟩
  refine ⟨C, T0', hC, hT0', ?_⟩
  intro σ t hσ_left hσ_right ht
  let z : ℂ := (σ : ℂ) + 2 * I * t
  calc
    (-deriv riemannZeta z / riemannZeta z).re
        ≤ ‖-deriv riemannZeta z / riemannZeta z‖ := Complex.re_le_norm _
    _ = ‖logDeriv riemannZeta z‖ :=
        norm_neg_deriv_div_riemannZeta_eq_norm_logDeriv z
    _ ≤ C * Real.log |t| := by
        simpa [z] using hnorm σ t hσ_left hσ_right ht

/-- Shifted norm bridge from a future Borel/Jensen-style affine growth
estimate at the ordinary vertical point `sigma + iu`. -/
lemma exists_norm_logDeriv_riemannZeta_shifted_vertical_log_bound_of_affine_log_norm_add_three_bound_high_height
    (T0 A B : ℝ) (hT0 : 5 ≤ T0) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvertical :
      ∀ σ u : ℝ, T0 ≤ |u| → σ ∈ Set.Icc 1 2 →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * u)‖ ≤
          A + B * Real.log (‖((σ : ℂ) + I * u)‖ + 3)) :
    ∃ C T0' : ℝ, 0 ≤ C ∧ 3 ≤ T0' ∧
      ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → T0' ≤ |t| →
        ‖logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖ ≤ C * Real.log |t| := by
  rcases
      exists_re_im_logDeriv_vertical_log_bound_of_affine_log_norm_add_three_bound_high_height
        T0 A B hT0 hA hB hvertical with
    ⟨C, T0', hC, _hT0', hnorm⟩
  exact
    exists_norm_logDeriv_riemannZeta_shifted_vertical_log_bound_of_vertical_log_bound
      (T0 := T0') (B := C) hC hnorm

/-- Shifted real-part quotient bridge from a future Borel/Jensen-style affine
growth estimate at the ordinary vertical point `sigma + iu`. -/
lemma exists_re_neg_deriv_div_riemannZeta_shifted_vertical_log_bound_of_affine_log_norm_add_three_bound_high_height
    (T0 A B : ℝ) (hT0 : 5 ≤ T0) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvertical :
      ∀ σ u : ℝ, T0 ≤ |u| → σ ∈ Set.Icc 1 2 →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * u)‖ ≤
          A + B * Real.log (‖((σ : ℂ) + I * u)‖ + 3)) :
    ∃ C T0' : ℝ, 0 ≤ C ∧ 3 ≤ T0' ∧
      ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → T0' ≤ |t| →
        (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
            riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤ C * Real.log |t| := by
  rcases
      exists_re_im_logDeriv_vertical_log_bound_of_affine_log_norm_add_three_bound_high_height
        T0 A B hT0 hA hB hvertical with
    ⟨C, T0', hC, _hT0', hnorm⟩
  exact
    exists_re_neg_deriv_div_riemannZeta_shifted_vertical_log_bound_of_vertical_norm_log_bound
      (T0 := T0') (B := C) hC hnorm

/-- Shifted norm bridge from a future ordinary vertical estimate already
stated in the safe height scale `A + B * log(|u| + 3)`. -/
lemma exists_norm_logDeriv_riemannZeta_shifted_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height
    (T0 A B : ℝ) (hT0 : 3 ≤ T0) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvertical :
      ∀ σ u : ℝ, T0 ≤ |u| → σ ∈ Set.Icc 1 2 →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * u)‖ ≤
          A + B * Real.log (|u| + 3)) :
    ∃ C T0' : ℝ, 0 ≤ C ∧ 3 ≤ T0' ∧
      ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → T0' ≤ |t| →
        ‖logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖ ≤ C * Real.log |t| := by
  rcases
      exists_re_im_logDeriv_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height
        T0 A B hT0 hA hB hvertical with
    ⟨C, T0', hC, _hT0', hnorm⟩
  exact
    exists_norm_logDeriv_riemannZeta_shifted_vertical_log_bound_of_vertical_log_bound
      (T0 := T0') (B := C) hC hnorm

/-- Shifted real-part quotient bridge from a future ordinary vertical estimate
already stated in the safe height scale `A + B * log(|u| + 3)`. -/
lemma exists_re_neg_deriv_div_riemannZeta_shifted_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height
    (T0 A B : ℝ) (hT0 : 3 ≤ T0) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvertical :
      ∀ σ u : ℝ, T0 ≤ |u| → σ ∈ Set.Icc 1 2 →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * u)‖ ≤
          A + B * Real.log (|u| + 3)) :
    ∃ C T0' : ℝ, 0 ≤ C ∧ 3 ≤ T0' ∧
      ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → T0' ≤ |t| →
        (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
            riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤ C * Real.log |t| := by
  rcases
      exists_re_im_logDeriv_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height
        T0 A B hT0 hA hB hvertical with
    ⟨C, T0', hC, _hT0', hnorm⟩
  exact
    exists_re_neg_deriv_div_riemannZeta_shifted_vertical_log_bound_of_vertical_norm_log_bound
      (T0 := T0') (B := C) hC hnorm

/-- Signed-input shifted norm bridge from a future ordinary vertical estimate
for `-logDeriv ζ` in the safe height scale `A + B * log(|u| + 3)`. -/
lemma exists_norm_logDeriv_riemannZeta_shifted_vertical_log_bound_of_neg_affine_log_abs_add_three_bound_high_height
    (T0 A B : ℝ) (hT0 : 3 ≤ T0) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvertical :
      ∀ σ u : ℝ, T0 ≤ |u| → σ ∈ Set.Icc 1 2 →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * u)‖ ≤
          A + B * Real.log (|u| + 3)) :
    ∃ C T0' : ℝ, 0 ≤ C ∧ 3 ≤ T0' ∧
      ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → T0' ≤ |t| →
        ‖logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖ ≤ C * Real.log |t| := by
  rcases
      exists_re_im_neg_logDeriv_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height
        T0 A B hT0 hA hB hvertical with
    ⟨C, T0', hC, _hT0', hnorm_neg⟩
  have hnorm :
      ∀ σ u : ℝ, 1 ≤ σ → σ ≤ 2 → T0' ≤ |u| →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * u)‖ ≤ C * Real.log |u| := by
    intro σ u hσ_left hσ_right hu
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * u)‖
          = ‖-logDeriv riemannZeta ((σ : ℂ) + I * u)‖ := (norm_neg _).symm
      _ ≤ C * Real.log |u| := hnorm_neg σ u hσ_left hσ_right hu
  exact
    exists_norm_logDeriv_riemannZeta_shifted_vertical_log_bound_of_vertical_log_bound
      (T0 := T0') (B := C) hC hnorm

/-- Signed-input shifted real-part quotient bridge from a future ordinary
vertical estimate for `-logDeriv ζ` in the safe height scale
`A + B * log(|u| + 3)`. -/
lemma exists_re_neg_deriv_div_riemannZeta_shifted_vertical_log_bound_of_neg_affine_log_abs_add_three_bound_high_height
    (T0 A B : ℝ) (hT0 : 3 ≤ T0) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvertical :
      ∀ σ u : ℝ, T0 ≤ |u| → σ ∈ Set.Icc 1 2 →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * u)‖ ≤
          A + B * Real.log (|u| + 3)) :
    ∃ C T0' : ℝ, 0 ≤ C ∧ 3 ≤ T0' ∧
      ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → T0' ≤ |t| →
        (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
            riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤ C * Real.log |t| := by
  rcases
      exists_re_im_neg_logDeriv_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height
        T0 A B hT0 hA hB hvertical with
    ⟨C, T0', hC, _hT0', hnorm_neg⟩
  have hnorm :
      ∀ σ u : ℝ, 1 ≤ σ → σ ≤ 2 → T0' ≤ |u| →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * u)‖ ≤ C * Real.log |u| := by
    intro σ u hσ_left hσ_right hu
    calc
      ‖logDeriv riemannZeta ((σ : ℂ) + I * u)‖
          = ‖-logDeriv riemannZeta ((σ : ℂ) + I * u)‖ := (norm_neg _).symm
      _ ≤ C * Real.log |u| := hnorm_neg σ u hσ_left hσ_right hu
  exact
    exists_re_neg_deriv_div_riemannZeta_shifted_vertical_log_bound_of_vertical_norm_log_bound
      (T0 := T0') (B := C) hC hnorm

/-- Borel-Carathéodory for the signed logarithmic derivative `-logDeriv ζ` on
a right half-strip.  This is the sign convention used by the 3-4-1 inequality. -/
lemma borelCaratheodory_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le
    {M R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < M) (ha₀ : 1 ≤ a) (hHpos : 0 < H)
    (hlog : ∀ w : ℂ, w ∈ verticalRegion a b H →
      (-logDeriv riemannZeta w).re ≤ M)
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R) (hz : z ∈ Metric.ball ((σ : ℂ) + I * t) R) :
    ‖-logDeriv riemannZeta z‖ ≤
      2 * M * ‖z - ((σ : ℂ) + I * t)‖ /
          (R - ‖z - ((σ : ℂ) + I * t)‖) +
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ *
          (R + ‖z - ((σ : ℂ) + I * t)‖) /
          (R - ‖z - ((σ : ℂ) + I * t)‖) := by
  refine borelCaratheodory_centered_verticalRegion hM
    (differentiableOn_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re
      ha₀ hHpos) ?_ ha hb hH hR hz
  intro w hw
  exact hlog w hw

/-- Oscillation Borel-Carathéodory for the signed logarithmic derivative
`-logDeriv ζ` on a right half-strip. -/
lemma borelCaratheodory_sub_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le
    {M R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < M) (ha₀ : 1 ≤ a) (hHpos : 0 < H)
    (hlog : ∀ w : ℂ, w ∈ verticalRegion a b H →
      ((-logDeriv riemannZeta w) -
        (-logDeriv riemannZeta ((σ : ℂ) + I * t))).re ≤ M)
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R) (hz : z ∈ Metric.ball ((σ : ℂ) + I * t) R) :
    ‖(-logDeriv riemannZeta z) -
        (-logDeriv riemannZeta ((σ : ℂ) + I * t))‖ ≤
      2 * M * ‖z - ((σ : ℂ) + I * t)‖ /
        (R - ‖z - ((σ : ℂ) + I * t)‖) := by
  refine borelCaratheodory_sub_centered_verticalRegion hM
    (differentiableOn_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re
      ha₀ hHpos) ?_ ha hb hH hR hz
  intro w hw
  exact hlog w hw

/-- Half-radius Borel-Carathéodory bound for `-logDeriv ζ` on a right
half-strip.

This removes the rational disk factors from the Borel output in the common
case where the evaluation point lies in the half-radius subdisk. -/
lemma borelCaratheodory_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le_half_radius
    {M R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < M) (ha₀ : 1 ≤ a) (hHpos : 0 < H)
    (hlog : ∀ w : ℂ, w ∈ verticalRegion a b H →
      (-logDeriv riemannZeta w).re ≤ M)
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R)
    (hz_half : ‖z - ((σ : ℂ) + I * t)‖ ≤ R / 2) :
    ‖-logDeriv riemannZeta z‖ ≤
      2 * M + 3 * ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := by
  refine borelCaratheodory_centered_half_radius_bound
    (f := fun z : ℂ => -logDeriv riemannZeta z)
    (c := (σ : ℂ) + I * t) hM
    (differentiableOn_ball_sigma_it_of_differentiableOn_verticalRegion
      (differentiableOn_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re
        ha₀ hHpos)
      ha hb hH) ?_ hR hz_half
  intro w hw
  exact hlog w (ball_sigma_it_subset_verticalRegion ha hb hH hw)

/-- Half-radius oscillation Borel-Carathéodory bound for `-logDeriv ζ` on a
right half-strip.

This is the centered regular-part shape used when controlling variation of
`-ζ'/ζ` across a local disk. -/
lemma borelCaratheodory_sub_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le_half_radius
    {M R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < M) (ha₀ : 1 ≤ a) (hHpos : 0 < H)
    (hlog : ∀ w : ℂ, w ∈ verticalRegion a b H →
      ((-logDeriv riemannZeta w) -
        (-logDeriv riemannZeta ((σ : ℂ) + I * t))).re ≤ M)
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R)
    (hz_half : ‖z - ((σ : ℂ) + I * t)‖ ≤ R / 2) :
    ‖(-logDeriv riemannZeta z) -
        (-logDeriv riemannZeta ((σ : ℂ) + I * t))‖ ≤ 2 * M := by
  refine borelCaratheodory_sub_centered_half_radius_bound
    (f := fun z : ℂ => -logDeriv riemannZeta z)
    (c := (σ : ℂ) + I * t) hM
    (differentiableOn_ball_sigma_it_of_differentiableOn_verticalRegion
      (differentiableOn_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re
        ha₀ hHpos)
      ha hb hH) ?_ hR hz_half
  intro w hw
  exact hlog w (ball_sigma_it_subset_verticalRegion ha hb hH hw)

/-- Half-radius Borel-Carathéodory bound for the signed logarithmic
derivative `-logDeriv ζ` with an affine full-height real-part input. -/
lemma borelCaratheodory_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_affine_re_le_half_radius
    {Are Bre Acenter Bcenter R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < Are + Bre * Real.log (‖((σ : ℂ) + I * t)‖ + 3))
    (ha₀ : 1 ≤ a) (hHpos : 0 < H)
    (hlog : ∀ w : ℂ, w ∈ verticalRegion a b H →
      (-logDeriv riemannZeta w).re ≤
        Are + Bre * Real.log (‖((σ : ℂ) + I * t)‖ + 3))
    (hcenter :
      ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
        Acenter + Bcenter * Real.log (‖((σ : ℂ) + I * t)‖ + 3))
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R)
    (hz_half : ‖z - ((σ : ℂ) + I * t)‖ ≤ R / 2) :
    ‖-logDeriv riemannZeta z‖ ≤
      (2 * Are + 3 * Acenter) +
        (2 * Bre + 3 * Bcenter) *
          Real.log (‖((σ : ℂ) + I * t)‖ + 3) := by
  let ell : ℝ := Real.log (‖((σ : ℂ) + I * t)‖ + 3)
  let mBound : ℝ := Are + Bre * ell
  have hborel :
      ‖-logDeriv riemannZeta z‖ ≤
        2 * mBound + 3 * ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := by
    refine
      borelCaratheodory_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le_half_radius
        (M := mBound) (R := R) (σ := σ) (t := t) (a := a) (b := b)
        (H := H) (z := z) ?_ ha₀ hHpos ?_ ha hb hH hR hz_half
    · simpa [mBound, ell] using hM
    · intro w hw
      simpa [mBound, ell] using hlog w hw
  have hcenter_mul :
      3 * ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
        3 * (Acenter + Bcenter * ell) := by
    exact mul_le_mul_of_nonneg_left (by simpa [ell] using hcenter)
      (by norm_num : (0 : ℝ) ≤ 3)
  calc
    ‖-logDeriv riemannZeta z‖
        ≤ 2 * mBound + 3 * ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ :=
          hborel
    _ ≤ 2 * mBound + 3 * (Acenter + Bcenter * ell) := by
      nlinarith
    _ = (2 * Are + 3 * Acenter) +
          (2 * Bre + 3 * Bcenter) *
            Real.log (‖((σ : ℂ) + I * t)‖ + 3) := by
      simp [mBound, ell]
      ring

/-- Half-radius oscillation Borel-Carathéodory bound for the signed
logarithmic derivative `-logDeriv ζ` with an affine full-height real-part
input. -/
lemma borelCaratheodory_sub_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_affine_re_le_half_radius
    {Are Bre R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < Are + Bre * Real.log (‖((σ : ℂ) + I * t)‖ + 3))
    (ha₀ : 1 ≤ a) (hHpos : 0 < H)
    (hlog : ∀ w : ℂ, w ∈ verticalRegion a b H →
      ((-logDeriv riemannZeta w) -
        (-logDeriv riemannZeta ((σ : ℂ) + I * t))).re ≤
          Are + Bre * Real.log (‖((σ : ℂ) + I * t)‖ + 3))
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R)
    (hz_half : ‖z - ((σ : ℂ) + I * t)‖ ≤ R / 2) :
    ‖(-logDeriv riemannZeta z) -
        (-logDeriv riemannZeta ((σ : ℂ) + I * t))‖ ≤
      2 * Are + 2 * Bre * Real.log (‖((σ : ℂ) + I * t)‖ + 3) := by
  let ell : ℝ := Real.log (‖((σ : ℂ) + I * t)‖ + 3)
  let mBound : ℝ := Are + Bre * ell
  have hborel :
      ‖(-logDeriv riemannZeta z) -
          (-logDeriv riemannZeta ((σ : ℂ) + I * t))‖ ≤ 2 * mBound := by
    refine
      borelCaratheodory_sub_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le_half_radius
        (M := mBound) (R := R) (σ := σ) (t := t) (a := a) (b := b)
        (H := H) (z := z) ?_ ha₀ hHpos ?_ ha hb hH hR hz_half
    · simpa [mBound, ell] using hM
    · intro w hw
      simpa [mBound, ell] using hlog w hw
  calc
    ‖(-logDeriv riemannZeta z) -
        (-logDeriv riemannZeta ((σ : ℂ) + I * t))‖
        ≤ 2 * mBound := hborel
    _ = 2 * Are + 2 * Bre *
          Real.log (‖((σ : ℂ) + I * t)‖ + 3) := by
      simp [mBound, ell]
      ring

/-- Jensen formula specialized to the logarithmic derivative of ζ on a closed
ball. -/
lemma jensen_circleAverage_log_norm_logDeriv_riemannZeta_closedBall
    {c : ℂ} {R : ℝ} (hR : R ≠ 0) :
    circleAverage (Real.log ‖logDeriv riemannZeta ·‖) c R
      = ∑ᶠ u, divisor (logDeriv riemannZeta) (closedBall c |R|) u *
          Real.log (R * ‖c - u‖⁻¹)
        + divisor (logDeriv riemannZeta) (closedBall c |R|) c * Real.log R
        + Real.log ‖meromorphicTrailingCoeffAt (logDeriv riemannZeta) c‖ :=
  jensen_circleAverage_log_norm hR
    (meromorphicOn_logDeriv_riemannZeta_closedBall c |R|)

/-- The signed and unsigned logarithmic derivatives have the same logarithmic
norm pointwise. -/
lemma log_norm_neg_logDeriv_riemannZeta_eq (z : ℂ) :
    Real.log ‖-logDeriv riemannZeta z‖ =
      Real.log ‖logDeriv riemannZeta z‖ := by
  simp

/-- The circle-average side of Jensen's formula is unchanged when replacing
`logDeriv ζ` by `-logDeriv ζ`. -/
lemma circleAverage_log_norm_neg_logDeriv_riemannZeta_eq (c : ℂ) (R : ℝ) :
    circleAverage (fun z : ℂ => Real.log ‖-logDeriv riemannZeta z‖) c R =
      circleAverage (Real.log ‖logDeriv riemannZeta ·‖) c R :=
  circleAverage_congr_sphere fun z _hz =>
    log_norm_neg_logDeriv_riemannZeta_eq z

/-- Multiplying a meromorphic complex-valued function by `-1` does not change
its divisor. -/
lemma divisor_neg_of_meromorphicOn {f : ℂ → ℂ} {U : Set ℂ}
    (hf : MeromorphicOn f U) :
    divisor (fun z : ℂ => -f z) U = divisor f U := by
  ext z
  by_cases hz : z ∈ U
  · have hneg : MeromorphicOn (fun z : ℂ => -f z) U := by
      simpa only [Pi.neg_apply] using hf.neg
    rw [MeromorphicOn.divisor_apply hneg hz, MeromorphicOn.divisor_apply hf hz]
    have hfun : (fun w : ℂ => -f w) = (fun _ : ℂ => (-1 : ℂ)) • f := by
      ext w
      simp
    have horder :
        meromorphicOrderAt (fun w : ℂ => -f w) z =
          meromorphicOrderAt f z := by
      rw [hfun]
      exact meromorphicOrderAt_smul_of_ne_zero
        (f := f) (g := fun _ : ℂ => (-1 : ℂ)) (x := z)
        analyticAt_const (by norm_num)
    rw [horder]
  · simp [hz]

/-- The signed and unsigned logarithmic derivatives of ζ have the same divisor
on every closed ball. -/
lemma divisor_neg_logDeriv_riemannZeta_eq_divisor_logDeriv_closedBall
    (c : ℂ) (R : ℝ) :
    divisor (fun z : ℂ => -logDeriv riemannZeta z) (closedBall c R) =
      divisor (logDeriv riemannZeta) (closedBall c R) :=
  divisor_neg_of_meromorphicOn
    (meromorphicOn_logDeriv_riemannZeta_closedBall c R)

/-- The signed and unsigned logarithmic derivatives of ζ have the same divisor
on the project's vertical regions. -/
lemma divisor_neg_logDeriv_riemannZeta_eq_divisor_logDeriv_verticalRegion
    (a b H : ℝ) :
    divisor (fun z : ℂ => -logDeriv riemannZeta z) (verticalRegion a b H) =
      divisor (logDeriv riemannZeta) (verticalRegion a b H) :=
  divisor_neg_of_meromorphicOn
    (meromorphicOn_logDeriv_riemannZeta_verticalRegion a b H)

/-- Multiplying a meromorphic function by `-1` negates its trailing
coefficient. -/
lemma meromorphicTrailingCoeffAt_neg_of_meromorphicAt
    {f : ℂ → ℂ} {z : ℂ} (hf : MeromorphicAt f z) :
    meromorphicTrailingCoeffAt (fun w : ℂ => -f w) z =
      -meromorphicTrailingCoeffAt f z := by
  have hfun : (fun w : ℂ => -f w) = (fun _ : ℂ => (-1 : ℂ)) • f := by
    ext w
    simp
  rw [hfun]
  simpa using
    (MeromorphicAt.meromorphicTrailingCoeffAt_smul
      (x := z) (f₁ := fun _ : ℂ => (-1 : ℂ)) (f₂ := f)
      (MeromorphicAt.const (-1 : ℂ) z) hf)

/-- Multiplying a meromorphic function by `-1` does not change the norm of its
trailing coefficient. -/
lemma norm_meromorphicTrailingCoeffAt_neg_of_meromorphicAt
    {f : ℂ → ℂ} {z : ℂ} (hf : MeromorphicAt f z) :
    ‖meromorphicTrailingCoeffAt (fun w : ℂ => -f w) z‖ =
      ‖meromorphicTrailingCoeffAt f z‖ := by
  rw [meromorphicTrailingCoeffAt_neg_of_meromorphicAt hf, norm_neg]

/-- The signed and unsigned logarithmic derivatives of ζ have the same
logarithmic norm of the trailing coefficient at every point. -/
lemma log_norm_meromorphicTrailingCoeffAt_neg_logDeriv_riemannZeta_eq
    (z : ℂ) :
    Real.log ‖meromorphicTrailingCoeffAt
        (fun w : ℂ => -logDeriv riemannZeta w) z‖ =
      Real.log ‖meromorphicTrailingCoeffAt (logDeriv riemannZeta) z‖ := by
  have hf : MeromorphicAt (logDeriv riemannZeta) z := by
    exact meromorphicOn_logDeriv_riemannZeta_closedBall z 0 z (by simp)
  rw [norm_meromorphicTrailingCoeffAt_neg_of_meromorphicAt hf]

/-- Translating the input by `c` preserves the meromorphic trailing coefficient
at the translated center. -/
lemma meromorphicTrailingCoeffAt_comp_add_const_zero
    {f : ℂ → ℂ} (c : ℂ) (hf : MeromorphicAt f c) :
    meromorphicTrailingCoeffAt (fun z : ℂ => f (z + c)) 0 =
      meromorphicTrailingCoeffAt f c := by
  have horder :
      meromorphicOrderAt (fun z : ℂ => f (z + c)) 0 =
        meromorphicOrderAt f c := by
    simpa [Function.comp_def] using
      (meromorphicOrderAt_comp_of_deriv_ne_zero
        (f := f) (g := fun z : ℂ => z + c) (x := 0)
        (by fun_prop) (by simp))
  have hfcomp : MeromorphicAt (fun z : ℂ => f (z + c)) 0 := by
    simpa [Function.comp_def] using
      (meromorphicAt_comp_iff_of_deriv_ne_zero
        (f := f) (g := fun z : ℂ => z + c) (x := 0)
        (by fun_prop) (by simp)).2 (by simpa using hf)
  by_cases htop : meromorphicOrderAt f c = ⊤
  · rw [MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top
      (f := fun z : ℂ => f (z + c)) (x := 0) (by simp [horder, htop])]
    rw [MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top
      (f := f) (x := c) htop]
  · obtain ⟨g, hg, hgne, hfg⟩ := (meromorphicOrderAt_ne_top_iff hf).1 htop
    have hnc : ¬EventuallyConst (fun z : ℂ => z + c) (𝓝 0) := by
      intro hconst
      rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top] at hconst
      have hlin : AnalyticAt ℂ (fun z : ℂ => z + c) 0 := by
        fun_prop
      have hone :
          analyticOrderAt ((fun z : ℂ => z + c) · -
              (fun z : ℂ => z + c) 0) 0 = 1 :=
        hlin.analyticOrderAt_sub_eq_one_of_deriv_ne_zero (by simp)
      rw [hone] at hconst
      norm_num at hconst
    have htendsto :
        Tendsto (fun z : ℂ => z + c) (𝓝[≠] 0) (𝓝[≠] c) := by
      have hlin : AnalyticAt ℂ (fun z : ℂ => z + c) 0 := by
        fun_prop
      change map (fun z : ℂ => z + c) (𝓝[≠] 0) ≤ 𝓝[≠] c
      convert hlin.map_nhdsNE hnc using 1
      simp
    have hgcomp : AnalyticAt ℂ (fun z : ℂ => g (z + c)) 0 := by
      have hlin : AnalyticAt ℂ (fun z : ℂ => z + c) 0 := by
        fun_prop
      simpa [Function.comp_def] using
        hg.comp_of_eq' hlin (by simp)
    have hfg_comp :
        (fun z : ℂ => f (z + c)) =ᶠ[𝓝[≠] 0]
          fun z : ℂ =>
            (z - 0) ^
              (meromorphicOrderAt (fun z : ℂ => f (z + c)) 0).untop₀ •
              (fun z : ℂ => g (z + c)) z := by
      rw [horder]
      filter_upwards [hfg.comp_tendsto htendsto] with z hz
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hz
    rw [hgcomp.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
      (by simpa using hgne) hfg_comp]
    rw [hg.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE hgne hfg]
    simp

/-- Translating the input by `c` preserves the norm of the meromorphic
trailing coefficient at the translated center. -/
lemma norm_meromorphicTrailingCoeffAt_comp_add_const_zero
    {f : ℂ → ℂ} (c : ℂ) (hf : MeromorphicAt f c) :
    ‖meromorphicTrailingCoeffAt (fun z : ℂ => f (z + c)) 0‖ =
      ‖meromorphicTrailingCoeffAt f c‖ := by
  rw [meromorphicTrailingCoeffAt_comp_add_const_zero c hf]

/-- Translating the input by `c` preserves the logarithmic norm of the
meromorphic trailing coefficient at the translated center. -/
lemma log_norm_meromorphicTrailingCoeffAt_comp_add_const_zero
    {f : ℂ → ℂ} (c : ℂ) (hf : MeromorphicAt f c) :
    Real.log ‖meromorphicTrailingCoeffAt (fun z : ℂ => f (z + c)) 0‖ =
      Real.log ‖meromorphicTrailingCoeffAt f c‖ := by
  rw [norm_meromorphicTrailingCoeffAt_comp_add_const_zero c hf]

/-- Value-distribution Jensen formula translated from Mathlib's zero-centered
statement to a disk centered at `c`.

The function being counted is the translated function `z ↦ f (z+c)`, while
the circle-average side is stated on the original disk centered at `c`. -/
lemma valueDistribution_logCounting_translate_eq_circleAverage_sub_const
    {f : ℂ → ℂ} (c : ℂ)
    (hf : Meromorphic (fun z : ℂ => f (z + c)))
    {R : ℝ} (hR : R ≠ 0) :
    (ValueDistribution.logCounting (fun z : ℂ => f (z + c)) 0 -
        ValueDistribution.logCounting (fun z : ℂ => f (z + c)) ⊤) R =
      circleAverage (fun z : ℂ => Real.log ‖f z‖) c R -
        Real.log ‖meromorphicTrailingCoeffAt
          (fun z : ℂ => f (z + c)) 0‖ := by
  rw [ValueDistribution.logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_const
    hf hR]
  rw [circleAverage_map_add_const
    (f := fun z : ℂ => Real.log ‖f z‖) (c := c) (R := R)]

/-- Translated value-distribution Jensen formula for `logDeriv ζ`. -/
lemma valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_circleAverage_sub_const
    (c : ℂ) {R : ℝ} (hR : R ≠ 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => logDeriv riemannZeta (z + c)) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => logDeriv riemannZeta (z + c)) ⊤) R =
      circleAverage (fun z : ℂ => Real.log ‖logDeriv riemannZeta z‖) c R -
        Real.log ‖meromorphicTrailingCoeffAt
          (fun z : ℂ => logDeriv riemannZeta (z + c)) 0‖ := by
  exact valueDistribution_logCounting_translate_eq_circleAverage_sub_const
    (f := fun z : ℂ => logDeriv riemannZeta z)
    c
    (meromorphic_comp_add_const meromorphic_logDeriv_riemannZeta c) hR

/-- Translated value-distribution Jensen formula for `-logDeriv ζ`. -/
lemma valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_eq_circleAverage_sub_const
    (c : ℂ) {R : ℝ} (hR : R ≠ 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => -logDeriv riemannZeta (z + c)) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => -logDeriv riemannZeta (z + c)) ⊤) R =
      circleAverage (fun z : ℂ => Real.log ‖-logDeriv riemannZeta z‖) c R -
        Real.log ‖meromorphicTrailingCoeffAt
          (fun z : ℂ => -logDeriv riemannZeta (z + c)) 0‖ := by
  exact valueDistribution_logCounting_translate_eq_circleAverage_sub_const
    (f := fun z : ℂ => -logDeriv riemannZeta z)
    c
    (meromorphic_comp_add_const meromorphic_neg_logDeriv_riemannZeta c) hR

/-- Translated value-distribution Jensen formula for the signed logarithmic
derivative, with the circle-average and trailing-coefficient terms rewritten to
the unsigned `logDeriv ζ` convention. -/
lemma valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_circleAverage
    (c : ℂ) {R : ℝ} (hR : R ≠ 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => -logDeriv riemannZeta (z + c)) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => -logDeriv riemannZeta (z + c)) ⊤) R =
      circleAverage (fun z : ℂ => Real.log ‖logDeriv riemannZeta z‖) c R -
        Real.log ‖meromorphicTrailingCoeffAt
          (fun z : ℂ => logDeriv riemannZeta (z + c)) 0‖ := by
  rw [valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_eq_circleAverage_sub_const
    c hR]
  rw [circleAverage_log_norm_neg_logDeriv_riemannZeta_eq]
  have hf0 :
      MeromorphicAt (fun z : ℂ => logDeriv riemannZeta (z + c)) 0 :=
    (meromorphic_comp_add_const meromorphic_logDeriv_riemannZeta c) 0
  rw [norm_meromorphicTrailingCoeffAt_neg_of_meromorphicAt hf0]

/-- Value-distribution Jensen formula for `logDeriv ζ` on the disk centered at
`σ + I*t`, stated in the coordinates used by the zero-free-region chain. -/
lemma valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_circleAverage_sub_const
    {σ t R : ℝ} (hR : R ≠ 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => logDeriv riemannZeta (z + ((σ : ℂ) + I * t))) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => logDeriv riemannZeta (z + ((σ : ℂ) + I * t))) ⊤) R =
      circleAverage (fun z : ℂ => Real.log ‖logDeriv riemannZeta z‖)
        ((σ : ℂ) + I * t) R -
        Real.log ‖meromorphicTrailingCoeffAt
          (fun z : ℂ => logDeriv riemannZeta
            (z + ((σ : ℂ) + I * t))) 0‖ :=
  valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_circleAverage_sub_const
    ((σ : ℂ) + I * t) hR

/-- Value-distribution Jensen formula for `-logDeriv ζ` on the disk centered at
`σ + I*t`, with the circle-average and trailing-coefficient terms rewritten
to the unsigned `logDeriv ζ` convention. -/
lemma valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_circleAverage
    {σ t R : ℝ} (hR : R ≠ 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => -logDeriv riemannZeta
          (z + ((σ : ℂ) + I * t))) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => -logDeriv riemannZeta
            (z + ((σ : ℂ) + I * t))) ⊤) R =
      circleAverage (fun z : ℂ => Real.log ‖logDeriv riemannZeta z‖)
        ((σ : ℂ) + I * t) R -
        Real.log ‖meromorphicTrailingCoeffAt
          (fun z : ℂ => logDeriv riemannZeta
            (z + ((σ : ℂ) + I * t))) 0‖ :=
  valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_circleAverage
    ((σ : ℂ) + I * t) hR

/-- Translated log-counting Jensen formula for `logDeriv ζ`, rewritten all the
way to the local-divisor side on the original disk centered at `c`.

The remaining trailing-coefficient term is intentionally the translated
zero-centered one.  This avoids requiring a separate theorem that identifies
translated trailing coefficients with original trailing coefficients. -/
lemma valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_localDivisor
    (c : ℂ) {R : ℝ} (hR : R ≠ 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => logDeriv riemannZeta (z + c)) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => logDeriv riemannZeta (z + c)) ⊤) R =
      (∑ᶠ u, divisor (logDeriv riemannZeta) (closedBall c |R|) u *
          Real.log (R * ‖c - u‖⁻¹)
        + divisor (logDeriv riemannZeta) (closedBall c |R|) c * Real.log R
        + Real.log ‖meromorphicTrailingCoeffAt (logDeriv riemannZeta) c‖) -
        Real.log ‖meromorphicTrailingCoeffAt
          (fun z : ℂ => logDeriv riemannZeta (z + c)) 0‖ := by
  rw [valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_circleAverage_sub_const
    c hR]
  rw [jensen_circleAverage_log_norm_logDeriv_riemannZeta_closedBall hR]

/-- Signed translated log-counting Jensen formula for `-logDeriv ζ`, rewritten
to the unsigned `logDeriv ζ` local-divisor side on the original disk centered
at `c`. -/
lemma valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_localDivisor
    (c : ℂ) {R : ℝ} (hR : R ≠ 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => -logDeriv riemannZeta (z + c)) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => -logDeriv riemannZeta (z + c)) ⊤) R =
      (∑ᶠ u, divisor (logDeriv riemannZeta) (closedBall c |R|) u *
          Real.log (R * ‖c - u‖⁻¹)
        + divisor (logDeriv riemannZeta) (closedBall c |R|) c * Real.log R
        + Real.log ‖meromorphicTrailingCoeffAt (logDeriv riemannZeta) c‖) -
        Real.log ‖meromorphicTrailingCoeffAt
          (fun z : ℂ => logDeriv riemannZeta (z + c)) 0‖ := by
  rw [valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_circleAverage
    c hR]
  rw [jensen_circleAverage_log_norm_logDeriv_riemannZeta_closedBall hR]

/-- Local-divisor version of translated log-counting Jensen for `logDeriv ζ`
on a disk centered at `σ + I*t`. -/
lemma valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_localDivisor
    {σ t R : ℝ} (hR : R ≠ 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => logDeriv riemannZeta
          (z + ((σ : ℂ) + I * t))) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => logDeriv riemannZeta
            (z + ((σ : ℂ) + I * t))) ⊤) R =
      (∑ᶠ u, divisor (logDeriv riemannZeta)
          (closedBall ((σ : ℂ) + I * t) |R|) u *
          Real.log (R * ‖((σ : ℂ) + I * t) - u‖⁻¹)
        + divisor (logDeriv riemannZeta)
            (closedBall ((σ : ℂ) + I * t) |R|)
            ((σ : ℂ) + I * t) * Real.log R
        + Real.log ‖meromorphicTrailingCoeffAt (logDeriv riemannZeta)
            ((σ : ℂ) + I * t)‖) -
        Real.log ‖meromorphicTrailingCoeffAt
          (fun z : ℂ => logDeriv riemannZeta
            (z + ((σ : ℂ) + I * t))) 0‖ :=
  valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_localDivisor
    ((σ : ℂ) + I * t) hR

/-- Signed local-divisor version of translated log-counting Jensen for
`-logDeriv ζ` on a disk centered at `σ + I*t`, using unsigned local-divisor
terms. -/
lemma valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_localDivisor
    {σ t R : ℝ} (hR : R ≠ 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => -logDeriv riemannZeta
          (z + ((σ : ℂ) + I * t))) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => -logDeriv riemannZeta
            (z + ((σ : ℂ) + I * t))) ⊤) R =
      (∑ᶠ u, divisor (logDeriv riemannZeta)
          (closedBall ((σ : ℂ) + I * t) |R|) u *
          Real.log (R * ‖((σ : ℂ) + I * t) - u‖⁻¹)
        + divisor (logDeriv riemannZeta)
            (closedBall ((σ : ℂ) + I * t) |R|)
            ((σ : ℂ) + I * t) * Real.log R
        + Real.log ‖meromorphicTrailingCoeffAt (logDeriv riemannZeta)
            ((σ : ℂ) + I * t)‖) -
        Real.log ‖meromorphicTrailingCoeffAt
          (fun z : ℂ => logDeriv riemannZeta
            (z + ((σ : ℂ) + I * t))) 0‖ :=
  valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_localDivisor
    ((σ : ℂ) + I * t) hR

/-- Translated log-counting Jensen formula for `logDeriv ζ`, with translated
trailing-coefficient terms cancelled. -/
lemma valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_localDivisor_pure
    (c : ℂ) {R : ℝ} (hR : R ≠ 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => logDeriv riemannZeta (z + c)) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => logDeriv riemannZeta (z + c)) ⊤) R =
      (∑ᶠ u, divisor (logDeriv riemannZeta) (closedBall c |R|) u *
          Real.log (R * ‖c - u‖⁻¹))
        + divisor (logDeriv riemannZeta) (closedBall c |R|) c * Real.log R := by
  rw [valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_localDivisor
    c hR]
  rw [log_norm_meromorphicTrailingCoeffAt_comp_add_const_zero c
    (meromorphic_logDeriv_riemannZeta c)]
  ring

/-- Signed translated log-counting Jensen formula for `-logDeriv ζ`, with the
right-hand side in unsigned `logDeriv ζ` local-divisor notation and translated
trailing-coefficient terms cancelled. -/
lemma valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_localDivisor_pure
    (c : ℂ) {R : ℝ} (hR : R ≠ 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => -logDeriv riemannZeta (z + c)) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => -logDeriv riemannZeta (z + c)) ⊤) R =
      (∑ᶠ u, divisor (logDeriv riemannZeta) (closedBall c |R|) u *
          Real.log (R * ‖c - u‖⁻¹))
        + divisor (logDeriv riemannZeta) (closedBall c |R|) c * Real.log R := by
  rw [valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_localDivisor
    c hR]
  rw [log_norm_meromorphicTrailingCoeffAt_comp_add_const_zero c
    (meromorphic_logDeriv_riemannZeta c)]
  ring

/-- Pure local-divisor translated log-counting Jensen formula for `logDeriv ζ`
on a disk centered at `σ + I*t`. -/
lemma valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_localDivisor_pure
    {σ t R : ℝ} (hR : R ≠ 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => logDeriv riemannZeta
          (z + ((σ : ℂ) + I * t))) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => logDeriv riemannZeta
            (z + ((σ : ℂ) + I * t))) ⊤) R =
      (∑ᶠ u, divisor (logDeriv riemannZeta)
          (closedBall ((σ : ℂ) + I * t) |R|) u *
          Real.log (R * ‖((σ : ℂ) + I * t) - u‖⁻¹))
        + divisor (logDeriv riemannZeta)
            (closedBall ((σ : ℂ) + I * t) |R|)
            ((σ : ℂ) + I * t) * Real.log R :=
  valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_localDivisor_pure
    ((σ : ℂ) + I * t) hR

/-- Signed pure local-divisor translated log-counting Jensen formula for
`-logDeriv ζ` on a disk centered at `σ + I*t`, using unsigned `logDeriv ζ`
local-divisor terms. -/
lemma valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_localDivisor_pure
    {σ t R : ℝ} (hR : R ≠ 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => -logDeriv riemannZeta
          (z + ((σ : ℂ) + I * t))) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => -logDeriv riemannZeta
            (z + ((σ : ℂ) + I * t))) ⊤) R =
      (∑ᶠ u, divisor (logDeriv riemannZeta)
          (closedBall ((σ : ℂ) + I * t) |R|) u *
          Real.log (R * ‖((σ : ℂ) + I * t) - u‖⁻¹))
        + divisor (logDeriv riemannZeta)
            (closedBall ((σ : ℂ) + I * t) |R|)
            ((σ : ℂ) + I * t) * Real.log R :=
  valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_localDivisor_pure
    ((σ : ℂ) + I * t) hR

/-- If `logDeriv ζ` has order zero at every point of a closed ball, its divisor
on that closed ball vanishes pointwise. -/
lemma divisor_logDeriv_riemannZeta_closedBall_eq_zero_of_order_eq_zero
    (c : ℂ) (R : ℝ)
    (horder : ∀ u ∈ closedBall c R,
      meromorphicOrderAt (logDeriv riemannZeta) u = 0) :
    ∀ u ∈ closedBall c R,
      divisor (logDeriv riemannZeta) (closedBall c R) u = 0 := by
  intro u hu
  rw [divisor_apply (meromorphicOn_logDeriv_riemannZeta_closedBall c R) hu]
  rw [horder u hu]
  simp

/-- Analyticity and nonvanishing of `logDeriv ζ` at every point of a closed
ball imply that its divisor on the closed ball vanishes pointwise. -/
lemma divisor_logDeriv_riemannZeta_closedBall_eq_zero_of_analyticAt_ne_zero
    (c : ℂ) (R : ℝ)
    (han : ∀ u ∈ closedBall c R, AnalyticAt ℂ (logDeriv riemannZeta) u)
    (hne : ∀ u ∈ closedBall c R, logDeriv riemannZeta u ≠ 0) :
    ∀ u ∈ closedBall c R,
      divisor (logDeriv riemannZeta) (closedBall c R) u = 0 :=
  divisor_logDeriv_riemannZeta_closedBall_eq_zero_of_order_eq_zero c R
    (fun u hu => by
      rw [(han u hu).meromorphicOrderAt_eq]
      rw [(han u hu).analyticOrderAt_eq_zero.2 (hne u hu)]
      simp)

/-- If the logarithmic derivative has no divisor contribution on the local
closed ball, the translated log-counting difference for `logDeriv ζ` vanishes. -/
lemma valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_zero_of_divisor_eq_zero
    (c : ℂ) {R : ℝ} (hR : R ≠ 0)
    (hdiv : ∀ u ∈ closedBall c |R|,
      divisor (logDeriv riemannZeta) (closedBall c |R|) u = 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => logDeriv riemannZeta (z + c)) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => logDeriv riemannZeta (z + c)) ⊤) R = 0 := by
  rw [valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_localDivisor_pure
    c hR]
  have hterm : ∀ u : ℂ,
      divisor (logDeriv riemannZeta) (closedBall c |R|) u *
          Real.log (R * ‖c - u‖⁻¹) = 0 := by
    intro u
    by_cases hu : u ∈ closedBall c |R|
    · rw [hdiv u hu]
      norm_num
    · have hz :
          divisor (logDeriv riemannZeta) (closedBall c |R|) u = 0 := by
        simp [hu]
      rw [hz]
      norm_num
  rw [finsum_eq_zero_of_forall_eq_zero hterm]
  have hc : c ∈ closedBall c |R| := by simp
  rw [hdiv c hc]
  norm_num

/-- Signed version of the zero-divisor local log-counting vanishing lemma,
with the divisor hypothesis stated for unsigned `logDeriv ζ`. -/
lemma valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_eq_zero_of_divisor_eq_zero
    (c : ℂ) {R : ℝ} (hR : R ≠ 0)
    (hdiv : ∀ u ∈ closedBall c |R|,
      divisor (logDeriv riemannZeta) (closedBall c |R|) u = 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => -logDeriv riemannZeta (z + c)) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => -logDeriv riemannZeta (z + c)) ⊤) R = 0 := by
  rw [valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_localDivisor_pure
    c hR]
  have hterm : ∀ u : ℂ,
      divisor (logDeriv riemannZeta) (closedBall c |R|) u *
          Real.log (R * ‖c - u‖⁻¹) = 0 := by
    intro u
    by_cases hu : u ∈ closedBall c |R|
    · rw [hdiv u hu]
      norm_num
    · have hz :
          divisor (logDeriv riemannZeta) (closedBall c |R|) u = 0 := by
        simp [hu]
      rw [hz]
      norm_num
  rw [finsum_eq_zero_of_forall_eq_zero hterm]
  have hc : c ∈ closedBall c |R| := by simp
  rw [hdiv c hc]
  norm_num

/-- `σ + I*t` specialization of the zero-divisor local log-counting vanishing
lemma for `logDeriv ζ`. -/
lemma valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_zero_of_divisor_eq_zero
    {σ t R : ℝ} (hR : R ≠ 0)
    (hdiv : ∀ u ∈ closedBall ((σ : ℂ) + I * t) |R|,
      divisor (logDeriv riemannZeta) (closedBall ((σ : ℂ) + I * t) |R|) u = 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => logDeriv riemannZeta
          (z + ((σ : ℂ) + I * t))) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => logDeriv riemannZeta
            (z + ((σ : ℂ) + I * t))) ⊤) R = 0 :=
  valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_zero_of_divisor_eq_zero
    ((σ : ℂ) + I * t) hR hdiv

/-- Signed `σ + I*t` specialization of the zero-divisor local log-counting
vanishing lemma, with the divisor hypothesis stated for unsigned `logDeriv ζ`. -/
lemma valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_eq_zero_of_divisor_eq_zero
    {σ t R : ℝ} (hR : R ≠ 0)
    (hdiv : ∀ u ∈ closedBall ((σ : ℂ) + I * t) |R|,
      divisor (logDeriv riemannZeta) (closedBall ((σ : ℂ) + I * t) |R|) u = 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => -logDeriv riemannZeta
          (z + ((σ : ℂ) + I * t))) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => -logDeriv riemannZeta
            (z + ((σ : ℂ) + I * t))) ⊤) R = 0 :=
  valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_eq_zero_of_divisor_eq_zero
    ((σ : ℂ) + I * t) hR hdiv

/-- If `logDeriv ζ` has order zero throughout the local closed ball, the
translated log-counting difference for `logDeriv ζ` vanishes. -/
lemma valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_zero_of_order_eq_zero
    (c : ℂ) {R : ℝ} (hR : R ≠ 0)
    (horder : ∀ u ∈ closedBall c |R|,
      meromorphicOrderAt (logDeriv riemannZeta) u = 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => logDeriv riemannZeta (z + c)) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => logDeriv riemannZeta (z + c)) ⊤) R = 0 :=
  valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_zero_of_divisor_eq_zero
    c hR
    (divisor_logDeriv_riemannZeta_closedBall_eq_zero_of_order_eq_zero c |R| horder)

/-- Signed version of the order-zero log-counting vanishing lemma, with the
order hypothesis stated for unsigned `logDeriv ζ`. -/
lemma valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_eq_zero_of_order_eq_zero
    (c : ℂ) {R : ℝ} (hR : R ≠ 0)
    (horder : ∀ u ∈ closedBall c |R|,
      meromorphicOrderAt (logDeriv riemannZeta) u = 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => -logDeriv riemannZeta (z + c)) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => -logDeriv riemannZeta (z + c)) ⊤) R = 0 :=
  valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_eq_zero_of_divisor_eq_zero
    c hR
    (divisor_logDeriv_riemannZeta_closedBall_eq_zero_of_order_eq_zero c |R| horder)

/-- `σ + I*t` specialization of the order-zero log-counting vanishing lemma
for `logDeriv ζ`. -/
lemma valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_zero_of_order_eq_zero
    {σ t R : ℝ} (hR : R ≠ 0)
    (horder : ∀ u ∈ closedBall ((σ : ℂ) + I * t) |R|,
      meromorphicOrderAt (logDeriv riemannZeta) u = 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => logDeriv riemannZeta
          (z + ((σ : ℂ) + I * t))) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => logDeriv riemannZeta
            (z + ((σ : ℂ) + I * t))) ⊤) R = 0 :=
  valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_zero_of_order_eq_zero
    ((σ : ℂ) + I * t) hR horder

/-- Signed `σ + I*t` specialization of the order-zero log-counting vanishing
lemma, with the order hypothesis stated for unsigned `logDeriv ζ`. -/
lemma valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_eq_zero_of_order_eq_zero
    {σ t R : ℝ} (hR : R ≠ 0)
    (horder : ∀ u ∈ closedBall ((σ : ℂ) + I * t) |R|,
      meromorphicOrderAt (logDeriv riemannZeta) u = 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => -logDeriv riemannZeta
          (z + ((σ : ℂ) + I * t))) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => -logDeriv riemannZeta
            (z + ((σ : ℂ) + I * t))) ⊤) R = 0 :=
  valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_eq_zero_of_order_eq_zero
    ((σ : ℂ) + I * t) hR horder

/-- If `logDeriv ζ` is analytic and nonzero throughout the local closed ball,
the translated log-counting difference for `logDeriv ζ` vanishes. -/
lemma valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_zero_of_analyticAt_ne_zero
    (c : ℂ) {R : ℝ} (hR : R ≠ 0)
    (han : ∀ u ∈ closedBall c |R|, AnalyticAt ℂ (logDeriv riemannZeta) u)
    (hne : ∀ u ∈ closedBall c |R|, logDeriv riemannZeta u ≠ 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => logDeriv riemannZeta (z + c)) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => logDeriv riemannZeta (z + c)) ⊤) R = 0 :=
  valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_zero_of_divisor_eq_zero
    c hR
    (divisor_logDeriv_riemannZeta_closedBall_eq_zero_of_analyticAt_ne_zero
      c |R| han hne)

/-- Signed analytic-and-nonzero log-counting vanishing lemma, with the local
hypotheses stated for unsigned `logDeriv ζ`. -/
lemma valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_eq_zero_of_analyticAt_ne_zero
    (c : ℂ) {R : ℝ} (hR : R ≠ 0)
    (han : ∀ u ∈ closedBall c |R|, AnalyticAt ℂ (logDeriv riemannZeta) u)
    (hne : ∀ u ∈ closedBall c |R|, logDeriv riemannZeta u ≠ 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => -logDeriv riemannZeta (z + c)) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => -logDeriv riemannZeta (z + c)) ⊤) R = 0 :=
  valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_eq_zero_of_divisor_eq_zero
    c hR
    (divisor_logDeriv_riemannZeta_closedBall_eq_zero_of_analyticAt_ne_zero
      c |R| han hne)

/-- `σ + I*t` specialization of the analytic-and-nonzero log-counting
vanishing lemma for `logDeriv ζ`. -/
lemma valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_zero_of_analyticAt_ne_zero
    {σ t R : ℝ} (hR : R ≠ 0)
    (han : ∀ u ∈ closedBall ((σ : ℂ) + I * t) |R|,
      AnalyticAt ℂ (logDeriv riemannZeta) u)
    (hne : ∀ u ∈ closedBall ((σ : ℂ) + I * t) |R|,
      logDeriv riemannZeta u ≠ 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => logDeriv riemannZeta
          (z + ((σ : ℂ) + I * t))) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => logDeriv riemannZeta
            (z + ((σ : ℂ) + I * t))) ⊤) R = 0 :=
  valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_zero_of_analyticAt_ne_zero
    ((σ : ℂ) + I * t) hR han hne

/-- Signed `σ + I*t` specialization of the analytic-and-nonzero
log-counting vanishing lemma, with the hypotheses stated for unsigned
`logDeriv ζ`. -/
lemma valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_eq_zero_of_analyticAt_ne_zero
    {σ t R : ℝ} (hR : R ≠ 0)
    (han : ∀ u ∈ closedBall ((σ : ℂ) + I * t) |R|,
      AnalyticAt ℂ (logDeriv riemannZeta) u)
    (hne : ∀ u ∈ closedBall ((σ : ℂ) + I * t) |R|,
      logDeriv riemannZeta u ≠ 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => -logDeriv riemannZeta
          (z + ((σ : ℂ) + I * t))) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => -logDeriv riemannZeta
            (z + ((σ : ℂ) + I * t))) ⊤) R = 0 :=
  valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_eq_zero_of_analyticAt_ne_zero
    ((σ : ℂ) + I * t) hR han hne

/-- Right-half-plane closed-ball version of the analytic-and-nonzero
log-counting vanishing lemma for `logDeriv ζ`. -/
lemma valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_zero_of_one_le_re_of_ne_one_of_logDeriv_ne_zero
    (c : ℂ) {R : ℝ} (hR : R ≠ 0)
    (hre : ∀ u ∈ closedBall c |R|, 1 ≤ u.re)
    (h1 : ∀ u ∈ closedBall c |R|, u ≠ 1)
    (hlogne : ∀ u ∈ closedBall c |R|, logDeriv riemannZeta u ≠ 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => logDeriv riemannZeta (z + c)) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => logDeriv riemannZeta (z + c)) ⊤) R = 0 :=
  valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_zero_of_analyticAt_ne_zero
    c hR
    (analyticAt_logDeriv_riemannZeta_closedBall_of_one_le_re_of_ne_one
      c |R| hre h1)
    hlogne

/-- Signed right-half-plane closed-ball version of the analytic-and-nonzero
log-counting vanishing lemma, with hypotheses stated for unsigned
`logDeriv ζ`. -/
lemma valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_eq_zero_of_one_le_re_of_ne_one_of_logDeriv_ne_zero
    (c : ℂ) {R : ℝ} (hR : R ≠ 0)
    (hre : ∀ u ∈ closedBall c |R|, 1 ≤ u.re)
    (h1 : ∀ u ∈ closedBall c |R|, u ≠ 1)
    (hlogne : ∀ u ∈ closedBall c |R|, logDeriv riemannZeta u ≠ 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => -logDeriv riemannZeta (z + c)) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => -logDeriv riemannZeta (z + c)) ⊤) R = 0 :=
  valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_eq_zero_of_analyticAt_ne_zero
    c hR
    (analyticAt_logDeriv_riemannZeta_closedBall_of_one_le_re_of_ne_one
      c |R| hre h1)
    hlogne

/-- `σ + I*t` specialization of the right-half-plane log-counting vanishing
lemma for `logDeriv ζ`. -/
lemma valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_zero_of_one_le_re_of_ne_one_of_logDeriv_ne_zero
    {σ t R : ℝ} (hR : R ≠ 0)
    (hre : ∀ u ∈ closedBall ((σ : ℂ) + I * t) |R|, 1 ≤ u.re)
    (h1 : ∀ u ∈ closedBall ((σ : ℂ) + I * t) |R|, u ≠ 1)
    (hlogne : ∀ u ∈ closedBall ((σ : ℂ) + I * t) |R|,
      logDeriv riemannZeta u ≠ 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => logDeriv riemannZeta
          (z + ((σ : ℂ) + I * t))) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => logDeriv riemannZeta
            (z + ((σ : ℂ) + I * t))) ⊤) R = 0 :=
  valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_zero_of_one_le_re_of_ne_one_of_logDeriv_ne_zero
    ((σ : ℂ) + I * t) hR hre h1 hlogne

/-- Signed `σ + I*t` specialization of the right-half-plane log-counting
vanishing lemma, with hypotheses stated for unsigned `logDeriv ζ`. -/
lemma valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_eq_zero_of_one_le_re_of_ne_one_of_logDeriv_ne_zero
    {σ t R : ℝ} (hR : R ≠ 0)
    (hre : ∀ u ∈ closedBall ((σ : ℂ) + I * t) |R|, 1 ≤ u.re)
    (h1 : ∀ u ∈ closedBall ((σ : ℂ) + I * t) |R|, u ≠ 1)
    (hlogne : ∀ u ∈ closedBall ((σ : ℂ) + I * t) |R|,
      logDeriv riemannZeta u ≠ 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => -logDeriv riemannZeta
          (z + ((σ : ℂ) + I * t))) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => -logDeriv riemannZeta
            (z + ((σ : ℂ) + I * t))) ⊤) R = 0 :=
  valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_eq_zero_of_one_le_re_of_ne_one_of_logDeriv_ne_zero
    ((σ : ℂ) + I * t) hR hre h1 hlogne

/-- Disk-geometric specialization of the right-half-plane log-counting
vanishing lemma for `logDeriv ζ`.  The numeric hypotheses say the disk centered
at `σ + I*t` lies in `Re >= 1` and stays a positive height away from the pole
at `1`. -/
lemma valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_zero_of_disk_right_half_of_logDeriv_ne_zero
    {σ t R H : ℝ} (hR : R ≠ 0)
    (hσ : 1 + |R| ≤ σ) (hHpos : 0 < H) (hH : H + |R| ≤ |t|)
    (hlogne : ∀ u ∈ closedBall ((σ : ℂ) + I * t) |R|,
      logDeriv riemannZeta u ≠ 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => logDeriv riemannZeta
          (z + ((σ : ℂ) + I * t))) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => logDeriv riemannZeta
            (z + ((σ : ℂ) + I * t))) ⊤) R = 0 :=
  valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_zero_of_one_le_re_of_ne_one_of_logDeriv_ne_zero
    hR
    (fun u hu =>
      closedBall_sigma_it_one_le_re_of_add_le
        (z := u) (σ := σ) (t := t) (R := |R|) hu hσ)
    (fun u hu =>
      closedBall_sigma_it_ne_one_of_height_add_le
        (z := u) (σ := σ) (t := t) (R := |R|) (H := H) hu hHpos hH)
    hlogne

/-- Positive-radius version of the direct disk-geometric log-counting
vanishing lemma for `logDeriv ζ`.  This normalizes the disk radius from
`|R|` to `R`, matching the Borel-Carathéodory APIs. -/
lemma valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_zero_of_disk_right_half_of_logDeriv_ne_zero_pos_radius
    {σ t R H : ℝ} (hR : 0 < R)
    (hσ : 1 + R ≤ σ) (hHpos : 0 < H) (hH : H + R ≤ |t|)
    (hlogne : ∀ u ∈ closedBall ((σ : ℂ) + I * t) R,
      logDeriv riemannZeta u ≠ 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => logDeriv riemannZeta
          (z + ((σ : ℂ) + I * t))) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => logDeriv riemannZeta
            (z + ((σ : ℂ) + I * t))) ⊤) R = 0 := by
  have hAbs : |R| = R := abs_of_pos hR
  have hσ' : 1 + |R| ≤ σ := by simpa [hAbs] using hσ
  have hH' : H + |R| ≤ |t| := by simpa [hAbs] using hH
  have hlogne' : ∀ u ∈ closedBall ((σ : ℂ) + I * t) |R|,
      logDeriv riemannZeta u ≠ 0 := by
    intro u hu
    exact hlogne u (by simpa [hAbs] using hu)
  simpa [hAbs] using
    valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_zero_of_disk_right_half_of_logDeriv_ne_zero
      (σ := σ) (t := t) (R := R) (H := H) hR.ne' hσ' hHpos hH' hlogne'

/-- Signed disk-geometric specialization of the right-half-plane log-counting
vanishing lemma, with hypotheses stated for unsigned `logDeriv ζ`. -/
lemma valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_eq_zero_of_disk_right_half_of_logDeriv_ne_zero
    {σ t R H : ℝ} (hR : R ≠ 0)
    (hσ : 1 + |R| ≤ σ) (hHpos : 0 < H) (hH : H + |R| ≤ |t|)
    (hlogne : ∀ u ∈ closedBall ((σ : ℂ) + I * t) |R|,
      logDeriv riemannZeta u ≠ 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => -logDeriv riemannZeta
          (z + ((σ : ℂ) + I * t))) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => -logDeriv riemannZeta
            (z + ((σ : ℂ) + I * t))) ⊤) R = 0 :=
  valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_eq_zero_of_one_le_re_of_ne_one_of_logDeriv_ne_zero
    hR
    (fun u hu =>
      closedBall_sigma_it_one_le_re_of_add_le
        (z := u) (σ := σ) (t := t) (R := |R|) hu hσ)
    (fun u hu =>
      closedBall_sigma_it_ne_one_of_height_add_le
        (z := u) (σ := σ) (t := t) (R := |R|) (H := H) hu hHpos hH)
    hlogne

/-- Positive-radius signed disk-geometric log-counting vanishing lemma, with
hypotheses stated for unsigned `logDeriv ζ`. -/
lemma valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_eq_zero_of_disk_right_half_of_logDeriv_ne_zero_pos_radius
    {σ t R H : ℝ} (hR : 0 < R)
    (hσ : 1 + R ≤ σ) (hHpos : 0 < H) (hH : H + R ≤ |t|)
    (hlogne : ∀ u ∈ closedBall ((σ : ℂ) + I * t) R,
      logDeriv riemannZeta u ≠ 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => -logDeriv riemannZeta
          (z + ((σ : ℂ) + I * t))) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => -logDeriv riemannZeta
            (z + ((σ : ℂ) + I * t))) ⊤) R = 0 := by
  have hAbs : |R| = R := abs_of_pos hR
  have hσ' : 1 + |R| ≤ σ := by simpa [hAbs] using hσ
  have hH' : H + |R| ≤ |t| := by simpa [hAbs] using hH
  have hlogne' : ∀ u ∈ closedBall ((σ : ℂ) + I * t) |R|,
      logDeriv riemannZeta u ≠ 0 := by
    intro u hu
    exact hlogne u (by simpa [hAbs] using hu)
  simpa [hAbs] using
    valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_eq_zero_of_disk_right_half_of_logDeriv_ne_zero
      (σ := σ) (t := t) (R := R) (H := H) hR.ne' hσ' hHpos hH' hlogne'

/-- Nonvanishing of the signed logarithmic derivative implies nonvanishing of
the unsigned logarithmic derivative. -/
lemma logDeriv_riemannZeta_ne_zero_of_neg_logDeriv_ne_zero {z : ℂ}
    (hneg : -logDeriv riemannZeta z ≠ 0) :
    logDeriv riemannZeta z ≠ 0 := by
  intro h
  apply hneg
  simp [h]

/-- Signed disk-geometric log-counting vanishing with the local nonvanishing
hypothesis stated directly for `-logDeriv ζ`. -/
lemma valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_eq_zero_of_disk_right_half_of_neg_logDeriv_ne_zero
    {σ t R H : ℝ} (hR : R ≠ 0)
    (hσ : 1 + |R| ≤ σ) (hHpos : 0 < H) (hH : H + |R| ≤ |t|)
    (hnegne : ∀ u ∈ closedBall ((σ : ℂ) + I * t) |R|,
      -logDeriv riemannZeta u ≠ 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => -logDeriv riemannZeta
          (z + ((σ : ℂ) + I * t))) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => -logDeriv riemannZeta
            (z + ((σ : ℂ) + I * t))) ⊤) R = 0 :=
  valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_eq_zero_of_disk_right_half_of_logDeriv_ne_zero
    hR hσ hHpos hH
    (fun u hu =>
      logDeriv_riemannZeta_ne_zero_of_neg_logDeriv_ne_zero (hnegne u hu))

/-- Positive-radius signed disk-geometric log-counting vanishing with the
local nonvanishing hypothesis stated directly for `-logDeriv ζ`. -/
lemma valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_eq_zero_of_disk_right_half_of_neg_logDeriv_ne_zero_pos_radius
    {σ t R H : ℝ} (hR : 0 < R)
    (hσ : 1 + R ≤ σ) (hHpos : 0 < H) (hH : H + R ≤ |t|)
    (hnegne : ∀ u ∈ closedBall ((σ : ℂ) + I * t) R,
      -logDeriv riemannZeta u ≠ 0) :
    (ValueDistribution.logCounting
        (fun z : ℂ => -logDeriv riemannZeta
          (z + ((σ : ℂ) + I * t))) 0 -
        ValueDistribution.logCounting
          (fun z : ℂ => -logDeriv riemannZeta
            (z + ((σ : ℂ) + I * t))) ⊤) R = 0 := by
  have hAbs : |R| = R := abs_of_pos hR
  have hσ' : 1 + |R| ≤ σ := by simpa [hAbs] using hσ
  have hH' : H + |R| ≤ |t| := by simpa [hAbs] using hH
  have hnegne' : ∀ u ∈ closedBall ((σ : ℂ) + I * t) |R|,
      -logDeriv riemannZeta u ≠ 0 := by
    intro u hu
    exact hnegne u (by simpa [hAbs] using hu)
  simpa [hAbs] using
    valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_eq_zero_of_disk_right_half_of_neg_logDeriv_ne_zero
      (σ := σ) (t := t) (R := R) (H := H) hR.ne' hσ' hHpos hH' hnegne'

/-- Jensen formula specialized to the signed logarithmic derivative of ζ on a
closed ball. -/
lemma jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_closedBall
    {c : ℂ} {R : ℝ} (hR : R ≠ 0) :
    circleAverage (fun z : ℂ => Real.log ‖-logDeriv riemannZeta z‖) c R
      = ∑ᶠ u,
          divisor (fun z : ℂ => -logDeriv riemannZeta z) (closedBall c |R|) u *
            Real.log (R * ‖c - u‖⁻¹)
        + divisor (fun z : ℂ => -logDeriv riemannZeta z) (closedBall c |R|) c *
            Real.log R
        + Real.log ‖meromorphicTrailingCoeffAt
            (fun z : ℂ => -logDeriv riemannZeta z) c‖ :=
  jensen_circleAverage_log_norm hR
    (meromorphicOn_neg_logDeriv_riemannZeta_closedBall c |R|)

/-- Jensen formula for `-logDeriv ζ` on a closed ball, with the right-hand
side rewritten into the unsigned `logDeriv ζ` divisor and trailing coefficient
bookkeeping. -/
lemma jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_closedBall_unsigned_terms
    {c : ℂ} {R : ℝ} (hR : R ≠ 0) :
    circleAverage (fun z : ℂ => Real.log ‖-logDeriv riemannZeta z‖) c R
      = ∑ᶠ u,
          divisor (logDeriv riemannZeta) (closedBall c |R|) u *
            Real.log (R * ‖c - u‖⁻¹)
        + divisor (logDeriv riemannZeta) (closedBall c |R|) c *
            Real.log R
        + Real.log ‖meromorphicTrailingCoeffAt (logDeriv riemannZeta) c‖ := by
  rw [jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_closedBall hR]
  rw [divisor_neg_logDeriv_riemannZeta_eq_divisor_logDeriv_closedBall c |R|]
  rw [log_norm_meromorphicTrailingCoeffAt_neg_logDeriv_riemannZeta_eq c]

/-- Jensen formula specialized directly to ζ on a `σ + I*t` disk. -/
lemma jensen_circleAverage_log_norm_riemannZeta_sigma_it
    {R σ t : ℝ} (hR : R ≠ 0) :
    circleAverage (Real.log ‖riemannZeta ·‖) ((σ : ℂ) + I * t) R
      = ∑ᶠ u,
          divisor riemannZeta (closedBall ((σ : ℂ) + I * t) |R|) u *
            Real.log (R * ‖((σ : ℂ) + I * t) - u‖⁻¹)
        + divisor riemannZeta (closedBall ((σ : ℂ) + I * t) |R|)
            ((σ : ℂ) + I * t) * Real.log R
        + Real.log ‖meromorphicTrailingCoeffAt riemannZeta
            ((σ : ℂ) + I * t)‖ :=
  jensen_circleAverage_log_norm_riemannZeta_closedBall hR

/-- Positive-radius Jensen formula specialized directly to ζ on a
`σ + I*t` disk. -/
lemma jensen_circleAverage_log_norm_riemannZeta_sigma_it_of_pos_radius
    {R σ t : ℝ} (hR : 0 < R) :
    circleAverage (Real.log ‖riemannZeta ·‖) ((σ : ℂ) + I * t) R
      = ∑ᶠ u,
          divisor riemannZeta (closedBall ((σ : ℂ) + I * t) R) u *
            Real.log (R * ‖((σ : ℂ) + I * t) - u‖⁻¹)
        + divisor riemannZeta (closedBall ((σ : ℂ) + I * t) R)
            ((σ : ℂ) + I * t) * Real.log R
        + Real.log ‖meromorphicTrailingCoeffAt riemannZeta
            ((σ : ℂ) + I * t)‖ := by
  have hAbs : |R| = R := abs_of_pos hR
  have h :=
    jensen_circleAverage_log_norm_riemannZeta_sigma_it
      (R := R) (σ := σ) (t := t) hR.ne'
  rw [hAbs] at h
  exact h

/-- Jensen formula specialized directly to `logDeriv ζ` on a `σ + I*t`
disk. -/
lemma jensen_circleAverage_log_norm_logDeriv_riemannZeta_sigma_it
    {R σ t : ℝ} (hR : R ≠ 0) :
    circleAverage (Real.log ‖logDeriv riemannZeta ·‖)
        ((σ : ℂ) + I * t) R
      = ∑ᶠ u,
          divisor (logDeriv riemannZeta)
            (closedBall ((σ : ℂ) + I * t) |R|) u *
            Real.log (R * ‖((σ : ℂ) + I * t) - u‖⁻¹)
        + divisor (logDeriv riemannZeta)
            (closedBall ((σ : ℂ) + I * t) |R|)
            ((σ : ℂ) + I * t) * Real.log R
        + Real.log ‖meromorphicTrailingCoeffAt (logDeriv riemannZeta)
            ((σ : ℂ) + I * t)‖ :=
  jensen_circleAverage_log_norm_logDeriv_riemannZeta_closedBall hR

/-- Positive-radius Jensen formula specialized directly to `logDeriv ζ` on a
`σ + I*t` disk. -/
lemma jensen_circleAverage_log_norm_logDeriv_riemannZeta_sigma_it_of_pos_radius
    {R σ t : ℝ} (hR : 0 < R) :
    circleAverage (Real.log ‖logDeriv riemannZeta ·‖)
        ((σ : ℂ) + I * t) R
      = ∑ᶠ u,
          divisor (logDeriv riemannZeta)
            (closedBall ((σ : ℂ) + I * t) R) u *
            Real.log (R * ‖((σ : ℂ) + I * t) - u‖⁻¹)
        + divisor (logDeriv riemannZeta)
            (closedBall ((σ : ℂ) + I * t) R)
            ((σ : ℂ) + I * t) * Real.log R
        + Real.log ‖meromorphicTrailingCoeffAt (logDeriv riemannZeta)
            ((σ : ℂ) + I * t)‖ := by
  have hAbs : |R| = R := abs_of_pos hR
  have h :=
    jensen_circleAverage_log_norm_logDeriv_riemannZeta_sigma_it
      (R := R) (σ := σ) (t := t) hR.ne'
  rw [hAbs] at h
  exact h

/-- Jensen formula specialized directly to `-logDeriv ζ` on a `σ + I*t`
disk. -/
lemma jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_sigma_it
    {R σ t : ℝ} (hR : R ≠ 0) :
    circleAverage (fun z : ℂ => Real.log ‖-logDeriv riemannZeta z‖)
        ((σ : ℂ) + I * t) R
      = ∑ᶠ u,
          divisor (fun z : ℂ => -logDeriv riemannZeta z)
            (closedBall ((σ : ℂ) + I * t) |R|) u *
            Real.log (R * ‖((σ : ℂ) + I * t) - u‖⁻¹)
        + divisor (fun z : ℂ => -logDeriv riemannZeta z)
            (closedBall ((σ : ℂ) + I * t) |R|)
            ((σ : ℂ) + I * t) * Real.log R
        + Real.log ‖meromorphicTrailingCoeffAt
            (fun z : ℂ => -logDeriv riemannZeta z)
            ((σ : ℂ) + I * t)‖ :=
  jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_closedBall hR

/-- Positive-radius Jensen formula specialized directly to `-logDeriv ζ` on a
`σ + I*t` disk. -/
lemma jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_sigma_it_of_pos_radius
    {R σ t : ℝ} (hR : 0 < R) :
    circleAverage (fun z : ℂ => Real.log ‖-logDeriv riemannZeta z‖)
        ((σ : ℂ) + I * t) R
      = ∑ᶠ u,
          divisor (fun z : ℂ => -logDeriv riemannZeta z)
            (closedBall ((σ : ℂ) + I * t) R) u *
            Real.log (R * ‖((σ : ℂ) + I * t) - u‖⁻¹)
        + divisor (fun z : ℂ => -logDeriv riemannZeta z)
            (closedBall ((σ : ℂ) + I * t) R)
            ((σ : ℂ) + I * t) * Real.log R
        + Real.log ‖meromorphicTrailingCoeffAt
            (fun z : ℂ => -logDeriv riemannZeta z)
            ((σ : ℂ) + I * t)‖ := by
  have hAbs : |R| = R := abs_of_pos hR
  have h :=
    jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_sigma_it
      (R := R) (σ := σ) (t := t) hR.ne'
  rw [hAbs] at h
  exact h

/-- Jensen formula specialized directly to `-logDeriv ζ` on a `σ + I*t`
disk, with unsigned `logDeriv ζ` divisor and trailing coefficient terms on the
right-hand side. -/
lemma jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_sigma_it_unsigned_terms
    {R σ t : ℝ} (hR : R ≠ 0) :
    circleAverage (fun z : ℂ => Real.log ‖-logDeriv riemannZeta z‖)
        ((σ : ℂ) + I * t) R
      = ∑ᶠ u,
          divisor (logDeriv riemannZeta)
            (closedBall ((σ : ℂ) + I * t) |R|) u *
            Real.log (R * ‖((σ : ℂ) + I * t) - u‖⁻¹)
        + divisor (logDeriv riemannZeta)
            (closedBall ((σ : ℂ) + I * t) |R|)
            ((σ : ℂ) + I * t) * Real.log R
        + Real.log ‖meromorphicTrailingCoeffAt (logDeriv riemannZeta)
            ((σ : ℂ) + I * t)‖ :=
  jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_closedBall_unsigned_terms hR

/-- Positive-radius Jensen formula for the signed left side on a `σ + I*t`
disk, with unsigned `logDeriv ζ` divisor and trailing coefficient terms. -/
lemma jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_sigma_it_unsigned_terms_of_pos_radius
    {R σ t : ℝ} (hR : 0 < R) :
    circleAverage (fun z : ℂ => Real.log ‖-logDeriv riemannZeta z‖)
        ((σ : ℂ) + I * t) R
      = ∑ᶠ u,
          divisor (logDeriv riemannZeta)
            (closedBall ((σ : ℂ) + I * t) R) u *
            Real.log (R * ‖((σ : ℂ) + I * t) - u‖⁻¹)
        + divisor (logDeriv riemannZeta)
            (closedBall ((σ : ℂ) + I * t) R)
            ((σ : ℂ) + I * t) * Real.log R
        + Real.log ‖meromorphicTrailingCoeffAt (logDeriv riemannZeta)
            ((σ : ℂ) + I * t)‖ := by
  have hAbs : |R| = R := abs_of_pos hR
  have h :=
    jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_sigma_it_unsigned_terms
      (R := R) (σ := σ) (t := t) hR.ne'
  rw [hAbs] at h
  exact h

/-- Jensen formula specialized to ζ on a `σ + I*t` disk using the ambient
vertical-region wrapper. -/
lemma jensen_circleAverage_log_norm_riemannZeta_verticalRegion
    {R σ t a b H : ℝ}
    (hR : R ≠ 0) (ha : a + |R| ≤ σ)
    (hb : σ + |R| ≤ b) (hH : H + |R| ≤ |t|) :
    circleAverage (Real.log ‖riemannZeta ·‖) ((σ : ℂ) + I * t) R
      = ∑ᶠ u,
          divisor riemannZeta (closedBall ((σ : ℂ) + I * t) |R|) u *
            Real.log (R * ‖((σ : ℂ) + I * t) - u‖⁻¹)
        + divisor riemannZeta (closedBall ((σ : ℂ) + I * t) |R|)
            ((σ : ℂ) + I * t) * Real.log R
        + Real.log ‖meromorphicTrailingCoeffAt riemannZeta
            ((σ : ℂ) + I * t)‖ :=
  jensen_circleAverage_log_norm_verticalRegion hR
    (meromorphicOn_riemannZeta_verticalRegion a b H) ha hb hH

/-- Jensen formula specialized to the logarithmic derivative of ζ on a
`σ + I*t` disk using the ambient vertical-region wrapper. -/
lemma jensen_circleAverage_log_norm_logDeriv_riemannZeta_verticalRegion
    {R σ t a b H : ℝ}
    (hR : R ≠ 0) (ha : a + |R| ≤ σ)
    (hb : σ + |R| ≤ b) (hH : H + |R| ≤ |t|) :
    circleAverage (Real.log ‖logDeriv riemannZeta ·‖)
        ((σ : ℂ) + I * t) R
      = ∑ᶠ u,
          divisor (logDeriv riemannZeta)
            (closedBall ((σ : ℂ) + I * t) |R|) u *
            Real.log (R * ‖((σ : ℂ) + I * t) - u‖⁻¹)
        + divisor (logDeriv riemannZeta)
            (closedBall ((σ : ℂ) + I * t) |R|)
            ((σ : ℂ) + I * t) * Real.log R
        + Real.log ‖meromorphicTrailingCoeffAt (logDeriv riemannZeta)
            ((σ : ℂ) + I * t)‖ :=
  jensen_circleAverage_log_norm_verticalRegion hR
    (meromorphicOn_logDeriv_riemannZeta_verticalRegion a b H) ha hb hH

/-- Jensen formula specialized to the signed logarithmic derivative of ζ on a
`σ + I*t` disk using the ambient vertical-region wrapper. -/
lemma jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_verticalRegion
    {R σ t a b H : ℝ}
    (hR : R ≠ 0) (ha : a + |R| ≤ σ)
    (hb : σ + |R| ≤ b) (hH : H + |R| ≤ |t|) :
    circleAverage (fun z : ℂ => Real.log ‖-logDeriv riemannZeta z‖)
        ((σ : ℂ) + I * t) R
      = ∑ᶠ u,
          divisor (fun z : ℂ => -logDeriv riemannZeta z)
            (closedBall ((σ : ℂ) + I * t) |R|) u *
            Real.log (R * ‖((σ : ℂ) + I * t) - u‖⁻¹)
        + divisor (fun z : ℂ => -logDeriv riemannZeta z)
            (closedBall ((σ : ℂ) + I * t) |R|)
            ((σ : ℂ) + I * t) * Real.log R
        + Real.log ‖meromorphicTrailingCoeffAt
            (fun z : ℂ => -logDeriv riemannZeta z)
            ((σ : ℂ) + I * t)‖ :=
  jensen_circleAverage_log_norm_verticalRegion hR
    (meromorphicOn_neg_logDeriv_riemannZeta_verticalRegion a b H) ha hb hH

/-- Jensen formula for `-logDeriv ζ` on a `σ + I*t` disk, using the ambient
vertical-region wrapper while rewriting the right-hand side into the unsigned
`logDeriv ζ` divisor and trailing coefficient bookkeeping. -/
lemma jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_verticalRegion_unsigned_terms
    {R σ t a b H : ℝ}
    (hR : R ≠ 0) (ha : a + |R| ≤ σ)
    (hb : σ + |R| ≤ b) (hH : H + |R| ≤ |t|) :
    circleAverage (fun z : ℂ => Real.log ‖-logDeriv riemannZeta z‖)
        ((σ : ℂ) + I * t) R
      = ∑ᶠ u,
          divisor (logDeriv riemannZeta)
            (closedBall ((σ : ℂ) + I * t) |R|) u *
            Real.log (R * ‖((σ : ℂ) + I * t) - u‖⁻¹)
        + divisor (logDeriv riemannZeta)
            (closedBall ((σ : ℂ) + I * t) |R|)
            ((σ : ℂ) + I * t) * Real.log R
        + Real.log ‖meromorphicTrailingCoeffAt (logDeriv riemannZeta)
            ((σ : ℂ) + I * t)‖ := by
  rw [jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_verticalRegion
    hR ha hb hH]
  rw [divisor_neg_logDeriv_riemannZeta_eq_divisor_logDeriv_closedBall
    ((σ : ℂ) + I * t) |R|]
  rw [log_norm_meromorphicTrailingCoeffAt_neg_logDeriv_riemannZeta_eq
    ((σ : ℂ) + I * t)]

end ZeroFreeRegion
