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
  let regularPart : ℂ :=
    -deriv riemannZeta s / riemannZeta s + (s - ρ)⁻¹
  have hregular_norm :
      ‖regularPart‖ ≤ B * Real.log |s.im| := by
    simpa [regularPart] using
      hregular s ρ hs_height hs_re_mem hζρ hρ_im_eq hρ_re_lt hsub
  have hregular_re_le :
      regularPart.re ≤ ‖regularPart‖ :=
    le_trans (le_abs_self regularPart.re) (abs_re_le_norm regularPart)
  have hregular_re :
      regularPart.re =
        (-deriv riemannZeta s / riemannZeta s).re +
          1 / (s.re - ρ.re) := by
    simp [regularPart, inv_sub_same_im_re hρ_im_eq hsub]
  calc
    (-deriv riemannZeta s / riemannZeta s).re +
        1 / (s.re - ρ.re)
        = regularPart.re := hregular_re.symm
    _ ≤ ‖regularPart‖ := hregular_re_le
    _ ≤ B * Real.log |s.im| := hregular_norm

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

/-- The logarithmic derivative of ζ is meromorphic on every closed ball. -/
lemma meromorphicOn_logDeriv_riemannZeta_closedBall (c : ℂ) (R : ℝ) :
    MeromorphicOn (logDeriv riemannZeta) (closedBall c R) :=
  (meromorphicOn_riemannZeta_closedBall c R).logDeriv

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

end ZeroFreeRegion
