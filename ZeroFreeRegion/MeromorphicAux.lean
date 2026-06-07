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

/-- Eventual pole-order bound near `1` in explicit quotient notation `ζ'/ζ`. -/
lemma eventually_norm_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one :
    ∀ᶠ s in 𝓝[≠] (1 : ℂ),
      ‖deriv riemannZeta s / riemannZeta s‖ ≤ 2 / ‖s - 1‖ := by
  filter_upwards [eventually_norm_logDeriv_riemannZeta_le_two_div_norm_sub_one]
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

/-- The logarithmic derivative of ζ is meromorphic at the pole `1`. -/
lemma meromorphicAt_logDeriv_riemannZeta_one :
    MeromorphicAt (logDeriv riemannZeta) (1 : ℂ) :=
  meromorphicAt_riemannZeta_one.deriv.div meromorphicAt_riemannZeta_one

/-- The logarithmic derivative of ζ is meromorphic on every closed ball. -/
lemma meromorphicOn_logDeriv_riemannZeta_closedBall (c : ℂ) (R : ℝ) :
    MeromorphicOn (logDeriv riemannZeta) (closedBall c R) :=
  (meromorphicOn_riemannZeta_closedBall c R).logDeriv

end ZeroFreeRegion
