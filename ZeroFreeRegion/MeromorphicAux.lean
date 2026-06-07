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

end ZeroFreeRegion
