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

/-- ζ is meromorphic at `1`.

The proof rewrites ζ on a punctured neighborhood of `1` as the sum of an
analytic regular part and the simple pole term
`(s - 1)⁻¹ * (Gammaℝ s)⁻¹`. -/
lemma meromorphicAt_riemannZeta_one :
    MeromorphicAt riemannZeta 1 := by
  let regular : ℂ → ℂ := fun s =>
    (completedRiemannZeta₀ s - 1 / s) * (Gammaℝ s)⁻¹
  let pole : ℂ → ℂ := fun s =>
    (s - 1)⁻¹ * (Gammaℝ s)⁻¹
  have hcompleted : AnalyticAt ℂ completedRiemannZeta₀ 1 :=
    differentiable_completedZeta₀.analyticAt 1
  have hone_div : AnalyticAt ℂ (fun s : ℂ => 1 / s) 1 := by
    exact (analyticAt_const.div analyticAt_id one_ne_zero)
  have hgamma_inv : AnalyticAt ℂ (fun s : ℂ => (Gammaℝ s)⁻¹) 1 :=
    differentiable_Gammaℝ_inv.analyticAt 1
  have hregular : MeromorphicAt regular 1 := by
    exact ((hcompleted.sub hone_div).mul hgamma_inv).meromorphicAt
  have hsub : MeromorphicAt (fun s : ℂ => s - 1) 1 :=
    (analyticAt_id.sub analyticAt_const).meromorphicAt
  have hpole : MeromorphicAt pole 1 := by
    exact hsub.inv.mul hgamma_inv.meromorphicAt
  have hsum : MeromorphicAt (fun s => regular s + pole s) 1 :=
    hregular.add hpole
  refine hsum.congr ?_
  filter_upwards [eventually_ne_nhdsWithin one_ne_zero, self_mem_nhdsWithin] with s hs0 _hs1
  simp only [regular, pole]
  rw [riemannZeta_def_of_ne_zero hs0, completedRiemannZeta_eq, div_eq_mul_inv]
  have hden : (1 - s) = -(s - 1) := by ring
  rw [hden]
  simp [div_eq_mul_inv]
  have hinv : (s - 1)⁻¹ = - (1 - s)⁻¹ := by
    have hlin : (s - 1) = -(1 - s) := by ring
    rw [hlin, inv_neg]
  rw [hinv]
  ring

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
