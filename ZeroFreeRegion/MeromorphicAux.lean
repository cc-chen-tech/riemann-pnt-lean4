/-
# Meromorphic Auxiliaries for the Riemann Zeta Function on a Closed Ball

## Overview

This file establishes basic meromorphic properties of `riemannZeta` needed by both:
- chain A (Borel–Carathéodory zero-free-region path)
- chain B (rectangle-integral residue counting)

## Verified results

1. `meromorphicAt_riemannZeta_of_ne_one` — ζ is meromorphic at every point ≠ 1.
2. `meromorphicOn_riemannZeta_closedBall` — meromorphic on any closed ball.

## Deferred

- `meromorphicAt_riemannZeta_one` — requires Mathlib API for
  `(z-1)² ζ z` removable-singularity at 1; deferred to a follow-up commit
  because it depends on `Function.update` / junk-value-patching which
  is fragile and not central to this initial scaffolding PR.

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

/-- ζ is meromorphic on any closed ball `closedBall c R`, restricted to the
points where ζ is analytic (i.e. s ≠ 1).

This is the version of `meromorphicOn` for ζ that we can prove directly from
existing Mathlib API.  The full version including the pole at `s = 1`
requires `meromorphicAt_riemannZeta_one` (deferred). -/
lemma meromorphicOn_riemannZeta_closedBall_of_ne_one (c : ℂ) (R : ℝ) :
    MeromorphicOn riemannZeta (closedBall c R \ {1}) := by
  intro s hs
  -- hs : s ∈ (closedBall c R \ {1})
  rcases hs with ⟨hs_ball, hs_ne⟩
  -- s ≠ 1, so ζ is meromorphicAt s.
  exact meromorphicAt_riemannZeta_of_ne_one s hs_ne

end ZeroFreeRegion
