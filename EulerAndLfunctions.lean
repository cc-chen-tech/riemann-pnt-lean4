/-
# Euler Products and Dirichlet L-Functions

## Overview

This file bridges Mathlib's existing Euler product and Dirichlet L-function theory
to the project's framework. The declarations here are convenience wrappers around
Mathlib results and have no proof placeholders.

Mathlib theorems used:
- `riemannZeta_eulerProduct_tprod` — Euler product for ζ(s), Re(s) > 1
- `riemannZeta_two` — ζ(2) = π²/6
- `riemannZeta_zero` — ζ(0) = -1/2
- `riemannZeta_re_pos_of_one_lt` — ζ(s) > 0 for real s > 1
- `riemannZeta_ne_zero_of_one_lt_re` — ζ(s) ≠ 0 for Re(s) > 1
- `riemannZeta_ne_zero_of_one_le_re` — ζ(s) ≠ 0 for Re(s) ≥ 1
- `DirichletCharacter.LSeries_ne_zero_of_one_lt_re` — LSeries nonvanishing
- `LFunction_eq_LSeries` — analytic continuation agrees with series for Re(s) > 1

## Key results in this file

1. `EulerProduct.euler_product` — Euler product in project notation
2. `EulerProduct.euler_product_inv` — reciprocal of the verified Euler product
3. `ZetaValues.zeta_two` — ζ(2) = π²/6
4. `ZetaValues.zeta_zero` — ζ(0) = -1/2
5. `ZetaValues.zeta_pos_real` — ζ(s) > 0 for s > 1 (real)
6. `ZetaValues.zeta_ne_zero` — ζ(s) ≠ 0 for Re(s) > 1
7. `DirichletNonvanishing.lseries_ne_zero` — L(s,χ) ≠ 0, Re(s) > 1
8. `DirichletNonvanishing.lfunction_ne_zero` — LFunction ≠ 0, Re(s) > 1

## Dependencies

- Mathlib (LSeries, DirichletCharacter, RiemannZeta)
- RiemannExplorer (for KnownResults)
-/

import Mathlib
import RiemannExplorer

open Complex
open scoped ArithmeticFunction LSeries.notation

/-! ## Euler Product Theory -/

namespace EulerProduct

/-- Euler product for ζ(s): ζ(s) = ∏_{p prime} 1/(1-p^{-s}) for Re(s) > 1.
    Direct wrapper around Mathlib's `riemannZeta_eulerProduct_tprod`. -/
theorem euler_product (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s = ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹ := by
  have h := riemannZeta_eulerProduct_tprod hs
  rw [← h]

/-- Reciprocal of the verified Euler product for ζ(s), for Re(s) > 1. -/
theorem euler_product_inv (s : ℂ) (hs : 1 < s.re) :
    (riemannZeta s)⁻¹ = (∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹)⁻¹ := by
  rw [riemannZeta_eulerProduct_tprod hs]

end EulerProduct

/-! ## Zeta Function Special Values -/

namespace ZetaValues

/-- ζ(2) = π²/6 — the Basel problem, proved by Euler (1734).
    Wrapper around Mathlib's `riemannZeta_two`. -/
theorem zeta_two : riemannZeta (2 : ℂ) = ((Real.pi : ℂ) ^ 2) / 6 := by
  simpa using riemannZeta_two

/-- ζ(0) = -1/2.
    Follows from the functional equation relating ζ(0) to ζ(1). -/
theorem zeta_zero : riemannZeta (0 : ℂ) = (-1 : ℂ) / 2 := by
  exact riemannZeta_zero

/-- ζ(s) is positive real for real s > 1.
    Directly from the Dirichlet series: every term 1/n^s > 0. -/
theorem zeta_pos_real {s : ℝ} (hs : 1 < s) : 0 < (riemannZeta (s : ℂ)).re := by
  simpa using riemannZeta_re_pos_of_one_lt hs

/-- ζ(s) ≠ 0 for Re(s) > 1.
    Immediate from the Euler product (every factor is nonzero). -/
theorem zeta_ne_zero {s : ℂ} (hs : 1 < s.re) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re hs

/-- ζ(s) ≠ 0 on the closed half-plane `Re(s) ≥ 1`.
    Wrapper around Mathlib's boundary-inclusive nonvanishing theorem. -/
theorem zeta_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs

/-- Coordinate form of ζ(s) ≠ 0 on the closed half-plane `Re(s) ≥ 1`. -/
theorem zeta_ne_zero_re_im_of_one_le {β t : ℝ} (hβ : 1 ≤ β) :
    riemannZeta ((β : ℂ) + I * t) ≠ 0 := by
  exact zeta_ne_zero_of_one_le_re (by simpa using hβ)

end ZetaValues

/-! ## Dirichlet L-Function Nonvanishing -/

namespace DirichletNonvanishing

open DirichletCharacter

/-- For Re(s) > 1, the Dirichlet L-series of χ does not vanish.
    Follows from the Euler product: L(s,χ) = ∏_p 1/(1-χ(p)p^{-s}) ≠ 0.
    Direct wrapper around Mathlib. -/
theorem lseries_ne_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun (n : ℕ) => χ ↑n) s ≠ 0 :=
  DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ hs

/-- For Re(s) > 1, the analytically continued LFunction equals the LSeries,
    hence also does not vanish.
    Uses Mathlib's `LFunction_eq_LSeries` to bridge the two definitions. -/
theorem lfunction_ne_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) : LFunction χ s ≠ 0 := by
  rw [LFunction_eq_LSeries χ hs]
  exact lseries_ne_zero χ hs

/-- Coordinate form of `LFunction` nonvanishing in `Re(s) > 1`. -/
theorem lfunction_ne_zero_re_im {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {σ t : ℝ} (hσ : 1 < σ) :
    LFunction χ ((σ : ℂ) + I * t) ≠ 0 := by
  exact lfunction_ne_zero χ (by simpa using hσ)

end DirichletNonvanishing
