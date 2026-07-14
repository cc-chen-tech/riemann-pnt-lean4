# PNT via a Dynamic First-Order Perron Contour

## Goal

Prove `PNTForm3` unconditionally from the existing first-order explicit
formula, classical zero-free region, and global zero-count estimates.

## Route

Keep the completed finite-zero-sum contour architecture and replace its fixed
right edge `c = 2` by

```lean
1 + 1 / Real.log (m : ℝ)
```

at natural samples `m >= 2`.  The required height is selected in a unit
interval above `exp (sqrt (b * log m))`, where `b` is a positive constant
obtained by combining the high-height zero-free region with its compact
low-height patch.

The proof has four mathematical units:

1. Quantify the near-one von Mangoldt Dirichlet-series norm by
   `O(epsilon ^ (-2))`.
2. Prove a uniform dynamic-line Perron error
   `O(m * (1 + log m) ^ 2 / T)` by retaining integer distance from the jump
   and using a quantitative p-series tail.
3. Replace the complete horizontal-edge factor `m ^ 2` by the moving-right
   factor `m ^ c(m) = exp 1 * m`, then assemble the dynamic truncated formula.
4. Bound the finite zero sum using the existing zero-free region and
   reciprocal zero-multiplicity mass, prove `psi(m) - m = o(m)`, extend from
   natural samples to real `x`, and derive `PNTForm3`.

## Claim Boundary

- A dynamic Perron theorem alone does not prove PNT; the horizontal edge must
  be sharpened to the same moving right endpoint.
- Any estimate retaining `m ^ 2 / T` or a constant chosen after `m` is
  insufficient for the subpolynomial height selection.
- No conditional endpoint proposition, `def ... : Prop`, or API-only alias
  counts as a completed unit.
- The route targets ordinary PNT only, not RH, a RH-scale error term,
  Vinogradov-Korobov, or zero exclusion on `Re(s) = 1 / 3`.

## Verification

Each unit starts with a failing Lean contract for the stronger theorem.
Completion requires focused builds, full `lake build`, inventory and chain
checks, and the axiom allowlist.
