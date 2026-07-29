# Classical zero-free dynamic profile

## Purpose

The fixed right-edge transfer uses a constant `beta < 1`.  That hypothesis is
too strong to represent the proved classical zeta zero-free region, whose
boundary approaches `1` as the truncation height grows.

This module records the first actual height-dependent bridge:

```text
classical zeta zero-free region
  + compact bounded-height patch
  -> rho.re <= 1 - b / log (T + 6)
     for every rho in nontrivialZerosFinset T.
```

The bridge reuses the proved theorem
`ExplicitFormulaAux.exists_nontrivialZero_re_le_one_sub_div_log_truncation`.
It does not assume RH and does not introduce a hypothetical zero-free
predicate.

## Dynamic truncation arithmetic

Put

```text
log T = alpha * sqrt (log x).
```

At this scale the two competing exponential rates are:

```text
contour rate   = alpha,
zero-free rate = b / alpha.
```

The common guaranteed rate is therefore

```text
min alpha (b / alpha).
```

The Lean theorem `classicalDynamicBalancedRate_isMax` proves that its exact
maximum over all real `alpha` is `sqrt b`, attained at
`alpha = sqrt b`.  The theorem
`add_competing_exp_le_optimal_exp` then gives the corresponding combined
majorant

```text
exp (-sqrt(b) * u) + exp (-(b / sqrt(b)) * u)
  <= 2 * exp (-sqrt(b) * u).
```

This is the arithmetic core of the optimal classical dynamic truncation
height.  It is stronger and more reusable than fixing an arbitrary small
height exponent.

## Honest boundary

This step supplies:

- an actual zeta-zero moving right edge;
- the low-height compact patch;
- the exact optimizer for the two principal decay rates.

It does not yet prove that the repository's selected good contour height lies
at the exact balanced scale, and it does not yet combine Carlson layer counts
with a Vinogradov-Korobov boundary.  Those are separate analytic bridges.

No oscillation or RH conclusion follows from this upper-bound profile.
