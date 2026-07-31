# Strict-margin grid transfer for the full actual PNT budget

## Problem

Stack 125 minimizes the actual Pintz hybrid PNT budget over a finite rate
grid. Stack 126 proves a `1 / q` approximation for the continuous classical
profile

`min k (b / k)`.

These statements cannot be composed by identifying their constants. The
singleton low-density term in Stack 125 is controlled by the Pintz envelope,
whereas `b / k` is supplied by the classical zero-free region. Moreover, the
actual finite-zero estimate contains `log (T + 6)`, so an eventual pointwise
bound needs a strict margin below `b / k`.

## Design

Fix `0 < theta < 1`. At truncation rate `k`, use the strict zero-free rate

`theta * b / k`.

Its product with the height rate is `theta * b < b`, which is exactly the
strict inequality needed to absorb the additive constant in `log (T + 6)`.
The competing analytic rate is therefore

`min k (theta * b / k) = classicalDynamicBalancedRate (theta * b) k`.

Stack 126 applies unchanged after replacing `b` by `theta * b`. If the finite
grid contains a multiplicative `q`-approximation to the constrained optimizer
for `theta * b`, the envelope-optimal grid rate retains at least

`classicalAdmissibleBalancedRate (theta * b) / q`.

## Components

The Lean module introduces:

- `classicalStrictMarginZeroFreeRate`, with positivity and strict-margin
  multiplication lemmas;
- an arbitrary-rate full-budget analytic envelope with separate contour and
  zero-free coefficients plus a rate-independent residual;
- a closed grid envelope at the explicit `1 / q` rate;
- a transparent predicate saying that an actual Stack 125 rate budget is
  eventually dominated by the analytic envelope;
- transfer theorems from that predicate to the pointwise minimum actual budget
  and then to the real relative `psi0` error.

## Claim boundary

This slice proves the arithmetic and optimizer transfer once the actual
per-rate domination is supplied. It does not prove that the Stack 125 Pintz
hybrid budget automatically satisfies the classical strict-margin envelope.
That requires a separate theorem aligning the actual finite-zero and contour
decomposition at the same selected height.

It does not prove continuous optimality of the discontinuous actual budget,
an unconditional Omega theorem, RH, or a VK-edge constant.

## Audit

The contract checks every public definition and theorem. The axiom audit
prints the strict-margin identity and the final real-error transfer theorem.
The expected axiom boundary is the repository baseline:

`propext`, `Classical.choice`, and `Quot.sound`.
