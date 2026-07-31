# Carlson-Weighted Optimal Polynomial-Height Window Design

## Goal

Instantiate the weighted minimax optimizer with Carlson's classical density
slope `q(sigma) = 4 sigma (1 - sigma)`, expose the exact critical real-part
threshold, and construct the corresponding actual selected-height and
explicit-formula remainder certificate.

## Scope and claim boundary

This stack names and uses the exponent already present in the formalized
Carlson asymptotic estimate. It does not alter or strengthen that estimate,
does not formalize newer external density bounds, and does not close the
conditional visible-main witnesses required by the signed transfer. It makes
no RH or unconditional Omega claim and does not modify protected, Sharp, or
VK-edge modules.

## Exact threshold

For

```text
q(sigma) = 4 sigma (1 - sigma),
```

the Stack147 weighted feasibility gap is

```text
W(beta, sigma) = beta - sigma - q(sigma) * (1 - beta).
```

Since `q(sigma) + 1 > 0` on `0 <= sigma <= 1`, elementary rearrangement gives

```text
0 < W(beta, sigma)
  iff
(sigma + q(sigma)) / (1 + q(sigma)) < beta.
```

The quotient is the exact Carlson-weighted critical real part. On
`0 < sigma < 1` it lies strictly between `sigma` and `1`.

## Strict improvement over unit slope

For `1/2 < sigma < 1`,

```text
0 < q(sigma) < 1.
```

Consequently,

```text
sigma
  < (sigma + q(sigma)) / (1 + q(sigma))
  < (1 + sigma) / 2.
```

Thus using Carlson's actual power slope lowers the bookkeeping threshold from
the unit-slope critical half to the exact smaller quotient. This is an
optimization of the transfer budget, not a stronger zero-density theorem.

## Lean interface

The new module provides:

1. A canonical name for Carlson's polynomial density slope.
2. The exact critical real-part definition and location theorems.
3. An iff theorem between positive weighted gap and strict criticality.
4. A strict comparison with the previous unit-slope threshold.
5. Carlson-specialized minimax exponents and selected-height/remainder
   certificates.

The contract locks this interface. The axiom audit must report only
`propext`, `Classical.choice`, and `Quot.sound`.
