# VK-edge zero-cluster closed-term L2 design

## Goal

Bound the closed-form part of the actual finite-zero-cluster remainder in
continuous logarithmic local second moments.

For `a >= 1`, `beta >= 0`, and `L >= 0`, prove an explicit estimate of the
form

```text
closedSecondMoment beta a L
  <= L * (exp (-beta * a) * B)^2
```

where

```text
B = log (2*pi) + (1/2) * exp (-2) / (1 - exp (-2)).
```

## Method

1. Reuse the existing pointwise closed-term estimate.
2. Show `q / (1-q)` is bounded by its value at `q = exp (-2)` whenever
   `y >= 1`.
3. Apply the normalization monotonicity
   `exp (-beta*y) <= exp (-beta*a)`.
4. Integrate the resulting constant bound over `[a, a+L]`.

## Additional API

Define normalized complement and approximation-error components and prove the
no-jump remainder is exactly their sum with the normalized closed term.  This
records that after PR #32 and this stage, only two analytic budgets remain.

## Boundary

This stage gives a genuine explicit upper bound for the closed term.  It does
not estimate the complementary zero sum or provide a truncation height that
works uniformly over a logarithmic window.
