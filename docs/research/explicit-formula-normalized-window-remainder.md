# Normalized explicit-formula remainder on fixed log windows

## Verified endpoint

For fixed `1 / 2 < beta < 1`, fixed `L >= 0`, and every `eta > 0`,
the Lean theorem

```lean
eventually_exists_uniform_goodHeight_normalized_window_remainder_lt
```

proves that, for all sufficiently large logarithmic centers `a`, one can
select a single good height

```text
T in [exp(a / 2), exp(a / 2) + 1]
```

such that every real `y in [a, a + L]` satisfies

```text
exp(-beta * y) *
  ||explicitFormulaApproxWithMultiplicity (exp y) T - psi0(exp y)|| < eta.
```

The selected height is shared by the entire real window.  The proof uses the
uniform real-sample explicit-formula estimate, controls the interpolation and
closed-term errors, and absorbs the resulting quadratic factors into
`exp((1 / 2 - beta) * a)`.

## Boundary

This is an unconditional approximation-remainder theorem.  It does not control
the complementary zero package in the VK-edge cluster argument.  Consequently
it does not prove a localized oscillation theorem, a zero-density
contradiction, or RH.
