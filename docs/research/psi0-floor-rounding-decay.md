# Decay of the psi0 floor-rounding budget

## Pointwise estimate

For every `x >= 1`,

```text
0 <= jumpVonMangoldt x <= log x.
```

Applying this both at `x` and at `floor x`, using
`log (floor x) <= log x`, and bounding `x - floor x` by one gives

```text
chebyshevPsi0FloorRoundingBudget x <= log x + 1.
```

## Scale consequence

For every `beta > 0`,

```text
chebyshevPsi0FloorRoundingBudget = o(x ^ beta).
```

Thus converting a continuous explicit-formula witness at `x = exp y` to the
natural point `floor (exp y)` does not change its leading zero-forced power
scale.  A fixed coefficient such as `1 / |rho|` is therefore preserved after
an arbitrarily small asymptotic loss.

## Boundary

This result controls only sampling loss.  It does not provide the
complementary-zero energy upper bound needed for an unconditional Omega
theorem.
