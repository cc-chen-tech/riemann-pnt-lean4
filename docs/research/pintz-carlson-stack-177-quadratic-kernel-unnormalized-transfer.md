# Stack 177: unnormalized quadratic-kernel transfer

## Exact scale

The relative reciprocal-height amplitude is

```text
x^(beta(x) - 1) / x^alpha.
```

Multiplying by `x` gives

```text
x^(beta(x) - alpha) = x^beta(x) / x^alpha.
```

Thus, when the selected target zero has size comparable with
`H(x) = x^alpha`, this is the correct `x^Re(rho) / |rho|` scale.

## Transfer

The Stack176 quadratic-kernel certificate and one unsigned natural-point
moving-main witness now imply:

- a positive surviving coefficient `c - loss`;
- `Omega_+` or `Omega_-` for the actual unnormalized centered Chebyshev error;
- the exact variable scale `(c-loss) x^(beta(x)-alpha)`.

## Claim boundary

The actual order-two smoothed zeta kernel and its moving-main witness remain
unproved inputs.  This stack proves a one-sign alternative, not both signs,
and does not imply RH.
