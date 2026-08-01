# Stack 176: quadratic-kernel moving PNT certificate

## Certificate

A proposed smoothed moving main term must provide an eventual bound

```text
|relativeChebyshevPsi0Error(m) - main(m)|
  <= C m^(-2 alpha) (1 + log m)^2
```

with `C >= 0`.

## Automatic transfer

Under the existing contour margin `1 - beta0 < alpha` and an eventually
larger moving exponent `beta(m) >= beta0`, the certificate implies residual
negligibility at

```text
m^(beta(m) - 1) / m^alpha.
```

One unsigned far-point witness for the proposed main term at coefficient `c`
then yields a positive surviving coefficient `c - loss` and an `Omega_+` or
`Omega_-` alternative for the genuine relative Chebyshev error at exactly
that reciprocal-height scale.

## Mathematical role

This is the abstract interface between a future order-two smoothed explicit
formula and the existing moving-boundary anti-cancellation machinery.  Unlike
an ordinary `o(m^(beta-1))` remainder assumption, its displayed bound is
strong enough to retain the natural `1 / |rho|` coefficient when
`|rho|` is comparable with the polynomial truncation height.

## Claim boundary

The source does not construct the smoothed zeta kernel and does not prove the
certificate for the actual zeta main term.  The conclusion is a one-sign
alternative, not simultaneous signed Omega, and does not imply RH.
