# Carlson two-height split

## Purpose

The growing-ordinate rectangle estimate cannot cover all positive zeta zeros:
any fixed zero eventually lies below a floor tending to infinity.  The
non-vacuous construction must split the truncated zero sum at an intermediate
height.

Let

```text
q = 4 sigma (1 - sigma),
T(x) = x^alpha,
U(x) = x^gamma.
```

For a real strip with upper endpoint `tau`:

```text
low ordinates:  N(sigma, U) * x^(tau - 1)
high ordinates: N(sigma, T) * x^(tau - 1) / U.
```

Ignoring the fourth logarithmic power, the exponents are

```text
L(gamma) = q gamma + tau - 1,
H(gamma) = q alpha + tau - 1 - gamma.
```

They are equal at

```text
gamma* = q alpha / (q + 1).
```

The common exponent is

```text
tau - 1 + q^2 alpha / (q + 1).
```

This is strictly smaller than the unsplit outer-height exponent
`q alpha + tau - 1` whenever `1/2 < sigma < 1` and `alpha > 0`.

## Lean theorem chain

The module
`PrimeNumberTheorem/ZeroDensityLayerBudgetCarlsonTwoHeightSplit.lean`
proves:

1. `0 < gamma* < alpha`;
2. exact equality of the low and high exponents at `gamma*`;
3. strict improvement over a single outer-height count;
4. decay of the sum of the two Carlson logarithmic majorants under one
   balanced negative-margin hypothesis.

## Honest boundary

This slice is the optimized arithmetic and asymptotic majorant.  It does not
yet claim that the low and high filtered zeta-zero finsets have been
constructed.  The next implementation step is a certified partition of the
actual positive truncated zero finset into

```text
0 < Im rho <= U(x)
```

and

```text
U(x) < Im rho <= T(x),
```

followed by the corresponding multiplicity-count and kernel bounds.
