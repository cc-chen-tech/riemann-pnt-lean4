# Actual Carlson two-height zeta split

## Constructed sets

For fixed real endpoints `sigma < Re rho <= tau`, outer height `T`, and
intermediate height `U`, the Lean module constructs:

```text
low  = {rho : 0 < Im rho <= U},
high = {rho : U < Im rho <= T}.
```

Both are filters of the actual finite zeta-zero set counted with analytic
multiplicity.  When `U <= T`, their union is the complete actual strip and
the union is disjoint.

## Kernel and count bounds

The low piece uses

```text
sigma < Re rho <= |Re rho| <= |rho|,
```

so

```text
|x^(rho-1) / rho| <= x^(tau-1) / sigma.
```

Its multiplicity mass is at most `N(sigma,U)`.

The high piece uses `U < Im rho <= |rho|`, so

```text
|x^(rho-1) / rho| <= x^(tau-1) / U.
```

Its multiplicity mass is at most `N(sigma,T)`.

## Transfer theorem

At

```text
T = x^alpha,
U = x^gamma,
```

`tendsto_sum_norm_actualPositiveCarlsonStrip_twoHeight` proves that the
complete actual multiplicity-weighted zeta-kernel mass in the strip tends to
zero when both two-height exponents have a strict negative margin.

This closes the gap explicitly left by the arithmetic-only module: the
filtered sets are now genuine zeta-zero finsets, not an abstract bucket
family.
