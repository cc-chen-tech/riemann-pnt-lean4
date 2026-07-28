# Dynamic-boundary witness transfer

## Scope

This module is a transfer boundary, not a new oscillation theorem.  It connects
the moving equal-real-part package used by the dynamic Carlson decomposition to
the genuine relative Chebyshev error.

The input is

```text
moving package has far natural-point witnesses at
  c * x^(beta - 1),
```

together with the already established explicit-formula statement

```text
relative PNT error - moving package = o(x^(beta - 1)).
```

For every fixed `loss > 0`, the output is a genuine PNT-error witness at

```text
(c - loss) * x^(beta - 1).
```

If `loss < c`, this coefficient is strictly positive.

## Constant and scale bookkeeping

There is no fixed `1 / 2` loss in this transfer.  Because the full residual is
little-oh of the target amplitude, the loss can be chosen arbitrarily small.
Any multiplicity or `1 / |rho|` factor proved by a local oscillation theorem is
carried inside `c`.

For the relative error `(psi0(x) - x) / x`, the target is `x^(beta - 1)`.
After undoing the normalization by `x`, this is the expected
`x^beta / |rho|` scale when `c` contains the zero coefficient.

## Deliberate open input

The module does not prove that the moving package has far witnesses.  In
particular it does not formalize a zero-reproduction tree, a growing-dimensional
anti-cancellation theorem, or a sharp local pi-over-two argument.  Those are
separate analytic inputs and can be connected through the two transfer
theorems without changing the density or explicit-formula layer.
