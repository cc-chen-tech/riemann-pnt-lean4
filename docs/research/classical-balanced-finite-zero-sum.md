# Classical balanced finite zero sum

## Quantitative transfer

At the selected balanced good height

```text
H_b(m) in
  [exp(sqrt(b) * sqrt(log m)) - 1,
   exp(sqrt(b) * sqrt(log m))],
```

the actual finite zero sum includes:

- every nontrivial zero with ordinate up to `H_b(m)`;
- analytic multiplicity;
- the kernel factor `m^rho / rho`.

For every `epsilon` satisfying

```text
0 < epsilon < sqrt(b),
```

the new theorem proves, beyond explicit lower thresholds,

```text
norm finiteZeroSum(m, H_b(m))
  <= C * m
       * exp (-(sqrt(b) - epsilon) * sqrt(log m))
       * (1 + log(H_b(m) + 6))^2.
```

The proof chain is:

```text
actual classical moving right edge
  -> epsilon-sharp width at the balanced height
  -> exponent comparison for m^(1-width)
  -> global reciprocal multiplicity bound
  -> full finite zero-sum estimate.
```

This is not a pointwise kernel estimate: the complete finite sum is bounded,
with multiplicities visible in the proved constant and logarithmic factor.

## Remaining upper-bound assembly

The zero contribution is now at the correct near-optimal square-root
exponential scale.  The remaining assembly step is to bound the selected
contour certificate at the same scale and absorb the visible logarithmic
factors into an arbitrarily small exponential-rate loss.

Carlson density is deliberately absent from this classical global
zero-free-region estimate.  It should be introduced only for stripwise
profiles where a global cap no longer controls the whole zero sum.
