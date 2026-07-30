# Finite phase sums under natural-floor sampling

After extracting the common power from an equal-real-part zero package, the
remaining factor is a finite Fourier sum

```text
P(y) = sum_z a_z exp(i gamma_z y).
```

The module proves the explicit global estimate

```text
norm(P(u) - P(v))
  <= (sum_z norm(a_z) * abs(gamma_z)) * abs(u - v).
```

It also proves

```text
log(floor x) - log(x) -> 0
```

and hence

```text
norm(P(log(floor x)) - P(log x)) -> 0.
```

This closes the oscillatory phase part of natural-point sampling without any
frequency-separation assumption.  The next bridge identifies the normalized
actual equal-real-part zeta-zero package with this finite phase sum.
