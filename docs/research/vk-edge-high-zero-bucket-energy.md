# High-zero bucket energy

## Proved in this branch

For each natural number `n`, collect all nontrivial zeta zeros with

```text
n <= |Im rho| < n + 1
```

and count analytic multiplicity.  The repository's fixed-width local divisor
bound gives

```text
bucketMultiplicity(n) = O(log n).
```

Since `|rho| >= |Im rho| >= n`, the total explicit-formula coefficient mass
in one bucket satisfies

```text
bucketCoefficientMass(n) = O(log n / n).
```

The branch proves in Lean that

```text
sum_n bucketCoefficientMass(n)^2 < infinity.
```

It also proves the uniform finite-tail form: for every positive `eta`, every
sufficiently high finite interval of buckets has total squared mass below
`eta`.

This estimate is collision-safe.  Zeros in one unit interval may be
arbitrarily close or have repeated ordinates; the proof charges their complete
analytic multiplicity to the same bucket.

## Subsequent Gaussian bridge

The diagonal-energy result is now combined in the stacked Gaussian bucket
branch with a collision-safe Schur estimate.  That theorem controls all
cross-bucket Gaussian interactions by a constant multiple of this square
energy, without a minimum zero-spacing assumption.

The remaining analytic bridge is stronger: identify that Gaussian quadratic
form with the weighted local `L2` norm of the actual moving complementary zero
sum.  This still has to account for the moving truncation height and the
real-part drift of each zero coefficient.

Nothing here proves an unconditional zeta/PNT oscillation theorem, a
zero-density contradiction, or RH.
