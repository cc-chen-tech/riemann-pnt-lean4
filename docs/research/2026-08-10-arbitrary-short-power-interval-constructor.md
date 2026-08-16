# Arbitrary short power-interval constructor

## Purpose

The analytic parameter lemmas are most convenient under

```text
1 < lambda < 2.
```

The final oscillation theorem, however, must work in every requested interval

```text
[Y, Y^(1 + epsilon)]
```

with `epsilon > 0`.  This note gives one explicit constructor connecting the
two statements and records every threshold required by the long triangle
observation kernel.

## Explicit interval exponent

Fix

```text
0 < epsilon.
```

Define

```text
intervalSlack := min (epsilon / 2) (1 / 2),
lambda        := 1 + intervalSlack.
```

Then

```text
0 < intervalSlack,
intervalSlack <= 1/2,
intervalSlack < epsilon,

1 < lambda,
lambda <= 3/2,
lambda < 2,
lambda < 1 + epsilon.
```

The strict inequality `intervalSlack < epsilon` follows in both cases:

- if `epsilon / 2 <= 1/2`, then `intervalSlack = epsilon/2 < epsilon`;
- otherwise `1 < epsilon`, so `intervalSlack = 1/2 < epsilon`.

No smallness assumption on the requested `epsilon` is needed.

## Interval inclusion

Assume

```text
1 <= Y.
```

Real exponentiation is monotone in the exponent at such a base, so

```text
Y^lambda <= Y^(1 + epsilon).
```

Consequently

```text
Set.Icc Y (Y^lambda)
  subset Set.Icc Y (Y^(1 + epsilon)).
```

Any witness constructed in the internal interval is therefore a witness in
the user-requested interval.

The proof should be stated as a reusable interval-inclusion theorem rather
than repeated at the final oscillation theorem.

## Logarithmic observation interval

For the internal interval, define

```text
uMin := log Y,
uMax := lambda * log Y,
u0   := (uMin + uMax) / 2,
L    := (uMax - uMin) / 2.
```

Then

```text
L = intervalSlack * log Y / 2.
```

The complex triangle-Laplace row-mass argument uses `L >= 1`.  An explicit
sufficient threshold is

```text
log Y >= 2 / intervalSlack,
```

or equivalently

```text
Y >= exp (2 / intervalSlack).
```

Beyond this threshold,

```text
0 < L,
1 <= L.
```

The threshold depends on the requested interval width, as expected, but the
oscillation constant and target-zero scale do not.

## Compatibility with beta > 1/2 feasibility

Fix

```text
1/2 < beta < 1
```

and put

```text
g := lambda * (1 - beta).
```

Since `lambda < 2` and `1 - beta < 1/2`,

```text
0 < g < 1.
```

Since `beta > 1/2`,

```text
g < lambda / 2.
```

Thus the explicit `lambda` satisfies every base hypothesis of the direct-L2
middle-tail and cubic two-height feasibility construction:

```text
alpha := (1 + g) / 2,
d     := (1 - g) / 8,
```

with

```text
g < alpha < 1,
0 < d.
```

No new lower bound on `beta` is introduced by the arbitrary requested
`epsilon`.

## Exact witness conversion

Suppose the internal transfer theorem provides

```text
x in Set.Icc Y (Y^lambda)
```

and

```text
|E(x)|
  >= c * x^beta / |rho0|.
```

Then the interval inclusion immediately gives

```text
x in Set.Icc Y (Y^(1 + epsilon))
```

with the identical lower bound.  In particular, if

```text
pi / 2 < c,
```

the strict sharp constant is unchanged when passing to the requested
interval.

The conversion loses neither a power of `Y`, a power of `|rho0|`, nor any part
of the oscillation surplus.

## Threshold ledger

The final theorem should combine the following lower bounds on `Y` by taking
their maximum:

```text
Y >= 1,
Y >= exp (2 / intervalSlack),
Y >= retained-cluster cubic-fidelity threshold,
Y >= direct-L2 middle-tail threshold,
Y >= cubic high-tail threshold,
Y >= contour threshold,
Y >= sZero threshold,
Y >= trivial-zero threshold.
```

Every threshold should be exposed or collected by a typed finite maximum.
The phrase "for sufficiently large Y" may be a final corollary, but it must be
derived from this explicit ledger rather than hiding incompatible thresholds.

## Proposed arithmetic theorem chain

```text
shortIntervalSlack
shortIntervalSlack_pos
shortIntervalSlack_le_half
shortIntervalSlack_lt_epsilon
shortIntervalLambda
one_lt_shortIntervalLambda
shortIntervalLambda_lt_two
shortIntervalLambda_lt_one_add_epsilon
rpow_shortIntervalLambda_le
shortIntervalIcc_subset
shortIntervalTriangleHalfWidth_eq
one_le_shortIntervalTriangleHalfWidth
shortIntervalSupportGap_lt_one
shortIntervalSupportGap_lt_halfCap
shortIntervalWitnessTransfer
```

Names are provisional.

## Audit rules

- Keep the requested `epsilon` distinct from kernel-error tolerances.
- Keep `intervalSlack` distinct from the cubic relative width `eta = Y^(-d)`.
- Require `1 <= Y` for exponent monotonicity.
- Record the explicit `L >= 1` threshold.
- Preserve the exact witness constant and `x^beta/|rho0|` scale.
- Do not claim that a witness in the larger interval lies in the internal
  interval; only the forward inclusion is used.
- Do not strengthen the absolute witness to a signed conclusion.
