# Shared-height L1/L2 cubic exponent ledger

## Purpose and scope

This note specializes the finite affine minimax certificate to one explicit
parameter choice for the normalized zero complement.  It combines:

- the Carlson linear-mass `L1` shell exponent;
- the multiplicity-weighted Schur `L2` shell exponent;
- the cubic contour remainder;
- the residue at `s = 0`;
- the trivial-zero remainder.

It is only an exponent ledger.  It does not prove the sharp lower energy
theorem, Gram/Schur occupancy, or the final signed oscillation theorem.

The important logical separation is:

- direct `L2` alone has a feasible height range for every `beta > 1/2`;
- requiring one height to satisfy both the normalized `L1` and `L2` ledgers
  imposes the stronger condition `beta > 5/8` for the explicit choice below;
- this `5/8` threshold is not a Carlson impossibility statement and is not a
  barrier for the direct `L2` route.

## Parameters

Fix

```text
1/2 < beta < 1,
1 < lambda < 2,
b := 2 * beta - 1,
g := lambda * (1 - beta).
```

The interval in logarithmic coordinates is

```text
[log X, lambda * log X].
```

The assumption `lambda < 2` implies `0 < g < 1`.  Set the outer cubic
contour and short smoothing parameters to

```text
alpha := (1 + g) / 2,
d     := (1 - g) / 8.
```

Thus

```text
g < alpha < 1,
0 < d.
```

For a requested interval `[X, X^(1 + epsilon)]`, it is enough to choose any
`lambda` with

```text
1 < lambda < min (2, 1 + epsilon).
```

A witness found in the shorter interval is also a witness in the requested
interval.

## Carlson density exponent

Write

```text
q(sigma) := 4 * sigma * (1 - sigma)
```

and define the endpoint-support function

```text
kappa_lambda(r) := r          if r <= 0,
                   lambda * r if 0 <= r.
```

For a strip whose real parts are represented by `sigma`, and a dyadic height
`T = X^gamma`, the normalized shell exponents are:

```text
L1(sigma, gamma)
  := kappa_lambda(sigma - beta) + gamma * (q(sigma) - 1),

L2(sigma, gamma)
  := 2 * kappa_lambda(sigma - beta) + gamma * (q(sigma) - 2).
```

The `L1` denominator is one reciprocal zero height.  The `L2` denominator is
the square reciprocal height supplied by the triangle-Laplace kernel.  The
weighted Schur reduction uses Carlson's linear analytic-multiplicity mass and
costs one local logarithm, so the current `L2` logarithmic loss is

```text
(log X)^5 = Carlson (log X)^4 * local weighted occupancy (log X).
```

There is no additional maximum-multiplicity logarithm in this route.

## Direct L2 range

For `sigma <= beta`,

```text
L2(sigma, gamma) <= -gamma.
```

For `beta <= sigma <= 1`, if `gamma < lambda / 2`, the right-hand branch is
increasing and its maximum is at `sigma = 1`:

```text
L2(1, gamma) = -2 * (gamma - g).
```

Consequently, if

```text
g < gamma < lambda / 2,
```

then

```text
r2 := min gamma (2 * (gamma - g)) > 0
```

and the infinitesimal-strip envelope is at most `-r2`.

This interval for `gamma` is nonempty exactly when `beta > 1/2`.  Equality
`gamma = g` is critical: the top-strip polynomial exponent is zero and the
remaining `(log X)^5` does not decay.

## Optional shared L1 and L2 height

The `L1` envelope can be calculated exactly.  For `sigma <= beta`, put
`y = 2 * sigma - 1`, so `0 <= y <= b`.  Then

```text
L1 = (y - b) / 2 - gamma * y^2.
```

For `sigma >= beta`, put `y = 2 * sigma - 1`, so `b <= y <= 1`.  Then

```text
L1 = (lambda / 2) * (y - b) - gamma * y^2.
```

Completing the square on the two branches gives the sufficient uniform
bounds

```text
L1 <= -(b / 2 - 1 / (16 * gamma)),
L1 <= -(lambda * b / 2 - lambda^2 / (16 * gamma)).
```

Both margins are positive when

```text
gamma > lambda / (8 * b).
```

Combining this with the direct `L2` cap `gamma < lambda / 2` is possible
exactly when

```text
b > 1/4,
```

equivalently

```text
beta > 5/8.
```

Again, this is only the threshold for a shared `L1`/`L2` height under this
ledger.  It does not exclude the direct `L2` argument for `1/2 < beta <= 5/8`.

## Explicit shared-height witness

Assume `beta > 5/8`, hence `b > 1/4`, and choose the midpoint

```text
gamma := (lambda / (8 * b) + lambda / 2) / 2
       = lambda * (4 * b + 1) / (16 * b).
```

Then

```text
lambda / (8 * b) < gamma < lambda / 2,
g < gamma.
```

The last inequality follows from

```text
gamma - g
  = lambda * (8 * b^2 - 4 * b + 1) / (16 * b) > 0,
```

because the quadratic `8 * b^2 - 4 * b + 1` has negative discriminant.

Define the two explicit `L1` margins

```text
mLeft
  := b / 2 - 1 / (16 * gamma)
   = b * (lambda * (4 * b + 1) - 2)
       / (2 * lambda * (4 * b + 1)),

mRight
  := lambda * b / 2 - lambda^2 / (16 * gamma)
   = lambda * b * (4 * b - 1) / (2 * (4 * b + 1)),

m1 := min mLeft mRight.
```

All three are strictly positive.  Define

```text
r2 := min gamma (2 * (gamma - g)) > 0.
```

The infinitesimal envelopes therefore satisfy

```text
L1 <= -m1,
L2 <= -r2.
```

## One finite strip mesh

For a strip `[sigmaL, sigmaR]` of width at most `delta`, compare its exponent
at `sigmaL`.  Since `kappa_lambda` is `lambda`-Lipschitz, replacing
`sigmaL` by the strip upper endpoint costs at most

```text
lambda * delta   in L1,
2 * lambda * delta in L2.
```

Choose the shared mesh width

```text
delta := min (m1 / (2 * lambda)) (r2 / (4 * lambda)).
```

Then every finite strip has the strict bounds

```text
L1Strip <= -m1 / 2,
L2Strip <= -r2 / 2.
```

The `L2` logarithmic loss is `(log X)^5`.  It can be absorbed into half of
the remaining polynomial margin, leaving the convenient asymptotic rate

```text
X^(-r2 / 4).
```

No decay is claimed at equality of any polynomial exponent.

## Cubic explicit-formula ledger

With

```text
alpha = (1 + g) / 2,
d     = (1 - g) / 8,
```

the already isolated nonzero exponents are:

```text
contour    = -(3 + g) / 4,
sZero      = -beta,
trivial    = 2 * d - 2 - beta
           = -(7 + g + 4 * beta) / 4.
```

They are all strictly negative under `1/2 < beta < 1`, `1 < lambda < 2`.
The pole at `s = 1` is not an error exponent: it cancels the exact triangular
main term.  The residue at `s = 0` has only a fixed polynomial logarithmic
factor, and every fixed logarithmic power is absorbed by its strict
`-beta` margin.

The combined post-log polynomial margin may therefore be chosen as

```text
eta := min (m1 / 4)
       (min (r2 / 4)
         (min ((3 + g) / 8)
           (min (beta / 2) ((7 + g + 4 * beta) / 8)))).
```

Every entry is strictly positive.  The factors of two reserve room for fixed
polylogarithmic losses and for finite-strip discretization; they are not
claimed to be optimized.

## Affine certificate packaging

After `beta`, `lambda`, and a finite strip mesh are fixed, each strip exponent
is affine in the remaining height variable `gamma`.  The formal certificate
should therefore contain:

```text
tag       : upperL1 | lowerL2 | contour | sZero | trivialZero
constant  : Real
slope     : Fin n -> Real
logLoss   : Nat
strictGap : Real
```

The checker should verify:

1. feasibility of the proposed parameter vector;
2. positivity of every declared `strictGap`;
3. each affine exponent is at most the negative declared gap;
4. fixed logarithmic losses are absorbed only after strict negativity;
5. deleting a finite zero set preserves each nonnegative Carlson mass bound.

The optimizer remains external.  Lean checks a finite primal/dual arithmetic
certificate and the analytic lemmas connecting each tagged row to its actual
zeta contribution.

## Proposed theorem chain

The next formal slice should be arithmetic-only:

```text
sharedHeightGamma
sharedHeightGamma_gt_l1Critical
sharedHeightGamma_lt_l2Cap
sharedHeightGamma_gt_supportCritical
sharedHeightL1LeftMargin_pos
sharedHeightL1RightMargin_pos
sharedHeightL1Envelope_le
sharedHeightL2Envelope_le
sharedHeightMesh_pos
sharedHeightL1StripExponent_neg
sharedHeightL2StripExponent_neg
cubicContourExponent_neg
cubicSZeroExponent_neg
cubicTrivialExponent_neg
sharedHeightCombinedMargin_pos
```

The theorem names are provisional.  This slice must not import or restate the
Sharp lower bound, Gram separation, or half-isolated occupancy results.

## Audit checklist

- Record the polynomial exponent and logarithmic loss separately.
- Mark equality cases as critical, never decaying.
- Keep analytic multiplicity in the Carlson linear mass.
- Do not insert an extra maximum-multiplicity logarithm after weighted Schur.
- Use nonnegative-mass monotonicity after deleting a finite set.
- Do not identify the `beta > 5/8` shared-height threshold with the direct
  `L2` threshold `beta > 1/2`.
- Do not identify `gamma` with the outer contour height `alpha`.
- Do not claim that this arithmetic ledger proves an unconditional
  oscillation theorem.
