# Revesz prior-art boundary and the short-interval direct-L2 target

## Purpose

This note narrows the novelty claim for the Pintz-Carlson-explicit-formula
program.  A sharp oscillation constant by itself is not a new target.  The
candidate new mechanism is instead a quantitative, machine-checkable transfer
from actual zeta zero-density capacity to a short multiplicative interval,
while preserving the sharp constant supplied by the low-zero energy theorem.

This is a design and audit document.  It does not claim that the final zeta
theorem has already been proved.

## Prior-art boundary

Revesz proves for the classical Riemann zeta function that a prescribed zero
`rho0 = beta0 + i gamma0` forces arbitrarily large `x` with

```text
|Delta(x)| >= (pi / 2 - epsilon) * x^beta0 / |rho0|.
```

Consequently, none of the following is a valid standalone novelty claim:

- a single zeta zero causes an absolute-value Omega result;
- the scale is `x^(Re rho) / |rho|`;
- the constant can approach `pi / 2`;
- a finite conjugate-pair cluster can be handled by a power-sum argument.

The relevant source is:

- Szilard Gy. Revesz, *Oscillation of the remainder term in the prime number
  theorem of Beurling, caused by a given zeta-zero*, arXiv:2202.01837,
  <https://arxiv.org/abs/2202.01837>.

Revesz also gives a quantitative localization theorem in the Beurling setting,
but the resulting interval is of the form

```text
[Y, Y^(A * log(gamma0 + 5) / (beta0 - theta)^2)].
```

That is qualitatively different from a uniform interval
`[Y, Y^(1 + epsilon)]`.  The proof uses a modified Cassels power-sum theorem;
it is not the Carlson multiplicity-square direct-L2 complement proposed here.

## Precise candidate novelty

The target is the following implication, with every dependency exposed:

```text
actual Carlson strip count
  + local analytic multiplicity bound
  + half-isolated Occupancy / Gram-Schur bound
  + smoothed explicit formula with a second-order high-zero multiplier
  + strict low-zero energy constant
  -> a witness in [Y, Y^(1 + epsilon)]
     at the x^(Re rho0) / |rho0| scale
     with a constant still strictly larger than pi / 2 after the tail loss.
```

The potentially new ingredients are therefore:

1. The high-zero complement is bounded directly in L2, rather than first by
   an absolute L1 zero sum.
2. Carlson's linear analytic-multiplicity count is converted into the exact
   square-multiplicity mass needed by the explicit-formula energy.
3. The real-part decomposition uses a fixed finite grid, so no uniform
   moving-`sigma` Carlson certificate is silently assumed.
4. The short interval exponent `1 + epsilon` appears explicitly in the
   feasibility inequalities.
5. The complete chain is intended to be checked against the actual zeta kernel
   and explicit formula, rather than an unconstrained abstract `hkernel`.

The final theorem must not be advertised as new merely because it contains the
constant `pi / 2`.  Novelty depends on closing all five items above.

## Direct-L2 capacity input

For a dyadic height block and a fixed real-part strip beginning at `sigma`, the
actual Carlson and local multiplicity inputs should expose

```text
sum_{rho in block} multiplicity(rho)^2 / |rho|^2
  <= C * T^(q(sigma) - 2) * (1 + log T)^5,

q(sigma) = 4 * sigma * (1 - sigma).
```

The fifth logarithm has an auditable origin:

```text
Carlson linear count:       (1 + log T)^4
local maximum multiplicity: (1 + log T)^1
------------------------------------------------
square-multiplicity mass:   (1 + log T)^5.
```

Deleting any fixed finite low-zero cluster `S` must use nonnegative-mass
monotonicity.  It must not introduce a new zero-density hypothesis depending on
`S`.

After multiplication by a half-isolated Occupancy bound

```text
Occupancy(T) <= Cocc * T^theta * (1 + log T)^r,
```

the high-zero block has polynomial exponent

```text
q(sigma) - 2 + theta
```

and logarithmic loss `5 + r`.  The Carlson side owns the count, weighted mass,
and multiplicity bounds.  The half-isolated side owns only Occupancy and the
Gram/Schur estimate.

## Normalized exponent ledger

Let the target zero have real part `beta`, let the logarithmic observation
interval have length `lambda * log Y`, and put `T = Y^gamma`.  The two endpoint
normalizations lead to

```text
F_right(sigma, gamma)
  = 2 * lambda * (sigma - beta)
    + gamma * (q(sigma) - 2 + theta),

F_left(sigma, gamma)
  = 2 * (sigma - beta)
    + gamma * (q(sigma) - 2 + theta).
```

At `sigma = 1`, the right critical height is

```text
gammaStar = 2 * lambda * (1 - beta) / (2 - theta).
```

An independent direct-L2 cutoff below `lambda / 2` exists exactly when

```text
theta < 4 * beta - 2.
```

This is the intrinsic direct-L2 condition.  Equality is critical and does not
give decay; `theta > 4 * beta - 2` fails at the right edge.  This statement is
not a general impossibility result for Carlson methods, and it does not exclude
zeta zeros with real part greater than `2/3`.

## Why the interval can become [Y, Y^(1 + epsilon)]

If the direct-L2 cutoff must share the existing outer explicit-formula cap
`alpha < 2 * beta - 1`, set

```text
lambda = 1 + epsilon.
```

The exact shared-cap condition is

```text
theta
  < 2 - 2 * lambda * (1 - beta) / (2 * beta - 1),
```

equivalently

```text
epsilon
  < ((2 - theta) * (2 * beta - 1)) / (2 * (1 - beta)) - 1.
```

For the polylogarithmic Occupancy case `theta = 0`, this becomes

```text
epsilon < (3 * beta - 2) / (1 - beta).
```

Thus a positive short-interval parameter exists precisely in the intended
range `beta > 2/3`.  This explains mathematically why shortening a fixed large
power interval to `[Y, Y^(1 + epsilon)]` is not cosmetic: it is the parameter
that makes the direct-L2 height compatible with the outer contour height.

For general `theta`, some positive `epsilon` exists exactly under

```text
theta < 2 * (3 * beta - 2) / (2 * beta - 1).
```

The intrinsic threshold `4 * beta - 2` and this shared-outer threshold coincide
at `beta = 3/4`.  Below `3/4` the shared-outer condition is stronger; above
`3/4` the intrinsic direct-L2 condition is stronger.  Both inequalities must
remain visible in the theorem interface.

## Fixed-grid real-part decomposition

The proof should not request Carlson uniformly at a moving real parameter.
Use a finite grid instead:

```text
coarse layer: Re rho <= 13 / 25,
fine layers:  j / 100 <= Re rho < (j + 1) / 100,
              j = 52, ..., 99.
```

The target `beta` is assigned to a grid bin by a finite filter.  Every Carlson
application is then at a fixed rational `sigma`.  The width loss is explicit
and can be absorbed into a common negative exponent only after proving the
corresponding numerical margin.

For the existing hundredth-strip design, the intended coarse uniform margin is
`-1/20`; it is not accepted until the numerical core and every endpoint
inequality have been checked by Lean.

## Absolute-height shell bridge

The explicit formula naturally groups zeros by `T <= |Im rho| < 2T`, while an
actual Carlson theorem may count positive ordinates.  The bridge should use:

- conjugation symmetry;
- one current positive shell;
- at an exact dyadic boundary, at most one preceding positive shell;
- a fixed numerical boundary factor.

This bridge must preserve the polynomial exponent and logarithmic power.  The
constant can increase, but no extra factor of `T` or `log T` may be hidden.

## Smoothed explicit-formula requirement

The unsmoothed contour remainder is unusable after normalization by the target
amplitude: it leaves

```text
Y^(1 - beta) * (1 + log Y)^2,
```

which diverges.  The direct-L2 theorem therefore requires a genuine
second-order high-zero multiplier.  The intended centered cubic multiplier is

```text
C_h(s)
  = (exp(h*s) - 2 + exp(-h*s)) / (h^2 * s^2)
  = exp(-h*s) * ((exp(h*s) - 1) / (h*s))^2,
```

with a bound of the form

```text
|C_h(s)| <= K * min(1, (h * |s|)^(-2)).
```

The corresponding three-point difference of the quadratic Riesz sum is a
triangle average of `psi`:

```text
(F(x*exp(h)) - 2*F(x) + F(x*exp(-h))) / h^2
  = integral_{-1}^1 (1 - |u|) * psi(x*exp(h*u)) du.
```

This identity is the bridge from the smoothed explicit formula back to a point
witness for the genuine PNT error.  A facade that assumes `h * T <= 1` cannot
be used, because the required high-zero decay needs `h * T` to grow.

## The theorem chain to formalize

The implementation should be split into reviewable slices:

1. `DirectL2NumericalCore`: exact critical height, strict inequalities,
   equality case, hundredth-strip margins.
2. `DirectL2SharedOuterFeasibility`: compatibility of `gammaL2Left`,
   `gammaL2Right`, and `alpha`, with `lambda = 1 + epsilon` exposed.
3. `ActualCarlsonAbsoluteShellBridge`: actual-zeta absolute-height block mass,
   finite-cluster deletion, and no exponent/log loss.
4. `DirectL2FixedGridTail`: fixed real grid, Occupancy product, and exact
   dyadic summation of a strictly negative exponent.
5. `CenteredCubicExplicitFormula`: multiplier estimate and contour remainder.
6. `TriangleAverageTransfer`: turn the smoothed witness into a point witness in
   `[Y, Y^(1 + epsilon)]`.
7. `DirectL2ShortIntervalOscillation`: combine the existing strict low-zero
   energy theorem with a tail smaller than its strict margin.

The parameters must remain distinct throughout:

```text
alpha          outer contour height exponent
gammaLow       low-zero detection height
gammaHigh      existing Carlson two-height split
gammaL2Left    direct-L2 left-end cutoff
gammaL2Right   direct-L2 right-end cutoff
d              smoothing exponent
lambda         observation interval exponent, 1 + epsilon
```

## Claims explicitly deferred

Until all theorem-chain slices and audits pass, do not claim:

- an unconditional short-interval Omega or Omega-plus-minus theorem;
- that parameter feasibility excludes `Re rho > 2/3`;
- that Carlson alone supplies Gram separation or Occupancy;
- that `1 / |rho|^2` alone fixes the contour remainder;
- that the strict `pi / 2` constant is itself new;
- that the direct-L2 method has been proved uniformly over moving strips;
- that the final result follows from the current abstract transfer facade.

## Acceptance evidence

The candidate new theorem is complete only after all of the following hold on
the same current `main` base:

- production statements use the actual zeta zero kernel and analytic
  multiplicity;
- every fixed-grid Carlson certificate is explicit;
- the square-multiplicity logarithmic loss is exactly accounted for;
- finite-cluster deletion is proved by nonnegative monotonicity;
- all dyadic exponents are strictly negative, with equality cases separately
  rejected;
- the centered-cubic contour remainder is small relative to
  `Y^beta / |rho0|`;
- the triangle average yields a witness inside the requested short interval;
- the low-zero strict constant survives all tail and smoothing losses;
- focused source, Contract, AxiomAudit, allowlist, and full baseline all pass;
- the final literature statement cites Revesz and does not overclaim novelty.
