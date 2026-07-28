# VK-edge zero-cluster local L2 design

## Goal

Combine the collision-safe drifting exponential-polynomial model, the
Carneiro--Littmann local-separation Hilbert inequality, and equal-ordinate
phase coercivity into a quantitative local second-moment lower bound for a
finite zeta-zero cluster.

## Mathematical design

For a finite frequency set `U`, frozen coefficients `d`, window length `L`,
and local separations `delta_u`, the frozen exponential polynomial satisfies

```text
integral |P(t)|^2 dt
  >= L * sum_u |d_u|^2
     - 4*pi * sum_u |d_u|^2 / delta_u.
```

The existing drift comparison loses

```text
L * (1 - exp (-Delta * L))^2 * mass^2.
```

After equal frequencies are merged, the zeta coefficients have a common
negative-imaginary direction. The phase-coercivity theorem therefore gives

```text
mass^2 <= 4 * card(U) * sum_u |d_u|^2.
```

The final lower bound is

```text
1/2 * (
    L * mass^2 / (4 * card(U))
    - 4*pi * localSeparationEnergy)
  - L * driftLoss^2 * mass^2
<= integral |normalizedFiniteZeroClusterContribution|^2.
```

It yields strict positivity whenever the displayed lower bound is positive.
The local-separation energy remains explicit; no unknown zero-spacing estimate
is hidden.

## Modules

- `MathlibAux/DriftingExponentialPolynomialHilbert.lean`
  proves the generic Hilbert lower bound for a drifting finite exponential
  polynomial.
- `PrimeNumberTheorem/VKEdgeZeroClusterLocalL2.lean`
  specializes it to a finite zeta-zero cluster and inserts phase coercivity.
- Matching contract and axiom-audit modules lock every public theorem.

## Scope boundary

This stage proves a finite-cluster local `L2` lower bound. It does not yet:

- identify a canonical cluster supplied by the full zeta explicit formula;
- control complementary zeros or contour tails;
- derive a zero-density contradiction;
- prove RH.

The next mathematical input is a bound for the local-separation energy in
terms of zero density, zero spacing, or a cluster decomposition.

## Verification

The implementation must use test-first contracts, focused builds, central
axiom registration, placeholder scans, `verify-baseline.sh`, and a full
`lake build`. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
