# Conrey global right-vertical design

## Objective

Prove the actual quantitative right-vertical input used in Conrey 1989,
equation (37), for the repository's explicit degree-one certificate.  The
target is a theorem at the corrected moving edge `sigma = 2 log log T` whose
right-edge logarithmic integral over the global height interval is
`O(T / log T)`.  The theorem must concern the concrete
`conreyDegreeOneV1 * conreyMollifier`, not an abstract surrogate.

## Source boundary

Conrey 1989, equation (37), integrates over `1 <= t <= T`.  Conrey 1983,
Section 4, proves the moving-right normalization only on a proportional
block `T <= t <= T + U`.  Therefore a pointwise `1 + O(1 / log T)` theorem on
`T <= t <= 2T` is a reusable local input, not the global equation-(37)
boundary theorem.  The global proof must retain and integrate the
`log(t / T)` variation.

For the explicit polynomial `Q(y) = 1 - 51 y / 50`, the pre-change polynomial
is `Q1(x) = 49 / 100 + 51 x / 50`.  Hence the exact degree-one parameters are
`g = 49 / 100`, `g0 = 0`, and `g1 = 51 / 50`; their proportional-height main
constant is `g + g1 / 2 = 1`.

## Selected approach

Use the Gauss series for digamma already proved in
`PrimeNumberTheorem/DigammaBounds.lean`.  At
`z = (sigma + i t) / 2`, split the series at `N = ceil |z|`.  When
`2 <= t` and `0 < sigma <= t`, the first reciprocal block, the quadratic
tail, and the harmonic/log comparison are all bounded by explicit absolute
constants.  This gives

```
||digamma ((sigma + i t) / 2) - log t|| <= 9
```

and consequently an explicit constant bound for

```
H'(sigma + i t) / H(sigma + i t) - (1/2) log(t / (2*pi)).
```

This route is preferred to building a general complex Stirling expansion:
it proves exactly the norm estimate needed here from existing no-axiom
infrastructure.  An abstract asymptotic hypothesis is rejected because it
would move, rather than solve, the equation-(37) gate.

## Components

### Infinite zeta tail

Create a focused right-tail module proving

```
||zeta(s) - 1||
  <= 2^(-Re s) * (1 + 2 / (Re s - 1))      (1 < Re s)
```

from the absolutely convergent Dirichlet series and the same integral
comparison already used for the finite mollifier.  Specialize it at
`Re s = 2 log L` to obtain `3 / L`.  Reuse the existing Cauchy estimate
`||zeta'(s)|| <= zeta(2) <= 5/3` once `Re s >= 4`.

### Digamma and archimedean height main term

Create a module exposing the Gauss-series split and the height-uniform
digamma bound.  Promote the exact `H'/H` formula currently private in
`ConreyFarRight.lean` to a public theorem, then prove the explicit
height-main estimate.  All conditions (`2 <= t`, `0 < sigma`, `sigma <= t`)
remain visible in the interface.

### Degree-one `V1` decomposition

Define the height main term

```
(g + i*g0) + (g1/L) * ((1/2) * log(t/(2*pi))).
```

Prove the exact identity obtained by subtracting this term from
`conreyDegreeOneV1`, followed by a quantitative norm theorem on the corrected
moving edge.  The theorem must use the concrete zeta, zeta derivative, and
archimedean bounds; it must not assume the desired `V1` estimate.

### Explicit global logarithmic integral

Specialize to `(49/100, 0, 51/50)`.  On the high part
`2 log log T <= t <= T`, compare `V1` with

```
a_L(t) = 49/100 + 51/(100*log T) * log(t/(2*pi)).
```

Prove `1/5 <= a_L(t) <= 1`, control the logarithm by
`3/log T * log(2*pi*T/t)`, and integrate this elementary majorant.  On the
short low part, use the existing coarse logarithmic digamma bound to keep
`V1` and its reciprocal bounded; its length is only `O(log log T)`.  Add the
already-proved mollifier logarithm bound.  The final public theorem bounds
the integral of the absolute logarithm, which is stronger than the signed
right-edge term in Littlewood's identity.

## Public proof boundary

Completing this design closes only the right-vertical quantitative item in
equation (37).  It does not prove the two horizontal Jensen bounds, select
admissible endpoint heights, prove equations (38)--(41), or prove the long
mollified mean square.  Documentation and theorem names must preserve this
boundary.

## Verification

Each component gets a contract file written before production code.  A
contract is first run and must fail because its named theorem or module is
absent.  After implementation, run the focused contract, the production
module build, `git diff --check`, and the default full `lake build`.  Axiom
audits for every public endpoint must report only the standard Lean/Mathlib
axioms already accepted by this repository.
