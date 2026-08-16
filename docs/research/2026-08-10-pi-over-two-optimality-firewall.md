# The pi/2 optimality firewall

## Why this firewall is necessary

The unified transfer layer is intended to be more general than one concrete
Riemann-zeta theorem.  That generality creates a mathematical restriction:
the constant `pi/2` cannot be hard-coded as a consequence of only a generic
explicit formula and the existence of a conjugate zero pair.

Revesz records the classical Riemann-zeta theorem

```text
|psi(x)-x|
  >= (pi/2 - epsilon) * x^(Re rho0) / |rho0|
```

for suitable arbitrarily large `x`.  He also constructs Beurling/zeta-type
systems in which the corresponding error is bounded above by

```text
(pi/2 + epsilon) * x^(Re rho0) / |rho0|
```

for all sufficiently large `x`.  Thus `pi/2` is optimal in that broad class.

Primary source:

- Szilard Gy. Revesz, *Oscillation of the remainder term in the prime number
  theorem of Beurling, caused by a given zeta-zero*, arXiv:2202.01837,
  <https://arxiv.org/abs/2202.01837>.

The counterexample is not a counterexample for the classical Riemann zeta
function.  It therefore does not logically exclude a stronger actual-zeta
result.  It does show that any stronger result must visibly use hypotheses not
shared by the general counterexample class.

## Three theorem levels

The formal development should keep three levels separate.

### Level 1: constant-free abstract transfer

The generic theorem accepts constants as parameters:

```text
mainEnergy:
  ||M||_2 >= c_main * A * sqrt(W),

tailEnergy:
  ||R||_2 <= c_tail * A * sqrt(W),

strictGap:
  c_target < c_main - c_tail.
```

It concludes a point with

```text
|E(x)| > c_target * A(x).
```

This theorem contains no occurrence of `pi/2` in its assumptions beyond what a
caller chooses to instantiate.  It is valid for upper-bound, lower-bound, and
different zeta-type settings.

### Level 2: sharp-minus short-interval transfer

A robust short-interval target is:

```text
for every eta > 0,
there exists x in [Y, Y^(1+epsilon)] with
|E(x)| >= (pi/2 - eta) * x^beta / |rho0|.
```

This combines two features that appear separately in the known literature:

- Revesz gives the sharp-minus constant and reciprocal-zero scale, but not the
  same short-power localization;
- Schlage-Puchta gives `[X, X^(1+epsilon)]`, but with a
  `gamma0^(1+epsilon)` denominator and an unspecified computable constant.

Primary source for the latter:

- Jan-Christoph Schlage-Puchta, *Oscillations of the error term in the prime
  number theorem*, arXiv:1912.00853,
  <https://arxiv.org/abs/1912.00853>.

Even this level must not be called new until a complete literature audit and
the actual-zeta proof chain are finished.

### Level 3: actual-zeta strict-greater transfer

The ambitious target retained by this project is a final constant strictly
larger than `pi/2` on the short interval.  Its theorem must expose an
actual-zeta-specific surplus:

```text
c_main = pi/2 + delta_actual,
0 < delta_actual,
c_tail + c_kernel + c_contour + c_point < delta_actual.
```

The conclusion is then

```text
|psi(x)-x|
  > (pi/2 + delta_final) * x^beta / |rho0|,

0 < delta_final
  < delta_actual
    - c_tail - c_kernel - c_contour - c_point.
```

This is not a generic consequence of a zero.  The production theorem must
identify which actual-zeta input creates `delta_actual`.

Possible sources include:

- a protected actual-zeta low-packet energy theorem with a strict surplus;
- an actual-zeta frequency/occupancy theorem stronger than the assumptions
  available in the Beurling counterexample;
- additional arithmetic or functional-equation structure used quantitatively.

Merely instantiating a generic explicit formula, conjugation symmetry, and a
zero-density function is not enough justification.

## Implication for the unified API

The unified upper/lower transfer machine should be constant-parametric:

```text
structure OscillationTransferInput where
  targetAmplitude : X -> Real
  mainConstant : Real
  kernelLoss : X -> Real
  complementLoss : X -> Real
  contourLoss : X -> Real
  pointLoss : X -> Real
  mainLower : ...
  complementUpper : ...
  contourUpper : ...

theorem oscillation_of_positive_remainingMargin
  (hmargin :
    targetConstant
      < mainConstant
        - kernelLoss x
        - complementLoss x
        - contourLoss x
        - pointLoss x) :
  exists witness, ...
```

The actual-zeta facade may then instantiate

```text
targetConstant = pi/2 + delta_final,
```

while a Beurling or generic facade can instantiate only a compatible weaker
constant.  This prevents the abstraction from proving a statement contradicted
by its own intended model class.

## What Carlson direct L2 contributes

Carlson direct L2 is a tail-reduction mechanism.  It can make

```text
complementLoss(Y) -> 0
```

under strict exponent conditions.  It does not by itself increase the main
constant.  Therefore:

```text
Carlson capacity + Occupancy
  preserves an existing strict surplus;

Carlson capacity + Occupancy
  does not create a strict surplus from pi/2 exactly.
```

This distinction should appear in theorem names and documentation.  A theorem
named `strictPiOverTwo_of_directL2Tail` must require a main constant already
strictly above `pi/2`.

## Relation to finite clusters

A finite cluster can have a low-energy constant larger than that supplied by a
single conjugate pair.  However, this is useful only if:

- the cluster is the same cluster removed from the Carlson complement;
- its normalization is still the requested
  `x^(Re rho0)/|rho0|` scale;
- its strict surplus is uniform over the short observation interval;
- smoothing changes the cluster by less than the surplus;
- the cluster theorem is actual-zeta-specific or has assumptions excluding the
  known optimality examples.

The transfer layer must not infer these properties from finiteness alone.

## Required audit before a final strict-greater claim

Before publishing a final constant greater than `pi/2`, verify all of:

1. The protected low-energy theorem concludes a numerical constant strictly
   above `pi/2`, not merely a non-strict or asymptotic statement.
2. Its amplitude is exactly `x^beta/|rho0|`, including analytic multiplicity.
3. Its main set is identical to the set deleted from the complement.
4. The surplus is uniform in the interval parameter `Y` used by the tail.
5. Kernel, Carlson, contour, and point losses are all measured in the same
   norm and normalization.
6. Their total is strictly smaller than the surplus.
7. The assumptions contain enough actual-zeta structure that the Beurling
   optimality construction is not an instance of the theorem.
8. The literature claim distinguishes a stronger classical-zeta theorem from
   a generic zeta-type theorem.

If any item is missing, the correct current conclusion is only the
constant-parametric transfer, not a strict-greater-than-`pi/2` theorem.

## Nonclaims

This firewall does not claim:

- that a strict-greater classical-zeta theorem is impossible;
- that the Revesz Beurling construction satisfies the exact actual Carlson
  exponent used in this project;
- that the protected low-energy theorem lacks a strict surplus;
- that the sharp-minus short-interval combination is absent from all
  literature;
- that direct L2 alone proves an oscillation theorem.

It only records which logical dependencies must be visible for the final claim
to be mathematically defensible.
