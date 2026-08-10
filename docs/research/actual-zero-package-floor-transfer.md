# Actual zeta zero package to natural psi0 witnesses

## Concrete energy

The module defines the actual equal-real-part zeta-zero package energy

```text
sum multiplicity-weighted reciprocal norms squared
  - offDiagonalBound / L.
```

The existing continuous mean-square theorem supplies a point `y` in every
logarithmic interval `(X, X + L)` at which the package norm is at least

```text
exp(beta*y) * sqrt(energy).
```

The statement remains formally true when the energy is nonpositive because
the real square root then vanishes.  A nontrivial lower bound requires
`sqrt(energy) > remainderCoeff + loss`.

## Actual PNT transfer

At the same point, a power-scale bound

```text
norm zeroPackageExplicitFormulaRemainder
  <= remainderCoeff * exp(beta*y)
```

and the proved floor-rounding estimate give the natural-point lower bound

```text
(sqrt(energy) - remainderCoeff - loss) * exp(beta*y)
  <= |chebyshevPsi0Error(floor(exp y))|.
```

An eventual remainder bound therefore produces such a witness in every
sufficiently far logarithmic interval.

## Honest boundary

The theorem uses the actual zeta zero package, analytic multiplicities,
explicit-formula remainder, and `chebyshevPsi0Error`.  It does not prove the
eventual remainder hypothesis.  Closing that hypothesis requires the
Carlson-controlled complementary-zero layers and contour remainder to be
small relative to the selected package energy.
