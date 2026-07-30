# Actual target-amplitude positive-tail composition design

## Scope

This stack composes the two immediately preceding estimates for the same
canonical outside-cluster bucket input:

- stack37 controls canonical layer `0`, whose zeros satisfy
  `Re rho <= sigma`, by a global-zero-count two-height split;
- stack36 controls canonical layer `1`, whose zeros satisfy
  `sigma < Re rho <= tau`, by an actual Carlson two-height strip.

No conjugation, real-ordinate residual, contour remainder, or oscillation
cluster theorem is added here.

## Pointwise chain

At outer height `x ^ alpha`, the existing canonical two-layer cover gives

```text
positive outside-cluster tail norm
  <= norm(layer 0) + norm(layer 1).
```

For layer `0`, triangle inequality and the exact stack37 ordinate
partition give

```text
norm(layer 0)
  <= low-ordinate multiplicity mass + high-annulus multiplicity mass.
```

For layer `1`, an outside-cluster real-part cap

```text
sigma < Re rho -> Re rho <= tau
```

embeds the layer into

```text
actualPositiveCarlsonStrip sigma tau (x ^ alpha).
```

Therefore, after division by `x ^ (beta - 1)`,

```text
positive outside-cluster tail
  <= stack37 normalized low-layer mass
     + stack36 normalized actual Carlson-strip mass.
```

## Asymptotic inputs

The low layer requires

```text
gammaLow + sigma - beta + epsilonLow < 0
alpha + sigma - beta - gammaLow + epsilonLow < 0.
```

The high strip requires the two stack36 target-amplitude Carlson exponent
margins.  The sum tends to zero when both inputs do.

## Claim boundary

The result is a complete positive-ordinate, outside-cluster tail theorem
under an explicit real-part cap.  The full conjugation-symmetric tail still
requires the existing negative-ordinate transfer and a separate
real-ordinate residual theorem.
