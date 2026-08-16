# Analytic multiplicity versus frequency Occupancy

## The bookkeeping problem

The explicit formula contains analytic multiplicity in the coefficient of a
distinct zero:

```text
a(rho) = multiplicity(rho) * x^rho / rho.
```

Its diagonal L2 mass therefore contains

```text
multiplicity(rho)^2 / |rho|^2.
```

At the same time, a Gram/Schur estimate counts how many frequencies interact
with a given frequency.  If analytic multiplicity is also represented by
repeating the same zero as several Gram indices, the same multiplicity is paid
twice.

This note fixes the representation used by the direct-L2 route.

## Two valid models that must not be mixed

### Model A: distinct zeros with weighted coefficients

The index set contains each distinct zero once.  Its coefficient is

```text
a(rho) = m(rho) * kernel(rho).
```

Then

```text
sum_rho |a(rho)|^2
  = sum_rho m(rho)^2 * |kernel(rho)|^2.
```

The Gram Occupancy counts distinct zero indices and their frequency
interactions.  It does not count `m(rho)` copies of the same analytic zero.

### Model B: multiplicity-expanded zero occurrences

The index set contains `m(rho)` copies of `rho`, each with coefficient
`kernel(rho)`.  The coefficient diagonal is only linear in multiplicity, but
the Gram matrix has `m(rho)` identical rows/frequencies.  Their cross terms
recover the square multiplicity.

Both models can describe the same exponential polynomial when implemented
consistently.

The invalid hybrid is:

```text
coefficient already contains m(rho)
  + Gram index repeats rho exactly m(rho) times.
```

That hybrid can introduce an artificial cubic multiplicity loss.

## Chosen model for this project

The Carlson work already targets the capacity

```text
sum distinct rho
  m(rho)^2 * weight(rho).
```

Therefore the direct-L2 transfer must use Model A:

```text
index type: distinct analytic zeros;
coefficient: analytic multiplicity times the zeta kernel;
Carlson capacity: square multiplicity;
Gram Occupancy: distinct-frequency geometry only.
```

The local maximum multiplicity theorem is used exactly once, in the Carlson
conversion

```text
sum m(rho)^2 * w(rho)
  <= maxMultiplicity(T) * sum m(rho) * w(rho).
```

It must not reappear as an automatic factor in the Gram theorem.

## Equal ordinates of distinct zeros

Distinct zeros can in principle have the same imaginary part.  Model A removes
analytic copies of one zero, but it does not make the frequency map

```text
rho -> Im rho
```

injective.

There are two correct ways for the half-isolated interface to handle this.

### Indexed Gram bound

Keep the Gram matrix indexed by distinct zeros.  Exact equal-frequency
collisions have kernel value `K(0)` and are included directly in the Schur row
sum.  The Occupancy theorem counts every distinct zero index in the relevant
frequency neighborhood.

### Grouped-frequency bound

Group coefficients by ordinate:

```text
A(gamma)
  = sum_{rho : Im rho = gamma} a(rho).
```

Then use finite Cauchy-Schwarz:

```text
|A(gamma)|^2
  <= n(gamma)
     * sum_{rho : Im rho = gamma} |a(rho)|^2,
```

where `n(gamma)` is the number of distinct zeros in that fiber.  The factor
`n(gamma)` is a frequency-collision Occupancy factor, not analytic
multiplicity.

The indexed version is preferable because it avoids a second grouping API.

## Log-loss ledger

Under Model A, the Carlson coefficient mass has

```text
Carlson linear count:       log^4
local maximum multiplicity: log^1
square coefficient mass:    log^5.
```

Suppose the half-isolated Schur theorem gives

```text
Occupancy(T) <= C_occ * T^theta * log^r T.
```

Then the complete block energy has log loss

```text
5 + r.
```

No additional multiplicity logarithm is permitted unless the Occupancy theorem
itself explicitly proves and states an extra exact-frequency collision factor.

In particular, the following unexplained ledger is invalid:

```text
log^4 Carlson
+ log^1 local multiplicity
+ log^1 repeated Gram copies
= log^6.
```

The last term duplicates analytic multiplicity under Model A.

## Finite-cluster deletion

Let `S` be the finite distinct-zero main cluster.  The complement index set is

```text
B \ S
```

at the distinct-zero level.  Nonnegative monotonicity gives

```text
sum_{rho in B \ S} m(rho)^2 * w(rho)
  <= sum_{rho in B} m(rho)^2 * w(rho).
```

There is no need to remove `m(rho)` separate copies.  This is another reason to
keep the main cluster and Carlson complement in Model A.

## Real-part strips and identical frequencies

If two distinct zeros with the same ordinate lie in different real-part
strips, the current fixed-grid design combines strips by finite Minkowski or
finite Cauchy-Schwarz.  Their cross-strip interaction is then absorbed by the
fixed number of strips.

Within one strip, exact-frequency collisions remain part of that block's
Occupancy.  The Carlson theorem should not assume frequency injectivity.

## Lean-facing interface

The common index type should represent distinct zeros and expose:

```text
zero : ZeroIndex -> Complex
analyticMultiplicity : ZeroIndex -> Nat
frequency i = (zero i).im
coefficient i = analyticMultiplicity i * kernel (zero i)
```

The Carlson side supplies:

```text
sum i in block,
  (analyticMultiplicity i)^2 * weight i
    <= capacityBound.
```

The half-isolated side supplies:

```text
weightedEnergy
  (fun t => sum i in block, coefficient i * exp(I*frequency i*t))
  <= gramConstant * occupancyBound
     * sum i in block, normSq (coefficient i).
```

The Gram statement must work without an injectivity hypothesis on `frequency`,
or must expose the exact additional hypothesis and fiber loss if it requires
one.

Suggested audit theorems are:

```text
distinctZeroCoefficient_normSq
analyticMultiplicity_used_once
indexedGram_allows_equalFrequencies
finiteClusterDeletion_distinctZeros
carlsonOccupancy_logLoss_eq_five_add_r
```

## Contract with the protected half-isolated task

The only required half-isolated output is:

```text
for the distinct-zero block supplied by Carlson,
the Schur row sum or Occupancy is bounded by
C_occ * T^theta * (1 + log T)^r.
```

That theorem owns:

- near-frequency collisions;
- exact-frequency collisions between distinct zeros;
- any separation hypothesis it needs.

It does not own:

- analytic multiplicity conversion;
- Carlson zero count;
- square-multiplicity log `5`;
- finite-cluster density monotonicity.

## Nonclaims

This note does not claim:

- that distinct zeta zeros always have distinct ordinates;
- that an existing Gram theorem already uses Model A;
- that exact-frequency fiber size is uniformly bounded without proof;
- that the Occupancy exponent or log power has already been instantiated;
- that Model B is mathematically wrong when used consistently.

It fixes Model A because that is the model compatible with the requested
Carlson square-multiplicity capacity.
