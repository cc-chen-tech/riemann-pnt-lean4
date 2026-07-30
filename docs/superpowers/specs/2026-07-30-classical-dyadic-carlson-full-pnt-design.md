# Classical Dyadic Carlson Full-PNT Transfer Design

## Purpose

Close a complete ordinary-scale PNT upper-bound route at the classical
admissible subpolynomial selected height while retaining the Carlson/dyadic
provenance of the zero-tail estimate.

The repository already has an unconditional classical selected-height PNT
limit through a finite-zero-sum route.  Repeating that endpoint is not the
objective.  This module must expose one auditable certificate containing the
classical zero-free edge, Carlson dyadic gap, complete finite zero-tail decay,
actual explicit-formula remainder certificate, and the resulting PNT error
limit.

## Height bridge

For every `k >= 0` and `alpha > 0`, prove on real inputs

```text
pintzCarlsonHeight(k, x) + 1 <= x^alpha
```

eventually.  The one-unit margin absorbs the complete selector window and
shows the classical selected height is eventually below a polynomial ceiling.
Separately, its lower window endpoint and
`tendsto_pintzCarlsonHeight_atTop` prove that the selected height is cofinal.

These are exactly the two hypotheses needed by the generic critical-half
layer estimate: a polynomial upper bound and height cofinality.

## Zero-tail decomposition

Use the existing inequality

```text
positive tail
  <= critical-half layer + moving middle mass + moving right-strip mass.
```

The terms are closed as follows.

1. Critical half: apply the generic hybrid selected-height cardinality
   majorant using the real-variable polynomial ceiling and cofinality.
2. Middle mass: import the stack-19 classical dyadic middle-mass theorem.
3. Right strip: once `delta(m) <= 1/16`, every zero in
   `(1 - 2 delta, 1 - delta]` lies above `7/8` and therefore belongs to the
   same dyadic fixed-anchor window.
4. Real ordinate: abstract the existing proof to every cofinal height.
5. Full zero tail: combine positive conjugation and real-ordinate decay.

The classical width `rate / (1 + sqrt(log m))` is eventually below every
positive constant, in particular `1/16`.

## Explicit-formula remainder

Define the natural-point upper bound

```text
(cofinal contour remainder + closed logarithmic term) / m.
```

The classical selected-height truncated certificate gives eventual domination
of the actual relative remainder.  Its contour part tends to zero by the
proved classical contour theorem; the closed logarithmic part uses the
existing target-negligibility theorem at `beta = 1`.  Squeezing constructs
`ActualSelectedHeightNaturalPointRemainderCertificate 1 H`.

## Final endpoint

`exists_selectedClassicalAdmissibleDyadicCarlsonFullPNTTransfer` returns
positive `b, rate` and, for every uniform good-height selector, simultaneously
certifies:

```text
IsCarlsonMovingDyadicLogPowerGap delta
IsSelectedHeightDynamicZeroFree H delta
dynamicFullPNTZeroTailNorm H m -> 0
ActualSelectedHeightNaturalPointRemainderCertificate 1 H
relativeChebyshevPsi0Error m -> 0
```

## Scope boundary

This is a complete Carlson-based ordinary relative-PNT upper chain.  It is not
a quantitative optimal PNT error rate and does not close target-zero-amplitude
normalized complementary remainders needed for an Omega theorem.  It neither
modifies complementary-zero/VK-edge files nor proves a new density estimate,
an unconditional oscillation theorem, or RH.

## Verification

Build the production module and exact contract together.  Run the standalone
axiom audit and require every public endpoint to use only `propext`,
`Classical.choice`, and `Quot.sound`.
