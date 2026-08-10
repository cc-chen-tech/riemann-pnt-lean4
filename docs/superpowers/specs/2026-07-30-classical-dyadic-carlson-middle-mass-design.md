# Classical Dyadic Carlson Middle-Mass Design

## Purpose

The classical admissible selected height is subpolynomial:

```text
H_classical(x) = exp(O(sqrt(log x))).
```

The existing automatic dyadic Carlson mass theorem is organized at a fixed
polynomial ceiling.  The new theorem must connect these two scales without
assuming that the abstract good-height selector is monotone.

## Mathematical design

Fix a positive polynomial exponent `alpha`.

1. Prove the strict height margin

   ```text
   pintzCarlsonHeight(k, m) + 1 <= m^alpha
   ```

   eventually.  The proof uses

   ```text
   log 2 + k sqrt(log m) <= alpha log m.
   ```

2. Combine that margin with the two unit-window selector certificates.  The
   upper endpoint of the classical unit window lies below the lower endpoint
   of the polynomial unit window.  This orders the selected heights without
   any selector monotonicity axiom.

3. Use finset inclusion to transfer the fixed low-strip decay from the
   polynomial selected height to the classical selected height.

4. Split the classical moving middle strip at real part `7/8`.

   - The lower part is the fixed low strip.
   - Every zero in the upper part belongs to the dyadic fixed-anchor window at
     the polynomial ceiling.

5. Apply the existing automatic dyadic Carlson fixed-anchor theorem and squeeze
   the classical moving middle mass between zero and the sum of two decaying
   masses.

6. Instantiate the width from the classical dyadic Carlson gap theorem.  The
   final endpoint uses one pair of constants `b, rate` for both the dynamic
   zero-free edge and moving-middle-mass decay.

## Public theorem chain

```text
eventually_pintzCarlsonHeight_add_one_le_nat_rpow
  -> eventually_selectedClassicalAdmissibleGoodHeight_le_selectedUniformGoodHeight
  -> tendsto_actualSelectedClassicalAdmissibleSevenEighthsLowMass_zero
  -> actualSelectedHeightMovingCarlsonMiddleMass_le_low_add_dyadicFixedAnchor
  -> tendsto_actualSelectedClassicalAdmissibleMovingMiddleMass_zero_of_dyadic
  -> exists_selectedClassicalAdmissibleDyadicCarlsonMiddleMassDecay
```

## Scope boundary

This result closes the Carlson-controlled middle-zero contribution at the
classical selected height.  It does not yet prove decay of the complete
nontrivial-zero sum at that height.  The critical-line contribution,
real-ordinate contribution, and final explicit-formula reassembly remain
separate gates.

The implementation does not modify complementary-zero or VK-edge modules.  It
does not formalize a new zero-density theorem, prove an unconditional
oscillation theorem, or imply RH.

## Verification

The production module and exact contract must build together.  A standalone
axiom audit must show that every public endpoint uses only:

```text
propext
Classical.choice
Quot.sound
```
