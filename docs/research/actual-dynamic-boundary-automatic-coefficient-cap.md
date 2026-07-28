# Automatic coefficient cap for the dynamic boundary package

## Explicit constant

The dynamic equal-real-part package has the uniform coefficient cap

```text
C(sigma)
  =
  2 * sum'_{positive Carlson zero indices i}
        multiplicity(rho_i) / |rho_i|
  + finiteVisibleClusterCoefficientMass(real-ordinate zeros).
```

The Carlson series is summable for `1/2 < sigma < 1`.  The real-ordinate term
is a fixed finite sum.

## Proof chain

1. Finite coefficient mass splits exactly into positive, negative, and
   real-ordinate parts.
2. Every positive member of the dynamic package is a high Carlson zero when
   `sigma < beta`, so its finite mass is bounded by the Carlson `tsum`.
3. The dynamic package is stable under conjugation, and analytic multiplicity
   and norm are preserved, so negative mass equals positive mass.
4. Its real part is contained in
   `realOrdinateNontrivialZerosFinset 0`.

Therefore every package, at every height, has mass at most `C(sigma)`.  This
proves `DynamicBoundaryPackageCoefficientCap` without adding an external
upper-side certificate.

## Consequence

The previously conditional dynamic PNT upper transfer can now use this cap
automatically.  The local oscillation witness remains the separate lower-side
input.
