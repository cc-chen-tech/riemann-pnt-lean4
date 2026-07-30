# Carlson transfer for a growing ordinate floor

## Rectangle exponent

At truncation height

```text
T(x) = x^alpha
```

Carlson contributes the density exponent

```text
4 * alpha * sigma * (1 - sigma).
```

A real-part upper endpoint `tau` contributes `tau - 1` to the relative PNT
kernel.  If the rectangle has lower ordinate `x^gamma`, the denominator gives
the additional gain `-gamma`.  The complete exponent is therefore

```text
4 * alpha * sigma * (1 - sigma) + tau - 1 - gamma.
```

This is formalized as `carlsonRectangleExponent`.

## Decay criterion

If there is an `epsilon > 0` such that

```text
carlsonRectangleExponent sigma tau alpha gamma + epsilon < 0,
```

then the fourth logarithmic power in Carlson's theorem is absorbed and both
the direct count majorant and the actual multiplicity-weighted count times the
rectangle kernel tend to zero.

## Actual zeta layer

`tendsto_actualPositiveRectangleLayerMass` applies the criterion to a genuine
height-dependent `PositiveZeroRectangleInput`.  It assumes:

```text
the layer's Carlson threshold is the fixed sigma;
the real-part upper endpoint is the fixed tau;
the ordinate floor is eventually x^gamma.
```

The conclusion concerns the actual sum of norms of
`pntRelativeZeroContribution`, including analytic multiplicity.

## Mathematical significance

The identity

```text
rectangle exponent = strip-endpoint exponent - gamma
```

quantifies exactly what ordinate layering buys.  A strip that fails the
purely real-part endpoint criterion can become summable when its zeros occupy
a sufficiently high ordinate band.

The next assembly step is a finite family of such rectangles sharing one
truncation height, plus a separate finite low-ordinate residual.
