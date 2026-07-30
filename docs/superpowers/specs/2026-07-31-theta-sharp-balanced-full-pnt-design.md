# Theta-Sharp Balanced Full-PNT Design

## Objective

Propagate the theta-sharp Carlson estimate from the actual fixed-anchor
multiplicity mass through the moving zero layers and the complete explicit
formula. For every fixed

```text
1 / 4 < theta < 1 / 2,
```

the final theorem must bound the actual natural-point relative Chebyshev error
by a closed-form majorant whose Carlson contribution decays at the exact rate
`theta * gapRate`.

## Mathematical chain

The balanced height selection supplies

```text
gapRate = classicalAdmissibleBalancedRate b / 2.
```

Stack 30 supplies the fixed-anchor bound

```text
actual fixed-anchor mass
  <= exp(log D - 3 log gapRate
       + 11 log(1 + sqrt(log m))
       - theta * gapRate * sqrt(log m)).
```

The new module transports this same term, without weakening its exponent,
through:

1. moving middle mass = seven-eighths low mass + fixed-anchor mass;
2. positive zero tail = critical-half mass + moving middle + moving strip;
3. full finite zero tail = two positive tails + the real-ordinate sum;
4. explicit formula = full zero tail + closed real-axis term + contour
   remainder.

The final theorem records

```text
classicalAdmissibleThetaVerifiedPNTDecayRate b theta
  = theta * gapRate,
```

as well as the strict inequalities

```text
old verified rate < theta rate < balanced height rate / 4.
```

## Architecture

Create one parallel module importing stack 30. Define theta versions of the
middle, positive-tail, full-zero-tail, and closed-form full-PNT majorants.
Existing critical-half, low-strip, real-ordinate, closed-axis, and contour
terms are reused unchanged.

The old stack 28 and stack 29 modules remain untouched. This avoids rewriting
already reviewed declarations and makes the quantitative improvement visible
as a bounded stacked PR.

## Public declarations

- `classicalDyadicCarlsonThetaMiddleMajorant`
- `classicalDyadicCarlsonThetaPositiveZeroTailMajorant`
- `classicalDyadicCarlsonThetaFullZeroTailMajorant`
- `classicalDyadicCarlsonThetaClosedFormFullPNTErrorMajorant`
- convergence lemmas for all four majorants
- `eventually_abs_relativeChebyshevPsi0Error_le_thetaClosedFormFullPNTMajorant`
- `exists_selectedClassicalAdmissibleDyadicCarlsonThetaQuantitativeMassMajorant_of_zeroFree`
- `exists_selectedBalancedClassicalAdmissibleDyadicCarlsonThetaClosedFormFullPNTErrorMajorant`

## Verification boundary

The focused module build and contract build must succeed. The axiom audit must
show only the repository-standard logical axioms:

```text
propext
Classical.choice
Quot.sound
```

This stack proves an improved explicit PNT upper-bound transfer. It does not
prove the endpoint `theta = 1 / 2`, an omega theorem, RH, or control of the
separately owned complementary-zero module.
