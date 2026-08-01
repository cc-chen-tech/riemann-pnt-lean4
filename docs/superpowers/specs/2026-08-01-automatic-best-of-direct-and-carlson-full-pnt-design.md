# Automatic Best-of-Direct-and-Carlson Full-PNT Bound

## Objective

Make the strict-margin explicit-formula route and the dyadic Carlson route act
on one concrete object: the real relative Chebyshev error. The unified bound is
the pointwise minimum of their independently certified majorants.

## Design

- Define `bestOfDirectAndCarlsonPNTErrorMajorant f g m = min (f m) (g m)`.
- Prove the minimum tends to zero when both inputs tend to zero.
- Prove the minimum still dominates the real PNT error when both inputs do.
- Instantiate the generic transfer with Stack134 and Stack132, retaining all
  actual-grid identities and the Carlson dynamic zero-free certificate.

The direct and Carlson grids are intentionally independent. Combining bounds
does not require or assert a common selected height.

## Claim boundary

The result automatically selects the better of two already-proved upper
bounds at each natural point. It does not compare their constants, improve
either exponent, create a shared-height theorem, prove oscillation, or imply RH.
