# Actual strict-margin finite-zero majorant

## Goal

Close the zero-free half of the Stack 127 domination interface at the same
actual good height used by the truncated explicit formula.

For `u = sqrt (log m)`, height rate `k`, and `0 < theta < 1`, prove the actual
multiplicity-weighted finite zero sum satisfies eventually

`norm zeroSum / m <= 9 C u^2 exp (-(theta * b / k) u)`.

## Inputs

- the proved uniform classical finite-zero estimate with constants `b` and
  `C`;
- an actual candidate height selected in the unit interval below
  `exp (k u)`;
- `0 < k <= 1`;
- the strict rate `theta * b / k` from Stack 127.

The product identity

`(theta * b / k) * k = theta * b < b`

provides the strict margin needed by `dynamicHeight_classicalZeroFreeWidth_ge`.

## Output

The module provides a pointwise eventual theorem for supplied classical
constants and an existential theorem that obtains those constants directly
from the proved zeta zero-free finite-sum theorem, uniformly for every rate in
one finite grid.

## Claim boundary

This slice controls the actual finite zero sum only. It does not yet add the
actual contour remainder, minimize the resulting complete error envelope, or
prove a target-amplitude estimate, Omega theorem, or RH.
