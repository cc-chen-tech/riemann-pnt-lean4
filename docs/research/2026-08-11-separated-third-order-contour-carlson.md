# Separated contour and Carlson heights

The existing joint two-height parameters use a relatively small `layerAlpha`
to make the low-layer and Carlson exponents strictly negative. That exponent
must not be conflated with the analytic contour exponent required by the
third-order explicit formula.

This slice fixes the outer contour exponent at `3/4`, so it lies strictly
between `2/3` and `1`, while retaining the independently constructed
`layerAlpha`, `gammaLow = layerAlpha / 2`, and balanced `gammaHigh`.

Since `layerAlpha <= 1`, one has `gammaLow <= 1/2 < 3/4`. The cubic diagonal
tail begins at `gammaLow` and is independent of the upper endpoint, so the
actual normalized smoothed strip energy between `gammaLow` and the contour
height `3/4` tends to zero. At the same exponent, the genuine third-order
contour remainder has eventually available good heights and tends to zero.

The theorem records all four strict target-amplitude exponent margins and all
three cubic L2 block exponents. It does not use Gram/Schur occupancy, prove an
Omega theorem, imply RH, or claim that a single height exponent works for both
roles.
