# Third-order dynamic contour decay

## Result

This slice specializes the genuine cubic zeta contour remainder to a dynamic
height window T in [x^alpha, x^alpha + 1].

For every 2/3 < alpha < 1, 1 < c <= 2, and epsilon > 0, all sufficiently
large x admit a good height in that window with

    norm (thirdOrderContourRemainder x (-1) c (T / (2*pi))) < epsilon.

The selected-height constant is uniform in x, c, and the lower height
parameter. This quantifier order is essential for the limit statement.

## Explicit envelope

The proof dominates the selected-height remainder by a fixed constant multiple
of

    x^(2 - 3*alpha) * (log x)^8
      + x^(alpha - 1) * (log x)^4
      + x^(-1) * (log x)^4.

The polynomial exponents have the following status:

- 2 - 3*alpha < 0 strictly because alpha > 2/3;
- alpha - 1 < 0 strictly because alpha < 1;
- -1 < 0 strictly;
- alpha = 2/3 is critical for the horizontal term;
- alpha = 1 is critical for the left-edge term.

The log^8 loss comes from squaring the reusable log^4 absorption bound for
the two horizontal edges. The left edge retains only log^4. No multiplicity
loss occurs in this contour estimate.

## Role in the unified route

This closes the contour-height obstruction for the genuine third-order
explicit formula: the third reciprocal kernel power makes the horizontal
remainder decay for alpha > 2/3, while the fixed negative-one line decays for
alpha < 1.

It does not yet bound the medium/high zeta-zero tail, transfer the smoothed
formula back to the unsmoothed PNT error, prove an Omega theorem, or imply RH.
Those remain separate downstream interfaces.
