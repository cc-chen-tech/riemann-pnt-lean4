# Finite-Rate Actual Remainder Decay

## Goal

Prove that pointwise optimization across the actual Pintz good-height rate grid
preserves ordinary natural-point explicit-formula remainder decay.

## Fixed-rate chain

For every grid rate `k` with `0 < k <= 1`:

1. the regularized candidate is eventually in the good-height interval below
   `pintzCarlsonHeight k m`;
2. the exact cofinal contour bound divided by `m` tends to zero;
3. the closed logarithmic real-axis contribution divided by `m` tends to zero;
4. the truncated formula certificate bounds the actual multiplicity-aware
   relative remainder by their sum;
5. squeezing gives actual remainder convergence to zero.

## Finite switching

At each natural sample, the optimized height equals one fixed-rate candidate.
Its absolute remainder is therefore at most the sum of all candidate absolute
remainders. The finite sum tends to zero, so the optimized-height actual
remainder tends to zero even when the selected rate changes with the sample.

## Boundary

This is ordinary relative remainder decay. It is not decay relative to a
moving target-zero amplitude, and it does not prove unconditional Omega or RH.
