# Actual zero-package moving-right-edge Omega design

## Objective

Close one concrete dynamic-layering path in which the same actual zeta-zero
objects feed the mean-square lower bound, Carlson density control, and the
explicit formula.

## Quantitative chain

Let `P_T` be an actual equal-real-part package at real part `beta`, let
`E(T,beta,L)` be its sampled energy, and put

```text
c = q * sqrt(E(T,beta,L))
B = actualCarlsonOutsideClusterBoundaryMass beta P_T
delta = (c - 2*B) / 2
loss = 2*B + delta
coefficient = (c - 2*B) / 4
```

The automatic package selector proves `2*B < c`.  The package mean-square
theorem gives a natural-point seed witness of size `c*x^(beta-1)`.  Boundary
absolute mass bounds every zero entering the moving right-edge cluster but
outside `P_T` by `loss*x^(beta-1)`.  Moving Carlson bounds the complementary
cluster and the selected-height explicit formula bounds the contour terms.
The moving-seed transfer retains half of `c-loss`, which is exactly the stated
positive coefficient.

## Claim boundary

The attained-edge facade assumes a maximal real part is explicitly attained,
lies above `2/3`, and is below `1`.  The result is an unsigned Omega witness at
the exact `x^beta` scale.  It does not prove attainment, signed Omega in both
directions, or RH.
