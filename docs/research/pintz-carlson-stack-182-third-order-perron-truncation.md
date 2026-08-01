# Stack 182: Explicit quadratic third-order Perron truncation

## Goal

Turn Stack 181's all-height cubic Perron inversion into the finite-height
`H^-2` estimate required by the quadratic-kernel PNT transfer.

## Theorem chain

For `W > 0` and `W <= |w|`, the imaginary part gives

```text
2 pi |w| <= norm(c + 2 pi i w).
```

Therefore the cubic kernel satisfies

```text
norm(exp((c + 2 pi i w)u) / (c + 2 pi i w)^3)
  <= exp(cu) / (8 pi^3 |w|^3).
```

Integrating `w^-3` over either tail yields

```text
upper tail <= exp(cu) / (16 pi^3 W^2),
lower tail <= exp(cu) / (16 pi^3 W^2).
```

Combining both tails with Stack 181's exact all-height inversion gives

```text
norm(integral_[-W,W] K3(c,u,w) - max(u,0)^2/2)
  <= exp(cu) / (8 pi^3 W^2).
```

## Significance

This is an actual, explicit `W^-2` Perron truncation estimate.  It supplies the
analytic remainder order that Stacks 175-177 previously treated abstractly.

## Claim boundary

The estimate is still scalar.  The von Mangoldt coefficient sum and its
summability constant have not yet been inserted, and no cubic zeta contour
shift or twice-differenced PNT remainder bound is claimed here.
