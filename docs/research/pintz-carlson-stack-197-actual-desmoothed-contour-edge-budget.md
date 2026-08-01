# Stack197: actual de-smoothed contour edge budgets

Stack196 identified the normalized cubic second difference with a first-order
explicit-formula expression and the actual de-smoothed bottom, top, and left
contour integrals.  Stack197 makes the remaining contour estimate quantitative
without hiding a global zeta bound.

## Machine-checked chain

For `x > 0`, the actual integrand satisfies the exact norm factorization

```text
||deSmoothedIntegrand(x,h,s)||
  = ||zeta'/zeta(s)|| * (x^(Re s) / ||s||) * ||M(s,h)||.
```

On the local range `h ||s|| <= 1`, Stack193 gives

```text
||M(s,h)|| <= 1 + 3 h ||s||.
```

The new module proves the concrete contour geometry

```text
2*pi*W <= ||sigma +/- 2*pi*W*i|| <= c + 2*pi*W,
a        <= ||a + t*i||             <= a + 2*pi*W,
```

on the relevant intervals.  It then derives bottom, top, and left integral
budgets with their actual lengths `|c-a|`, `|c-a|`, and `4*pi*W`, and assembles
them into the Stack196 contour remainder.

## Explicit hypothesis boundary

The edge theorems take visible pointwise bounds for
`||logDeriv riemannZeta||`.  This is necessary: the existing
`O((log T)^2)` theorem only applies in a narrower zero-free strip near
`Re s = 1`, while a horizontal contour from `a < 1` to `c` generally leaves
that strip.  Mere nonvanishing on a compact edge gives some finite bound but
not a universal explicit expression in `a,c,W`.

The next quantitative step is therefore to split each horizontal edge into a
right zero-free segment, where the existing log-squared theorem applies, and a
left segment controlled by quantitative zero-distance or zero-density input.

## Claim boundary

This stack proves actual contour-integral budgets conditional on displayed
local logarithmic-derivative bounds.  It does not prove those bounds on the
entire rectangle, an optimized contour remainder, RH, or an unconditional
Omega theorem.
