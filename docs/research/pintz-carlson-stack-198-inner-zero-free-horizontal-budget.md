# Stack198: inner zero-free horizontal contour budget

Stack197 reduced each actual de-smoothed contour edge to a visible local bound
for `||zeta'/zeta||`.  Stack198 discharges that input on the right portions of
both horizontal edges using the proved narrower classical zero-free region.

## Dynamic right segment

At height

```text
T = 2*pi*W,
```

the segment begins at

```text
b(W) = 1 - k / (2*log T).
```

The existing analytic theorem supplies constants `k > 0`, `C >= 0`, and
`T0 >= 2` such that, for `T >= T0` and `b(W) <= sigma <= 2`,

```text
||logDeriv riemannZeta (sigma +/- i*T)|| <= C*(log T)^2.
```

The new Lean module proves that the actual cubic bottom and top contour points
match these two signs, then feeds the common log-squared budget into Stack197.
Consequently both de-smoothed right horizontal integrals have the explicit
bound

```text
pointwiseBudget(x,h,c,T,C*(log T)^2,c+T) * |c-b(W)|.
```

The theorem `exists_actual_innerZeroFreeHorizontalContourBudgets` obtains all
three constants directly from the proved zeta zero-free-region theorem; it
does not assume a new analytic estimate.

## Remaining split

This closes only the horizontal portion from `b(W)` to `c`.  If the original
left endpoint satisfies `a < b(W)`, the segments from `a` to `b(W)` still need
a quantitative zero-distance or zero-density estimate.  The vertical left
edge also remains separate.

## Claim boundary

Stack198 is an unconditional specialization of the existing inner zero-free
region to actual de-smoothed horizontal contour integrals.  It is not a bound
for the whole rectangle, an optimized PNT remainder, RH, or an unconditional
Omega theorem.
