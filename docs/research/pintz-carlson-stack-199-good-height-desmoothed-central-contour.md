# Stack199: good-height de-smoothed central contour

Stack197 reduced the actual cubic de-smoothed contour to local bounds for
`||zeta'/zeta||`.  Stack198 discharged that input only on the right inner
zero-free segment.  Stack199 closes the entire positive-real-part horizontal
edge by selecting the contour height dynamically.

## Analytic chain

The existing actual-zeta good-height theorem combines:

```text
local zero ordinates in a fixed window = O(log A),
distance from the selected height to every zero ordinate >= c/log A,
shifted-Jensen local divisor mass = O(log A),
shifted-Jensen regular part = O(log A).
```

Therefore one height `T in [A,A+1]` simultaneously satisfies

```text
||logDeriv zeta(sigma +/- i*T)|| <= C*(1+log(A+6))^2
```

throughout `-1 <= sigma <= 2`.

Stack199 converts this height to the cubic parameter

```text
W = T/(2*pi),
```

so the actual cubic contour edges are exactly at imaginary parts `-T` and
`+T`.  Stack197 then gives, simultaneously for every
`0 < a <= c <= 2`, both de-smoothed integral bounds

```text
pointwiseBudget(x,h,c,T,C*(1+log(A+6))^2,c+T) * |c-a|,
```

under the natural local-kernel condition `h*(c+T) <= 1`.

## Mathematical significance

This removes the whole-edge logarithmic-derivative hypothesis from Stack197.
The contour height is now selected by actual zeta-zero separation, while the
same height controls both signs.  The remaining contour-remainder task is the
vertical left edge, not an uncontrolled horizontal critical-strip segment.

## Claim boundary

The result is a machine-checked actual-zeta horizontal contour budget for the
cubic de-smoothing chain.  It does not yet bound the left vertical edge,
optimize `T=T(x)` and `h=h(x)`, prove RH, or prove an unconditional Omega
theorem.
