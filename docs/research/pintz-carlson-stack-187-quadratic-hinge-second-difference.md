# Stack 187: Quadratic hinge second-difference kernel

## Goal

Formalize the exact scalar kernel needed to remove second-order Riesz
smoothing by two forward differences in the logarithmic variable.

## Kernel

For `Q(q)=max(q,0)^2/2`, define

```text
D_h(q) = Q(q+2h) - 2 Q(q+h) + Q(q).
```

For `h>0`, the formalized bounds are

```text
0 <= D_h(q) <= h^2.
```

Moreover,

```text
D_h(q) = h^2  when q >= 0,
D_h(q) = 0    when q + 2h <= 0.
```

Consequently the normalized kernel `D_h(q)/h^2` lies in `[0,1]`, equals one
for terms already active at the left endpoint, and vanishes for terms still
inactive at the right endpoint.

## Significance

These are exactly the pointwise facts needed to sum against nonnegative von
Mangoldt coefficients and sandwich the twice-differenced second Riesz mean
between Chebyshev psi at the two endpoints.

## Claim boundary

This stack proves the scalar kernel theorem.  The arithmetic summation and
the resulting `chebyshevPsi` endpoint inequality are the next stack.
