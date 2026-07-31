# Variable-Boundary Low-Strip Decay Design

## Goal

Close the last analytic tail input in the variable-boundary explicit-formula
chain by proving decay of the actual moving low positive strip.

## Method

At each natural point, use the canonical two-strip input after deleting the
package at `beta(m)`. The empty-cluster norm guard supplies one uniform
`kappa > 0` for every such low layer. The global zero-multiplicity estimate
then bounds the numerator by the existing polynomial-height/log-power
majorant. If `beta0 <= beta(m)` eventually, the moving target amplitude is at
least `m^(beta0-1)`, so the fixed margin

```text
sigma - beta0 + alpha + epsilon < 0
```

forces decay.

Stack107 supplies the exact `positive <= low + visible` bridge, stack106
discharges real ordinates, and stack105 restores conjugate negative ordinates.
The final corollary therefore produces the complete actual moving
explicit-formula residual at the variable target amplitude.

## Claim boundary

This closes the analytic residual side under the stated polynomial-height,
right-edge, fixed-gap, and contour inputs. It does not construct the moving
package anti-cancellation witness, prove both oscillation signs, or imply RH.
