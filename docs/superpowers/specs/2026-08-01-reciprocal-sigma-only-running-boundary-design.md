# Reciprocal Sigma-Only Running-Boundary Design

## Goal

Turn the reciprocal variable-boundary transfer into a sigma-only facade that
automatically selects the fixed anchor, selected height, contour certificate,
real-zero separation, monotone running boundary, and indexed right edge.

## New anchor

The reciprocal low layer only requires `sigma < beta0`. The finite real-axis
residual additionally requires every real-ordinate zero to lie below `beta0`.
Define

```text
B(sigma) = max(realOrdinatePNTZeroBottleneck, sigma)
beta0    = (B(sigma) + 1) / 2.
```

For `1/2 < sigma < 1`, this gives `sigma < beta0 < 1` and strict exclusion of
all fixed real-ordinate zeros.

## Height parameters

Choose

```text
inner   = 1 - beta0 / 2
outer   = (inner + 1) / 2
epsilon = (beta0 - sigma) / 2.
```

Then

```text
0 < inner < outer,
inner <= 1,
1 - beta0 < inner,
sigma - beta0 + epsilon < 0.
```

The uniform good-height selector at `inner` is eventually below the
polynomial height at `outer`, tends to infinity, and supplies the actual
natural-point remainder certificate.

## Running boundary

The natural running visible-zero boundary automatically provides:

```text
beta0 <= beta(m),
monotonicity on natural samples,
indexed variable-boundary right-edge capture.
```

The final public theorem therefore accepts only `sigma`, ordinary positive
constants, a good-height selector, and positive/negative visible-main
witnesses.

## Claim boundary

The upper transfer is automatic. The signed conclusion remains conditional
on the two explicit visible-main witnesses. No anti-cancellation theorem, RH,
or unconditional Omega conclusion is claimed. Protected, Sharp, and VK-edge
modules remain untouched.
