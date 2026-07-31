# Cubic Strict Theta-Only Reverse Zero-Free Design

## Goal

Complete the quantitative reverse direction at the cubic-strict target
exponent selected automatically from `theta`.

## Inputs

- `1 / 2 < theta < 1`;
- `q < 1 / 2`;
- a global positive-zero real-part bound `rho.re <= theta`;
- an eventual actual PNT-error bound at the cubic-strict target scale;
- a visible-cluster witness whenever the automatically selected right-edge
  cluster is nonempty.

## Reverse chain

The stack74 actual transfer is specialized to the finite-height right-edge
zero finset at

```text
beta = jointTwoHeightCubicStrictTargetExponent theta.
```

If the adjoined cluster were nonempty, the visible-cluster witness and actual
transfer would produce arbitrarily large points satisfying

```text
abs(relativeChebyshevPsi0Error x)
  >= targetZeroPowerAmplitude beta x / 2.
```

The eventual upper bound with coefficient `q < 1 / 2` excludes such points.
Therefore the adjoined cluster, and hence the right-edge zero finset, is empty.

## Output

The theorem returns the inverse boundary, cubic-strict target, all optimized
truncation parameters, their defining certificates, and
`FiniteHeightRightEdgeZeroFree beta H`.

## Boundary

The numerical parameter selection and quantitative contradiction are
automatic. The visible-cluster anti-cancellation witness remains explicit, so
this is not an unconditional zero-free theorem or RH.
