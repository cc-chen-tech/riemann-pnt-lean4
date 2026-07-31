# Reciprocal Optimal Contour Height Design

## Goal

Identify and realize the exact infimum of polynomial selected-height exponents
after reciprocal summation removes the low-layer power cost.

## Feasible windows

A reciprocal contour window consists of `inner` and `outer` satisfying

```text
0 < inner <= 1
1 - beta < inner
inner < outer.
```

Every feasible outer exponent therefore satisfies

```text
1 - beta < outer.
```

The inequality is strict, so the floor is generally not attained.

## Near-optimal realization

For every `0 < delta < beta`, choose

```text
inner = 1 - beta + delta / 2
outer = 1 - beta + delta.
```

This is feasible, has `outer < 1`, and lies exactly `delta` above the contour
floor. Given any `epsilon > 0`, taking

```text
delta = min(epsilon / 2, beta / 2)
```

produces a feasible window strictly within `epsilon` of the floor.

## Actual selected height

The uniform good-height selector at `inner`:

- is eventually bounded by `x^outer`;
- tends to infinity on natural samples;
- supplies the actual natural-point explicit-formula remainder certificate.

Thus `1 - beta` is not merely a formal arithmetic lower bound. It is the
exact infimum of exponents realized by the machine-verified selected-height
and contour-remainder chain.

## Claim boundary

This optimizes truncation height for the reciprocal transfer. It does not
construct visible-main witnesses, prove RH, or prove an unconditional Omega
theorem. Protected, Sharp, and VK-edge modules remain untouched.
