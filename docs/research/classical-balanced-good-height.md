# Classical balanced good height

## The actual schedule

Let `b > 0` be the constant in the proved moving right edge

```text
rho.re <= 1 - b / log (T + 6).
```

For the common uniform good-height selector, define

```text
A_b(x) = exp (sqrt(b) * sqrt(log x)),
H_b(x) = selection.height (A_b(x) - 1).
```

The selector theorem gives, eventually,

```text
A_b(x) - 1 <= H_b(x) <= A_b(x)
```

and `H_b(x)` is an analytic good height.  The same selected height retains the
full natural-point truncated explicit-formula certificate.

## Near-optimal width without a fixed loss

The finite-zero theorem contains `log (T + 6)`, so an exact identity with
`sqrt(b) / sqrt(log x)` is unavailable at finite `x`.  The correct statement
is epsilon-sharp:

```text
b / log (T + 6)
  >= (sqrt(b) - epsilon) / sqrt(log x)
```

for every `epsilon` with `0 < epsilon < sqrt(b)` and all sufficiently large
`x`, provided `T <= A_b(x)`.

`classicalBalancedHeight_zeroFreeWidth_ge` proves the quantitative arithmetic
step with an explicit threshold.  Thus the `+6` changes only a lower-order
term; it does not force a fixed factor such as `1/2` in the asymptotic
exponential rate.

## Integration status

The chain now contains actual objects throughout:

```text
proved zeta zero-free region
  -> moving finite-zero right edge
  -> optimally scaled unit good-height window
  -> actual natural-point explicit-formula certificate.
```

The remaining upper-bound integration is to combine the epsilon-sharp width
with the finite zero-sum multiplicity bound and the selected contour
remainder in one relative PNT theorem.  Carlson density is not needed for the
classical global upper bound itself; it becomes relevant when a weaker
height-dependent boundary is aggregated strip by strip.
