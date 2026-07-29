# Classical admissible good height

Let

```text
alpha_* = min(1, sqrt(b))
H_*(x) = exp(alpha_* * sqrt(log x)).
```

The uniform natural-point good-height selector is evaluated at

```text
H_*(x) - 1.
```

The selected height therefore lies eventually in

```text
[H_*(x) - 1, H_*(x)],
```

is an analytic good height, and carries the same truncated explicit-formula
certificate for every natural sample.

Because `0 < alpha_* <= 1`, the existing depth-zero contour theorem applies
without any new analytic hypothesis.  The resulting proved limit is

```text
cofinalPNTFormulaRemainderBound(..., selectedHeight, m, 0) / m
  -> 0.
```

The important compatibility fact is that the good-height selector, the
finite-zero truncation, and the contour remainder all use the same selected
height.  No exchange between separately chosen existential heights is made.
