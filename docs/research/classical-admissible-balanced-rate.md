# Classical admissible balanced rate

## Why the unconstrained optimizer is not the final contour rate

For a classical zero-free constant `b > 0`, the unconstrained competition

```text
min(alpha, b / alpha)
```

is maximized at `alpha = sqrt(b)`.

The explicit-formula contour also needs its truncation height

```text
exp(alpha * sqrt(log x))
```

to remain at most polynomially comparable with `x`.  The existing contour
majorant uses the concrete sufficient restriction

```text
alpha <= 1.
```

Therefore the actual constrained optimizer is

```text
alpha_* = min(1, sqrt(b)).
```

## Formal result

`classicalAdmissibleBalancedRate_isOptimal` proves all four required facts:

```text
0 < alpha_*,
alpha_* <= 1,
min(alpha_*, b / alpha_*) = alpha_*,
min(alpha, b / alpha) <= alpha_*
  whenever 0 < alpha <= 1.
```

In particular,

```text
b / alpha_* >= alpha_*,
```

so the zero-free contribution never decays more slowly than the contour
contribution at the constrained optimum.

This correction matters formally even if the numerical classical zero-free
constant is expected to be less than one: the proved existence theorem only
states positivity and does not expose such a numerical upper bound.
