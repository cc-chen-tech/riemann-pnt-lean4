# Classical admissible finite-zero decay

## General dynamic margin

For a truncation height satisfying

```text
T <= exp(alpha * u),
```

the classical moving boundary supplies a target width `rate / u` once

```text
rate * alpha < b.
```

The theorem `dynamicHeight_classicalZeroFreeWidth_ge` proves the exact
finite-threshold statement, including the `log(T + 6)` denominator.

This isolates the real optimization condition: the contour rate `alpha` and
the desired zero-free decay rate `rate` consume the product budget `b`.

## Application at the constrained optimizer

Set

```text
alpha_* = min(1, sqrt(b)),
rate = alpha_* / 2.
```

The constrained optimizer theorem gives `alpha_*^2 <= b`, hence

```text
rate * alpha_* < b.
```

At the same selected good height used by the contour certificate, the full
multiplicity-weighted finite zero sum then satisfies a majorant of the form

```text
constant * sqrt(log m)^2
  * exp(-rate * sqrt(log m)).
```

Consequently,

```text
norm(finiteZeroSum(m, selectedHeight(m))) / m -> 0.
```

No independent height choice is introduced.  This is the zero contribution
needed beside the already proved contour-relative limit.
