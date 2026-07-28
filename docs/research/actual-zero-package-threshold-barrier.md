# Fixed-package Carlson threshold barrier

This module proves a necessary condition for the threshold-driven actual
zero-package transfer.

For `1/2 < sigma < 1`, if `beta <= tau` and `beta < 1`, then

```text
carlsonStripEndpointTargetThreshold(sigma, tau) < beta
```

is impossible. Therefore every zero covered by a strip satisfying the strict
threshold inequality must have real part strictly below `beta`.

If the selected height tends to infinity, a fixed finite cluster satisfying
these strip conditions must contain every positive-ordinate nontrivial zero
with real part exactly `beta`.

For the height-truncated package

```text
equalRealPartZeroPackage(T, beta),
```

this implies that every positive-ordinate zero on the same real-part line has
imaginary part at most `T`. In particular, one such zero above `T` contradicts
the entire fixed-package threshold setup.

This establishes a formal design constraint:

```text
fixed finite package + strict Carlson decay
```

requires global exhaustion of the target real-part line. Carlson density alone
does not provide that exhaustion. A more general unconditional route must
either use a dynamically growing main package or control the full boundary
package without treating it as a negligible complement.

