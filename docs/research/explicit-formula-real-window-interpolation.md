# Real-window explicit-formula interpolation

## Current bridge

The previous two stacked milestones provide:

1. one good height controlling all natural samples;
2. fixed-height spatial variation of the moving finite explicit formula.

To pass to an arbitrary real `x`, set `m = floor x`.  The Chebyshev function
is constant between consecutive integers, but the midpoint convention is not
literally equal at `x` and `m`.  The exact correction is

```text
psi0 x - psi0 m = (jump m - jump x) / 2.
```

Both jumps are nonnegative and logarithmically bounded.  This module first
formalizes that bookkeeping before combining it with the contour estimate.

## Claim boundary

The floor and jump lemmas are unconditional.  They do not yet choose a power
truncation height or prove a normalized window remainder estimate.
