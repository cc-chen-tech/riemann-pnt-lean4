# Quantitative floor rounding for continuous psi0 witnesses

## Result

For a real point `x`, replacing `x` by `floor x` does not change
`chebyshevPsi x`.  The midpoint version `chebyshevPsi0` can differ only
through its half-jump terms.  Consequently,

```text
|E(x) - E(floor x)|
  <= |jump(x)| / 2
     + |jump(floor x)| / 2
     + |x - floor x|,
```

where `E(x) = chebyshevPsi0(x) - x`.

The reverse-triangle corollary transfers a continuous witness at
`x = exp y` to the natural point `floor (exp y)` after subtracting exactly
this explicit budget.

## Role in the unified chain

The existing zero-package mean-square theorem produces a real logarithmic
point `y`.  The Carlson window-energy transfer is indexed by natural points.
This module supplies the first concrete bridge between those sampling
conventions without changing the main `x^beta` scale.

## Remaining estimate

To make the loss asymptotically negligible at scale `x^beta`, one still needs
an upper bound for the two von Mangoldt jumps.  The geometric floor loss is
already less than one for positive `x`.  This module does not assert the
missing jump estimate and does not claim an unconditional Omega theorem.
