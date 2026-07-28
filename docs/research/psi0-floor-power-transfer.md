# Power-scale transfer from continuous psi0 witnesses to natural floors

## Theorem chain

For `beta > 0` and every `loss > 0`,

```text
roundingBudget(x) = o(x^beta)
  -> eventually roundingBudget(x) <= loss * x^beta
  -> eventually roundingBudget(exp y) <= loss * exp(beta*y).
```

Consequently,

```text
c * exp(beta*y) <= |psi0(exp y) - exp y|
```

eventually implies

```text
(c - loss) * exp(beta*y)
  <= |psi0(floor(exp y)) - floor(exp y)|.
```

This preserves both the correct zero-forced power and every strict constant
margin.  A factor such as `1 / |rho|` can be included in `c`.

## Remaining bridge

The continuous equal-real-part zero-package theorem supplies the main
witness.  The unresolved analytic step is still a sufficiently small
complementary-zero and contour remainder at that witness, or an aligned
window-energy upper estimate.  This module proves no unconditional Omega
statement.
