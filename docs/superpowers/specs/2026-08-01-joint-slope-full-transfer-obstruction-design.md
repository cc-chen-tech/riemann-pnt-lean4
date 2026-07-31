# Joint-Slope Full-Transfer Obstruction Design

## Goal

Identify the correct minimax slope when a polynomial-height PNT transfer has
two independent costs, and formally separate the Carlson density-count budget
from the unit-slope low-kernel budget present in the current full transfer.

## Why this stack is necessary

Stack148 proves that Carlson's density exponent

```text
q(sigma) = 4 sigma (1 - sigma)
```

is below one and therefore gives a lower critical real part for the density
sub-budget. The existing full dynamic-boundary PNT assembler, however, also
requires

```text
sigma - beta + alpha + epsilon < 0.
```

That second condition has unit slope in the height exponent. Since the weaker
condition with `q(sigma) * alpha` does not imply it, directly installing the
Stack148 window into the full assembler would be invalid.

## Joint-slope theorem

For nonnegative `outer`, two constraints

```text
q * outer + epsilon + margin <= budget
k * outer + epsilon + margin <= budget
```

are equivalent to the single constraint

```text
max(q, k) * outer + epsilon + margin <= budget.
```

The Stack147 optimizer therefore applies with effective slope `max(q, k)`.
This yields both a general joint minimax upper bound and an attaining equal-
margin allocation.

## Carlson consequence

For `1/2 < sigma < 1`,

```text
0 < 4 sigma (1 - sigma) < 1.
```

Combining Carlson's slope with the independent unit-slope low-kernel cost
gives

```text
max(4 sigma (1 - sigma), 1) = 1.
```

Hence the full-transfer optimizer is exactly the existing quarter-gap
unit-slope optimizer. Stack148 remains a real improvement for the density
sub-budget, but not yet for the complete PNT chain.

## Explicit non-implication witness

For every `sigma < beta`, take

```text
outer  = beta - sigma
epsilon = (1 - q(sigma)) * (beta - sigma) / 2.
```

Both parameters are positive. The Carlson-density margin is strict, while the
unit-slope full-transfer margin fails. This gives a machine-checked reason why
the current facade cannot accept only the weighted condition.

## Claim boundary

This stack is an obstruction and optimization theorem, not a new density
estimate or PNT rate. It does not modify protected, Sharp, or VK-edge modules
and does not claim RH or an unconditional Omega theorem. A genuine threshold
improvement for the full transfer now requires reducing or replacing the
independent unit-slope low-kernel cost.
