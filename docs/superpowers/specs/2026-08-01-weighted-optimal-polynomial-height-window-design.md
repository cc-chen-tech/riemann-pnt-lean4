# Weighted Optimal Polynomial-Height Window Design

## Goal

Generalize the minimax polynomial-height allocation from the classical unit
density slope to an arbitrary nonnegative power-density slope `q`, while
retaining an exact specialization back to the existing quarter-gap optimizer.

## Scope

This stack adds only a density/transfer arithmetic layer. It does not modify
the protected complementary-zero module, the VK-edge modules, or the Sharp
oscillation work. It does not formalize a new Carlson, Guth-Maynard, Johnston,
or Bellotti estimate, and it does not claim RH or an unconditional Omega
theorem.

## Budget geometry

Write

```text
L = 1 - beta
D = beta - sigma
W = D - q L.
```

For a common safety margin `r`, require

```text
L + r <= inner
inner + r <= outer
r <= epsilon
q * outer + epsilon + r <= D.
```

When `q >= 0`, the first two inequalities imply
`q * (L + 2r) <= q * outer`. Combining all four constraints gives

```text
2 * (q + 1) * r <= W.
```

Hence every feasible allocation satisfies

```text
r <= W / (2 * (q + 1)).
```

The proposed optimizer takes

```text
r*      = W / (2 * (q + 1))
inner*  = L + r*
outer*  = L + 2r*
epsilon = r*.
```

All four margins are then exactly `r*`. For `q = 1`, `W` is the existing
canonical gap `2 beta - 1 - sigma`, so `r* = W / 4` and all four public
parameters agree with the previous optimizer.

## Lean interface

The implementation exposes definitions for `W`, `r*`, `inner*`, `outer*`,
and `epsilon`, followed by four theorem layers:

1. A general minimax upper bound for every feasible allocation.
2. Exact attainment of all four margins by the proposed allocation.
3. Exact recovery of the existing optimizer at `q = 1`.
4. A strict-feasibility specification and an actual selected-height/remainder
   certificate.

The selected-height theorem reuses the existing uniform good-height selector,
polynomial upper-height comparison, divergence to infinity, and actual
natural-point remainder certificate. It introduces no new analytic axiom.

## Audit boundary

The implementation, contract, and axiom-audit targets are compiled directly
against the existing overlay. The expected axiom boundary is exactly
`propext`, `Classical.choice`, and `Quot.sound`.
