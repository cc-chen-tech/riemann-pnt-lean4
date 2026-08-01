# Exceptional-zero detect-or-count: one strict step

## Closed integration step

Let `S` be a finite set already known to consist only of nontrivial zeta
zeros in `nontrivialZerosFinset T`.

The module proves two concrete update rules:

1. If an upstream theorem produces
   `rho ∈ nontrivialZerosFinset T` with `rho ∉ S`, use
   `S' = insert rho S`.
2. If an upstream theorem produces a nonempty packet `P` contained in
   `nontrivialZerosFinset T` and disjoint from `S`, use `S' = S ∪ P`.

In both cases Lean proves

```text
S ⊆ S'
S.card < S'.card
S' ⊆ nontrivialZerosFinset T
```

The combined endpoint is
`exists_strictly_larger_recordedZeroSet_of_detect_or_count`.

## Adjacent Sharp handoff

The stacked Sharp branch
`research/vk-edge-distinct-complement-witness` supplies the exact single-zero
input:

```text
∃ rho ∈ nontrivialZerosFinset T, rho ∉ S
```

from strict positivity of the full complementary moving Gaussian energy, or
from a selected-cluster remainder surplus above the approximation and closed
term budgets.  Once that stacked theorem is available on the integration
base, it can be composed directly with
`exists_strictly_larger_recordedZeroSet_of_new_nontrivialZero`.

## Exact remaining blocker

This module does not prove that the Sharp surplus survives after replacing
`S` by `S'`.  Consequently it proves one strict growth step, not an infinite
iteration, a Carlson contradiction, zero exclusion, or the Riemann
hypothesis.
