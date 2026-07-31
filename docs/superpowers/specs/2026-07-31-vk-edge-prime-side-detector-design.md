# VK-Edge Prime-Side Detector Design

## Goal

Determine whether a finite Dirichlet detector can simultaneously annihilate
already-used zeta-zero poles and the pole at `s = 1` while retaining enough
sign information on the prime side to force a new singularity.

The first mergeable milestone is an exact algebraic obstruction at `s = 1`.
For a finite coefficient family `a_n`, define

```text
A(1) = sum_{n in S} a_n / n.
```

Lean will prove that nonnegative, nonzero coefficients force `A(1) > 0`.
Consequently a nontrivial detector satisfying `A(1) = 0` must use signed
coefficients. It will also identify the exact cancellation budget:

```text
A(1) = positive weighted mass - negative weighted mass.
```

Thus pole cancellation is equivalent to equality of those two masses.

## Mathematical Boundary

This milestone does not construct a detector that vanishes at prescribed
zeta zeros. It does not prove a prime-side lower bound after introducing
signed coefficients. It does not force a new zeta zero and does not imply RH.

Its purpose is to rule out the naive Landau route using a nonzero Dirichlet
polynomial with nonnegative coefficients: such a polynomial cannot cancel the
main pole at `s = 1`.

## Definitions

Create a focused module under `PrimeNumberTheorem` with:

```lean
finiteDirichletDetectorAtOne
positiveDirichletDetectorMassAtOne
negativeDirichletDetectorMassAtOne
```

The support is a `Finset ℕ`. Every public theorem assumes every supported
index is positive, so division by the natural index has a strictly positive
real denominator.

## Public Theorems

The module exposes:

```lean
finiteDirichletDetectorAtOne_eq_positive_sub_negative
finiteDirichletDetectorAtOne_pos_of_nonnegative
finiteDirichletDetectorAtOne_ne_zero_of_nonnegative
finiteDirichletDetectorAtOne_eq_zero_iff_mass_balance
positive_and_negative_coefficients_of_vanishes_at_one
```

The final theorem assumes the coefficient family is nonzero on the support
and concludes that both a positive and a negative supported coefficient
exist.

## Next Gate

After this obstruction is formalized, the next mathematical question is not
another wrapper. It is to construct a signed detector with both:

1. exact zeros at the selected old zeta poles and at `s = 1`;
2. a quantitative prime-side response larger than the cancellation mass
   introduced by the negative coefficients.

If the second condition cannot be met, the branch records the concrete
inequality that fails. No conditional `Prop` facade is added.

## Verification

- exact contract for every public theorem;
- dedicated `#print axioms` audit;
- central axiom allowlist registration;
- placeholder scan and focused build;
- `LEAN_NUM_THREADS=1` for any Lake build, with one global Lean process.

