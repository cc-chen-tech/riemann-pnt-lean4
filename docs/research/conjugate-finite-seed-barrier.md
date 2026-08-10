# Conjugation-aware finite-seed barrier

## Scope

This note records a finite arithmetic obstruction in the
Carlson/explicit-formula transfer layer. It does not construct a localized
pi/2 oscillation theorem, a zero-reproduction tree, RH, or an unconditional
Omega theorem.

## Theorem chain

Let `E = S \ S0` be the finite extension of a seed cluster.

1. Exact boundary allocation:

   `captured(E) + outside(S) = outside(S0)`.

2. Positive-height Carlson capture:

   Carlson indices count positive-height zeros. Restricting `E` to positive
   height therefore leaves `captured(E)` unchanged.

3. Conjugation cost:

   If `E` is conjugation-stable and every member of `E` is a nontrivial zeta
   zero, the positive and negative coefficient masses agree. Hence

   `2 * captured(E) <= finiteCoefficientMass(E)`.

4. Canonical budgets:

   If `finiteCoefficientMass(E) < loss`, then
   `captured(E) < loss / 2`. If

   `2 * outside(S) < (c - loss) - (c - loss) / 2`,

   then `outside(S) < (c - loss) / 4`.

5. Necessary seed condition:

   For `0 < c - loss`, the previous inequalities imply

   `outside(S0) < loss / 2 + (c - loss) / 4 < c / 2`.

Thus a seed with `outside(S0) >= c / 2` cannot be repaired by any finite
conjugation-stable, zero-supported extension satisfying the canonical
budgets, even if `loss` may vary.

## Honest interface boundary

Conjugation stability alone is not enough. The factor-two argument uses
equality of analytic multiplicities at conjugate zeta zeros, so every member
of the extension must be certified as a nontrivial zeta zero.

The current finite-seed selector exposes boundary support but does not yet
expose this all-members-are-zeros certificate. Therefore the strengthened
barrier is a conditional interface theorem, not yet an automatic consequence
of the existing selector.
