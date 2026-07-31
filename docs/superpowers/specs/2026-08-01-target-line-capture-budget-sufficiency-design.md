# Target-line Carlson capture budget sufficiency

## Objective

Prove the converse direction missing from the existing half-coefficient
barrier.  Under a strict real-ordinate exclusion at the target line, show that
an initial outside boundary mass below `c / 2` is sufficient to construct a
finite target-line extension satisfying both the local extension coefficient
budget and the final canonical Carlson outside budget.

## Exact factor-two identity

For a finite conjugation-stable cluster `E` of nontrivial zeros satisfying
`Re rho = beta`, `Im rho != 0`, and `sigma < beta`, Carlson coverage gives

`finiteVisibleClusterCoefficientMass E =
  2 * actualCarlsonCapturedBoundaryMass beta E`.

The proof first identifies the positive-height coefficient mass with captured
Carlson mass using the injective and surjective high-positive-zero index.  The
negative-height mass equals the positive mass by conjugation, while the real
part is empty.

## Sufficiency construction

Write `B0` for the outside boundary mass of the original seed and assume
`B0 < c / 2`.  Capture until the final outside mass `Bout` satisfies

`2 * Bout < c - 2 * B0`.

Exact seed-relative allocation and the factor-two identity imply

`coefficientMass(S \\ S0) < c - 4 * Bout`.

Choose `loss` as the midpoint between these two quantities.  Then

- `coefficientMass(S \\ S0) < loss`;
- `0 < c - loss`;
- `2 * Bout < (c - loss) / 2`.

## Claim boundary

The construction assumes every real-ordinate nontrivial zero lies strictly
left of `beta`.  It establishes simultaneous budgets, not seed oscillation
witnesses or an unconditional Omega theorem.  Together with the existing
necessity barrier, it identifies `B0 < c / 2` as the sharp budget threshold
under the stated target-line and real-ordinate hypotheses.
