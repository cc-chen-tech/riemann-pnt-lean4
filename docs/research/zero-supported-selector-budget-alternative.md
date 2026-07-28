# Zero-supported selector budget alternative

## Quantitative statement

Assume:

- `0 < c - loss`;
- the seed is conjugation-stable and has an outside real-part cap;
- `outside(S0) >= c / 2`.

The strengthened selector produces a finite extension `S` with:

- seed inclusion;
- conjugation stability;
- nontrivial-zero support on `S \ S0`;
- the existing real-part and real-ordinate structural outputs;
- the canonical Carlson gap
  `2 * outside(S) < (c - loss) / 2`.

For this selected cluster one necessarily has

`loss <= finiteCoefficientMass(S \ S0)`.

## Proof mechanism

If the coefficient mass were `< loss`, conjugation would imply

`2 * captured(S \ S0) < loss`.

Together with the canonical outside gap and exact boundary allocation, this
would force `outside(S0) < c / 2`, contradicting the seed threshold.

## Interpretation

The selector now closes the structural and zero-membership interfaces. The
remaining failure is quantitative: a finite extension cannot simultaneously
capture enough Carlson boundary mass and stay below the perturbative
coefficient budget once the seed crosses the half-coefficient threshold.

This does not prove RH or an unconditional Omega theorem.
