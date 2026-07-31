# Seed-witness signed PNT transfer below the half threshold

## Objective

Close the gap between an original finite target-line seed and the actual PNT
error.  The local positive and negative witnesses are stated on the prescribed
seed `S0`, not on an automatically enlarged cluster.

## Inputs

- a conjugation-stable target-line zeta seed `S0`;
- `1/2 < sigma < 1` and `(1 + sigma) / 2 < beta`;
- an outside real-part cap at `beta`;
- strict left separation for real-ordinate nontrivial zeros;
- initial outside Carlson boundary mass below `c / 2`;
- positive and negative coefficient-`c` visible-main witnesses for `S0`.

## Transfer chain

1. Stack90 selects `S` and `loss` with extension coefficient mass below
   `loss` and final canonical boundary budget below `(c - loss) / 2`.
2. The finite coefficient estimate bounds the newly adjoined visible terms by
   `loss` on the target scale.
3. Both seed witnesses survive on `S` with coefficient `c - loss`.
4. The fixed Carlson boundary signed transfer sends both signs to the actual
   relative Chebyshev error with coefficient `(c - loss) / 2`.
5. The same theorem returns natural-point relative PNT convergence.

## Claim boundary

This is conditional on the seed's signed visible-main witnesses and on the
explicit half-threshold and real-ordinate hypotheses.  It does not produce the
seed witnesses, prove an unconditional Omega theorem, or imply RH.
