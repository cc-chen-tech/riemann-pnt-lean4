# Mass barrier in the bidirectional actual-PNT certificate

## Verified alternative

For a conjugation-stable seed with

`outside(S0) >= c / 2`,

the zero-supported bidirectional selector still supplies:

- fixed-rate relative PNT decay;
- all Carlson real-part and boundary-gap certificates;
- an actual-PNT lower-transfer implication at scale
  `((c - loss) / 2) * x ^ beta`.

But its selected extension necessarily satisfies

`loss <= finiteCoefficientMass(S \ S0)`.

Therefore the lower implication's strict trigger

`finiteCoefficientMass(S \ S0) < loss`

is impossible for the same selected certificate.

## Mathematical meaning

This identifies a genuine incompatibility rather than a missing Lean
plumbing lemma. Finite conjugation-stable boundary capture pays twice for
positive-height Carlson mass. Once the seed outside mass reaches half the
local coefficient, the extension cannot both close the Carlson tail and
remain perturbatively small.

No unconditional Omega conclusion or RH is claimed. Closing the lower branch
requires new information that changes this coefficient-mass balance, such as
a stronger cluster oscillation mechanism rather than another selector facade.
