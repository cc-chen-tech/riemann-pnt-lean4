# Zero-supported finite-seed Carlson selector

## Strengthened output

The seeded selector now retains the construction-level certificate

`forall rho in S \ S0, IsNontrivialZero rho`.

This is strictly stronger than boundary support. The seed `S0` itself is not
required to consist of zeros; only newly adjoined members are certified.

## Construction

The final cluster is

`S = S1 union S0 union realOrdinateZeros`,

where `S1` is the zero-supported Carlson boundary capture.

For a member of `S \ S0`:

- membership through `S1` gives the zero certificate from finite capture;
- membership through the real-ordinate set gives the zero certificate from
  its defining finite zero set;
- membership through `S0` contradicts the set-difference condition.

The selector continues to provide conjugation stability, outside real-part
caps, boundary support, real-ordinate absorption, and the doubled Carlson
outside-mass gap.

## Remaining quantitative obstruction

This selector does not make the finite coefficient mass of `S \ S0`
arbitrarily small. Therefore it does not by itself close an unconditional
Omega transfer. It does, however, make the conjugation factor-two barrier
applicable without an external zero-membership hypothesis.
