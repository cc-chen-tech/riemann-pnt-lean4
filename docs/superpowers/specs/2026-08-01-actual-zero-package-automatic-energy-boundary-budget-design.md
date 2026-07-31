# Actual Zero-Package Automatic Energy-Boundary Budget

## Objective

Remove the circular-looking external inequality comparing actual package
energy with its Carlson outside-boundary mass.

## Construction

Start from a nonempty finite target-line seed with a global outside real-part
cap. Put it in an initial height package `P0`. Its diagonal energy `D0` is
strictly positive. Fix the anchor `d = D0 / 2` before any further choices.

For a fixed `q > 0`, use stack97 with tolerance `q * sqrt(d) / 2`. This gives a
larger actual height package `P` whose outside boundary mass is below that
tolerance. Diagonal energy is monotone under package inclusion, so
`d < diagonalEnergy(P)`. Stack96 then chooses `L > 0` with
`d < actualEnergy(P,L)`.

Strict monotonicity of square root now gives

`outsideMass(P) < q * sqrt(actualEnergy(P,L)) / 2`.

The threshold was fixed from `P0`, so the argument is non-circular.

## Claim boundary

The result still assumes a nonempty target-line seed and its global right-edge
cap. It does not assert that a rightmost zeta zero exists, does not prove both
oscillation signs, and does not imply RH.
