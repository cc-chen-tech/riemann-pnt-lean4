# Actual Zero-Package Automatic PNT Sign Alternative

## Objective

Compose the automatic energy-boundary budget with the actual-package Carlson
transfer and expose the resulting unnormalized PNT oscillation theorem.

## Inputs

- a nonempty finite seed of actual nontrivial zeros on `Re rho = beta`;
- `1/2 < sigma < 1` and `(1 + sigma) / 2 < beta`;
- a global outside-cluster real-part cap at `beta`;
- strict inequality `Re rho < beta` for real-ordinate nontrivial zeros;
- a sampling coefficient `0 < q < 1`;
- a uniform natural-point good-height selection.

No package height, smoothing window, energy positivity, or Carlson boundary
threshold is supplied externally.

## Construction

Stack98 chooses `T,L` and proves positive package energy together with
`outsideMass < q * sqrt(energy) / 2`. Stack95 then applies the natural
mean-square sign alternative, finite target-line capture, Carlson residual
control, and relative-to-unnormalized transfer.

## Output

The theorem returns all intermediate energy and boundary certificates,
fixed-rate relative PNT convergence, and one persistent sign for
`chebyshevPsi0(x) - x` at coefficient

`(q * sqrt(energy) - loss) / 2`

times `x^beta`. The coefficient is proved positive.

## Claim boundary

This is conditional on an attained global right-edge seed and real-ordinate
strictness. It proves `Omega+ OR Omega-`, not simultaneous `Omega+-`. It does
not assert existence of a rightmost zero, does not prove RH, and does not
replace the separate Sharp local pi/2 phase work.
