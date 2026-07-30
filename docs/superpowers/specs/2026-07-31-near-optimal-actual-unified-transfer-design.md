# Near-optimal actual unified transfer design

## Goal

Run the actual automatic-good-height Pintz-Carlson-explicit-formula transfer
at the proven near-optimal truncation exponent.

## Inputs

- `2 / 3 < beta < 1`;
- `1 / 2 < sigma < 1`;
- a prescribed global positive-zero real-part cap `theta`;
- `0 < eta < C_theta - (1 - beta)`;
- a conjugation-invariant base cluster;
- a global bound `rho.re <= theta` for positive-imaginary nontrivial zeros.

## Construction

Stack54 supplies:

- `alpha = C_theta - eta`;
- an endpoint `sigma < tau` and `theta < tau < beta`;
- balanced low and Carlson cuts;
- positive epsilons and all strict margins.

The global zero bound closes the selected-height strip cap. Adjoining fixed
real-ordinate zeros closes the real-axis residual. The automatic good-height
remainder theorem then applies at exactly the near-optimal `alpha`.

## Result

For every supplied natural-point visible-cluster witness, the theorem returns:

- fixed-rate natural-point relative PNT convergence;
- a half-target-amplitude far witness for the actual relative Chebyshev error.

The sharp visible-cluster witness remains explicit.

