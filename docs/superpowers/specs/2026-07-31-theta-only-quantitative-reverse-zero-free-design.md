# Theta-Only Quantitative Reverse Zero-Free Design

## Goal

Complete the reverse direction with `theta` as the only numerical
zero-location input.

## Inputs

- `1 / 2 < theta < 1`;
- a global positive-zero real-part bound `rho.re <= theta`;
- `q < 1 / 2`;
- an eventual actual-error bound measured at the canonical target exponent
  selected from `theta`;
- a visible-cluster witness whenever the automatically selected right-edge
  cluster is nonempty.

## Automatic chain

Stack70 selects:

- the unique boundary target exponent;
- a canonical strict target exponent;
- the global density optimizer;
- a strip endpoint, strict loss, and outer height;
- the actual half-target-amplitude lower transfer.

If the enlarged right-edge cluster were nonempty, the lower transfer would
produce arbitrarily large half-amplitude witnesses. The eventual coefficient
`q < 1 / 2` excludes them, so the cluster is empty and the selected target
exponent is finite-height right-edge zero-free.

## Boundary

All numerical parameters are automatic. The visible-cluster anti-cancellation
witness remains explicit.
