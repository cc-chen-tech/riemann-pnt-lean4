# Automatic actual-grid dyadic Carlson full-PNT package

## Goal

Place the existing balanced dyadic Carlson closed-form PNT theorem on the same
actual singleton-grid height interface introduced by Stacks 130 and 131.

## Construction

If the existing Carlson theorem supplies the balanced parameter `b`, construct
the automatic grid with

`theta = 1 / 2`, `parentB = 2 * b`.

Then `theta * parentB = b`, so the grid rate is exactly
`classicalAdmissibleBalancedRate b`, and Stack 131 identifies its actual
candidate with `selectedClassicalAdmissibleGoodHeight b` eventually.

## Output package

The theorem returns:

- the original dyadic gap and verified decay-rate identities;
- the actual grid rates, base rate, and selector identities;
- the dynamic zero-free predicate on the actual grid candidate;
- the existing closed-form Carlson majorant and its convergence to zero;
- eventual domination of the real relative `psi0` error.

## Claim boundary

This theorem transports the existing Carlson result; it does not improve its
constants. It does not prove target-amplitude negligibility, an Omega theorem,
or RH.
