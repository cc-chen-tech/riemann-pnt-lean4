# Zero-supported transfer to the actual PNT error

The finite-seed Carlson lower transfer now uses the strengthened selector and
returns an explicit certificate that every member of `S \ S0` is a
nontrivial zeta zero.

The theorem chain is:

1. select a finite, conjugation-stable, zero-supported extension;
2. use the Carlson boundary gap to obtain a positive net cluster constant;
3. transfer a visible-cluster natural-point witness to the relative
   `psi0` error;
4. pass from natural points to real points;
5. remove the normalization to obtain a witness for
   `chebyshevPsi0Error`.

Unsigned and signed variants are provided. Their visible-main oscillation
witnesses remain hypotheses, so these declarations do not assert an
unconditional Omega or Omega-plus-minus theorem.
