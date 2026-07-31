# Seed-Witness Half-Threshold Sign-Alternative PNT Transfer

## Objective

Connect the persistent-sign disjunction from stack92 to the actual relative
Chebyshev error without requiring both signed seed witnesses.

## Design

Split the existing automatic Carlson-boundary signed transfer into positive
and negative one-sided declarations. Both reuse the same eventual residual
bound and the existing one-sided `transfer_eventually_sub_lt` lemmas.

Build one common target-line capture certificate before eliminating the seed
sign disjunction. In the positive branch, extend only the positive seed
witness and invoke the positive transfer. In the negative branch, do the
corresponding negative construction. The output preserves the canonical
half-threshold coefficient `(c - loss) / 2`, the target amplitude
`x^(beta - 1)`, and fixed-rate relative PNT convergence.

Finally, accept an unsigned far seed witness and obtain the required sign
disjunction using stack92's `signAlternative` theorem.

## Claim boundary

The result proves a conditional `Omega+ OR Omega-` alternative. It does not
prove both signs, simultaneous `Omega+-`, RH, or any new phase recurrence.
The local pi/2 oscillation work and VK-edge modules remain outside scope.

## Audit

The focused contract checks all four public declarations. The axiom audit
prints their dependencies and is expected to remain within the repository's
standard logical allowlist.
