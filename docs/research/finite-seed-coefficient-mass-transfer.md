# Finite-seed coefficient-mass transfer

## Auditable theorem chain

The actual-PNT finite-seed transfer now has the following explicit chain.

1. The balanced Carlson selector chooses one fixed `sigma`, a dynamic height,
   and a finite conjugation-stable extension `S` of the prescribed seed `S₀`.
2. The same certificate gives relative PNT decay, a strict real-part gap away
   from `S`, and a small outside-boundary mass.
3. Boundary support plus the seed's zeta-zero real-part cap proves
   `Re rho <= beta` for every `rho` in `S \ S₀`.
4. The exact finite mass
   `sum rho in S \ S₀, analyticOrderNatAt zeta rho / norm rho`
   bounds the visible added-cluster main term on the scale
   `x^(beta - 1)`.
5. A seed oscillation coefficient `c` and the numerical condition
   `finiteVisibleClusterCoefficientMass (S \ S₀) < loss` transfer to an
   actual unnormalized PNT witness with coefficient `(c - loss) / 2`.

Unsigned and signed versions use the same added-cluster mass budget.

## Remaining mathematical condition

The coefficient-mass inequality is not automatic.  Carlson boundary capture
reduces the mass outside `S` by adjoining boundary zeros to `S`, but those
adjoined zeros contribute to `finiteVisibleClusterCoefficientMass (S \ S₀)`.
Thus aggressive boundary capture can improve the complementary-zero estimate
while worsening the seed-perturbation estimate.

The current theorem exposes this finite allocation tradeoff instead of hiding
it in a functional eventual hypothesis.  It does not prove that a suitable
allocation always exists, does not formalize a zero-reproduction argument, and
does not imply RH or an unconditional Omega theorem.
