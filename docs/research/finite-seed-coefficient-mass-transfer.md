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

## Indexed boundary allocation

At the Carlson positive-zero index level there is now an exact identity

`total boundary mass = captured boundary mass + outside boundary mass`.

Consequently, strict captured and outside allowances imply the same summed
allowance for the total boundary layer.  This is the precise budget
obstruction behind finite capture.  The captured term is intentionally kept
as an indexed sum: identifying it with the finite distinct-zero coefficient
mass requires a separate uniqueness and counting argument.

The first uniqueness step is now isolated: dyadic ordinate shells are
pairwise disjoint, the base interval is disjoint from every dyadic shell, and
the combined map from Carlson positive-zero indices to complex zeros is
injective.  The indexed weight is also identified with the exact
analytic-multiplicity coefficient of its represented zero.

With uniqueness available, the indexed captured mass is bounded by the full
finite distinct-zero coefficient mass.  For every seed inclusion `S₀ ⊆ S`,
the exact relative allocation is

`captured boundary mass of (S \ S₀) + outside mass of S
  = outside mass of S₀`.

Hence extension mass below `addedAllowance` and final outside mass below
`outsideAllowance` force the seed's original outside mass below their sum.
This is a necessary quantitative compatibility condition for the
coefficient-mass actual-PNT transfer.
