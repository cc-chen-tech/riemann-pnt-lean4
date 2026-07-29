# Finite Zero Cluster Explicit-Formula L2 Design

## Goal

Connect the finite zero-cluster local second-moment theorem to the actual
multiplicity-aware zeta explicit formula for the standard Chebyshev function
`psi`.

The endpoint must use:

- an actual sub-finset of `nontrivialZerosFinset T`;
- analytic multiplicity `analyticOrderNatAt riemannZeta`;
- the actual complementary zero sum;
- the proved finite-height explicit-formula approximation error;
- the closed-form terms and the midpoint jump correction.

It must not replace these objects by an abstract residual or a cosine model.

## Exact decomposition

For `S` contained in the height-`T` nontrivial-zero finset, define the
unselected zero contribution using `nontrivialZerosFinset T \ S`. Define the
standard-`psi` remainder by adding:

1. the unselected zero contribution;
2. `explicitFormulaApproxWithMultiplicity - chebyshevPsi0`;
3. `zeroPackageClosedTerms`;
4. the negative midpoint jump correction.

After multiplying by `exp (-beta * y)`, prove the pointwise identity

```text
normalized standard psi error
  = - normalized selected zero cluster - normalized actual remainder.
```

## L2 transfer

Use the pointwise inequality

```text
(1/2) * ||P||^2 - ||R||^2 <= ||P + R||^2
```

and interval integrability of the three actual functions. Combining it with
the local-separation theorem from PR #30 gives

```text
one half of the finite-cluster energy lower bound
  - actual remainder second moment
  <= standard psi-error second moment.
```

The strict endpoint requires the displayed lower budget to dominate the
actual remainder second moment.

## Claim boundary

This stage proves an exact finite-height explicit-formula bridge. It does not
bound the complementary zero sum or the truncation error strongly enough to
obtain an unconditional positive lower bound. It does not prove a
zero-density contradiction or RH.
