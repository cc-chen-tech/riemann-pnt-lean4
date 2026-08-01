# VK Edge Sharp Left-Gap Stability Design

## Goal

Prove that the genuine cofinal low-height zeta energy from
`VKEdgeSharpLowHeightEnergy` survives deleting any fixed finite set of
nontrivial zeros whose real parts lie a fixed positive distance to the left of
the target exponent `beta`.

## Mathematical statement

For `delta > 0`, a finite set `S`, and

```lean
forall rho in S, rho.re <= beta - delta,
```

the selected normalized zero package satisfies, for `y >= a >= 0`,

```text
||selected_S(beta, y)||
  <= exp (-delta * a) * sum_{rho in S} m(rho) / ||rho||.
```

Consequently its forward Gaussian second moment tends to zero as `a -> infinity`.
Once the selected zeros are all present below the genuine detector height
`Tlow`, the exact finite-sum decomposition is

```text
complement_empty = selected_S + complement_S.
```

The elementary inequality

```text
||u||^2 <= 2 * ||u - v||^2 + 2 * ||v||^2
```

then transfers the existing positive `S = empty` lower bound to the complement
after deleting `S`. The retained lower-bound constant is fixed independently
of `S`; only the eventual threshold depends on the finite mass and gap of `S`.

## Scope boundary

- The finite sums are the actual zeta zeros with multiplicity
  `analyticOrderNatAt riemannZeta`.
- The detector height remains `Tlow ~ exp (gammaLow * log Y)` and the outer
  height remains `exp (alpha * log Y)`.
- The endpoint keeps the existing assumptions `rho.re > 2/3` and the joint
  two-height parameter inequalities.
- This result does not delete the target zero pair or any zero on the same
  maximal real-part layer. It therefore does not provide arbitrary-`S`
  repeatability, a Carlson contradiction, or RH.
- No Gate B witness extraction, finite-set growth, Carlson upper bound, or
  Gram/Schur theorem is implemented here.

## Modules

`PrimeNumberTheorem/VKEdgeSharpLeftGapDecay.lean` owns the finite-package
norm bound, Gaussian energy bound, eventual height containment, exact
complement decomposition, and fixed-height deletion stability.

`PrimeNumberTheorem/VKEdgeSharpLeftGapStability.lean` composes those lemmas
with the genuine low-height `S = empty` theorem and exposes the cofinal
`beta > 2/3` endpoint.

Contracts and axiom audits lock every public theorem's exact type. The central
multiplicity audit and allowlist are updated only after focused verification.

## Acceptance

The final theorem must display the literal Gaussian integral of
`normalizedFiniteZeroClusterComplementContribution S Tlow ...`, retain a
strict positive constant independent of `S`, quantify genuine good heights,
and preserve the separate `gammaLow` and `alpha` bounds. New source must contain
no `sorry`, `admit`, or project `axiom`.
