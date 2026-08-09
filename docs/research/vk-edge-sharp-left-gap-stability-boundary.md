# Sharp left-gap stability boundary

## Proved in this branch

Let `rho` be a genuine nontrivial zeta zero with `rho.re > 2/3`, and let `S`
be a fixed finite family of genuine nontrivial zeta zeros. If there is a fixed
`delta > 0` such that

```text
z.re <= rho.re - delta  for every z in S,
```

then the genuine low-height Gaussian energy from the `S = empty` Sharp theorem
survives deleting `S`. More precisely, for cofinally large `Y` there is a true
good detector height

```text
Tlow in [exp (gammaLow * log Y), exp (gammaLow * log Y) + 1]
```

which remains below the independent outer height `exp (alpha * log Y)`, and

```text
initialEmptyClusterFullMovingGaussianL2Constant eps rho k / 4
  < integral over [0, eps * log Y]
      normalizedGaussian ((eps * log Y)^2) t
        * ||normalizedFiniteZeroClusterComplementContribution
              S Tlow rho.re (log Y + t)||^2.
```

The finite set `S` and the gap `delta` affect the eventual starting point but
not the retained factor `1/4`.

## Why the proof works

Each deleted zero contributes after normalization at exponent `beta` at most
its reciprocal-norm multiplicity times `exp (-delta * a)`. A fixed finite sum
therefore has Gaussian second moment tending to zero. The exact true-zeta
finite-sum identity

```text
complement(empty) = selected(S) + complement(S)
```

and the elementary `2-2` square inequality retain one quarter of the original
energy once the selected package is sufficiently small.

## Exact remaining blocker

This theorem does not apply when `S` contains the target zero, its conjugate,
or any other zero with real part equal to `rho.re`. In that case no positive
`delta` exists and the selected package need not decay after normalization.
The existing `rightHigherExclusionSet` deliberately deletes the anchor pair
once `Told >= rho.im`, so this branch does not yet supply the arbitrary-`S`
repeatable input needed by Gate B.

A true continuation must obtain new energy on the same maximal real-part layer
or prove that another higher/right zero exists. Replacing that missing analytic
input by an abstract lower-bound hypothesis would only rename the blocker.

## Claim boundary

This is a genuine zeta finite-zero theorem, not a cosine model. It proves no
Carlson contradiction, zero-free theorem, or instance of RH. It isolates the
same-layer deletion problem by proving that every strictly-left fixed finite
deletion is asymptotically harmless.
