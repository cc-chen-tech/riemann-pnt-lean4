# VK-edge Target-Pair Annihilator Design

## Goal

The previous residual-amplification branch proves that the existing swept
ordinary `L2` lower bound is smaller than one half of the local energy already
supplied by one selected zeta zero and its conjugate.  This branch therefore
does not try to improve the same lower bound by another constant factor.

Its goal is to construct a real-space detector which annihilates the selected
conjugate pair exactly, identify its action on every other frequency, and
isolate the precise arithmetic lower bound that would force nonzero residual
energy.  The branch must not claim another zero, a Carlson contradiction, or
RH unless that arithmetic lower bound is actually proved.

## Alternatives Considered

### 1. Raise the total second-moment coefficient above the pair budget

The selected pair has leading normalized energy `2 * m^2` per unit logarithmic
length.  The existing theorem gives less than `m^2` after the window scaling.
More importantly, the one-frequency model itself shows that an argument using
only the selected residue and generic Fourier inequalities cannot force a
coefficient larger than the complete pair budget.

This route is not used in this branch.

### 2. Iterate local zero clusters directly

The existing density-amplification branches prove a Carlson contradiction
from disjoint expanding zero layers.  They also contain finite counterexamples
showing that local degree alone does not imply growth: different parents can
share the same children, and an equal-ordinate cluster can stall a directed
iteration.

This route remains downstream.  It cannot start before one has a theorem
forcing a contribution outside the selected pair.

### 3. Annihilate the selected pair and test the residual

This is the selected route.  It directly targets the obstruction proved in the
parent branch and has an exact spectral interpretation.  It also has a clear
failure certificate: if no nonzero arithmetic lower bound survives after
annihilation, the branch records that fact rather than turning a conditional
interface into a zero-existence claim.

## Core Detector

For a real function `F`, step `h`, and selected frequency `gamma`, define

```text
D_(h,gamma) F(y)
  = F(y+h) - 2 cos(gamma h) F(y) + F(y-h).
```

For the existing cosine package

```text
P_(m,lambda,phase)(y) = -2 m cos(lambda y - phase),
```

the detector satisfies the exact multiplier identity

```text
D_(h,gamma) P_(m,lambda,phase)(y)
  = 2 (cos(lambda h) - cos(gamma h))
      P_(m,lambda,phase)(y).
```

Consequently the selected pair `lambda = gamma` is annihilated pointwise.
Other frequencies remain visible unless their cosine multipliers collide.
The collision condition is recorded explicitly; no frequency-separation
claim is inferred from distinct ordinates alone.

## Zeta Specialization

For a zeta zero `rho = beta + i gamma`, define

```text
annihilatedNormalizedPsiError rho h
  = D_(h,gamma) (normalizedPsiError rho).
```

Because

```text
normalizedPsiError rho
  = normalizedTargetZeroPair rho + normalizedPsiResidual rho,
```

the selected-pair annihilation gives the exact identity

```text
annihilatedNormalizedPsiError rho h
  = D_(h,gamma) (normalizedPsiResidual rho).
```

The same function is expanded into a three-scale classical-prime expression:

```text
norm rho * exp (-beta y) *
  ( exp (-beta h) * E(exp (y+h))
    - 2 cos(gamma h) * E(exp y)
    + exp (beta h) * E(exp (y-h)) ),
```

where `E(x) = chebyshevPsi x - x`.

This formula names the genuine new arithmetic input.  A lower bound for this
three-scale correlation cannot be replaced by the already proved lower bound
for `normalizedPsiError`.

## Local `L2` Gate

The branch proves a reusable local transfer theorem.  On an inner interval,
the square of the detector is bounded by the residual energy on the interval
expanded by `|h|`.  A coarse explicit constant is acceptable at this stage;
the theorem must be unconditional and its interval inclusions explicit.

The resulting implication has the form

```text
integral_inner (D residual)^2 >= C * length
------------------------------------------------
integral_outer residual^2 >= c * C * length,
```

for an explicit numerical `c > 0`.

This is a conditional residual-energy bridge.  The difficult premise is a
lower bound for the true three-scale prime correlation.

## No-go Certificates

The branch proves two boundaries.

1. The detector is identically zero on the pure selected-pair model.  Hence no
   positive detector lower bound follows from the selected zero alone.
2. Distinct frequencies need not be visible for a fixed `h`, because
   `cos(lambda h) = cos(gamma h)` can occur.  Any later zero-counting theorem
   must either choose `h` away from finitely many collision sets or average
   over `h`.

These are theorem-level obstructions, not informal warnings.

## Connection to Carlson

The existing iterative Carlson adapter is reused only after two new facts are
available:

1. a positive detector lower bound for the real prime error;
2. a spectral converse turning that residual signal into a distinct,
   deduplicated zero contribution.

This branch targets the first interface and the exact detector algebra.  It
does not duplicate the already formalized layer-counting or Carlson
combinatorics.

## Files

- `PrimeNumberTheorem/VKEdgeTargetPairAnnihilator.lean`
- `Test/VKEdgeTargetPairAnnihilatorContract.lean`
- `Test/VKEdgeTargetPairAnnihilatorAxiomAudit.lean`
- `docs/research/vk-edge-target-pair-annihilator-audit.md`
- `lakefile.lean`

## Verification

- Focused source and contract builds.
- `#print axioms` for every public endpoint; only standard Lean/Mathlib
  logical axioms are allowed.
- No `sorry`, `admit`, project `axiom`, or theorem-shaped placeholder.
- `git diff --check`.
- Repository baseline and serialized complete build before publication.

## Claim Boundary

Success for this branch means exact target-pair annihilation, exact
other-frequency multipliers, the true three-scale `psi` formula, and a
verified local residual-energy transfer.

It does not by itself prove positive residual energy, an additional zeta zero,
a zero-density contradiction, or the Riemann hypothesis.
