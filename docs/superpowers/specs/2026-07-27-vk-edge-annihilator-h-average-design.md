# VK-edge Annihilator Step-Average Design

## Goal

This branch determines exactly what averaging the target-pair annihilator over
its step parameter can and cannot prove.

For a selected positive frequency `gamma`, the parent branch defines

```text
D_(h,gamma) F(y)
  = F(y+h) - 2 cos(gamma h) F(y) + F(y-h).
```

It annihilates the selected conjugate cosine pair pointwise.  A fixed step can
also annihilate a different frequency by accident.  The present branch removes
that fixed-step collision by averaging over `h`, then states the honest zeta
dichotomy exposed by the resulting spectral formula.

The branch must not assert that one off-critical-line zero forces positive
annihilated energy.  If the selected pair is the unique rightmost pair and the
remaining spectrum has a fixed real-part gap, the normalized annihilated
signal may decay to zero.

## Alternatives

### One fixed step

This is already implemented in the parent branch.  It is unsuitable as the
next endpoint because distinct frequencies can satisfy

```text
cos(lambda h) = cos(gamma h).
```

No uniform spectral converse follows from one arbitrary step.

### A finite set of steps

A finite step set can distinguish a fixed finite frequency package.  Its
constant depends on the package and can degenerate when frequencies approach
one another.  This remains useful as a later effective specialization, but it
does not give the clean structural theorem needed first.

### Average over a step interval

This is the selected route.  For

```text
M_(lambda,gamma)(h)
  = 2 * (cos(lambda h) - cos(gamma h)),
```

the normalized mean square satisfies

```text
(1 / H) * integral_[0,H] M_(lambda,gamma)(h)^2 dh -> 4
```

for distinct positive frequencies `lambda` and `gamma`.  The target frequency
has multiplier identically zero.  Thus step averaging separates every fixed
non-target frequency without choosing an exceptional step in advance.

## Abstract Spectral Layer

The first module introduces the real multiplier

```text
frequencyAnnihilatorMultiplier h gamma lambda
  = 2 * (cos(lambda h) - cos(gamma h)).
```

It proves:

1. an exact finite-`H` integral formula for the square;
2. the target identity at `lambda = gamma`;
3. convergence of the normalized integral to `4` when
   `0 < gamma`, `0 < lambda`, and `lambda != gamma`;
4. eventual lower bounds such as

   ```text
   2 <= (1 / H) * integral_[0,H] multiplier(h)^2 dh;
   ```

5. a finite-frequency simultaneous version obtained by taking the maximum of
   finitely many thresholds.

The finite-`H` theorem must expose all denominators explicitly.  No hidden
frequency-separation constant is introduced.

## Finite Package Energy

For a finite real cosine package with distinct positive frequencies, combine:

- the exact action of the annihilator on each frequency;
- step averaging in `h`;
- long-window mean-square orthogonality in `y`.

The endpoint is conditional only on the package containing a nonzero
coefficient at a frequency different from `gamma`.  It proves that the
two-parameter average

```text
integral_h integral_y |D_(h,gamma) package(y)|^2
```

has a positive asymptotic density.  Repeated frequencies must be collected
before applying the theorem, so cancellation at equal frequencies is handled
in the coefficient rather than hidden in the proof.

The first implementation may expose the abstract orthogonality hypotheses if
the repository's existing finite exponential-polynomial mean-square theorem
does not match the required real-cosine normalization.  It must not duplicate
the existing general mean-square library.

## Zeta Dichotomy

Let `rho = beta + i gamma` be a selected zeta zero.  The parent branch proves

```text
annihilatedNormalizedPsiError rho h
  = D_(h,gamma) (normalizedPsiResidual rho).
```

The new zeta-facing statements are deliberately split.

### Same-edge residual package

Under an explicit finite-package hypothesis saying that the normalized
residual contains a nonzero zero contribution with:

```text
real part = beta
positive ordinate lambda != gamma,
```

the step-averaged annihilator has positive local mean-square density.  This is
the valid spectral converse for a known same-edge package.

### Real-part gap

Under a complementary hypothesis saying that every remaining zero
contribution has real part at most `beta - delta`, with `delta > 0`, and that
the truncated explicit-formula remainder obeys the existing uniform bound, the
annihilated normalized signal is allowed to decay at the corresponding
exponential scale.

The initial theorem may be stated for the repository's finite truncated zero
package.  Extending it to the complete explicit formula requires a separately
audited uniform tail limit.

### Honest conclusion

The combined mathematical boundary is:

```text
positive non-decaying annihilator energy
  -> a same-edge or arbitrarily near-edge residual contribution,
```

not:

```text
one off-line zero -> another equally far-right zero.
```

Proving that every off-line zero has such a companion would be an additional
new theorem and is not assumed in this branch.

## Interfaces and Files

Planned files:

- `PrimeNumberTheorem/VKEdgeTargetPairAnnihilatorAverage.lean`
- `Test/VKEdgeTargetPairAnnihilatorAverageContract.lean`
- `Test/VKEdgeTargetPairAnnihilatorAverageAxiomAudit.lean`
- `docs/research/vk-edge-target-pair-annihilator-average-audit.md`
- `lakefile.lean`

The module imports the parent annihilator API and existing finite-frequency
mean-square infrastructure.  It does not modify:

- `PrimeNumberTheorem/VKEdgeTargetPairAnnihilator.lean`;
- the residual-amplification parent;
- Carlson density iteration;
- zero-layer deduplication;
- Vinogradov--Korobov public cores.

## Contract-First Implementation

Each public endpoint is added to the contract before implementation, and the
expected missing-declaration failure is recorded.

The contract covers:

- the multiplier definition;
- exact finite-interval square integral;
- target annihilation;
- normalized mean-square limit;
- eventual positive lower bound for a non-target frequency;
- finite-family simultaneous separation;
- finite-package averaged-energy endpoint;
- the conditional zeta same-edge bridge;
- the finite-gap decay/no-go endpoint that can be supported by existing
  explicit-formula estimates.

If the zeta bridge requires a hypothesis equivalent to its conclusion, it is
rejected rather than published as a route interface.

## Verification

Before publication:

- focused source and contract builds;
- `#print axioms` for every public theorem;
- only `propext`, `Classical.choice`, and `Quot.sound` are allowed;
- no `sorry`, `admit`, project `axiom`, or theorem-shaped placeholder;
- `git diff --check`;
- repository baseline verification;
- serialized complete `lake build`;
- branch scope checked against parent commit `1c363dc`.

## Success and Failure Criteria

This branch succeeds if it proves the exact step-average spectral separation
and an honest conditional zeta dichotomy without overstating zero creation.

It counts as a stronger mathematical advance only if an unconditional
arithmetic input is found that rules out the isolated-rightmost-pair case.

The branch stops and records a no-go result if:

- the proposed positive zeta lower bound uses only the selected pair;
- a finite-package lower bound loses positivity when equal frequencies are
  correctly collected;
- the full zeta statement needs an unaudited infinite-tail interchange;
- the claimed Carlson contradiction assumes the additional zero layer it is
  meant to prove.

It does not claim:

- an additional zeta zero;
- positive annihilated energy from one zero alone;
- a Carlson contradiction;
- the Riemann hypothesis.
