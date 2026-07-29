# VK-Edge Fixed-Proportion Large Values Design

## Goal

Upgrade the conditional ordinary local second-moment lower bound from PR #23
to a quantitative fixed-proportion large-value theorem. The theorem must keep
the fourth-moment input explicit: the repository does not yet prove a matching
fourth-moment bound for the true normalized prime-counting error.

## Mathematical statement

Write

```text
I(Y, epsilon) = [log Y, (1 + epsilon) log Y]
F_rho(y) = normalizedPsiError rho y.
```

PR #23 proves that a hypothetical zeta zero `rho`, with
`1 / 2 < re rho < 1`, supplies a missing odd harmonic `k` and an explicit
constant

```text
c2 = centeredSharpenedSweptOrdinaryL2Constant epsilon rho k > 0
```

such that eventually

```text
c2 * log Y < integral over I(Y, epsilon) of F_rho(y)^2.
```

Assume in addition that a constant `C4 > 0` satisfies, eventually,

```text
IntegrableOn (fun y => F_rho(y)^4) I(Y, epsilon)
integral over I(Y, epsilon) of F_rho(y)^4 <= C4 * log Y.
```

For `0 <= theta < 1`, Paley--Zygmund then gives

```text
measure {
  y in I(Y, epsilon) |
  theta * c2 / epsilon < F_rho(y)^2
}
>
((1 - theta)^2 * c2^2 / C4) * log Y.
```

Since `measure I(Y, epsilon) = epsilon * log Y` for `Y > 1`, this is the
fixed proportion

```text
eta = (1 - theta)^2 * c2^2 / (C4 * epsilon).
```

The main endpoint will specialize to `theta = 1 / 2`, yielding the clean
threshold `c2 / (2 * epsilon)` and proportion
`c2^2 / (4 * C4 * epsilon)`.

## Architecture

### Generic quantitative transfer

Create `MathlibAux/ScaledPaleyZygmund.lean`. It will reuse
`MathlibAux.paleyZygmund_mul_secondMoment_le_measure` and prove a theorem for
an arbitrary finite-measure set `s` whose measure is `epsilon * L`.

Inputs:

- measurability of `s` and `g`;
- `epsilon > 0`, `L > 0`, `c2 > 0`, `C4 > 0`;
- integrability of `g^4` on `s`;
- `c2 * L < integral_s g^2`;
- `integral_s g^4 <= C4 * L`;
- `0 <= theta < 1`.

Output:

```text
((1 - theta)^2 * c2^2 / C4) * L
  <
measure {x in s | theta * c2 / epsilon < g x ^ 2}.
```

This theorem contains no zeta-specific definitions and can be reused by the
Hardy--Littlewood and zero-density developments.

### Zeta endpoint

Create `PrimeNumberTheorem/VKEdgePiOverTwoFixedProportion.lean`. It imports
the swept local L2 endpoint and the generic scaled Paley--Zygmund theorem.

The public endpoint takes a genuine eventual fourth-moment hypothesis for
`normalizedPsiError rho`. It invokes the existing Carlson missing-harmonic
selection through the PR #23 endpoint, then applies the generic transfer on
`I(Y, epsilon)`.

The endpoint returns:

- the selected harmonic `k`;
- its nonvanishing zeta condition;
- positivity of the explicit second-moment constant;
- an eventual fixed-proportion measure inequality.

No new `def ... : Prop` target is introduced.

## Alternatives rejected

### Finite exponential-polynomial fourth moments

`MathlibAux.ExponentialPolynomialFourthMoment` controls a finite frequency
sum. The true `normalizedPsiError` also contains the complementary zero sum
and contour remainder. Passing from a finite sum to the true error in fourth
moment requires exactly the missing remainder estimate. Applying the finite
sum theorem alone would hide rather than solve that gap.

### Crude pointwise bounds

The unconditional pointwise estimate currently available grows like
`exp ((1 - re rho) * y)` after normalization. Combining it with the L2 lower
bound gives a measure lower bound whose proportion decays exponentially with
`Y`. It is not a fixed-proportion theorem and cannot create an RH
contradiction.

## Contradiction boundary

This milestone does not prove the required `O(log Y)` fourth moment. It proves
that such an estimate would force a fixed positive fraction of every late
epsilon window to contain error of scale `exp (re rho * y) / norm rho`.

Even that fixed-proportion conclusion does not by itself contradict Carlson
zero density, because it counts large error locations rather than distinct
zeta zeros. A later contradiction still requires one of:

1. an unconditional upper bound incompatible with the large-value proportion;
2. an injective construction turning separated large-value windows into too
   many distinct zeros;
3. a zero-density-weighted explicit formula upper bound on the same local
   fourth moment.

Only a contradiction excluding every zero with real part greater than
`1 / 2`, followed by functional-equation symmetry, would prove RH.

## Verification

- A contract checks the generic transfer and the zeta endpoint signatures.
- An axiom audit checks both public theorems.
- New source contains no `sorry`, `admit`, or project `axiom`.
- Run focused builds, `./scripts/verify-baseline.sh`, and `git diff --check`.
- Open a dependent draft PR against `research/vk-edge-swept-l2`.
