# VK-edge Gaussian L2 and positive-measure design

## Goal

Upgrade the strict `pi / 2` epsilon-window oscillation theorem from a
single witness to two moment statements:

1. a Gaussian-kernel weighted second-moment lower bound for the normalized
   PNT error;
2. positive logarithmic Lebesgue measure of the set on which the same strict
   oscillation threshold is exceeded.

The result remains conditional on a zeta zero with real part greater than
`1 / 2`. It does not assert RH, an unconditional square-root bound, separate
`Omega+`/`Omega-` oscillation, or a uniform positive proportion.

## Natural weight

The contour identity pairs `normalizedPsiError rho` with
`centeredSharpenedProjectedPsiKernel`. The moment weight is therefore

```lean
|centeredSharpenedProjectedPsiKernel q rho k m y|
```

rather than the bare normalized Gaussian. This retains the finite-pole
annihilator and the missing-harmonic certificate. Calling the result
"Gaussian weighted" is accurate because the projected kernel is the fixed
polynomial-differential transform of the normalized Gaussian used by the
contour.

For a window `W_m = localizedGaussianLogWindow q d m`, define

```text
M1(m) = integral over W_m of |F(y)| * |K_m(y)|
M2(m) = integral over W_m of F(y)^2 * |K_m(y)|
```

where `F(y) = normalizedPsiError rho y`.

## Analytic inequality

Setwise weighted Cauchy-Schwarz gives

```text
M1(m)^2 <= M2(m) * integral over W_m of |K_m|
         <= M2(m) * coefficient(m).
```

The existing contour argument is strengthened before taking a supremum:

```text
signal(m) <= M1(m) + remainder(m).
```

Together with

```text
signal(m)     -> 2 * multiplicity,
coefficient(m)-> 2 * mean,
remainder(m)  -> 0,
```

this yields, for every

```text
C2 < 2 * multiplicity^2 / mean,
```

the eventual lower bound `C2 < M2(m)`.

## Positive measure

For any `C >= 0` with `C < multiplicity / mean`, eventually

```text
M2(m) > C^2 * coefficient(m).
```

If the set

```text
{y in W_m | C < |normalizedPsiError rho y|}
```

had measure zero, then almost everywhere on `W_m` the squared error would be
at most `C^2`, forcing the reverse inequality. Hence this set has positive
Lebesgue measure.

The final specialization uses the Carlson-selected missing odd harmonic and

```text
C = multiplicity * strictPiOverTwoOscillationConstant k.
```

The already proved strict inequality

```text
strictPiOverTwoOscillationConstant k
  < 1 / sharpenedMissingHarmonicDenominator k
```

supplies the threshold condition. Substitution of `epsilonGaussianScale`
turns `W_m` into

```text
[Real.log Y, (1 + epsilon) * Real.log Y].
```

The final theorem asserts positive measure in this logarithmic interval for
every sufficiently large `Y`.

## Code boundaries

- Add a reusable weighted set-integral Cauchy-Schwarz lemma under
  `MathlibAux`.
- Extend `CenteredLocalizedContourData` with the actual kernel, kernel mass,
  first-moment contour inequality, and second-moment integrability.
- Put generic moment extraction in a new focused
  `VKEdgePiOverTwoGaussianL2` module.
- Put null-set contradiction and the zeta specialization in a new focused
  `VKEdgePiOverTwoPositiveMeasure` module.
- Do not change the zero-density, zero-forced-oscillation, VK, or main
  worktrees.

## Verification

- Contracts pin definitions and theorem signatures before implementation.
- Axiom audits permit only Lean/Mathlib standard logical axioms.
- New source contains no `sorry`, `admit`, or project `axiom`.
- Run focused module builds, `./scripts/verify-baseline.sh`, and full
  `lake build`.

