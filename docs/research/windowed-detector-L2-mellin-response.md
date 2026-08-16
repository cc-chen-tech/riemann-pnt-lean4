# L2 windowed Mellin response: paper specification

## Status

Paper specification for lemma L2 of `windowed-detector-lean-spec.md`.
Companion to the L1 drafts (`lean-drafts/`).  No theorem claims; this
pins the response identity and the per-term estimates that a Lean L2
module must prove.

## Objects

Fix the cubic smoothing scale `h = X^(-d)` and the centered cubic kernel
(from `2026-08-10-direct-l2-carlson-explicit-formula-design.md` section 7)

```text
C_h(s) = (exp(h s) - 2 + exp(-h s)) / (h^2 s^2),
|C_h(s)| <= K * min(1, (h |s|)^(-2)),
```

the detection frequency `gamma`, and the window `[X, X^lambda]`.
Define the windowed Mellin response of the centered second difference

```text
R(gamma)
  := integral from X to X^lambda of
       (F''_h(x)) * x^(-1 - i gamma) dx,
```

where `F''_h` is the centered second difference of the Riesz/triangle mean
used by the cubic explicit formula (the `C_h` kernel is its Mellin
multiplier), or equivalently the truncated zero sum with weight `C_h`.

## Identity (the L2 target)

```text
R(gamma)
  = sum over nontrivial zeros |Im rho| <= T of
      m(rho) * C_h(rho) * I(rho, gamma)
    + Err(X, lambda, T, h, gamma),

I(rho, gamma) := integral from X to X^lambda of x^(rho - 1 - i gamma) dx
               = (X^(lambda (rho - i gamma)) - X^(rho - i gamma)) / (rho - i gamma)
```

with `T = X^alpha` the truncation height and an error envelope bounded by
the existing truncated explicit-formula remainder
(`ExplicitFormulaAllHeights` / `ExplicitFormulaResidues` lines, the same
inputs already consumed by `HalfIsolatedSimplifiedDetectorInput`).

Lean shape: the identity is the integral of the proved truncated explicit
formula against `x^(-1 - i gamma)`; finite-sum/integral exchange is
`intervalIntegral.integral_finset_sum`.  No new contour theory.

## Per-term estimates

### Seed term (aligned, gamma = Im rho_0, Re rho_0 = beta, |rho_0| ~ T0 = X^(gamma0))

```text
I(rho_0, Im rho_0) = (X^(lambda beta) - X^beta) / beta
                   ~  X^(lambda beta) / beta   (lambda > 1, X large).
```

The kernel factor is `C_h(rho_0) ~ (h |rho_0|)^(-2) = X^(-2 (gamma0 - d))`
when `gamma0 > d` (top-layer seed), or tends to 1 for a fixed-height
target.  In either case the factor is present on BOTH sides of the L3
comparison below, so it cancels.

### Complementary term (Re rho <= beta - gap)

```text
|m(rho) C_h(rho) I(rho, gamma)|
  <= m(rho) * K * min(1, (h |rho|)^(-2)) * 2 X^(lambda (beta - gap)) / |gamma - Im rho|.
```

At top-layer heights `|rho| ~ T0 = X^(gamma0)` with `gamma0 > d` the
kernel factor is `K (h |rho|)^(-2) = K X^(-2 (gamma0 - d))`, so the
complementary weighted contribution is bounded by

```text
x^(lambda (beta - gap) - 2 (gamma0 - d)) * (K / T0) * sum 1 / |gamma - Im rho|
```

plus the below-`X^d` low part, which is handled by the global reciprocal
mass (`exists_globalReciprocalZeroMultiplicity_le_log_sq`).

### Ratio (the L3 seed-vs-complementary comparison)

The kernel factor `X^(-2 (gamma0 - d))` appears on both sides and cancels;
the comparison reduces to

```text
X^(lambda gap) / (lam * log X)  >  C * (1 + log T1)^2 * T1 / (T0 * H) * (T0 / X^(lambda gap)) ...
```

i.e., with `T1 = T0 + H = X^(gamma0) (1 + X^(h - gamma0))` and
`H = T0^? = X^(gamma0 h')` the same exponent shape as in the L1
feasibility check:

```text
gap > (1 - h') * gamma0   (to leading order).
```

Conclusion: L2's kernel factor does not change the L3 threshold; the L1
revised bound remains the operative input.

## Parameter coordination (to be fixed in the Lean signature)

- `gamma0` (seed height exponent), `d` (smoothing exponent), `alpha`
  (truncation exponent) must satisfy `gamma0 > d` and `alpha > d`
  (so `h T -> infinity`), `lambda > 1`, and `H = X^(gamma0 h')` with
  `h' in (0,1)`.
- The L1 statement uses `H <= T0`; together with `H = X^(gamma0 h')` this
  forces `h' <= 1`, consistent with the L3 condition `gap > (1 - h') gamma0`.
- The error envelope `Err` must be smaller than the seed term: the cubic
  design's `X^(-1/20)` tail margin
  (`lambda (1 - beta) + 2 d - 2 alpha = -(3 + g)/4 < 0`) is the intended
  budget; the L2 Lean statement should expose `Err <= C X^(lambda beta - eps)`
  with `eps = 1/20` as its explicit hypothesis.

## Open items

1. Exact form of the centered second-difference signal whose Mellin
   multiplier is `C_h` (the `ZeroForcingUnifiedTransfer` / cubic explicit
   formula modules own this; L2 must import it read-only).
   RESOLVED (2026-08-15, worktree `actual-cubic-two-height-l2-tail`):
   - `ZeroDensityLayerBudgetCubicKernelFactorization`:
     `cubicZeroResidueSecondDifference_div_sq_eq_simple_mul_multiplier`,
     `norm_cubicSimpleZeroKernel_eq`,
     `norm_cubicZeroResidueSecondDifference_div_sq_eq`,
     `cubicPoleOneSecondDifference_div_sq_eq`;
   - `ZeroDensityLayerBudgetCubicKernelNearOne`:
     `norm_cubicKernelMultiplier_sub_one_le_three_mul` (the `C_h -> 1`
     near-one estimate);
   - `ZeroDensityLayerBudgetActualDesmoothedContourEdgeBudget`:
     `norm_desmoothedCubicContourIntegrand_le` (contour integrand bound).
2. Whether to state the identity for the raw `psi` oscillation times
   `x^(-1-i gamma)` (simpler) or the smoothed `F''_h` version (matches the
   cubic budget); the draft recommends the smoothed version.
3. The low part (heights below `X^d`) estimate: reuse
   `exists_globalReciprocalZeroMultiplicity_le_log_sq` with the
   `|gamma - Im rho| >= X^(gamma0)/2` separation.

## Boundaries

Specification only.  Lean work starts after the L1 promotion (see
`L1-formalization-checklist.md`).
