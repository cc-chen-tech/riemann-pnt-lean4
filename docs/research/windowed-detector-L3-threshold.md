# L3 threshold comparison: paper specification

## Status

Paper specification for lemma L3 of `windowed-detector-lean-spec.md`.
Companion to the L1 drafts and the L2 specification.  No theorem claims.

## The gap L2 left open

L2's complementary estimate covers zeros with `Re rho <= beta - gap`.
Top-layer zeros with `Re rho = beta` and `Im rho` OUTSIDE the window
`[T0, T0+H]` are NOT gap-suppressed: their contribution to the response
carries the full `X^(lambda beta)` scale.  L3 must handle them by the
eta-avoidance separation, not by the real-part gap.  This is the new
content of this specification.

## Setup

- Window `[T0, T0+H]`, `H = X^(gamma0 h')`, `T0 = X^gamma0`, `T = X^alpha`
  truncation, smoothing `h = X^(-d)`.
- `gamma` = the L1 detection point (eta-avoiding every zero outside the
  window).
- Hypothesis `hnoZero`: no non-trivial zero with `Re = beta` and
  `Im in [T0, T0+H]`.
- Seed `rho_0 = beta + i gamma_0` with `gamma_0 in [T0, T0+H]` (the
  counterfactual seed whose existence is the gate's assumption).

## Decomposition of the response under hnoZero

```text
R(gamma) = seedTerm(rho_0, gamma)
         + sum_{Re = beta, Im outside window}   m C_h I      (A: outside top)
         + sum_{Re <= beta - gap}               m C_h I      (B: complementary)
         + Err.
```

With `gamma = Im rho_0` (aligned):

```text
seedTerm ~ X^(lambda beta) / beta * C_h(rho_0) * (1 - o(1)).
```

### A: outside top layer

Each term `<= m * K * min(1,(h|rho|)^-2) * 2 X^(lambda beta)/|gamma - Im rho|`.
For top-layer heights `|rho| ~ T0`, `gamma0 > d`, the kernel factor is
`K X^(-2(gamma0 - d))`, and the eta-avoidance gives `|gamma - Im rho| >= eta`,
so

```text
A <= X^(lambda beta - 2(gamma0 - d)) * (2K / (T0 eta)) * sum_top m
   <= X^(lambda beta - 2(gamma0 - d)) * (2K / (T0 eta)) * C T1 log T1.
```

The seed has `X^(lambda beta - 2(gamma0 - d)) * (1/beta)`; the ratio of A
to the seed is `<= 2 K C * T1 log T1 / (T0 eta) = 2 K C * T1 log T1 *
4 N0 / (T0 H) ~ C' * (T1/T0)^2 * log^2 T1 / H`, which tends to 0 since
`H = X^(gamma0 h')` grows polynomially.  **A is negligible.**

### B: complementary layer

From L2 and the L1 revised bound `S(gamma) <= C (1+log T1)^2 T1/(T0 H)`:

```text
B <= X^(lambda (beta - gap) - 2(gamma0 - d)) * (K/T0) * S(gamma) * (T0 factor)
   <= X^(lambda beta - 2(gamma0 - d)) * X^(-lambda gap) * C (1+log T1)^2 T1/(T0 H) * ...
```

Ratio to the seed: `<= C X^(-lambda gap) * beta * (1+log T1)^2 T1/(T0 H)`
(times harmless constants).  This is `< 1` once

```text
lambda gap * log X > log(T1/(T0 H)) + 2 log log T1 + O(1)
                  = (1 - h') gamma0 log X + O(log log X),
```

the same condition `gap > (1 - h') gamma0 / lambda` (to leading order)
already established in the L1 feasibility check.

### Err

Bounded by the cubic budget `X^(lambda beta - 1/20)` (explicit hypothesis
of the L2 statement); ratio to the seed `<= beta X^(-1/20) * (1+o(1))`,
negligible.

## Conclusion of L3

Under `hnoZero`, the response equals `seed + A + B + Err` with
`A, B, Err` strictly dominated by the seed term once the parameter
conditions hold (`gap > (1-h') gamma0 / lambda`, `H = X^(gamma0 h')`,
`gamma0 > d`, cubic margin).  But the seed term comes from a zero that,
by `hnoZero`, does not exist — contradiction.  Hence some zero with
`Re = beta` lies in `[T0, T0+H]`.

Lean shape: a pure inequality assembly over the L1 `S(gamma)` bound, the
L2 identity, and three "negligibility" lemmas (A, B, Err); no further
analysis.  The three negligibility lemmas are the remaining real-analysis
targets after L1/L2.

## Parameter summary (one feasible point)

```text
beta > 2/3 arbitrary;  lambda = 1.1;  h' = 0.6;  gamma0 = g = lambda (1 - beta)
(taken at its lower bound);  d = (1-g)/8;  alpha = (1+g)/2.
Condition:  gap > (1 - h') gamma0 / lambda = 0.4 * (1 - beta) / 1.1 ...
= 0.3636 (1 - beta) < beta for every beta > 0.267, and gap < beta by
definition.  Feasible.
```

## Boundaries

Specification only.  Promotion order: L1 -> L2 -> the three negligibility
lemmas -> L3 assembly (see `L1-formalization-checklist.md` and this file's
predecessors).
