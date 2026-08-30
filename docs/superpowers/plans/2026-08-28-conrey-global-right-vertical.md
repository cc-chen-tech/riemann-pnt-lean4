# Conrey Global Right-Vertical Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan.

**Goal:** Prove the concrete global right-vertical estimate needed for Conrey 1989 equation (37), with the height-dependent main term retained, while keeping the unresolved horizontal and mean-square gates explicit.

**Architecture:** Four small Lean modules form a dependency chain: an infinite zeta right tail, an elementary Gauss-series digamma height bound, the exact degree-one `V1` height-main decomposition, and the explicit global logarithmic integral.  Every public endpoint is introduced by a failing contract test and proved from existing no-axiom analytic infrastructure.  The local proportional-height normalization remains a lemma; only the final integral theorem is advertised as the right-vertical equation-(37) input.

**Tech Stack:** Lean 4, Mathlib complex analysis and measure integration, existing `PrimeNumberTheorem.DigammaBounds`, existing Conrey modules, Lake contract tests.

**Spec:** `docs/superpowers/specs/2026-08-28-conrey-global-right-vertical-design.md`

## Global constraints

- Do mathematics before expanding Lean interfaces; if an inequality is not proved on paper, do not introduce it as a hypothesis merely to make the file compile.
- Preserve the global interval `1 <= t <= T`.  A theorem only valid on `T <= t <= 2*T` is local and cannot close equation (37).
- Use the explicit parameters `g = 49/100`, `g0 = 0`, `g1 = 51/50` for the final theorem.
- Do not claim the horizontal Jensen estimates, admissible endpoint selection, equations (38)--(41), the long mollified mean square, or Conrey's strict `> 2/5` theorem.
- For each task: write the contract first, run it and record the expected missing-module or missing-declaration failure, then add production code.
- After each public endpoint, run `#print axioms`; no new project axiom is allowed.

### Task 1: Infinite zeta right tail

**Files:**

- Create: `Test/ConreyZetaRightEdgeContract.lean`
- Create: `HardyTheorem/ConreyZetaRightEdge.lean`
- Modify: `lakefile.lean`

**Step 1: Write the failing contract**

The contract imports `HardyTheorem.ConreyZetaRightEdge` and type-checks these endpoints:

```lean
#check HardyTheorem.tsum_nat_add_two_rpow_le_rightTail
#check HardyTheorem.norm_riemannZeta_sub_one_le_rightTail
#check HardyTheorem.norm_riemannZeta_movingRight_sub_one_le
```

Run `lake env lean Test/ConreyZetaRightEdgeContract.lean`; expect failure because the module does not exist.

**Step 2: Prove the general real tail**

Implement

```lean
theorem tsum_nat_add_two_rpow_le_rightTail
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (∑' n : ℕ, (n + 2 : ℝ) ^ (-sigma)) ≤
      2 ^ (-sigma) * (1 + 2 / (sigma - 1))
```

using `Real.tsum_le_of_sum_range_le` and
`CarlsonZeroDensity.sum_Icc_rpow_le_add_div_of_lt_neg_one`.  The finite-sum reindexing must be exact; positivity of the discarded upper endpoint is the only relaxation.

**Step 3: Identify and bound the complex Dirichlet tail**

Prove privately that

```lean
riemannZeta s - 1 = ∑' n : ℕ, 1 / (n + 2 : ℂ) ^ s
```

for `1 < s.re`, then apply `norm_tsum_le_tsum_norm` and
`Complex.norm_cpow_eq_rpow_re_of_pos` to prove

```lean
theorem norm_riemannZeta_sub_one_le_rightTail
    {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s - 1‖ ≤
      2 ^ (-s.re) * (1 + 2 / (s.re - 1))
```

**Step 4: Specialize to the moving edge**

Prove an explicit specialization with hypotheses `Real.exp 1 <= L` and
`s.re = 2 * Real.log L`:

```lean
theorem norm_riemannZeta_movingRight_sub_one_le
    {L : ℝ} (hL : Real.exp 1 ≤ L) {s : ℂ}
    (hre : s.re = 2 * Real.log L) :
    ‖riemannZeta s - 1‖ ≤ 3 / L
```

The algebra must explicitly use `2 ^ (-2*log L) <= 1/L` and
`1 + 2/(2*log L-1) <= 3`; a weaker hidden constant is not acceptable.

**Step 5: Verify and register**

Add both production and test roots to `lakefile.lean`.  Run:

```bash
lake env lean Test/ConreyZetaRightEdgeContract.lean
lake build HardyTheorem.ConreyZetaRightEdge Test.ConreyZetaRightEdgeContract
```

### Task 2: Digamma and archimedean height main

**Files:**

- Create: `Test/ConreyDigammaHeightContract.lean`
- Create: `HardyTheorem/ConreyDigammaHeight.lean`
- Modify: `HardyTheorem/ConreyFarRight.lean`
- Modify: `lakefile.lean`

**Step 1: Write the failing contract**

Check the exact logarithmic derivative identity and the two quantitative endpoints:

```lean
#check HardyTheorem.logDeriv_conreyH_eq
#check HardyTheorem.norm_digamma_halfLine_sub_log_le_nine
#check HardyTheorem.norm_logDeriv_conreyH_sub_half_log_t_div_two_pi_le
```

Run the contract and expect a missing-module failure.

**Step 2: Expose the existing exact identity**

Remove only the `private` modifier from the already-proved theorem in
`ConreyFarRight.lean`.  Do not alter its statement or proof.

**Step 3: Prove the Gauss-series split**

For `z = (sigma + t*I)/2` and `N = ceil ‖z‖₊`, use the existing Gauss digamma series.  Establish, as named private lemmas:

- the first reciprocal block is at most `3`;
- the quadratic tail is at most `1`;
- `1/‖z‖ <= 1` and Euler's constant is at most `1`;
- the harmonic number differs from `log t` by at most the remaining budget.

Combine them into

```lean
theorem norm_digamma_halfLine_sub_log_le_nine
    {sigma t : ℝ} (ht : 2 ≤ t) (hsigma : 1 < sigma)
    (hst : sigma ≤ t) :
    ‖Complex.digamma ((sigma + t * I) / 2) - Real.log t‖ ≤ 9
```

If the exact formal constant `9` fails, stop and revise the mathematical ledger and spec before changing the theorem.

**Step 4: Deduce the `H'/H` height estimate**

Substitute the digamma theorem into `logDeriv_conreyH_eq`, control the two rational terms directly from `t >= 2`, and prove

```lean
theorem norm_logDeriv_conreyH_sub_half_log_t_div_two_pi_le
    {sigma t : ℝ} (ht : 2 ≤ t) (hsigma : 1 < sigma)
    (hst : sigma ≤ t) :
    ‖logDeriv conreyH (sigma + t * I) -
      ((Real.log (t / (2 * Real.pi)) / 2 : ℝ) : ℂ)‖ ≤ 8
```

The restriction `1 < sigma` matches the existing exact `H'/H` identity and
is automatic on the target edge `sigma = 2*log L`.  The constant `8` follows
from half the digamma error plus the two rational terms and the elementary
`log 2`/`log pi` comparison.

**Step 5: Verify and register**

Run the focused contract and Lake roots, followed by `#print axioms` for both endpoints.

### Task 3: Exact degree-one `V1` height-main decomposition

**Files:**

- Create: `Test/ConreyV1RightEdgeContract.lean`
- Create: `HardyTheorem/ConreyV1RightEdge.lean`
- Modify: `lakefile.lean`

**Step 1: Write the failing contract**

Check:

```lean
#check HardyTheorem.conreyDegreeOneHeightMain
#check HardyTheorem.conreyDegreeOneV1_sub_heightMain_eq
#check HardyTheorem.norm_conreyDegreeOneV1_sub_heightMain_movingRight_le
```

Run it and expect a missing-module failure.

**Step 2: Define the height main term**

Define

```lean
def conreyDegreeOneHeightMain (g g0 g1 L t : ℝ) : ℂ :=
  (g + g0 * I) + (g1 / L) * (Real.log (t / (2 * Real.pi)) / 2)
```

and prove the explicit-parameter simplification

```lean
A_L(t) = 49/100 + 51/(100*L) * log(t/(2*pi)).
```

**Step 3: Prove the exact decomposition**

Starting from the definition of `conreyDegreeOneV1`, prove without inequalities:

```text
V1 - A
 = A * (zeta - 1)
   + (g1/L) * zeta'
   + (g1/L) * (H'/H - heightMainH) * zeta.
```

Use this identity as the single source for all norm estimates.

**Step 4: Prove the moving-edge norm estimate**

Combine Task 1, the existing Cauchy zeta-derivative estimate, Task 2, and
`‖zeta‖ <= 1 + ‖zeta-1‖` to prove a bound of the form

```lean
‖conreyDegreeOneV1 ... s - conreyDegreeOneHeightMain ... t‖ ≤
  (3 * ‖conreyDegreeOneHeightMain ... t‖ + 34 * |g1|) / L
```

under visible hypotheses `exp 2 <= L`, `s.re = 2*log L`, `s.im = t`,
`2 <= t`, and `s.re <= t`.  If the proved arithmetic yields a different constant, update the paper ledger first and retain the smallest clean verified integer.

**Step 5: Verify and register**

Run the focused contract, both new modules, and axiom checks.

### Task 4: Explicit global right-vertical integral

**Files:**

- Create: `Test/ConreyExplicitRightVerticalContract.lean`
- Create: `HardyTheorem/ConreyExplicitRightVertical.lean`
- Modify: `lakefile.lean`
- Modify: `docs/research/2026-08-25-conrey-two-fifths-mathematical-audit.md`

**Step 1: Write the failing contract**

Check the explicit main term, its interval bounds, the elementary logarithmic integral, and the final absolute-log integral theorem.

**Step 2: Prove explicit main-term algebra**

For `L = log T`, prove on the high interval `2*log L <= t <= T` and explicit sufficiently-large `T` hypotheses:

```text
1/5 <= A_L(t) <= 1,
1 - A_L(t) = 51/(100*L) * log(2*pi*T/t).
```

Use the exact identity, not an asymptotic rewrite.

**Step 3: Convert pointwise error to a log bound**

After proving the concrete `V1 * mollifier` stays in a disk that avoids zero, apply the local Lipschitz bound for the real absolute logarithm to get

```text
|log |V1(sigma+it) B(sigma+it)|||
  <= C/L * (1 + log(2*pi*T/t))
```

on the high interval.  The lower bound must be explicit in the theorem hypotheses/proof, not an assumed nonvanishing predicate.

**Step 4: Integrate the high and low parts**

Prove the elementary high-part integral directly.  On
`1 <= t <= 2*log L`, use the existing coarse digamma and finite-mollifier estimates to prove a uniform logarithmic bound; multiply by the interval length.  Show the sum is eventually at most `C*T/L` for a concrete natural constant `C`.

**Step 5: State the public right-vertical endpoint**

Expose a theorem for the concrete degree-one parameters and concrete mollifier which bounds

```text
∫ t in 1..T, |log |V1(2*log(log T)+it) B(...)||| <= C*T/log T.
```

The theorem name and docstring must say `rightVertical`; it must not say `conrey_two_fifths` or `complete`.

**Step 6: Verify, document, and checkpoint**

Run all four contracts, `git diff --check`, and the full default `lake build`.  Update the audit ledger to mark only the global right-vertical item proved.  Commit, push the existing branch, and update PR #489 while retaining ready-for-review status.

### Task 5: Next mathematical gate after this checkpoint

**Files:**

- Modify only after Task 4 is verified: `docs/research/2026-08-25-conrey-two-fifths-mathematical-audit.md`

Record the remaining order exactly:

1. horizontal Jensen bounds and admissible endpoint heights;
2. equations (38)--(41), including the long mollified mean square;
3. optimization and strict `> 2/5` extraction.

Do not start a broad Lean abstraction for these items until the corresponding paper estimate has been reconstructed with constants and interval normalizations.
