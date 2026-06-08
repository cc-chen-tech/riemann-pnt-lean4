# Follow-Up Playbook for riemann-pnt-lean4

This document collects every `def ... : Prop` placeholder target in the project,
classified by **what it actually needs to be proved**, with a concrete handoff
package for each.  It is written for a future maintainer (human or specialized
Lean-prover AI) who wants to attack the remaining gap between the current
scaffolding and a full de la Vallée Poussin analytic PNT in Lean 4.

It is **not** a development plan; it is a triage tool.  Each entry below should
be readable in under a minute and answer four questions:

1. What does the target mean, mathematically?
2. What is the minimum Lean 4 API surface needed to discharge it?
3. What is the realistic human effort to formalize it?
4. What is the first concrete step to start?

---

## Scope and Status

| Phase | Status |
| --- | --- |
| Phase 1–3: scaffolding (interface names, trivial bridges, simple API) | Done |
| Phase 4: real proof of de la Vallée Poussin-class analytic PNT | Not started |
| Phase 5: RH itself (the 100+ year open problem) | Out of scope |

The current `verify-baseline.sh` baseline holds **22 `def ... : Prop` target
placeholders** across four namespaces.  None of them are proved.  They are
intentional seams for the four unfinished analytic chains listed in
`docs/missing-chains-index.md`.

There are also a few `def ... : Prop` declarations in the project that are
**reusable predicates, not open targets** — for example
`HardyTheorem.weightedIntegralOf_tail_dominates` (a hypothesis that
higher-up `lemma`s consume) is excluded from the open-target list by
`scripts/list-prop-targets.py:19`.  This document only enumerates the 22
open targets; the predicate layer is documented in
`docs/formal-theorem-inventory.md:256` and is not in scope for the
triage.

This file is the per-target extension of `docs/missing-chains-index.md`.

---

## How to Use This Document

For each target, read the four fields in order.  If you are picking up a
single target, ignore the rest of the document.  The "Capability profile"
column drives effort estimation; the "First step" column is the literal first
edit a maintainer should make.

The targets are grouped by namespace, not by chain, because the namespace
matches the source file and a maintainer will tend to work in one file at a
time.

---

## `ZeroFreeRegion.lean` (chain A)

### Target 1: `classical_zero_free_region`

```lean
def classical_zero_free_region : Prop :=
  ∃ c : ℝ, c > 0 ∧
    ∀ s : ℂ, riemannZeta s = 0 → 1 - c / Real.log (|s.im| + 1) ≤ s.re
```

**Mathematical content.**  Standard PNT-strength zero-free strip
`Re(s) ≥ 1 - c / log(|Im(s)| + 1)` for some absolute `c > 0`.  This is the
de la Vallée Poussin (1899) result, and the project already has the compact
strip `classical_zero_free_region_compact` proved in
`ZeroFreeRegion.lean:282` (nonconstructive positive width, but per-height).

**Capability profile.**
- Complex analysis: Borel–Carathéodory lemma, Jensen's formula, Hadamard
  three-lines / three-circles, log-modulus continuity estimates.
- Mathlib: `Complex.analyticAt`, `MeromorphicAt`, `CircleIntegral`,
  `Real.log`, `Complex.deriv`, `bornology.IsBounded`.
- Standard difficulty for an analytic number theory textbook proof.

**Effort estimate.**  60–120 person-hours, or 6–12 hours of
specialized-LLM attempts with multiple cycles.  The hard part is not
Borel–Carathéodory per se but the chain of `norm_cast`, `positivity`, and
`NNReal`-vs-`Real` coercions that Mathlib forces on log estimates.

**First step.**
1. Open `ZeroFreeRegion.lean` after `classical_zero_free_region_compact`
   (around line 282).
2. Sketch the textbook proof of de la Vallée Poussin's zero-free region in a
   comment, citing the Borel–Carathéodory step, the use of
   `log_deriv_zeta_pos_real` (already proved in this file at line 326), and
   the residue inequality `1 < (σ-1) Re ζ(σ) ≤ σ` (proved in
   `residue_bounds`).
3. Promote each step into a separate `lemma` with `:= by sorry` for now and
   write the full proof sketch inline as `/- ... -/`.

**Adjacent tools.**
- `classical_zero_free_region_compact` (proved, line 282) is the
  starting point.
- `residue_bounds`, `log_deriv_zeta_pos_real`,
  `log_deriv_zeta_antitone` (all proved) supply the analytic ingredients.
- Mathlib `Mathlib.Analysis.Complex.BorelCaratheodory` (if it exists;
  otherwise roll the inequality by hand from
  `Complex.abs_cdf_eq_zero_iff` + `ContinuousOn.norm`).

---

### Target 2: `vinogradov_korobov_zero_free_region`

```lean
def vinogradov_korobov_zero_free_region : Prop :=
  ∃ c : ℝ, c > 0 ∧
    ∀ s : ℂ, riemannZeta s = 0 → 1 - c / Real.log (|s.im| + 1) ^ (2/3 : ℝ) ≤ s.re
```

**Mathematical content.**  The stronger Vinogradov–Korobov zero-free region
(1958, 1958), with `c / log^⅔(|Im(s)|+1)`.  Strictly stronger than
`classical_zero_free_region` and the cleanest current state-of-the-art
asymptotic strip without RH.

**Capability profile.**
- All of Target 1, plus handling of fractional-power log estimates.
- Typically a 1.5–2× multiplier on the Target 1 effort.

**Effort estimate.**  90–180 person-hours, or 10–20 LLM hours.

**First step.**
1. Reuse the Target 1 framework.  Add an extra lemma for
   `Real.log (|s.im| + 1) ^ (2/3 : ℝ)` and its monotonicity.
2. Vinogradov's original trick: the `3/2`-moment bound on
   `Re ζ'/ζ` plus mollification, replacing the `3/2` exponent used in
   `log_deriv_zeta_nonneg_combination`.
3. Promote to `:= by sorry` skeletons, then attack one lemma at a time.

**Adjacent tools.**
- `log_deriv_zeta_nonneg_combination` (proved) is the `1` exponent case.
  Vinogradov uses a sharper mollified combination.
- Mathlib `Real.rpow_add` and friends for the `2/3` exponent.

---

## `PrimeNumberTheorem.lean` (chains B, C, D)

### Target 3: `PNTForm1`

```lean
def PNTForm1 : Prop :=
  ∀ ε : ℝ, ε > 0 → ∀ᶠ x : ℝ in atTop,
    |π x - x / Real.log x| < ε * (x / Real.log x)
```

**Mathematical content.**  Prime Number Theorem in the form
`π(x) ~ x / log x`.  This is the headline.

**Capability profile.**
- Explicit formula (chain B) is the natural path; Perron's formula and
  truncated-sum estimates are the bottleneck.
- Partial summation from Chebyshev's `ψ(x) - x` error to `π(x) - Li(x)`.
- The project already has `pnt_forms_equivalent` (proved,
  `PrimeNumberTheorem.lean`), so the three PNTForm variants are
  provably equivalent.  Attack whichever your chain makes easiest; PNTForm3
  (`ψ(x) ~ x`) is usually the cleanest.

**Effort estimate.**  80–200 person-hours, contingent on chain B
(explicit formula) being discharged.

**First step.**
1. Confirm chain B target `explicit_formula_von_mangoldt` (Target 11) is
   proved first; PNTForm1/2/3 follow by partial summation and
   `pnt_forms_equivalent` (already proved).
2. If chain B is stalled, attack PNTForm3 (`ψ(x) ~ x`) directly via the
   Chebyshev function identity `ψ(x) = ∑_{n≤x} Λ(n)` and a
   `summable`-driven bound, bypassing Perron.  This is harder analytically
   but Lean-cleaner.

**Adjacent tools.**
- `pnt_forms_equivalent` (proved) makes all three PNTForm targets
  equivalent; pick the easiest one and the others follow.
- `chebyshevPsi_eq_mathlib` (proved) provides the
  Chebyshev-function identity hook.
- `vonMangoldt_eq_mathlib` (proved) supplies `Λ` from Mathlib.

---

### Target 4: `PNTForm2`

```lean
def PNTForm2 : Prop :=
  ∀ ε : ℝ, ε > 0 → ∀ᶠ x : ℝ in atTop,
    |π x - li x| < ε * li x
```

**Mathematical content.**  PNT in the `Li(x)` form.  Same effort class as
PNTForm1.

**Effort estimate.**  Same as PNTForm1; both should drop in one commit once
`pnt_forms_equivalent` is wired to a proved form.

**First step.**  See Target 3.  No separate attack needed.

---

### Target 5: `PNTForm3`

```lean
def PNTForm3 : Prop :=
  ∀ ε : ℝ, ε > 0 → ∀ᶠ x : ℝ in atTop,
    |ψ x - x| < ε * x
```

**Mathematical content.**  PNT in Chebyshev form.  This is the form the
explicit formula drives most directly, so it is the natural place to start
once chain B is ready.

**Effort estimate.**  Same as PNTForm1.

**First step.**  See Target 3.  No separate attack needed.

---

### Target 6: `RH_PsiErrorBound`

```lean
def RH_PsiErrorBound : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ C : ℝ, C > 0 ∧
    ∀ x : ℝ, x ≥ 2 → |ψ x - x| ≤ C * x ^ (1/2 + ε)
```

**Mathematical content.**  The `O(x^{1/2+ε})` Chebyshev error bound assuming
RH.  Half-exponent error from the explicit formula plus the `O(x^{1/2+ε})`
zero-counting estimate.

**Capability profile.**
- Conditional on RH (`RiemannHypothesis_of_rh_iff_pointwise_error`,
  proved, wraps to a Mathlib hook).
- Zero-counting `N(T) ~ T log T / 2π` is the only nontrivial analytic
  input needed.
- `summable`-of-primes and partial summation.

**Effort estimate.**  30–60 person-hours; lower than PNTForm1 because the
explicit-formula machinery is already there conditionally.

**First step.**
1. Search Mathlib for `Function.PrimeCounting.asymptotic` or
   `Nat.Prime.asymptotic` for `π(x) ~ x / log x`; this gives the
   counting needed to wire the explicit-formula conditional.
2. If absent, write a `def zero_counting_le {T : ℝ} (hT : 0 < T) :
   Nat.card {ρ : ℂ // ...} ≤ T * Real.log T / (2 * Real.pi) + ...` from
   `Jensen_complex_log` and an argument-principle contour.

---

### Target 7: `RH_ThetaErrorBound`

```lean
def RH_ThetaErrorBound : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ C : ℝ, C > 0 ∧
    ∀ x : ℝ, x ≥ 2 → |θ x - x| ≤ C * x ^ (1/2 + ε)
```

**Mathematical content.**  Same as Target 6 but for the second Chebyshev
function `θ(x) = ∑_{p≤x} log p`.  Drop-in sibling.

**Effort estimate.**  ≤ 10 person-hours on top of Target 6 once that
target's machinery exists.

**First step.**  Same as Target 6, with `θ` swapped in.

---

### Target 8: `RH_PrimeCountingLiErrorBound`

```lean
def RH_PrimeCountingLiErrorBound : Prop :=
  ∃ C : ℝ, C > 0 ∧
    ∀ x : ℝ, x ≥ 2 → |π x - li x| ≤ C * x ^ (1/2 + ε)
```

(Simplified: parameter `ε` left implicit; the project statement is in
`PrimeNumberTheorem.lean:1338`.)

**Mathematical content.**  RH-quality `π(x) - Li(x)` bound.

**Effort estimate.**  ≤ 5 person-hours after Target 6 and 7 exist.

**First step.**  Partial summation from `θ` to `π`, already in Mathlib as
`Real.deriv_mono` + `summable_pow_mul_of_one_lt`.

---

### Target 9: `RH_ErrorBound`

```lean
def RH_ErrorBound : Prop :=
  ∃ C : ℝ, C > 0 ∧
    ∀ x : ℝ, x ≥ 2 → |π x - li x| ≤ C * Real.sqrt x * Real.log x
```

**Mathematical content.**  The classic Cramer-style `O(√x log x)` RH
error.  Stronger than `RH_PrimeCountingLiErrorBound`.

**Effort estimate.**  20–40 person-hours; needs a sharper
explicit-formula remainder term.

**First step.**
1. Pick up the conditional machinery from
   `RH_PrimeCountingLiErrorBound_of_rh_iff_pointwise_error` (proved).
2. Tighten the `x^{1/2+ε}` bound to `x^{1/2} log x` via a `von Mangoldt
   tail bound` lemma: `∑_{ρ, |Im ρ| > T} |...| ≤ x^{1/2} / T`.

---

### Target 10: `rh_iff_optimal_error`

```lean
def rh_iff_optimal_error : Prop :=
  RH ↔ (∃ C : ℝ, C > 0 ∧
    ∀ x : ℝ, x ≥ 2 → |π x - li x| ≤ C * Real.sqrt x * Real.log x)
```

**Mathematical content.**  RH is equivalent to the `O(√x log x)` prime
counting error bound.

**Capability profile.**
- Reverse direction (`⇒`) is Target 9.
- Forward direction (`⇐`) is the deep result: it requires showing that if
  the `O(√x log x)` bound fails, then RH is false.  The cleanest path
  goes through `rh_iff_optimal_error_of_pointwise_implications` and
  `RH_ErrorBound_of_rh_iff_optimal_error` (both proved), which are
  sufficient conditional bridges; the gap is connecting the bridges to
  the abstract RH.

**Effort estimate.**  20–40 person-hours.

**First step.**  Prove the forward direction first; the reverse
direction is just chaining the proved `iff`s.

---

### Target 11: `explicit_formula_von_mangoldt`

```lean
def explicit_formula_von_mangoldt (x : ℝ) (_hx : x ≥ 2) : Prop :=
  -- (truncated/principal-value form, see line 3646)
```

**Mathematical content.**  The von Mangoldt explicit formula:
`ψ(x) - x = -∑_{ρ, Im ρ ≠ 0} x^ρ / ρ + ...`
(with principal-value truncation and an edge-term bound).  This is the
workhorse of chain B.

**Capability profile.**
- Perron's formula application.
- Rectangle contour integral: needs `RectangleIntegral` from Mathlib or
  hand-rolled `CauchyIntegral` chain.
- Residue calculus at `s = 1` and at the nontrivial zeros.
- `Mathlib.Analysis.SpecialFunctions.Gamma` for the pole term.

**Effort estimate.**  100–250 person-hours, or 12–24 LLM hours.  This is
**the single biggest blocker** for the rest of chain B and C.

**First step.**
1. The project already has two helpers in
   `MathlibAux/RectangleResidue.lean` (commit
   `feat(shared-rectangle-residue)`, branch
   `feat/shared-rectangle-residue`) and
   `PrimeNumberTheorem/ExplicitFormulaAux.lean`
   (`feat/explicit-formula-psi0-infra`).  Use them.
2. Sketch the textbook contour: vertical strip
   `Re s ∈ [a, 2]` for `a > 1`, indented around `s = 1` and
   around `Re s = a`.  Apply Perron's formula, then take the limit.
3. The first concrete lemma to write is a `Real.tendsto_atTop` reformulation
   of the truncated-sum remainder; the project file
   `PrimeNumberTheorem/ExplicitFormulaTruncated.lean` (commit
   `feat/explicit-formula-truncated`) has the type-level skeleton.

---

## `HardyTheorem.lean` (chain C)

### Target 12: `integral_asymptotic_target`

```lean
def integral_asymptotic_target (n : ℕ) : Prop :=
  -- (per-moment, see line 562)
```

**Mathematical content.**  Per-moment asymptotic expansion
`∫₀ᵀ Z(t)ⁿ dt ~ κₙ T^{...}` for `n = 1, 2, ...`.  These power the
Hardy–Littlewood and Conrey-style moment bounds.

**Capability profile.**
- Real analysis: dominated convergence, monotone convergence, basic
  asymptotics of trigonometric integrals.
- Mathlib: `MeasureTheory.integral`, `Tendsto.const_mul`,
  `Asymptotics.IsLittleO`.
- These are mostly textbook-calculus skills; the difficulty is
  bookkeeping the `n`-th moment uniformly.

**Effort estimate.**  20–50 person-hours per moment `n`.  The
`n = 1, 2` cases are the only ones the rest of chain C needs.

**First step.**
1. Start with `n = 1` only.  Prove `∫₀ᵀ Z(t) dt = o(T log T)`.
2. Use Mathlib's `Real.tsum_eq_tsum_of_norm_tendsto_zero` to swap
   the sum/integral after applying the explicit formula to `Z(t)`.

---

### Target 13: `hardy_two_signed_moments_target`

```lean
def hardy_two_signed_moments_target : Prop :=
  -- (line 617)
```

**Mathematical content.**  The Hardy-style split into even-moment
(positive) and odd-moment (negative) signed contributions.  This is the
conditional that `weightedIntegralOf_neg` consumes.

**Capability profile.**  Same as Target 12, plus sign bookkeeping.

**Effort estimate.**  30–60 person-hours.

**First step.**  Same as Target 12.  Both targets can be discharged by
the same `Moment` infrastructure once it exists.

---

### Target 14: `hardy_theorem_target`

```lean
def hardy_theorem_target : Prop :=
  -- (line 976)
```

**Mathematical content.**  The full Hardy theorem: there exist nontrivial
zeros off the critical line **if and only if** the unsigned-moment
asymptotic is violated.  Equivalently, the convergence of the two signed
moments forces all zeros onto the critical line.

**Capability profile.**
- Depends on `integral_asymptotic_target` (Target 12),
  `hardy_two_signed_moments_target` (Target 13), and
  the predicate `weightedIntegralOf_tail_dominates` (not an open
  target; see `HardyTheorem.lean:745`).
- The forward direction (signed moments ⇒ critical line) is Hardy's
  original 1914 argument; the converse is a standard exercise.

**Effort estimate.**  40–80 person-hours after Targets 12 and 13 are done.

**First step.**  Disprove conditional — write
`¬ integral_asymptotic_target 0 → ∃ ρ, riemannZeta ρ = 0 ∧ ρ.re ≠ 1/2`
first, as it is shorter.

---

### Target 15: `hardy_zeros_unbounded_target`

```lean
def hardy_zeros_unbounded_target : Prop :=
  -- (line 1056)
```

**Mathematical content.**  The set `{ρ : ℂ // riemannZeta ρ = 0 ∧ ρ.re = 1/2}`
is unbounded in imaginary part.  Hardy's original 1914 theorem.  This is
the unconditional one, and a `:= True` placeholder today.

**Capability profile.**
- This **is** the Hardy theorem, but stated unconditionally (the
  moment estimates were the historical hard part; modern textbook proofs
  use either Hardy–Littlewood 1920 or Levinson 1974).
- The "monotone reformulation" `hardy_zeros_abs_unbounded_target`
  (Target 16) is a one-liner if this is proved.

**Effort estimate.**  30–60 person-hours if the moment targets
(12, 13) are available; 200+ person-hours otherwise.

**First step.**
1. Wire `hardy_two_signed_moments_target` (Target 13) into
   `exists_zero_on_critical_line_of_two_signed_moments` (proved at
   `HardyTheorem.lean`).
2. The remaining gap is a "no-sign-flip" argument on the signed moments;
   see Hardy, "Sur les zéros de la fonction ζ(s) de Riemann", CR Acad.
   Sci. Paris 158 (1914), 1012–1014.

---

### Target 16: `hardy_zeros_abs_unbounded_target`

```lean
def hardy_zeros_abs_unbounded_target : Prop :=
  -- (line 1062; monotone reformulation of Target 15)
```

**Mathematical content.**  Monotone reformulation: same as
`hardy_zeros_unbounded_target`.

**Effort estimate.**  ≤ 5 person-hours after Target 15 is proved.

**First step.**  See `docs/formal-theorem-inventory.md:271`: a
`lemma` wrapping `hardy_zeros_unbounded_target` with monotone envelope
machinery.  This is a one-liner.

---

### Target 17: `hardy_littlewood_lower_bound_target`

```lean
def hardy_littlewood_lower_bound_target : Prop :=
  -- (line 1482)
```

**Mathematical content.**  The Hardy–Littlewood lower bound on the
count of zeros on the critical line in a height range.  Strictly weaker
than Target 15 (unconditional infinity) and Target 18
(Selberg proportion), but stronger than Target 19 (Conrey 40%).

**Capability profile.**  Same as Targets 16, 19.

**Effort estimate.**  60–100 person-hours; falls out of Target 18 as a
corollary.

**First step.**  See `docs/formal-theorem-inventory.md:274`: this
target is "available as a derived output if `selberg_zero_proportion_target`
is available".  Skip it; pick up Target 18.

---

### Target 18: `selberg_zero_proportion_target`

```lean
def selberg_zero_proportion_target : Prop :=
  -- (line 1485; Selberg 1942: positive proportion of zeros on critical line)
```

**Mathematical content.**  Selberg's 1942 result that a positive
proportion (specifically ≥ c > 0) of the nontrivial zeros lie on the
critical line.  This is the cleanest modern "lots of zeros on the line"
statement and a key pre-requisite for the Conrey-style 40% result.

**Capability profile.**
- Selberg's sieve / moment method.  Mostly real analysis with some
  Dirichlet series manipulation.
- The proof is long but elementary; the project already has
  `selberg_zero_proportion_target` wired into
  `exists_zero_on_critical_line_of_selberg_zero_proportion` (proved),
  so once the target is discharged, the `exists_zero_on_critical_line`
  corollary is one `exact` away.

**Effort estimate.**  100–200 person-hours.

**First step.**
1. This is the most analyzed open target in the literature; you should
   not start from scratch.  Read Selberg's 1942 paper first.
2. The key lemma is a `Selberg` sieve bound on
   `∑_{d≤D} μ(d)² / d` for the squarefree divisor; this needs
   `Finset.sum_mono_set` + `Real.summable_of_nat_one_div` plumbing.

---

### Target 19: `gamma_asymptotic_half_plus_it_target`

```lean
def gamma_asymptotic_half_plus_it_target : Prop :=
  -- (line 1738)
```

**Mathematical content.**  Stirling's asymptotic for
`Γ(1/2 + it)` as `t → ∞`, with the explicit error term
`Γ(1/2 + it) = √(2π) |t|^{-1/2} e^{-π|t|/2} (1 + O(1/t))`.

**Capability profile.**
- Real analysis: log-convexity of `Γ`, dominated convergence, basic
  integration by parts.
- The Stirling asymptotic is in Mathlib as `Real.Gamma_asymptotic` or
  `Complex.Gamma_asymptotic` (verify in the local Mathlib).

**Effort estimate.**  10–30 person-hours.  Mathlib probably already
has it; this is mostly a wrapper.

**First step.**  Search `vendor/mathlib` for `Gamma_asymptotic`,
`log_gamma_asymptotic`, or `RiemannSiegelTheta`.  If present, this
target is a 5-line wrapper.

---

### Target 20: `theta_asymptotic_target`

```lean
def theta_asymptotic_target : Prop :=
  -- (line 1763)
```

**Mathematical content.**  Asymptotic for the Riemann–Siegel theta
function `θ(t) = (1/2) Im log Γ(1/4 + it/2) - (t/2) log π`.  Usually
stated `θ(t) = (t/2) log(t/2π) - t/2 - π/8 + O(1/t)`.

**Capability profile.**  Same as Target 19; Mathlib has `RiemannSiegelTheta`.

**Effort estimate.**  5–10 person-hours once Target 19 is in place.

**First step.**  Search `vendor/mathlib` for `RiemannSiegelTheta`.  If
present, this is a 10-line wrapper.

---

### Target 21: `approximate_functional_equation_target`

```lean
def approximate_functional_equation_target : Prop :=
  -- (line 1790)
```

**Mathematical content.**  The Riemann–Siegel `S(t)` formula
`ζ(s) = S(t) + χ(s) S(1-s) + O(x^{-1/2})` (with `s = 1/2 + it` and
`x = √(t/2π)`).  This is the engine of the explicit formula in
chain B for high `t`.

**Capability profile.**
- Hard: it requires the saddle-point argument for the theta function
  plus a contour shift.
- Mathlib has the components (the theta target above, the chi factor
  `chi s = 2^s π^{s-1} sin (πs/2) Γ(1-s)`), but the saddle-point
  argument is not in Mathlib.

**Effort estimate.**  60–120 person-hours.

**First step.**
1. Pick up the theta asymptotic (Target 20) first; the AFE is built
   on top of it.
2. The standard textbook source is Edwards, "Riemann's Zeta Function",
   §3.7.

---

## `RiemannExplorer.lean` (chain D)

### Target 22 (alias of 19): `conrey_40_percent_zeros_on_critical_line_target`

```lean
def conrey_40_percent_zeros_on_critical_line_target : Prop :=
  RiemannExplorer.Conrey40.lowerBound
```

**Mathematical content.**  Conrey's 1989 strengthening of Selberg's
positive-proportion result to ≥ 2/5 of the nontrivial zeros on the
critical line.  The project's nested namespace
`RiemannExplorer.Conrey40` (`commit feat/conrey-40-percent-target`,
branch `feat/conrey-40-percent-target`) holds the type-level
skeleton.

**Capability profile.**  Strictly stronger than Target 18
(Selberg proportion).  Conrey's improvement uses a GUE-style
autocorrelation argument on the pair-correlation of the zeros,
which requires understanding of the Riemann–Siegel `Z`-function
autocorrelation.

**Effort estimate.**  100–250 person-hours; strictly harder than
Selberg.  Skip this until Target 18 is done.

**First step.**  Same as Target 18: read Selberg first, then Conrey
"More than two fifths of the zeros of the Riemann zeta function are
on the critical line", J. Reine Angew. Math. 399 (1989), 1–26.

---

## Diagnostic: meromorphic-at-1 attempt (deferred to follow-up)

The Q3 2026 multi-chain PR #1 ships a `MeromorphicAux.lean` file with
`meromorphicAt_riemannZeta_of_ne_one` and
`meromorphicOn_riemannZeta_closedBall` proved, but
`meromorphicAt_riemannZeta_one` (the value at the pole) deferred.

**What I tried (and why it failed).**  The Mathlib API for
`MeromorphicAt` requires exhibiting, around `s = 1`, a function `g`
holomorphic in a punctured neighborhood such that `(s - 1) * ζ s = g s`
eventually.  This is equivalent to showing `(s-1)² ζ s → 0` as
`s → 1`, which the project already has as `riemannZeta_pole_simple`
(proved in `PrimeNumberTheorem.lean`).

The Lean 4.29.1 obstruction is **not mathematical** but **mechanical**:

- `obtain ⟨δ, hδpos, hδball⟩ := ...` destructures an `Exists` in
  polymorphic context, and `δ` is inferred as `ℕ → ℂ` (the type of
  the rest of the lemma's binder) rather than `ℝ`.  Eight
  variations tried; all failed at the type-inference step.
- `@Classical.choose ℝ` annotation does not propagate into the
  `Exists` destructured context.
- A `let` binding to a `Classical.choose` does not survive into the
  subsequent `MeromorphicAt` constructor application because the
  constructor expects a specific `δ` with `0 < δ` in `ℝ`.

**Recommended first step for the next maintainer.**
1. Open `wt-meromorphic/ZeroFreeRegion/MeromorphicAux.lean` from the
   feat branch `feat/meromorphic-aux-zerofree` (HEAD:
   `meromorphicAt_riemannZeta_of_ne_one` proved, the
   `meromorphicAt_riemannZeta_one` line is the `:=` placeholder).
2. Add a `local notation` to force `δ : ℝ` to be lifted from the
   ambient `∃ δ : ℝ, ...` before destructuring.
3. If that does not work, lift the entire
   `meromorphicAt_riemannZeta_one` claim to a separate `lemma` whose
   **first** binder is `δ : ℝ`, so that Mathlib's elaborator is
   pushed into the right context.
4. The mathematical content is trivial: it is a wrapper around
   `riemannZeta_pole_simple` plus the Mathlib lemma
   `MeromorphicAt_of_removable_singularity` (or its equivalent).
   Once the `δ`-binding issue is resolved, the proof body is
   expected to be 5–10 lines.

This is a 30-minute problem for someone who knows Lean 4's
elaborator; it is a multi-day problem for an LLM that doesn't.

---

## Diagnostic: `verify-baseline.sh` does not recurse

The baseline verification script at `scripts/verify-baseline.sh:13`
uses `rg -n "\bsorry\b|\badmit\b|\baxiom\b" *.lean`, which does **not**
recurse into subdirectories.  The project root has `HardyTheorem.lean`
and `PrimeNumberTheorem.lean` at the top level, so the script catches
placeholders in those two files, but a placeholder in
`MathlibAux/RectangleResidue.lean` or
`ZeroFreeRegion/MeromorphicAux.lean` would not be flagged.

**Recommended first step.**
1. Update `scripts/verify-baseline.sh:13` to use
   `rg -n --no-ignore --hidden "\bsorry\b|\badmit\b|\baxiom\b" .`
   (with a project-root `.rgignore` if needed for `.lake/`).
2. Or add an explicit `rg` pass per top-level subdirectory:
   `for d in MathlibAux PrimeNumberTheorem HardyTheorem ZeroFreeRegion RiemannExplorer; do ...; done`.

This is a 5-minute fix and was the subject of a memory entry
already filed at the agent level.

---

## Triage Summary

| Effort | Targets |
| --- | --- |
| ≤ 10 person-hours (quick wins) | 16, 19, 20, plus the verify-baseline script fix |
| 10–50 person-hours (medium) | 8, 9, 12, 13, 15, 17 |
| 50–150 person-hours (large) | 1, 2, 6, 7, 18, 21 |
| 150+ person-hours (epic) | 10, 11, 22 |
| PNT 1/2/3 chain (drops with 11) | 3, 4, 5 |

**The single highest-leverage target is `explicit_formula_von_mangoldt`
(Target 11).**  Discharging it unlocks Targets 3, 4, 5, 6, 7, 8, 9
conditionally, and reduces the rest of the project's PNT chain to
bookkeeping.

**The single highest-leverage quick win is `theta_asymptotic_target`
(Target 20).**  It is 5–10 hours of pure real analysis, has no
analytic-number-theory content, and unblocks Target 21.

**The right execution order for a new maintainer:**

1. Fix the `verify-baseline.sh` recursion (5 minutes).
2. Pick up Target 20 (theta asymptotic; 5–10 hours).
3. Pick up Target 19 (gamma asymptotic; 10–30 hours) if Mathlib has
   the underlying Stirling.
4. Pick up Target 11 (explicit formula; 100–250 hours).
5. With Target 11 done, Targets 3, 4, 5 drop in one commit each.
6. With Target 11 done conditionally, Targets 6–10 follow from
   `pnt_forms_equivalent` and the existing `iff` bridges.
7. Pick up Target 18 (Selberg proportion) for chain C.
8. Pick up Target 22 (Conrey 40%) only after Target 18.
9. Targets 1, 2 (zero-free region) can run in parallel with all of the
   above.

---

## Out of Scope

- **The Riemann Hypothesis itself.**  This is a 165-year-old open
  problem.  Even a partial-conditional disproof of RH is a Clay
  Millennium problem and not the work of a Lean 4 formalization
  project; it is the work of a research mathematician.
- **Pair-correlation, GUE, Montgomery's theorem.**  These power
  Conrey's 40% result (Target 22) and are themselves non-trivial
  analytic statements.  They are an entire research project
  beyond the current scope.
- **A full proof of the explicit formula with the optimal error term**
  (the `O(x^{-1/2})` Riemann–Siegal-formula bound).  The `O(x^{-1/4})`
  version (Perron + crude rectangle) is the realistic target.

---

## Appendix: File-Level Dependency Map

For a maintainer who is working in one file at a time, the current
defs to fix are concentrated in five files:

| File | Open targets |
| --- | --- |
| `ZeroFreeRegion.lean` | 1, 2 (chain A) |
| `PrimeNumberTheorem.lean` | 3, 4, 5, 6, 7, 8, 9, 10, 11 (chain B, C) |
| `HardyTheorem.lean` | 12, 13, 14, 15, 16, 17, 18, 19, 20, 21 (chain C) |
| `RiemannExplorer.lean` | 22 (chain D, alias of 18) |
| `ZeroFreeRegion/MeromorphicAux.lean` | (the meromorphic-at-1 follow-up) |
| `MathlibAux/RectangleResidue.lean` | (interface helper, no targets) |
| `PrimeNumberTheorem/ExplicitFormulaAux.lean` | (interface helper, no targets) |
| `PrimeNumberTheorem/ExplicitFormulaTruncated.lean` | (interface helper, no targets) |
| `HardyTheorem/Phase1Aux.lean` | (interface helper, no targets) |
| `HardyTheorem/AFE.lean` | (interface helper, no targets) |
| `RiemannExplorer/Conrey40.lean` | (interface helper, no targets) |

The helper files (no open targets) are scaffolding only; they are
intended as the API surface a future maintainer will use to discharge
the real targets in the main files.
