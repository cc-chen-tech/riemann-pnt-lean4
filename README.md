# De la Vallee Poussin 3-4-1 Infrastructure for the Riemann Zeta Function in Lean 4

A Lean 4 project developing formalized infrastructure around the Riemann zeta
function, Hardy's theorem, zero-free regions, and Prime Number Theorem statements.
It is built on Mathlib and currently serves as a buildable proof framework with
explicitly isolated unproved target statements.

The publishable core of the current repository is:

> **de la Vallee Poussin 3-4-1 machinery and a compact zero-free strip in Lean 4**

This means the project verifies the local analytic mechanism

1. the real-part Dirichlet-series expansion for `-ζ'/ζ` in terms of the von
   Mangoldt function;
2. the 3-4-1 logarithmic-derivative inequality using
   `3 + 4*cos θ + cos (2*θ) >= 0`;
3. the compactness argument turning Mathlib's nonvanishing on `Re(s) >= 1` into
   a positive-width zero-free strip for each fixed height bound.

The repository does **not** claim the classical quantitative zero-free region
`σ >= 1 - c / log |t|`, the full PNT, or RH.

## Evaluation Framework

This repository should be evaluated under two separate lenses.

### Internal proof progress

The internal status asks what the current Lean checkout proves.  For this
purpose, the relevant distinction is:

- proved Lean declarations such as `theorem`/`lemma`;
- unproved roadmap declarations written as `def ... : Prop`;
- route interfaces and reusable predicates that are intentionally not exported
  as theorems.

The internal target count is useful for engineering progress, but it is not by
itself a novelty or publication claim.

### External SOTA positioning

The external academic value must be judged only after comparing with existing
formalizations and Mathlib infrastructure.  In particular, existing work already
includes:

- elementary PNT formalizations in Isabelle/HOL;
- Newman's analytic PNT proof in HOL Light;
- Lean PNT work via the Wiener-Ikehara route in `PrimeNumberTheoremAnd`;
- Mathlib's zeta/L-function formalization, including `riemannZeta`, Euler
  products, the functional equation, and nonvanishing in `Re(s) >= 1`;
- newer Lean repositories should also be checked before making a public SOTA
  claim.

Therefore the stable claim for this repository is narrower:

> A local Lean 4 formalization of the de la Vallee Poussin 3-4-1 machinery and
> compact zero-free strip, complementary to existing PNT formalizations by other
> routes.

Do not describe this repository as a first formalization of PNT, a completed
classical analytic PNT proof, a proof of RH, or a completed quantitative
zero-free-region formalization.

## Distance to PNT

The current project is best viewed as the front half of the classical
de la Vallee Poussin engine, not as a near-complete PNT proof.

| Goal | Current distance |
|---|---|
| Publish a Lean 4 formalization module around `3-4-1 + compact strip` | comparatively close |
| Prove the classical zero-free region `1 - c / log |t|` | still far; needs core analytic estimates |
| Derive a full PNT proof along this route | very far |
| Derive a PNT with classical error term | farther still |

The verified chain currently looks like:

```text
von Mangoldt series for -zeta'/zeta
        -> 3-4-1 inequality
        -> compact zero-free strip
        -> local pole-side log-derivative principal-part package
        -> conditional closure interfaces
```

To reach classical PNT through this route, at least two major analytic segments
are still missing:

```text
A. Quantitative zero-free region:
   zeta(s) != 0 for Re(s) >= 1 - c / log |Im(s)|

B. From the zero-free region to PNT:
   explicit formula / Perron or Tauberian input,
   psi(x) ~ x,
   pi(x) ~ x / log x
```

The next genuinely hard lemma is not another target inventory update.  It is a
boundary-strip logarithmic-derivative estimate of the following shape:

```lean
∃ B T0, ∀ z : ℂ,
  1 ≤ z.re → z.re ≤ 2 → T0 ≤ |z.im| →
  ‖logDeriv riemannZeta z‖ ≤ B * Real.log |z.im|
```

The checkout now names this objective-shaped interface as
`ZeroFreeRegion.LogDerivVerticalLogBound`, with signed
`ZeroFreeRegion.NegLogDerivVerticalLogBound` and real-part quotient
`ZeroFreeRegion.ReNegDerivDivVerticalLogBound` variants.  The constructors
`ZeroFreeRegion.logDeriv_riemannZeta_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height`,
`ZeroFreeRegion.negLogDeriv_riemannZeta_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height`,
and
`ZeroFreeRegion.reNegDerivDiv_riemannZeta_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height`
convert a future affine `A + B log(|t|+3)` high-height input into these exact
`C log |t|` interfaces.  If a future estimate is already stated in the exact
`B log |t|` scale, the constructors
`ZeroFreeRegion.logDerivVerticalLogBound_of_high_height_log_abs_bound`,
`ZeroFreeRegion.negLogDerivVerticalLogBound_of_high_height_log_abs_bound`, and
`ZeroFreeRegion.reNegDerivDivVerticalLogBound_of_high_height_log_abs_bound`
package it directly as the named interfaces.  These are verified handoffs, not
the missing zeta-specific high-height estimate itself.

The second missing high-height input is also named in Lean:
`ZeroFreeRegion.LogDerivRegularPartLogBound` and
`ZeroFreeRegion.MultiplicityLogDerivRegularPartLogBound` state the expected
local regular-part estimate near a zero candidate `ρ = β + i t`, with and
without explicit zero multiplicity.  The verified conditional closures
`ZeroFreeRegion.classical_zero_free_region_of_LogDerivRegularPartLogBound_and_LogDerivVerticalLogBound`
and
`ZeroFreeRegion.classical_zero_free_region_of_MultiplicityLogDerivRegularPartLogBound_and_LogDerivVerticalLogBound`
show that these named regular-part inputs plus the named vertical bound close
the existing Lean target `classical_zero_free_region`.  The direct real-part
variants
`ZeroFreeRegion.classical_zero_free_region_of_LogDerivRegularPartLogBound_and_ReNegDerivDivVerticalLogBound`
and its multiplicity-aware analogue prove the same final conditional closure
from a weaker vertical input: an estimate for the exact
`Re(-ζ'/ζ)` quantity used by the 3-4-1 argument, without first strengthening it
to a norm bound.  The existential wrappers
`ZeroFreeRegion.classical_zero_free_region_of_exists_LogDerivRegularPartLogBound_and_exists_LogDerivVerticalLogBound`
and the corresponding `...exists_ReNegDerivDivVerticalLogBound` analogues allow
the two estimates to be proved above different height cutoffs, merging the
cutoffs by `max`.

Mathematically, that regular-part estimate has the shape:

```text
Re(-ζ'/ζ(σ + i t)) <= -1 / (σ - β) + O(log |t|).
```

These are the current hard wall.  They normally require zeta growth estimates
together with Borel-Caratheodory, Jensen/Hadamard factorization, or equivalent
zero-repulsion machinery.  The repository already has fixed-margin estimates
for `1 + ε <= Re(s)`, compact bounded-height norm bounds for
`H <= |Im(s)| <= T`, and bridge lemmas that patch a future high-height
`B * log |t|` estimate into an all-height affine logarithmic estimate.  Those
bridges still do not provide the missing high-height boundary-strip estimate on
`1 <= Re(s)`.  The polynomial-growth handoff into Jensen/Borel scale is also
now proved: `ZeroFreeRegion.log_norm_bound_of_polynomial_growth` and its
zeta-specific coordinate forms convert
`‖ζ(s)‖ <= A * (‖s‖ + 3)^B` into
`log ‖ζ(s)‖ <= log A + B log(‖s‖ + 3)`, and on the standard strip
`1 <= σ <= 2`, `|t| >= 5`, further into
`log ‖ζ(σ+it)‖ <= log A + 2B log(|t|+3)`.  A circle-average version also
turns the same input into
`circleAverage(log ‖ζ‖) <= log A + 2B log(|t|+|R|+3)` whenever the circle
stays in the high vertical strip.  The Borel-Caratheodory side now also has
positive and signed `logDeriv ζ` half-radius bridges, including centered
oscillation versions, whose real-part and center hypotheses are already stated
in the `log(|t|+3)` height scale; right-shifted versions convert such local
inputs into pure `C log |t|` outputs at `σ+it`.  These handoff lemmas do not
prove the missing polynomial growth or boundary-strip logarithmic-derivative
estimate itself.  On the pole side, the local decomposition
`logDeriv ζ(s) = -(s-1)^-1 + logDeriv(unit)(s)` is now proved near `s=1`,
and the unit logarithmic derivative is locally bounded; this improves the
real-axis bookkeeping but still does not supply the missing high-height
zeta-specific estimates.

## Paper Positioning

The recommended paper framing is to make the `3-4-1 + compact zero-free strip`
module the main contribution, after explicitly locating the project relative to
the existing PNT and zeta/L-function formalization landscape.  The remaining
infrastructure should be presented as secondary contributions and future work.
This keeps the claims tight:

1. **Primary contribution:** formalizing the real-part logarithmic-derivative
   Dirichlet series, the de la Vallee Poussin 3-4-1 inequality, and the compact
   zero-free strip.
2. **Secondary contribution:** correctly formulating the Riemann-von Mangoldt
   explicit formula target using `chebyshevPsi0`, finite-height truncations, and
   explicit error/remainder forms rather than an unordered infinite zero sum.
3. **Supporting contribution:** proving PNT-form equivalences and RH-scale error
   propagation lemmas that will compose with a future proof of `ψ(x) ~ x` or a
   future explicit formula theorem.
4. **Framework contribution:** building a Hardy-Z/critical-line-zero framework
   with explicit target statements for Hardy, Hardy-Littlewood, Selberg, and
   Conrey-style zero-counting results.
5. **Mathlib roadmap:** isolating the missing analytic inputs: zeta growth and
   logarithmic-derivative estimates for quantitative zero-free regions, Perron
   and residue-theorem machinery for the explicit formula, and special-function
   asymptotics for Hardy's theorem.

The strongest current title direction is:

> **Formalizing the 3-4-1 Inequality and a Compact Zero-Free Strip for the
> Riemann Zeta Function in Lean 4**

Broader PNT/RH/Hardy titles should be used only if the title clearly says this
is infrastructure or a framework, not a completed proof of PNT or RH.

## Status

`lake build` succeeds with Lean 4.29.1 / Mathlib 4.29.1. The repository is not
a completed proof of the Prime Number Theorem or the Riemann Hypothesis.

Current code status:

| File | `sorry` count | Unproved targets |
|---|---:|---|
| `GammaResidue.lean` | 0 | General Gamma residue formula completed |
| `HardyTheorem.lean` | 0 | Hardy-Z phase facts proved; corrected integral asymptotic, positivity and zero-counting targets |
| `PrimeNumberTheorem.lean` | 0 | Bounded-height zero finiteness and zero-symmetry bridges proved; RH error equivalence and von Mangoldt explicit formula targets |
| `ZeroFreeRegion.lean` | 0 | 3-4-1 and compact zero-free region proved; quantitative zero-free-region targets |

Total: 0 syntactic `sorry` occurrences in Lean source files.

Unresolved mathematical target declarations (currently not promoted to
theorems): **22**.

 - `HardyTheorem` namespace: 7
 - `HardyTheorem.Details` namespace: 3
 - `PrimeNumberTheorem` namespace: 9
 - `KnownResults` namespace: 1
 - `ZeroFreeRegion` namespace: 1
 - global namespace: 1 (`vinogradov_korobov_zero_free_region`)

Full `def ... : Prop` inventory:

- mathematical targets: 22;
- route interfaces: 6
  (`HardyTheorem.AFE.zeta_critical_afe_target`,
  `MathlibAux.rectangleIntegral_meromorphic_eq_residue_sum`,
  `PrimeNumberTheorem.ExplicitFormulaConversePowerTarget`,
  `PrimeNumberTheorem.ExplicitFormulaTruncated.ExplicitFormulaTruncatedConverseRoute`,
  `PrimeNumberTheorem.ExplicitFormulaTruncated.ExplicitFormulaTruncatedTarget`,
  `RiemannExplorer.Conrey40.conrey_40_percent_zeros_on_critical_line_target`);
- reusable predicates: 2
  (`HardyTheorem.weightedIntegralOf_tail_dominates`,
  `PrimeNumberTheorem.ExplicitFormulaAux.goodHeight`);
- unclassified Prop definitions: 0.

No route interface currently has a body equal to `True`.  The rectangle
contour/residue interface is a real `Prop` statement, but it is still not a
proved general residue theorem.  The repository does prove the constant-function
sanity checks `MathlibAux.rectangleBoundaryIntegral_const`,
`MathlibAux.rectangleIntegral_const`, and
`MathlibAux.rectangleIntegral_const_zero`; these show that the interface is
satisfiable in the holomorphic empty-pole case, not that Perron's formula or the
general rectangle residue theorem has been proved.

## File Overview

| File | Description | Status |
|---|---|---|
| `RiemannPNT.lean` | Build entry point importing all top-level modules | sorry-free |
| `RiemannExplorer.lean` | Riemann Hypothesis statement, zeta definitions, functional equation, trivial zeros | sorry-free |
| `EulerAndLfunctions.lean` | Thin wrappers around Mathlib zeta/Euler product/L-function facts | sorry-free |
| `GammaResidue.lean` | Gamma residue facts and numerical special cases | sorry-free |
| `HardyTheorem.lean` | Hardy Z-function setup with corrected target statements for critical-line zeros | sorry-free, targets unproved |
| `PrimeNumberTheorem.lean` | PNT forms, equivalences, Li(x) asymptotics, zero symmetry, bounded-height zero finiteness, explicit formula target | sorry-free, targets unproved |
| `ZeroFreeRegion.lean` | 3-4-1 setup, log derivative series, compact zero-free region, quantitative zero-free-region targets | sorry-free, quantitative targets unproved |
| `PrimeNumberTheorem/ExplicitFormulaAux.lean` | `chebyshevPsi0`, `goodHeight`, finite zero-sum support helpers | sorry-free, support predicate only |
| `PrimeNumberTheorem/ExplicitFormulaTruncated.lean` | Truncated explicit-formula route interface with a real Prop body | sorry-free, route interface unproved |
| `MathlibAux/RectangleResidue.lean` | Rectangle residue route interface for future Perron/explicit-formula work, plus constant-function sanity checks | sorry-free, route interface unproved |
| `HardyTheorem/AFE.lean` | Corrected AFE route interface using an unwrapped theta wrapper | sorry-free, route interface unproved |
| `RiemannExplorer/Conrey40.lean` | Conrey target alias to the upper-level `KnownResults` target | sorry-free, route interface alias |

## Verified Components

The project currently verifies several supporting statements, including:

- the formal RH statement restricted to nontrivial zeros;
- zeta special-value and Euler-product wrappers available in Mathlib;
- basic PNT-form equivalence scaffolding and asymptotic lemmas;
- the trigonometric identity `3 + 4cos θ + cos 2θ = 2(1+cos θ)² ≥ 0`;
- the full 3-4-1 logarithmic-derivative nonnegativity combination;
- scaled complex-exponential certificate hooks for finite zero-detector
  trigonometric polynomials, plus Lean-checked BTY detector coefficients
  `a_0 = 1`, `a_1 = 865534 / 497079`, and
  `sum_{1 <= k <= 16} a_k = 2919857 / 828465`;
- the full scaled complex-exponential absolute-square certificate for the
  degree-16 Bellotti-Trudgian-Yang detector and its automatic
  logarithmic-derivative detector inequality;
- the algebraic lower-bound step that isolates one term from a nonnegative
  finite detector combination;
- the BTY degree-16 detector lower bound for the first shifted
  logarithmic-derivative term;
- BTY-specific coefficient positivity, remaining-coefficient sum, shifted
  upper-bound lower bridges, and the simplified rational constant bridge for
  the selected `k=1` logarithmic-derivative term;
- center-one finite zero-pair positivity bridges, average finite-zero
  contribution nonnegativity, new-zero block reflection/reindexing/averages/norm
  bounds, eventually-zero/tendsto-zero tail collapses under empty new-zero
  hypotheses, pointwise critical-strip positivity suppliers for candidate
  zero-detector kernels, generic finite nonnegative kernel-combination closure,
  a concrete resolvent/Laplace prototype kernel with finite-zero and new-zero
  nonnegativity wrappers, finite nonnegative resolvent-kernel combinations with
  the same wrappers, single and finite affine resolvent-kernel variants with
  the same finite-zero/new-zero wrappers, and
  reflected-line conditional bridges for explicit-formula/PNT-error routes;
- several zeta nonvanishing and pole-behavior wrappers from Mathlib;
- the Gamma residue formula at negative integers and numerical special cases;
- the compact zero-free region near `Re(s)=1` for each bounded height;
- meromorphicity of `riemannZeta` at its pole and on closed balls;
- finiteness of nontrivial zeros in each bounded-height strip.

## Publishable Core Theorem Inventory

The following declarations are the current paper-grade core.  They are proved
Lean declarations in `ZeroFreeRegion.lean` and
`ZeroFreeRegion/MeromorphicAux.lean`, not `def ... : Prop` target statements.

| Lean declaration | Kind | Mathematical content | Publication role |
|---|---|---|---|
| `ZeroFreeRegion.log_deriv_zeta_re_series` | `lemma` | For `Re(s) > 1`, expands `Re(-ζ'(s)/ζ(s))` as the von Mangoldt Dirichlet series `∑' n, Λ(n) cos(Im(s) log n) / n^Re(s)`. | Main technical bridge from Mathlib's complex L-series identity to a real series usable in the 3-4-1 argument. |
| `ZeroFreeRegion.norm_logDeriv_riemannZeta_le_real_neg_deriv_div` | `lemma` | For `Re(s) > 1`, proves `‖logDeriv ζ(s)‖ ≤ Re(-ζ'/ζ(Re(s)))` by applying the triangle inequality to the von Mangoldt L-series. | Zeta-specific half-plane bound that reduces a vertical log-derivative estimate to the real-axis series in the region of absolute convergence. |
| `ZeroFreeRegion.exists_norm_logDeriv_riemannZeta_le_log_abs_im_add_three_of_one_add_le_re` | `lemma` | For every fixed `ε > 0`, proves existence of `C ≥ 0` with `‖logDeriv ζ(z)‖ ≤ C log(|Im z|+3)` throughout `1+ε ≤ Re(z)`. | A genuine fixed-margin vertical logarithmic bound in the absolute-convergence half-plane; it marks the boundary between proved L-series control and the still-missing estimate down to `Re(z)=1`. |
| `ZeroFreeRegion.exists_norm_neg_logDeriv_riemannZeta_le_log_abs_im_add_three_of_one_add_le_re` | `lemma` | Signed version of the fixed-margin vertical logarithmic bound for `‖-logDeriv ζ(z)‖`. | Keeps the absolute-convergence estimate directly available in the sign convention used by de la Vallée Poussin's 3-4-1 inequality. |
| `ZeroFreeRegion.exists_norm_logDeriv_riemannZeta_sigma_it_le_log_abs_of_fixed_margin` / `ZeroFreeRegion.exists_norm_logDeriv_riemannZeta_sigma_two_it_le_log_abs_of_fixed_margin` | `lemma` | Converts the fixed-margin `σ+it` and `σ+2it` norm bounds to the exact high-height scale `C log |t|`, still assuming `1+ε ≤ σ`. | Matches the target shape of the missing vertical logarithmic estimate while making explicit that the proved result remains fixed-margin, not boundary-strip. |
| `ZeroFreeRegion.exists_norm_neg_logDeriv_riemannZeta_sigma_it_le_log_abs_add_three_of_one_add_le` / `ZeroFreeRegion.exists_norm_neg_logDeriv_riemannZeta_sigma_two_it_le_log_abs_add_three_of_one_add_le` | `lemma` | Signed coordinate fixed-margin bounds at `σ+it` and `σ+2it` in the `C log(|t|+3)` scale. | Lets fixed-margin Borel/Jensen-facing estimates stay in `-logDeriv ζ` notation before exact high-height normalization. |
| `ZeroFreeRegion.exists_norm_neg_logDeriv_riemannZeta_sigma_it_le_log_abs_of_fixed_margin` / `ZeroFreeRegion.exists_norm_neg_logDeriv_riemannZeta_sigma_two_it_le_log_abs_of_fixed_margin` | `lemma` | Signed fixed-margin versions of the same exact high-height norm bounds. | Keeps the proved fixed-margin estimates available in the `-logDeriv ζ` convention used by the 3-4-1 and zero-repulsion chain. |
| `ZeroFreeRegion.exists_re_neg_deriv_div_riemannZeta_sigma_it_le_log_abs_add_three_of_one_add_le` | `lemma` | Converts the fixed-margin `σ+it` norm bound into the real-part quotient form `Re(-ζ'/ζ(σ+it)) ≤ C log(|t|+3)`. | Gives the second 3-4-1 term in the project's classical sign convention on any fixed-margin half-plane. |
| `ZeroFreeRegion.exists_norm_logDeriv_riemannZeta_sigma_two_it_le_log_abs_add_three_of_one_add_le` / `ZeroFreeRegion.exists_re_neg_deriv_div_riemannZeta_sigma_two_it_le_log_abs_add_three_of_one_add_le` | `lemma` | Specializes the fixed-margin bound to the shifted 3-4-1 point `σ+2it`, giving norm and real-part bounds by `C log(|t|+3)` when `1+ε ≤ σ`. | Shows the third 3-4-1 term is controlled on any fixed-margin half-plane; the classical chain still needs the corresponding boundary-strip estimate. |
| `ZeroFreeRegion.exists_re_neg_deriv_div_riemannZeta_fixed_margin_three_four_one_bounds` | `lemma` | Packages the real-axis, `σ+it`, and `σ+2it` real-part bounds under one constant `C log(|t|+3)` for every fixed `ε > 0`. | One-entry fixed-margin estimate for all three terms of the 3-4-1 expression; useful for local arguments but still not the moving-boundary estimate needed for `c/log|t|`. |
| `ZeroFreeRegion.exists_three_four_one_combination_le_log_abs_add_three_of_one_add_le` | `lemma` | Proves the full 3-4-1 combination is nonnegative and bounded above by `C log(|t|+3)` on each fixed-margin half-plane. | Couples the proved 3-4-1 nonnegativity theorem with the fixed-margin vertical estimates. |
| `ZeroFreeRegion.exists_norm_logDeriv_riemannZeta_fixed_margin_shift_pair_le_log_abs` / `..._neg_logDeriv...` | `lemma` | Packages the proved fixed-margin high-height estimates into one shared `C log |t|` bound for both `σ+it` and `σ+2it`, still under `1+ε ≤ σ ≤ 2`. | Gives a verified fixed-margin analogue of the missing boundary-strip pair estimate, without weakening the claim boundary. |
| `ZeroFreeRegion.exists_re_neg_deriv_div_riemannZeta_fixed_margin_shift_pair_le_log_abs` | `lemma` | Converts that fixed-margin pair norm package into shared real-part quotient bounds for the two shifted 3-4-1 terms. | Provides the exact sign/norm handoff used by the 3-4-1 chain on fixed-margin half-planes. |
| `ZeroFreeRegion.exists_three_four_one_combination_le_log_abs_of_fixed_margin` | `lemma` | Upgrades the fixed-margin full 3-4-1 combination upper bound from `log(|t|+3)` to the high-height scale `C log |t|`. | Strongest currently proved fixed-margin full-combination growth statement; it is still not the classical moving-boundary estimate. |
| `ZeroFreeRegion.trig_identity_nonneg` | `lemma` | Proves `3 + 4 cos θ + cos(2θ) ≥ 0` via `2(1+cos θ)^2`. | Pointwise nonnegativity input for the de la Vallee Poussin combination. |
| `ZeroFreeRegion.log_deriv_zeta_nonneg_combination` | `lemma` | Proves `3 Re(-ζ'/ζ(σ)) + 4 Re(-ζ'/ζ(σ+it)) + Re(-ζ'/ζ(σ+2it)) ≥ 0` for `σ > 1`. | Primary 3-4-1 theorem. |
| `ZeroFreeRegion.log_deriv_zeta_finset_series_identity` | `lemma` | Expands any finite logarithmic-derivative detector combination into one von Mangoldt Dirichlet series weighted by the corresponding finite cosine polynomial. | Removes the manual `hseries` input for finite detector combinations in the absolute-convergence half-plane. |
| `ZeroFreeRegion.log_deriv_zeta_nonneg_finset_combination` / `...list_combination` | `lemma` | General finite trigonometric-detector skeleton: a finite logarithmic-derivative combination is nonnegative once it is identified with a von Mangoldt series weighted by a nonnegative trigonometric polynomial. | Abstracts the finite algebraic core behind possible Stechkin/Heath-Brown detector variants. |
| `ZeroFreeRegion.finset_weighted_nonneg_term_lower_bound` | `lemma` | Isolates a selected term from a nonnegative finite weighted sum: if `0 ≤ ∑ a_k x_k` and `a_m > 0`, then `x_m ≥ -(∑_{k≠m} a_k x_k)/a_m`. | Algebraic step for turning finite detector nonnegativity into a lower bound for one chosen log-derivative term. |
| `ZeroFreeRegion.log_deriv_zeta_term_lower_bound_of_finset_detector` / `log_deriv_zeta_bty_first_shift_lower_bound` | `lemma` | Turns a nonnegative finite trigonometric detector into a lower bound for a selected shifted log-derivative term, with a concrete BTY degree-16 specialization at `k=1`. | Higher-degree analogue of the classical 3-4-1 lower-bound rearrangement. |
| `ZeroFreeRegion.finite_weighted_sum_single_lower_bound` / `...of_upper_bounds` / `...of_uniform_upper_bound` | `lemma` | Isolates a selected term from a nonnegative finite weighted sum, and optionally absorbs pointwise or uniform upper bounds for the remaining terms when their coefficients are nonnegative. | Algebraic step for turning finite detector nonnegativity into a lower bound for one chosen log-derivative term. |
| `ZeroFreeRegion.log_deriv_zeta_nonneg_finset_combination_auto` / `...list_combination_auto` | `lemma` | Automatic finite detector versions: the series identity is discharged from `log_deriv_zeta_re_series`, leaving only the finite trigonometric-polynomial nonnegativity hypothesis. | First reusable Lean step toward higher-degree de la Vallee Poussin/Stechkin detector polynomials. |
| `ZeroFreeRegion.trigPolynomial_nonneg_of_sq_certificate` / `...auto_of_sq_certificate` | `lemma` | Turns a finite cosine-square certificate for a detector polynomial into pointwise nonnegativity and then into the automatic finite detector inequality. | First certificate hook for detector nonnegativity. |
| `ZeroFreeRegion.ComplexExpAbsSqCertificate` / `...complex_exp_abs_sq_certificate` | `abbrev` / `lemma` | Packages the certificate shape `P(θ)=‖∑ c_k exp(i k θ)‖²` and feeds it into the automatic finite detector theorem. | Matches the certificate style used by high-degree nonnegative trigonometric polynomials in Heath-Brown/Bellotti-Trudgian-Yang style arguments. |
| `ZeroFreeRegion.ScaledComplexExpAbsSqCertificate` / `...scaled_complex_exp_abs_sq_certificate` / `...single_lower_bound_of_scaled_complex_exp_abs_sq_certificate` | `abbrev` / `lemma` | Packages the scaled certificate shape `scale * P(θ)=‖∑ c_k exp(i k θ)‖²`, derives detector nonnegativity when `scale > 0`, and feeds it directly into selected-term lower-bound extraction with optional shifted upper bounds. | Avoids square-root coefficients and matches integer-coefficient detector tables. |
| `ZeroFreeRegion.btyRawCoeff` / `btyDetectorCoeff_zero` / `btyDetectorCoeff_one` / `btyDetectorCoeff_sum_one_to_K` / `btyDetectorCoeff_eq_zero_of_seventeen_le` | `def` / `lemma` | Encodes the Bellotti-Trudgian-Yang degree-16 exponential-square detector coefficient table, checks `a_0 = 1`, `a_1 = 865534 / 497079`, `∑_{1≤k≤16} a_k = 2919857 / 828465`, and proves coefficients vanish above degree `16`. | Concrete high-degree detector data sits behind the reusable finite-detector certificate API. |
| `ZeroFreeRegion.norm_sq_sum_real_coeff_complex_exp_eq_double_sum` / `btyScaledComplexExpAbsSqCertificate` / `log_deriv_zeta_nonneg_bty_detector_from_scaled_certificate` | `lemma` | Expands a finite real-coefficient exponential-square norm as a double cosine sum, proves the full scaled BTY certificate, and feeds it into the automatic finite log-derivative detector theorem. | Gives a checked high-degree detector instance beyond the base 3-4-1 polynomial. |
| `ZeroFreeRegion.btyDetectorCoeff_nonneg_of_mem_support` / `btyDetectorCoeff_sum_support_erase_one` / `btyDetectorCoeff_mixed_center_sum` / `log_deriv_zeta_bty_detector_one_lower_bound_of_uniform_shift_upper_bound` / `..._simplified` | `lemma` | Proves BTY support coefficients are nonnegative/positive, computes the coefficient sum excluding `k=1` as `6917296 / 2485395`, computes the mixed center/nonzero sum as `B0 + (4431901 / 2485395) L`, and turns uniform upper bounds into lower bounds for `Re(-ζ'/ζ(σ+it))`, including the simplified coefficient `3458648 / 2163835`. | Direct algebraic handoff from the checked BTY detector to future high-height shifted log-derivative estimates. |
| `ZeroFreeRegion.log_deriv_zeta_bty_detector_one_lower_bound_of_center_and_LogDerivVerticalLogBound` / `..._simplified` | `lemma` | Applies the named high-height vertical bound to all nonzero BTY detector frequencies and takes a separate real-axis `k=0` upper bound; the simplified form evaluates the finite coefficient sum. | Removes the finite-frequency bookkeeping from the BTY route while keeping the true zeta-specific vertical estimate and central-term bound explicit. |
| `ZeroFreeRegion.exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_LogDerivVerticalLogBound` / `..._simplified` | `lemma` | Uses the existing fixed-margin `Re(s) >= 1 + ε` estimate to discharge the real-axis `k=0` center term, while keeping `LogDerivVerticalLogBound` for nonzero detector frequencies; the simplified form evaluates the finite coefficient sum. | Gives a cleaner fixed-margin BTY route; the classical boundary case still needs the real high-height vertical estimate. |
| `ZeroFreeRegion.log_deriv_zeta_bty_detector_one_lower_bound_of_center_and_ReNegDerivDivVerticalLogBound` / fixed-margin variants | `lemma` | Direct BTY handoff from the named real-part quotient vertical bound, including finite coefficient simplifications and fixed-margin center discharge. | Allows the detector route to use a future `Re(-ζ'/ζ)` estimate without first proving a stronger norm bound. |
| `ZeroFreeRegion.log_deriv_zeta_nonneg_three_four_one_from_finset` | `lemma` | Re-exposes the existing 3-4-1 theorem as the base finite-detector instance. | Keeps the generalized detector API tied to the verified 3-4-1 result. |
| `ZeroFreeRegion.log_deriv_zeta_lower_bound` | `lemma` | Rearranges the 3-4-1 inequality into the lower bound for `Re(-ζ'/ζ(σ+it))`. | Algebraic corollary used by the future quantitative zero-free-region chain. |
| `ZeroFreeRegion.logDeriv_riemannZeta_eq_deriv_div` / `ZeroFreeRegion.neg_logDeriv_riemannZeta_re_eq_neg_deriv_div_re` | `lemma` | Bridges Mathlib's `logDeriv ζ` notation with the classical `ζ'/ζ` and `-ζ'/ζ` quotient notation, including real-part and norm forms. | Lets future Borel/Jensen `logDeriv` estimates rewrite directly into the 3-4-1 sign convention. |
| `ZeroFreeRegion.reNegDerivDivVerticalLogBound_of_negLogDerivVerticalLogBound` / `negLogDerivVerticalLogBound_mono_height` | `lemma` | Converts the named signed vertical norm interface directly to the `Re(-ζ'/ζ)` interface and proves the signed interface is stable under raising the high-height cutoff. | Removes a small sign-convention and cutoff-management step from the future quantitative zero-free-region assembly. |
| `ZeroFreeRegion.sigmaOf_log_gt_one` | `lemma` | Proves `1 < 1 + a / log |t|` above height `2` when `a > 0`. | Real-variable input for the standard high-height choice of `σ`. |
| `ZeroFreeRegion.sigmaOf_log_le_two` | `lemma` | Proves `1 + a / log |t| ≤ 2` above height `2` when `a ≤ log 2`. | Supplies the `σ ≤ 2` side condition for the 3-4-1 assembly. |
| `ZeroFreeRegion.sigmaOf_log_sub_pos` | `lemma` | Proves `(1 + a / log |t|) - β > 0` whenever `β < 1`. | Supplies the zero-separation side condition in the 3-4-1 contradiction. |
| `ZeroFreeRegion.sigmaOf_log_le_one_add` | `lemma` | Proves `1 + a / log |t| ≤ 1 + d` from `a ≤ d log 2`. | Connects the standard high-height choice to local right-neighborhood bounds near `1`. |
| `ZeroFreeRegion.three_four_one_sigmaOf_log_margin` | `lemma` | Proves the pure real-variable negativity margin for `σ = 1 + a / log |t|`. | Turns shifted log-derivative bounds into the strict negative upper bound needed by the 3-4-1 contradiction. |
| `ZeroFreeRegion.exists_sigmaOf_log_margin_constants` | `lemma` | Chooses positive `a,c` satisfying `a ≤ log 2`, `a ≤ d log 2`, and `3C/a+K < 4/(a+c)` when `1<C<4/3`. | Removes the remaining constant-choice algebra from the high-height zero-free assembly. |
| `ZeroFreeRegion.exists_sigmaOf_log_margin_constants_for_shift_bounds` | `lemma` | Specializes the constant choice to the shifted-estimate margin `3C/a + 4*Czero + Ctwo < 4/(a+c)` when `Czero,Ctwo ≥ 0`. | Lets future shifted log-derivative estimates feed the 3-4-1 closure without restating `K = 4*Czero + Ctwo`. |
| `ZeroFreeRegion.exists_sigmaOf_log_margin_constants_same_const` | `lemma` | Specializes the margin constants to a single nonnegative coefficient `B`, giving `3C/a + 5B < 4/(a+c)`. | Direct constant package for the same-coefficient shifted-estimate closure. |
| `ZeroFreeRegion.residue_bounds` | `lemma` | Proves `1 < (σ-1) Re(ζ(σ)) ≤ σ` for `σ > 1`. | Real-axis residue-scale control near the pole at `1`. |
| `ZeroFreeRegion.classical_zero_free_region_compact` | `theorem` | For every `T ≥ 2`, proves existence of `d > 0` such that `ζ(s) ≠ 0` whenever `|Im(s)| ≤ T` and `Re(s) ≥ 1-d`. | Compact zero-free strip, the topological output of Mathlib nonvanishing plus openness/compactness. |
| `ZeroFreeRegion.meromorphicAt_riemannZeta_one` | `lemma` | Proves ζ is meromorphic at its pole `s = 1` by rewriting it as an analytic regular part plus `(s-1)⁻¹ / Γℝ(s)`. | Supplies the local meromorphic input needed by divisor, residue, and logarithmic-derivative infrastructure. |
| `ZeroFreeRegion.meromorphicOn_riemannZeta_closedBall` | `lemma` | Proves ζ is meromorphic on every closed ball. | Rectangle/Jensen/Perron infrastructure hook for the zero-free and explicit-formula chains. |
| `ZeroFreeRegion.meromorphicOrderAt_riemannZeta_one` | `lemma` | Proves `meromorphicOrderAt riemannZeta 1 = -1`. | Records that the pole at `1` is simple in Mathlib's meromorphic-order API. |
| `ZeroFreeRegion.divisor_riemannZeta_pole_one` | `lemma` | Proves `(MeromorphicOn.divisor riemannZeta U) 1 = -1` for any meromorphic domain `U` containing `1`. | Enables divisor/residue bookkeeping for Jensen, rectangle-residue, and log-derivative work. |
| `ZeroFreeRegion.eventually_ne_zero_riemannZeta_nhdsNE_one` | `lemma` | Proves ζ is eventually nonzero in the punctured neighborhood of its pole `1`. | Supplies the local denominator condition needed for `ζ'/ζ` manipulations near the pole. |
| `ZeroFreeRegion.analyticAt_logDeriv_riemannZetaPoleUnitAtOne` | `lemma` | Proves the logarithmic derivative of the analytic pole unit is analytic at `1`. | Makes the regular term in the simple-pole decomposition available as an analytic object. |
| `ZeroFreeRegion.eventually_norm_logDeriv_riemannZetaPoleUnitAtOne_le_const` | `lemma` | Proves `‖logDeriv(unit)(s)‖` is locally bounded near `1`. | Supplies the bounded regular part in the pole-side `ζ'/ζ` estimate. |
| `ZeroFreeRegion.eventuallyEq_logDeriv_riemannZeta_simplePoleAtOne` | `lemma` | Proves near `1`, `logDeriv ζ(s) = -(s-1)⁻¹ + logDeriv(unit)(s)` on the punctured neighborhood. | Separates the simple-pole principal part from a bounded analytic-unit contribution. |
| `ZeroFreeRegion.eventuallyEq_inv_riemannZeta_simpleZeroAtOne` | `lemma` | Rewrites `1/ζ(s)` near `1` as `(s-1)` times the inverse pole unit. | Converts the simple pole of ζ into a simple-zero model for reciprocal/log-derivative work. |
| `ZeroFreeRegion.analyticAt_riemannZetaReciprocalModelAtOne` | `lemma` | Proves the reciprocal local model `(s-1) * unit(s)⁻¹` is analytic at `1`. | Gives an analytic replacement for Mathlib's global reciprocal at the pole value. |
| `ZeroFreeRegion.deriv_riemannZetaReciprocalModelAtOne_one` | `lemma` | Proves the reciprocal local model has derivative `1` at `1`. | Records that `1/ζ` has the expected simple-zero local model. |
| `ZeroFreeRegion.tendsto_mul_logDeriv_inv_riemannZeta_simpleZeroAtOne` | `lemma` | Proves `(s-1) * logDeriv (1/ζ)(s) → 1` in the punctured neighborhood of `1`. | Converts the reciprocal simple-zero model into a logarithmic-residue statement. |
| `ZeroFreeRegion.tendsto_mul_logDeriv_riemannZeta_simplePoleAtOne` | `lemma` | Proves `(s-1) * logDeriv ζ(s) → -1` in the punctured neighborhood of `1`. | Principal-part input for future Borel-Caratheodory/Jensen estimates on `ζ'/ζ`. |
| `ZeroFreeRegion.eventually_norm_logDeriv_riemannZeta_le_two_div_norm_sub_one` | `lemma` | Proves eventually near `1`, `‖logDeriv ζ(s)‖ ≤ 2 / ‖s-1‖`. | Local pole-order bound that can feed later quantitative estimates. |
| `ZeroFreeRegion.eventually_norm_mul_logDeriv_riemannZeta_lt_const` | `lemma` | For every `C > 1`, proves `‖(s-1) logDeriv ζ(s)‖ < C` eventually near `1`. | Flexible local constant management from the principal-part limit. |
| `ZeroFreeRegion.eventually_norm_logDeriv_riemannZeta_lt_const_div_norm_sub_one` | `lemma` | For every `C > 1`, proves `‖logDeriv ζ(s)‖ < C / ‖s-1‖` eventually near `1`. | Flexible version of the local pole-order bound. |
| `ZeroFreeRegion.eventually_norm_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one` | `lemma` | Rewrites the eventual local bound in quotient notation `ζ'/ζ`. | Filter-level input for estimates stated with the analytic quotient. |
| `ZeroFreeRegion.eventually_norm_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one` | `lemma` | For every `C > 1`, rewrites the flexible eventual local bound in quotient notation `ζ'/ζ`. | Flexible filter-level quotient input for later local estimates. |
| `ZeroFreeRegion.eventually_norm_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one` | `lemma` | Rewrites the eventual local bound for `-ζ'/ζ`. | Filter-level input matching the sign convention of the 3-4-1 chain. |
| `ZeroFreeRegion.eventually_norm_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one` | `lemma` | For every `C > 1`, rewrites the flexible eventual local bound for `-ζ'/ζ`. | Flexible signed quotient input matching the 3-4-1 sign convention. |
| `ZeroFreeRegion.eventually_abs_re_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one` | `lemma` | Bounds `|Re(-ζ'/ζ)(s)|` by `2 / ‖s-1‖` eventually near `1`. | Filter-level real-part control for later 3-4-1 estimates. |
| `ZeroFreeRegion.eventually_abs_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one` | `lemma` | For every `C > 1`, bounds `|Re(-ζ'/ζ)(s)|` by `C / ‖s-1‖` eventually near `1`. | Flexible real-part input for later local 3-4-1 estimates. |
| `ZeroFreeRegion.eventually_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one` | `lemma` | For every `C > 1`, proves `Re(-ζ'/ζ)(s) < C / ‖s-1‖` eventually near `1`. | One-sided upper bound used directly by later 3-4-1 estimates. |
| `ZeroFreeRegion.exists_punctured_ball_norm_logDeriv_riemannZeta_le_two_div_norm_sub_one` | `lemma` | Packages the same local bound as a concrete punctured ball around `1`. | Disk-shaped input for future local Borel-Caratheodory/Jensen estimates. |
| `ZeroFreeRegion.exists_punctured_closedBall_norm_logDeriv_riemannZeta_le_two_div_norm_sub_one` | `lemma` | Packages the local pole-order bound on a smaller closed punctured ball around `1`. | Closed-disk input for future compact local Borel-Caratheodory/Jensen estimates. |
| `ZeroFreeRegion.exists_punctured_closedBall_norm_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one` | `lemma` | Rewrites the closed-ball local bound in quotient notation `ζ'/ζ`. | Direct input for estimates stated with the analytic quotient instead of `logDeriv`. |
| `ZeroFreeRegion.exists_punctured_closedBall_norm_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one` | `lemma` | For every `C > 1`, gives the closed punctured-ball flexible quotient bound for `ζ'/ζ`. | Flexible closed-disk quotient input. |
| `ZeroFreeRegion.exists_punctured_closedBall_norm_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one` | `lemma` | Rewrites the closed-ball local bound for `-ζ'/ζ`. | Matches the sign convention used in the 3-4-1 inequality and future contradiction estimates. |
| `ZeroFreeRegion.exists_punctured_closedBall_norm_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one` | `lemma` | For every `C > 1`, gives the closed punctured-ball flexible quotient bound for `-ζ'/ζ`. | Flexible closed-disk signed quotient input. |
| `ZeroFreeRegion.exists_punctured_closedBall_abs_re_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one` | `lemma` | Bounds `|Re(-ζ'/ζ)(s)|` by `2 / ‖s-1‖` on a closed punctured ball. | Closed-disk real-part control for compact local estimates. |
| `ZeroFreeRegion.exists_punctured_closedBall_abs_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one` | `lemma` | For every `C > 1`, gives the closed punctured-ball real-part bound with constant `C`. | Flexible closed-disk real-part control for compact local estimates. |
| `ZeroFreeRegion.exists_punctured_closedBall_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one` | `lemma` | For every `C > 1`, gives the closed punctured-ball one-sided real-part upper bound. | Closed-disk one-sided input for compact local estimates. |
| `ZeroFreeRegion.exists_rightNeighborhood_norm_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_sub_one` | `lemma` | Proves `‖-ζ'/ζ(σ)‖ ≤ 2 / (σ-1)` for real `σ > 1` sufficiently close to `1`. | Concrete real-axis norm input for local 3-4-1 estimates. |
| `ZeroFreeRegion.exists_rightNeighborhood_abs_re_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_sub_one` | `lemma` | Proves `|Re(-ζ'/ζ)(σ)| ≤ 2 / (σ-1)` for real `σ > 1` sufficiently close to `1`. | Concrete real-axis real-part input for local 3-4-1 estimates. |
| `ZeroFreeRegion.exists_rightNeighborhood_re_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_sub_one` | `lemma` | Proves `Re(-ζ'/ζ)(σ) ≤ 2 / (σ-1)` for real `σ > 1` sufficiently close to `1`. | Concrete one-sided real-axis upper bound for local 3-4-1 estimates. |
| `ZeroFreeRegion.exists_rightNeighborhood_re_neg_deriv_riemannZeta_div_riemannZeta_le_inv_sub_one_add_const` | `lemma` | Proves `Re(-ζ'/ζ)(σ) ≤ 1/(σ-1)+M` for real `σ > 1` sufficiently close to `1`. | Additive principal-part form of the pole-side real-axis input, closer to the classical de la Vallee Poussin bookkeeping than the coarser `C/(σ-1)` wrappers. |
| `ZeroFreeRegion.exists_rightNeighborhood_hreal_two_div_sub_one` | `lemma` | Packages the concrete bound as the `hreal` input shape for any future `σOf t` staying in a right neighborhood of `1`. | Discharges the real-axis term of `three_four_one_zero_free_high_height_of_log_deriv_bounds` from local pole control. |
| `ZeroFreeRegion.exists_sigmaOf_log_hreal_two_div_sub_one` | `lemma` | Specializes the concrete `hreal` bound to `σOf t = 1 + a / log |t|` for sufficiently small `a`. | Direct real-axis input for the standard high-height 3-4-1 setup. |
| `ZeroFreeRegion.exists_sigmaOf_log_hreal_two_mul_log_div` | `lemma` | Rewrites that concrete bound as `≤ 2 * log |t| / a`. | Converts the pole denominator into the vertical-height scale used in the quantitative strip. |
| `ZeroFreeRegion.exists_sigmaOf_log_hreal_inv_sub_one_add_const_log_bound` | `lemma` | Specializes the additive pole-side bound to `σ = 1 + a/log|t|`, giving `≤ (1/a + M/log 2) log |t|`. | Separates the singular `1/a` contribution from the bounded regular pole-unit contribution on the standard high-height scale. |
| `ZeroFreeRegion.exists_rightNeighborhood_norm_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_sub_one` | `lemma` | For every `C > 1`, proves `‖-ζ'/ζ(σ)‖ < C / (σ-1)` for real `σ > 1` sufficiently close to `1`. | Real-axis norm input for local 3-4-1 estimates. |
| `ZeroFreeRegion.exists_rightNeighborhood_abs_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_sub_one` | `lemma` | For every `C > 1`, proves `|Re(-ζ'/ζ)(σ)| < C / (σ-1)` for real `σ > 1` sufficiently close to `1`. | Real-axis local input for the 3-4-1 contradiction estimates. |
| `ZeroFreeRegion.exists_rightNeighborhood_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_sub_one` | `lemma` | For every `C > 1`, proves `Re(-ζ'/ζ)(σ) < C / (σ-1)` for real `σ > 1` sufficiently close to `1`. | Direct real-axis upper bound for the 3-4-1 contradiction estimates. |
| `ZeroFreeRegion.exists_rightNeighborhood_hreal_const_div_sub_one` | `lemma` | For every `C > 1`, packages the flexible bound as the `hreal` input shape for any future `σOf t` staying in a right neighborhood of `1`. | Flexible real-axis input for the high-height 3-4-1 assembly. |
| `ZeroFreeRegion.exists_sigmaOf_log_hreal_const_div_sub_one` | `lemma` | For every `C > 1`, specializes the flexible `hreal` bound to `σOf t = 1 + a / log |t|` for sufficiently small `a`. | Flexible real-axis input for the standard high-height 3-4-1 setup. |
| `ZeroFreeRegion.exists_sigmaOf_log_hreal_const_mul_log_div` | `lemma` | For every `C > 1`, rewrites the flexible bound as `≤ C * log |t| / a`. | Flexible vertical-height real-axis input for the standard high-height setup. |
| `ZeroFreeRegion.exists_sigmaOf_log_two_t_norm_bound_const_mul_log_div` / `ZeroFreeRegion.exists_sigmaOf_log_two_t_bound_const_mul_log_div` | `lemma` | Uses the half-plane L-series norm bound to control the `σ+2it` point by `≤ C * log |t| / a`. | Records the honest absolute-convergence bound and its `1/a` loss; the classical target still needs a height-independent `O(log |t|)` vertical estimate. |
| `ZeroFreeRegion.exists_sigma_ge_sigmaOf_log_norm_bound_const_mul_log_div` / `ZeroFreeRegion.exists_sigma_ge_sigmaOf_log_re_neg_deriv_div_bound_const_mul_log_div` | `lemma` | Extends the same weak absolute-convergence control from the standard point `σ = 1 + a/log|t|` to the moving half-strip `1+a/log|t| ≤ σ ≤ 2`. | Gives a real moving-strip theorem rather than a point wrapper, while still explicitly retaining the `1/a` loss that blocks the classical zero-free strip. |
| `ZeroFreeRegion.exists_sigma_ge_sigmaOf_log_any_im_norm_bound_const_mul_log_div` / `ZeroFreeRegion.exists_sigma_ge_sigmaOf_log_any_im_re_neg_deriv_div_bound_const_mul_log_div` | `lemma` | Allows the estimated point to have arbitrary imaginary coordinate `u`, with `t` still controlling the scale `log |t|` and the lower edge `1+a/log|t|`. | Makes the weak moving-strip estimate reusable for both `σ+it` and `σ+2it` terms without changing the height scale. |
| `ZeroFreeRegion.exists_sigma_ge_sigmaOf_log_two_t_norm_bound_const_mul_log_div` / `ZeroFreeRegion.exists_sigma_ge_sigmaOf_log_two_t_re_neg_deriv_div_bound_const_mul_log_div` | `lemma` | Specializes the arbitrary-imaginary moving-strip estimate to the exact `σ+2it` point used by the third 3-4-1 term. | Provides the most convenient weak `σ+2it` moving-strip API while preserving the explicit `1/a` obstruction. |
| `ZeroFreeRegion.exists_sigma_ge_sigmaOf_log_two_t_norm_bound_log_scale` / `ZeroFreeRegion.exists_sigma_ge_sigmaOf_log_two_t_re_neg_deriv_div_bound_log_scale` | `lemma` | Rewrites the weak `σ+2it` moving-strip estimate as `≤ B log|t|` for each fixed `a`, with `B = C/a`. | Matches the vertical-log API shape while making clear that the constant depends on the moving-strip parameter and is not the missing uniform estimate. |
| `ZeroFreeRegion.exists_sigma_ge_sigmaOf_log_any_im_norm_bound_log_scale` / `ZeroFreeRegion.exists_sigma_ge_sigmaOf_log_any_im_re_neg_deriv_div_bound_log_scale` / `ZeroFreeRegion.exists_sigma_ge_sigmaOf_log_shift_pair_re_neg_deriv_div_bound_log_scale` | `lemma` | Repackages the arbitrary-imaginary weak estimate and gives a shared-constant bound for both `σ+it` and `σ+2it`. | Provides a direct comparison object for the future shifted estimates: the API shape is right, but the constant still has the `1/a` loss. |
| `ZeroFreeRegion.exists_sigma_ge_sigmaOf_log_neg_logDeriv_norm_bound_const_mul_log_div` / `ZeroFreeRegion.exists_sigma_ge_sigmaOf_log_any_im_neg_logDeriv_norm_bound_const_mul_log_div` / `ZeroFreeRegion.exists_sigma_ge_sigmaOf_log_two_t_neg_logDeriv_norm_bound_const_mul_log_div` | `lemma` | Adds signed `-logDeriv ζ` norm variants of the weak moving-strip estimates, including arbitrary-imaginary and `σ+2it` forms. | Keeps the public API aligned with the 3-4-1 sign convention while preserving the same explicit `1/a` loss. |
| `ZeroFreeRegion.exists_sigma_ge_sigmaOf_log_any_im_neg_logDeriv_norm_bound_log_scale` / `ZeroFreeRegion.exists_sigma_ge_sigmaOf_log_two_t_neg_logDeriv_norm_bound_log_scale` | `lemma` | Rewrites the signed weak moving-strip norm variants as `≤ B log|t|` for fixed `a`, with `B = C/a`. | Useful comparison interface for future vertical estimates; still not the missing uniform `O(log |t|)` theorem. |
| `ZeroFreeRegion.sigmaOf_log_weak_two_t_margin_impossible` | `lemma` | Proves that if the `σ+2it` term keeps a `Ctwo/a` coefficient with `Ctwo ≥ 1`, then the required 3-4-1 constant inequality cannot hold for any positive width `c`. | Formalizes the obstruction: absolute convergence alone cannot close the de la Vallee Poussin `c/log|t|` strip. |
| `ZeroFreeRegion.no_sigmaOf_log_margin_constants_with_weak_two_t` | `lemma` | Existential version: no positive `a,c` satisfy the standard 3-4-1 margin when both real-axis and weak `σ+2it` coefficients are at least one. | Prevents the weak `σ+2it` theorem from being mistaken for the missing vertical-strip estimate. |
| `ZeroFreeRegion.sigmaOf_log_weak_shift_pair_margin_impossible` / `ZeroFreeRegion.no_sigmaOf_log_margin_constants_with_weak_shift_pair` | `lemma` | Shows the 3-4-1 margin also cannot close when both shifted terms only have a shared weak `C/a` coefficient. | Records the precise boundary of the shared weak moving-strip package. |
| `ZeroFreeRegion.exists_sigmaOf_log_classical_zero_free_region_of_log_deriv_bounds` | `lemma` | Packages the standard `σ(t)=1+a/log |t|` choice into the verified 3-4-1 and compact-patch assembly. | Reduces the classical zero-free target to the two shifted log-derivative estimates plus the negativity margin. |
| `ZeroFreeRegion.exists_sigmaOf_log_classical_zero_free_region_of_shift_bounds` | `lemma` | Specializes the closure theorem to shifted bounds of the form `-1/(σ-β)+Czero log|t|` and `Ctwo log|t|`. | Leaves exactly the two zeta-specific shifted estimates plus a constant inequality. |
| `ZeroFreeRegion.classical_zero_free_region_of_sigma_log_shift_estimates` | `lemma` | Combines local pole control, constant selection, the standard `σ=1+a/log|t|` choice, and compact patching. | Turns the classical zero-free target into exactly two shifted log-derivative estimates. |
| `ZeroFreeRegion.classical_zero_free_region_of_sigma_log_shift_estimates_nonneg_constants` | `lemma` | Same closure with individual nonnegativity hypotheses `Czero ≥ 0` and `Ctwo ≥ 0` instead of the bundled `0 ≤ 4*Czero + Ctwo`. | More ergonomic interface for future analytic estimates that naturally produce nonnegative constants. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_sigma_log_shift_estimates_nonneg_constants` | `lemma` | Existentially packages the general nonnegative shifted-estimate inputs with some `1 < C < 4/3`. | General single-entry conditional interface before fixing the real-axis coefficient. |
| `ZeroFreeRegion.classical_zero_free_region_of_sigma_log_shift_estimates_five_fourths` | `lemma` | Fixes the real-axis coefficient to `5/4`, which satisfies `1 < 5/4 < 4/3`. | Removes the abstract `C` range hypotheses from the shifted-estimate closure. |
| `ZeroFreeRegion.classical_zero_free_region_of_sigma_log_shift_estimates_five_fourths_nonneg_constants` | `lemma` | Fixed `5/4` closure with individual nonnegative shifted constants. | Shortest shifted-estimate closure before same-constant specialization. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_sigma_log_shift_estimates_five_fourths_nonneg_constants` | `lemma` | Existentially packages the fixed `5/4` nonnegative shifted-estimate inputs. | Single-entry conditional interface for future analytic estimates with separate constants. |
| `ZeroFreeRegion.classical_zero_free_region_of_sigma_log_shift_estimates_same_const` | `lemma` | Uses one nonnegative logarithmic coefficient `B` for both shifted estimates. | Most ergonomic conditional interface for the remaining zero-free-region analytic estimates. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_sigma_log_shift_estimates_same_const_high_height` | `lemma` | Existentially packages the same-constant shifted estimates above some sufficiently large height. | Lets future high-height analytic estimates feed the same-constant zero-free chain while compact patching handles bounded heights. |
| `ZeroFreeRegion.classical_zero_free_region_of_sigma_log_shift_estimates_same_const_at_two` | `lemma` | Fixes the height cutoff in the same-constant shifted-estimate closure to `2`. | Exact-height interface matching the statement of `classical_zero_free_region`. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_sigma_log_shift_estimates_same_const` | `lemma` | Packages the remaining analytic input as existence of one nonnegative `B` controlling both shifted estimates above height `2`. | Final conditional interface before proving the zeta-specific shifted logarithmic-derivative estimates. |
| `ZeroFreeRegion.classical_zero_free_region_of_regular_part_bound_and_two_t_bound` | `lemma` | Replaces the zero-candidate shifted estimate by a complex regular-part bound `Re(-ζ'/ζ)(s)+1/(Re(s)-Re(ρ)) ≤ B log |Im(s)|`, plus the `σ+2it` bound. | Direct bridge from the Borel-Caratheodory/Jensen-shaped analytic input to the classical zero-free target. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_regular_part_bound_and_two_t_bound` | `lemma` | Existentially packages the regular-part bound and the `σ+2it` bound under one nonnegative logarithmic coefficient. | Intermediate regular-part interface for the quantitative zero-free-region chain. |
| `ZeroFreeRegion.inv_sub_same_im_re` | `lemma` | Proves `Re((s-ρ)⁻¹)=1/(Re(s)-Re(ρ))` when `Im(ρ)=Im(s)` and `Re(s)>Re(ρ)`. | Algebraic conversion from complex regular parts to the real singular term in the zero-free contradiction. |
| `ZeroFreeRegion.re_neg_deriv_div_riemannZeta_add_inv_le_of_regular_part_norm` / `..._multiplicity_regular_part_norm` | `lemma` | Converts a pointwise norm bound on `-ζ'/ζ(s)+n(s-ρ)⁻¹` with `n≥1` into `Re(-ζ'/ζ(s))+1/(Re(s)-Re(ρ))≤M`. | Last-mile algebraic bridge from local principal-part estimates to the real zero-repulsion input; it is not itself the missing analytic estimate. |
| `ZeroFreeRegion.re_neg_logDeriv_riemannZeta_add_inv_le_of_regular_part_norm` / `..._multiplicity_regular_part_norm` | `lemma` | Same bridge in Mathlib's signed `-logDeriv ζ` notation. | Lets future Borel/Jensen local estimates feed the zero-free chain without rewriting quotient notation by hand. |
| `ZeroFreeRegion.re_neg_logDeriv_riemannZeta_sigma_it_add_inv_le_of_regular_part_norm` / `..._multiplicity_regular_part_norm` | `lemma` | Coordinate version for estimates stated at `s=σ+it`, `ρ=β+it`, with the principal part written as `((σ-β):ℂ)⁻¹`. | Matches the shape of future high-height estimates written directly in real variables. |
| `ZeroFreeRegion.re_neg_logDeriv_riemannZeta_sigma_it_add_inv_le_of_regular_part_norm_one_add_log` / `..._multiplicity_regular_part_norm_one_add_log` | `lemma` | Converts coordinate `C(1+log |t|)` regular-part bounds at `|t|≥3` into pure `2C log |t|` real-part bounds. | Normalizes common Big-O-style local estimates into the logarithmic coefficient shape consumed by the zero-free-region closures. |
| `ZeroFreeRegion.re_neg_logDeriv_riemannZeta_sigma_it_add_inv_le_of_regular_part_norm_log_abs_add_three` / `..._multiplicity_regular_part_norm_log_abs_add_three` | `lemma` | Converts coordinate `C log(|t|+3)` regular-part bounds at `|t|≥3` into pure `2C log |t|` real-part bounds. | Normalizes safe-height logarithmic local estimates before feeding shifted-estimate closures. |
| `ZeroFreeRegion.exists_eventually_norm_logDeriv_le_const_of_analyticAt_ne_zero` / `...neg_logDeriv...` | `lemma` | Proves local boundedness of `logDeriv g` and `-logDeriv g` for any analytic function nonzero at the center. | Discharges the bounded-unit input used by local principal-part separation. |
| `ZeroFreeRegion.exists_punctured_closedBall_norm_logDeriv_sub_order_mul_inv_le_of_analyticAt_order_eq_nat_auto` / signed and zeta-specific auto variants | `lemma` | Turns an analytic-order factorization directly into a punctured-ball regular-part norm bound with an internally chosen constant. | Removes the previous need to pass a manual `hregularBound` for local zeta-zero regular parts. |
| `ZeroFreeRegion.classical_zero_free_region_of_regular_part_norm_bound_and_two_t_bound` | `lemma` | Replaces the regular-part real estimate by the norm estimate `‖-ζ'/ζ(s)+(s-ρ)⁻¹‖ ≤ B log |Im(s)|`, plus the `σ+2it` bound. | Current narrowest conditional interface matching Borel/Jensen norm estimates. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_multiplicity_regular_part_norm_bound_and_two_t_bound` | `lemma` | Allows the future local estimate to isolate `-ζ'/ζ(s)+n(s-ρ)⁻¹` for some positive multiplicity `n`, then recovers the unit-principal real-part bound. | Avoids baking a simple-zero assumption into the conditional zero-free-region bridge. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_regular_part_norm_bound_and_two_t_bound` | `lemma` | Existentially packages the norm regular-part bound and the `σ+2it` bound under one nonnegative logarithmic coefficient. | Quotient-notation norm bridge before proving the zeta-specific estimates. |
| `ZeroFreeRegion.classical_zero_free_region_of_neg_logDeriv_regular_part_norm_bound_and_two_t_bound` | `lemma` | Same norm-bound closure written in Mathlib's natural `-logDeriv ζ` notation. | Lets future Borel/Jensen estimates feed the zero-free chain without manual quotient rewriting. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_multiplicity_neg_logDeriv_regular_part_norm_bound_and_two_t_bound` | `lemma` | Same multiplicity-aware closure written directly for `-logDeriv ζ` estimates. | Connects the local principal-part decomposition theorem to the zero-free-region bridge without quotient-rewrite boilerplate. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_bound_and_two_t_bound` | `lemma` | Existential `-logDeriv ζ` notation wrapper for the same norm-bound input. | Single-coefficient conditional interface for the quantitative zero-free-region path. |
| `ZeroFreeRegion.classical_zero_free_region_of_neg_logDeriv_regular_part_norm_bounds` | `lemma` | Allows separate nonnegative logarithmic coefficients for the regular-part norm estimate and the `σ+2it` estimate, then merges them by `max`. | Removes unnecessary same-constant bookkeeping from the remaining analytic estimates. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_bounds` | `lemma` | Existential two-coefficient version of the same `-logDeriv ζ` norm-bound closure. | Flexible interface when the `σ+2it` input is already a real-part estimate. |
| `ZeroFreeRegion.classical_zero_free_region_of_neg_logDeriv_regular_part_norm_and_two_t_norm_bounds` | `lemma` | Allows both remaining estimates to be supplied as norm bounds in `-logDeriv ζ` notation. | Matches the most common output shape of future Borel/Jensen estimates. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_and_two_t_norm_bounds` | `lemma` | Existential fully norm-bound version with separate nonnegative coefficients. | Analysis-facing interface when the `σ+2it` norm estimate is already specialized. |
| `ZeroFreeRegion.log_abs_two_mul_le_two_log_abs` | `lemma` | Proves `log |2t| ≤ 2 log |t|` for `|t| ≥ 2`. | Converts vertical estimates at height `2t` back to the `log |t|` scale in the zero-free target. |
| `ZeroFreeRegion.classical_zero_free_region_of_neg_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound` | `lemma` | Uses a regular-part norm estimate plus a general vertical-strip norm estimate `‖-logDeriv ζ(z)‖ ≤ B log |Im z|` on `1 ≤ Re z ≤ 2`. | Reduces the `σ+2it` input to a standard vertical-strip log-derivative growth estimate. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound` | `lemma` | Existential version of the regular-part plus vertical-strip norm estimate closure. | Highest-level conditional interface in the signed `-logDeriv ζ` convention. |
| `ZeroFreeRegion.classical_zero_free_region_of_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound` | `lemma` | Same closure in the natural local-zero convention `‖logDeriv ζ(s)-(s-ρ)⁻¹‖ ≤ B log |Im s|` plus a vertical norm bound for `logDeriv ζ`. | Removes sign-convention friction for future local principal-part estimates. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound` | `lemma` | Existential sign-convention wrapper for the positive `logDeriv ζ` regular-part and vertical-strip norm estimates. | Highest-level conditional interface in standard logarithmic-derivative notation. |
| `ZeroFreeRegion.classical_zero_free_region_of_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height` | `lemma` | High-height version of the positive `logDeriv ζ` regular-part plus vertical-strip norm closure, requiring the two analytic estimates only for `T0 ≤ |Im|` with `T0 ≥ 2`. | Lets future Borel/Jensen estimates proved only above a large height close the full classical target via the existing compact patch. |
| `ZeroFreeRegion.classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height` | `lemma` | Coordinate high-height version of the unit-principal positive `logDeriv ζ` regular-part closure, with inputs stated directly in `σ, β, t`. | Matches the most common future Borel/Jensen estimate shape before adding zero multiplicity bookkeeping. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height` | `lemma` | Existential wrapper for the unit-principal coordinate high-height closure. | Single-entry target when the regular-part and vertical estimates are produced together in real coordinates. |
| `ZeroFreeRegion.LogDerivRegularPartLogBound` / `ZeroFreeRegion.MultiplicityLogDerivRegularPartLogBound` | `abbrev : Prop` | Names the high-height zero-candidate regular-part `O(log |t|)` estimate, in simple-principal-part and multiplicity-aware forms. | Makes the second remaining hard analytic input as explicit as the vertical `LogDerivVerticalLogBound` interface. |
| `ZeroFreeRegion.classical_zero_free_region_of_LogDerivRegularPartLogBound_and_LogDerivVerticalLogBound` / multiplicity-aware variant | `lemma` | Assembles the named regular-part input and named vertical log-derivative input into `classical_zero_free_region`. | Proves the current Lean zero-free chain is closed modulo exactly those two zeta-specific high-height estimates. |
| `ZeroFreeRegion.classical_zero_free_region_of_LogDerivRegularPartLogBound_and_ReNegDerivDivVerticalLogBound` / multiplicity-aware variant | `lemma` | Assembles the named regular-part input with the direct real-part vertical bound for `Re(-ζ'/ζ)`. | Closes the final conditional chain from the exact 3-4-1 real-part input, avoiding an unnecessary vertical norm-strengthening requirement. |
| `ZeroFreeRegion.logDerivVerticalLogBound_mono_height` / `..._mono_const` / signed, real-part, and regular-part analogues | `lemma` | Shows the named high-height estimates remain valid after raising the cutoff or increasing the bound constant. | Lets independently proved analytic estimates with different `T0` and constant values be merged without changing the statement shape. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_LogDerivRegularPartLogBound_and_exists_LogDerivVerticalLogBound` / multiplicity-aware variant | `lemma` | Takes separate existential regular-part and vertical log-derivative bounds, possibly with different cutoffs, and derives `classical_zero_free_region`. | The cleanest current conditional statement: the classical target follows from exactly the two named high-height estimates. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_LogDerivRegularPartLogBound_and_exists_ReNegDerivDivVerticalLogBound` / multiplicity-aware variant | `lemma` | Existential version of the direct real-part final assembly, merging regular-part and real-part vertical cutoffs by `max`. | Lets a future `Re(-ζ'/ζ) ≤ C log |t|` estimate plug directly into the final conditional classical-zero-free target. |
| `ZeroFreeRegion.logDerivVerticalLogBound_of_high_height_log_abs_bound` / signed and real-part quotient variants | `lemma` | Packages a future high-height `B log |t|` estimate directly into the named vertical interfaces. | Removes the remaining API mismatch once the true zeta-specific high-height estimate is proved. |
| `ZeroFreeRegion.classical_zero_free_region_of_multiplicity_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height` | `lemma` | High-height closure whose regular-part input may isolate `n/(s-ρ)` for a positive zero multiplicity, plus the vertical-strip `logDeriv` norm bound. | Aligns the final high-height conditional interface with the multiplicity-weighted local principal-part decomposition, avoiding a hidden simple-zero assumption. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_multiplicity_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height` | `lemma` | Existential packaging of the multiplicity-aware high-height regular-part and vertical-strip norm inputs. | Single-entry high-height conditional interface for future multiplicity-aware Borel/Jensen estimates. |
| `ZeroFreeRegion.classical_zero_free_region_of_re_im_multiplicity_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height` | `lemma` | Coordinate version of the multiplicity-aware high-height closure, with estimates stated in real variables `σ, β, t`. | Lets future estimates written directly for `σ+it` and same-height zero candidates `β+it` feed the multiplicity-aware bridge. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_multiplicity_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height` | `lemma` | Existential coordinate wrapper for the multiplicity-aware high-height closure. | Most direct current interface for future high-height local principal-part and vertical `logDeriv` bounds. |
| `ZeroFreeRegion.classical_zero_free_region_of_re_im_multiplicity_logDeriv_regular_part_norm_one_add_log_bound_high_height` | `lemma` | Coordinate multiplicity-aware high-height closure from a single `C * (1 + log |t|)` bound. | Matches common big-O outputs while still carrying zero multiplicity in the local principal part. |
| `ZeroFreeRegion.classical_zero_free_region_of_re_im_multiplicity_logDeriv_regular_part_norm_one_add_log_bounds_high_height` | `lemma` | Coordinate multiplicity-aware high-height closure from separate regular-part and vertical `C * (1 + log |t|)` bounds. | Avoids forcing the same coefficient on the two remaining analytic estimates. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_multiplicity_logDeriv_regular_part_norm_one_add_log_bound_high_height` / `..._bounds_high_height` | `lemma` | Existential wrappers for the one-add-log multiplicity-aware coordinate closures. | Analysis-facing entry points for future high-height Borel/Jensen estimates. |
| `ZeroFreeRegion.classical_zero_free_region_of_re_im_multiplicity_neg_logDeriv_regular_part_norm_one_add_log_bound_high_height` / `..._bounds_high_height` | `lemma` | Signed `-logDeriv ζ` versions of the coordinate multiplicity-aware one-add-log closures. | Matches the sign convention of the 3-4-1 inequality and local principal-part separation. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_multiplicity_neg_logDeriv_regular_part_norm_one_add_log_bound_high_height` / `..._bounds_high_height` | `lemma` | Existential signed wrappers for the multiplicity-aware one-add-log coordinate closures. | Lets future signed high-height estimates feed the same zero-free-region bridge directly. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height` | `lemma` | Existential high-height wrapper for the same two positive `logDeriv ζ` estimates. | Final high-height conditional interface before proving the zeta-specific regular-part and vertical log-derivative bounds. |
| `ZeroFreeRegion.exists_norm_logDeriv_riemannZeta_vertical_log_bound_of_high_height_log_abs_bound` / `..._neg_logDeriv...` | `lemma` | Objective-shaped wrappers turning a future high-height `B log |t|` estimate on `1 ≤ σ ≤ 2` into the exact existential vertical-bound form. | Exposes the next hard lemma in the shape consumed by the quantitative zero-free-region chain, without claiming the zeta-specific estimate is proved. |
| `ZeroFreeRegion.exists_re_neg_deriv_div_riemannZeta_vertical_log_bound_of_norm_high_height_log_abs_bound` | `lemma` | Converts a future norm estimate for `logDeriv ζ(σ+it)` into the real-part quotient convention `Re(-ζ'/ζ)(σ+it) ≤ C log |t|`. | Removes sign/norm bookkeeping between Borel/Jensen-style estimates and the 3-4-1 inequality. |
| `ZeroFreeRegion.exists_norm_logDeriv_riemannZeta_shifted_vertical_log_bound_of_vertical_log_bound` / `...shifted_vertical_log_bound_of_vertical_norm_log_bound` | `lemma` | Derives the shifted `σ+2it` norm and real-part estimates from an ordinary vertical estimate at height `u`, absorbing `log |2t| ≤ 2 log |t|`. | Lets a single future vertical-strip growth theorem supply the third term in the 3-4-1 inequality. |
| `ZeroFreeRegion.exists_norm_logDeriv_riemannZeta_shift_pair_vertical_log_bound_of_vertical_log_bound` | `lemma` | Packages one future ordinary vertical estimate into one shared existential bound for both `σ+it` and `σ+2it`. | Gives the 3-4-1 route a single norm-bound handoff once the hard vertical `O(log |t|)` estimate is proved. |
| `ZeroFreeRegion.exists_norm_logDeriv_riemannZeta_shift_pair_vertical_log_bound_of_neg_vertical_log_bound` | `lemma` | Same pair package when the future ordinary vertical estimate is stated for `-logDeriv ζ`. | Aligns the vertical-bound handoff with the signed convention used by Borel/Jensen interfaces without adding a new analytic assumption. |
| `ZeroFreeRegion.exists_re_neg_deriv_div_riemannZeta_shift_pair_vertical_log_bound_of_vertical_norm_log_bound` | `lemma` | Converts that shared norm package into shared bounds for `Re(-ζ'/ζ)(σ+it)` and `Re(-ζ'/ζ)(σ+2it)`. | Provides the direct real-part 3-4-1 handoff from one future vertical `logDeriv` norm estimate. |
| `ZeroFreeRegion.exists_re_neg_deriv_div_riemannZeta_shift_pair_vertical_log_bound_of_neg_vertical_norm_log_bound` | `lemma` | Signed-input version of the same real-part pair handoff. | Lets future `-logDeriv ζ` norm estimates feed the 3-4-1 real-part quotient bounds directly. |
| `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_circleAverage_sub_const` | `lemma` | Rewrites the translated ValueDistribution log-counting difference for `logDeriv ζ(z+c)` as the circle average of `log ‖logDeriv ζ‖` on the disk centered at `c`, minus the translated trailing-coefficient term. | Connects Mathlib's zero-centered log-counting Jensen theorem to the off-center disks used in the zero-free-region chain. |
| `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_circleAverage` | `lemma` | Gives the same translated log-counting Jensen bridge for `-logDeriv ζ`, while rewriting the circle-average and trailing-coefficient terms into the unsigned `logDeriv ζ` convention. | Removes sign-convention friction between the 3-4-1 `-ζ'/ζ` side and the Jensen/log-counting divisor side. |
| `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_circleAverage_sub_const` / `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_circleAverage` | `lemma` | Specializes the translated log-counting Jensen bridge to disks centered at `σ+it`. | Gives future vertical-strip estimates a direct API in the coordinates used by the zero-free-region chain. |
| `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_localDivisor` / `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_localDivisor` | `lemma` | Rewrites the same translated log-counting difference directly to the closed-ball local-divisor side. | Connects zero-centered value-distribution log-counting to the divisor/trailing-coefficient quantities used by local Jensen estimates without an extra manual circle-average rewrite. |
| `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_localDivisor` / `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_localDivisor` | `lemma` | Specializes the local-divisor log-counting bridge to disks centered at `σ+it`. | Gives future high-height Jensen estimates a direct local-divisor API in the zero-free-region coordinates. |
| `ZeroFreeRegion.meromorphicTrailingCoeffAt_comp_add_const_zero` / `ZeroFreeRegion.log_norm_meromorphicTrailingCoeffAt_comp_add_const_zero` | `lemma` | Proves that translating `f` by `c` preserves the trailing coefficient at the translated center `0`. | Cancels the extra trailing-coefficient bookkeeping introduced by zero-centered log-counting. |
| `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_localDivisor_pure` / `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_localDivisor_pure` | `lemma` | Rewrites translated log-counting directly as the two local-divisor terms, with trailing coefficients cancelled. | Gives the cleanest current Jensen/log-counting handoff for future zero-count estimates. |
| `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_localDivisor_pure` / `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_localDivisor_pure` | `lemma` | Specializes the pure local-divisor bridge to disks centered at `σ+it`. | Direct high-height API for estimates in the zero-free-region coordinates. |
| `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_zero_of_divisor_eq_zero` / `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_eq_zero_of_divisor_eq_zero` | `lemma` | If the unsigned `logDeriv ζ` divisor vanishes on a closed ball, the translated log-counting difference is `0` for both `logDeriv ζ` and `-logDeriv ζ`. | Turns a local no-divisor hypothesis into the exact log-counting vanishing statement used by future Jensen estimates. |
| `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_zero_of_divisor_eq_zero` / `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_eq_zero_of_divisor_eq_zero` | `lemma` | Specializes the zero-divisor log-counting vanishing lemma to disks centered at `σ+it`. | Gives future high-height arguments a direct no-divisor-to-log-counting-zero API. |
| `ZeroFreeRegion.divisor_logDeriv_riemannZeta_closedBall_eq_zero_of_order_eq_zero` / `ZeroFreeRegion.divisor_logDeriv_riemannZeta_closedBall_eq_zero_of_analyticAt_ne_zero` | `lemma` | Converts pointwise order-zero, or analytic-and-nonzero, hypotheses for `logDeriv ζ` on a closed ball into vanishing of its local divisor. | Bridges analytic local hypotheses to the divisor condition consumed by the log-counting vanishing API. |
| `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_zero_of_order_eq_zero` / `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_eq_zero_of_order_eq_zero` | `lemma` | If `logDeriv ζ` has order zero on the local closed ball, the translated log-counting difference is `0` for both signs. | Removes one manual divisor step from future Jensen estimates in disks with no local zeros or poles of `logDeriv ζ`. |
| `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_zero_of_order_eq_zero` / `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_eq_zero_of_order_eq_zero` | `lemma` | Specializes the order-zero log-counting vanishing bridge to disks centered at `σ+it`. | Gives the high-height zero-free chain a direct local-order-to-log-counting-zero statement in vertical coordinates. |
| `ZeroFreeRegion.exists_eventuallyEq_sub_mul_unit_of_analyticAt_zero_deriv_ne_zero` / `ZeroFreeRegion.exists_eventuallyEq_logDeriv_sub_inv_of_analyticAt_zero_deriv_ne_zero` | `lemma` | Factors a simple analytic zero locally as `f z = (z - x) * g z`, then proves `logDeriv f z - (z-x)⁻¹ = logDeriv g z` on the punctured neighborhood. | First hard local algebra input for later bounding the regular part of `logDeriv ζ` near simple zeros; the missing global height estimate is still separate. |
| `ZeroFreeRegion.exists_eventuallyEq_neg_logDeriv_add_inv_of_analyticAt_zero_deriv_ne_zero` / `ZeroFreeRegion.exists_eventuallyEq_neg_logDeriv_riemannZeta_add_inv_of_simple_zero` | `lemma` | Gives the signed version `-logDeriv f z + (z-x)⁻¹ = -logDeriv g z`, with a ζ-specific simple-zero wrapper away from the pole. | Matches the `-ζ'/ζ + (s-ρ)⁻¹` regular-part shape consumed by the conditional zero-free-region bridge. |
| `ZeroFreeRegion.exists_eventuallyEq_logDeriv_sub_order_mul_inv_of_analyticAt_order_eq_nat` / `ZeroFreeRegion.exists_eventuallyEq_neg_logDeriv_riemannZeta_add_order_mul_inv_of_order_eq_nat` | `lemma` | Generalizes the local principal-part separation to arbitrary finite natural order `n`, giving `logDeriv f - n/(z-x)` and the signed zeta-specific `-logDeriv ζ + n/(z-ρ)` forms. | Removes the unnecessary simple-zero restriction from the local algebra layer; global Borel/Jensen height bounds remain the missing analytic input. |
| `ZeroFreeRegion.exists_punctured_ball_norm_logDeriv_sub_order_mul_inv_le_of_eventuallyEq` / `ZeroFreeRegion.exists_punctured_closedBall_norm_neg_logDeriv_add_order_mul_inv_le_of_eventuallyEq` | `lemma` | Converts an eventually-equal multiplicity regular part plus an eventual norm bound into an explicit punctured open/closed ball bound, in both signs. | Bridges local principal-part algebra to disk estimates without claiming the missing global height bound. |
| `ZeroFreeRegion.exists_punctured_ball_norm_logDeriv_riemannZeta_sub_order_mul_inv_le_of_order_eq_nat` / `ZeroFreeRegion.exists_punctured_closedBall_norm_neg_logDeriv_riemannZeta_add_order_mul_inv_le_of_order_eq_nat` | `lemma` | Zeta-specific bridges from `analyticOrderAt ζ ρ = n` and a local-unit logarithmic-derivative bound to punctured open/closed ball regular-part bounds, in both signs. | Connects multiplicity factorization to usable disk estimates once the local unit is bounded. |
| `ZeroFreeRegion.analyticAt_logDeriv_of_analyticAt_ne_zero` / `ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_of_ne_one_of_ne_zero` | `lemma` | Proves the logarithmic derivative is analytic wherever the original function is analytic and nonzero, with zeta-specific away-from-pole wrappers. | Supplies the natural analytic regularity input for the local divisor/log-counting vanishing bridges. |
| `ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_of_one_le_re_of_ne_one` / `ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_closedBall_of_ne_one_of_ne_zero` | `lemma` | Packages zeta nonvanishing on `Re(s) >= 1` and pointwise closed-ball hypotheses into analyticity of `logDeriv ζ`. | Lets right-half-plane and local closed-ball arguments feed the Jensen/log-counting layer without re-proving quotient analyticity. |
| `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_zero_of_analyticAt_ne_zero` / `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_eq_zero_of_analyticAt_ne_zero` | `lemma` | If `logDeriv ζ` is analytic and nonzero on the local closed ball, the translated log-counting difference is `0` for both signs. | Lets future local regularity estimates feed Jensen log-counting vanishing without manually proving divisor or order-zero hypotheses. |
| `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_zero_of_analyticAt_ne_zero` / `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_eq_zero_of_analyticAt_ne_zero` | `lemma` | Specializes the analytic-and-nonzero log-counting vanishing bridge to disks centered at `σ+it`. | Direct vertical-coordinate API for disks where `logDeriv ζ` is locally regular and nonvanishing. |
| `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_zero_of_one_le_re_of_ne_one_of_logDeriv_ne_zero` / `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_eq_zero_of_one_le_re_of_ne_one_of_logDeriv_ne_zero` | `lemma` | On local closed balls in `Re(s) >= 1` avoiding the pole, nonvanishing of `logDeriv ζ` implies translated log-counting vanishes for both signs. | Packages Mathlib zeta nonvanishing and quotient analyticity into the exact Jensen/log-counting vanishing form. |
| `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_zero_of_one_le_re_of_ne_one_of_logDeriv_ne_zero` / `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_eq_zero_of_one_le_re_of_ne_one_of_logDeriv_ne_zero` | `lemma` | Specializes the right-half-plane log-counting vanishing bridge to disks centered at `σ+it`. | Direct vertical-coordinate API for future disks known to lie in the nonzero right half-plane. |
| `ZeroFreeRegion.closedBall_sigma_it_one_le_re_of_add_le` / `ZeroFreeRegion.closedBall_sigma_it_ne_one_of_height_add_le` | `lemma` | Converts numeric disk conditions `1+R <= σ` and `H+R <= |t|`, with `H>0`, into pointwise right-half-plane and pole-exclusion facts on the disk centered at `σ+it`. | Removes repeated geometry from high-height Jensen/log-counting disks. |
| `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_zero_of_disk_right_half_of_logDeriv_ne_zero` / `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_eq_zero_of_disk_right_half_of_logDeriv_ne_zero` | `lemma` | If a `σ+it` disk is contained in `Re(s) >= 1`, stays a positive height away from the pole, and `logDeriv ζ` is nonzero on it, then the translated log-counting difference vanishes for both signs. | Direct disk-geometric bridge from high-height numeric hypotheses to Jensen/log-counting vanishing. |
| `ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_closedBall_sigma_it_of_disk_right_half` / `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_eq_zero_of_disk_right_half_of_neg_logDeriv_ne_zero` | `lemma` | Gives the disk-geometric analyticity wrapper for `logDeriv ζ` and the signed `-logDeriv ζ` log-counting vanishing wrapper with the nonzero hypothesis stated directly for the signed function. | Lets later signed Jensen/Borel estimates use the 3-4-1 sign convention without manual `-f ≠ 0` to `f ≠ 0` conversions. |
| `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_zero_of_disk_right_half_of_logDeriv_ne_zero_pos_radius` / signed analogues | `lemma` | Positive-radius versions of the direct `σ+it` log-counting vanishing bridges. | Normalizes the local disk radius from `|R|` to `R` under `0<R`, matching the Borel-Carathéodory disk APIs. |
| `ZeroFreeRegion.differentiableOn_logDeriv_riemannZeta_comp_add_sigma_it_ball_of_disk_right_half` / `ZeroFreeRegion.differentiableOn_neg_logDeriv_riemannZeta_comp_add_sigma_it_ball_of_disk_right_half` | `lemma` | Proves differentiability on the zero-centered translated open disk for `logDeriv ζ` and `-logDeriv ζ` from the same numeric right-half/pole-exclusion disk conditions. | Direct regularity input for centered Borel-Carathéodory estimates in the high-height zero-free chain. |
| `ZeroFreeRegion.classical_zero_free_region_of_logDeriv_regular_part_norm_affine_log_bound_and_vertical_logDeriv_norm_affine_log_bound_high_height` | `lemma` | Converts high-height estimates of the natural form `A + B log |Im|` into the multiplicative logarithmic interface using `log |Im| ≥ 1` above height `3`. | Lets Borel/Jensen estimates with additive constants feed the zero-free chain without manual constant absorption. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_logDeriv_regular_part_norm_affine_log_bound_and_vertical_logDeriv_norm_affine_log_bound_high_height` | `lemma` | Existential version of the high-height affine-log closure. | Most permissive current conditional interface for the remaining zeta-specific estimates. |
| `ZeroFreeRegion.classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_affine_bounds_high_height` | `lemma` | Coordinate version of the affine-log closure, with estimates stated in real variables `σ, β, t`. | Lets future analytic estimates written directly on `σ+it` and zero candidates `β+it` feed the complex zero-free chain. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_affine_bounds_high_height` | `lemma` | Existential coordinate affine-log wrapper. | Current most ergonomic conditional interface for hand-written Borel/Jensen estimates. |
| `ZeroFreeRegion.classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_affine_bounds_high_height` | `lemma` | Signed coordinate version of the affine-log closure, with estimates stated in `-logDeriv ζ` notation. | Lets future signed estimates written directly on `σ+it` and zero candidates `β+it` feed the zero-free chain. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_affine_bounds_high_height` | `lemma` | Existential signed coordinate affine-log wrapper. | Most permissive signed coordinate interface before specializing constants. |
| `ZeroFreeRegion.classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_one_add_log_bound_high_height` | `lemma` | Coordinate high-height closure from a single `C(1+log |t|)` bound for both regular-part and vertical log-derivative estimates. | Matches the common Big-O output shape of analytic estimates while preserving a proved route to the classical target. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_one_add_log_bound_high_height` | `lemma` | Existential single-constant `C(1+log |t|)` wrapper. | Simplest current conditional interface for the remaining zeta-specific estimates. |
| `ZeroFreeRegion.classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_one_add_log_bounds_high_height` | `lemma` | Coordinate high-height closure from separate `Cregular(1+log |t|)` and `Cvertical(1+log |t|)` bounds. | Lets the two remaining Big-O estimates carry different constants. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_one_add_log_bounds_high_height` | `lemma` | Existential two-constant `C(1+log |t|)` wrapper. | Flexible Big-O shaped interface before choosing a specific analytic proof. |
| `ZeroFreeRegion.classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_one_add_log_bound_high_height` | `lemma` | Signed coordinate high-height closure from a single `C(1+log |t|)` bound. | Simplest Big-O shaped interface in the `-logDeriv ζ` convention used by 3-4-1. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_one_add_log_bound_high_height` | `lemma` | Existential signed single-constant `C(1+log |t|)` wrapper. | Compact signed handoff when one constant controls both estimates. |
| `ZeroFreeRegion.classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_one_add_log_bounds_high_height` | `lemma` | Signed coordinate high-height closure from separate `Cregular(1+log |t|)` and `Cvertical(1+log |t|)` bounds. | Lets signed regular-part and vertical estimates carry different constants. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_one_add_log_bounds_high_height` | `lemma` | Existential signed two-constant `C(1+log |t|)` wrapper. | Flexible signed Big-O handoff before choosing the zeta-specific proof. |
| `ZeroFreeRegion.log_abs_add_three_le_two_log_abs` | `lemma` | Proves `log(|t|+3) ≤ 2 log |t|` for `|t| ≥ 3`. | Normalizes a common safe-height logarithmic scale to the classical `log |t|` scale. |
| `ZeroFreeRegion.exists_re_im_logDeriv_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height` | `lemma` | Converts a future boundary-strip estimate `‖logDeriv ζ(σ+it)‖ ≤ A + B log(|t|+3)` on `1 ≤ σ ≤ 2` into the exact `C log |t|` target shape. | Direct objective-shaped handoff for the most common safe-height estimate; the zeta-specific estimate itself remains open. |
| `ZeroFreeRegion.exists_re_im_logDeriv_vertical_log_bound_of_log_abs_add_three_bound_high_height` | `lemma` | Multiplicative `C log(|t|+3)` version of the same vertical-bound normalizer. | Removes the last constant/height bookkeeping once the hard analytic estimate is available in `log(|t|+3)` form. |
| `ZeroFreeRegion.exists_re_im_neg_logDeriv_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height` | `lemma` | Signed affine normalizer for estimates on `‖-logDeriv ζ(σ+it)‖ ≤ A + B log(|t|+3)`. | Matches the sign convention used in the 3-4-1 proof while keeping the missing estimate explicit. |
| `ZeroFreeRegion.exists_re_neg_deriv_div_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height` / `..._of_neg_affine_log_abs_add_three_bound_high_height` | `lemma` | Converts affine `log(|t|+3)` norm growth for `logDeriv ζ` or `-logDeriv ζ` into `Re(-ζ'/ζ) ≤ C log |t|`. | Feeds future vertical growth estimates directly into the real-part quotient form used by the zero-free-region route. |
| `ZeroFreeRegion.norm_sigma_add_I_mul_le_abs_add_two` | `lemma` | Proves `‖σ+it‖ ≤ |t|+2` on the strip `1 ≤ σ ≤ 2`. | Converts full complex-height estimates into imaginary-height estimates. |
| `ZeroFreeRegion.log_norm_sigma_add_I_mul_add_three_le_two_log_abs` | `lemma` | Proves `log(‖σ+it‖+3) ≤ 2 log |t|` for `1 ≤ σ ≤ 2` and `|t| ≥ 5`. | Normalizes full-height logarithmic estimates to the classical `log |t|` scale. |
| `ZeroFreeRegion.log_norm_sigma_add_I_mul_add_three_le_two_log_abs_of_re_le_three` | `lemma` | Proves the same comparison on the wider strip `1 ≤ σ ≤ 3` for `|t| ≥ 6`. | Matches the right-shifted Borel centers `(σ+r)+it`, which can sit to the right of the target point. |
| `ZeroFreeRegion.log_abs_le_log_norm_sigma_add_I_mul_add_three` | `lemma` | Proves the reverse scale comparison `log |t| ≤ log(‖σ+it‖+3)` for positive height. | Lets estimates already normalized to `log |t|` feed closures stated in the full complex-height scale. |
| `ZeroFreeRegion.log_abs_add_three_le_log_norm_sigma_add_I_mul_add_three` | `lemma` | Proves `log(|t|+3) ≤ log(‖σ+it‖+3)` for all `σ,t`. | Lets fixed-margin half-plane estimates in the safe `log(|Im|+3)` scale discharge right-shifted Borel center bounds stated in the full complex-height scale. |
| `ZeroFreeRegion.log_norm_add_three_le_two_log_abs_im` | `lemma` | Complex-variable form: `log(‖s‖+3) ≤ 2 log |Im(s)|` when `1 ≤ Re(s) ≤ 2` and `|Im(s)| ≥ 5`. | Lets future estimates stated directly in `s` use the same height normalization. |
| `ZeroFreeRegion.exists_re_im_logDeriv_vertical_log_bound_of_affine_log_norm_add_three_bound_high_height` | `lemma` | Converts a future boundary-strip estimate `‖logDeriv ζ(σ+it)‖ ≤ A + B log(‖σ+it‖+3)` on `1 ≤ σ ≤ 2` into the exact `C log |t|` target shape. | Standalone normalizer for the next hard lemma; it removes constant/height bookkeeping but does not prove the missing zeta-specific growth estimate. |
| `ZeroFreeRegion.exists_re_im_logDeriv_vertical_log_bound_of_log_norm_add_three_bound_high_height` | `lemma` | Multiplicative version of the same normalizer for inputs already stated as `C log(‖σ+it‖+3)`. | Makes the intended `logDeriv_riemannZeta_vertical_log_bound` shape directly reusable once a full-height analytic estimate is available. |
| `ZeroFreeRegion.exists_re_im_neg_logDeriv_vertical_log_bound_of_affine_log_norm_add_three_bound_high_height` | `lemma` | Signed version of the affine full-height normalizer for estimates on `‖-logDeriv ζ(σ+it)‖`. | Matches the `-ζ'/ζ` sign convention used by the 3-4-1 inequality while preserving the same honest “future estimate required” boundary. |
| `ZeroFreeRegion.exists_re_im_neg_logDeriv_vertical_log_bound_of_log_norm_add_three_bound_high_height` | `lemma` | Signed multiplicative full-height normalizer for inputs already stated as `C log(‖σ+it‖+3)`. | Lets future Borel/Jensen outputs in the natural signed convention feed the exact `C log |t|` vertical-bound shape. |
| `ZeroFreeRegion.exists_re_neg_deriv_div_vertical_log_bound_of_affine_log_norm_add_three_bound_high_height` / `..._of_neg_affine_log_norm_add_three_bound_high_height` | `lemma` | Converts affine full-height norm growth for `logDeriv ζ` or `-logDeriv ζ` directly into the `Re(-ζ'/ζ) ≤ C log |t|` convention. | Bridges the natural Borel/Jensen output shape to the real-part quotient estimates used in the 3-4-1 route. |
| `ZeroFreeRegion.logDerivVerticalLogBound_of_affine_log_norm_add_three_bound_high_height` / signed and real-part variants | `lemma` | Packages the full-height normalizers directly into the named `LogDerivVerticalLogBound`, `NegLogDerivVerticalLogBound`, and `ReNegDerivDivVerticalLogBound` interfaces. | Lets a future zeta-specific `A + B log(‖σ+it‖+3)` estimate plug into the exact mid-term vertical-bound target without unpacking the existential normalizer by hand. |
| `ZeroFreeRegion.logDerivVerticalLogBound_of_affine_log_norm_add_three_bound_on_verticalRegion` / signed and real-part variants | `lemma` | Specializes future complex-variable estimates on `verticalRegion 1 2 T0` to the coordinate `σ+it` vertical-bound interfaces. | Matches the natural statement shape of zeta/log-derivative high-height estimates while keeping the same named target boundary. |
| `ZeroFreeRegion.reNegDerivDivVerticalLogBound_of_affine_re_log_norm_add_three_bound_high_height` / `..._on_verticalRegion` | `lemma` | Accepts a direct full-height estimate for `Re(-ζ'/ζ)` rather than deriving it from a norm bound. | Matches the exact real-part input consumed by the 3-4-1 inequality and avoids unnecessary norm strengthening when the future analytic estimate is already signed. |
| `ZeroFreeRegion.exists_re_neg_deriv_div_riemannZeta_shift_pair_vertical_log_bound_of_ReNegDerivDivVerticalLogBound` | `lemma` | Turns the named direct real-part vertical bound into a shared ordinary/shifted pair bound for `σ+it` and `σ+2it`. | Lets the 3-4-1 route consume a future `Re(-ζ'/ζ)` estimate directly, including the `u=2t` height rescaling. |
| `ZeroFreeRegion.exists_norm_logDeriv_riemannZeta_shifted_vertical_log_bound_of_affine_log_norm_add_three_bound_high_height` / `...exists_re_neg_deriv_div...shifted...` | `lemma` | Composes affine full-height growth at `σ+iu` with the shifted `σ+2it` bridge. | A future ordinary vertical-strip growth theorem now supplies the shifted 3-4-1 norm and real-part inputs automatically. |
| `ZeroFreeRegion.exists_norm_logDeriv_riemannZeta_shifted_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height` / `..._of_neg_affine_log_abs_add_three_bound_high_height` | `lemma` | Composes affine `log(|u|+3)` growth at the ordinary vertical point with the shifted `σ+2it` bridge, including signed-input variants. | Lets the most common safe-height vertical estimate feed both ordinary and shifted 3-4-1 inputs without restating height bookkeeping. |
| `ZeroFreeRegion.exists_norm_logDeriv_riemannZeta_shifted_vertical_log_bound_of_log_abs_add_three_bound_high_height` / signed and real-part variants | `lemma` | Multiplicative specialization for future estimates already stated as `B log(|u|+3)`. | Removes dummy affine constants from the next hard `logDeriv ζ` vertical-bound handoff; the zeta-specific estimate is still not proved here. |
| `ZeroFreeRegion.classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_log_abs_add_three_bound_high_height` | `lemma` | Coordinate high-height closure from a single `C log(|t|+3)` bound for both remaining log-derivative estimates. | Accepts another standard analytic-number-theory estimate shape without changing the final target. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_log_abs_add_three_bound_high_height` | `lemma` | Existential `C log(|t|+3)` wrapper. | Alternative simplest current interface when estimates are stated with `log(|t|+3)`. |
| `ZeroFreeRegion.classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_log_abs_add_three_bound_high_height` | `lemma` | Signed coordinate high-height closure from a single `C log(|t|+3)` bound. | Simplest safe-height logarithmic interface in the `-logDeriv ζ` convention. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_log_abs_add_three_bound_high_height` | `lemma` | Existential signed `C log(|t|+3)` wrapper. | Compact signed safe-height handoff when one constant controls both estimates. |
| `ZeroFreeRegion.classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_log_abs_add_three_bounds_high_height` | `lemma` | Coordinate high-height closure from separate `Cregular log(|t|+3)` and `Cvertical log(|t|+3)` bounds. | Lets future regular-part and vertical-strip estimates carry different constants. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_log_abs_add_three_bounds_high_height` | `lemma` | Existential two-constant `log(|t|+3)` wrapper. | Most flexible safe-height logarithmic interface for the remaining zeta-specific estimates. |
| `ZeroFreeRegion.classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_log_abs_add_three_bounds_high_height` | `lemma` | Signed coordinate high-height closure from separate `Cregular log(|t|+3)` and `Cvertical log(|t|+3)` bounds. | Lets future estimates use the imaginary-height logarithmic scale directly in the `-logDeriv ζ` convention. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_log_abs_add_three_bounds_high_height` | `lemma` | Existential signed coordinate `log(|t|+3)` wrapper. | Signed handoff when the remaining estimates are already normalized to the common safe-height scale. |
| `ZeroFreeRegion.classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_affine_log_abs_add_three_bounds_high_height` / signed variant | `lemma` | Coordinate high-height closure from affine `A + B log(|t|+3)` regular-part and vertical bounds, including the `-logDeriv ζ` convention. | Direct safe-height affine interface for future Borel/Jensen estimates with additive constants; still conditional on the missing zeta-specific bounds. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_affine_log_abs_add_three_bounds_high_height` / signed variant | `lemma` | Existential wrappers for the affine `log(|t|+3)` coordinate closures. | Compact handoff when constants are produced existentially by an analytic estimate. |
| `ZeroFreeRegion.classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height` | `lemma` | Coordinate high-height closure from separate `Cregular log(‖σ+it‖+3)` and `Cvertical log(‖σ+it‖+3)` bounds. | Accepts full complex-height logarithmic estimates above height `5`. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height` | `lemma` | Existential two-constant `log(‖σ+it‖+3)` wrapper. | Highest-level safe interface when estimates are stated using full complex height. |
| `ZeroFreeRegion.classical_zero_free_region_of_re_im_multiplicity_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height` / `..._bound_high_height` | `lemma` | Coordinate multiplicity-aware full-height logarithmic closures for `logDeriv ζ`. | Lets future Borel/Jensen estimates isolate `n/(σ-β)` without assuming simple zeros. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_multiplicity_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height` / `..._bound_high_height` | `lemma` | Existential coordinate multiplicity-aware full-height logarithmic wrappers. | Compact handoff from multiplicity-aware full-height estimates to the zero-free-region bridge. |
| `ZeroFreeRegion.classical_zero_free_region_of_re_im_multiplicity_neg_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height` / `..._bound_high_height` | `lemma` | Signed `-logDeriv ζ` versions of the multiplicity-aware full-height logarithmic coordinate closures. | Matches the 3-4-1 sign convention while preserving zero multiplicity. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_multiplicity_neg_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height` / `..._bound_high_height` | `lemma` | Existential signed multiplicity-aware full-height logarithmic wrappers. | Direct target shape for future signed Borel/Jensen estimates. |
| `ZeroFreeRegion.classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height` | `lemma` | Signed coordinate high-height closure from separate `Cregular log(‖σ+it‖+3)` and `Cvertical log(‖σ+it‖+3)` bounds. | Lets estimates written directly in real variables use the `-logDeriv ζ` convention of the 3-4-1 inequality. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height` | `lemma` | Existential signed coordinate full-height logarithmic wrapper. | Ergonomic signed handoff for future Borel/Jensen estimates stated as `σ, β, t` inequalities. |
| `ZeroFreeRegion.classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height` | `lemma` | Signed coordinate high-height closure from one `C log(‖σ+it‖+3)` bound for both remaining estimates. | Simplest signed full-height handoff when one constant controls the regular-part and vertical estimates. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height` | `lemma` | Existential signed coordinate single-constant full-height logarithmic wrapper. | Compact target for future Borel/Jensen estimates with a shared Big-O constant. |
| `ZeroFreeRegion.classical_zero_free_region_of_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height` | `lemma` | Complex-variable high-height closure from `Cregular log(‖s‖+3)` and `Cvertical log(‖z‖+3)` bounds. | Closest conditional interface to Borel/Jensen estimates stated directly on complex variables. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height` | `lemma` | Existential complex-variable full-height logarithmic wrapper. | Single handoff target for future complex-variable regular-part and vertical-strip estimates. |
| `ZeroFreeRegion.classical_zero_free_region_of_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height` | `lemma` | Complex-variable high-height closure from one `C log(‖s‖+3)`/`C log(‖z‖+3)` bound. | Simplest complex-variable Borel/Jensen handoff when a shared constant controls both estimates. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height` | `lemma` | Existential complex-variable single-constant full-height logarithmic wrapper. | Compact public target for future complex-variable Big-O estimates with one constant. |
| `ZeroFreeRegion.classical_zero_free_region_of_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height` | `lemma` | Complex-variable high-height closure from affine `A + B log(‖s‖+3)` and `A + B log(‖z‖+3)` bounds. | Matches the common Borel/Jensen output shape with additive constants. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height` | `lemma` | Existential affine full-height logarithmic wrapper. | Most flexible current complex-variable handoff for future analytic estimates. |
| `ZeroFreeRegion.classical_zero_free_region_of_neg_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height` | `lemma` | Signed complex-variable high-height closure from affine `A + B log(‖s‖+3)` and `A + B log(‖z‖+3)` bounds. | Directly consumes estimates in the `-logDeriv ζ` sign convention used by 3-4-1. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height` | `lemma` | Existential signed affine full-height logarithmic wrapper. | Handoff point from signed Borel outputs to the classical zero-free-region target. |
| `ZeroFreeRegion.classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height` | `lemma` | Signed coordinate high-height closure from affine `A + B log(‖σ+it‖+3)` bounds. | Lets future signed Borel estimates stay in real-coordinate notation without losing additive constants. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height` | `lemma` | Existential signed coordinate affine full-height wrapper. | Most ergonomic signed coordinate handoff when estimates include additive constants. |
| `ZeroFreeRegion.classical_zero_free_region_of_neg_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height` | `lemma` | Signed complex-variable high-height closure from separate `Cregular log(‖s‖+3)` and `Cvertical log(‖z‖+3)` bounds. | Simpler Big-O handoff when no additive constants are needed. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height` | `lemma` | Existential signed multiplicative full-height logarithmic wrapper. | Compact signed handoff from full-height Borel/Jensen estimates to the classical target. |
| `ZeroFreeRegion.classical_zero_free_region_of_neg_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height` | `lemma` | Signed complex-variable high-height closure from one full-height logarithmic constant. | Simplest signed complex-variable handoff for Borel/Jensen estimates in the `-logDeriv ζ` convention. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height` | `lemma` | Existential signed complex-variable single-constant full-height wrapper. | Compact signed Big-O target when one constant controls both complex-variable estimates. |
| `ZeroFreeRegion.meromorphicOn_logDeriv_riemannZeta_closedBall` | `lemma` | Proves the logarithmic derivative `logDeriv riemannZeta` is meromorphic on every closed ball. | Local analytic input for future Borel-Caratheodory/Jensen bounds on `ζ'/ζ`. |
| `ZeroFreeRegion.meromorphicAt_neg_logDeriv_riemannZeta_one` / `ZeroFreeRegion.meromorphicOn_neg_logDeriv_riemannZeta_closedBall` | `lemma` | Proves the signed logarithmic derivative `-logDeriv ζ` is meromorphic at the pole and on closed balls. | Keeps local Jensen/Borel work in the 3-4-1 sign convention without extra rewrites. |
| `ZeroFreeRegion.borelCaratheodory_zero_centered` | `lemma` | Translates Mathlib's vanishing-at-zero Borel-Caratheodory theorem to disks centered at arbitrary `c`. | Reusable disk-centered tool for future estimates around points such as `1+it`. |
| `ZeroFreeRegion.borelCaratheodory_centered` | `lemma` | Translates Mathlib's general Borel-Caratheodory theorem to disks centered at arbitrary `c`. | Removes the repeated change-of-variables step from future zero-free-region estimates. |
| `ZeroFreeRegion.borelCaratheodory_centered_half_radius_bound` | `lemma` | Converts the centered Borel-Caratheodory rational disk factors to the fixed bound `2M + 3‖f(c)‖` on the half-radius subdisk. | Gives future local estimates a cleaner constant-bookkeeping interface. |
| `ZeroFreeRegion.borelCaratheodory_sub_centered` | `lemma` | Bounds `‖f z - f c‖` from a real-part bound on the centered function `f - f(c)`. | Direct oscillation form for future regular-part/log-derivative estimates. |
| `ZeroFreeRegion.borelCaratheodory_sub_centered_half_radius_bound` | `lemma` | Converts the centered oscillation Borel estimate to `‖f z - f c‖ ≤ 2M` on the half-radius subdisk. | Cleaner constant interface for regular-part and centered log-derivative estimates. |
| `ZeroFreeRegion.jensen_circleAverage_log_norm_riemannZeta_closedBall` | `lemma` | Specializes Mathlib's Jensen formula to ζ on closed balls. | Connects zeta meromorphicity directly to Jensen zero/divisor bookkeeping. |
| `ZeroFreeRegion.jensen_circleAverage_log_norm_logDeriv_riemannZeta_closedBall` | `lemma` | Specializes Jensen formula to `logDeriv riemannZeta` on closed balls. | Direct Jensen input for future logarithmic-derivative growth and zero-count estimates. |
| `ZeroFreeRegion.log_norm_neg_logDeriv_riemannZeta_eq` / `ZeroFreeRegion.circleAverage_log_norm_neg_logDeriv_riemannZeta_eq` | `lemma` | Proves the logarithmic norm and Jensen left-side circle average are unchanged by replacing `logDeriv ζ` with `-logDeriv ζ`. | Removes repeated `norm_neg` bookkeeping when moving between Mathlib's `logDeriv` notation and the `-ζ'/ζ` convention. |
| `ZeroFreeRegion.divisor_neg_logDeriv_riemannZeta_eq_divisor_logDeriv_closedBall` / `ZeroFreeRegion.divisor_neg_logDeriv_riemannZeta_eq_divisor_logDeriv_verticalRegion` | `lemma` | Proves the Jensen divisor bookkeeping is unchanged by replacing `logDeriv ζ` with `-logDeriv ζ`. | Lets future Jensen zero-count estimates use whichever sign convention is natural without changing divisor terms. |
| `ZeroFreeRegion.log_norm_meromorphicTrailingCoeffAt_neg_logDeriv_riemannZeta_eq` | `lemma` | Proves the Jensen trailing-coefficient logarithmic norm is unchanged by replacing `logDeriv ζ` with `-logDeriv ζ`. | Completes the signed/unsigned conversion for all Jensen terms except the intentionally signed formula statement itself. |
| `ZeroFreeRegion.jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_closedBall` | `lemma` | Specializes Jensen formula to the signed logarithmic derivative `-logDeriv ζ` on closed balls. | Signed Jensen input aligned with de la Vallee Poussin's `-ζ'/ζ` convention. |
| `ZeroFreeRegion.jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_closedBall_unsigned_terms` / `ZeroFreeRegion.jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_verticalRegion_unsigned_terms` | `lemma` | States Jensen for the signed left side `log ‖-logDeriv ζ‖` while using unsigned `logDeriv ζ` divisor/trailing-coefficient terms on the right. | Direct handoff for future Jensen zero-count estimates that combine the 3-4-1 sign convention with Mathlib's `logDeriv` bookkeeping. |
| `ZeroFreeRegion.closedBall_re_bounds` / `ZeroFreeRegion.ball_re_bounds` | `lemma` | Bounds the real coordinate of points in a complex disk by the center real coordinate plus/minus the radius. | Moves vertical-strip real-coordinate hypotheses onto Borel/Jensen disks. |
| `ZeroFreeRegion.closedBall_abs_im_ge_of_add_le` / `ZeroFreeRegion.ball_abs_im_ge_of_add_le` | `lemma` | If a disk center has imaginary height at least `H+R`, then every point in the disk has imaginary height at least `H`. | Transfers high-height zeta estimates from centers to all points in local disks. |
| `ZeroFreeRegion.closedBall_sigma_it_re_bounds` / `ZeroFreeRegion.closedBall_sigma_it_abs_im_ge_of_add_le` | `lemma` | Specializes the disk geometry to centers of the form `σ+it`. | Direct geometry interface for zeta estimates on disks centered in vertical strips. |
| `ZeroFreeRegion.closedBall_sigma_it_mem_verticalRegion` / `ZeroFreeRegion.ball_sigma_it_mem_verticalRegion` | `lemma` | Packages the `σ+it` disk geometry as simultaneous real-strip and high-height membership. | Direct vertical-region transfer for future Borel-Caratheodory/Jensen/zeta growth estimates. |
| `ZeroFreeRegion.closedBall_sigma_it_subset_verticalRegion` / `ZeroFreeRegion.ball_sigma_it_subset_verticalRegion` | `lemma` | Upgrades the same vertical-region membership to set inclusion for local disks. | Lets future estimates restrict whole Borel/Jensen disks to a vertical strip in one hypothesis. |
| `ZeroFreeRegion.mapsTo_add_closedBall_zero_sigma_it_verticalRegion` / `ZeroFreeRegion.mapsTo_add_ball_zero_sigma_it_verticalRegion` | `lemma` | Translates zero-centered disks by `σ+it` into `verticalRegion a b H`. | Matches the centered-disk change of variables used by Borel-Caratheodory wrappers. |
| `ZeroFreeRegion.differentiableOn_ball_sigma_it_of_differentiableOn_verticalRegion` / `ZeroFreeRegion.meromorphicOn_closedBall_sigma_it_of_meromorphicOn_verticalRegion` | `lemma` | Restricts differentiability/meromorphicity from `verticalRegion` to local disks. | Supplies the exact local regularity hypotheses needed by Borel-Caratheodory and Jensen. |
| `ZeroFreeRegion.borelCaratheodory_centered_verticalRegion` / `ZeroFreeRegion.borelCaratheodory_sub_centered_verticalRegion` | `lemma` | Applies Borel-Caratheodory on a `σ+it` disk from ambient `verticalRegion` hypotheses. | Direct entry point for future zeta/log-derivative growth estimates in the zero-free-region chain. |
| `ZeroFreeRegion.borelCaratheodory_centered_verticalRegion_half_radius_bound` / `ZeroFreeRegion.borelCaratheodory_sub_centered_verticalRegion_half_radius_bound` | `lemma` | Half-radius versions of the ambient `verticalRegion` Borel wrappers. | Removes disk denominator bookkeeping before specializing to zeta or logarithmic derivatives. |
| `ZeroFreeRegion.borelCaratheodory_riemannZeta_verticalRegion` / `ZeroFreeRegion.borelCaratheodory_sub_riemannZeta_verticalRegion` | `lemma` | Specializes the vertical-region Borel wrappers to ζ and centered ζ. | Reduces future zeta growth estimates to ambient real-part bounds on `verticalRegion`. |
| `ZeroFreeRegion.borelCaratheodory_riemannZeta_verticalRegion_of_re_le` / `ZeroFreeRegion.borelCaratheodory_sub_riemannZeta_verticalRegion_of_re_le` | `lemma` | Pointwise real-part estimate versions of the ζ Borel bounds. | Lets future zeta growth estimates be supplied as ordinary `∀ z ∈ verticalRegion, Re(...) ≤ M` hypotheses. |
| `ZeroFreeRegion.borelCaratheodory_riemannZeta_verticalRegion_half_radius_bound` / `ZeroFreeRegion.borelCaratheodory_sub_riemannZeta_verticalRegion_half_radius_bound` / `ZeroFreeRegion.borelCaratheodory_riemannZeta_verticalRegion_of_re_le_half_radius` / `ZeroFreeRegion.borelCaratheodory_sub_riemannZeta_verticalRegion_of_re_le_half_radius` | `lemma` | Half-radius ζ Borel bounds in both `Set.MapsTo` and pointwise real-part forms. | Gives future ζ growth estimates the same denominator-free local-disk interface as the log-derivative estimates. |
| `ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_verticalRegion` / `ZeroFreeRegion.borelCaratheodory_sub_logDeriv_riemannZeta_verticalRegion` | `lemma` | Conditional Borel bounds for `logDeriv ζ` and centered `logDeriv ζ`. | Keeps differentiability and real-part bounds explicit as the remaining zeta-specific analytic input. |
| `ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_verticalRegion_of_re_le` / `ZeroFreeRegion.borelCaratheodory_sub_logDeriv_riemannZeta_verticalRegion_of_re_le` | `lemma` | Pointwise real-part estimate versions of the conditional `logDeriv ζ` Borel bounds. | Lets future zeta/log-derivative height estimates be supplied as ordinary `∀ z ∈ verticalRegion, Re(...) ≤ M` hypotheses. |
| `ZeroFreeRegion.differentiableOn_logDeriv_riemannZeta_verticalRegion_of_one_le_re` | `lemma` | Proves `logDeriv ζ` is differentiable on positive-height vertical regions with real part bounded below by `1`. | Uses ζ nonvanishing on `Re(s) ≥ 1` to discharge a Borel regularity hypothesis. |
| `ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le` / `ZeroFreeRegion.borelCaratheodory_sub_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le` | `lemma` | Right-half-strip Borel bounds for `logDeriv ζ` where differentiability is automatic. | Leaves only pointwise real-part height bounds as analytic inputs for the Borel route. |
| `ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le` / `ZeroFreeRegion.borelCaratheodory_sub_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le` | `lemma` | Direct Borel bounds on a `σ+it` disk whose numeric geometry puts it in the right half-plane and away from the pole. | Removes the ambient `verticalRegion` detour for local high-height Borel estimates. |
| `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le` / `ZeroFreeRegion.borelCaratheodory_sub_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le` | `lemma` | Direct signed Borel bounds for `-logDeriv ζ` on the same right-half `σ+it` disks. | Lets future high-height estimates stay in the 3-4-1 sign convention from the start. |
| `ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le_half_radius` / `ZeroFreeRegion.borelCaratheodory_sub_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le_half_radius` / signed analogues | `lemma` | Direct half-radius Borel bounds on right-half `σ+it` disks for both `logDeriv ζ` and `-logDeriv ζ`. | Removes raw disk denominator terms without routing through an ambient vertical region. |
| `ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_affine_re_le_half_radius` / `ZeroFreeRegion.borelCaratheodory_sub_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_affine_re_le_half_radius` / signed analogues | `lemma` | Direct affine full-height half-radius Borel bounds on local right-half `σ+it` disks. | Accepts `A + B log(‖σ+it‖+3)` estimates directly, matching the quantitative zero-free-region handoff shape. |
| `ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_sigma_it_right_shift_of_affine_re_le_half_radius` / signed analogue | `lemma` | Right-shifted affine Borel transfer: a disk centered at `(σ+r)+it` controls the boundary-near point `σ+it`. | Packages the local geometric handoff needed before a vertical `logDeriv ζ` estimate; the zeta-specific real-part and center bounds remain hypotheses. |
| `ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius` / signed analogue | `lemma` | Normalizes the right-shifted affine Borel transfer to a pure `C log |t|` bound when `1 ≤ σ+r ≤ 3` and `|t| ≥ 6`. | Removes the remaining height-scale bookkeeping after the local Borel hypotheses are supplied; it still does not prove those zeta-specific hypotheses. |
| `ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_sigma_it_right_shift_le_log_norm_of_affine_re_le_half_radius` / signed analogue | `lemma` | Repackages the same right-shifted Borel transfer in the full complex-height scale `C log (‖σ+it‖+3)`. | Lets later closures stated in the natural vertical-height norm scale consume the already-normalized `log |t|` Borel output. |
| `ZeroFreeRegion.re_neg_deriv_div_riemannZeta_sigma_it_right_shift_le_log_abs_of_affine_logDeriv_re_le_half_radius` / `..._affine_neg_logDeriv_re_le_half_radius` | `lemma` | Converts the normalized right-shifted Borel output to the real-part quotient convention `Re(-ζ'/ζ)(σ+it) ≤ C log |t|`. | Feeds the 3-4-1 zero-free-region route directly once the same local Borel hypotheses are available. |
| `ZeroFreeRegion.re_neg_deriv_div_riemannZeta_sigma_it_right_shift_le_log_norm_of_affine_logDeriv_re_le_half_radius` / `..._affine_neg_logDeriv_re_le_half_radius` | `lemma` | Same quotient conversion in the full complex-height scale `C log (‖σ+it‖+3)`. | Lets a future vertical `O(log height)` closure use the `Re(-ζ'/ζ)` convention without redoing norm-to-real bookkeeping. |
| `ZeroFreeRegion.re_neg_deriv_div_riemannZeta_finset_right_shift_le_log_norm_of_affine_logDeriv_re_le_half_radius` / `..._affine_neg_logDeriv_re_le_half_radius` | `lemma` | Finite-family version of the right-shifted quotient conversion over heights `tau k`. | Gives higher-degree finite detectors a Borel-side supplier shape with one shifted upper bound per frequency before specializing to frequencies such as `k*t`. |
| `RiemannPNT.API.log_deriv_zeta_finset_single_lower_bound_auto_of_right_shift_borel_family` / `..._signed_right_shift_borel_family` | `theorem` | Combines the automatic finite detector lower-bound theorem with finite-family right-shifted Borel suppliers over `S.erase m`. | Removes the manual `hupper` handoff between future Borel estimates and finite detector algebra; the zeta-specific Borel hypotheses remain explicit. |
| `RiemannPNT.API.log_deriv_zeta_bty_detector_one_lower_bound_of_right_shift_borel_family` / `..._signed_right_shift_borel_family` | `theorem` | BTY degree-16 specialization of the detector/Borel-family bridge for the selected `k=1` term. | Discharges the BTY certificate and coefficient side conditions, leaving only the right-shifted Borel estimates for the remaining BTY frequencies. |
| `RiemannPNT.API.log_deriv_zeta_bty_detector_one_lower_bound_of_uniform_right_shift_borel_family` / `..._uniform_right_shift_borel_family_simplified` / `..._uniform_signed_right_shift_borel_family` | `theorem` | Uniform-bound version of the BTY right-shifted Borel bridge using the computed remaining-coefficient sum `6917296 / 2485395`, plus an unsigned simplified-constant facade with coefficient `3458648 / 2163835`. | Gives the later zero-free-region route the cleaner one-constant upper-bound interface expected from global height comparisons. |
| `RiemannPNT.API.log_deriv_zeta_bty_detector_one_lower_bound_of_center_and_LogDerivVerticalLogBound` | `theorem` | Public entrypoint for the mixed BTY handoff from `LogDerivVerticalLogBound` plus a separate `k=0` center upper bound. | Current exact API shape for feeding a future high-height `‖logDeriv ζ(σ+it)‖ <= C log |t|` estimate into the BTY detector without pretending that estimate is proved here. |
| `RiemannPNT.API.exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_LogDerivVerticalLogBound` | `theorem` | Public fixed-margin version of the mixed BTY handoff, using the proved `Re(s) >= 1 + ε` quotient estimate for the `k=0` center term. | Keeps the route usable away from the boundary while preserving the boundary `LogDerivVerticalLogBound` gap. |
| `ZeroFreeRegion.re_neg_deriv_div_riemannZeta_sigma_two_it_right_shift_le_log_abs_of_affine_logDeriv_re_le_half_radius` / `..._affine_neg_logDeriv_re_le_half_radius` | `lemma` | Shifted third-term version controlling `Re(-ζ'/ζ)(σ+2it)` from local right-shifted Borel hypotheses at height `2t`. | Supplies the `σ+2it` term needed by the 3-4-1 route after absorbing `log |2t|` into `log |t|`. |
| `ZeroFreeRegion.re_neg_deriv_div_riemannZeta_shift_pair_right_shift_le_log_abs_of_affine_logDeriv_re_le_half_radius` / `..._affine_neg_logDeriv_re_le_half_radius` | `lemma` | Pair package combining right-shifted Borel hypotheses at heights `t` and `2t` into one shared `C log |t|` bound for both shifted `Re(-ζ'/ζ)` terms. | Gives the 3-4-1 route a single local-Borel handoff once the zeta-specific real-part and center estimates are supplied. |
| `ZeroFreeRegion.re_neg_deriv_div_riemannZeta_shift_pair_right_shift_le_log_norm_of_affine_logDeriv_re_le_half_radius` / `..._affine_neg_logDeriv_re_le_half_radius` | `lemma` | Full-height version of the same pair package, with output in the `C log(‖σ+it‖+3)` scale. | Lets high-height closures written in complex-height notation consume both shifted Borel outputs without separate conversion steps. |
| `ZeroFreeRegion.exists_re_neg_deriv_div_riemannZeta_shift_pair_right_shift_le_log_norm_of_affine_logDeriv_re_le_half_radius_fixed_margin_center` / signed analogue | `lemma` | Existential full-height pair package whose right-shifted center norm estimates are discharged by the proved fixed-margin half-plane bound. | Reduces the remaining Borel input to local real-part estimates on the `t` and `2t` disks; the center bounds are no longer independent analytic hypotheses. |
| `ZeroFreeRegion.re_neg_deriv_div_riemannZeta_sigma_two_it_right_shift_le_log_norm_of_affine_logDeriv_re_le_half_radius` / `..._affine_neg_logDeriv_re_le_half_radius` | `lemma` | Full-height `log (‖σ+it‖+3)` version of the shifted `σ+2it` third-term bridge. | Lets the third 3-4-1 term feed closures formulated in the same full-height scale as the main `σ+it` estimate. |
| `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_regularPart_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius` | `lemma` | Applies the same right-shifted Borel normalization to the zero-candidate regular part `-logDeriv ζ(w)+(w-ρ)⁻¹`. | Direct handoff for future local zero-repulsion estimates; differentiability, real-part, and center bounds for the regular part remain explicit hypotheses. |
| `ZeroFreeRegion.re_neg_logDeriv_riemannZeta_sigma_it_add_inv_right_shift_le_log_abs_of_affine_regularPart_re_le_half_radius` | `lemma` | Converts that normalized regular-part norm bound into `Re(-ζ'/ζ)(σ+it)+1/(σ-β) ≤ C log |t|`. | Produces the exact zero-term estimate consumed by the high-height 3-4-1 closure once the missing regular-part Borel/Jensen inputs are proved. |
| `ZeroFreeRegion.exists_re_neg_logDeriv_riemannZeta_sigma_it_add_inv_right_shift_le_log_abs_of_affine_regularPart_re_le_half_radius_fixed_margin_center` | `lemma` | Discharges the regular-part center norm hypothesis using the proved fixed-margin `-logDeriv ζ` bound plus the explicit `‖((σ+r+it)-(β+it))⁻¹‖ ≤ 1/r` distance estimate. | Reduces the simple-zero regular-part handoff to differentiability and local real-part bounds on the right-shifted disk; the boundary-strip `O(log |t|)` estimate itself remains open. |
| `ZeroFreeRegion.exists_re_neg_logDeriv_riemannZeta_sigma_it_add_inv_right_shift_le_log_norm_of_affine_regularPart_re_le_half_radius_fixed_margin_center` | `lemma` | Full-height version of the simple-zero center-discharged zero-repulsion bridge. | Lets later high-height closures consume the same result in the `C log (‖σ+it‖+3)` scale. |
| `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius` | `lemma` | Multiplicity-aware version with regular part `-logDeriv ζ(w)+n(w-ρ)⁻¹`. | Keeps the Borel handoff compatible with multiple zeros rather than assuming a simple zero. |
| `ZeroFreeRegion.re_neg_logDeriv_riemannZeta_sigma_it_add_multiplicity_inv_right_shift_le_log_abs_of_affine_regularPart_re_le_half_radius` | `lemma` | Converts the multiplicity-aware right-shifted Borel output into the same unit-principal zero-repulsion estimate. | Uses `n≥1` to recover the required `1/(σ-β)` term while preserving multiplicity in the analytic input. |
| `ZeroFreeRegion.exists_re_neg_logDeriv_riemannZeta_sigma_it_add_multiplicity_inv_right_shift_le_log_abs_of_affine_regularPart_re_le_half_radius_fixed_margin_center` | `lemma` | Multiplicity-aware center-discharged zero-repulsion bridge; the center principal-part cost is `(n : ℝ)/r`, while `n≥1` still yields the unit `1/(σ-β)` conclusion. | Removes the center norm hypothesis for multiple-zero regular parts, leaving only local differentiability and real-part estimates as future analytic input. |
| `ZeroFreeRegion.exists_re_neg_logDeriv_riemannZeta_sigma_it_add_multiplicity_inv_right_shift_le_log_norm_of_affine_regularPart_re_le_half_radius_fixed_margin_center` | `lemma` | Full-height multiplicity-aware version of the center-discharged zero-repulsion bridge. | Keeps the multiple-zero handoff aligned with closures stated using `log (‖σ+it‖+3)`. |
| `ZeroFreeRegion.borelCaratheodory_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius` | `lemma` | Positive-sign multiplicity-aware version for `logDeriv ζ(w)-n(w-ρ)⁻¹`. | Lets future local factorization estimates feed the Borel handoff before converting to the signed 3-4-1 convention. |
| `ZeroFreeRegion.exists_borelCaratheodory_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius_fixed_margin_center` | `lemma` | Positive-sign multiplicity-aware Borel bridge with its center norm discharged by the fixed-margin `logDeriv ζ` bound and the same `(n : ℝ)/r` principal-part cost. | Matches the natural local-factorization sign convention while removing another center-bound hypothesis from the future zero-repulsion chain. |
| `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_norm_of_affine_re_le_half_radius` / positive-sign analogue | `lemma` | Multiplicity-aware regular-part Borel transfer in the full complex-height scale `C log (‖σ+it‖+3)`. | Bridges the future local factorization/Jensen input to closures stated with `log (‖σ+it‖+3)`, without assuming the missing regular-part estimates. |
| `ZeroFreeRegion.exists_borelCaratheodory_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_norm_of_affine_re_le_half_radius_fixed_margin_center` | `lemma` | Positive-sign multiplicity-aware full-height Borel bridge with the right-shifted center norm discharged by the fixed-margin `logDeriv ζ` bound. | Provides the natural `log (‖σ+it‖+3)` handoff for future local-factorization estimates without keeping a separate center-bound hypothesis. |
| `ZeroFreeRegion.exists_borelCaratheodory_neg_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_norm_of_affine_re_le_half_radius_fixed_margin_center` | `lemma` | Signed multiplicity-aware full-height Borel bridge with the right-shifted center norm discharged by the fixed-margin `-logDeriv ζ` bound. | Gives the same center-discharged handoff directly in the `-ζ'/ζ` convention used by the 3-4-1 route. |
| `ZeroFreeRegion.re_neg_logDeriv_riemannZeta_sigma_it_add_multiplicity_inv_right_shift_le_log_norm_of_affine_regularPart_re_le_half_radius` | `lemma` | Full-height multiplicity-aware zero-repulsion estimate `Re(-ζ'/ζ)(σ+it)+1/(σ-β) ≤ C log (‖σ+it‖+3)`. | Exposes the exact local zero term in the scale used by future high-height closure hypotheses. |
| `ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le_half_radius` / `ZeroFreeRegion.borelCaratheodory_sub_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le_half_radius` | `lemma` | Half-radius right-half-strip Borel bounds for positive `logDeriv ζ`. | Matches the sign convention of local regular-part estimates before translating to `-ζ'/ζ`. |
| `ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_affine_re_le_half_radius` / `ZeroFreeRegion.borelCaratheodory_sub_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_affine_re_le_half_radius` | `lemma` | Affine full-height half-radius Borel bounds for `logDeriv ζ` and its centered oscillation. | Normalizes raw Borel output to the `A + B log(‖σ+it‖+3)` scale used by the high-height zero-free handoff. |
| `ZeroFreeRegion.differentiableOn_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re` | `lemma` | Signed version for `-logDeriv ζ` on positive-height right half-strips. | Matches the sign convention used by the 3-4-1 inequality. |
| `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le` / `ZeroFreeRegion.borelCaratheodory_sub_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le` | `lemma` | Borel bounds for `-logDeriv ζ` with automatic differentiability. | Lets future estimates stay in the signed `-ζ'/ζ` notation through the Borel route. |
| `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le_half_radius` | `lemma` | Half-radius constant-bound version of the signed `-logDeriv ζ` Borel estimate. | Removes the disk denominator terms from the most common signed Borel application. |
| `ZeroFreeRegion.borelCaratheodory_sub_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le_half_radius` | `lemma` | Half-radius oscillation version for signed `-logDeriv ζ`. | Direct centered-control interface for future local regular-part estimates. |
| `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_affine_re_le_half_radius` / `ZeroFreeRegion.borelCaratheodory_sub_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_affine_re_le_half_radius` | `lemma` | Affine full-height half-radius Borel bounds for signed `-logDeriv ζ` and its centered oscillation. | Same denominator-free affine interface in the exact sign convention used by the 3-4-1 inequality. |
| `ZeroFreeRegion.jensen_circleAverage_log_norm_verticalRegion` | `lemma` | Applies Jensen's formula on a `σ+it` disk from ambient `verticalRegion` meromorphicity. | Direct entry point for future zero-count/log-derivative Jensen estimates. |
| `ZeroFreeRegion.differentiableOn_riemannZeta_verticalRegion_of_pos_height` / `ZeroFreeRegion.meromorphicOn_logDeriv_riemannZeta_verticalRegion` | `lemma` | Supplies ζ differentiability on positive-height vertical regions and log-derivative meromorphicity on all such regions. | Zeta-specific regularity layer feeding the Borel/Jensen wrappers. |
| `ZeroFreeRegion.jensen_circleAverage_log_norm_riemannZeta_verticalRegion` / `ZeroFreeRegion.jensen_circleAverage_log_norm_logDeriv_riemannZeta_verticalRegion` | `lemma` | Specializes the vertical-region Jensen wrapper to ζ and `logDeriv ζ`. | Ready-to-use zeta Jensen statements for future zero-count/log-derivative estimates. |
| `ZeroFreeRegion.meromorphicOn_neg_logDeriv_riemannZeta_verticalRegion` / `ZeroFreeRegion.jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_verticalRegion` | `lemma` | Signed vertical-region meromorphicity and Jensen specialization for `-logDeriv ζ`. | Lets future high-height Jensen estimates stay in the signed convention used by 3-4-1. |
| `ZeroFreeRegion.jensen_circleAverage_log_norm_riemannZeta_sigma_it` / `ZeroFreeRegion.jensen_circleAverage_log_norm_logDeriv_riemannZeta_sigma_it` / signed analogues | `lemma` | Direct Jensen formulas on `σ+it` disks, including a signed-left/unsigned-right version for `-logDeriv ζ`. | Avoids ambient vertical-region bookkeeping when the local Jensen disk is already the natural object. |
| `ZeroFreeRegion.jensen_circleAverage_log_norm_riemannZeta_sigma_it_of_pos_radius` / `ZeroFreeRegion.jensen_circleAverage_log_norm_logDeriv_riemannZeta_sigma_it_of_pos_radius` / signed analogues | `lemma` | Positive-radius direct Jensen formulas on `σ+it` disks. | Removes `|R|` radius bookkeeping in the Jensen local-divisor side when future estimates already assume `0<R`. |

Two important boundaries:

- `ZeroFreeRegion.classical_zero_free_region_compact` is not the classical
  quantitative region `Re(s) ≥ 1 - c / log |Im(s)|`; that remains the target
  `ZeroFreeRegion.classical_zero_free_region`.
- `ZeroFreeRegion.residue_bounds` and
  `ZeroFreeRegion.tendsto_mul_logDeriv_riemannZeta_simplePoleAtOne` give
  local pole/principal-part control.  The derived local norm bound
  `ZeroFreeRegion.eventually_norm_logDeriv_riemannZeta_le_two_div_norm_sub_one`
  and its punctured-ball/closed-ball forms are still local estimates near
  `1`, not global logarithmic-derivative growth estimates in vertical strips.
- `ZeroFreeRegion.meromorphicOn_logDeriv_riemannZeta_closedBall` records
  meromorphicity of `ζ'/ζ`, but does not by itself prove the
  Borel-Caratheodory/Jensen growth estimates needed for the quantitative
  zero-free region.

## Publication Core and Remaining Targets

### 3-4-1 Logarithmic-Derivative Combination

```
3·Re(-ζ'/ζ(σ)) + 4·Re(-ζ'/ζ(σ+it)) + Re(-ζ'/ζ(σ+2it)) ≥ 0
```

The full infinite-series combination is proved in
`ZeroFreeRegion.log_deriv_zeta_nonneg_combination`.

### Compact Zero-Free Region

For any T ≥ 2, there exists d > 0 such that ζ(s) has no zeros in
{|Im(s)| ≤ T, Re(s) ≥ 1-d}.

This is proved in `ZeroFreeRegion.classical_zero_free_region_compact`.

### Prime Number Theorem Equivalences

The three classical forms are equivalent:
1. π(x) ~ x/log x
2. π(x) ~ Li(x)
3. ψ(x) ~ x

These equivalence and error-propagation lemmas are supporting infrastructure.
They are useful for composition once an analytic PNT input is available, but the
three PNT forms themselves remain `def ... : Prop` target statements in this
repository.

### Von Mangoldt Explicit Formula

The current repository contains this as a corrected `Prop` target statement,
not as a proved theorem.  The Lean target now uses the midpoint convention
`chebyshevPsi0` and a height-truncated zero contribution
`finiteNontrivialZeroSum`, rather than an unconditional unordered `tsum` over
all nontrivial zeros.

The explicit-formula side also contains route interfaces such as
`PrimeNumberTheorem.ExplicitFormulaConversePowerTarget` and
`PrimeNumberTheorem.ExplicitFormulaTruncated.ExplicitFormulaTruncatedConverseRoute`.
These name the future oscillation/converse dependency from a truncated explicit
formula to zero-free vertical lines; they are not unconditional proofs of those
analytic inputs.  The public API exposes both the direct `Re(s)=2/3` consequence
and the reflected `Re(s)=1/3` consequence of this conditional route, including
direct wrappers for the concrete `theta < 2/3` `psi`-error input.

The finite truncated-zero bookkeeping is proved as ordinary theorem-level
infrastructure.  In particular,
`new_zero_contribution_sum_eventually_zero_of_eventually_sdiff_eq_empty`,
`new_zero_contribution_sum_tendsto_zero_of_eventually_sdiff_eq_empty`,
`new_zero_inv_norm_tail_tendsto_zero_of_eventually_sdiff_eq_empty`, and
`new_zero_card_tail_tendsto_zero_of_eventually_sdiff_eq_empty` show that if no
new bounded-height zeros appear eventually above a base cutoff, then the finite
new-zero contribution and the two RH-tail controls collapse to zero.  These are
finite-combinatorial tail bridges, not substitutes for Perron's formula or the
global explicit formula.

The finite zero-pair infrastructure also contains proved positivity suppliers
for elementary detector kernels.  The public API includes the resolvent kernel
`resolventLaplaceKernel`, its center-reflected version
`symmetricResolventLaplaceKernel`, finite nonnegative ordinary and symmetric
kernel combinations, and their height-truncated/new-zero sum, average, and
paired-contribution nonnegativity wrappers.  These are concrete algebraic
suppliers for later Stechkin/Heath-Brown-style detector arguments; they do not
prove the missing high-height zeta growth or logarithmic-derivative estimates.

### Target Statements, Not Proved Theorems

The remaining 22 target declarations are intentionally `def ... : Prop` rather
than theorem declarations. They are tracked as future proof obligations and must
not be cited as completed proofs:

- PNT and RH-scale error targets:
  `PNTForm1`, `PNTForm2`, `PNTForm3`, `RH_PsiErrorBound`,
  `RH_ThetaErrorBound`, `RH_PrimeCountingLiErrorBound`, `RH_ErrorBound`,
  `rh_iff_optimal_error`;
- explicit formula target:
  `explicit_formula_von_mangoldt`;
- quantitative zero-free-region targets:
  `classical_zero_free_region`, `vinogradov_korobov_zero_free_region`;
- Hardy/critical-line targets:
  `integral_asymptotic_target`, `hardy_two_signed_moments_target`,
  `hardy_theorem_target`, `hardy_zeros_unbounded_target`,
  `hardy_zeros_abs_unbounded_target`, `hardy_littlewood_lower_bound_target`,
  `selberg_zero_proportion_target`,
  `HardyTheorem.Details.gamma_asymptotic_half_plus_it_target`,
  `HardyTheorem.Details.theta_asymptotic_target`,
  `HardyTheorem.Details.approximate_functional_equation_target`,
  `KnownResults.conrey_40_percent_zeros_on_critical_line_target`.

The four missing analytic chains are:

1. **Quantitative zero-free region**: upgrade the compact strip to
   `1 - c / log |t|` using zeta growth and logarithmic-derivative estimates
   together with Borel-Caratheodory or Hadamard/Jensen machinery.
2. **Explicit formula**: prove the Perron/residue-theorem chain that yields the
   finite-height Riemann-von Mangoldt formula for `chebyshevPsi0`.
3. **RH error equivalence**: connect the explicit formula under RH to the
   `sqrt x * log x` prime-counting error and prove the reverse implication.
4. **Hardy theorem**: prove the signed moment/asymptotic inputs for Hardy's
   theorem and the stronger critical-line zero-counting targets.

## Quick Start

### Prerequisites

- [Lean 4](https://lean-lang.org/) via `elan`
- [Elan](https://github.com/leanprover/elan) (Lean version manager)
- The checked-in `lean-toolchain` pins Lean to `leanprover/lean4:v4.29.1`

### Build

```bash
# Install Lean 4 via elan (if not already installed)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Clone and build
git clone https://github.com/cc-chen-tech/riemann-pnt-lean4.git
cd riemann-pnt-lean4
lake build
```

This checkout is configured to use a local path dependency at `vendor/mathlib`.
That directory is ignored by git because it is large. For a fresh clone, either
place Mathlib 4.29.1 at `vendor/mathlib`, or change `lakefile.lean` back to a
git dependency and regenerate the manifest.

## Infrastructure Gaps

See [`PUBLISHING.md`](PUBLISHING.md) for the exact release-readiness checklist
and the commands used to verify the current proof-gap count.

See [`docs/mathematical-contributions.md`](docs/mathematical-contributions.md)
for a precise mathematical description of the project-local verified
contributions and their proof routes.

See [`docs/formal-theorem-inventory.md`](docs/formal-theorem-inventory.md)
for a reviewer-oriented inventory separating proved declarations from target
statements.

See [`docs/target-statements-and-chains.md`](docs/target-statements-and-chains.md)
for a compact checklist of all `def ... : Prop` targets and the four missing
analytic chains they belong to.

See [`docs/implementation-standards.md`](docs/implementation-standards.md)
for the standard that prevents target statements from being reported as proved
theorems.

See [`docs/missing-chains-index.md`](docs/missing-chains-index.md) for the
parallel work breakdown of the remaining analytic chains.

| Theorem | Missing Mathlib Component | Difficulty |
|---|---|---|
| Explicit formula (Perron) | Contour integration / Residue theorem | High |
| Classical zero-free region (σ ≥ 1-c/log|t|) | Hadamard factorization or Borel-Carathéodory | Medium |
| Vinogradov-Korobov zero-free region | Exponential sum estimates | Very High |
| Hardy's theorem targets | Corrected moment estimates and asymptotic expansions of special functions | Medium–High |

### Easiest Path Forward

The **Borel-Carathéodory** route is lighter than full Hadamard factorization,
but this repository still needs additional zeta growth and logarithmic-derivative
estimates before the quantitative zero-free region can be closed.

## Related Work

- [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
  (Lean 4) — PNT and related analytic number theory goals via routes including
  Wiener-Ikehara.
- [strongpnt](https://github.com/math-inc/strongpnt) (Lean 4) — AI-generated
  Lean formalization of the strong PNT; check its current state before any
  public SOTA comparison.
- Avigad et al. (2007) — Elementary PNT in Isabelle/HOL.
- Harrison (2009) — Newman's analytic PNT in HOL Light.
- Mathlib's `riemannZeta` and zeta/L-function work by Loeffler--Stoll — zeta
  basics, Euler products, the functional equation, and nonvanishing in the
  closed half-plane `Re(s) >= 1`.

## Citation

If you use this work in your research, please cite:

```bibtex
@software{riemann_pnt_lean4,
  title = {Lean 4 Infrastructure for de la Vallee Poussin 3-4-1 Zeta Machinery},
  year = {2026},
  url = {https://github.com/cc-chen-tech/riemann-pnt-lean4}
}
```

## License

Apache 2.0 — same as Mathlib.
