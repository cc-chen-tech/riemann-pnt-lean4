# Riemann Zeta Function and Prime Number Theorem — Lean 4 Formalization

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

## Paper Positioning

The recommended paper framing is to make the `3-4-1 + compact zero-free strip`
module the main contribution, with the remaining infrastructure presented as
secondary contributions and future work.  This keeps the claims tight:

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
| `PrimeNumberTheorem.lean` | 0 | Bounded-height zero finiteness proved; RH error equivalence and von Mangoldt explicit formula targets |
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
- route interfaces: 4
  (`HardyTheorem.AFE.zeta_critical_afe_target`,
  `MathlibAux.rectangleIntegral_meromorphic_eq_residue_sum`,
  `PrimeNumberTheorem.ExplicitFormulaTruncated.ExplicitFormulaTruncatedTarget`,
  `RiemannExplorer.Conrey40.conrey_40_percent_zeros_on_critical_line_target`);
- reusable predicates: 2
  (`HardyTheorem.weightedIntegralOf_tail_dominates`,
  `PrimeNumberTheorem.ExplicitFormulaAux.goodHeight`);
- unclassified Prop definitions: 0.

No route interface currently has a body equal to `True`.  The rectangle
contour/residue interface is a real `Prop` statement, but it is still not a
proved theorem.

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
| `MathlibAux/RectangleResidue.lean` | Rectangle residue route interface for future Perron/explicit-formula work | sorry-free, route interface unproved |
| `HardyTheorem/AFE.lean` | Corrected AFE route interface using an unwrapped theta wrapper | sorry-free, route interface unproved |
| `RiemannExplorer/Conrey40.lean` | Conrey target alias to the upper-level `KnownResults` target | sorry-free, route interface alias |

## Verified Components

The project currently verifies several supporting statements, including:

- the formal RH statement restricted to nontrivial zeros;
- zeta special-value and Euler-product wrappers available in Mathlib;
- basic PNT-form equivalence scaffolding and asymptotic lemmas;
- the trigonometric identity `3 + 4cos θ + cos 2θ = 2(1+cos θ)² ≥ 0`;
- the full 3-4-1 logarithmic-derivative nonnegativity combination;
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
| `ZeroFreeRegion.trig_identity_nonneg` | `lemma` | Proves `3 + 4 cos θ + cos(2θ) ≥ 0` via `2(1+cos θ)^2`. | Pointwise nonnegativity input for the de la Vallee Poussin combination. |
| `ZeroFreeRegion.log_deriv_zeta_nonneg_combination` | `lemma` | Proves `3 Re(-ζ'/ζ(σ)) + 4 Re(-ζ'/ζ(σ+it)) + Re(-ζ'/ζ(σ+2it)) ≥ 0` for `σ > 1`. | Primary 3-4-1 theorem. |
| `ZeroFreeRegion.log_deriv_zeta_lower_bound` | `lemma` | Rearranges the 3-4-1 inequality into the lower bound for `Re(-ζ'/ζ(σ+it))`. | Algebraic corollary used by the future quantitative zero-free-region chain. |
| `ZeroFreeRegion.logDeriv_riemannZeta_eq_deriv_div` / `ZeroFreeRegion.neg_logDeriv_riemannZeta_re_eq_neg_deriv_div_re` | `lemma` | Bridges Mathlib's `logDeriv ζ` notation with the classical `ζ'/ζ` and `-ζ'/ζ` quotient notation, including real-part and norm forms. | Lets future Borel/Jensen `logDeriv` estimates rewrite directly into the 3-4-1 sign convention. |
| `ZeroFreeRegion.sigmaOf_log_gt_one` | `lemma` | Proves `1 < 1 + a / log |t|` above height `2` when `a > 0`. | Real-variable input for the standard high-height choice of `σ`. |
| `ZeroFreeRegion.sigmaOf_log_le_two` | `lemma` | Proves `1 + a / log |t| ≤ 2` above height `2` when `a ≤ log 2`. | Supplies the `σ ≤ 2` side condition for the 3-4-1 assembly. |
| `ZeroFreeRegion.sigmaOf_log_sub_pos` | `lemma` | Proves `(1 + a / log |t|) - β > 0` whenever `β < 1`. | Supplies the zero-separation side condition in the 3-4-1 contradiction. |
| `ZeroFreeRegion.sigmaOf_log_le_one_add` | `lemma` | Proves `1 + a / log |t| ≤ 1 + d` from `a ≤ d log 2`. | Connects the standard high-height choice to local right-neighborhood bounds near `1`. |
| `ZeroFreeRegion.three_four_one_sigmaOf_log_margin` | `lemma` | Proves the pure real-variable negativity margin for `σ = 1 + a / log |t|`. | Turns shifted log-derivative bounds into the strict negative upper bound needed by the 3-4-1 contradiction. |
| `ZeroFreeRegion.exists_sigmaOf_log_margin_constants` | `lemma` | Chooses positive `a,c` satisfying `a ≤ log 2`, `a ≤ d log 2`, and `3C/a+K < 4/(a+c)` when `1<C<4/3`. | Removes the remaining constant-choice algebra from the high-height zero-free assembly. |
| `ZeroFreeRegion.exists_sigmaOf_log_margin_constants_for_shift_bounds` | `lemma` | Specializes the constant choice to the shifted-estimate margin `3C/a + 4*Czero + Ctwo < 4/(a+c)` when `Czero,Ctwo ≥ 0`. | Lets future shifted log-derivative estimates feed the 3-4-1 closure without restating `K = 4*Czero + Ctwo`. |
| `ZeroFreeRegion.residue_bounds` | `lemma` | Proves `1 < (σ-1) Re(ζ(σ)) ≤ σ` for `σ > 1`. | Real-axis residue-scale control near the pole at `1`. |
| `ZeroFreeRegion.classical_zero_free_region_compact` | `theorem` | For every `T ≥ 2`, proves existence of `d > 0` such that `ζ(s) ≠ 0` whenever `|Im(s)| ≤ T` and `Re(s) ≥ 1-d`. | Compact zero-free strip, the topological output of Mathlib nonvanishing plus openness/compactness. |
| `ZeroFreeRegion.meromorphicAt_riemannZeta_one` | `lemma` | Proves ζ is meromorphic at its pole `s = 1` by rewriting it as an analytic regular part plus `(s-1)⁻¹ / Γℝ(s)`. | Supplies the local meromorphic input needed by divisor, residue, and logarithmic-derivative infrastructure. |
| `ZeroFreeRegion.meromorphicOn_riemannZeta_closedBall` | `lemma` | Proves ζ is meromorphic on every closed ball. | Rectangle/Jensen/Perron infrastructure hook for the zero-free and explicit-formula chains. |
| `ZeroFreeRegion.meromorphicOrderAt_riemannZeta_one` | `lemma` | Proves `meromorphicOrderAt riemannZeta 1 = -1`. | Records that the pole at `1` is simple in Mathlib's meromorphic-order API. |
| `ZeroFreeRegion.divisor_riemannZeta_pole_one` | `lemma` | Proves `(MeromorphicOn.divisor riemannZeta U) 1 = -1` for any meromorphic domain `U` containing `1`. | Enables divisor/residue bookkeeping for Jensen, rectangle-residue, and log-derivative work. |
| `ZeroFreeRegion.eventually_ne_zero_riemannZeta_nhdsNE_one` | `lemma` | Proves ζ is eventually nonzero in the punctured neighborhood of its pole `1`. | Supplies the local denominator condition needed for `ζ'/ζ` manipulations near the pole. |
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
| `ZeroFreeRegion.exists_rightNeighborhood_hreal_two_div_sub_one` | `lemma` | Packages the concrete bound as the `hreal` input shape for any future `σOf t` staying in a right neighborhood of `1`. | Discharges the real-axis term of `three_four_one_zero_free_high_height_of_log_deriv_bounds` from local pole control. |
| `ZeroFreeRegion.exists_sigmaOf_log_hreal_two_div_sub_one` | `lemma` | Specializes the concrete `hreal` bound to `σOf t = 1 + a / log |t|` for sufficiently small `a`. | Direct real-axis input for the standard high-height 3-4-1 setup. |
| `ZeroFreeRegion.exists_sigmaOf_log_hreal_two_mul_log_div` | `lemma` | Rewrites that concrete bound as `≤ 2 * log |t| / a`. | Converts the pole denominator into the vertical-height scale used in the quantitative strip. |
| `ZeroFreeRegion.exists_rightNeighborhood_norm_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_sub_one` | `lemma` | For every `C > 1`, proves `‖-ζ'/ζ(σ)‖ < C / (σ-1)` for real `σ > 1` sufficiently close to `1`. | Real-axis norm input for local 3-4-1 estimates. |
| `ZeroFreeRegion.exists_rightNeighborhood_abs_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_sub_one` | `lemma` | For every `C > 1`, proves `|Re(-ζ'/ζ)(σ)| < C / (σ-1)` for real `σ > 1` sufficiently close to `1`. | Real-axis local input for the 3-4-1 contradiction estimates. |
| `ZeroFreeRegion.exists_rightNeighborhood_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_sub_one` | `lemma` | For every `C > 1`, proves `Re(-ζ'/ζ)(σ) < C / (σ-1)` for real `σ > 1` sufficiently close to `1`. | Direct real-axis upper bound for the 3-4-1 contradiction estimates. |
| `ZeroFreeRegion.exists_rightNeighborhood_hreal_const_div_sub_one` | `lemma` | For every `C > 1`, packages the flexible bound as the `hreal` input shape for any future `σOf t` staying in a right neighborhood of `1`. | Flexible real-axis input for the high-height 3-4-1 assembly. |
| `ZeroFreeRegion.exists_sigmaOf_log_hreal_const_div_sub_one` | `lemma` | For every `C > 1`, specializes the flexible `hreal` bound to `σOf t = 1 + a / log |t|` for sufficiently small `a`. | Flexible real-axis input for the standard high-height 3-4-1 setup. |
| `ZeroFreeRegion.exists_sigmaOf_log_hreal_const_mul_log_div` | `lemma` | For every `C > 1`, rewrites the flexible bound as `≤ C * log |t| / a`. | Flexible vertical-height real-axis input for the standard high-height setup. |
| `ZeroFreeRegion.exists_sigmaOf_log_two_t_norm_bound_const_mul_log_div` / `ZeroFreeRegion.exists_sigmaOf_log_two_t_bound_const_mul_log_div` | `lemma` | Uses the half-plane L-series norm bound to control the `σ+2it` point by `≤ C * log |t| / a`. | Records the honest absolute-convergence bound and its `1/a` loss; the classical target still needs a height-independent `O(log |t|)` vertical estimate. |
| `ZeroFreeRegion.sigmaOf_log_weak_two_t_margin_impossible` | `lemma` | Proves that if the `σ+2it` term keeps a `Ctwo/a` coefficient with `Ctwo ≥ 1`, then the required 3-4-1 constant inequality cannot hold for any positive width `c`. | Formalizes the obstruction: absolute convergence alone cannot close the de la Vallee Poussin `c/log|t|` strip. |
| `ZeroFreeRegion.no_sigmaOf_log_margin_constants_with_weak_two_t` | `lemma` | Existential version: no positive `a,c` satisfy the standard 3-4-1 margin when both real-axis and weak `σ+2it` coefficients are at least one. | Prevents the weak `σ+2it` theorem from being mistaken for the missing vertical-strip estimate. |
| `ZeroFreeRegion.exists_sigmaOf_log_classical_zero_free_region_of_log_deriv_bounds` | `lemma` | Packages the standard `σ(t)=1+a/log |t|` choice into the verified 3-4-1 and compact-patch assembly. | Reduces the classical zero-free target to the two shifted log-derivative estimates plus the negativity margin. |
| `ZeroFreeRegion.exists_sigmaOf_log_classical_zero_free_region_of_shift_bounds` | `lemma` | Specializes the closure theorem to shifted bounds of the form `-1/(σ-β)+Czero log|t|` and `Ctwo log|t|`. | Leaves exactly the two zeta-specific shifted estimates plus a constant inequality. |
| `ZeroFreeRegion.classical_zero_free_region_of_sigma_log_shift_estimates` | `lemma` | Combines local pole control, constant selection, the standard `σ=1+a/log|t|` choice, and compact patching. | Turns the classical zero-free target into exactly two shifted log-derivative estimates. |
| `ZeroFreeRegion.classical_zero_free_region_of_sigma_log_shift_estimates_five_fourths` | `lemma` | Fixes the real-axis coefficient to `5/4`, which satisfies `1 < 5/4 < 4/3`. | Removes the abstract `C` range hypotheses from the shifted-estimate closure. |
| `ZeroFreeRegion.classical_zero_free_region_of_sigma_log_shift_estimates_same_const` | `lemma` | Uses one nonnegative logarithmic coefficient `B` for both shifted estimates. | Most ergonomic conditional interface for the remaining zero-free-region analytic estimates. |
| `ZeroFreeRegion.classical_zero_free_region_of_sigma_log_shift_estimates_same_const_at_two` | `lemma` | Fixes the height cutoff in the same-constant shifted-estimate closure to `2`. | Exact-height interface matching the statement of `classical_zero_free_region`. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_sigma_log_shift_estimates_same_const` | `lemma` | Packages the remaining analytic input as existence of one nonnegative `B` controlling both shifted estimates above height `2`. | Final conditional interface before proving the zeta-specific shifted logarithmic-derivative estimates. |
| `ZeroFreeRegion.classical_zero_free_region_of_regular_part_bound_and_two_t_bound` | `lemma` | Replaces the zero-candidate shifted estimate by a complex regular-part bound `Re(-ζ'/ζ)(s)+1/(Re(s)-Re(ρ)) ≤ B log |Im(s)|`, plus the `σ+2it` bound. | Direct bridge from the Borel-Caratheodory/Jensen-shaped analytic input to the classical zero-free target. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_regular_part_bound_and_two_t_bound` | `lemma` | Existentially packages the regular-part bound and the `σ+2it` bound under one nonnegative logarithmic coefficient. | Intermediate regular-part interface for the quantitative zero-free-region chain. |
| `ZeroFreeRegion.inv_sub_same_im_re` | `lemma` | Proves `Re((s-ρ)⁻¹)=1/(Re(s)-Re(ρ))` when `Im(ρ)=Im(s)` and `Re(s)>Re(ρ)`. | Algebraic conversion from complex regular parts to the real singular term in the zero-free contradiction. |
| `ZeroFreeRegion.classical_zero_free_region_of_regular_part_norm_bound_and_two_t_bound` | `lemma` | Replaces the regular-part real estimate by the norm estimate `‖-ζ'/ζ(s)+(s-ρ)⁻¹‖ ≤ B log |Im(s)|`, plus the `σ+2it` bound. | Current narrowest conditional interface matching Borel/Jensen norm estimates. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_regular_part_norm_bound_and_two_t_bound` | `lemma` | Existentially packages the norm regular-part bound and the `σ+2it` bound under one nonnegative logarithmic coefficient. | Quotient-notation norm bridge before proving the zeta-specific estimates. |
| `ZeroFreeRegion.classical_zero_free_region_of_neg_logDeriv_regular_part_norm_bound_and_two_t_bound` | `lemma` | Same norm-bound closure written in Mathlib's natural `-logDeriv ζ` notation. | Lets future Borel/Jensen estimates feed the zero-free chain without manual quotient rewriting. |
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
| `ZeroFreeRegion.classical_zero_free_region_of_exists_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height` | `lemma` | Existential high-height wrapper for the same two positive `logDeriv ζ` estimates. | Final high-height conditional interface before proving the zeta-specific regular-part and vertical log-derivative bounds. |
| `ZeroFreeRegion.classical_zero_free_region_of_logDeriv_regular_part_norm_affine_log_bound_and_vertical_logDeriv_norm_affine_log_bound_high_height` | `lemma` | Converts high-height estimates of the natural form `A + B log |Im|` into the multiplicative logarithmic interface using `log |Im| ≥ 1` above height `3`. | Lets Borel/Jensen estimates with additive constants feed the zero-free chain without manual constant absorption. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_logDeriv_regular_part_norm_affine_log_bound_and_vertical_logDeriv_norm_affine_log_bound_high_height` | `lemma` | Existential version of the high-height affine-log closure. | Most permissive current conditional interface for the remaining zeta-specific estimates. |
| `ZeroFreeRegion.classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_affine_bounds_high_height` | `lemma` | Coordinate version of the affine-log closure, with estimates stated in real variables `σ, β, t`. | Lets future analytic estimates written directly on `σ+it` and zero candidates `β+it` feed the complex zero-free chain. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_affine_bounds_high_height` | `lemma` | Existential coordinate affine-log wrapper. | Current most ergonomic conditional interface for hand-written Borel/Jensen estimates. |
| `ZeroFreeRegion.classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_one_add_log_bound_high_height` | `lemma` | Coordinate high-height closure from a single `C(1+log |t|)` bound for both regular-part and vertical log-derivative estimates. | Matches the common Big-O output shape of analytic estimates while preserving a proved route to the classical target. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_one_add_log_bound_high_height` | `lemma` | Existential single-constant `C(1+log |t|)` wrapper. | Simplest current conditional interface for the remaining zeta-specific estimates. |
| `ZeroFreeRegion.log_abs_add_three_le_two_log_abs` | `lemma` | Proves `log(|t|+3) ≤ 2 log |t|` for `|t| ≥ 3`. | Normalizes a common safe-height logarithmic scale to the classical `log |t|` scale. |
| `ZeroFreeRegion.classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_log_abs_add_three_bound_high_height` | `lemma` | Coordinate high-height closure from a single `C log(|t|+3)` bound for both remaining log-derivative estimates. | Accepts another standard analytic-number-theory estimate shape without changing the final target. |
| `ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_log_abs_add_three_bound_high_height` | `lemma` | Existential `C log(|t|+3)` wrapper. | Alternative simplest current interface when estimates are stated with `log(|t|+3)`. |
| `ZeroFreeRegion.meromorphicOn_logDeriv_riemannZeta_closedBall` | `lemma` | Proves the logarithmic derivative `logDeriv riemannZeta` is meromorphic on every closed ball. | Local analytic input for future Borel-Caratheodory/Jensen bounds on `ζ'/ζ`. |
| `ZeroFreeRegion.borelCaratheodory_zero_centered` | `lemma` | Translates Mathlib's vanishing-at-zero Borel-Caratheodory theorem to disks centered at arbitrary `c`. | Reusable disk-centered tool for future estimates around points such as `1+it`. |
| `ZeroFreeRegion.borelCaratheodory_centered` | `lemma` | Translates Mathlib's general Borel-Caratheodory theorem to disks centered at arbitrary `c`. | Removes the repeated change-of-variables step from future zero-free-region estimates. |
| `ZeroFreeRegion.borelCaratheodory_centered_half_radius_bound` | `lemma` | Converts the centered Borel-Caratheodory rational disk factors to the fixed bound `2M + 3‖f(c)‖` on the half-radius subdisk. | Gives future local estimates a cleaner constant-bookkeeping interface. |
| `ZeroFreeRegion.borelCaratheodory_sub_centered` | `lemma` | Bounds `‖f z - f c‖` from a real-part bound on the centered function `f - f(c)`. | Direct oscillation form for future regular-part/log-derivative estimates. |
| `ZeroFreeRegion.borelCaratheodory_sub_centered_half_radius_bound` | `lemma` | Converts the centered oscillation Borel estimate to `‖f z - f c‖ ≤ 2M` on the half-radius subdisk. | Cleaner constant interface for regular-part and centered log-derivative estimates. |
| `ZeroFreeRegion.jensen_circleAverage_log_norm_riemannZeta_closedBall` | `lemma` | Specializes Mathlib's Jensen formula to ζ on closed balls. | Connects zeta meromorphicity directly to Jensen zero/divisor bookkeeping. |
| `ZeroFreeRegion.jensen_circleAverage_log_norm_logDeriv_riemannZeta_closedBall` | `lemma` | Specializes Jensen formula to `logDeriv riemannZeta` on closed balls. | Direct Jensen input for future logarithmic-derivative growth and zero-count estimates. |
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
| `ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le_half_radius` / `ZeroFreeRegion.borelCaratheodory_sub_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le_half_radius` | `lemma` | Half-radius right-half-strip Borel bounds for positive `logDeriv ζ`. | Matches the sign convention of local regular-part estimates before translating to `-ζ'/ζ`. |
| `ZeroFreeRegion.differentiableOn_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re` | `lemma` | Signed version for `-logDeriv ζ` on positive-height right half-strips. | Matches the sign convention used by the 3-4-1 inequality. |
| `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le` / `ZeroFreeRegion.borelCaratheodory_sub_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le` | `lemma` | Borel bounds for `-logDeriv ζ` with automatic differentiability. | Lets future estimates stay in the signed `-ζ'/ζ` notation through the Borel route. |
| `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le_half_radius` | `lemma` | Half-radius constant-bound version of the signed `-logDeriv ζ` Borel estimate. | Removes the disk denominator terms from the most common signed Borel application. |
| `ZeroFreeRegion.borelCaratheodory_sub_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le_half_radius` | `lemma` | Half-radius oscillation version for signed `-logDeriv ζ`. | Direct centered-control interface for future local regular-part estimates. |
| `ZeroFreeRegion.jensen_circleAverage_log_norm_verticalRegion` | `lemma` | Applies Jensen's formula on a `σ+it` disk from ambient `verticalRegion` meromorphicity. | Direct entry point for future zero-count/log-derivative Jensen estimates. |
| `ZeroFreeRegion.differentiableOn_riemannZeta_verticalRegion_of_pos_height` / `ZeroFreeRegion.meromorphicOn_logDeriv_riemannZeta_verticalRegion` | `lemma` | Supplies ζ differentiability on positive-height vertical regions and log-derivative meromorphicity on all such regions. | Zeta-specific regularity layer feeding the Borel/Jensen wrappers. |
| `ZeroFreeRegion.jensen_circleAverage_log_norm_riemannZeta_verticalRegion` / `ZeroFreeRegion.jensen_circleAverage_log_norm_logDeriv_riemannZeta_verticalRegion` | `lemma` | Specializes the vertical-region Jensen wrapper to ζ and `logDeriv ζ`. | Ready-to-use zeta Jensen statements for future zero-count/log-derivative estimates. |

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

- [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) (Lean 4) — PNT via Wiener-Ikehara
- Avigad et al. (2007) — Elementary PNT in Isabelle
- Harrison (2009) — Newman's analytic PNT in HOL Light
- Mathlib's `riemannZeta` — Zeta function basics by Loeffler & Stoll

## Citation

If you use this work in your research, please cite:

```bibtex
@software{riemann_pnt_lean4,
  title = {Lean 4 Infrastructure Toward Analytic Prime Number Theorem Formalization},
  year = {2026},
  url = {https://github.com/cc-chen-tech/riemann-pnt-lean4}
}
```

## License

Apache 2.0 — same as Mathlib.
