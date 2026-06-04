# Formal Theorem Inventory

This inventory separates proved Lean declarations from target statements.  It is
intended for reviewers and for future work planning.

Current verified baseline:

```bash
lake build
rg -n "sorry|admit|axiom" *.lean
```

At the time of writing, `lake build` succeeds and the placeholder search has no
Lean-source matches.

## Proved Project-Local Results

### `ZeroFreeRegion.lean`

Core verified declarations:

- `trig_identity_nonneg`
  proves `3 + 4 cos theta + cos (2 theta) >= 0`.
- `log_deriv_zeta_re_series`
  extracts the real-part Dirichlet series for `-zeta'/zeta`.
- `log_deriv_zeta_nonneg_combination`
  proves the full 3-4-1 logarithmic-derivative nonnegativity combination.
- `classical_zero_free_region_compact`
  proves a nonconstructive positive-width zero-free strip for each bounded
  height.
- `residue_bounds`
  proves `1 < (sigma - 1) * Re(zeta(sigma)) <= sigma` for `sigma > 1`.
- `log_deriv_zeta_pos_real`
  proves positivity of the real-axis logarithmic derivative expression.
- `log_deriv_zeta_antitone`
  proves the real-axis antitone property of the logarithmic derivative series.

Supporting declarations include:

- `zeta_no_zeros_on_line_one`
- `riemannZeta_pos_of_real_gt_one`
- `log_riemannZeta_dirichlet_series`
- `riemannZeta_re_eq_tsum_real`
- `summable_one_div_rpow`
- `riemannZeta_re_gt_one`
- `riemannZeta_gt_one_div_sub`
- `riemannZeta_re_le_sigma_div_sub`
- `log_deriv_zeta_real_eq_series`

Private technical lemma:

- `natCast_cpow_neg_re`
  computes `Re ((n : C)^(-s))` for positive natural `n`.

### `PrimeNumberTheorem.lean`

Core verified declarations:

- `logIntegral_asymptotic`
  proves the asymptotic relation needed for `Li(x) ~ x / log x`.
- `pnt_forms_equivalent`
  proves equivalence of the project-local `PNTForm1`, `PNTForm2`, and
  `PNTForm3`.
- `nontrivial_zero_symmetric`
  proves symmetry of nontrivial zeros under `rho -> 1 - rho`.
- `nontrivial_zero_symmetric'`
  packages the symmetry as preservation of `IsNontrivialZero`.
- `riemannZeta_ne_zero_of_re_le_zero`
  excludes nontrivial zeros in `Re(s) <= 0`, except for the trivial zero
  locations.
- `nontrivial_zero_in_critical_strip`
  derives `0 < Re(s) < 1` for nontrivial zeros.
- `finite_nontrivial_zeros_bounded_height`
  proves finiteness of nontrivial zeros with bounded imaginary part.
- `rh_iff_nontrivial_zeros_on_line`
  identifies the local RH statement with the condition that every nontrivial
  zero has real part `1/2`.
- `rh_statement_iff_mathlib`
  relates the local RH statement to Mathlib's `RiemannHypothesis`.
- `riemannZeta_pole_simple`
  proves `(s - 1)^2 zeta(s) -> 0` at the punctured neighborhood of `1`.
- `rh_zero_symmetric_self_consistent`
  records the compatibility of RH with zero symmetry.
- `zero_contribution`
  rewrites the oscillatory contribution of a zero.
- `PNTForm2_iff_PNTForm1`, `PNTForm3_iff_PNTForm2`, and
  `PNTForm3_iff_PNTForm1`
  package reverse orientations of the already-proved PNT-form equivalences.

Supporting declarations include:

- `primeCounting_eq_mathlib`
- `vonMangoldt_eq_mathlib`
- `chebyshevPsi_eq_mathlib`
- `logIntegral_integration_by_parts`
- `logIntegral_nonneg`
- `logIntegral_pos`
- `riemannZeta_not_frequently_zero_nhdsNE_of_ne_one`
- `RH_PrimeCountingLiErrorBound_iff_RH_ErrorBound`
- `rh_iff_optimal_error_of_pointwise_implications`
- `RH_ErrorBound_of_rh_iff_optimal_error`
- `RiemannHypothesis_of_rh_iff_pointwise_error`
- `explicit_formula_von_mangoldt_iff_re_im_error_tendsto_zero`
- `explicit_formula_von_mangoldt_iff_re_im_error_isLittleO_one`
- `hardy_zeros_abs_unbounded_of_two_signed_moments`
- `hardy_zeros_unbounded_of_two_signed_moments`
- `hardy_zeros_abs_unbounded_of_integral_asymptotic_one_two`
- `hardy_zeros_unbounded_of_integral_asymptotic_one_two`
- `infinitely_many_zeros_on_critical_line_of_two_signed_moments`
- `infinitely_many_zeros_on_critical_line_of_integral_asymptotic_one_two`
- `infinitely_many_zeros_on_critical_line_of_hardy_littlewood_lower_bound`
- `exists_zero_on_critical_line_of_two_signed_moments`
- `exists_zero_on_critical_line_of_integral_asymptotic_one_two`
- `exists_zero_on_critical_line_of_hardy_littlewood_lower_bound`
- `exists_zero_on_critical_line_of_selberg_zero_proportion`
- `exists_zero_on_critical_line_of_conrey_40_percent_target`

### `HardyTheorem.lean`

Core verified declarations:

- `completedRiemannZeta_conj_eq_of_one_lt_re`
- `completedRiemannZeta₀_conj_eq`
- `completedRiemannZeta_critical_line_real`
- `Gammaℝ_re_im_arg`
- `hardyZ_zero_implies_zeta_zero`
- `hardyZ_zero_iff_zeta_zero`
- `hardyZ_continuous`
- `hardyZ_eventually_const_sign_of_finite_zeros`
- `weightedIntegralOf_neg`
- `hardy_two_signed_moments_target_iff_integral_asymptotic_one_two`
- `hardy_theorem_target_of_two_signed_moments`
- `hardy_theorem_target_of_integral_asymptotic_one_two`
- `exists_zero_on_critical_line_of_hardy_theorem_target`
- `exists_zero_on_critical_line_of_two_signed_moments`
- `exists_zero_on_critical_line_of_integral_asymptotic_one_two`
- `hardy_theorem_target_iff_abs_unbounded_of_bounded_strips`
- `hardy_zeros_abs_unbounded_of_two_signed_moments_of_bounded_strips`
- `hardy_zeros_unbounded_of_two_signed_moments_of_bounded_strips`
- `hardy_zeros_abs_unbounded_of_integral_asymptotic_one_two_of_bounded_strips`
- `hardy_zeros_unbounded_of_integral_asymptotic_one_two_of_bounded_strips`
- `hardy_zeros_unbounded_iff_abs_unbounded`

These prove the local Hardy-Z setup and the equivalence between zeros of
`hardyZ` and zeros of `zeta` on the critical line, plus conditional bridges
from the signed-moment targets to Hardy's infinite and unbounded-height zero
interfaces.  They do not prove Hardy's theorem unconditionally; the moment
estimates needed for Hardy's theorem remain targets.

### `GammaResidue.lean`

Core verified declarations:

- `gamma_residue_at_zero`
- `gamma_residue_at_neg_natural`
- `residue_at_zero_eq_one`
- `residue_at_minus_one_eq_minus_one`
- `residue_at_minus_two_eq_half`

The general theorem proves the residue of `Gamma` at nonpositive integers:

```text
Res(Gamma, -n) = (-1)^n / n!
```

### `EulerAndLfunctions.lean`

This file contains wrappers around existing Mathlib results:

- `EulerProduct.euler_product`
- `EulerProduct.euler_product_inv`
- `ZetaValues.zeta_two`
- `ZetaValues.zeta_zero`
- `ZetaValues.zeta_pos_real`
- `ZetaValues.zeta_ne_zero`
- `DirichletNonvanishing.lseries_ne_zero`
- `DirichletNonvanishing.lfunction_ne_zero`

These are useful for the project API but should not be presented as new
mathematical theorems.

### `RiemannExplorer.lean`

This file provides project-level definitions and wrappers:

- `RiemannHypothesis.riemannZetaSeries`
- `RiemannHypothesis.euler_product`
- `RiemannHypothesis.zeta_pole_at_one`
- `RiemannHypothesis.functional_equation`
- `RiemannHypothesis.riemannHypothesis_iff_zeros_on_critical_line`
- `KnownResults.zeta_no_zeros_on_one_line`
- `KnownResults.zeta_no_zeros_on_zero_line`
- `KnownResults.infinitely_many_zeros_on_critical_line_of_hardy_littlewood_lower_bound`
- `KnownResults.exists_zero_on_critical_line_of_two_signed_moments`
- `KnownResults.exists_zero_on_critical_line_of_integral_asymptotic_one_two`
- `KnownResults.exists_zero_on_critical_line_of_hardy_littlewood_lower_bound`
- `KnownResults.exists_zero_on_critical_line_of_selberg_zero_proportion`

It also records exploratory strategy strings.  Those strings are explanatory
metadata, not proof results.

## Target Statements, Not Proved Theorems

The following declarations are intentionally `def ... : Prop` targets.  They
are not exported as theorems and should not be cited as proved.

As of `2026-06-03`, there are **23** target declarations:

- `HardyTheorem` namespace: **11**  
- `PrimeNumberTheorem` namespace: **9**  
- `ZeroFreeRegion` namespace: **2**  
- `RiemannExplorer` namespace: **1**  

### `ZeroFreeRegion.lean`

- `classical_zero_free_region`
  target: a uniform zero-free region
  `Re(s) >= 1 - c / log |Im(s)|`.
- `vinogradov_korobov_zero_free_region`
  target: the stronger Vinogradov-Korobov zero-free region.

### `PrimeNumberTheorem.lean`

- `rh_iff_optimal_error`
  target: equivalence between RH and a prime-counting error term.
- `explicit_formula_von_mangoldt`
  target: a von Mangoldt explicit formula in midpoint/truncated-limit form,
  using `chebyshevPsi0` and `finiteNontrivialZeroSum`.
- `PNTForm1`, `PNTForm2`, `PNTForm3`
  local PNT-format targets:
  `pi(x) ~ x / log x`, `pi(x) ~ Li(x)`, and `psi(x) ~ x`. These are
  intentionally target placeholders because the bridge to a full analytic proof
  runs through explicit-formula machinery.

### `HardyTheorem.lean`

- `integral_asymptotic_target`
- `hardy_two_signed_moments_target`
- `weightedIntegralOf_tail_dominates`
- `hardy_theorem_target`
- `hardy_zeros_unbounded_target`
- `hardy_zeros_abs_unbounded_target`
- `hardy_littlewood_lower_bound_target`
- `selberg_zero_proportion_target`
- `gamma_asymptotic_half_plus_it_target`
- `theta_asymptotic_target`
- `approximate_functional_equation_target`

These replace earlier overstrong or false theorem statements.  In particular,
eventual positivity of a function is not by itself enough to imply eventual
positivity of its integral from `0` to `T`; an additional tail-dominance
hypothesis is needed.  The weighted-integral positivity/negativity bridge and
the finite-zero contradiction under signed-moment and tail-dominance hypotheses
are now proved lemmas, not target statements.

### `RiemannExplorer.lean`

- `conrey_40_percent_zeros_on_critical_line_target`
  target: a positive-proportion statement on critical-line zeros, expressed as
  a target alias for `HardyTheorem.selberg_zero_proportion_target`.

Current status in `HardyTheorem.lean` target list:

- `hardy_zeros_abs_unbounded_target` is a monotone reformulation of
  `hardy_zeros_unbounded_target`.
- `hardy_littlewood_lower_bound_target` is available as a derived output if
  `selberg_zero_proportion_target` is available.

Detailed dependency maps for the four unfinished analytic chains are collected
under `docs/missing-chains-index.md`.

## Dependency Boundary

The project uses substantial Mathlib infrastructure, including:

- `riemannZeta` and its Euler product;
- the functional equation and nonvanishing on `Re(s) >= 1`;
- `riemannZeta_residue_one`;
- von Mangoldt L-series identities;
- zeta asymptotics around the harmonic-series expansion;
- compactness and analytic continuation APIs.

The project-local novelty is the assembly and formal proof of the intermediate
zeta-function infrastructure listed above, especially the real-part
logarithmic-derivative series, the 3-4-1 combination, compact zero-free strip,
and residue-scale inequalities.

## Missing Chains for a Complete Analytic PNT

To turn the current framework into a full de la Vallee Poussin proof with error
term, the following chains remain:

1. **Quantitative zero-free region.**
   Need zeta growth and logarithmic-derivative estimates, likely through
   Hadamard factorization or Borel-Caratheodory, to upgrade the compact strip to
   `c / log |t|`.
2. **Explicit formula.**
   Need Perron's formula, contour integration, residue calculus, edge estimates,
   and a correct truncated/principal-value zero sum.
3. **RH error equivalence.**
   Need zero-counting estimates, explicit formula bounds under RH, and partial
   summation from Chebyshev functions to prime counting.
4. **Hardy theorem.**
   Need corrected moment asymptotics for Hardy's Z-function and supporting
   special-function asymptotics.
