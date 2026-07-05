# Three Directions Research Worktree

This worktree tracks concrete Lean progress along three zero-free/PNT/RH-adjacent
routes.  The branch is based on current `main`; the goal is to add verified
interfaces and small lemmas without overstating any unresolved analytic theorem.

## Baseline

- Worktree: `/Users/luicy/AI/Riemann/.worktrees/riemann-three-directions-research`
- Branch: `research/three-directions`
- Current base: `0946b01 feat(zero-free): lift zeta growth handoff to circle averages`
- Research work on this branch currently covers:
  - signed BTY detector/Borel facades;
  - center-one and general-center zero-pair bridges;
  - explicit-formula tail bridges from eventual/no-new-zero and global-height inputs;
  - a zeta polynomial-growth handoff to the classical high-height
    `log |t|` scale.
- Rule: do not present route interfaces or `def ... : Prop` targets as proved
  mathematics.

## Direction 1: BTY detector and Borel bounds

Verified assets now include:

- the BTY degree-16 trigonometric detector;
- the automatic finite Dirichlet-series identity
  `log_deriv_zeta_finset_series_identity`, so the detector `hseries` input is
  no longer a manual hypothesis in the automatic detector route;
- the pointwise BTY detector nonnegativity theorem
  `btyDetectorPolynomial_nonneg`;
- the simplified uniform BTY penalty
  `log_deriv_zeta_bty_detector_one_lower_bound_of_uniform_shift_upper_bound_simplified`;
- finite-family norm-bound facades
  `log_deriv_zeta_bty_detector_one_lower_bound_of_uniform_vertical_norm_bound`
  and
  `log_deriv_zeta_bty_detector_one_lower_bound_of_uniform_vertical_log_bound`;
- the global-vertical-to-finite-BTY handoff
  `btyDetector_uniform_vertical_log_bound_of_global_log_abs_add_three_bound`
  and the composed lower bound
  `log_deriv_zeta_bty_detector_one_lower_bound_of_global_vertical_log_abs_add_three_bound`;
- the automatic BTY finite-height comparison
  `btyDetector_log_abs_mul_add_three_le_log_seventeen_mul_abs_add_three`
  and its no-manual-`hlog` lower-bound wrapper
  `log_deriv_zeta_bty_detector_one_lower_bound_of_global_vertical_log_abs_add_three_bound_auto`;
- the unsigned simplified Borel facade
  `log_deriv_zeta_bty_detector_one_lower_bound_of_uniform_right_shift_borel_family_simplified`;
- the signed simplified Borel facade added on this branch:
  `log_deriv_zeta_bty_detector_one_lower_bound_of_uniform_signed_right_shift_borel_family_simplified`;
- the polynomial-growth-to-`log |t|` zeta handoff:
  `log_norm_riemannZeta_sigma_it_le_affine_log_abs_of_polynomial_growth`.

Next useful step:

```lean
log_deriv_zeta_bty_detector_one_lower_bound_of_uniform_vertical_pair_bound
```

The formerly separate `hseries` step is now closed in Lean.  The next bridge is
not a purely formal wrapper: the existing shift-pair estimates cover the
classical `t, 2t` shape, while the Borel facade accepts a finset-wide
upper-bound hypothesis over `btyDetectorSupport.erase 1`.  Closing that bridge
requires a uniform high-height/log bound for every BTY support index.  The new
finite-family norm facades make the exact required input explicit, and the
global-vertical handoff now reduces the finite-family part to a one-variable
bound
`‖logDeriv ζ(σ + i u)‖ <= B log(|u|+3)`.  The finite log-scale comparison is
now automatic at the conservative common scale `log(17 * (|t|+3))`.
The new polynomial-growth handoff removes one piece of height bookkeeping once
a usable zeta polynomial-growth input is available, but it does not prove that
input or a log-derivative estimate.

## Direction 2: Stechkin/Heath-Brown pair positivity

Verified assets now include:

- center-one zero-pair bridges over `nontrivialZerosFinset`;
- a general-center finite paired-sum bridge over full and new-zero finsets;
- paired-average bridges over full and new-zero finsets:
  `nontrivialZerosFinset_pair_average_nonnegative_of_laplace_pair_positive`;
  `nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_laplace_pair_positive`.
- center-one paired-average convenience wrappers:
  `nontrivialZerosFinset_pair_average_nonnegative_of_laplace_pair_positive_one`;
  `nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_laplace_pair_positive_one`.

Important boundary:

The general-center paired average is not an unpaired real-part average.  Turning
it into an unpaired sum needs a proof that the chosen center-pair map preserves
the relevant zero set.  For zeta this is available at center `1`, via
`rho -> 1 - rho`, not for an arbitrary center.

Next useful step is no longer another finset wrapper.  It needs a concrete
Stechkin/Heath-Brown kernel positivity theorem that instantiates
`LaplacePairPositive F 1`; without that analytic positivity input, the remaining
work would only rename existing lemmas.

## Direction 3: explicit formula / PNT error bridge

Verified assets now include:

- the public vertical-line and power-error route predicates:
  `NoZerosOnVerticalLine`, `PsiPowerErrorBelowTwoThirds`,
  `PsiPowerErrorBelowLine`, and `ExplicitFormulaConversePowerTarget`;
- the `1/3`/`2/3` reflection equivalence
  `exists_nontrivial_zero_on_one_third_iff_two_thirds`;
- direct conditional bridges from RH, a zero-free right half-plane
  `Re(s) >= 2/3`, a concrete `psi` power error below `2/3`, or the general
  explicit-formula converse target to no zeros on `Re(s)=1/3`;
- finite explicit-formula truncation increment identities;
- new-zero norm/count tail bounds under RH;
- eventual-no-new-zero tail convergence;
- composed bridges:
  `explicit_formula_von_mangoldt_of_RH_base_and_eventually_no_new_zeros_via_sum_tail`;
  `explicit_formula_von_mangoldt_of_RH_base_and_eventually_no_new_zeros_via_card_tail`.
- global-height-bound-to-tail bridges:
  `nontrivialZerosFinset_eventually_sdiff_eq_empty_of_global_height_bound`;
  `new_zero_inv_norm_tail_tendsto_zero_of_global_height_bound`;
  `new_zero_card_tail_tendsto_zero_of_global_height_bound`;
  `explicit_formula_von_mangoldt_of_RH_base_and_global_height_bound_via_sum_tail`;
  `explicit_formula_von_mangoldt_of_RH_base_and_global_height_bound_via_card_tail`.
- truncated explicit-formula converse facades:
  `no_zeros_on_two_thirds_of_truncated_explicit_formula_converse_route`;
  `no_zeros_on_one_third_of_truncated_explicit_formula_converse_route`;
  `no_zeros_on_reflected_line_of_truncated_explicit_formula_converse_route`.

Important boundary:

These theorems still assume the base explicit-formula identity at a stable
truncation.  The global-height variants are route interfaces, not realistic
unconditional inputs for zeta zeros.  They do not prove Perron's formula,
contour shifting, or the converse/oscillation theorem turning
`psi(x) - x = O(x^(beta - delta))` into zero exclusion.  The current Lean value
is that the formal path from any such future input at `beta = 2/3` to the
claimed `Re(s)=1/3` exclusion is now explicit and smoke-checked.

## Hard Gaps

- No classical zero-free region `Re(s) >= 1 - c / log |t|` is proved here.
- No Perron formula or contour-shift explicit formula is proved here.
- No explicit-formula converse / oscillation theorem is proved here.
- No result here proves RH or an unconditional zero-free vertical line.
