# Missing Chains Index

This page tracks the remaining mathematical chains that are not proved in the
current Lean checkout.  The project currently builds and contains no
`sorry`/`admit`/`axiom` placeholders in Lean source, but several deep goals are
intentionally recorded as `def ... : Prop` target statements.

At present there are **19** unresolved mathematical `def ... : Prop` targets,
partitioned into exactly **4** analytic chains.  The recursive scanner also
tracks 5 route interfaces and 7 reusable Prop predicates so subdirectory
interfaces cannot be hidden by the target count:

1. Quantitative zero-free region
2. Explicit formula
3. RH / prime-counting error equivalence
4. Hardy theorem

The chain-specific notes are maintained separately so that work can proceed in
parallel:

- `docs/implementation-standards.md`
  rules for promoting `def ... : Prop` targets to proved declarations, including
  forbidden shortcuts and corrected-target criteria;
- `docs/zero-free-region-chain.md`
  quantitative zero-free region, from the verified 3-4-1 infrastructure to
  `Re(s) >= 1 - c / log |Im(s)|`;
- `docs/explicit-formula-chain.md`
  the proved principal-value von Mangoldt formula and the remaining separate
  quantitative truncated-error route;
- `docs/rh-error-equivalence-chain.md`
  equivalence between RH and prime-counting error terms;
- `docs/hardy-theorem-chain.md`
  Hardy Z-function moment estimates and critical-line zeros.

## Evaluation Boundary

This page is a local proof-roadmap document.  It should not be used by itself
to make external novelty claims.

Two questions must stay separate:

- **Internal proof progress:** which target statements remain in this checkout,
  and which proved Lean declarations currently anchor each chain.
- **External academic value:** how this checkout compares with existing PNT and
  zeta/L-function formalizations, including Isabelle/HOL elementary PNT,
  HOL Light Newman's proof, Lean `PrimeNumberTheoremAnd`, Mathlib's
  zeta/L-function library, and any newer Lean repositories current at
  submission time.

The safe publication claim is a focused one: this repository develops verified
Lean 4 infrastructure for the de la Vallee Poussin 3-4-1 machinery, proves the
classical `c/log |t|` zero-free region, and derives the ordinary PNT through a
multiplicity-aware moving-height explicit formula, including the de la Vallee
Poussin-form Chebyshev `psi` remainder.  It is not the first PNT formalization,
does not yet prove the corresponding prime-counting `pi-Li` result, and is not
a proof of RH.

For the zero-free-region route, the classical `c/log |t|` milestone is now
proved by `classical_zero_free_region_proved`.  The remaining target in this
chain is the stronger Vinogradov-Korobov region, which requires exponential-sum
technology rather than more local Jensen/Borel wrappers.

## Chain Status Summary

| Chain | Current Lean target status | Main correction before proof work | Smallest useful next step | Open target count |
| --- | --- | --- | --- | --- |
| Quantitative zero-free region | `classical_zero_free_region` is proved; `vinogradov_korobov_zero_free_region` remains a target | Develop exponential-sum estimates for the stronger width | Formalize the Vinogradov-Korobov exponential-sum input without weakening the proved classical theorem | 1 |
| Explicit formula | `ExplicitFormulaTruncatedTarget`, the moving-height formula, ordinary PNT, and the de la Vallee Poussin-form `psi` remainder are proved | Preserve the natural-sample jump convention and multiplicities in stronger reusable variants | Prove the quantitative Abel-integral estimate needed for the corresponding `pi-Li` remainder | 0 |
| RH error equivalence | Ordinary PNT is proved; `rh_iff_optimal_error` is proved in both directions by `rh_iff_optimal_error_proved` | No remaining implication gap; RH itself and its equivalent error predicates remain unproved unconditionally | Reuse the completed equivalence when another endpoint supplies either RH or the error bound | 4 |
| Hardy theorem | `hardy_theorem_target` and related moment/asymptotic targets are `def ... : Prop` targets | Use an unbounded-height zero target as the main theorem; use signed moment targets, not merely nonzero constants | Prove bounded-zero eventual-sign control and generic asymptotic sign lemmas | 11 (7 in `HardyTheorem`, 3 in `HardyTheorem.Details`, 1 in `KnownResults`) |

## Target-to-Chain Mapping

| File | Target | Chain | Why it is still open |
| --- | --- | --- | --- |
| `ZeroFreeRegion.lean` | `vinogradov_korobov_zero_free_region` (global namespace) | Quantitative zero-free region | Requires Vinogradov–Korobov exponential-sum technology |
| `PrimeNumberTheorem.lean` | `RH_PsiErrorBound` | RH error equivalence | Equivalent to RH by a proved theorem; neither proposition is proved unconditionally |
| `PrimeNumberTheorem.lean` | `RH_ThetaErrorBound` | RH error equivalence | Equivalent to `RH_PsiErrorBound`; RH implies it, but it remains unresolved without assuming RH |
| `PrimeNumberTheorem.lean` | `RH_PrimeCountingLiErrorBound` | RH error equivalence | Equivalent to RH by proved forward and reverse implications; not known unconditionally |
| `PrimeNumberTheorem.lean` | `RH_ErrorBound` | RH error equivalence | Pointwise reformulation of `RH_PrimeCountingLiErrorBound`; RH implies it |
| `HardyTheorem.lean` | `integral_asymptotic_target` | Hardy theorem | Signed-moment asymptotic input |
| `HardyTheorem.lean` | `hardy_two_signed_moments_target` | Hardy theorem | Asymptotics for the first two weighted moments |
| `HardyTheorem.lean` | `hardy_theorem_target` | Hardy theorem | Combined target of Hardy theorem output |
| `HardyTheorem.lean` | `hardy_zeros_unbounded_target` | Hardy theorem | Harder zero distribution output in an unbounded-height form |
| `HardyTheorem.lean` | `hardy_zeros_abs_unbounded_target` | Hardy theorem | Equivalent form requiring symmetry/absolute-value zero extraction |
| `HardyTheorem.lean` | `hardy_littlewood_lower_bound_target` | Hardy theorem | Quantitative lower bound on critical-line zeros needed for positive density |
| `HardyTheorem.lean` | `selberg_zero_proportion_target` | Hardy theorem | Proportional form of Hardy-type lower bounds |
| `HardyTheorem.lean` | `HardyTheorem.Details.gamma_asymptotic_half_plus_it_target` | Hardy theorem | Gamma asymptotic used in approximate functional equation setup |
| `HardyTheorem.lean` | `HardyTheorem.Details.theta_asymptotic_target` | Hardy theorem | Riemann–Siegel theta asymptotic setup |
| `HardyTheorem.lean` | `HardyTheorem.Details.approximate_functional_equation_target` | Hardy theorem | Residual error form of the AFE used by Hardy integrals |
| `RiemannExplorer.lean` | `KnownResults.conrey_40_percent_zeros_on_critical_line_target` | Hardy theorem | Proportionality target for zero density on the critical line |

## Verified Starting Points

The following proved declarations are the main entry points for future work:

- `ZeroFreeRegion.log_deriv_zeta_re_series`
- `ZeroFreeRegion.log_deriv_zeta_nonneg_combination`
- `ZeroFreeRegion.norm_logDeriv_riemannZeta_le_real_neg_deriv_div`
- `ZeroFreeRegion.exists_norm_logDeriv_riemannZeta_le_log_abs_im_add_three_of_one_add_le_re`
- `ZeroFreeRegion.exists_re_neg_deriv_div_riemannZeta_sigma_it_le_log_abs_add_three_of_one_add_le`
- `ZeroFreeRegion.exists_re_neg_deriv_div_riemannZeta_sigma_two_it_le_log_abs_add_three_of_one_add_le`
- `ZeroFreeRegion.exists_re_neg_deriv_div_riemannZeta_fixed_margin_three_four_one_bounds`
- `ZeroFreeRegion.exists_three_four_one_combination_le_log_abs_add_three_of_one_add_le`
- `ZeroFreeRegion.exists_sigmaOf_log_two_t_norm_bound_const_mul_log_div`
- `ZeroFreeRegion.exists_sigmaOf_log_two_t_bound_const_mul_log_div`
- `ZeroFreeRegion.sigmaOf_log_weak_two_t_margin_impossible`
- `ZeroFreeRegion.no_sigmaOf_log_margin_constants_with_weak_two_t`
- `ZeroFreeRegion.exists_sigmaOf_log_margin_constants_for_shift_bounds`
- `ZeroFreeRegion.exists_sigmaOf_log_margin_constants_same_const`
- `ZeroFreeRegion.classical_zero_free_region_of_sigma_log_shift_estimates_nonneg_constants`
- `ZeroFreeRegion.classical_zero_free_region_of_exists_sigma_log_shift_estimates_nonneg_constants`
- `ZeroFreeRegion.classical_zero_free_region_of_sigma_log_shift_estimates_five_fourths_nonneg_constants`
- `ZeroFreeRegion.classical_zero_free_region_of_exists_sigma_log_shift_estimates_five_fourths_nonneg_constants`
- `ZeroFreeRegion.classical_zero_free_region_of_exists_sigma_log_shift_estimates_same_const_high_height`
- `ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_affine_bounds_high_height`
- `ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_one_add_log_bounds_high_height`
- `ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_one_add_log_bounds_high_height`
- `ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_log_abs_add_three_bounds_high_height`
- `ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_log_abs_add_three_bound_high_height`
- `ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_log_abs_add_three_bounds_high_height`
- `ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height`
- `ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height`
- `ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height`
- `ZeroFreeRegion.classical_zero_free_region_of_exists_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height`
- `ZeroFreeRegion.classical_zero_free_region_of_exists_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height`
- `ZeroFreeRegion.classical_zero_free_region_of_exists_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height`
- `ZeroFreeRegion.classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height`
- `ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height`
- `ZeroFreeRegion.classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height`
- `ZeroFreeRegion.classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height`
- `ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_affine_re_le_half_radius`
- `ZeroFreeRegion.borelCaratheodory_sub_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_affine_re_le_half_radius`
- `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_affine_re_le_half_radius`
- `ZeroFreeRegion.borelCaratheodory_sub_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_affine_re_le_half_radius`
- `ZeroFreeRegion.meromorphicOn_neg_logDeriv_riemannZeta_verticalRegion`
- `ZeroFreeRegion.log_norm_neg_logDeriv_riemannZeta_eq`
- `ZeroFreeRegion.circleAverage_log_norm_neg_logDeriv_riemannZeta_eq`
- `ZeroFreeRegion.divisor_neg_logDeriv_riemannZeta_eq_divisor_logDeriv_closedBall`
- `ZeroFreeRegion.divisor_neg_logDeriv_riemannZeta_eq_divisor_logDeriv_verticalRegion`
- `ZeroFreeRegion.log_norm_meromorphicTrailingCoeffAt_neg_logDeriv_riemannZeta_eq`
- `ZeroFreeRegion.jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_verticalRegion`
- `ZeroFreeRegion.jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_closedBall_unsigned_terms`
- `ZeroFreeRegion.jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_verticalRegion_unsigned_terms`
- `ZeroFreeRegion.jensen_circleAverage_log_norm_riemannZeta_sigma_it`
- `ZeroFreeRegion.jensen_circleAverage_log_norm_logDeriv_riemannZeta_sigma_it`
- `ZeroFreeRegion.jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_sigma_it`
- `ZeroFreeRegion.jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_sigma_it_unsigned_terms`
- `ZeroFreeRegion.valueDistribution_logCounting_translate_eq_circleAverage_sub_const`
- `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_circleAverage_sub_const`
- `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_eq_circleAverage_sub_const`
- `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_circleAverage`
- `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_circleAverage_sub_const`
- `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_circleAverage`
- `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_localDivisor`
- `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_localDivisor`
- `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_localDivisor`
- `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_localDivisor`
- `ZeroFreeRegion.meromorphicTrailingCoeffAt_comp_add_const_zero`
- `ZeroFreeRegion.norm_meromorphicTrailingCoeffAt_comp_add_const_zero`
- `ZeroFreeRegion.log_norm_meromorphicTrailingCoeffAt_comp_add_const_zero`
- `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_localDivisor_pure`
- `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_localDivisor_pure`
- `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_localDivisor_pure`
- `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_localDivisor_pure`
- `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_zero_of_divisor_eq_zero`
- `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_eq_zero_of_divisor_eq_zero`
- `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_zero_of_divisor_eq_zero`
- `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_eq_zero_of_divisor_eq_zero`
- `ZeroFreeRegion.divisor_logDeriv_riemannZeta_closedBall_eq_zero_of_order_eq_zero`
- `ZeroFreeRegion.divisor_logDeriv_riemannZeta_closedBall_eq_zero_of_analyticAt_ne_zero`
- `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_zero_of_order_eq_zero`
- `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_eq_zero_of_order_eq_zero`
- `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_zero_of_order_eq_zero`
- `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_eq_zero_of_order_eq_zero`
- `ZeroFreeRegion.analyticAt_logDeriv_of_analyticAt_ne_zero`
- `ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_of_analyticAt_ne_zero`
- `ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_of_ne_one_of_ne_zero`
- `ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_of_one_le_re_of_ne_one`
- `ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_closedBall_of_ne_one_of_ne_zero`
- `ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_closedBall_of_one_le_re_of_ne_one`
- `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_zero_of_analyticAt_ne_zero`
- `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_eq_zero_of_analyticAt_ne_zero`
- `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_zero_of_analyticAt_ne_zero`
- `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_eq_zero_of_analyticAt_ne_zero`
- `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_zero_of_one_le_re_of_ne_one_of_logDeriv_ne_zero`
- `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_eq_zero_of_one_le_re_of_ne_one_of_logDeriv_ne_zero`
- `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_zero_of_one_le_re_of_ne_one_of_logDeriv_ne_zero`
- `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_eq_zero_of_one_le_re_of_ne_one_of_logDeriv_ne_zero`
- `ZeroFreeRegion.closedBall_sigma_it_one_le_re_of_add_le`
- `ZeroFreeRegion.closedBall_sigma_it_ne_one_of_height_add_le`
- `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_zero_of_disk_right_half_of_logDeriv_ne_zero`
- `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_eq_zero_of_disk_right_half_of_logDeriv_ne_zero`
- `ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_closedBall_sigma_it_of_disk_right_half`
- `ZeroFreeRegion.logDeriv_riemannZeta_ne_zero_of_neg_logDeriv_ne_zero`
- `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_eq_zero_of_disk_right_half_of_neg_logDeriv_ne_zero`
- `ZeroFreeRegion.differentiableOn_logDeriv_riemannZeta_closedBall_sigma_it_of_disk_right_half`
- `ZeroFreeRegion.differentiableOn_logDeriv_riemannZeta_comp_add_sigma_it_ball_of_disk_right_half`
- `ZeroFreeRegion.differentiableOn_neg_logDeriv_riemannZeta_comp_add_sigma_it_ball_of_disk_right_half`
- `ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le`
- `ZeroFreeRegion.borelCaratheodory_sub_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le`
- `ZeroFreeRegion.differentiableOn_neg_logDeriv_riemannZeta_closedBall_sigma_it_of_disk_right_half`
- `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le`
- `ZeroFreeRegion.borelCaratheodory_sub_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le`
- `ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le_half_radius`
- `ZeroFreeRegion.borelCaratheodory_sub_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le_half_radius`
- `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le_half_radius`
- `ZeroFreeRegion.borelCaratheodory_sub_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le_half_radius`
- `ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_affine_re_le_half_radius`
- `ZeroFreeRegion.borelCaratheodory_sub_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_affine_re_le_half_radius`
- `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_affine_re_le_half_radius`
- `ZeroFreeRegion.borelCaratheodory_sub_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_affine_re_le_half_radius`
- `ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_sigma_it_right_shift_of_affine_re_le_half_radius`
- `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_right_shift_of_affine_re_le_half_radius`
- `ZeroFreeRegion.log_norm_sigma_add_I_mul_add_three_le_two_log_abs_of_re_le_three`
- `ZeroFreeRegion.log_abs_le_log_norm_sigma_add_I_mul_add_three`
- `ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius`
- `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius`
- `ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_sigma_it_right_shift_le_log_norm_of_affine_re_le_half_radius`
- `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_right_shift_le_log_norm_of_affine_re_le_half_radius`
- `ZeroFreeRegion.re_neg_deriv_div_riemannZeta_sigma_it_right_shift_le_log_abs_of_affine_logDeriv_re_le_half_radius`
- `ZeroFreeRegion.re_neg_deriv_div_riemannZeta_sigma_it_right_shift_le_log_abs_of_affine_neg_logDeriv_re_le_half_radius`
- `ZeroFreeRegion.re_neg_deriv_div_riemannZeta_sigma_it_right_shift_le_log_norm_of_affine_logDeriv_re_le_half_radius`
- `ZeroFreeRegion.re_neg_deriv_div_riemannZeta_sigma_it_right_shift_le_log_norm_of_affine_neg_logDeriv_re_le_half_radius`
- `ZeroFreeRegion.re_neg_deriv_div_riemannZeta_sigma_two_it_right_shift_le_log_abs_of_affine_logDeriv_re_le_half_radius`
- `ZeroFreeRegion.re_neg_deriv_div_riemannZeta_sigma_two_it_right_shift_le_log_abs_of_affine_neg_logDeriv_re_le_half_radius`
- `ZeroFreeRegion.re_neg_deriv_div_riemannZeta_sigma_two_it_right_shift_le_log_norm_of_affine_logDeriv_re_le_half_radius`
- `ZeroFreeRegion.re_neg_deriv_div_riemannZeta_sigma_two_it_right_shift_le_log_norm_of_affine_neg_logDeriv_re_le_half_radius`
- `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_regularPart_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius`
- `ZeroFreeRegion.re_neg_logDeriv_riemannZeta_sigma_it_add_inv_right_shift_le_log_abs_of_affine_regularPart_re_le_half_radius`
- `ZeroFreeRegion.exists_re_neg_logDeriv_riemannZeta_sigma_it_add_inv_right_shift_le_log_norm_of_affine_regularPart_re_le_half_radius_fixed_margin_center`
- `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius`
- `ZeroFreeRegion.re_neg_logDeriv_riemannZeta_sigma_it_add_multiplicity_inv_right_shift_le_log_abs_of_affine_regularPart_re_le_half_radius`
- `ZeroFreeRegion.exists_re_neg_logDeriv_riemannZeta_sigma_it_add_multiplicity_inv_right_shift_le_log_norm_of_affine_regularPart_re_le_half_radius_fixed_margin_center`
- `ZeroFreeRegion.borelCaratheodory_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius`
- `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_norm_of_affine_re_le_half_radius`
- `ZeroFreeRegion.borelCaratheodory_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_norm_of_affine_re_le_half_radius`
- `ZeroFreeRegion.exists_borelCaratheodory_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_norm_of_affine_re_le_half_radius_fixed_margin_center`
- `ZeroFreeRegion.exists_borelCaratheodory_neg_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_norm_of_affine_re_le_half_radius_fixed_margin_center`
- `ZeroFreeRegion.re_neg_logDeriv_riemannZeta_sigma_it_add_multiplicity_inv_right_shift_le_log_norm_of_affine_regularPart_re_le_half_radius`
- `ZeroFreeRegion.residue_bounds`
- `ZeroFreeRegion.classical_zero_free_region_compact`
- `ZeroFreeRegion.compact_patch_classical_zero_free_region_at_three`
- `ZeroFreeRegion.classical_zero_free_region_high_height`
- `ZeroFreeRegion.classical_zero_free_region_iff_high_height`
- `ZeroFreeRegion.classical_zero_free_region_iff_high_height_at_three`
- `ZeroFreeRegion.vinogradov_korobov_high_height_classical_zero_free_region`
- `ZeroFreeRegion.classical_zero_free_region_of_vinogradov_korobov`
- `PrimeNumberTheorem.finite_nontrivial_zeros_bounded_height`
- `PrimeNumberTheorem.pnt_forms_equivalent`
- `PrimeNumberTheorem.PNTForm1_iff_PNTForm2`
- `PrimeNumberTheorem.PNTForm2_iff_PNTForm1`
- `PrimeNumberTheorem.PNTForm2_iff_PNTForm3`
- `PrimeNumberTheorem.PNTForm3_iff_PNTForm2`
- `PrimeNumberTheorem.PNTForm3_iff_PNTForm1`
- `PrimeNumberTheorem.PNTForm3_proved`
- `PrimeNumberTheorem.PNTForm2_proved`
- `PrimeNumberTheorem.PNTForm1_proved`
- `PrimeNumberTheorem.pnt_forms_proved`
- `PrimeNumberTheorem.RH_PsiErrorBound_iff_RH_ThetaErrorBound`
- `PrimeNumberTheorem.theta_error_div_log_isBigO_sqrt_mul_log`
- `PrimeNumberTheorem.theta_error_integral_isBigO_sqrt_mul_log`
- `PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_of_RH_ThetaErrorBound`
- `PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_of_RH_PsiErrorBound`
- `PrimeNumberTheorem.RH_ErrorBound_of_RH_ThetaErrorBound`
- `PrimeNumberTheorem.RH_ErrorBound_of_RH_PsiErrorBound`
- `PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_of_RH_ErrorBound`
- `PrimeNumberTheorem.RH_ErrorBound_of_RH_PrimeCountingLiErrorBound_of_finite_intervals`
- `PrimeNumberTheorem.RH_ErrorBound_of_RH_PrimeCountingLiErrorBound`
- `PrimeNumberTheorem.RH_ErrorBound_iff_RH_PrimeCountingLiErrorBound`
- `PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_iff_RH_ErrorBound`
- `PrimeNumberTheorem.rh_iff_pointwise_error_iff`
- `PrimeNumberTheorem.rh_iff_optimal_error_of_pointwise_implications`
- `PrimeNumberTheorem.RH_ErrorBound_of_rh_iff_optimal_error`
- `PrimeNumberTheorem.RiemannHypothesis_of_rh_iff_pointwise_error`
- `PrimeNumberTheorem.psiPowerErrorBound_of_RH_PsiErrorBound_of_half_lt`
- `ZeroFreeRegion.nontrivial_zero_re_le_half_of_RH_PsiErrorBound`
- `ZeroFreeRegion.half_le_nontrivial_zero_re_of_RH_PsiErrorBound`
- `ZeroFreeRegion.riemannHypothesis_of_RH_PsiErrorBound`
- `PrimeNumberTheorem.ExplicitFormulaResidues.RH_PsiErrorBound_of_RiemannHypothesis`
- `PrimeNumberTheorem.ExplicitFormulaResidues.RH_ThetaErrorBound_of_RiemannHypothesis`
- `PrimeNumberTheorem.ExplicitFormulaResidues.RH_PrimeCountingLiErrorBound_of_RiemannHypothesis`
- `PrimeNumberTheorem.ExplicitFormulaResidues.RH_ErrorBound_of_RiemannHypothesis`
- `PrimeNumberTheorem.ExplicitFormulaResidues.riemannHypothesis_iff_RH_PsiErrorBound`
- `PrimeNumberTheorem.chebyshevTheta_sub_id_eq_primeCountingLi_error`
- `PrimeNumberTheorem.RH_ThetaErrorBound_of_RH_PrimeCountingLiErrorBound`
- `PrimeNumberTheorem.RH_PsiErrorBound_of_RH_PrimeCountingLiErrorBound`
- `PrimeNumberTheorem.riemannHypothesis_of_RH_PrimeCountingLiErrorBound`
- `PrimeNumberTheorem.rh_iff_optimal_error_proved`
- `PrimeNumberTheorem.primeCounting_logIntegral_finite_interval_bound`
- `PrimeNumberTheorem.explicit_formula_von_mangoldt_unweighted_iff_error_tendsto_zero`
- `PrimeNumberTheorem.explicit_formula_von_mangoldt_unweighted_iff_error_isLittleO_one`
- `PrimeNumberTheorem.explicit_formula_von_mangoldt_unweighted_iff_re_im_tendsto`
- `PrimeNumberTheorem.explicit_formula_von_mangoldt_unweighted_iff_re_im_error_tendsto_zero`
- `PrimeNumberTheorem.explicit_formula_von_mangoldt_unweighted_iff_re_im_error_isLittleO_one`
- `HardyTheorem.hardyZ_zero_iff_zeta_zero`
- `HardyTheorem.hardyZ_continuous`
- `HardyTheorem.critical_line_zeta_zero_neg_height`
- `HardyTheorem.hardy_two_signed_moments_target_iff_integral_asymptotic_one_two`
- `HardyTheorem.hardy_theorem_target_of_two_signed_moments`
- `HardyTheorem.hardy_theorem_target_of_integral_asymptotic_one_two`
- `HardyTheorem.exists_zero_on_critical_line_of_hardy_theorem_target`
- `HardyTheorem.exists_zero_on_critical_line_of_two_signed_moments`
- `HardyTheorem.exists_zero_on_critical_line_of_integral_asymptotic_one_two`
- `HardyTheorem.hardy_theorem_target_iff_abs_unbounded_of_bounded_strips`
- `HardyTheorem.hardy_zeros_unbounded_iff_abs_unbounded_of_neg_symm`
- `HardyTheorem.hardy_zeros_unbounded_iff_abs_unbounded`
- `HardyTheorem.hardy_theorem_target_iff_unbounded_of_bounded_strips`
- `HardyTheorem.exists_zero_on_critical_line_of_unbounded`
- `HardyTheorem.exists_zero_on_critical_line_of_abs_unbounded`
- `HardyTheorem.hardy_zeros_abs_unbounded_of_two_signed_moments_of_bounded_strips`
- `HardyTheorem.hardy_zeros_unbounded_of_two_signed_moments_of_bounded_strips`
- `HardyTheorem.hardy_zeros_abs_unbounded_of_integral_asymptotic_one_two_of_bounded_strips`
- `HardyTheorem.hardy_zeros_unbounded_of_integral_asymptotic_one_two_of_bounded_strips`
- `PrimeNumberTheorem.hardy_theorem_target_iff_unbounded`
- `PrimeNumberTheorem.hardy_zeros_abs_unbounded_of_two_signed_moments`
- `PrimeNumberTheorem.hardy_zeros_unbounded_of_two_signed_moments`
- `PrimeNumberTheorem.hardy_zeros_abs_unbounded_of_integral_asymptotic_one_two`
- `PrimeNumberTheorem.hardy_zeros_unbounded_of_integral_asymptotic_one_two`
- `PrimeNumberTheorem.hardy_theorem_target_of_two_signed_moments`
- `PrimeNumberTheorem.hardy_theorem_target_of_integral_asymptotic_one_two`
- `HardyTheorem.hardy_theorem_target_of_hardy_littlewood_lower_bound`
- `HardyTheorem.hardy_theorem_target_of_selberg_zero_proportion`
- `PrimeNumberTheorem.hardy_zeros_unbounded_of_hardy_littlewood_lower_bound`
- `PrimeNumberTheorem.hardy_zeros_unbounded_of_selberg_zero_proportion`
- `PrimeNumberTheorem.hardy_zeros_unbounded_of_conrey_40_percent_target`
- `PrimeNumberTheorem.infinitely_many_zeros_on_critical_line_of_two_signed_moments`
- `PrimeNumberTheorem.infinitely_many_zeros_on_critical_line_of_integral_asymptotic_one_two`
- `PrimeNumberTheorem.infinitely_many_zeros_on_critical_line_of_hardy_littlewood_lower_bound`
- `PrimeNumberTheorem.exists_zero_on_critical_line_of_two_signed_moments`
- `PrimeNumberTheorem.exists_zero_on_critical_line_of_integral_asymptotic_one_two`
- `PrimeNumberTheorem.exists_zero_on_critical_line_of_hardy_littlewood_lower_bound`
- `PrimeNumberTheorem.exists_zero_on_critical_line_of_selberg_zero_proportion`
- `PrimeNumberTheorem.exists_zero_on_critical_line_of_conrey_40_percent_target`
- `HardyTheorem.hardy_zeros_abs_unbounded_of_hardy_littlewood_lower_bound_of_bounded_strips`
- `HardyTheorem.hardy_zeros_unbounded_of_hardy_littlewood_lower_bound_of_bounded_strips`
- `HardyTheorem.hardy_zeros_abs_unbounded_of_selberg_zero_proportion_of_bounded_strips`
- `HardyTheorem.hardy_zeros_unbounded_of_selberg_zero_proportion_of_bounded_strips`
- `RiemannExplorer.hardy_theorem_target_of_conrey_target`
- `RiemannExplorer.hardy_theorem_target_of_two_signed_moments`
- `RiemannExplorer.hardy_theorem_target_of_integral_asymptotic_one_two`
- `RiemannExplorer.infinitely_many_zeros_on_critical_line_of_integral_asymptotic_one_two`
- `RiemannExplorer.infinitely_many_zeros_on_critical_line_of_hardy_littlewood_lower_bound`
- `RiemannExplorer.infinitely_many_zeros_on_critical_line_of_selberg_zero_proportion`
- `RiemannExplorer.infinitely_many_zeros_on_critical_line_of_conrey_target`
- `RiemannExplorer.exists_zero_on_critical_line_of_hardy_littlewood_lower_bound`
- `RiemannExplorer.exists_zero_on_critical_line_of_selberg_zero_proportion`

## Non-Goals

Do not convert target statements into theorem declarations unless the proof is
actually supplied and checked by Lean.  In particular:

- do not reintroduce `sorry`, `admit`, or `axiom`;
- do not use a theorem statement for a mathematically false intermediate
  statement;
- do not cite `def ... : Prop` targets as completed formal results.
- do not cite local target-count reduction by itself as evidence for any
  theorem; cite `PNTForm1_proved`, `PNTForm2_proved`, and `PNTForm3_proved` for
  ordinary PNT, and keep RH explicitly open.
- do not advertise this repository as the first PNT formalization or as an
  effective-error PNT or RH proof.

`HardyTheorem.weightedIntegralOf_tail_dominates` remains a `Prop`-valued
predicate in Lean, but it is a reusable hypothesis form rather than an
unresolved target statement.

Additional non-target Prop declarations:

- `PrimeNumberTheorem.ExplicitFormulaAux.goodHeight` is a reusable contour
  height predicate.
- `HardyTheorem.AFE.zeta_critical_afe_target`,
  `PrimeNumberTheorem.ExplicitFormulaTruncated.ExplicitFormulaTruncatedTarget`
  (proved by `explicitFormulaTruncatedTarget_proved`),
  `MathlibAux.rectangleIntegral_meromorphic_eq_residue_sum`, and
  `RiemannExplorer.Conrey40.conrey_40_percent_zeros_on_critical_line_target`
  are route interfaces with real statement bodies or aliases.

## Verification Commands

```bash
lake build
rg -n "sorry|admit|axiom" *.lean
```

Both commands should pass before any claim that the repository is in a clean
baseline state.
