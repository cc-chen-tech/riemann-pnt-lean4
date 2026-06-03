# Missing Chains Index

This page tracks the remaining mathematical chains that are not proved in the
current Lean checkout.  The project currently builds and contains no
`sorry`/`admit`/`axiom` placeholders in Lean source, but several deep goals are
intentionally recorded as `def ... : Prop` target statements.

At present there are **23** unresolved `def ... : Prop` targets, and they are
partitioned into exactly **4** analytic chains:

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
  Perron's formula, contour shifting, residues, and a corrected von Mangoldt
  explicit formula target;
- `docs/rh-error-equivalence-chain.md`
  equivalence between RH and prime-counting error terms;
- `docs/hardy-theorem-chain.md`
  Hardy Z-function moment estimates and critical-line zeros.

## Chain Status Summary

| Chain | Current Lean target status | Main correction before proof work | Smallest useful next step | Open target count |
| --- | --- | --- | --- | --- |
| Quantitative zero-free region | `classical_zero_free_region` and `vinogradov_korobov_zero_free_region` are `def ... : Prop` targets | Add zeta-specific meromorphic/growth/log-derivative estimates; do not cite compact zero-free region as the classical `c / log |t|` result | Prove conditional 3-4-1 algebra and compact-to-high-height patching lemmas | 2 |
| Explicit formula | `explicit_formula_von_mangoldt` is a `def ... : Prop` target | Replace the unconditional infinite `tsum` target with a truncated Perron/residue formula for `psi0`, then a principal-value limit | Define `psi0`, finite zero sums with multiplicity, good heights, and contour-error terms | 1 |
| RH error equivalence | `rh_iff_optimal_error` is a `def ... : Prop` target | Stage the result through `=O[atTop]` predicates for `psi`, `theta`, and `primeCounting - logIntegral` | Add explicit `IsBigO` target predicates and quantitative partial-summation milestones | 8 |
| Hardy theorem | `hardy_theorem_target` and related moment/asymptotic targets are `def ... : Prop` targets | Use an unbounded-height zero target as the main theorem; use signed moment targets, not merely nonzero constants | Prove bounded-zero eventual-sign control and generic asymptotic sign lemmas | 12 (11 in `HardyTheorem`, 1 in `RiemannExplorer`) |

## Target-to-Chain Mapping

| File | Target | Chain | Why it is still open |
| --- | --- | --- | --- |
| `ZeroFreeRegion.lean` | `classical_zero_free_region` | Quantitative zero-free region | Requires analytic growth and derivative estimates beyond compactness |
| `ZeroFreeRegion.lean` | `vinogradov_korobov_zero_free_region` | Quantitative zero-free region | Requires Vinogradov–Korobov exponential-sum technology |
| `PrimeNumberTheorem.lean` | `PNTForm1` | RH error equivalence | Formal statement of one classical asymptotic shape, kept as an interface |
| `PrimeNumberTheorem.lean` | `PNTForm2` | RH error equivalence | Equivalent to `PNTForm1` once one form is proved; no additional chain input yet |
| `PrimeNumberTheorem.lean` | `PNTForm3` | RH error equivalence | Equivalent to `PNTForm1`/`PNTForm2`; included as a target interface |
| `PrimeNumberTheorem.lean` | `RH_PsiErrorBound` | RH error equivalence | Needs explicit-formula error control under RH |
| `PrimeNumberTheorem.lean` | `RH_ThetaErrorBound` | RH error equivalence | Needs the same Hardy–Littlewood style input as `RH_PsiErrorBound` |
| `PrimeNumberTheorem.lean` | `RH_PrimeCountingLiErrorBound` | RH error equivalence | Partial-summation bridge from Chebyshev bounds to prime counting |
| `PrimeNumberTheorem.lean` | `RH_ErrorBound` | RH error equivalence | Textbook pointwise reformulation of `RH_PrimeCountingLiErrorBound` |
| `PrimeNumberTheorem.lean` | `rh_iff_optimal_error` | RH error equivalence | Final RH ↔ prime-counting error equivalence statement |
| `PrimeNumberTheorem.lean` | `explicit_formula_von_mangoldt` | Explicit formula | Main missing explicit-formula pipeline target |
| `HardyTheorem.lean` | `integral_asymptotic_target` | Hardy theorem | Signed-moment asymptotic input |
| `HardyTheorem.lean` | `hardy_two_signed_moments_target` | Hardy theorem | Asymptotics for the first two weighted moments |
| `HardyTheorem.lean` | `weightedIntegralOf_tail_dominates` | Hardy theorem | Tail-dominance hypothesis for weighted integrals |
| `HardyTheorem.lean` | `hardy_theorem_target` | Hardy theorem | Combined target of Hardy theorem output |
| `HardyTheorem.lean` | `hardy_zeros_unbounded_target` | Hardy theorem | Harder zero distribution output in an unbounded-height form |
| `HardyTheorem.lean` | `hardy_zeros_abs_unbounded_target` | Hardy theorem | Equivalent form requiring symmetry/absolute-value zero extraction |
| `HardyTheorem.lean` | `hardy_littlewood_lower_bound_target` | Hardy theorem | Quantitative lower bound on critical-line zeros needed for positive density |
| `HardyTheorem.lean` | `selberg_zero_proportion_target` | Hardy theorem | Proportional form of Hardy-type lower bounds |
| `HardyTheorem.lean` | `gamma_asymptotic_half_plus_it_target` | Hardy theorem | Gamma asymptotic used in approximate functional equation setup |
| `HardyTheorem.lean` | `theta_asymptotic_target` | Hardy theorem | Riemann–Siegel theta asymptotic setup |
| `HardyTheorem.lean` | `approximate_functional_equation_target` | Hardy theorem | Residual error form of the AFE used by Hardy integrals |
| `RiemannExplorer.lean` | `conrey_40_percent_zeros_on_critical_line_target` | Hardy theorem | Proportionality target for zero density on the critical line |

## Verified Starting Points

The following proved declarations are the main entry points for future work:

- `ZeroFreeRegion.log_deriv_zeta_re_series`
- `ZeroFreeRegion.log_deriv_zeta_nonneg_combination`
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
- `PrimeNumberTheorem.PNTForm2_iff_PNTForm3`
- `PrimeNumberTheorem.RH_PsiErrorBound_iff_RH_ThetaErrorBound`
- `PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_of_RH_ErrorBound`
- `PrimeNumberTheorem.RH_ErrorBound_of_RH_PrimeCountingLiErrorBound_of_finite_intervals`
- `PrimeNumberTheorem.RH_ErrorBound_of_RH_PrimeCountingLiErrorBound`
- `PrimeNumberTheorem.RH_ErrorBound_iff_RH_PrimeCountingLiErrorBound`
- `PrimeNumberTheorem.rh_iff_pointwise_error_iff`
- `PrimeNumberTheorem.primeCounting_logIntegral_finite_interval_bound`
- `PrimeNumberTheorem.explicit_formula_von_mangoldt_iff_error_tendsto_zero`
- `PrimeNumberTheorem.explicit_formula_von_mangoldt_iff_error_isLittleO_one`
- `PrimeNumberTheorem.explicit_formula_von_mangoldt_iff_re_im_tendsto`
- `HardyTheorem.hardyZ_zero_iff_zeta_zero`
- `HardyTheorem.hardyZ_continuous`
- `HardyTheorem.critical_line_zeta_zero_neg_height`
- `HardyTheorem.hardy_theorem_target_iff_abs_unbounded_of_bounded_strips`
- `HardyTheorem.hardy_zeros_unbounded_iff_abs_unbounded_of_neg_symm`
- `HardyTheorem.hardy_zeros_unbounded_iff_abs_unbounded`
- `PrimeNumberTheorem.hardy_theorem_target_iff_unbounded`
- `HardyTheorem.hardy_theorem_target_of_hardy_littlewood_lower_bound`
- `HardyTheorem.hardy_theorem_target_of_selberg_zero_proportion`
- `PrimeNumberTheorem.hardy_zeros_unbounded_of_hardy_littlewood_lower_bound`
- `PrimeNumberTheorem.hardy_zeros_unbounded_of_selberg_zero_proportion`
- `PrimeNumberTheorem.hardy_zeros_unbounded_of_conrey_40_percent_target`
- `HardyTheorem.hardy_zeros_abs_unbounded_of_hardy_littlewood_lower_bound_of_bounded_strips`
- `HardyTheorem.hardy_zeros_unbounded_of_hardy_littlewood_lower_bound_of_bounded_strips`
- `HardyTheorem.hardy_zeros_abs_unbounded_of_selberg_zero_proportion_of_bounded_strips`
- `HardyTheorem.hardy_zeros_unbounded_of_selberg_zero_proportion_of_bounded_strips`
- `RiemannExplorer.hardy_theorem_target_of_conrey_target`
- `RiemannExplorer.infinitely_many_zeros_on_critical_line_of_selberg_zero_proportion`
- `RiemannExplorer.infinitely_many_zeros_on_critical_line_of_conrey_target`

## Non-Goals

Do not convert target statements into theorem declarations unless the proof is
actually supplied and checked by Lean.  In particular:

- do not reintroduce `sorry`, `admit`, or `axiom`;
- do not use a theorem statement for a mathematically false intermediate
  statement;
- do not cite `def ... : Prop` targets as completed formal results.

## Verification Commands

```bash
lake build
rg -n "sorry|admit|axiom" *.lean
```

Both commands should pass before any claim that the repository is in a clean
baseline state.
