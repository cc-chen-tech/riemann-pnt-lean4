# Missing Chains Index

This page tracks the remaining mathematical chains that are not proved in the
current Lean checkout.  The project currently builds and contains no
`sorry`/`admit`/`axiom` placeholders in Lean source, but several deep goals are
intentionally recorded as `def ... : Prop` target statements.

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

| Chain | Current Lean target status | Main correction before proof work | Smallest useful next step |
| --- | --- | --- | --- |
| Quantitative zero-free region | `classical_zero_free_region` and `vinogradov_korobov_zero_free_region` are `def ... : Prop` targets | Add zeta-specific meromorphic/growth/log-derivative estimates; do not cite compact zero-free region as the classical `c / log |t|` result | Prove conditional 3-4-1 algebra and compact-to-high-height patching lemmas |
| Explicit formula | `explicit_formula_von_mangoldt` is a `def ... : Prop` target | Replace the unconditional infinite `tsum` target with a truncated Perron/residue formula for `psi0`, then a principal-value limit | Define `psi0`, finite zero sums with multiplicity, good heights, and contour-error terms |
| RH error equivalence | `rh_iff_optimal_error` is a `def ... : Prop` target | Stage the result through `=O[atTop]` predicates for `psi`, `theta`, and `primeCounting - logIntegral` | Add explicit `IsBigO` target predicates and quantitative partial-summation milestones |
| Hardy theorem | `hardy_theorem_target` and related moment/asymptotic targets are `def ... : Prop` targets | Use an unbounded-height zero target as the main theorem; use signed moment targets, not merely nonzero constants | Prove bounded-zero eventual-sign control and generic asymptotic sign lemmas |

## Verified Starting Points

The following proved declarations are the main entry points for future work:

- `ZeroFreeRegion.log_deriv_zeta_re_series`
- `ZeroFreeRegion.log_deriv_zeta_nonneg_combination`
- `ZeroFreeRegion.residue_bounds`
- `ZeroFreeRegion.classical_zero_free_region_compact`
- `PrimeNumberTheorem.finite_nontrivial_zeros_bounded_height`
- `PrimeNumberTheorem.pnt_forms_equivalent`
- `HardyTheorem.hardyZ_zero_iff_zeta_zero`
- `HardyTheorem.hardyZ_continuous`

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
