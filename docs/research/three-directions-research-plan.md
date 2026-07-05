# Three Directions Research Worktree

This worktree tracks concrete Lean progress along three zero-free/PNT/RH-adjacent
routes.  The branch is based on current `main`; the goal is to add verified
interfaces and small lemmas without overstating any unresolved analytic theorem.

## Baseline

- Worktree: `/Users/luicy/AI/Riemann/.worktrees/riemann-three-directions-research`
- Branch: `research/three-directions`
- Current base: `9266d36 feat(pnt): add simplified BTY Borel facade`
- Rule: do not present route interfaces or `def ... : Prop` targets as proved
  mathematics.

## Direction 1: BTY detector and Borel bounds

Verified assets now include:

- the BTY degree-16 trigonometric detector;
- the simplified uniform BTY penalty
  `log_deriv_zeta_bty_detector_one_lower_bound_of_uniform_shift_upper_bound_simplified`;
- the unsigned simplified Borel facade
  `log_deriv_zeta_bty_detector_one_lower_bound_of_uniform_right_shift_borel_family_simplified`;
- the signed simplified Borel facade added on this branch:
  `log_deriv_zeta_bty_detector_one_lower_bound_of_uniform_signed_right_shift_borel_family_simplified`.

Next useful step:

```lean
log_deriv_zeta_bty_detector_one_lower_bound_of_uniform_vertical_pair_bound
```

This would combine the signed/unsigned vertical-pair log bounds with the BTY
detector facade.

## Direction 2: Stechkin/Heath-Brown pair positivity

Verified assets now include:

- center-one zero-pair bridges over `nontrivialZerosFinset`;
- a general-center finite paired-sum bridge over full and new-zero finsets;
- paired-average bridges over full and new-zero finsets:
  `nontrivialZerosFinset_pair_average_nonnegative_of_laplace_pair_positive`;
  `nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_laplace_pair_positive`.

Important boundary:

The general-center paired average is not an unpaired real-part average.  Turning
it into an unpaired sum needs a proof that the chosen center-pair map preserves
the relevant zero set.  For zeta this is available at center `1`, via
`rho -> 1 - rho`, not for an arbitrary center.

Next useful step:

```lean
nontrivialZerosFinset_pair_average_nonnegative_of_center_one_laplace_pair_positive
```

as a convenience wrapper, then specialize it to concrete Stechkin kernels once
their positivity theorem is available.

## Direction 3: explicit formula / PNT error bridge

Verified assets now include:

- finite explicit-formula truncation increment identities;
- new-zero norm/count tail bounds under RH;
- eventual-no-new-zero tail convergence;
- composed bridges:
  `explicit_formula_von_mangoldt_of_RH_base_and_eventually_no_new_zeros_via_sum_tail`;
  `explicit_formula_von_mangoldt_of_RH_base_and_eventually_no_new_zeros_via_card_tail`.

Important boundary:

These theorems still assume the base explicit-formula identity.  They do not
prove Perron's formula, contour shifting, or the converse theorem turning
`psi(x) - x = O(x^(beta - delta))` into zero exclusion.

## Hard Gaps

- No classical zero-free region `Re(s) >= 1 - c / log |t|` is proved here.
- No Perron formula or contour-shift explicit formula is proved here.
- No explicit-formula converse / oscillation theorem is proved here.
- No result here proves RH or an unconditional zero-free vertical line.
