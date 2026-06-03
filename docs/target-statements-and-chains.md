# Unproved Target Statements and Missing Chains

This file is the authoritative checklist of the remaining `def ... : Prop`
statements (as of `2026-06-03`) in this Lean checkout.

All entries are intentionally **not** exported as theorems.  They are explicit
`Prop` targets used as roadmap checkpoints.

## Target count

- `HardyTheorem` namespace: 11
- `PrimeNumberTheorem` namespace: 9
- `ZeroFreeRegion` namespace: 2
- `RiemannExplorer` namespace: 1

Total: **23**.

## Chain 1: Quantitative zero-free region

### Target declarations

- `ZeroFreeRegion.classical_zero_free_region`
- `ZeroFreeRegion.vinogradov_korobov_zero_free_region`

### Current verified anchor theorems

- `ZeroFreeRegion.log_deriv_zeta_re_series`
- `ZeroFreeRegion.log_deriv_zeta_nonneg_combination`
- `ZeroFreeRegion.residue_bounds`
- `ZeroFreeRegion.classical_zero_free_region_compact`
- `ZeroFreeRegion.log_deriv_zeta_pos_real`
- `ZeroFreeRegion.log_deriv_zeta_antitone`

### Missing mathlib/analytic infrastructure

1. zeta-specific log-derivative growth bound near `Re(s)=1` for bounded-height
   high strips;
2. Borel–Carathéodory or equivalent zero-repulsion machinery;
3. explicit control of the pole-side term (`-zeta'/zeta` near `1`) and
   the `σ+2it` regular part;
4. real-variable bridge from a quantitative strip at large height to the bounded-
   height compact strip.

---

## Chain 2: Explicit formula

### Target declarations

- `PrimeNumberTheorem.explicit_formula_von_mangoldt`

### Current verified anchor theorems

- `PrimeNumberTheorem.finite_nontrivial_zeros_bounded_height`
- `PrimeNumberTheorem.zero_contribution`
- `PrimeNumberTheorem.chebyshevPsi_eq_mathlib`
- `PrimeNumberTheorem.vonMangoldt_eq_mathlib`

### Missing mathlib/analytic infrastructure

1. Perron's formula / contour-integral identity in a form usable for
   von Mangoldt sums;
2. residue-theorem-level contour argument for:
   - pole at `s=1`,
   - pole at `s=0`,
   - nontrivial zeros with multiplicity,
   - trivial-zero contribution;
3. corrected summation convention (truncated/symmetric principal value / midpoint
   `psi0`) and explicit edge-error estimates.

---

## Chain 3: RH ⇔ prime-counting error

### Target declarations

- `PrimeNumberTheorem.PNTForm1`
- `PrimeNumberTheorem.PNTForm2`
- `PrimeNumberTheorem.PNTForm3`
- `PrimeNumberTheorem.RH_PsiErrorBound`
- `PrimeNumberTheorem.RH_ThetaErrorBound`
- `PrimeNumberTheorem.RH_PrimeCountingLiErrorBound`
- `PrimeNumberTheorem.RH_ErrorBound`
- `PrimeNumberTheorem.rh_iff_optimal_error`

### Current verified anchor theorems

- `PrimeNumberTheorem.pnt_forms_equivalent`
- `PrimeNumberTheorem.chebyshevPsi_eq_mathlib`
- `PrimeNumberTheorem.primeCounting_eq_mathlib`
- `PrimeNumberTheorem.chebyshevPsi_eq_mathlib`

### Missing mathlib/analytic infrastructure

1. a usable explicit-formula endpoint from Chain 2 with quantified error terms,
   including truncation parameter handling;
2. zero-counting and reciprocal-zero sum control (e.g. `N(T)` and `sum 1/|rho|`)
   for converting explicit-formula sums to `sqrt(x) log^2 x`-type bounds;
3. precise `Chebyshev` ⇄ `primeCounting` bridge under RH-quality errors;
4. reverse implication machinery (error bounds on `pi`/`Li` imply RH in
   the required direction).

---

## Chain 4: Hardy theorem

### Target declarations

- `HardyTheorem.integral_asymptotic_target`
- `HardyTheorem.hardy_two_signed_moments_target`
- `HardyTheorem.weightedIntegralOf_tail_dominates`
- `HardyTheorem.hardy_theorem_target`
- `HardyTheorem.hardy_zeros_unbounded_target`
- `HardyTheorem.hardy_zeros_abs_unbounded_target`
- `HardyTheorem.hardy_littlewood_lower_bound_target`
- `HardyTheorem.selberg_zero_proportion_target`
- `HardyTheorem.gamma_asymptotic_half_plus_it_target`
- `HardyTheorem.theta_asymptotic_target`
- `HardyTheorem.approximate_functional_equation_target`

### Current verified anchor theorems

- `HardyTheorem.hardyZ_zero_iff_zeta_zero`
- `HardyTheorem.hardyZ_eventually_const_sign_of_finite_zeros`
- `HardyTheorem.weightedIntegralOf_neg`
- `HardyTheorem.hardy_theorem_target_of_two_signed_moments_and_tail_dominance`
- `HardyTheorem.hardyZ_continuous`

### Missing mathlib/analytic infrastructure

1. corrected asymptotic signed moment formulas with sign-normalized leading terms;
2. rigorous tail-dominance lemmas for weighted integrals;
3. Riemann–Siegel/AFE and `Γ`-factor asymptotics consistent with the chosen phase;
4. unbounded-height conclusion extracted from sign oscillation argument (infinite set
   alone is not a mathematically sufficient final target).

---

## Non-target declarations to avoid confusion

- `RiemannExplorer.conrey_40_percent_zeros_on_critical_line_target`
  appears as a downstream target form and is kept intentionally in
  `RiemannExplorer`.

All of the above is meant to be consumed as a roadmap, not a claim of completion.
