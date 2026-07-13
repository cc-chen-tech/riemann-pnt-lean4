# RH Error Equivalence Chain

This document scopes the formalization path around
`PrimeNumberTheorem.RH_ErrorBound` and
`PrimeNumberTheorem.rh_iff_optimal_error`.  It is a dependency map, not a claim
that the equivalence is already proved.

## Current Lean Anchors

The current project already provides these usable endpoints and support lemmas.

| Lean name | Current role in this chain |
| --- | --- |
| `RiemannHypothesis.IsNontrivialZero` | Local nontrivial-zero predicate: `zeta s = 0`, `0 < s.re`, `s.re < 1`. |
| `RiemannHypothesis.Statement` | Local RH statement: every local nontrivial zero has real part `1 / 2`. |
| `rh_iff_nontrivial_zeros_on_line` | Bridges Mathlib's root `RiemannHypothesis` to the all-nontrivial-zeros-on-line condition. |
| `rh_statement_iff_mathlib` | Bridges Mathlib's root `RiemannHypothesis` and `RiemannHypothesis.Statement`. |
| `finite_nontrivial_zeros_bounded_height` | Proves local finiteness of zeros with `|im| <= T`; useful for finite truncated zero sums, but not a zero-counting estimate. |
| `nontrivial_zero_symmetric` and `nontrivial_zero_symmetric'` | Prove zero symmetry under `rho -> 1 - rho`; useful in the reverse implication after excluding zeros with `re > 1 / 2`. |
| `primeCounting_eq_mathlib` | Connects project `primeCounting` to `Nat.primeCounting` for `x >= 0`. |
| `chebyshevPsi_eq_mathlib` | Connects project `chebyshevPsi` to Mathlib's `Chebyshev.psi`. |
| `pnt_forms_equivalent` | Proves asymptotic equivalence of `PNTForm1`, `PNTForm2`, and `PNTForm3`. |
| `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log` | Already used locally to show `psi(x) - theta(x) = o(x)`; can also absorb the `psi` to `theta` error under RH. |
| `Chebyshev.primeCounting_sub_theta_div_log_isBigO` | Current weak unconditional bridge for PNT equivalence; not strong enough for RH error terms. |
| `theta_error_integral_isBigO_sqrt_mul_log` | Bounds the Abel integral error from `RH_ThetaErrorBound`. |
| `RH_PrimeCountingLiErrorBound_of_RH_ThetaErrorBound` | Closed partial-summation bridge from RH-scale `theta` error to RH-scale `pi - Li` error. |
| `RH_PrimeCountingLiErrorBound_of_RH_PsiErrorBound` | Same bridge after the local `psi`/`theta` error equivalence. |
| `RH_ErrorBound_of_RH_ThetaErrorBound` | Converts the closed `theta` bridge to the pointwise textbook `RH_ErrorBound` target. |
| `RH_ErrorBound_of_RH_PsiErrorBound` | Same pointwise endpoint after the local `psi`/`theta` error equivalence. |
| `sqrt_mul_log_sq_isLittleO_rpow_of_half_lt` | Shows the RH-scale `sqrt x * log^2 x` model is smaller than every `x^theta` with `theta > 1/2`. |
| `psiPowerErrorBound_of_RH_PsiErrorBound_of_half_lt` | Converts `RH_PsiErrorBound` into every power-scale `PsiPowerErrorBound theta` with `theta > 1/2`. |
| `ZeroFreeRegion.riemannHypothesis_of_RH_PsiErrorBound` | Closes the reverse `RH_PsiErrorBound -> RiemannHypothesis` implication using the Mellin/Landau zero-exclusion bridge and zero symmetry. |
| `explicit_formula_von_mangoldt` | Present only as a target `Prop`; it uses a finite symmetric-height zero sum weighted by `analyticOrderNatAt`, followed by an `atTop` limit. |

## Current Target Assessment

The current definition is:

```lean
def RH_ErrorBound : Prop :=
  exists C > 0, forall x >= 2,
    |(primeCounting x : R) - logIntegral x| <= C * Real.sqrt x * Real.log x
```

As a mathematical endpoint for prime counting, the order

```text
pi(x) - Li(x) = O(sqrt x * log x)
```

is the standard von Koch RH equivalence.  The logarithm power is appropriate
for the `pi(x) - Li(x)` endpoint.  The common stronger-looking Chebyshev
endpoint has a different logarithm power:

```text
psi(x) - x = O(sqrt x * log^2 x)
theta(x) - x = O(sqrt x * log^2 x)
```

The main correction is therefore not the final `sqrt x * log x` order, but the
formal target shape and naming.  `RH_ErrorBound` is better treated as a
prime-counting/Li endpoint, not as the first theorem to prove from zeros.

Recommended staged targets:

```lean
def RH_PsiErrorBound : Prop :=
  (fun x : R => chebyshevPsi x - x)
    =O[atTop] (fun x : R => Real.sqrt x * (Real.log x)^2)

def RH_ThetaErrorBound : Prop :=
  (fun x : R => Chebyshev.theta x - x)
    =O[atTop] (fun x : R => Real.sqrt x * (Real.log x)^2)

def RH_PrimeCountingLiErrorBound : Prop :=
  (fun x : R => (primeCounting x : R) - logIntegral x)
    =O[atTop] (fun x : R => Real.sqrt x * Real.log x)

theorem rh_iff_primeCounting_li_error :
  RiemannHypothesis.Statement <-> RH_PrimeCountingLiErrorBound := ...
```

After that, prove a compatibility lemma from the asymptotic `IsBigO` statement
to the current `exists C, forall x >= 2, ...` shape if the all-`x >= 2`
form is still desired.  The `atTop` target is usually easier to compose with
explicit formula and partial summation estimates.

Also rename or document `rh_iff_optimal_error`: the bound is standard and sharp
as an RH-scale prime-counting target, but "optimal" is not the most precise
formal name unless a lower-bound or best-possible statement is also present.

## Forward Chain: RH to `primeCounting - Li`

Target:

```text
RiemannHypothesis.Statement
  -> pi(x) - Li(x) = O(sqrt x * log x)
```

### F1. RH to zeros on the critical line

Available now:

- `RiemannHypothesis.Statement` is already the local line condition.
- `rh_statement_iff_mathlib` and `rh_iff_nontrivial_zeros_on_line` bridge to
  Mathlib/root RH formulations when needed.

No new analytic input is needed for this step.

### F2. Bounded zero sums need zero counting

Needed:

```text
N(T) = #{rho : nontrivial zero | |im rho| <= T} = O(T log T)
sum_{|gamma| <= T} 1 / |rho| = O(log^2 T)
```

Current status:

- `finite_nontrivial_zeros_bounded_height T` gives finiteness in every bounded
  height box.
- It does not provide cardinal bounds, asymptotics for `N(T)`, or estimates for
  reciprocal zero sums.

Formalization dependencies:

- Argument principle or Jensen-style zero counting.
- Zeta growth bounds in vertical strips.
- Control near the pole at `1` and away from trivial zeros.
- A finite-set API converting bounded-height zeros into sums indexed by a
  finite set.

### F3. Replace the current explicit formula target

Needed theorem shape:

```text
psi0(x) = x - sum_{|gamma| <= T} x^rho / rho
          + O(x * log^2 x / T) + O(log x)
```

or a smoothed/test-function version strong enough to imply this estimate.  The
statement must specify:

- whether `psi`, `psi0`, or a smoothed Chebyshev function is used;
- jump conventions at prime powers;
- truncation by `|im rho| <= T`;
- the error term and its uniformity in `x` and `T`;
- exclusion or explicit accounting of the pole at `1`, trivial zeros, and
  `zeta'(0) / zeta(0)` constants.

Current status:

- `explicit_formula_von_mangoldt` is only a `Prop` target.
- Its finite symmetric-height truncations encode the principal-value convention
  and analytic multiplicities, but the all-height convergence proof is still
  missing; only a cofinal good-height convergence theorem is currently proved.

Formalization dependencies:

- Perron's formula or a smoothed Mellin inversion theorem.
- Contour shifting and residue calculus for `-zeta'/zeta`.
- A logarithmic derivative API for zeta, including the pole at `1`.
- Truncated-zero-sum estimates on contour edges.

### F4. Bound the explicit formula under RH

Under RH, each nontrivial zero has `rho.re = 1 / 2`, so

```text
|x^rho / rho| <= sqrt x / |rho|.
```

Using the zero-counting sum from F2:

```text
sum_{|gamma| <= T} |x^rho / rho| = O(sqrt x * log^2 T).
```

Choose a standard truncation, for example `T = x` or `T = x^2`, to obtain:

```text
psi(x) - x = O(sqrt x * log^2 x).
```

Current status:

- `zero_contribution` rewrites a single zero contribution into oscillatory
  form.  It is explanatory and may help local algebra, but it is not a
  zero-sum estimate.
- `finite_nontrivial_zeros_bounded_height` lets the truncated sum be finite.

### F5. Convert `psi` to `theta`

Needed:

```text
psi(x) - theta(x) = O(sqrt x * log x)
```

Current status:

- The project already uses Mathlib's
  `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log`.
- This is enough to pass from
  `psi(x) - x = O(sqrt x * log^2 x)` to
  `theta(x) - x = O(sqrt x * log^2 x)`.

This step is essentially connectable now once the `psi` RH error is available.

### F6. Convert `theta` to `pi - Li`

Needed partial summation theorem:

```text
pi(x) = theta(x) / log x
        + integral 2..x theta(t) / (t * log^2 t) dt
        + endpoint/normalization terms
```

Then write `theta(t) = t + E(t)` with
`E(t) = O(sqrt t * log^2 t)`.  The main term gives `Li(x)` up to the same
normalization used by `logIntegral`; the error contributes:

```text
E(x) / log x + integral_2^x E(t) / (t * log^2 t) dt
  = O(sqrt x * log x).
```

Current status:

- `pnt_forms_equivalent` proves asymptotic PNT equivalences.
- `Chebyshev.primeCounting_sub_theta_div_log_isBigO` gives a weaker
  unconditional `O(x / log^2 x)` bridge used for asymptotic equivalence.
- `primeCounting_sub_logIntegral_eq_theta_error_integral` supplies the exact
  Abel decomposition in the project's normalization.
- `theta_error_div_log_isBigO_sqrt_mul_log` bounds the endpoint term from
  `RH_ThetaErrorBound`.
- `theta_error_integral_isBigO_sqrt_mul_log` bounds the Abel integral error
  from `RH_ThetaErrorBound`.
- `RH_PrimeCountingLiErrorBound_of_RH_ThetaErrorBound` closes the forward
  quantitative partial-summation bridge.

Formalization dependencies:

- No remaining dependency for the forward
  `RH_ThetaErrorBound -> RH_PrimeCountingLiErrorBound` bridge.
- The open work is upstream: prove `RH_PsiErrorBound` / `RH_ThetaErrorBound`
  from an explicit formula under RH.

## Reverse Chain: `primeCounting - Li` to RH

Target:

```text
pi(x) - Li(x) = O(sqrt x * log x)
  -> RiemannHypothesis.Statement
```

### R1. Convert `pi - Li` error to Chebyshev errors

Needed:

```text
pi(x) - Li(x) = O(sqrt x * log x)
  -> theta(x) - x = O(sqrt x * log^2 x)
  -> psi(x) - x = O(sqrt x * log^2 x)
```

The first implication is another quantitative partial summation direction:

```text
theta(x) = pi(x) * log x - integral_2^x pi(t) / t dt
```

Substituting `pi(t) = Li(t) + E(t)` with
`E(t) = O(sqrt t * log t)` yields the `theta` error.  Then use
`psi - theta = O(sqrt x * log x)`.

Current status:

- The weak PNT-form equivalences do not provide this quantitative reverse
  estimate.
- The existing `psi - theta` Mathlib bound is enough for the final
  `theta -> psi` step.

### R2. Turn the `psi` error into analytic continuation of `-zeta'/zeta`

Needed theorem:

```text
-zeta'/zeta(s) = s * integral_1^infty psi(x) * x^(-s-1) dx
```

initially for `re s > 1`, then subtract the pole term:

```text
-zeta'/zeta(s) - 1 / (s - 1)
  = s * integral_1^infty (psi(x) - x) * x^(-s-1) dx + harmless terms.
```

If `psi(x) - x = O(sqrt x * log^2 x)`, this integral converges and is analytic
for `re s > 1 / 2`.  Therefore `-zeta'/zeta(s)` has no pole in that half-plane
except at `s = 1`.

Current status:

- The Mellin/Landau route is now proved for power-scale `psi` bounds:
  `regularizedNegLogDerivModel`,
  `differentiableOn_regularizedNegLogDerivModel_of_psi_power_error`, and
  `regularizedNegLogDerivModel_eq_neg_deriv_div_sub_pole` package the analytic
  continuation and overlap with `-zeta'/zeta - s/(s-1)`.
- `ZeroFreeRegion.psiPowerErrorBound_excludes_riemannZeta_zero_right` proves the
  resulting zero-exclusion theorem: `PsiPowerErrorBound theta`, with
  `0 <= theta < 1`, excludes zeta zeros in `theta < re rho < 1`.

### R3. Exclude zeros with `re > 1 / 2`

If zeta had a zero at `rho` with `rho.re > 1 / 2` and `rho != 1`, then
`-zeta'/zeta` would have a pole at `rho`.  R2 says the pole-subtracted
logarithmic derivative is analytic in `re s > 1 / 2`, contradiction.

Current status:

- The project no longer needs a separate general "zero implies log-derivative
  pole" API for this route.  The proved analytic-ODE nonvanishing argument in
  `ZeroFreeRegion.psiPowerErrorBound_excludes_riemannZeta_zero_right` gives the
  contradiction directly for `theta < re rho < 1`.
- `PrimeNumberTheorem.psiPowerErrorBound_of_RH_PsiErrorBound_of_half_lt`
  supplies the needed `PsiPowerErrorBound theta` for every `theta > 1/2` from
  `RH_PsiErrorBound`, so zeros with `re rho > 1/2` are excluded by choosing
  `theta` between `1/2` and `re rho`.

### R4. Use symmetry to finish RH

Once zeros with `re > 1 / 2` are excluded:

- A nontrivial zero with `re < 1 / 2` would map by
  `nontrivial_zero_symmetric'` to a nontrivial zero `1 - rho` with
  real part `> 1 / 2`.
- Therefore every nontrivial zero has `re = 1 / 2`.

Current status:

- `nontrivial_zero_symmetric'` is available.
- `RiemannHypothesis.Statement` is exactly the required endpoint.
- `rh_statement_iff_mathlib` bridges back to Mathlib/root RH if needed.
- `ZeroFreeRegion.riemannHypothesis_of_RH_PsiErrorBound` combines this symmetry
  with the right-half exclusion and proves the conditional endpoint
  `RH_PsiErrorBound -> RiemannHypothesis`.

## Minimal New Dependency Chain

The smallest coherent route to make
`rh_iff_primeCounting_li_error` a theorem is:

1. Define quantitative error predicates with `=O[atTop]` for `psi`, `theta`,
   and `primeCounting - logIntegral`.
2. Prove or import a truncated explicit formula for `psi` with precise jump and
   truncation conventions.
3. Prove zero-counting and reciprocal-zero-sum estimates:
   `N(T) = O(T log T)` and `sum 1 / |rho| = O(log^2 T)`.
4. Prove `RH -> RH_PsiErrorBound` by bounding the truncated explicit formula.
5. Use the existing `psi - theta` Mathlib bound to get `RH_ThetaErrorBound`.
6. Use the proved quantitative partial-summation bridge
   `RH_ThetaErrorBound -> RH_PrimeCountingLiErrorBound`.
7. For the reverse direction from the prime-counting endpoint, prove
   quantitative partial summation back to `RH_PsiErrorBound`.
8. Use the already-proved
   `ZeroFreeRegion.riemannHypothesis_of_RH_PsiErrorBound` to obtain Mathlib's
   `RiemannHypothesis` from that `psi` endpoint.

The already-proved PNT-form equivalence remains useful documentation and sanity
checking, but it is too coarse for the RH error equivalence: it tracks limits,
not the `sqrt x`-scale quantitative error.
