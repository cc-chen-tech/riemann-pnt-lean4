# Classical Prime-Counting Error Design

## Goal

Prove a theorem about the actual project functions `primeCounting` and
`logIntegral`:

```lean
theorem exists_abs_primeCounting_sub_logIntegral_le_exp_neg_sqrt_log :
    ∃ c C X : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ x : ℝ, X ≤ x →
      |(primeCounting x : ℝ) - logIntegral x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x))
```

The constants remain existential.  The publication claim is therefore a
classical de la Vallee Poussin-form remainder, not a numerically explicit
bound.  This theorem does not imply a power saving below `2/3`, exclude zeros
on `Re(s)=1/3`, or prove RH.

## Existing Inputs

The proof must consume checked analytic results rather than introduce a new
conditional interface:

- `exists_abs_chebyshevPsi_sub_id_le_exp_neg_sqrt_log` supplies the proved
  right-continuous Chebyshev `psi` estimate on all sufficiently large real
  arguments.
- `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log` controls the prime-power
  correction from `psi` to `theta`.
- `primeCounting_sub_logIntegral_eq_theta_error_integral` is the exact Abel
  decomposition in the repository's normalization.
- `intervalIntegrable_theta_error_div_id_log_sq_of_le` supplies integrability
  of the Abel error kernel on compact intervals above `2`.

No `def ... : Prop`, `sorry`, `admit`, custom axiom, or theorem-valued wrapper
may stand in for the final estimate.

## Considered Approaches

### 1. Direct pointwise transfer and split integral

First weaken the decay constant and transfer the proved `psi` estimate to
`theta`.  Then split the Abel integral into a fixed initial interval,
`[A, sqrt x]`, and `[sqrt x, x]`.  Estimate each interval pointwise and combine
the result with the exact Abel identity.

This is the selected approach.  Every inequality is visible in the final Lean
proof, and the output directly closes the named prime-counting endpoint.

### 2. General Big-O integration framework

Develop a reusable theorem saying that an error of de la Vallee Poussin form
is preserved by the Abel kernel.  This could shorten later applications, but
it would add a broad abstraction before the concrete endpoint exists and
would recreate part of asymptotic-integration infrastructure.

This approach is rejected for the current stage because it risks returning to
API-first work.

### 3. Prove eventual monotonicity of the complete kernel

Differentiate `x * exp (-c * sqrt (log x))` and use monotonicity to estimate
the whole Abel integral without splitting at `sqrt x`.  This is mathematically
clean but creates avoidable derivative, continuity, and endpoint obligations.

This approach is rejected because the split proof needs only order estimates
already present in Mathlib.

## Proof Architecture

### 1. Transfer the remainder from `psi` to `theta`

Create `PrimeNumberTheorem/ClassicalPrimeCountingError.lean`, importing
`PrimeNumberTheorem.ClassicalPNTError`.

From

```text
|psi(x)-x| <= C x exp(-c sqrt(log x))
```

and

```text
|psi(x)-theta(x)| <= 2 sqrt(x) log(x),
```

derive, after replacing `c` by a smaller positive constant `a`,

```text
|theta(x)-x| <= D x exp(-a sqrt(log x)).
```

The absorption is elementary.  For large `x`, use
`log x <= 4*x^(1/4)` and compare
`x^(3/4)` with `x*exp(-a*sqrt(log x))`.  The latter comparison follows once
`a*sqrt(log x) <= log(x)/4`.  This stage must produce an eventual pointwise
bound, not merely a qualitative `o(x)` statement.

### 2. Bound the Abel integral

Let

```text
K(t) = (theta(t)-t) / (t * log(t)^2).
```

Choose `A` above the theta-error threshold, `exp 1`, and `2`.  For sufficiently
large `x`, ensure `A <= sqrt x` and split

```text
integral 2 x K = integral 2 A K
                 + integral A (sqrt x) K
                 + integral (sqrt x) x K.
```

On `[A, sqrt x]`, `log t >= 1`, so the theta bound gives `|K(t)| <= D`.
The interval therefore contributes at most `D*sqrt x`.

On `[sqrt x, x]`, prove

```text
sqrt(log t) >= sqrt(log x) / 2.
```

Consequently this interval contributes at most

```text
D*x*exp(-(a/2)*sqrt(log x)).
```

Choose the final decay constant `b = a/4`.  For large `x`, both the fixed
initial integral and the `sqrt x` contribution are bounded by a constant
multiple of

```text
x*exp(-b*sqrt(log x)).
```

The result of this stage is a genuine eventual absolute-value estimate for
the Abel integral.

### 3. Assemble the prime-counting estimate

Use `primeCounting_sub_logIntegral_eq_theta_error_integral`.  Bound:

- `(theta(x)-x)/log x` by the theta remainder, using `1 <= log x`;
- the integral by Stage 2;
- the fixed term `2/log 2` by the final scale, which is eventually at least
  `1`.

Combine the three terms with `abs_add_le`, package the eventual statement as
explicit existential constants `c`, `C`, and `X`, and export exactly this
theorem through `RiemannPNT.API`.

## Testing and Audit

Before production code, add `Test/ClassicalPrimeCountingErrorContract.lean`
with examples requiring both the namespace theorem and the public API theorem.
Register it in `lakefile.lean` and run its target once to confirm failure due to
the missing declaration.

After implementation:

- build the focused contract;
- print axioms for the namespace theorem and API theorem;
- add both declarations to the existing standard-axiom allowlist;
- run target-inventory and chain-gap checks;
- run Python tests and the default `lake build`;
- run `scripts/verify-baseline.sh`;
- obtain an independent review of the theta absorption, interval split, and
  publication wording.

## Documentation Boundary

Update the theorem inventory, contribution summary, README, publishing notes,
missing-chain index, and proof atlas only after the theorem compiles.  State
the exact remainder shape.  Keep all of the following explicitly open:

- numerically explicit constants;
- any `O(x^(2/3-delta))` prime error;
- unconditional exclusion of zeros on `Re(s)=2/3` or `Re(s)=1/3`;
- RH, Hardy's theorem, and the Vinogradov-Korobov region.
