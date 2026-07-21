# Zero-Forced Oscillation Preregistration

## Status and scope

This document preregisters the classical-zeta target and the first formal
milestone before any theorem about zero-forced oscillation is claimed.  The
first milestone is deliberately finite-dimensional: prove an explicit
mean-square estimate for a finite exponential polynomial with arbitrary
complex coefficients, distinct real frequencies, and optional natural-number
multiplicities.  It does not transfer a zeta zero to an oscillation of
`psi(x) - x`.

The reference baseline is Theorem 1 quoted in Szilard Gy. Revesz,
*Oscillation of the remainder term in the prime number theorem of Beurling,
"caused by a given zeta-zero"*, IMRN 2023, arXiv:2202.01837v3.  Revesz states
the classical Riemann-zeta theorem with the constant `pi/2`; his Theorem 2
extends the conclusion to Beurling systems satisfying Axiom A.  The paper also
records the older constant `1` result of Pintz and explains why conjugate-zero
interference is the issue addressed by the `pi/2` result.

Primary sources:

- https://arxiv.org/abs/2202.01837
- https://doi.org/10.1093/imrn/rnac274

## Timeboxed milestone outcome

**Status: F0_PASSED_AND_ZETA_ALIGNED; F1_PACKAGE_ISOLATION_PASSED;
F1_CLOSED_TERMS_BOUNDED; F1_UNCONTROLLED_REMAINDER_OPEN.**  The checked Lean surface
proves the exact integral and interval-independent norm bound for one ordered
off-diagonal pair, the aggregate finite mean-square estimate, and an interior
point attaining the resulting lower average.  Natural multiplicity is retained
as an explicit coefficient factor.  It now also proves the exact
logarithmic-coordinate identity

```text
sum_{rho in S} m(rho) exp(y)^rho / rho
  = exp(beta*y) * sum_{rho in S} (m(rho)/rho) exp(i Im(rho) y)
```

for a finite package with `Re(rho) = beta`, derives ordinate injectivity from
that common-real-part condition, and specializes the F0 pointwise lower bound
directly to this complex-power package.  The contract and axiom audit cover
these declarations as well as the generic finite-spectrum mechanism.

The new heavy bridge module now filters the repository's actual
`nontrivialZerosFinset T`, retains `analyticOrderNatAt riemannZeta`, and proves
that the complete finite zero sum is the selected equal-real-part package plus
its complement. It also proves the exact identity

```text
psi0(exp y) - exp y = -selected_package(y) - explicit_remainder(y,T,beta)
```

and the corresponding reverse-triangle lower bound. This completes package
isolation inside the actual explicit-formula approximation. The closed block is
now split from the remaining analytic terms: Lean proves

```text
zeta'(0) / zeta(0) = log(2*pi)
|log(1 - exp(-2y))| <= exp(-2y) / (1 - exp(-2y))   (y > 0),
```

and hence a norm budget

```text
||closed_terms(y)|| <= log(2*pi)
  + (1/2) * exp(-2y) / (1 - exp(-2y)).
```

The resulting transfer theorem subtracts exactly this budget while retaining
`uncontrolled_remainder(y,T,beta)` as the sum of the complementary zero
package and the actual explicit-formula approximation error. It does not
bound either constituent, and does not give a uniform truncation estimate on a
logarithmic interval. Therefore the quantitative remainder requirement in F1,
the Revesz baseline recovery, and both novelty gates remain open.

## Exact classical-zeta candidate theorem

Write

```text
Delta(x) = psi(x) - x.
```

The research-line candidate is the following exact mathematical statement.
It is a preregistered target, not a declaration to add to Lean during this
milestone.

```text
For every rho0 in C and epsilon > 0, if

  zeta(rho0) = 0,
  0 < Re(rho0) < 1,
  Im(rho0) != 0,

then for every X > 0 there exists x >= X such that

  |psi(x) - x| >= (pi / 2 - epsilon)
                      * x ^ Re(rho0) / |rho0|.
```

The intended Lean endpoint will use the repository's actual predicates for a
nontrivial zero, its actual `chebyshevPsi` convention, `Real.rpow`, and an
explicit `forall X, exists x >= X` formulation.  No custom `Prop` alias will
stand in for this statement.  Endpoint conventions at prime powers must be
settled before formalization; changing between `psi` and the midpoint
`psi0` is allowed only after proving that the change is negligible at the
claimed scale.

## Revesz baseline and novelty gates

The baseline is already the classical `pi/2 - epsilon` amplitude at
arbitrarily large values of `x`.  Reproving a weaker Omega result, proving only
an absolute-value statement for a finite zero sum, or restating the target as
an assumption is not mathematical novelty.

The gates are cumulative:

1. **F0: finite-spectrum mechanism.**  Lean proves the explicit diagonal and
   ordered off-diagonal estimate

   ```text
   | integral_a^b |sum_j c_j exp(i omega_j t)|^2 dt
       - (b-a) sum_j |c_j|^2 |
     <= sum_j sum_{k != j} 2 |c_j| |c_k| / |omega_j-omega_k|,
   ```

   for arbitrary finite coefficients and frequencies injective on the chosen
   finite set.  It also proves an interior point whose squared modulus is at
   least the resulting lower average.  Natural multiplicities remain explicit
   as factors `m_j` in the coefficients.

2. **F1: explicit-formula transfer.**  A proved theorem, not a hypothesis,
   connects a finite multiplicity-aware zeta-zero sum and a quantitatively
   controlled remainder to `psi(x)-x` on a specified logarithmic interval.

3. **B0: baseline recovery.**  The formal theorem reaches every fixed
   constant below `pi/2` for arbitrarily large `x`, with the exact classical
   zeta and `psi`.  This matches Revesz and is a formalization result, not a new
   analytic theorem.

4. **N1: quantitative localization.**  A result is analytically stronger only
   if it gives a proved interval `[X, X^A]` or shorter, with `A` explicit in
   the zero data and epsilon, while retaining the `pi/2 - epsilon` amplitude.

5. **N2: classical-only improvement.**  A constant strictly above `pi/2`, or
   a materially shorter localization at the same constant, counts as a
   novelty candidate only after comparison with current classical literature
   and independent proof review.  Revesz's sharpness discussion for broader
   zeta-type/Beurling classes forbids extrapolating such an improvement to
   those classes.

## Intended F0 theorem contract

The production module is
`PrimeNumberTheorem/ZeroForcedOscillation.lean`.  It must import only the
Mathlib analysis needed for finite sums, elementary complex exponentials,
interval integrals, and the interval-average mean value theorem.  It must
provide genuine theorems for:

- the exact integral of one nonzero-frequency complex exponential;
- the diagonal integral;
- the norm bound for one ordered off-diagonal pair;
- the aggregate finite exponential-polynomial mean-square estimate;
- an interior point attaining the interval average, hence the quantitative
  lower pointwise consequence;
- a specialization retaining `multiplicity : i -> Nat` as an explicit factor.
- an exact conversion of a common-real-part complex-power package with
  coefficients `m(rho)/rho` to the generic exponential polynomial;
- the corresponding local pointwise lower bound with all analytic
  multiplicities and pairwise ordinate gaps visible.

The aggregate error is an ordered-pair sum.  Therefore each unordered pair is
represented twice, and the displayed constant `2` on each ordered pair is
intentional.  No minimum frequency-gap replacement is part of F0.

The checked contract now contains the pairwise formulas, the aggregate bound,
the interior-point consequence, the multiplicity-weighted specialization, and
the common-real-part complex-power bridge used by a zeta zero package.

## Failure conditions

Report this milestone as failed or incomplete if any of the following occurs:

- the module introduces `sorry`, `admit`, `axiom`, or an opaque route `Prop`;
- frequency distinctness is dropped while a denominator
  `|omega_j - omega_k|` remains;
- a `Finset` of zeros silently discards analytic multiplicity;
- coefficients are specialized to zeta coefficients before the generic
  finite theorem is proved;
- the diagonal term is weakened to an unspecified constant or asymptotic;
- the pointwise theorem is only an assumption-to-assumption wrapper;
- a numerical experiment is reported as evidence for the classical-zeta
  candidate theorem;
- a source build succeeds but `#print axioms` exposes a project-specific axiom;
- the zeta-to-`psi` transfer is claimed from F0 alone.

## Next exact gap

The next analytic/formal result is the remaining quantitative half of F1:
prove that `zeroPackageUncontrolledRemainder y T beta` is uniformly smaller
than the F0 lower amplitude minus the proved closed-form budget on a specified
logarithmic interval. The package is already an actual selected zeta-zero
contribution in the repository's finite-height approximation. What remains
requires quantitative control of complementary/lower-real-part zeros and the
explicit-formula approximation error. The closed logarithmic term is no
longer a gap, but no theorem here controls complementary zeros or a uniform
truncation error.

## Experiment schema

Experiments are diagnostic and begin only after F0 is checked.

### Inputs

- `zero_source`: immutable source/version for ordinates and multiplicities;
- `height_cutoff`: finite zero cutoff;
- `beta_slice`: rule selecting equal or near-equal real parts;
- `coefficient_rule`: for example `m(rho)/rho`, recorded exactly;
- `frequency_rule`: normally `Im(rho)` after conjugate-pair normalization;
- `u_interval`: `[U, U+L]` in logarithmic coordinate `u = log x`;
- `grid_step` and arithmetic precision;
- `remainder_model`: omitted, rigorous, or explicitly heuristic.

### Precomputed predictions

For each finite spectrum, record before sampling:

```text
diagonal_mass = sum_j |c_j|^2
off_diagonal_budget(L) =
  sum_j sum_{k != j} 2 |c_j| |c_k| / |omega_j-omega_k|
lower_mean_square = diagonal_mass - off_diagonal_budget(L) / L.
```

The run is informative only when `lower_mean_square > 0` and the grid is fine
enough to resolve the largest retained frequency.

### Outputs

- observed maximum of the finite polynomial and its location;
- numerical quadrature of the squared modulus;
- discrepancy from `L * diagonal_mass`;
- ratio of the discrepancy to the proved off-diagonal budget;
- sensitivity to cutoff, precision, interval length, and multiplicity;
- separate values for the finite zero sum and any modeled remainder.

### Held-out checks

Choose interval starts, a higher zero window, and at least one multiplicity or
coefficient perturbation before viewing results.  A claim survives the
experiment gate only if the qualitative conclusion is stable on these held-out
runs.  No experiment can pass F1, B0, N1, or N2.

## Verification protocol

The contract build must first fail because the production import is absent.
After implementation, run only:

```text
lake env lean Test/ZeroForcedOscillationExplicitFormulaContract.lean
lake env lean Test/ZeroForcedOscillationExplicitFormulaAxiomAudit.lean
```

The audit must print axioms for the aggregate mean-square bound, its
multiplicity specialization, the interior-point consequence, the
common-real-part complex-power bridge, the closed-term bound, and the
closed-budget transfer.
A final source scan must find no
`sorry`, `admit`, or `axiom` in the new production and test files.
