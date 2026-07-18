# Smoothed-Error Optimization Preregistration

Date fixed: 2026-07-19

## Scope and claim boundary

This milestone tests an optimization and proof interface. It does not prove any
of the candidate analytic error envelopes below, improve a published constant,
or strengthen the repository's current PNT or RH results. The numerical
constants in the benchmark profiles are fixed hypothetical inputs. A profile
may be called a mathematical improvement only after its envelope, constants,
and full range have been certified independently and connected to the Lean
transfer theorem.

Write

- `S(x) = smoothedChebyshevPsi x` for the first von Mangoldt Riesz mean;
- `A_T(x)` for a complex finite-height approximation to `S(x)`;
- `E(x,T)` for a nonnegative certified bound on `||A_T(x)-S(x)||`;
- `L(x,h) = log((x+h)/x)` for `x > 0` and `h > 0`.

The reusable transfer target is

```text
psi(x) <= (Re A_T(x+h) - Re A_T(x) + E(x,T) + E(x+h,T)) / L(x,h)
(Re A_T(x+h) - Re A_T(x) - E(x,T) - E(x+h,T)) / L(x,h)
  <= psi(x+h).
```

When the approximation's main term is `A_T(u) = u + error`, the comparison
prototype minimizes the certified endpoint penalty

```text
B(x,h,T) = max(h/L(x,h)-x, x+h-h/L(x,h))
           + (E(x,T)+E(x+h,T))/L(x,h).
```

This is an endpoint transfer penalty, not by itself a two-sided bound for
`|psi(x)-x|` at one point.

## Frozen repository baseline

The branch began clean at commit `638735b` on
`research/smoothed-error-optimization`. The relevant verified source surface
at that commit is:

- `PrimeNumberTheorem.SecondOrderExplicitFormula` supplies a finite-height
  complex approximation to `smoothedChebyshevPsi`, conditional on its explicit
  contour and truncation terms.
- `PrimeNumberTheorem.SafeSecondOrderExplicitFormula` supplies safe selected
  heights and left boundaries, but not the optimized explicit numerical
  envelopes preregistered below.
- `PrimeNumberTheorem.RieszDifference.chebyshevPsi_le_rieszDifference_div_log_le`
  sandwiches a finite difference of `S` between `psi(x)` and `psi(y)`.
- The repository proves existential classical zero-free and RH-conditional
  error interfaces. It does not expose numerical constants for the candidate
  envelopes below and does not prove RH.

The pre-edit Python baseline was `python3 -m pytest -q`: `27 passed in 12.75s`.
A cold `lake -Kjobs=1 build` was explicitly interrupted after task
`8248/8357`; it is not recorded as a passing baseline. This milestone therefore
uses only the new targeted Lean roots, as requested.

## Fixed candidate theorem profiles

Each item is a candidate statement to be tested later, not a theorem currently
claimed by this branch.

### FH-1: finite-height profile

For every integer `x >= 10^6` and integer `T >= x`, construct the exact
finite-height approximation `A_T` from the second-order explicit formula and
certify

```text
||A_T(x) - S(x)|| <= x^2/T.
```

The prototype model name is `finite_height`, with constant `C_F = 1` and
`E_F(x,T) = C_F x^2/T`. Rational inputs and this envelope are evaluated exactly
before decimal conversion.

### RH-1: RH-conditional profile

Assuming the repository's `RiemannHypothesis`, for every integer `x >= 10^6`,
certify

```text
|S(x)-x| <= sqrt(x) * log(x)^2.
```

The prototype model name is `rh`, with `C_RH = 1`. This is only a benchmark
envelope. The milestone neither proves RH nor proves this explicit constant and
range from the current RH-conditional existential theorem.

### ZFR-1: classical-zero-free profile

Unconditionally, for every integer `x >= 10^6`, certify

```text
|S(x)-x| <= x * exp(-(1/5) * sqrt(log(x))).
```

The prototype model name is `classical_zero_free`, with `C_Z = 1` and
`a_Z = 1/5`. The repository's classical zero-free region and classical PNT
remainder do not currently certify these numerical constants or this threshold.

## Frozen experiment domain

The preregistered comparison grid is:

```text
x in {10^6, 10^7, ..., 10^12}
T/x in {1, 2, 4, 8, 16, 32, 64}
h in {max(1, floor(x/2^j)) : j = 4, 5, ..., 20}
precision in {80, 120} decimal digits
```

For RH-1 and ZFR-1, `T` is retained as an inert experiment coordinate so all
three models use the same record schema. The frozen nonoptimized comparator is
`h_base = floor(x/256)`.

## Success gates

All gates are conjunctive.

1. **Formal contract.** The Lean theorem has genuine parameters `x`, `h`, and
   `T`, accepts complex approximations and norm errors at both endpoints, and
   yields both endpoint inequalities above.
2. **Proof audit.** The new theorem and contract compile with no `sorry`,
   `admit`, project `axiom`, or `def ... : Prop` target. `#print axioms` may list
   only Mathlib foundations already accepted by the repository:
   `propext`, `Classical.choice`, and `Quot.sound`.
3. **Arithmetic audit.** Rational terms are exact. Every `log`, `sqrt`, and
   `exp` result is widened outward by at least one decimal context ULP. Every
   reported objective is an upper endpoint, never a midpoint.
4. **Precision stability.** The selected `h` and winning candidate agree at 80
   and 120 digits at every frozen grid point. Any disagreement is failure, not
   a tie to resolve heuristically.
5. **Optimization gate.** At every frozen grid point, the optimized certified
   upper endpoint is at most `99/100` of the lower endpoint of the corresponding
   fixed-`h_base` comparator. Interval overlap with the `99/100` threshold is a
   failure.
6. **Analytic certification gate.** Before wording any result as an improved
   constant, the exact candidate envelope must be proved on its full stated
   range and instantiated into the Lean transfer theorem. Numerical success
   without this step is only a prototype result.
7. **Reproducibility gate.** Repeated runs with identical inputs emit identical
   UTF-8 JSON bytes and select the same candidate and `h`.

## Failure and stopping conditions

Stop without an improvement claim if any of the following occurs:

- an envelope is sampled numerically rather than proved or interval-certified;
- a candidate requires changing its constant, threshold, range, or grid after
  results are inspected;
- directed intervals overlap a comparison threshold;
- precision changes the selected candidate or smoothing width;
- the finite-height approximation used by Python cannot be identified with the
  approximation accepted by the Lean theorem;
- the axiom audit exceeds the accepted Mathlib foundations;
- any `sorry`, `admit`, `axiom`, or proposition placeholder is introduced;
- the result improves only selected sample points rather than the full frozen
  grid and stated theorem range.

Changing a frozen item requires a new dated preregistration and a fresh output
namespace; it must not overwrite this experiment.

## Reproducible record format

The prototype emits deterministic JSON with schema
`smoothed-error-comparison-v1`. Required top-level fields are `arithmetic`,
`domain`, `results`, `schema`, and `winner`. Decimal interval upper bounds are
serialized as strings, candidate rational parameters as canonical `Fraction`
strings, and no timestamp or machine-specific path is included.

One fixed-profile smoke command is:

```bash
python3 -m experiments.pnt.smoothed_error_optimizer \
  --x 1000000 --height 64000000 \
  --h 62500 --h 31250 --h 15625 --h 7812 --h 3906 \
  --candidate fh-1:finite_height:1 \
  --candidate rh-1:rh:1 \
  --candidate zfr-1:classical_zero_free:1:1/5 \
  --precision 80
```

The complete grid runner and analytic certification are explicitly outside this
first executable milestone. The unresolved mathematical problem is to derive
one of FH-1, RH-1, or ZFR-1 with explicit constants and ranges from the current
contour, zero-sum, and zero-free estimates without losing more in the smoothing
transfer than the optimizer recovers.
