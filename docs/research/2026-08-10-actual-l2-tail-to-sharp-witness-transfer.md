# Actual L2 tail to sharp witness transfer

## Purpose

This note specifies the one integration theorem needed between:

- a retained finite zero cluster with a sharp normalized `L2` lower bound;
- the actual-zeta complement with the dyadic Carlson `L2` upper bound;
- the cubic explicit-formula nonzero residual terms.

It does not reprove the Sharp lower bound, half-isolated separation, or the
actual Carlson shell estimate.  It only assembles their outputs on the same
normalized PNT error object.

## Common normalization

Fix a target zero `rho0` with

```text
beta0 := Re rho0,
gamma0 := Im rho0,
```

and use logarithmic position `u = log x`.  Normalize every explicit-formula
term by the exact target scale

```text
Scale(u) := exp (beta0 * u) / |rho0|.
```

For the PNT error `E(exp u)`, define

```text
normalizedError(u)
  := |rho0| * exp (-beta0 * u) * E(exp u).
```

The desired pointwise conclusion

```text
|normalizedError(u)| >= c
```

is exactly

```text
|E(x)| >= c * x^beta0 / |rho0|.
```

No denominator such as `|rho0|^(1+epsilon)` is substituted for this scale.

## Probability triangle weight

On the observation interval

```text
[uMin,uMax] = [log X, lambda * log X],
```

put

```text
u0 := (uMin + uMax) / 2,
L  := (uMax - uMin) / 2,

W_L(v) := (1 / L) * max (1 - |v| / L) 0.
```

For `L > 0`,

```text
W_L(v) >= 0,
support W_L subset [-L,L],
integral W_L = 1.
```

Define the weighted norm

```text
triangleNorm(F)
  := sqrt (integral v, W_L(v) * |F(v)|^2).
```

This is the ordinary `L2` norm of `sqrt(W_L) * F`, so Minkowski applies:

```text
triangleNorm(F + G)
  >= triangleNorm(F) - triangleNorm(G).
```

## Exact explicit-formula decomposition

Choose a finite retained zero cluster `S`.  On `u = u0 + v`, write the same
normalized explicit formula as

```text
normalizedError(u0 + v)
  = Main_S(v)
      + ZeroTail_S(v)
      + Contour(v)
      + SZero(v)
      + TrivialZeros(v).
```

The pole at `s = 1` has already cancelled the exact smoothed main term and is
not included in the residual norm.

Set

```text
Residual_S
  := ZeroTail_S + Contour + SZero + TrivialZeros.
```

The zero tail must use the complement of exactly the same finite set `S` that
defines `Main_S`.  This is where the finite-deletion monotonicity theorem from
the Carlson slice is consumed.

## Quantitative transfer theorem

The deterministic theorem has the following hypotheses:

```text
triangleNorm(Main_S) >= cMain,
triangleNorm(ZeroTail_S) <= cZeroTail,
triangleNorm(Contour) <= cContour,
triangleNorm(SZero) <= cSZero,
triangleNorm(TrivialZeros) <= cTrivial,
```

with all constants nonnegative.  Put

```text
cResidual
  := cZeroTail + cContour + cSZero + cTrivial.
```

Repeated Minkowski gives

```text
triangleNorm(Residual_S) <= cResidual
```

and therefore

```text
triangleNorm(normalizedError) >= cMain - cResidual.
```

If

```text
0 < cMain - cResidual,
```

continuity of the finite/smoothed explicit-formula expression on the compact
interval gives a point `v in [-L,L]` such that

```text
|normalizedError(u0 + v)| >= cMain - cResidual.
```

Equivalently, for

```text
x := exp (u0 + v) in [X, X^lambda],
```

one obtains

```text
|E(x)|
  >= (cMain - cResidual) * x^beta0 / |rho0|.
```

The compact-continuity step is part of the theorem contract.  An abstract
measure-space statement without essential-supremum or attainment hypotheses
must not claim an actual witness point.

## Preserving a strict pi/2 constant

The transfer theorem is constant-parametric.  Assume the retained cluster
supplies

```text
cMain >= pi / 2 + surplusMain
```

and the complete residual satisfies

```text
cResidual <= surplusTail,
0 <= surplusTail,
surplusTail < surplusMain.
```

Then

```text
cMain - cResidual
  >= pi / 2 + (surplusMain - surplusTail)
  > pi / 2.
```

The resulting witness therefore retains a constant strictly greater than
`pi/2` at the correct reciprocal-height scale:

```text
|E(x)| > (pi / 2) * x^beta0 / |rho0|.
```

Carlson does not create `surplusMain`; it only proves that the actual
complement consumes less than the surplus already supplied by the retained
cluster theorem.

## Decaying residual specialization

The dyadic exponent ledger should provide, for some `etaZero > 0`,

```text
triangleNorm(ZeroTail_S) = O(X^(-etaZero)).
```

The cubic ledger separately supplies positive exponents

```text
etaContour,
etaSZero,
etaTrivial.
```

Let

```text
etaResidual
  := min etaZero (min etaContour (min etaSZero etaTrivial)) > 0.
```

After increasing a fixed threshold, the total residual may be made smaller
than any prescribed positive part of `surplusMain`.  In particular, choosing

```text
cResidual <= surplusMain / 2
```

gives the explicit retained margin

```text
cMain - cResidual
  >= pi / 2 + surplusMain / 2.
```

The threshold must quantify every constant from the shell, dyadic, contour,
`s = 0`, and trivial-zero bounds.  A bare statement that each term tends to
zero is not yet an explicit transfer theorem.

## Absolute witness versus signed oscillation

The theorem above proves an absolute witness.  Since the PNT error is real,
the witness has one of the two signs, but the theorem does not determine which
one and does not prove both signs occur.

Therefore:

- it is sufficient for an absolute `Omega` conclusion;
- it is not sufficient for `Omega_+`;
- it is not sufficient for `Omega_-`;
- it is not sufficient for `Omega_+-`.

A signed conclusion requires an additional signed lower-bound input, a
phase-shift pair, a mean-zero argument, or two disjoint witness sets.  That
input belongs to Sharp/half-isolated, not to the Carlson tail module.

## Proposed Lean interface

The deterministic integration theorem belongs in the owned unified-transfer
module and should be stated independently of zeta:

```text
triangleNorm_add_lower
triangleNorm_finset_sum_upper
exists_norm_ge_triangleNorm_of_continuous
exists_witness_of_main_energy_and_residual_energy
exists_witness_gt_pi_div_two_of_surplus
```

The actual adapter then instantiates it with:

```text
actualNormalizedPNTError_eq_main_add_residual
actualZeroTail_triangleNorm_le
actualCubicResidual_triangleNorm_le
actualPNTError_exists_abs_witness
```

Names are provisional.  The actual theorem statement must expose:

```text
rho0, S, X, lambda,
cMain, surplusMain,
all residual constants and thresholds,
x in Set.Icc X (X^lambda),
|E(x)| > (pi / 2) * x^(Re rho0) / |rho0|.
```

It must not hide the target scale behind an arbitrary amplitude function.

## Formal proof dependency order

1. Prove nonnegativity, support, and unit mass of `W_L`.
2. Define `triangleNorm` through `sqrt(W_L) * F`.
3. Obtain Minkowski from the existing `L2` norm theorem.
4. Prove the finite residual-sum upper bound.
5. Prove norm attainment for continuous functions on `[-L,L]`.
6. Prove the deterministic main-minus-residual witness theorem.
7. Add the strict `pi/2` surplus arithmetic corollary.
8. Instantiate with the exact normalized cubic explicit formula.
9. Insert the actual-zeta finite-deletion tail bound.
10. Keep signed conclusions outside this slice.

## Audit requirements

- The main and complement use the identical finite set `S`.
- Every term uses the same `|rho0| * exp(-beta0*u)` normalization.
- The witness lies in `[X,X^lambda]` by the exact support calculation.
- The final denominator is exactly `|rho0|`.
- Strictly greater than `pi/2` comes from a positive surplus inequality.
- Energy bounds are square-rooted before being added as residual norms.
- No absolute-energy theorem is labelled `Omega_+` or `Omega_-`.
- No Sharp or half-isolated theorem is redefined in this module.
- No claim of RH or exclusion of zeros with `Re rho > 1/2` is made.
