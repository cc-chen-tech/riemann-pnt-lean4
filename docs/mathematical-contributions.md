# Mathematical Contributions

This note records the main project-local mathematical contributions in the
current Lean checkout.  The statements below are aligned with the checked Lean
declarations, rather than with earlier draft descriptions.

## Scope Relative to Existing Formalizations

This file is an internal theorem inventory, not a claim that this repository is
the first formalization of the Prime Number Theorem or a completed classical
analytic PNT proof.

External SOTA has to be checked separately before making publication claims.
Relevant baselines include Isabelle/HOL formalizations of elementary PNT,
HOL Light formalizations of Newman's analytic PNT proof, Lean PNT work such as
`PrimeNumberTheoremAnd`, Mathlib's zeta and Dirichlet `L`-function
infrastructure, and any newer Lean repositories current at submission time.

The stable project-local contribution is narrower:

```text
de la Vallee Poussin 3-4-1 machinery and compact zero-free strip in Lean 4
```

In particular, the theorem inventory below should be read as verified support
for that local module, not as evidence that PNT, RH, the quantitative
`1 - c / log |t|` zero-free region, or the full explicit formula has been
proved.

## 1. Real Part of the Logarithmic Derivative Series

**Lean declaration:** `ZeroFreeRegion.log_deriv_zeta_re_series`

For `s = sigma + it` with `sigma > 1`,

```text
Re (-zeta'(s) / zeta(s))
  = sum_n Lambda(n) * cos(t log n) / n^sigma.
```

In Lean notation, the theorem is stated as

```lean
(- deriv riemannZeta s / riemannZeta s).re =
  ∑' n : Nat, Lambda n * Real.cos (s.im * Real.log n) / (n : Real) ^ s.re
```

The proof starts from Mathlib's complex-valued identity
`ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`, together
with summability from `ArithmeticFunction.LSeriesSummable_vonMangoldt`.

The main local calculation is
`natCast_cpow_neg_re`: for `n != 0`,

```text
Re ((n : C)^(-s)) = (n : R)^(-Re s) * cos((Im s) log n).
```

The proof expands complex powers via `cpow_def_of_ne_zero` and uses
`Complex.ofReal_log` for positive real coercions.  The real part is moved
through the infinite sum using Mathlib's `Complex.re_tsum` and the available
summability proof for the von Mangoldt L-series.

## 2. The 3-4-1 Logarithmic-Derivative Inequality

**Lean declaration:** `ZeroFreeRegion.log_deriv_zeta_nonneg_combination`

For `sigma > 1` and real `t`,

```text
3 Re(-zeta'(sigma)/zeta(sigma))
+ 4 Re(-zeta'(sigma+it)/zeta(sigma+it))
+   Re(-zeta'(sigma+2it)/zeta(sigma+2it)) >= 0.
```

The proof expands the three logarithmic-derivative terms using
`log_deriv_zeta_re_series`.  The resulting summand has the factor

```text
3 + 4 cos(t log n) + cos(2 t log n).
```

The pointwise nonnegativity is the elementary identity

```text
3 + 4 cos(theta) + cos(2 theta) = 2 (1 + cos(theta))^2 >= 0,
```

proved in Lean as `ZeroFreeRegion.trig_identity_nonneg` using
`Real.cos_two_mul`, `ring`, and `positivity`.

The formal proof also supplies the required summability arguments and combines
the three infinite sums with `Summable` operations and `tsum` algebra before
applying `tsum_nonneg`.

## 3. Compact Zero-Free Region at Bounded Height

**Lean declaration:** `ZeroFreeRegion.classical_zero_free_region_compact`

For any real `T` with `T >= 2`, there exists `d > 0` such that

```text
zeta(s) != 0
```

whenever

```text
|Im s| <= T  and  Re s >= 1 - d.
```

This is slightly stronger than versions that only state the result for
`2 <= |Im s| <= T`: the current theorem covers the whole bounded-height strip,
including the neighborhood of `s = 1`.

The current Lean proof is not the sequential compactness argument from earlier
drafts.  It uses an open-thickening compactness argument:

1. Prove that zeta is nonzero in a full neighborhood of `1`.  This uses
   `riemannZeta_residue_one` on the punctured neighborhood and
   `riemannZeta_one_ne_zero` at the point `1` itself.
2. Prove that `{s | riemannZeta s != 0}` is open.  Away from `1`, this follows
   from differentiability of `riemannZeta`; at `1`, it uses the previous item.
3. Let

   ```text
   K = {s : C | Re s = 1 and |Im s| <= T}.
   ```

   This is compact as a real-imaginary product of compact intervals.
4. Since `K` is contained in the open nonvanishing locus, use
   `IsCompact.exists_cthickening_subset_open` to obtain a uniform thickness
   `d > 0`.
5. If `Re s >= 1`, use Mathlib's `riemannZeta_ne_zero_of_one_le_re`.
   If `1 - d <= Re s < 1`, vertically project `s` to
   `k = 1 + i Im(s)` on `K`; then `dist s k <= d`, so `s` lies in the compact
   thickening and hence in the nonvanishing locus.

This proof deliberately avoids Hadamard factorization, zeta growth estimates,
and Borel--Caratheodory.  Its limitation is that the positive width `d` is
nonconstructive and depends on `T`; it does not prove a bound of the form
`c / log T`.

## 4. Residue-Scale Bounds on the Real Axis

**Lean declaration:** `ZeroFreeRegion.residue_bounds`

For `sigma > 1`,

```text
1 < (sigma - 1) * Re(zeta(sigma)) <= sigma.
```

Since `zeta(sigma)` is real for real `sigma > 1`, this is the real-axis bound
usually written as

```text
1 < (sigma - 1) zeta(sigma) <= sigma.
```

The proof first identifies the real zeta series:

```text
Re(zeta(sigma)) = sum_n 1 / (n + 1)^sigma.
```

It then uses Mathlib's `ZetaAsymptotics.zeta_limit_aux1`, which gives

```text
sum_n 1/(n+1)^sigma - 1/(sigma - 1)
  = 1 - sigma * E(sigma),
```

where

```text
E(sigma) = ZetaAsymptotics.term_tsum sigma
```

and each term is nonnegative:

```text
ZetaAsymptotics.term n sigma
  = integral from n to n+1 of (x - n) / x^(sigma + 1).
```

For the upper bound, `E(sigma) >= 0` gives

```text
zeta(sigma) <= 1/(sigma - 1) + 1 = sigma/(sigma - 1).
```

For the lower bound:

- if `sigma >= 2`, then `zeta(sigma) > 1 >= 1/(sigma - 1)`;
- if `1 < sigma < 2`, the proof compares `E(sigma)` to `E(1) = 1 - gamma`
  and uses `gamma > 1/2` to show `sigma * E(sigma) < 1`, hence

  ```text
  zeta(sigma) > 1/(sigma - 1).
  ```

Multiplying both inequalities by the positive number `sigma - 1` gives the
stated result.

## 5. Local Zero-Removed Regular-Part Estimate

The quantitative zero-free-region branch now contains a proved local theorem
that removes the previous dependence on the distance to the nearest zero.
For a pole-free outer disk and a zeta-zero-free intermediate circle, the
divisor factors inside that circle are replaced by canonical numerators and
the outer factors are retained. The resulting `mixedCanonicalRegularUnit` is
analytic and nonzero on the retained closed disk, agrees with zeta in norm on
its boundary, and has center norm at least that of zeta. The zero-free-circle
assumption is qualitative; no quantitative distance from that circle to each
zero enters the estimate.

Combining Borel--Caratheodory/Cauchy control of this unit with the finite
canonical correction gives

```text
‖logDeriv ζ(z) - sum_u D(u)/(z-u)‖
  <= boundaryGrowthTerm + divisorMass/(r-d).
```

This is formalized as
`norm_regularized_logDeriv_riemannZeta_le_mixedCanonical_bound`. The estimate
is local and conditional on the displayed disk data, but its coefficient is
independent of the nearest zero distance. The next unresolved step is a
uniform high-height specialization using the already proved zeta growth and
Jensen divisor-mass bounds, followed by isolation of the selected
zero-candidate principal term.

The follow-up theorem
`norm_regularized_logDeriv_riemannZeta_le_of_good_radius_and_jensen` performs
the good-circle selection and Jensen mass substitution internally, replacing
the selected denominator by the fixed margin `a-d`. Separately, the Mobius
reciprocal identity extends the center estimate `‖ζ(s)‖≥1/3` to
`Re(s)≥3/2`. These are genuine reductions of the remaining uniformity problem;
the functional-equation module now additionally proves the exact
Gamma/trigonometric cancellation and `‖ζ(it)‖≤4|t|²` on `Re(s)=0`.  This closes
one boundary of the required wider strip, but does not yet provide the
Phragmen-Lindelof interior growth theorem on `0<Re(s)<1` needed by disks that
reach the boundary line `Re(s)=1`.

## What This Does and Does Not Prove

The project-local contribution is not a complete proof of the Prime Number
Theorem or the Riemann Hypothesis, and it is not a claim to be the first PNT
formalization.  The verified contribution is the Lean formalization of
supporting infrastructure for one classical local route:

- the real-part Dirichlet-series representation of `-zeta'/zeta`;
- the full 3-4-1 logarithmic-derivative nonnegativity argument;
- a compact zero-free strip at every bounded height;
- real-axis residue-scale bounds for zeta near `1`.

Mathlib already provides the qualitative nonvanishing theorem
`riemannZeta_ne_zero_of_one_le_re`.  The new compact zero-free theorem upgrades
this to a positive-width strip at each fixed height by a topological
compactness argument.

The 3-4-1 inequality is separate infrastructure for the later quantitative
zero-free region

```text
Re s >= 1 - c / log |Im s|.
```

That quantitative theorem is still recorded only as a target statement in this
checkout.  Closing it requires zeta-specific growth and logarithmic-derivative
estimates in addition to the 3-4-1 mechanism.
