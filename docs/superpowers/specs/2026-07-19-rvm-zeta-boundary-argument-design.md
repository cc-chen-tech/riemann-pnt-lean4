# Riemann-von Mangoldt Zeta Boundary Argument Design

## Objective

Prove the missing logarithmic bound for the zeta contribution on the upper
horizontal side of the Riemann-von Mangoldt counting rectangle.  The public
result must bound the branch-free argument variation

```text
integral sigma in 1/2..2 of
  Im (logDeriv riemannZeta (sigma + I*T))
```

by a constant times `1 + log (T + 5)` at every sufficiently high good height.
This is an actual theorem about the existing `riemannZeta`; it is not a `Prop`
target or a route interface.

## Chosen Route

Use the imaginary part of the logarithmic-derivative integral directly.  Do
not construct a global or pathwise branch of `Complex.log riemannZeta`.

The existing shifted Jensen theorem writes the logarithmic derivative on the
horizontal segment as

```text
regularized part + finsum_u D(u) * (z - u)^(-1),
```

where both the regularized part and the total nonnegative divisor mass are
`O(1 + log (T + 5))`.  Integrating the norm of the principal part pointwise
would lose another logarithm near a zero.  Instead, integrate its imaginary
part exactly: each inverse factor changes angle by at most `pi`, independently
of its distance from the horizontal line.  Multiplicity-weighting and summing
then costs only the divisor mass, preserving the required single logarithm.

## Public Interfaces

### Simple-pole angle helper

Add a focused real-variable helper under `MathlibAux`:

```lean
theorem abs_intervalIntegral_im_inv_horizontal_sub_le_pi
    {a b t : ℝ} {u : ℂ} (ht : t ≠ u.im) :
    |∫ sigma in a..b,
      ((((sigma : ℂ) + I * t) - u)⁻¹).im| ≤ Real.pi
```

The implementation may expose an exact arctangent endpoint formula as a
supporting theorem.  The exported bound must work for either endpoint order.

### Zeta horizontal argument variation

Define

```lean
noncomputable def zetaHorizontalArgumentVariation (T : ℝ) : ℝ :=
  ∫ sigma in (1 / 2 : ℝ)..2,
    (logDeriv riemannZeta ((sigma : ℂ) + I * T)).im
```

and prove

```lean
theorem exists_abs_zetaHorizontalArgumentVariation_le_log :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 4 ≤ T →
      ExplicitFormulaAux.goodHeight T →
      |zetaHorizontalArgumentVariation T| ≤
        C * (1 + Real.log (T + 5))
```

The theorem is intentionally stated for every good height, not merely a
selected height in each unit interval.  Good height is used only to exclude
zeros on the integration segment; no logarithmic zero-separation hypothesis
is allowed in this theorem.

## Proof Decomposition

### 1. One inverse factor

For `d = t - u.im != 0`, rewrite

```text
Im (((sigma + I*t) - u)^(-1))
  = -d / ((sigma - u.re)^2 + d^2).
```

Use the antiderivative

```text
-arctan ((sigma - u.re) / d)
```

and the fundamental theorem of interval integration.  Both endpoint values of
`arctan` lie strictly between `-pi/2` and `pi/2`, so their difference has
absolute value at most `pi`.  This proof must not assume `a <= b` or a lower
bound on `abs d`.

### 2. Finite divisor principal part

For the divisor on the radius-`7/5` closed ball centered at `3/2 + I*T`:

- obtain finite support from compactness;
- rewrite each relevant finsum as a finite sum over that support;
- commute the finite sum with the interval integral;
- use nonnegativity of zeta divisor values on the high disk;
- apply the simple-pole angle bound termwise;
- bound the result by `pi` times the finsum divisor mass.

Good height implies `T != u.im` for every divisor support point because every
such point is an existing nontrivial zeta zero.

### 3. Regularized part

Use
`ZeroFreeRegion.exists_shifted_disk_regularized_logDeriv_riemannZeta_log_bound`.
Every point with `1/2 <= sigma <= 2` lies in the retained radius-`1` disk, and
good height supplies zeta nonvanishing.  Bound the absolute value of the
integral of the imaginary part by the interval length times the pointwise
norm bound.  The fixed interval length is `3/2` and is absorbed into the final
constant.

### 4. Assembly

Pointwise, split `logDeriv riemannZeta` into the regularized part and the
principal divisor sum.  Prove interval integrability of both finite pieces,
integrate the equality, apply the two bounds, and use
`ZeroFreeRegion.exists_finsum_divisor_riemannZeta_shifted_disk_log_bound` for
the divisor mass.  Choose one nonnegative constant depending only on the two
existing Jensen constants and `pi`.

## Verification

Add contract modules for both public theorem surfaces and axiom-audit modules
using `#print axioms`.  Run focused builds with one Lake job:

```bash
lake -Kjobs=1 build MathlibAux.HorizontalArgument
lake -Kjobs=1 build Test.HorizontalArgumentContract Test.HorizontalArgumentAxiomAudit
lake -Kjobs=1 build PrimeNumberTheorem.RiemannVonMangoldt.ZetaArgumentBound
lake -Kjobs=1 build Test.RiemannVonMangoldtZetaArgumentContract
lake -Kjobs=1 build Test.RiemannVonMangoldtZetaArgumentAxiomAudit
lake -Kjobs=1 build PrimeNumberTheorem.RiemannVonMangoldt
```

The new source files must contain no `sorry`, `admit`, or `axiom`.  The final
axiom surfaces may contain only `propext`, `Classical.choice`, and `Quot.sound`.

## Explicit Non-goals

- constructing a continuous logarithm of zeta;
- proving a pointwise `O(log T)` bound for `norm (zeta'/zeta)`;
- controlling the left half of a wider explicit-formula contour;
- deriving the completed-zeta count/phase identity;
- proving the good-height or all-height Riemann-von Mangoldt formula;
- generalizing this estimate to arbitrary completed L-functions.

Those later steps consume this theorem but are not substitutes for it.
