# Zero-Free Region Chain

This note audits the remaining Lean work needed to turn the current
zero-free-region infrastructure into the target
`ZeroFreeRegion.classical_zero_free_region : Prop`.

Current Lean status: `ZeroFreeRegion.lean` checks with
`lake env lean -R . ZeroFreeRegion.lean`.  The quantitative target is still a
`def ... : Prop`, not a proved theorem.

## Verified Starting Points

The following declarations are available in the current checkout:

```lean
ZeroFreeRegion.log_deriv_zeta_re_series
  (s : ℂ) (hs : 1 < s.re) :
  (-deriv riemannZeta s / riemannZeta s).re =
    ∑' n : ℕ, Λ n * Real.cos (s.im * Real.log n) / (n : ℝ) ^ s.re

ZeroFreeRegion.log_deriv_zeta_nonneg_combination
  (σ : ℝ) (hσ : 1 < σ) (t : ℝ) :
  3 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
    + 4 * (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re
    + (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
        riemannZeta ((σ : ℂ) + 2 * I * t)).re ≥ 0

ZeroFreeRegion.residue_bounds
  (σ : ℝ) (hσ : 1 < σ) :
  1 < (σ - 1) * (riemannZeta (σ : ℂ)).re ∧
    (σ - 1) * (riemannZeta (σ : ℂ)).re ≤ σ

ZeroFreeRegion.classical_zero_free_region_compact
  (T : ℝ) (_hT : T ≥ 2) :
  ∃ d > 0, ∀ s : ℂ, |s.im| ≤ T → s.re ≥ 1 - d →
    riemannZeta s ≠ 0
```

`residue_bounds` confirms the normalization of the pole at `1`, but it is not
yet a logarithmic-derivative estimate.  The missing quantitative step is the
standard de la Vallee Poussin contradiction:

1. assume a zero `ρ = β + i t` near `Re(s) = 1`;
2. evaluate the 3-4-1 inequality at `σ = 1 + η`;
3. bound the real-axis and `σ + 2it` terms by `O(log |t|)`, while the
   `σ + it` term contributes `-1 / (σ - β) + O(log |t|)`;
4. choose `η` and the final constant `c` small enough to contradict
   nonnegativity.

## Mathlib API Check

The local Mathlib already contains more relevant complex-analysis API than the
comments in `ZeroFreeRegion.lean` suggest:

- `Complex.borelCaratheodory` and `Complex.borelCaratheodory_zero` exist in
  `Mathlib.Analysis.Complex.BorelCaratheodory`.
- `MeromorphicOn.circleAverage_log_norm` exists in
  `Mathlib.Analysis.Complex.JensenFormula`; this is the local Jensen formula
  over closed balls for meromorphic functions.
- `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'` and
  related declarations exist in `Mathlib.Analysis.Complex.Hadamard`.
- `PowerSeries.exists_isWeierstrassFactorization` exists, but this is
  Weierstrass preparation for formal power series over complete local rings.
  It is not a global Hadamard product/factorization theorem for entire
  functions of finite order.

I did not find a Mathlib theorem that directly states the global Hadamard
factorization/product for finite-order entire functions or a ready-made
classical zeta zero-free region.

Useful checked names:

```lean
#check Complex.borelCaratheodory
#check MeromorphicOn.circleAverage_log_norm
#check Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
#check PowerSeries.exists_isWeierstrassFactorization
#check riemannZeta_residue_one
#check differentiableAt_riemannZeta
#check riemannZeta_ne_zero_of_one_le_re
#check ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
```

## Minimal Missing Lemmas

The following is the smallest useful Lean decomposition I see.  The names are
suggestions; statements should be adjusted when implementation starts.

### 1. Zeta Meromorphicity on Closed Balls

Mathematical statement:
`ζ` is meromorphic on every closed ball, with only a simple pole at `1`.

Suggested Lean statement:

```lean
lemma meromorphicOn_riemannZeta_closedBall (c : ℂ) (R : ℝ) :
    MeromorphicOn riemannZeta (Metric.closedBall c R)

lemma riemannZeta_divisor_pole_one
    (U : Set ℂ) (hU : 1 ∈ U) :
    (MeromorphicOn.divisor riemannZeta U) 1 = -1
```

Mathlib status:
`differentiableAt_riemannZeta` and `riemannZeta_residue_one` exist, but I did
not find a direct `MeromorphicOn riemannZeta ...` theorem or divisor theorem
for the pole at `1`.

Difficulty:
Medium.  Away from `1` this is routine from differentiability.  At `1`, the
proof should use the completed zeta API or the residue theorem already in
Mathlib, then connect it to `MeromorphicAt`/`MeromorphicOn.divisor`.

### 2. Polynomial Growth for Zeta in Vertical Disks

Mathematical statement:
On fixed-radius disks or fixed-width strips near `Re(s) = 1`, `ζ(s)` has
polynomial growth in `|Im(s)|`.

Suggested Lean statement:

```lean
lemma riemannZeta_norm_le_poly_vertical
    (A B T0 R : ℝ) :
    0 < A → 0 ≤ B → 0 < R → 2 ≤ T0 →
    (∀ z : ℂ, T0 ≤ |z.im| → z.re ∈ Set.Icc (-(R + 1)) (R + 2) →
      ‖riemannZeta z‖ ≤ A * |z.im| ^ B)
```

For implementation, do not quantify over arbitrary constants as above; prove an
existential package:

```lean
lemma exists_riemannZeta_poly_bound_vertical :
    ∃ A > 0, ∃ B ≥ 0, ∃ T0 ≥ 2,
      ∀ z : ℂ, T0 ≤ |z.im| → z.re ∈ Set.Icc (-1) 3 →
        ‖riemannZeta z‖ ≤ A * |z.im| ^ B
```

Mathlib status:
No direct zeta vertical-growth theorem found.  Mathlib has the functional
equation and differentiability/completed-zeta infrastructure, so this should be
proved from existing zeta continuation and Gamma estimates, but it is not an
immediate API call.

Difficulty:
High.  This is analytic-number-theory infrastructure rather than Lean algebra.
It is the main input needed before Borel-Caratheodory can produce
`O(log |t|)` logarithmic-derivative bounds.

### 3. Borel-Caratheodory Log-Derivative Bound

Mathematical statement:
For large `|t|`, away from zeros and the pole at `1`, the logarithmic
derivative of `ζ` in a fixed neighborhood of `1 + it` is `O(log |t|)`, after
accounting for any zero contribution inside the disk.

Suggested Lean statement:

```lean
lemma zeta_logDeriv_regular_part_bound
    (C T0 : ℝ) :
    0 < C → 2 ≤ T0 →
    ∀ s ρ : ℂ,
      T0 ≤ |s.im| →
      s.re ∈ Set.Icc 1 2 →
      riemannZeta ρ = 0 →
      ρ.im = s.im →
      ρ.re < 1 →
      0 < s.re - ρ.re →
      ((-deriv riemannZeta s / riemannZeta s).re
        + 1 / (s.re - ρ.re)) ≤ C * Real.log |s.im|
```

Mathlib status:
`Complex.borelCaratheodory` exists.  `MeromorphicOn.logDeriv` and
`logDeriv` infrastructure exist.  Missing is the zeta-specific specialization
that combines meromorphicity, zero extraction, polynomial growth, and the
translation from `logDeriv riemannZeta` to `deriv riemannZeta / riemannZeta`.

Difficulty:
High.  This is the core formalization of the classical Borel-Caratheodory
route.

### 4. Pole-Side Log-Derivative Bound

Mathematical statement:
Near the pole at `1`, on the real axis just to the right of `1`,
`-ζ'(σ)/ζ(σ) ≤ 1/(σ - 1) + O(1)`.

Suggested Lean statement:

```lean
lemma zeta_logDeriv_real_near_one_upper
    (C : ℝ) :
    0 ≤ C →
    ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
        ≤ 1 / (σ - 1) + C
```

Mathlib status:
`riemannZeta_residue_one` exists, and this file has `residue_bounds`, but no
ready logarithmic-derivative estimate was found.

Difficulty:
Medium.  This should follow from writing
`ζ(s) = 1/(s - 1) + h(s)` with `h` analytic and bounded on a small disk, or
equivalently `(s - 1)ζ(s)` nonzero and analytic near `1`.

### 5. Off-Zero Log-Derivative Bound at `σ + 2it`

Mathematical statement:
The third 3-4-1 point has no forced zero singularity and is bounded by
`O(log |t|)`.

Suggested Lean statement:

```lean
lemma zeta_logDeriv_two_t_bound
    (C T0 : ℝ) :
    0 < C → 2 ≤ T0 →
    ∀ σ t : ℝ, T0 ≤ |t| → 1 < σ → σ ≤ 2 →
      (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
        riemannZeta ((σ : ℂ) + 2 * I * t)).re
        ≤ C * Real.log |t|
```

Mathlib status:
Same as lemma 3: the complex-analysis tools exist, but the zeta-specific bound
does not.

Difficulty:
Medium to High.  Once lemma 3 is proved as a general regular-part bound, this
should be a specialization with no zero subtraction.  Proving it separately
would duplicate work.

### 6. Zero Contribution Bound

Mathematical statement:
If `ρ = β + it` is a zero with `β < 1` and `σ > 1`, then the point
`s = σ + it` contributes the negative term `-1/(σ - β)` to
`Re(-ζ'/ζ(s))`, up to the regular-part bound from lemma 3.

Suggested Lean statement:

```lean
lemma zeta_logDeriv_at_zero_height_upper
    (C T0 : ℝ) :
    0 < C → 2 ≤ T0 →
    ∀ σ t β : ℝ,
      T0 ≤ |t| → 1 < σ → σ ≤ 2 → β < 1 →
      riemannZeta (β + I * t) = 0 →
      (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re
        ≤ -1 / (σ - β) + C * Real.log |t|
```

Mathlib status:
No direct theorem found.  This should be a thin corollary of lemma 3 after
normalizing the zero as `ρ = β + I*t`.

Difficulty:
Medium if lemma 3 exists; High otherwise.

### 7. Algebraic 3-4-1 Contradiction

Mathematical statement:
Given the three upper bounds above, there is a constant `c > 0` such that no
zero can satisfy `β ≥ 1 - c / log |t|` for large `|t|`.

Suggested Lean statement:

```lean
lemma three_four_one_zero_free_high_height
    (C T0 : ℝ) (hC : 0 < C) (hT0 : 2 ≤ T0)
    (hreal :
      ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
        (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
          ≤ 1 / (σ - 1) + C)
    (hzero :
      ∀ σ t β : ℝ, T0 ≤ |t| → 1 < σ → σ ≤ 2 → β < 1 →
        riemannZeta (β + I * t) = 0 →
        (-deriv riemannZeta ((σ : ℂ) + I * t) /
          riemannZeta ((σ : ℂ) + I * t)).re
          ≤ -1 / (σ - β) + C * Real.log |t|)
    (htwo :
      ∀ σ t : ℝ, T0 ≤ |t| → 1 < σ → σ ≤ 2 →
        (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
          riemannZeta ((σ : ℂ) + 2 * I * t)).re
          ≤ C * Real.log |t|) :
    ∃ c > 0, ∀ s : ℂ, T0 ≤ |s.im| →
      s.re ≥ 1 - c / Real.log |s.im| →
      riemannZeta s ≠ 0
```

Mathlib status:
This is mostly algebra plus the already-proved
`log_deriv_zeta_nonneg_combination`.

Difficulty:
Medium-Low.  The constants are tedious but not conceptually hard.  This is a
good immediate Lean target once the three analytic estimates are assumed as
hypotheses.

### 8. Compact-to-All-Heights Patching

Mathematical statement:
If the quantitative region is proved for `|t| ≥ T0`, combine it with
`classical_zero_free_region_compact T0` to obtain the target for every
`|t| ≥ 2`.

Suggested Lean statement:

```lean
lemma compact_patch_classical_zero_free_region
    (T0 : ℝ) (hT0 : 2 ≤ T0)
    (hhigh :
      ∃ c > 0, ∀ s : ℂ, T0 ≤ |s.im| →
        s.re ≥ 1 - c / Real.log |s.im| → riemannZeta s ≠ 0) :
    ZeroFreeRegion.classical_zero_free_region
```

Mathlib status:
All ingredients appear available: `classical_zero_free_region_compact`, basic
real-log positivity for `2 ≤ |t|`, and elementary inequalities.

Difficulty:
Low.  This is the most immediately fillable non-analytic lemma.  It should be
proved only after introducing a high-height theorem or as a conditional lemma.

## Suggested Execution Order

1. Prove the low-risk conditional algebra lemmas:
   `three_four_one_zero_free_high_height` and
   `compact_patch_classical_zero_free_region`.
2. Add zeta meromorphic/divisor infrastructure around `riemannZeta`.
3. Prove the local pole logarithmic-derivative bound near `1`.
4. Prove a reusable Borel-Caratheodory/Jensen regular-part estimate for
   meromorphic functions with polynomial growth.
5. Specialize it to zeta to obtain the zero-height and `2t` estimates.
6. Only then convert `classical_zero_free_region` from `def ... : Prop` to a
   theorem, and verify with `lake env lean -R . ZeroFreeRegion.lean`.

## Immediately Fillable Lemmas

The best immediate Lean work that does not require new deep analysis is:

- a conditional high-height algebra lemma wrapping the 3-4-1 contradiction;
- the compact patch from high height to all `|t| ≥ 2`;
- small real-analysis helper lemmas such as
  `2 ≤ |t| → 0 < Real.log |t|`.

These would not prove `classical_zero_free_region` by themselves, but they
would make the remaining analytic assumptions explicit and reduce the final
assembly to named hypotheses.
