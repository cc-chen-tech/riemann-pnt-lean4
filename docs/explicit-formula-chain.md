# Explicit formula chain for von Mangoldt

This note audits the current target
`PrimeNumberTheorem.explicit_formula_von_mangoldt` and records a corrected
Lean-facing dependency chain.  It is scoped to the current checkout and does
not propose edits to any `.lean` file.

## Current statement

Current source:

```lean
def explicit_formula_von_mangoldt (x : Real) (_hx : x >= 2) : Prop :=
  chebyshevPsi x = x
    - sum' rho : {s : Complex // RiemannHypothesis.IsNontrivialZero s},
        (x : Complex) ^ (rho : Complex) / (rho : Complex)
    - (deriv riemannZeta 0) / riemannZeta 0
    - (1 / 2) * Real.log (1 - x^(-2 : Real))
```

After elaboration, Lean treats this as a complex equality by coercing
`chebyshevPsi x`, `x`, and the final real logarithm into `Complex`.

This is not a mathematically suitable final target.

1. The zero sum is an unordered `tsum` over all nontrivial zeros.  The classical
   sum is not an absolutely convergent unordered sum of `x^rho / rho`; it needs
   a symmetric principal value, a truncation parameter, or another explicit
   summation convention.
2. `chebyshevPsi` is the right-continuous step function.  The classical exact
   formula is for the midpoint convention
   `psi0(x) = (psi(x+) + psi(x-)) / 2`, equivalently
   `psi(x) - Lambda(n) / 2` when `x = n` is a prime power and `psi(x)` otherwise.
   Away from prime powers, `psi0 x = psi x`.
3. Zeros must be counted with multiplicity.  The current subtype
   `{s // IsNontrivialZero s}` counts each zero once and would silently assume
   all nontrivial zeros are simple.
4. The constant and trivial-zero terms are only meaningful after a summation
   convention has been fixed.  The final term
   `-1/2 * log (1 - x^-2)` is the infinite contribution of the trivial zeros;
   it should arise as a limit from finite trivial-zero residues or be stated as
   a separate convergent real series.
5. A bare equality for every `x >= 2` hides boundary issues at prime powers and
   at contour heights passing through zeros.

## Corrected target

The safest formal target is a finite, truncated contour formula first.  It avoids
the hardest convergence convention while still exposing all residues.

Suggested first Lean target:

```lean
def chebyshevPsi0 (x : Real) : Real :=
  chebyshevPsi x - jumpVonMangoldt x / 2

def explicitFormulaTruncatedTarget : Prop :=
  forall x >= 2, forall T >= 2, goodHeight T ->
    ((chebyshevPsi0 x : Complex)
      = x
        - finiteNontrivialZeroSum x T
        - finiteTrivialZeroSum x T
        - deriv riemannZeta 0 / riemannZeta 0
        + contourError x T)
```

Here:

* `jumpVonMangoldt x` is `vonMangoldt n` if `x = n` for some natural `n`, and
  `0` otherwise.
* `finiteNontrivialZeroSum x T` should sum over
  `rho` with `IsNontrivialZero rho` and `abs rho.im <= T`, weighted by the
  order/multiplicity of the zero of `riemannZeta` at `rho`.
* `finiteTrivialZeroSum x T` should sum over trivial zeros `-2 * (n + 1)` inside
  the shifted rectangle.  In the eventual limit this becomes
  `-1/2 * Real.log (1 - x^(-2))`.
* `contourError x T` is the remaining rectangle-boundary integral after moving
  the Perron line.
* `goodHeight T` excludes zeros and poles on the horizontal edges and on the
  shifted vertical edge.

After the truncated identity, there are two reasonable final statements.

### Principal value final form

For `x >= 2`:

```lean
Tendsto
  (fun T =>
    x
      - symmetricNontrivialZeroSum x T
      - deriv riemannZeta 0 / riemannZeta 0
      - (1 / 2) * Real.log (1 - x^(-2 : Real)))
  atTop
  (nhds (chebyshevPsi0 x : Complex))
```

This is the best final target if the project wants the classical exact formula.
The nontrivial zero sum must be symmetric in height and counted with
multiplicity.

### Non-jump final form

For `x >= 2` and `x` not a prime power:

```lean
Tendsto
  (fun T =>
    x
      - symmetricNontrivialZeroSum x T
      - deriv riemannZeta 0 / riemannZeta 0
      - (1 / 2) * Real.log (1 - x^(-2 : Real)))
  atTop
  (nhds (chebyshevPsi x : Complex))
```

This avoids introducing `psi0` into downstream PNT statements, but the theorem
must carry an explicit `notPrimePowerReal x` hypothesis.

## Minimal Lean dependency chain

### Arithmetic and Dirichlet series

Already available or mostly available:

1. `vonMangoldt_eq_mathlib` and `chebyshevPsi_eq_mathlib`.
2. `ArithmeticFunction.LSeriesSummable_vonMangoldt`.
3. `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`.
4. A complex version of
   `sum Lambda(n) * n^(-s) = -zeta'(s) / zeta(s)` on `1 < s.re`.

Needed:

1. A Perron kernel theorem for finite step sums:
   `(1 / (2*pi*I)) * integral_vertical (F s * x^s / s)` recovers the half-jump
   sum.
2. Specialization to `F s = LSeries Lambda s`.

### Analytic continuation and poles

Already available or partially available:

1. `riemannZeta_residue_one` for `(s - 1) * zeta s -> 1`.
2. `riemannZeta_pole_simple` in this project.
3. `riemannZeta_ne_zero_of_one_le_re`.
4. `riemannZeta_ne_zero_of_re_le_zero` outside trivial zeros.
5. `finite_nontrivial_zeros_bounded_height`.
6. `riemannZeta_not_frequently_zero_nhdsNE_of_ne_one`.

Needed:

1. Meromorphicity of `riemannZeta` on rectangles, with the pole at `1`
   (proved as `ZeroFreeRegion.meromorphicOn_riemannZeta_closedBall`, with
   simple-pole divisor value proved as
   `ZeroFreeRegion.divisor_riemannZeta_pole_one`).
2. Meromorphicity of
   `fun s => -deriv riemannZeta s / riemannZeta s * (x : Complex)^s / s`
   (the `logDeriv riemannZeta` factor is now meromorphic on closed balls).
3. Residue at `s = 1`: contribution `x`.
4. Residue at `s = 0`: contribution `-deriv riemannZeta 0 / riemannZeta 0`.
5. Residue at a nontrivial zero `rho`: contribution
   `- multiplicity(rho) * x^rho / rho`.
6. Residues at trivial zeros `-2, -4, ...`, plus the finite-to-infinite limit
   giving `-1/2 * log (1 - x^-2)`.

### Contour and residue theorem

Mathlib 4.29.1 has useful contour pieces:

1. `Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`.
2. `Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn`.
3. `Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable`.
4. `Complex.circleIntegral_div_sub_of_differentiable_on_off_countable`.
5. `circleIntegral.norm_integral_le_of_norm_le_const`.
6. `MeromorphicOn.divisor`, `meromorphicOrderAt`, and
   `meromorphicTrailingCoeffAt`.
7. `MeromorphicOn.extract_zeros_poles` and Jensen-formula infrastructure.

I did not find a directly callable general residue theorem of the form
"rectangle contour integral equals `2*pi*I` times a finite residue sum".
The project will likely need an intermediate local theorem:

```lean
rectangleIntegral_meromorphic_eq_residue_sum
```

for a meromorphic function with finite divisor support in the rectangle.  It can
be built from small-circle indentation, Cauchy integral formulas, and the
existing rectangle Cauchy-Goursat theorem, but it is not currently a one-line
Mathlib call.

### Boundary estimates and convergence

For the truncated identity:

1. Choose `T` avoiding zero ordinates using finite bounded-height zeros.
2. Bound the right Perron truncation error from summability of the von Mangoldt
   Dirichlet series and the standard Perron kernel estimate.
3. Bound horizontal and shifted-left vertical sides of the rectangle.

For the principal value final formula:

1. Zero counting bound such as `N(T) = O(T log T)`.
2. Bounds for `zeta'/zeta` away from zeros and on selected good heights.
3. Convergence of symmetric zero sums or a proof that the contour-error limit is
   zero along good heights.
4. Geometric convergence of the trivial-zero contribution to
   `-1/2 * log (1 - x^-2)`.

For a PNT proof, the truncated formula plus a zero-free region and boundary
estimates may be more useful than the full principal-value exact formula.

The current Lean API also names the converse route explicitly:
`PrimeNumberTheorem.ExplicitFormulaConversePowerTarget` and
`PrimeNumberTheorem.ExplicitFormulaTruncated.ExplicitFormulaTruncatedConverseRoute`
package the future step from a uniform truncated explicit formula plus an
oscillation argument to zero-free vertical-line consequences.  These are route
interfaces, not proved analytic theorems.

The `Re(s)=1/3` specialization is represented as a conditional Lean bridge.
`PrimeNumberTheorem.no_zeros_on_one_third_of_explicit_formula_converse_power`
takes:

1. the converse explicit-formula target
   `ExplicitFormulaConversePowerTarget (2 / 3)`, saying a `ψ(x)-x = O(x^θ)`
   bound with `θ < 2/3` excludes nontrivial zeros on or to the right of
   `Re(s)=2/3`; and
2. an actual `PsiPowerErrorBelowLine (2 / 3)` hypothesis;

and returns `NoZerosOnVerticalLine (1 / 3)`.  The proved part is the symmetry
and packaging: a zero on `Re(s)=1/3` reflects to one on `Re(s)=2/3`.  The
unproved analytic part remains the explicit-formula converse/oscillation
argument that would justify `ExplicitFormulaConversePowerTarget (2 / 3)`.

The same reflection step is now available without hard-coding `1/3`.
`PrimeNumberTheorem.no_zeros_on_reflected_line_of_explicit_formula_converse_power`
takes `0 < beta < 1`, an `ExplicitFormulaConversePowerTarget beta`, and a
`PsiPowerErrorBelowLine beta` hypothesis, and returns
`NoZerosOnVerticalLine (1 - beta)`.  This remains a formal bridge: the hard
analytic content is still the converse explicit-formula theorem that would
produce `ExplicitFormulaConversePowerTarget beta`.

The public facade also exposes
`RiemannPNT.API.no_zeros_on_one_third_of_truncated_explicit_formula_converse_route`,
which composes the truncated route
`ExplicitFormulaTruncatedConverseRoute (2 / 3)`, a future proof of the
truncated explicit formula for all admissible `T,x`, and the `ψ` power-saving
hypothesis into the same `NoZerosOnVerticalLine (1 / 3)` conclusion.
The generalized facade
`RiemannPNT.API.no_zeros_on_reflected_line_of_truncated_explicit_formula_converse_route`
does the same composition for arbitrary `0 < beta < 1`, yielding
`NoZerosOnVerticalLine (1 - beta)`.

## Recommended next formalization order

1. Add definitions only: `jumpVonMangoldt`, `chebyshevPsi0`,
   `zeroMultiplicity`, finite zero sums, finite trivial-zero sums, and
   `goodHeight`.
2. Prove finite bounded-height support lemmas for the zero sums from
   `finite_nontrivial_zeros_bounded_height`.
3. Formalize a generic Perron half-jump theorem for finitely supported or
   absolutely summable Dirichlet series.
4. Formalize a rectangle meromorphic residue theorem as a reusable project
   lemma, since Mathlib currently supplies the analytic pieces but not the exact
   residue-sum wrapper needed here.
5. Prove the truncated explicit formula with an explicit contour-error term.
6. Only then state the principal-value or non-jump final formula as a limit.
