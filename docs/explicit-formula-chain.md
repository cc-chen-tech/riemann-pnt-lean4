# Explicit formula chain for von Mangoldt

This note audits the current target
`PrimeNumberTheorem.explicit_formula_von_mangoldt` and records a corrected
Lean-facing dependency chain.  It is scoped to the current checkout.

## Current statement

Current source is a multiplicity-aware symmetric-height limit:

```lean
def finiteNontrivialZeroSumWithMultiplicity (x T : Real) : Complex :=
  ∑ rho in nontrivialZerosFinset T,
    analyticOrderNatAt riemannZeta rho * x^rho / rho

def explicitFormulaApproxWithMultiplicity (x T : Real) : Complex :=
  x
    - finiteNontrivialZeroSumWithMultiplicity x T
    - (deriv riemannZeta 0) / riemannZeta 0
    - (1 / 2) * Real.log (1 - x^(-2 : Real))

def explicit_formula_von_mangoldt (x : Real) (_hx : x >= 2) : Prop :=
  Tendsto (fun T => explicitFormulaApproxWithMultiplicity x T) atTop
    (nhds (chebyshevPsi0 x : Complex))
```

This corrects the former unordered `tsum`, right-continuous `psi`, and
distinct-zero-only problems.  The retained `explicitFormulaApprox` and
`explicit_formula_von_mangoldt_unweighted` declarations are compatibility
infrastructure and are not the tracked mathematical target.

The weighted target has direct theorem-level unfolding and error interfaces:
`explicit_formula_von_mangoldt_iff`,
`explicit_formula_von_mangoldt_of_eventually_eq`,
`explicit_formula_von_mangoldt_of_eventually_exact`, and
`explicit_formula_von_mangoldt_iff_error_tendsto_zero`.  The older, broader
finite-tail helper family is explicitly suffixed `_unweighted_`.

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
        - finiteNontrivialZeroSumWithMultiplicity x T
        - finiteTrivialZeroSum x T
        - deriv riemannZeta 0 / riemannZeta 0
        + contourError x T)
```

Here:

* `jumpVonMangoldt x` is `vonMangoldt n` if `x = n` for some natural `n`, and
  `0` otherwise.
* `finiteNontrivialZeroSumWithMultiplicity x T` sums over
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
5. The absolutely convergent second-order Perron formula
   `PrimeNumberTheorem.secondOrderPerron_eq_max`, its finite-sum form, and the
   von Mangoldt specialization
   `PrimeNumberTheorem.integral_vonMangoldt_secondOrderPerron_eq`.  The last
   theorem recovers the first Riesz mean
   `sum_{n <= x} Lambda(n) * log (x / n)` from the vertical `1 / s^2` kernel.
6. The finite-difference bridge back to `chebyshevPsi` is proved as
   `PrimeNumberTheorem.chebyshevPsi_le_rieszDifference_div_log_le`: for
   `0 < x < y`, the normalized Riesz-mean difference lies between `psi x`
   and `psi y`.  Thus the second-order Perron output is no longer isolated
   from the unsmoothed arithmetic function.
7. `PrimeNumberTheorem.norm_truncated_secondOrderPerron_sub_max_le` proves the
   finite-height error for the second-order kernel: truncating to `[-W,W]`
   costs at most `exp (c*u) / (2*pi^2*W)`.  This is an unconditional theorem,
   not a truncation target or route interface.
8. `PrimeNumberTheorem.norm_truncated_vonMangoldt_secondOrderPerron_sub_smoothedPsi_le`
   sums that error over the actual von Mangoldt coefficients and obtains the
   explicit finite Dirichlet-polynomial remainder
   `sum_{n <= x} Lambda(n) * (x/n)^c / (2*pi^2*W)`.
9. `PrimeNumberTheorem.norm_truncated_vonMangoldt_secondOrderPerron_sub_smoothedPsi_le_explicit`
   eliminates the coefficient sum using Chebyshev's bound, giving
   `x^c * (log 4 + 4) * x / (2*pi^2*W)`.  The finite-height arithmetic starting
   integral therefore has a closed-form unconditional error bound.
10. `PrimeNumberTheorem.intervalIntegral_vonMangoldt_LSeries_eq_tsum` proves
    the uniform absolute convergence needed to exchange the full von Mangoldt
    `tsum` with the finite vertical integral for every `c > 1`.  Its companion
    `intervalIntegral_neg_logDeriv_riemannZeta_eq_vonMangoldt_tsum` rewrites
    that complete right-line integrand as `-zeta'/zeta`.
11. `PrimeNumberTheorem.norm_truncated_neg_logDeriv_riemannZeta_sub_smoothedPsi_le`
    applies the `1/W` kernel error to every term of the full Dirichlet series,
    including the `n > x` tail, and proves an unconditional finite-height
    right-line formula for the Riesz mean with an explicit summable remainder.
    This closes the second-order Perron/L-series starting-line gap; it does not
    yet move the line across zeta zeros or prove the classical first-order
    half-jump formula.
12. `PrimeNumberTheorem.ExplicitFormulaResidues.exists_norm_residue_sum_sub_contourRemainder_sub_smoothedPsi_le`
    now performs that finite-height contour shift on an arbitrary tall
    rectangle contained in `Re(s) > 0`.  It combines the complete right-line
    Perron formula with a finite zeta-pole residue sum and the normalized
    bottom, top, and left edge integrals.  The resulting unconditional theorem
    bounds the difference from the first Riesz mean by the same explicit
    summable `1/W` remainder.  Its residue witness is now accompanied by the
    proved value formula: `x` at `1` and
    `-multiplicity(rho) * x^rho / rho^2` at every nontrivial zero in the
    rectangle.
13. `PrimeNumberTheorem.ExplicitFormulaResidues.exists_safe_norm_residue_sum_sub_contourRemainder_sub_smoothedPsi_le`
    removes the pole-free-boundary hypothesis.  Above every prescribed Perron
    height it chooses a `goodHeight`, then uses bounded-height zero finiteness
    to choose a left edge `a in (0,1/2)` distinct from every enclosed zero's
    real part.  Thus arbitrarily high safe long rectangles, with fixed right
    edge `c > 1`, now feed the truncated formula unconditionally.  The main
    remaining analytic work is to estimate the three shifted edges.
14. `PrimeNumberTheorem.ExplicitFormulaResidues.norm_horizontal_right_secondOrderContour_difference_le`
    proves an actual, unconditional estimate for the portions of both
    horizontal edges with `1+epsilon <= Re(s) <= c`.  Absolute convergence of
    the von Mangoldt Dirichlet series gives a height-independent majorant for
    `|zeta'/zeta|`, and the second-order kernel then makes the two-edge
    difference `O(x^c * T^-2)`.  No future high-height zeta bound is assumed.
    The unresolved contour pieces are now the horizontal segments
    `a <= Re(s) <= 1+epsilon` and the left vertical edge `Re(s)=a`, where the
    Dirichlet series is not absolutely convergent.
15. `PrimeNumberTheorem.tendsto_truncated_firstOrderPerronKernel_atTop` and
    `PrimeNumberTheorem.tendsto_truncated_finset_firstOrderPerron_atTop`
    prove the conditionally convergent ordinary Perron kernel and its finite
    step-sum form.  Away from the jump, integration by parts reduces the
    first-order kernel to the already proved second-order kernel and gives an
    explicit `O(exp(c*u) / (|u|*W))` truncation error.  At the jump, the
    symmetric integral is computed as `atan(2*pi*W/c)/pi`, whose limit is
    `1/2`.  Thus the half-jump theorem for finite sums is no longer an input.
16. `PrimeNumberTheorem.tendsto_truncated_neg_logDeriv_firstOrderPerron_atTop`
    closes the full ordinary Perron starting-line formula.  For every `x > 0`
    and `c > 1`, the normalized symmetric contour integral
    `(2*pi*i)^(-1) integral x^s * (-zeta'(s)/zeta(s)) / s ds` on
    `Re(s)=c` tends to `psi0(x)`.  In Lean this is parameterized by
    `s = c + 2*pi*i*w` and integrated with respect to `dw`, so the
    normalization is already included.
    The proof exchanges the finite-height integral with the full von Mangoldt
    series, proves a summable Tannery majorant for the conditionally convergent
    kernel, and includes the half weight at an integral jump.  This is the
    actual first-order L-series specialization, not a finite-sum wrapper.
17. `PrimeNumberTheorem.ExplicitFormulaResidues.exists_scaledRightIntegral_eq_residue_sum_sub_firstOrderContourRemainder`
    proves the exact finite-height first-order contour shift with a fixed
    Perron right edge.  The normalized right-line integral equals the finite
    residue sum, with the residues at `0`, `1`, and every enclosed zeta zero
    identified explicitly, minus the normalized bottom, top, and left edges.
    The theorem includes both directions of the pole-set specification: every
    listed pole is a candidate singularity, and every candidate singularity
    in the closed rectangle occurs in the finite pole set.
    Its `..._of_goodHeight` specialization fixes the left edge at `Re(s)=-1`
    and proves that every `goodHeight (2*pi*W)` gives a pole-free boundary for
    arbitrary fixed `c>1`.  Thus the starting-line Perron theorem and the
    finite rectangle residue theorem are now connected in one Lean formula.
18. `PrimeNumberTheorem.ExplicitFormulaResidues.norm_horizontal_right_firstOrderContour_difference_le`
    proves an explicit `O(1/T)` bound for the combined top and bottom portions
    with `1+epsilon <= Re(s) <= c`.  Its companion
    `tendsto_horizontal_right_firstOrderContour_difference_atTop` proves that
    this contribution tends to zero.  This is the first-order analogue of the
    previously proved second-order right-tail estimate.  The unresolved
    horizontal interval is now `-1 <= Re(s) <= 1+epsilon`, where absolute
    convergence of the von Mangoldt Dirichlet series is unavailable.
19. `PrimeNumberTheorem.ExplicitFormulaAux.tendsto_finiteTrivialZeroSum_residues`
    proves that the finite simple-residue sums over
    `-2,-4,...,-2N` converge to the classical term
    `-1/2 * log (1 - x^-2)` for `x>1`.  The proof is connected to the
    repository's actual `finiteTrivialZeroSum (2N)`, not merely a separate
    sequence index.  The new theorem
    `ExplicitFormulaResidues.analyticOrderNatAt_riemannZeta_neg_even` proves
    that every trivial zeta zero has analytic order exactly one, using the
    completed-zeta functional equation and the simple zeros of reciprocal
    Gamma.  Consequently
    `tendsto_finiteTrivialZeroSum_multiplicity_residues` proves convergence of
    the corresponding multiplicity-aware trivial-zero truncations to the same
    logarithmic term.
20. `ExplicitFormulaResidues.exists_movingLeft_scaledRightIntegral_eq_trivial_add_remaining_sub_remainder`
    constructs, for every `N` and every good height, the rectangle with left
    edge `-(2N+1)` and proves an exact Perron contour identity in which the
    abstract pole sum has already been split into the explicit residues at
    `-2,-4,...,-2N` and the remaining poles.  The underlying theorem
    `trivialZeroPart_eq_finiteTrivialZeroSum` proves equality of the two
    finsets, not merely one-sided containment.
21. `ExplicitFormulaResidues.exists_jointCofinal_movingLeft_firstOrderContours`
    chooses one sequence with `W_n -> infinity`, strictly increasing `W_n`,
    `goodHeight (2*pi*W_n)`, and left edge `-(2n+1)`.  Every member satisfies
    the concrete truncated formula from item 22, while its trivial-zero residue
    sum converges to `-1/2 * log (1 - x^-2)`.  This closes the joint cofinal
    selection problem, but does not prove that the nontrivial-zero sum or the
    moving-left contour remainder converges.
22. `ExplicitFormulaResidues.movingLeft_scaledRightIntegral_eq_truncatedExplicitFormula`
    eliminates the abstract contour pole finset entirely.  At every good
    height it gives the finite formula with the pole-at-one term `x`, the
    kernel-pole term `-zeta'(0)/zeta(0)`, the first `N` trivial-zero residues,
    and the multiplicity-weighted sum over
    `nontrivialZerosFinset (2*pi*W)`, minus the three-edge contour remainder.
    The exact identification of the remaining poles is proved by
    `remainingPolePart_eq_explicit`.
23. `ExplicitFormulaResidues.exists_jointCofinal_nontrivialZeroSum_sub_remainder_tendsto`
    proves unconditionally that, along a joint cofinal sequence, the
    multiplicity-weighted nontrivial-zero sum minus the moving contour
    remainder converges to the exact value forced by `psi0`, the pole terms,
    and the trivial-zero logarithmic correction.  If the remainder tends to
    zero, the nontrivial-zero sum therefore has the corresponding limit along
    this cofinal sequence.  Passing from that sequence to arbitrary truncation
    heights remains necessary for the full principal-value target.
24. `LeftHorizontalEdge` proves the logarithmic-derivative functional-equation
    identity and uses it to split every nonreal far-left horizontal point into
    an Euler-product term and an explicit Gamma/digamma term.  The Euler term
    is bounded by `C*x^sigma/|T|`; after integration from an arbitrary moving
    left endpoint to `-epsilon`, both the upper and lower Euler contributions
    tend to zero.  Consequently the full far-left horizontal integrals differ
    from the displayed Gamma-factor integrals by a quantity tending to zero.
25. The same module proves the uniform complex-tangent bound
    `norm (tan z) <= 2` for `1 <= |Im z|`.  It uses this to show that both the
    `log(2*pi)` and tangent parts of the Gamma-factor integral vanish on the
    moving upper and lower far-left edges.  The full far-left horizontal
    integrals are therefore now proved asymptotic to the pure digamma
    integrals `digamma(s) * x^s / s`.
26. `LeftHorizontalEdge` now also derives the logarithmic derivative of
    Euler's Gamma reflection formula
    `digamma(s) = digamma(1-s) - pi*cot(pi*s)` off the real axis.  It proves
    `norm (cot z) <= 2` for `1 <= |Im z|` and shows that the resulting cotangent
    correction tends to zero on both moving far-left horizontal edges,
    uniformly in the left endpoint.  Thus the full far-left integrals are
    asymptotic to the right-half-plane terms
    `digamma(1-s) * x^s / s`.  This is a genuine reduction, not yet a proof
    that those remaining digamma integrals vanish.
27. `DigammaBounds` proves Gauss' convergent series for complex digamma on
    `Re(z)>0` from the canonical product for `1/Gamma`, including the required
    locally uniform product convergence and logarithmic-derivative passage.
    It obtains the quantitative bound
    `norm (digamma z) <= norm gamma + 3 + log (norm z + 1)` for `Re(z)>=1`.
    `LeftHorizontalEdge` integrates this bound and proves that both complete
    moving far-left horizontal contour integrals tend to zero, uniformly in
    every left endpoint satisfying `a(T)<=-epsilon`.  Thus no digamma or other
    Gamma-factor remainder remains on these two far-left horizontal pieces.
28. `LeftVerticalEdge` treats the complete moving left edge.  It first proves
    the uniform bound `norm (cot z) <= 1` on the
    entire vertical line obtained from `Re(s)=-(2N+1)` after halving and
    multiplying by `pi`; unlike the horizontal high-imaginary bound, this
    includes height zero.  It also proves
    `logDeriv Gammaℝ(s) = -log(pi)/2 + digamma(s/2)/2` whenever the ordinary
    Gamma factor is regular.  This is the nonsingular completed-factor
    decomposition needed at negative odd real points.  Finally,
    `exists_linearlyControlled_goodHeight_gt_one` strengthens the cofinal
    height construction by retaining `n+K < T_n < n+K+1`.  Using the completed
    zeta functional equation, it then proves a nonsingular logarithmic-
    derivative identity on `Re(s)=-(2N+1)`, reflects both digamma factors to
    `Re>=1`, and obtains the finite-height bound
    `O(T * x^(-(2N+1)) * (1 + log(2N+T+4)))`.  Consequently
    `tendsto_integral_explicitFormulaIntegrand_odd_vertical_atTop` proves that
    the complete left edge tends to zero whenever the height grows at most
    linearly.  The joint contour theorem now uses exactly such a sequence and
    exposes this zero limit in its conclusion.
29. `ExplicitFormulaResidues.exists_cofinal_nontrivialZeroSum_tendsto` selects
    an even subsequence of the logarithmically separated central heights so the
    heights are strictly increasing while remaining linearly controlled.  At
    every selected height it proves the exact finite moving-rectangle identity
    with left edge `-(4n+1)`.  It combines the far-left upper and lower limits,
    both central horizontal limits, and the moving left-vertical limit to prove
    that the complete `firstOrderContourRemainder` tends to zero.  Consequently
    the multiplicity-weighted nontrivial-zero sum itself converges to the exact
    `psi0` explicit-formula value along this cofinal sequence.  This closes the
    global contour-limit assembly.  `explicit_formula_von_mangoldt_proved`
    now promotes it to arbitrary symmetric real truncation heights.

Completed after the fixed-right-edge contour shift:

1. Control the multiplicity-weighted zero contributions between consecutive
   selected good heights.
   `NontrivialZeroMultiplicity.lean` now supplies multiplicity symmetry, a
   one-zero `m(rho) * x / T` bound, and finite multiplicity-mass control by the
   zeta divisor on a containing disk.  `QuantitativeGoodHeight.lean` upgrades
   this to total local multiplicity `O(log A)`, a fixed-window weighted bound
   `O_x(log A/A)`, and convergence of that window contribution to zero.
2. `norm_explicitFormulaApproxWithMultiplicity_sub_le_two_localWindows` covers
   each gap of length at most three by two fixed windows.  The floor index
   `floor((U-5)/2)` selects a cofinal height below every sufficiently large
   `U`, and `explicit_formula_von_mangoldt_proved` combines this with the
   cofinal approximation limit to prove the full real-height `Tendsto`.

### Analytic continuation and poles

Already available or partially available:

1. `riemannZeta_residue_one` for `(s - 1) * zeta s -> 1`.
2. `riemannZeta_pole_simple` in this project.
3. `riemannZeta_ne_zero_of_one_le_re`.
4. `riemannZeta_ne_zero_of_re_le_zero` outside trivial zeros.
5. `finite_nontrivial_zeros_bounded_height`.
6. `riemannZeta_not_frequently_zero_nhdsNE_of_ne_one`.

Current status:

1. Meromorphicity of `riemannZeta` on rectangles, with the pole at `1`
   (proved as `ZeroFreeRegion.meromorphicOn_riemannZeta_closedBall`, with
   simple-pole divisor value proved as
   `ZeroFreeRegion.divisor_riemannZeta_pole_one`).
2. Meromorphicity of
   `fun s => -deriv riemannZeta s / riemannZeta s * (x : Complex)^s / s`
   is proved globally as
   `PrimeNumberTheorem.ExplicitFormulaResidues.meromorphic_explicitFormulaIntegrand`.
   The theorem
   `exists_finite_explicitFormulaIntegrand_pole_candidates` further proves
   that on every compact set this concrete integrand is analytic outside a
   finite set consisting of the zeta-divisor support together with `0`.
3. Proved in
   `PrimeNumberTheorem.ExplicitFormulaResidues.tendsto_sub_one_mul_explicitFormulaIntegrand_one`:
   residue at `s = 1` is `x`.
4. Proved in
   `PrimeNumberTheorem.ExplicitFormulaResidues.tendsto_mul_explicitFormulaIntegrand_zero`:
   residue at `s = 0` is `-deriv riemannZeta 0 / riemannZeta 0`.
5. Proved with the actual `analyticOrderNatAt` multiplicity in
   `PrimeNumberTheorem.ExplicitFormulaResidues.tendsto_sub_mul_explicitFormulaIntegrand_of_nontrivialZero`:
   residue at a nontrivial zero `rho` is
   `-multiplicity(rho) * x^rho / rho`.
6. The corresponding local residue formula at every trivial zero is proved by
   `PrimeNumberTheorem.ExplicitFormulaResidues.tendsto_sub_mul_explicitFormulaIntegrand_trivialZero`.
   The same module proves analytic-germ principal-part subtraction at `0`,
   `1`, and every finite-order zeta zero via the
   `exists_analyticAt_eventuallyEq_explicitFormulaIntegrand_sub_principalPart...`
   theorem family.
   `exists_finite_explicitFormulaIntegrand_analytic_regularized_remainder`
   now assembles all compact-set principal parts into one normalized remainder
   analytic on the whole compact set.  The theorem
   `exists_rectangleBoundaryIntegral_explicitFormulaIntegrand_eq_residue_sum`
   feeds this remainder into the rectangle identity and proves the concrete
   finite residue formula under an explicit pole-free-boundary hypothesis.
   `exists_strictMono_tendsto_rectangleResidueContours` now constructs the
   required cofinal contour family from `goodHeight`, using squares with real
   sides `-1` and `2T-1`.  The finite-to-infinite residue limit giving
   `-1/2 * log (1 - x^-2)` is now proved by
   `tendsto_finiteTrivialZeroSum_multiplicity_residues`, including the analytic
   multiplicities used by the contour residue formula.  The pole-finset split
   is now included in the moving-left exact identity; the moving-left-edge
   limit is not yet proved.

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

The project now proves
`MathlibAux.circleIntegral_eq_finite_simple_pole_residue_sum`: a holomorphic
remainder plus finitely many principal parts `residue p / (z-p)` integrates
around a containing circle to `2*pi*I` times the finite residue sum.  This is
the genuine local finite-residue step.

The rectangle development also proves the local square kernels
`MathlibAux.rectangleBoundaryIntegral_inv_zero` and
`MathlibAux.rectangleBoundaryIntegral_sub_inv_center`: for every `R > 0`, the
positively oriented square centered at `0`, or at an arbitrary `c`, integrates
`1 / z` or `1 / (z-c)` to `2*pi*I`.  The arbitrary-center theorem is the local
calculation needed to excise a small square around each actual pole.

The project now also proves
`MathlibAux.rectangleBoundaryIntegral_sub_inv_of_mem_openRectangle` and
`MathlibAux.rectangleBoundaryIntegral_eq_finite_simple_pole_residue_sum`.
The first deforms an outer square containing an arbitrary simple pole to a
small square centered at that pole.  The second sums this over a finite pole
set.  The deformation uses four pole-free rectangles and the proved internal
edge-cancellation lemma
`MathlibAux.boundaryRectIntegral_eq_inner_of_four_rectangles`.

Finally,
`MathlibAux.rectangleBoundaryIntegral_eq_zero_of_differentiableOn` and
`MathlibAux.rectangleBoundaryIntegral_eq_finite_simple_pole_residue_sum_of_differentiableOn`
prove the version with an arbitrary holomorphic remainder on the closed
rectangle.  Thus the rectangle integral is complete once an integrand has
actually been decomposed into that remainder and finitely many simple
principal parts.

`MathlibAux.BoundaryRectResidue` removes the square-shape restriction.  It
proves `boundaryRectIntegral_sub_inv_of_mem` and
`boundaryRectIntegral_eq_finite_simple_pole_residue_sum_of_differentiableOn`
for arbitrary ordered horizontal and vertical endpoints.  This matters for
Perron inversion: the right edge `Re(s)=c>1` can now remain fixed while the
height grows, instead of being forced to grow with a square's half-side.
`PrimeNumberTheorem.SecondOrderExplicitFormula` applies this theorem after
dividing the first-order integrand by `s`; keeping the left edge at `a>0`
avoids the resulting double pole at `s=0`.

There is still no directly callable theorem for an arbitrary meromorphic
function of the form
"rectangle contour integral equals `2*pi*I` times a finite residue sum".
The remaining intermediate theorem is:

```lean
rectangleIntegral_meromorphic_eq_residue_sum
```

for a general meromorphic function with finite divisor support in the
rectangle.  Finite simple principal parts and the rectangle deformation are
now proved, including addition of a supplied holomorphic remainder.  For the
explicit-formula integrand, global meromorphicity, finite compact-set pole
candidates, and a single analytic normalized remainder after subtracting all
their principal parts are now proved.  The concrete rectangle identity is also
proved by
`PrimeNumberTheorem.ExplicitFormulaResidues.exists_rectangleBoundaryIntegral_explicitFormulaIntegrand_eq_residue_sum`
when all candidate poles lie in the open rectangle.  The remaining contour
sequence is now supplied by
`exists_strictMono_tendsto_rectangleResidueContours`: good heights `T > 1`
give squares `[-1,2T-1] x [-T,T]` whose vertical sides are zero-free and whose
horizontal sides avoid nontrivial zeros.  The fully general abstract theorem
would also need to treat higher-order poles.

The current `rectangleIntegral_meromorphic_eq_residue_sum` declaration remains
an existential certificate interface, not a theorem following from its radius
hypothesis.  The project also proves the constant-function sanity layer:
`MathlibAux.rectangleBoundaryIntegral_const`,
`MathlibAux.rectangleIntegral_const`, and
`MathlibAux.rectangleIntegral_const_zero` show that constant holomorphic
functions have zero rectangle boundary integral and satisfy the residue-sum
predicate using the empty pole set.  This is useful API validation only; it is
not the meromorphic rectangle residue theorem and does not supply Perron's
formula.

### Boundary estimates and convergence

For the truncated identity:

1. Completed: `ExplicitFormulaAux.exists_goodHeight_Ioo` chooses `T` in every
   unit interval while avoiding all nontrivial-zero ordinates, using finite
   bounded-height zero support;
   `ExplicitFormulaAux.exists_goodHeight_Icc_quantitatively_separated`
   strengthens this to a height whose distance from every nontrivial-zero
   absolute ordinate is at least `1/(4(N+1))`, where `N` counts distinct
   absolute zero ordinates in a fixed-width local window;
   for `A >= 4`,
   `ExplicitFormulaAux.exists_card_localZeroHeights_le_log_bound` now combines
   functional-equation symmetry, two fixed Jensen disks, and the divisor-mass
   estimate to prove `N <= B(1+log(A+6))`; the combined theorem
   `ExplicitFormulaAux.exists_goodHeight_Icc_logarithmically_separated` selects
   `T in [A,A+1]` at distance at least
   `1/(4(B(1+log(A+6))+1))` from every absolute zero ordinate;
   `ExplicitFormulaAux.exists_strictMono_goodHeight_tendsto` upgrades this to
   a strictly increasing good-height sequence tending to `+∞`;
   `ExplicitFormulaResidues.exists_strictMono_tendsto_rectangleResidueContours`
   converts a cofinal tail into concrete pole-free square residue contours.
   The first-order theorem
   `exists_scaledRightIntegral_eq_residue_sum_sub_firstOrderContourRemainder_of_goodHeight`
   now gives the corresponding safe rectangle with fixed right edge `c>1`
   and fixed left edge `-1`, so it is directly compatible with Perron.
2. Completed: the ordinary first-order right-line Perron integral converges to
   `psi0` by
   `tendsto_truncated_neg_logDeriv_firstOrderPerron_atTop`.  This is a limit
   theorem; it does not claim a closed-form uniform truncation rate for the
   full conditionally convergent series.
3. Completed on the far-left pieces and moving left edge: the linearly
   controlled good-height construction makes the horizontal pieces from
   `-(2N+1)` to `-delta` vanish at both heights, and the complete moving left
   vertical edge tends to zero.
4. Completed on the fixed right and inner zero-free segments: the portions
   `1+epsilon <= Re(s) <= c` vanish by the first-order `O(1/T)` bound, with
   interval integrability proved explicitly.  In addition,
   `ZeroFreeRegion.exists_norm_logDeriv_riemannZeta_le_log_sq_on_inner_zeroFreeRegion`
   proves a full-norm `O((log |t|)^2)` estimate on
   `1-c/(2log|t|) <= Re(s) <= 2`.  The signed theorem
   `ExplicitFormulaResidues.exists_tendsto_horizontal_inner_explicitFormulaIntegrand_signed_zero`
   then proves that this segment tends to zero on both horizontal sides.
5. Completed on the central horizontal band:
   `ZeroFreeRegion.exists_shifted_disk_regularized_logDeriv_riemannZeta_log_bound`
   moves the Jensen/Borel disk to `3/2+it` and controls the regularized
   logarithmic derivative down to `Re(s)=1/2`.  Combining its shifted divisor
   mass with logarithmic good-height separation gives
   `exists_goodHeight_Icc_norm_logDeriv_central_band_le_log_sq`, a full-norm
   `O(log^2 A)` bound on `-1 <= Re(s) <= 2`, simultaneously at heights `+T`
   and `-T`.  The resulting explicit contour bound is
   `O(log^2 A / T)`, and
   `exists_tendsto_horizontal_central_explicitFormulaIntegrand_both_zero`
   proves that both complete central horizontal integrals vanish along a
   cofinal good-height sequence.
6. Completed global assembly:
   `exists_cofinal_nontrivialZeroSum_tendsto` combines the finite rectangle
   identity with the far-left, moving-left, and central boundary limits.  It
   proves the complete remainder tends to zero and identifies the cofinal
   multiplicity-weighted zero-sum limit.  The all-height interpolation module
   now promotes this to arbitrary-height principal-value truncation.

For the principal value final formula:

1. Zero counting bound such as `N(T) = O(T log T)`.
2. Bounds for `zeta'/zeta` away from zeros and on selected good heights.
3. The fixed-window zero-sum contribution tends to zero.  Two windows cover
   every selected-height gap, and the floor-index argument now proves the full
   principal-value formula from the cofinal contour limit.
4. The final target is already aligned with analytic multiplicities.  The old
   unweighted approximation remains explicitly named legacy infrastructure.

For a PNT proof, the truncated formula plus a zero-free region and boundary
estimates may be more useful than the full principal-value exact formula.

The finite-zero increment layer now has a matching symmetry API.  The public
theorems `RiemannPNT.API.one_sub_mem_nontrivialZerosFinset_sdiff`,
`RiemannPNT.API.sum_nontrivialZerosFinset_sdiff_pair_re`, and
`RiemannPNT.API.nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_pair_contribution_nonnegative`
show that newly included zeros between two truncation heights are closed under
`rho -> 1 - rho`, can be reindexed by that symmetry, and inherit the
pair-positivity nonnegativity statement.  This is still finite combinatorics;
the analytic zero-density and contour estimates remain separate.

The current Lean API keeps the finite truncated-explicit-formula route explicit:
`PrimeNumberTheorem.ExplicitFormulaTruncated.ExplicitFormulaTruncatedConverseRoute`
packages the future step from one globally uniform truncated bound for all
`T ≥ 2` and `x ≥ 2`, plus an oscillation argument, to zero-free vertical-line
consequences.  The older
Prop shape `PrimeNumberTheorem.ExplicitFormulaConversePowerTarget` is no longer
a missing route interface: `ZeroFreeRegion.explicitFormulaConversePowerTarget_of_mellin`
proves it theorem-level from the Mellin/Landau converse.

The `Re(s)=1/3` specialization is represented as a conditional Lean bridge.
`PrimeNumberTheorem.no_zeros_on_one_third_of_explicit_formula_converse_power`
takes:

1. the theorem-level `ExplicitFormulaConversePowerTarget (2 / 3)` bridge,
   supplied by the Mellin/Landau converse, saying a `ψ(x)-x = O(x^θ)` bound
   with `θ < 2/3` excludes nontrivial zeros on or to the right of `Re(s)=2/3`;
   and
2. an actual `PsiPowerErrorBelowLine (2 / 3)` hypothesis;

and returns `NoZerosOnVerticalLine (1 / 3)`.  The proved part is now both the
Mellin/Landau converse and the symmetry packaging: a zero on `Re(s)=1/3`
reflects to one on `Re(s)=2/3`.  The unproved analytic part is obtaining a
strong enough `ψ` power-saving estimate, not the abstract zero-exclusion bridge.

The same reflection step is now available without hard-coding `1/3`.
`PrimeNumberTheorem.no_zeros_on_reflected_line_of_explicit_formula_converse_power`
takes `0 < beta < 1`, the now-proved `ExplicitFormulaConversePowerTarget beta`,
and a `PsiPowerErrorBelowLine beta` hypothesis, and returns
`NoZerosOnVerticalLine (1 - beta)`.  The hard analytic content is now upstream:
prove the `PsiPowerErrorBelowLine beta` estimate itself.

The current mainline now also contains a genuine obstruction lemma behind that
converse route.  The theorem
`PrimeNumberTheorem.not_psi_power_error_bound_sub_delta_of_frequently_negative_single_zero_complex_psi_decomposition`
says that if a selected zero contribution `-x^rho/rho` dominates the retained
tail on arbitrarily large good points, then
`PsiPowerErrorBound (rho.re - delta)` is impossible.  This is not yet a full
explicit-formula converse: the missing analytic step is still to produce those
good points and the decomposition from Perron/contour estimates.

The Mellin/Landau alternative to the oscillation argument now has both sides
of its overlap proved rather than merely named as route targets.
`PrimeNumberTheorem.mellinConvergent_psiErrorAboveOneComplex_neg_of_power_error`
and
`PrimeNumberTheorem.differentiableAt_mellin_psiErrorAboveOneComplex_neg_of_power_error`
show that `PsiPowerErrorBound theta` makes the Mellin transform of the cutoff
complex `psi(x)-x` error converge and become holomorphic throughout
`Re(s) > theta` after `z ↦ -z`.  The theorem
`PrimeNumberTheorem.mul_mellin_psiErrorAboveOneComplex_neg_eq_neg_logDeriv_sub_pole`
then proves on `Re(s) > 1` the exact overlap identity

`s * M(s) = -zeta'(s)/zeta(s) - s/(s-1)`.

The named model `PrimeNumberTheorem.regularizedNegLogDerivModel` packages the
left side.  Under `PsiPowerErrorBound theta`,
`PrimeNumberTheorem.differentiableOn_regularizedNegLogDerivModel_of_psi_power_error`
proves this model is differentiable on `Re(s) > theta`, and
`PrimeNumberTheorem.eqOn_regularizedNegLogDerivModel_neg_deriv_div_sub_pole`
records the overlap with the regularized zeta logarithmic derivative on
`Re(s) > 1`.

These steps are also exported through `RiemannPNT.API` as public entry points
for downstream files.

The analytic continuation step is now theorem-level as well.  In
`ZeroFreeRegion.MeromorphicAux`,
`ZeroFreeRegion.psiPowerErrorBound_excludes_riemannZeta_zero_right` proves the
Landau/Mellin converse:

`PsiPowerErrorBound theta`, with `0 <= theta < 1`, excludes zeta zeros throughout
`theta < Re(s) < 1`.

It uses the named Mellin model to extend a first-order ODE for the pole unit
`Q(s) = (s - 1) zeta(s)` from `Re(s) > 1` to `Re(s) > theta`, then applies the
generic nonvanishing theorem
`ZeroFreeRegion.analyticOnNhd_ne_zero_of_deriv_eq_mul_self`.  The public
specializations
`RiemannPNT.API.no_zeros_on_two_thirds_of_psi_power_error_bound_sub_delta` and
`RiemannPNT.API.no_zeros_on_one_third_of_psi_power_error_bound_sub_delta`
consume an `O(x^(2/3-delta))` `psi`-error input and exclude zeros on the
`2/3` and reflected `1/3` lines.  The remaining analytic gap is proving such a
power-saving `psi` estimate from an explicit formula, Tauberian theorem, or
equivalent zero-free input.

The finite truncated-zero layer also has a narrow tail-collapse API for the
degenerate case where no new zeros appear eventually above a base cutoff.  The
public theorems
`RiemannPNT.API.new_zero_contribution_sum_eventually_zero_of_eventually_sdiff_eq_empty`,
`RiemannPNT.API.new_zero_contribution_sum_tendsto_zero_of_eventually_sdiff_eq_empty`,
`RiemannPNT.API.new_zero_inv_norm_tail_tendsto_zero_of_eventually_sdiff_eq_empty`,
and `RiemannPNT.API.new_zero_card_tail_tendsto_zero_of_eventually_sdiff_eq_empty`
turn an eventual empty `nontrivialZerosFinset T \ nontrivialZerosFinset B`
block into eventual zero or convergence to zero for the finite contribution
and RH-tail controls.  These theorems are finite-tail handoffs and sanity
checks; they do not assert that the actual zeta zero set eventually has no new
zeros.
The norm handoff
`RiemannPNT.API.norm_explicitFormulaApprox_sub_le_new_zeros_sum_norm` gives the
same layer a direct triangle-inequality estimate for the change in
`explicitFormulaApprox` between two truncation heights from the summed norms of
the newly included zero contributions.

The same finite-tail layer also preserves the direct bridge from a stable base
truncation to the legacy unweighted compatibility predicate. The public theorem
`RiemannPNT.API.explicit_formula_von_mangoldt_unweighted_of_base_and_new_zero_contribution_tendsto_zero`
takes a base identity
`explicitFormulaApprox x B = chebyshevPsi0 x` and a proof that the new-zero
contribution
`sum_{rho in nontrivialZerosFinset T \ nontrivialZerosFinset B} x^rho / rho`
tends to zero, and returns
`explicit_formula_von_mangoldt_unweighted x hx`.  The wrapper
`RiemannPNT.API.explicit_formula_von_mangoldt_unweighted_of_base_and_new_zero_contribution_norm_tendsto_zero`
accepts the same tail convergence as a norm limit; the wrapper
`RiemannPNT.API.explicit_formula_von_mangoldt_unweighted_of_base_and_new_zero_contribution_sum_norm_tendsto_zero`
accepts convergence of the summed individual contribution norms.  The little-o
variant
`RiemannPNT.API.explicit_formula_von_mangoldt_unweighted_of_base_and_new_zero_contribution_sum_norm_isLittleO_one`
accepts the same summed-norm tail as `o(1)`.  The wrappers
`RiemannPNT.API.explicit_formula_von_mangoldt_unweighted_of_base_and_eventually_new_zero_contribution_norm_le`
and
`RiemannPNT.API.explicit_formula_von_mangoldt_unweighted_of_base_and_new_zero_contribution_norm_isBigO_tendsto_zero`
accept the eventual-bound and Big-O forms expected from contour estimates.  The
little-o variant
`RiemannPNT.API.explicit_formula_von_mangoldt_unweighted_of_base_and_new_zero_contribution_norm_isLittleO_one`
accepts the same norm tail as `o(1)`.  The wrapper
`RiemannPNT.API.explicit_formula_von_mangoldt_unweighted_of_base_and_eventually_no_new_zeros_via_contribution_tail`
is the degenerate eventual-empty-new-zero specialization.  These remain
conditional bridges around the finite truncation bookkeeping; none supplies
Perron's formula or the true analytic tail estimate.

The public facade also exposes
`RiemannPNT.API.no_zeros_on_two_thirds_of_truncated_explicit_formula_converse_route`,
which composes the truncated route
`ExplicitFormulaTruncatedConverseRoute (2 / 3)`, a future proof of the
truncated explicit formula for all admissible `T,x`, and the `ψ` power-saving
hypothesis into the direct right-side conclusion
`NoZerosOnVerticalLine (2 / 3)`.  This is the formal version of the
explicit-formula/PNT-error step before using zero symmetry.
The companion bridge
`RiemannPNT.API.no_zeros_on_one_third_of_truncated_explicit_formula_converse_route`,
uses the same hypotheses and then reflects the conclusion to
`NoZerosOnVerticalLine (1 / 3)`.
The generalized facade
`RiemannPNT.API.no_zeros_on_reflected_line_of_truncated_explicit_formula_converse_route`
does the same composition for arbitrary `0 < beta < 1`, yielding
`NoZerosOnVerticalLine (1 - beta)`.
The power-saving facades
`RiemannPNT.API.no_zeros_on_vertical_line_of_truncated_explicit_formula_converse_route_saving`
and
`RiemannPNT.API.no_zeros_on_reflected_line_of_truncated_explicit_formula_converse_route_saving`
use the sharper hypothesis `PsiPowerErrorBound (beta - delta)`.  Their
concrete `2/3` and reflected `1/3` specializations are exposed as
`RiemannPNT.API.no_zeros_on_two_thirds_of_truncated_explicit_formula_converse_route_saving`
and
`RiemannPNT.API.no_zeros_on_one_third_of_truncated_explicit_formula_converse_route_saving`.
Their existence-form companions
`RiemannPNT.API.not_exists_nontrivial_zero_on_line_of_truncated_explicit_formula_converse_route_saving`
and
`RiemannPNT.API.not_exists_nontrivial_zero_on_reflected_line_of_truncated_explicit_formula_converse_route_saving`
state the same direct power-saving exclusion as absence of a nontrivial zero on
the corresponding line.  The concrete existence-form specializations are
`RiemannPNT.API.not_exists_nontrivial_zero_on_two_thirds_of_truncated_explicit_formula_converse_route_saving`
and
`RiemannPNT.API.not_exists_nontrivial_zero_on_one_third_of_truncated_explicit_formula_converse_route_saving`.

## Recommended next formalization order

1. Already completed in the support layer: `jumpVonMangoldt`,
   `chebyshevPsi0`, `zeroMultiplicity`, finite zero sums, finite trivial-zero
   sums, and `goodHeight`.
2. Already completed for the current support layer: `goodHeight` iff/negation
   normalizers, `exists_goodHeight_Ioo` and
   `exists_strictMono_goodHeight_tendsto` for an unbounded admissible contour
   sequence, membership/monotonicity wrappers for the finite nontrivial-zero
   truncation, self-height membership of nontrivial zeros, and the current
   finset-based `zeroMultiplicity` values `0`/`1` according to membership in
   the self-height truncation; finite trivial-zero membership, real-axis /
   negative-real-part facts, denominator safety, `2 <= ‖s‖` and
   `‖s‖⁻¹ <= 1/2` denominator estimates, absolute-height normalization,
   nontrivial-zero separation, the single-term bound
   `‖x^s / s‖ <= (1/2) * x^s.re`, the standalone `x >= 1` power comparison
   `x^s.re <= x^(-2)`, the single-term specialization
   `‖x^s / s‖ <= (1/2) * x^(-2)`, the corresponding finite retained
   trivial-zero contribution-sum bound, the coarser
   `card * (1/2) * x^(-2)` finite-sum bound, and the explicit
   `floor(T/2) * (1/2) * x^(-2)` cutoff bound, with a further nonnegative
   height-scale bound `(T/2) * (1/2) * x^(-2)`, are also proved.  The truncated
   target predicate and conditional
   repackaging lemma are public API, but still target infrastructure.  Future analytic
   multiplicity/order work can refine this API without changing the downstream
   target shape.
3. Prove finite bounded-height support lemmas for the zero sums from
   `finite_nontrivial_zeros_bounded_height`.
4. Either prove the ordinary `1 / s` half-jump formula, or combine the proved
   finite-height `1 / s^2` formula and Riesz finite-difference squeeze with a
   quantitative choice of `y - x` in the contour-shift error argument.  The
   second-order vertical truncation, its von Mangoldt specialization, its
   closed-form coefficient bound, and the exact finite-difference bridge are
   complete.  Replacing the finite Dirichlet polynomial by the `-zeta'/zeta`
   series on the right line, and then estimating the shifted contour edges,
   remain open; the ordinary conditionally convergent half-jump is the alternate
   route.
5. Extend the existing constant-function rectangle sanity checks to a real
   rectangle meromorphic residue theorem as a reusable project
   lemma, since Mathlib currently supplies the analytic pieces but not the exact
   residue-sum wrapper needed here.
6. Prove the truncated explicit formula with an explicit contour-error term.
7. Only then state the principal-value or non-jump final formula as a limit.
