# Direct-L2 actual-zeta implementation DAG

Status: static design only.  None of the declarations below is claimed to be
formalized or built.  Lean/lake and publication remain frozen.

## Scope boundary

This DAG owns only deterministic cubic-kernel arithmetic, Carlson capacity,
complex observation kernels, actual-zeta tail adapters, and normalized transfer
assembly.  It must not modify the Sharp lower-bound modules, the half-isolated
Gram/Schur modules, or the complementary-bound module.

Every slice must be independently reviewable and mergeable.  A later slice may
import an earlier merged slice, but no PR may contain the implementation of two
slices merely to make its own build pass.

## Dependency graph

```text
PR1 cubic kernel --------------------+
                                      +--> PR4 actual-zeta tail adapter --> PR5 transfer
PR2 arithmetic certificates --------+
                                      +--> PR5 transfer
PR3 weighted Schur/observation ------+
```

PR1, PR2, and PR3 are mutually independent.  PR4 depends on all three.  PR5
depends on PR2 and PR4 plus the already-owned Sharp witness interface.

## PR1: deterministic relative cubic kernel

Proposed production file:

`PrimeNumberTheorem/ZeroDensityLayerBudgetCubicRelativeKernel.lean`

Purpose: isolate the exact second-difference Mellin kernel and its low/high
frequency bounds.  This slice contains no zeta zeros, density hypothesis, or
oscillation theorem.

Proposed public definitions:

1. `cubicRelativeKernel`
2. `triangleLaplaceKernel`
3. `retainedClusterDistortionConstant`

Proposed public theorems:

1. `cubicRelativeKernel_eq_triangleLaplaceKernel`
2. `cubicRelativeKernel_low_frequency_error`
3. `cubicRelativeKernel_high_frequency_bound`
4. `retainedCluster_cubic_distortion_bound`
5. `retainedCluster_cubic_distortion_below_budget`

Required mathematical statements:

```text
B_eta(s)
  = ((1+eta)^(s+2) - 2 + (1-eta)^(s+2))
      / (eta^2 s (s+1) (s+2))
  = (1/s) integral[-1,1] (1-|u|) (1+eta*u)^s du.

|s * B_eta(s) - 1| <= eta^2 * |s(s-1)| / 3
  for eta <= 1/2 and 0 <= re(s) <= 1.

|B_eta(s)| <= 7 / (eta^2 * |im(s)|^3).
```

Audit target: 3 typed definition examples and 5 typed theorem examples in the
Contract; 5 `#print axioms` entries in AxiomAudit; all 5 theorems in the
allowlist.  No `sorry`, `admit`, project axiom, or opaque analytical hypothesis.

## PR2: finite arithmetic certificates

Proposed production file:

`PrimeNumberTheorem/ZeroDensityLayerBudgetDirectL2Certificates.lean`

Purpose: package all deterministic choices used by the later analytical
adapter.  This is the only slice that chooses lambda, gammaLow, gammaHigh, the
finite real-strip mesh, dyadic shell count, and explicit residual thresholds.

Proposed public definitions:

1. `directL2IntervalSlack`
2. `directL2Lambda`
3. `directL2Gap`
4. `directL2OuterHeight`
5. `directL2SmoothingExponent`
6. `directL2GammaLow`
7. `directL2GammaHigh`
8. `directL2RealStripCount`
9. `directL2RealStripLeft`
10. `directL2RealStripRight`
11. `directL2DyadicShellCount`
12. `polylogAbsorptionConstant`
13. `residualTermThreshold`
14. `compiledResidualThreshold`

Proposed public theorem groups:

1. Interval constructor: `1 < lambda`, `lambda < 2`, and
   `[Y,Y^lambda]` contained in `[Y,Y^(1+epsilon)]`.
2. Two-height ordering: `g < gammaLow < gammaHigh < alpha`.
3. Exponent ledger: middle direct-L2 and high cubic-L1 exponents are strictly
   negative for every `1/2 < beta < 1`.
4. Real-strip cover: the finite half-open strips cover `[1/2,1]`, have width at
   most `r/(4*lambda)`, and preserve at least half the envelope margin.
5. Dyadic cover: the shells cover `[H,U]`; the last partial shell is dominated
   by its full shell.
6. Exact shell moments: the middle log-five majorant is `2164`; the high
   log-four majorant is `300`.
7. Polylog compiler: for positive eta and `X >= 1`,
   `(1+log X)^ell <= K(eta,ell) * X^(eta/2)`.
8. Residual compiler: every registered nonnegative residual is below its typed
   budget beyond `compiledResidualThreshold`.
9. Budget sum: the fixed allocation uses at most `7*delta/8`, leaving strict
   surplus `delta/8`.

This PR replaces, rather than duplicates, weaker single-inequality parameter
lemmas.  The outer contour exponent `alpha`, low probe exponent `gammaLow`, and
Carlson split exponent `gammaHigh` must remain distinct types or named fields.

Contract/AxiomAudit counts must be derived mechanically from the final public
surface before publication; every public definition gets a typed example and
every public theorem gets both a typed example and `#print axioms`.

## PR3: multiplicity-weighted Schur and complex observation kernel

Proposed production files:

1. `PrimeNumberTheorem/ZeroDensityLayerBudgetMultiplicityWeightedSchur.lean`
2. `PrimeNumberTheorem/ZeroDensityLayerBudgetComplexTriangleObservation.lean`

Purpose: provide the exact bridge from linear multiplicity Carlson capacity to
quadratic energy without inserting a maximum-multiplicity factor.

Proposed public definitions:

1. `multiplicityWeightedRowMass`
2. `complexTriangleLaplaceKernel`
3. `complexTriangleObservationMajorant`

Proposed public theorems:

1. `multiplicityWeighted_schur_bound`
2. `multiplicityWeighted_schur_bound_after_delete`
3. `complexTriangleLaplaceKernel_abs_le_exp_min`
4. `sameStrip_complexTriangle_support_bound`
5. `linearCarlson_to_quadraticEnergy_logFive`

The central Schur statement must consume

```text
sum j, multiplicity j * A i j <= occupancy
```

and conclude

```text
abs (sum i,j, multiplicity i * multiplicity j
       * a i * conj (a j) * K i j)
  <= occupancy * sum i, multiplicity i * |a i|^2.
```

Finite deletion is a corollary of nonnegative-mass monotonicity.  It must not
rerun or restate Carlson density for each deleted set.  The actual complex
kernel estimate is

```text
|K_L(a+i*delta)|
  <= exp(|a|*L) * min(1, 4/(L^2*(a^2+delta^2))).
```

The advertised logarithmic ledger is exactly Carlson log-four plus one local
weighted-occupancy log, hence log-five.  No extra maximum-multiplicity log is
allowed.  PR3 does not prove Gram separation or an occupancy theorem; those are
inputs owned by half-isolated.

Audit target: 3 typed definition examples and 5 typed theorem examples; 5
`#print axioms` entries; all 5 theorems in the allowlist.

## PR4: actual-zeta two-height residual adapter

Proposed production file:

`PrimeNumberTheorem/ZeroDensityLayerBudgetActualCubicTwoHeightL2Tail.lean`

Purpose: instantiate PR1-PR3 with actual zeta-zero shells and the existing
Carlson capacity theorem.  This is the first slice allowed to mention the actual
explicit-formula zero collection.

Proposed public definitions:

1. `actualCubicLowZeroEnergy`
2. `actualCubicMiddleZeroEnergy`
3. `actualCubicHighZeroMass`
4. `actualCubicResidualNorm`

Proposed public theorems:

1. `actualCubicMiddleShell_energy_bound`
2. `actualCubicMiddleShell_energy_bound_after_delete`
3. `actualCubicMiddleRange_energy_bound`
4. `actualCubicMiddleRange_norm_bound`
5. `actualCubicHighShell_mass_bound`
6. `actualCubicHighRange_mass_bound`
7. `actualCubicTwoHeight_residual_bound`
8. `actualCubicTwoHeight_residual_below_budget`

Required exponent and log ledger:

```text
middle energy:
  X^(2*kappa*lambda*(sigmaR-beta)
     + gamma*(q(sigmaL)-2)) * (1+log X)^5

middle norm after finite strips and polylog absorption:
  O(X^(-rMiddle/8))

high absolute mass:
  X^(kappa*lambda*(sigmaR-beta)
     + 2*d + gammaHigh*(q(sigmaL)-3)) * (1+log X)^4.
```

All strict inequalities and equality-critical cases come from PR2.  PR4 must
state explicitly that exponent equality does not yield decay because the
remaining logarithmic factor is nonnegative and growing.

Deletion of the retained finite cluster must use PR3 monotonicity.  The adapter
must preserve the direct-L2 `1/|rho|^2` weight and must not fall back to the old
L1 square-half-height argument.

Audit target: 4 typed definition examples and 8 typed theorem examples; 8
`#print axioms` entries; all 8 theorems in the allowlist.

## PR5: normalized main-minus-residual transfer

Proposed production file:

`PrimeNumberTheorem/ZeroForcingUnifiedTransferActualCubicL2.lean`

Purpose: connect the existing Sharp witness interface to PR4 without proving a
new Sharp theorem.  This slice performs only normalization, threshold
compilation, triangle inequality, and the final change from logarithmic time to
an actual `x` witness.

Proposed public definitions:

1. `actualCubicNormalizedMain`
2. `actualCubicNormalizedResidual`
3. `actualCubicTransferThreshold`

Proposed public theorems:

1. `actualCubic_normalized_decomposition`
2. `actualCubic_main_approximation`
3. `actualCubic_residual_below_compiled_budget`
4. `actualCubic_main_sub_residual_gt_pi_div_two`
5. `actualCubic_shortInterval_absolute_witness`

The final theorem may conclude only an absolute witness of the form

```text
exists x in Set.Icc Y (Y^(1+epsilon)),
  |E x| > (pi/2) * x^beta / |rho0|.
```

It must retain the strict `> pi/2`, the exact `x^beta/|rho0|` scale, and the
requested short power interval.  It must not claim `Omega_plus`, `Omega_minus`,
RH, exclusion of all zeros with real part above `1/2`, or exceptional-zero
proliferation.  Those require additional mathematics not supplied by this DAG.

Audit target: 3 typed definition examples and 5 typed theorem examples; 5
`#print axioms` entries; all 5 theorems in the allowlist.

## Integration gates for every PR

1. Production diff is limited to the named owned prefixes.
2. Contract covers every public definition and theorem with exact typed
   examples; bare `#check` is insufficient.
3. AxiomAudit prints axioms for every public theorem.
4. All public theorems are entered in the allowlist.
5. Focused source, Contract, and AxiomAudit builds pass on the locked current
   main.
6. Target/chain, placeholder scan, diff audit, allowlist, and complete baseline
   pass on that same base/head pair.
7. No force-push.  If main moves, replay on the new main and rerun the gates.
8. Publish only a Ready PR after the queue explicitly unfreezes publication.

## Stop conditions

Stop and report instead of broadening a slice if implementation would require:

1. changing a production theorem statement, hypothesis, or constant owned by
   Sharp or half-isolated;
2. inserting a generic zero-proliferation tree;
3. replacing actual zeta zeros by an unconstrained abstract kernel in PR4;
4. adding a maximum-multiplicity factor to rescue the Schur argument;
5. treating exponent equality as decay;
6. deriving a sign-specific oscillation conclusion from an absolute witness;
7. weakening the interval from `1+epsilon`, the constant from strict `pi/2`, or
   the scale from `x^beta/|rho0|`.

