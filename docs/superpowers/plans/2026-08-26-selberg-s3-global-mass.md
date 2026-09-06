# Selberg S3 Global Mass Implementation Plan

> Status: paper proof complete in
> `docs/research/2026-08-24-selberg-mainline-mathematical-audit.md`;
> Status: Tasks 1--5 complete in Lean.  This plan
> deliberately separates the arithmetic/Gaussian input from Plancherel and
> from the abstract sliding window argument.

**Goal:** Prove the S3 global square-mass estimate for
`selbergCompletedMollifiedFComplex`, then derive the absolute sliding-window
second moment with the exact factor `H^2`.

**Mathematical route:** Put `G=delta^(-2)` and
`theta=1 / log G`.  Bound `[1,G]` using only `J(1,theta)`.  Bound `(G,infinity)`
directly from the Gaussian theta series.  Assemble residue and nonconstant
positive-frequency mass, reflect by reality, transport the exact `2*pi`
normalization, and use `Lp.norm_fourier_eq`.  Finally apply pointwise
Cauchy--Schwarz and Tonelli to the nonnegative absolute window.

---

## Task 1: Delta-scale low physical mass

**Files:**

- Create: `HardyTheorem/SelbergGlobalLowMass.lean`
- Create: `Test/SelbergGlobalLowMassContract.lean`

**RED:** Add a contract for an existential uniform bound of

```lean
∫ x in Set.Ioc 1 (delta ^ (-2 : ℝ)),
  Complex.normSq (selbergPhysicalThetaKernel delta x X)
```

by a constant times

```lean
delta ^ (-(1 / 2 : ℝ)) * Real.log (1 / delta) / Real.log X
```

under the existing S2 parameter hypotheses and the explicit eventual
condition `2 ≤ Real.log (delta ^ (-2 : ℝ))`.

**GREEN:** Instantiate `exists_abs_selbergJ_le` at `x=1` and
`theta=1/log(delta^(-2))`; reuse
`selbergJLowMass_le_exp_one_mul_J_unconditional`.  Prove all positivity,
logarithm, and `1≤X^a` obligations explicitly.  Do not extend the base-point
range of `J`.

**VERIFY:** Compile the source and contract; print the theorem assumptions
and audit that no new axiom or placeholder entered the interface.

## Task 2: Direct Gaussian tail of the physical theta kernel

**Files:**

- Create: `HardyTheorem/SelbergPhysicalThetaGaussianTail.lean`
- Create: `Test/SelbergPhysicalThetaGaussianTailContract.lean`

**RED:** Contract the following layers separately:

1. norm of one physical Gaussian term;
2. geometric majorant for one positive theta ray when
   `delta * u^2 / (2*X^2) ≥ 1/2`;
3. outer coefficient mass at most `X*(1+log X)`;
4. pointwise square bound for `selbergPhysicalThetaKernel`;
5. integrated tail on `Ioi (delta^(-2))`.

**GREEN:** Use `delta_le_two_pi_mul_sin`,
`abs_selbergSqrtZetaTaperedCoeff_le_one`, and
`selberg_sum_Icc_inv_le_one_add_log`.  Majorize `n^2` by `n`, sum the
geometric series, split `exp(-2*B*u^2)` at `u=G`, apply the complete Gaussian
integral, and absorb the endpoint exponential using `exp(-z)≤2/z^2`.
Keep a concrete universal constant; no asymptotic notation appears in Lean.

**VERIFY:** Compile source and contract and inspect theorem axioms.

## Task 3: Positive explicit-kernel and global time-domain mass

**Files:**

- Create: `HardyTheorem/SelbergGlobalFourierMass.lean`
- Create: `Test/SelbergGlobalFourierMassContract.lean`

**RED:** Contract:

1. full positive nonconstant inverse-kernel mass on `Ioi 0`;
2. full positive explicit-kernel mass on `Ioi 0`;
3. the S3a bound for
   `∫ t, ‖selbergCompletedMollifiedFComplex delta X t‖^2`.

**GREEN:** Split at `log(delta^(-2))`, use the exact logarithmic mass bridge,
Tasks 1--2, and the existing residue exponential bound.  Assemble with
`normSq_selbergExplicitInverseFourierKernel_le`.  Prove an even-energy
whole-line identity from `RealFourierEnergySymmetry`, apply the existing a.e.
S1 compatibility at Mathlib frequency, and finish with
`MathlibAux.integral_norm_sq_coeFn_eq_norm_sq` and
`MeasureTheory.Lp.norm_fourier_eq`.

**VERIFY:** Compile source/contract; check the displayed target has the exact
`log(1/delta)/(sqrt(delta)*log X)` scale and no missing `2*pi` factor.

## Task 4: Abstract absolute sliding-window L2 theorem

**Files:**

- Create: `MathlibAux/AbsoluteSlidingWindowL2.lean`
- Create: `Test/AbsoluteSlidingWindowL2Contract.lean`

**RED:** Contract a theorem saying that for `H≥0` and square-integrable
`F : ℝ → ℂ`,

```lean
∫ t, (∫ u in t..t + H, ‖F u‖) ^ 2
  ≤ H ^ 2 * ∫ u, ‖F u‖ ^ 2
```

**GREEN:** Prove interval Cauchy--Schwarz first.  Rewrite the interval as a
nonnegative set integral, use Tonelli, and show the fiber
`{t | t ≤ u ∧ u ≤ t+H}` has Lebesgue measure `H`.  Keep this theorem
independent of Selberg.

**VERIFY:** Compile source/contract and test `H=0` through simplification.

## Task 5: Public S3b assembly and PR update

**Files:**

- Create: `HardyTheorem/SelbergSlidingAbsoluteSecondMoment.lean`
- Create: `Test/SelbergSlidingAbsoluteSecondMomentContract.lean`
- Modify: `docs/research/2026-08-24-selberg-mainline-mathematical-audit.md`

**RED/GREEN:** Combine Task 3 with Task 4 to export the Selberg S3b theorem.
The witness constant may depend only on fixed `a,c`; it must be uniform in
`X,delta,H` under the documented hypotheses.

**VERIFY:** Run direct Lean compilation for every new source and contract,
then the relevant `lake build` targets, `git diff --check`, and the repository
placeholder/axiom audit.  Commit, push to
`codex/selberg-mainline-s2-fourier-20260825`, update PR #484's body to mark
S3 complete only if all checks pass, and confirm the PR remains open,
non-draft, and mergeable.
