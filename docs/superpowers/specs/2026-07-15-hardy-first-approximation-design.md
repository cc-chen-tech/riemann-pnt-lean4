# Hardy Theorem via the First Zeta Approximation

> **Status:** Completed and verified. The final witnesses are
> `HardyTheorem.hardy_zeros_unbounded_target_proved` and
> `HardyTheorem.hardy_theorem_target_proved`. The risks below are retained as
> the historical design record, not as current blockers.

## Objective

Prove the existing unconditional target

```lean
HardyTheorem.hardy_zeros_unbounded_target
```

and derive `HardyTheorem.hardy_theorem_target`.  The result must say that zeta
has critical-line zeros at arbitrarily large positive height.  A conditional
bridge, a new `def ... : Prop`, or a proof assuming an approximate functional
equation does not satisfy this objective.

## Claim Boundary

The result is Hardy's theorem, not the Riemann hypothesis.  It proves
infinitely many zeros on `Re(s) = 1/2`; it does not prove that every
nontrivial zero lies there and does not exclude zeros on `Re(s) = 1/3`.

No numerical constants are promised.  All constants in asymptotic estimates
may be existential, but every estimate must be a proved theorem about the
actual zeta and Hardy-Z functions.

## Selected Proof

Use the first-approximation proof in Usha K. Sangale, *A note on Hardy's
theorem*, rather than the current two-signed-moment target or a full
Riemann-Siegel approximate functional equation:

1. Assume the critical-line zero set is bounded.  The already-proved
   `hardyZ_eventually_const_sign_of_bounded_zeros` makes `hardyZ` constant-sign
   on every sufficiently high dyadic interval `[T, 2*T]`.
2. Constant sign gives

   ```text
   |integral T (2*T) hardyZ| = integral T (2*T) |hardyZ|.
   ```

3. Prove `|hardyZ t| = ||zeta(1/2 + i*t)||`.  A specialized first
   approximation formula for zeta then gives

   ```text
   integral T (2*T) |hardyZ t| >= c*T
   ```

   for all sufficiently large `T`.
4. Prove a vertical Stirling estimate for the normalized `GammaR` phase.  Do
   not differentiate the principal-branch `thetaPhase`.  Instead compare the
   exact unit phase

   ```text
   GammaR(1/2 + i*t) / ||GammaR(1/2 + i*t)||
   ```

   directly with `exp(i * thetaModel t)`, where

   ```text
   thetaModel t = t/2 * log (t/(2*pi)) - t/2 - pi/8.
   ```

   The comparison error is `O(1/t)`.
5. Insert the first zeta approximation into the exact Hardy-Z phase identity.
   The main terms have phase

   ```text
   phase n t = t/2 * log (t / (2*pi*exp(1)*n^2)) - pi/8.
   ```

6. Prove first- and second-derivative oscillatory-integral bounds.  Split the
   finite sum at a constant multiple of `sqrt T`: near stationary indices use
   the second-derivative estimate `O(sqrt T)`; for the remaining indices use
   the monotone first-derivative estimate `O(1)`.  Summation with weights
   `n^(-1/2)` yields

   ```text
   |integral T (2*T) hardyZ| <= C*T^(3/4)
   ```

   for all sufficiently large `T`.
7. Since `T^(3/4) = o(T)`, the upper and lower bounds contradict constant
   sign.  Thus the zero set is unbounded, proving
   `hardy_zeros_unbounded_target` directly.

## Why This Route

### Chosen: first zeta approximation

This route needs one zeta approximation, one vertical Gamma estimate, and two
general oscillatory-integral estimates.  Its final contradiction uses one
dyadic Hardy-Z integral and has a direct unbounded-zero conclusion.

### Rejected: two signed weighted moments

The existing logical bridge from two signed moments to Hardy's theorem is
correct, but proving both full moment asymptotics is stronger than required.
Continuing to package the moment target without proving the asymptotics would
repeat the interface-only work this project is now avoiding.

### Rejected: contour shift of `chi(s)^(-1/2) * zeta(s)`

The contour proof can reuse some Phragmen-Lindelof zeta bounds, but it requires
an analytic square-root branch for `chi` on a strip and more contour boundary
bookkeeping.  The first-approximation route avoids that branch construction.

### Rejected: full Riemann-Siegel AFE

A full AFE is a valuable later result but is not needed for Hardy's theorem.
It introduces an unwrapped theta function and a stronger remainder statement
than this proof consumes.

## Module Boundaries

### `HardyTheorem/FirstZetaApproximation.lean`

Prove the specialized critical-line first approximation on a dyadic interval.
It must expose a finite Dirichlet polynomial plus the elementary pole term and
a norm-bounded remainder.  It must also prove the resulting lower bound for
the integral of `norm (riemannZeta (1/2 + i*t))`.

### `HardyTheorem/VerticalGammaAsymptotic.lean`

Define `thetaModel` and prove the unit-phase comparison with error `O(1/t)`.
This module owns all complex-Gamma asymptotics.  It must not claim that the
principal-value `thetaPhase` itself has a global real asymptotic.

### `HardyTheorem/OscillatoryIntegral.lean`

Prove reusable, actual integral theorems:

- monotone first derivative bounded away from zero implies a uniform bound on
  the integral of `exp(i*F(t))`;
- a second derivative bounded away from zero implies the square-root bound
  needed for the near-stationary range.

These are analytic theorems with derivative hypotheses, not Hardy-specific
conditional predicates.

### `HardyTheorem/HardyIntegralContradiction.lean`

Assemble the exact Hardy-Z phase identity, the lower and upper dyadic integral
bounds, and the final contradiction.  This module must contain the theorem

```lean
theorem hardy_zeros_unbounded_target_proved : hardy_zeros_unbounded_target
```

and the corollary

```lean
theorem hardy_theorem_target_proved : hardy_theorem_target
```

## Proof Order

The implementation proceeds from the final contract backwards:

1. Add a failing compile-time contract for the two final theorems.
2. Prove `abs_hardyZ_eq_norm_riemannZeta` and the constant-sign integral
   equality.
3. Prove the two generic oscillatory-integral estimates.
4. Prove the vertical Gamma unit-phase estimate.
5. Prove the specialized first zeta approximation and lower integral bound.
6. Prove the Hardy-Z dyadic upper bound.
7. Close the contradiction and make the original contract green.

This ordering allows the implementation to stop honestly at a hard analytic
lemma.  No unfinished step may be replaced by a hypothesis in the final
theorem.

## Verification

Acceptance requires all of the following:

- `lake build Test.HardyFirstApproximationContract` succeeds;
- `lake build` succeeds from the shared project cache;
- `./scripts/verify-baseline.sh` succeeds;
- the target inventory marks `hardy_theorem_target` and
  `hardy_zeros_unbounded_target` as proved by named theorems;
- `#print axioms` for both final declarations reports only `propext`,
  `Classical.choice`, and `Quot.sound`;
- no `sorry`, `admit`, custom axiom, or new route-interface `Prop` is added;
- an independent review checks the Gamma phase direction, both oscillatory
  estimates, the finite-sum split, and the final constant-sign contradiction.

## Risks

The dominant risks are mathematical infrastructure, not Lean syntax:

1. Mathlib has Euler's complex Gamma integral and functional identities but no
   complex vertical Stirling theorem.  This estimate must be proved locally.
2. Mathlib has no ready-made van der Corput first/second derivative integral
   tests in the required form.  They must be developed from integration by
   parts and real-variable monotonicity.
3. At design time the repository had no finite critical-line first
   approximation for zeta. This was closed by `criticalLineZetaFirstApprox`
   using a finite-sum plus tail-integral argument.

These risks were closed in the implementation by the vertical Gamma,
oscillatory-integral, and first-zeta-approximation modules. The final contract
and full verification pass before the theorem is reported as proved.
