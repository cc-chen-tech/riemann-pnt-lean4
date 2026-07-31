# Vinogradov-Korobov Exponential-Sum Foundation Design

## Objective

Build the first verified Lean 4 layer on the route to the
Vinogradov-Korobov zero-free region.  The final project goal remains the
unconditional theorem `vinogradov_korobov_zero_free_region` and its
`3/5`-type prime-number-theorem error consequence.  This first layer is a
feasibility gate: it must end with a nontrivial estimate for a dyadic block of
the Dirichlet polynomial `sum n^(-it)`, not merely with abstract interfaces.

## Prior Art And Reuse Decision

The discrete van der Corput fundamental inequality is not new infrastructure.
Ralf Stephan's public-domain file
`ForMathlib/Analysis/Equidistribution/VanDerCorput.lean` at commit
`d9d838819277fc2d8bd2b0ee09c773f1402a7aa6` proves the required
Cauchy-Schwarz/autocorrelation inequality.  The source compiles against this
repository's Lean 4.29.1 toolchain after replacing the unavailable later
Mathlib import `Mathlib.Algebra.Order.Star.Real` by the equivalent current
snapshot import `Mathlib.Data.Real.StarOrdered`.

An independent temporary audit on 2026-07-19 produced:

```text
'vanDerCorput_fundamental_inequality' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

The project will therefore adapt and attribute that proof rather than rewrite
it.  It will be placed in the project namespace to avoid a future name clash
if the upstream theorem enters Mathlib.  No new remote Lake dependency will be
added.

## Architecture

### Layer 1: Fundamental difference inequality

`ZeroFreeRegion/VinogradovKorobov/VanDerCorput.lean` contains the attributed
adaptation and exports
`ZeroFreeRegion.VinogradovKorobov.vanDerCorputFundamentalInequality`.
The theorem keeps the upstream natural-indexed statement, arbitrary step
`a`, analytic diagonal term, and explicit autocorrelation sum.

### Layer 2: Unit phases and first derivative cancellation

`ZeroFreeRegion/VinogradovKorobov/ExponentialSum.lean` defines finite interval
phase sums and proves:

- unit norm of every phase term;
- exact conjugate-product conversion to a phase difference;
- the geometric bound for a linear phase;
- a discrete Kusmin-Landau theorem under a monotone derivative and a stated
  separation from integral frequencies.

The first derivative theorem must have an explicit numerical bound.  A
predicate whose proof is supplied as an argument is not a successful
deliverable.

### Layer 3: Second derivative estimate

`ZeroFreeRegion/VinogradovKorobov/SecondDerivative.lean` combines the
fundamental inequality with the first derivative estimate for shifted phase
differences.  It exports a concrete second derivative test of the shape

```text
norm (sum exp (I * f n)) <= C * (N * sqrt lambda + 1 / sqrt lambda)
```

under explicit interval, differentiability, monotonicity, and two-sided
second-derivative hypotheses.  Constants may be nonoptimal but must be
absolute and proved positive.

### Layer 4: Logarithmic phase application

`ZeroFreeRegion/VinogradovKorobov/LogPhase.lean` specializes the second
derivative theorem to `f(x) = -t * log x` on a dyadic interval.  It must prove
an unconditional bound for

```text
sum n in Ioc M (M + N), Complex.exp (-I * t * log n)
```

and a corollary that is strictly smaller than the trivial bound `N` on a
nonempty, explicitly stated parameter regime.  This is the feasibility gate.

### Later layers retained by the project goal

After the gate passes, later plans will add repeated differencing or an
exponent-pair calculus, weighted partial summation to `sum n^(-sigma-it)`, a
critical-strip zeta growth estimate, the Vinogradov-Korobov zero-repulsion
closure, and the `3/5` PNT error.  These are not replaced by the first-layer
deliverables.

## Verification And Claim Boundary

Every layer receives a contract module and the final public theorem receives
an axiom audit.  The required allowlist is exactly:

```text
propext
Classical.choice
Quot.sound
```

Source scans must find no `sorry`, `admit`, or project-level `axiom`.  Until
the final zero-free-region predicate has a corresponding proved theorem, the
repository must continue to describe Vinogradov-Korobov as open.

## Stop Conditions

The feasibility phase fails if the logarithmic-phase estimate cannot beat the
trivial length bound in any useful dyadic regime without adding an unproved
assumption.  In that case the general exponential-sum library remains valid,
but no VK completion claim is made.
