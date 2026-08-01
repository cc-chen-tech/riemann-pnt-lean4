# VK-Edge Q-Power Detector Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Construct and audit a real finite q-power Dirichlet detector which cancels the main-pole node and prescribed real/conjugate-pair nodes, is normalized at a noncolliding target node, and has an exact negative-mass identity plus an explicit weighted-coefficient bound.

**Architecture:** Represent the detector as a real polynomial evaluated at `z_q(s) = exp (-s * log q)`.  Build old-pole annihilation from real linear factors and real quadratic conjugate-pair factors, then multiply by a real linear interpolator which normalizes the target response.  Keep coefficient-mass estimates in a second module so the algebraic construction and the quantitative loss certificate can be reviewed independently.

**Tech Stack:** Lean 4, Mathlib complex analysis and real polynomials, Lake, exact contract modules, dedicated and central axiom audits.

## Global Constraints

- Work only in `/Users/luicy/AI/Riemann/riemann-pnt-lean4/.worktrees/vk-edge-q-power-detector-design` on branch `codex/vk-edge-q-power-detector-design`.
- Do not modify Gate B witness extraction, Finset growth, iterative counting, or Carlson stitching modules.
- Do not add a class, a Prop-only route wrapper, a project `axiom`, `sorry`, or `admit`.
- Keep the integer-base noncollision theorem and the real zeta contour response outside this implementation plan.
- Do not claim a repeatable Sharp lower bound, a Carlson contradiction, or RH.
- Run at most one global Lean process.  Before each Lean command, verify that no unrelated `lake`, `lean`, or `leanc` process is active.
- Use `LEAN_NUM_THREADS=1` for every Lean or Lake invocation.
- Run focused source, contract, and dedicated audit checks before the central audit.  Do not start an untargeted full build.

## File Structure

- Create `PrimeNumberTheorem/QPowerDetectorAlgebra.lean`: q-power node, real polynomial evaluation, real and conjugate-pair factors, real linear interpolation, normalized annihilator, and exact detector response.
- Create `PrimeNumberTheorem/QPowerDetectorMass.lean`: weighted coefficient L1, positive/negative mass, exact half-L1 identity at a vanished real node, submultiplicativity, and the explicit product estimate.
- Create `Test/QPowerDetectorAlgebraContract.lean`: exact public types for the algebra module.
- Create `Test/QPowerDetectorMassContract.lean`: exact public types for the mass module.
- Create `Test/QPowerDetectorAxiomAudit.lean`: `#print axioms` for every public theorem added by both modules.
- Modify `Test/MultiplicityAxiomAudit.lean`: import both modules and register every public theorem.
- Modify `scripts/check_axiom_allowlist.py`: register the dedicated audit and all public theorem names.
- Modify `lakefile.lean`: add the two source modules and three test modules to their existing library lists.
- Modify `docs/research/vk-edge-prime-side-q-power-detector-design.md`: replace planned status with the exact proved endpoint and remaining strict-margin blocker after verification.

---

### Task 1: Lock the algebra API with a failing exact contract

**Files:**
- Create: `Test/QPowerDetectorAlgebraContract.lean`

**Interfaces:**
- Consumes: Mathlib `Polynomial`, `Complex.exp`, and finite products.
- Produces: the exact public names and types implemented in Task 2.

- [x] **Step 1: Create the failing contract**

```lean
import PrimeNumberTheorem.QPowerDetectorAlgebra

open Polynomial

namespace PrimeNumberTheorem.PrimeSideDetector

#check (qPowerNode : Nat → Complex → Complex)
#check (@qPowerNode_one :
  forall {q : Nat}, q ≠ 0 → qPowerNode q 1 = ((q : Real)⁻¹ : Complex))
#check (evalRealPolynomial : Polynomial Real → Complex → Complex)
#check (realNodeFactor : Real → Polynomial Real)
#check (conjugatePairFactor : Complex → Polynomial Real)
#check (realLinearInterpolator : Complex → Complex → Polynomial Real)

#check (evalRealPolynomial_realNodeFactor_self :
  forall r : Real, evalRealPolynomial (realNodeFactor r) r = 0)

#check (evalRealPolynomial_conjugatePairFactor_left :
  forall z : Complex, evalRealPolynomial (conjugatePairFactor z) z = 0)

#check (evalRealPolynomial_conjugatePairFactor_right :
  forall z : Complex,
    evalRealPolynomial (conjugatePairFactor z) (star z) = 0)

#check (@evalRealPolynomial_realLinearInterpolator :
  forall {z w : Complex},
    (z.im = 0 → w.im = 0) →
    evalRealPolynomial (realLinearInterpolator z w) z = w)

#check (qPowerAnnihilator :
  Nat → Finset Real → Finset Complex → Polynomial Real)

#check (@normalizedQPowerPolynomial :
  Nat → Finset Real → Finset Complex → Complex → Polynomial Real)

#check (@normalizedQPowerPolynomial_eval_target :
  forall {q : Nat} {realNodes : Finset Real}
      {pairNodes : Finset Complex} {z0 : Complex},
    evalRealPolynomial (qPowerAnnihilator q realNodes pairNodes) z0 ≠ 0 →
    evalRealPolynomial
      (normalizedQPowerPolynomial q realNodes pairNodes z0) z0 = 1)

#check (@normalizedQPowerPolynomial_eval_main :
  forall {q : Nat} {realNodes : Finset Real}
      {pairNodes : Finset Complex} {z0 : Complex},
    q ≠ 0 →
    evalRealPolynomial
      (normalizedQPowerPolynomial q realNodes pairNodes z0)
      ((q : Real)⁻¹) = 0)

#check (@normalizedQPowerPolynomial_eval_realNode :
  forall {q : Nat} {realNodes : Finset Real}
      {pairNodes : Finset Complex} {z0 : Complex} {r : Real},
    r ∈ realNodes →
    evalRealPolynomial
      (normalizedQPowerPolynomial q realNodes pairNodes z0) r = 0)

#check (@normalizedQPowerPolynomial_eval_pairNode :
  forall {q : Nat} {realNodes : Finset Real}
      {pairNodes : Finset Complex} {z0 z : Complex},
    z ∈ pairNodes →
    evalRealPolynomial
      (normalizedQPowerPolynomial q realNodes pairNodes z0) z = 0)

#check (qPowerDetector : Nat → Polynomial Real → Complex → Complex)

#check (qPowerDetector_eq_polynomial_eval :
  forall (q : Nat) (H : Polynomial Real) (s : Complex),
    qPowerDetector q H s = evalRealPolynomial H (qPowerNode q s))

#check (qPowerDetector_eq_coeff_sum :
  forall (q : Nat) (H : Polynomial Real) (s : Complex),
    qPowerDetector q H s =
      ∑ k ∈ H.support, (H.coeff k : Complex) * (qPowerNode q s) ^ k)

#check (normalizedQPowerDetector :
  Nat → Finset Real → Finset Complex → Complex → Complex → Complex)

#check (@normalizedQPowerDetector_at_target :
  forall {q : Nat} {realNodes : Finset Real}
      {pairNodes : Finset Complex} {s0 : Complex},
    evalRealPolynomial (qPowerAnnihilator q realNodes pairNodes)
        (qPowerNode q s0) ≠ 0 →
    normalizedQPowerDetector q realNodes pairNodes s0 s0 = 1)

#check (@normalizedQPowerDetector_at_one :
  forall {q : Nat} {realNodes : Finset Real}
      {pairNodes : Finset Complex} {s0 : Complex},
    q ≠ 0 → normalizedQPowerDetector q realNodes pairNodes s0 1 = 0)

end PrimeNumberTheorem.PrimeSideDetector
```

- [x] **Step 2: Verify that the contract fails for the intended reason**

Run:

```bash
LEAN_NUM_THREADS=1 lake env lean Test/QPowerDetectorAlgebraContract.lean
```

Expected: failure because `PrimeNumberTheorem.QPowerDetectorAlgebra` and its declarations do not exist.

- [x] **Step 3: Commit the red contract**

```bash
git add Test/QPowerDetectorAlgebraContract.lean
git commit -m "test: lock q-power detector algebra API"
```

### Task 2: Implement real annihilation and target normalization

**Files:**
- Create: `PrimeNumberTheorem/QPowerDetectorAlgebra.lean`
- Modify: `Test/QPowerDetectorAlgebraContract.lean` only if elaboration exposes a syntactic namespace qualification issue; do not weaken a mathematical type.

**Interfaces:**
- Consumes: the exact contract from Task 1.
- Produces: a real polynomial with exact main-node, real-node, and conjugate-pair annihilation and exact target normalization.

- [x] **Step 1: Define q-power nodes and real polynomial evaluation**

```lean
def qPowerNode (q : Nat) (s : Complex) : Complex :=
  Complex.exp (-(s * Real.log q))

def evalRealPolynomial (p : Polynomial Real) (z : Complex) : Complex :=
  (p.map Complex.ofRealHom).eval z

def realNodeFactor (r : Real) : Polynomial Real := X - C r

def conjugatePairFactor (z : Complex) : Polynomial Real :=
  X ^ 2 - C (2 * z.re) * X + C (Complex.normSq z)
```

Prove the three factor-evaluation theorems from the contract by unfolding,
using `Complex.ext`, and reducing the quadratic identity to `Complex.normSq`.
Prove `qPowerNode_one` from positivity of a nonzero natural number,
`Real.exp_neg`, and `Real.exp_log`.

- [x] **Step 2: Define and prove the real linear interpolation lemma**

```lean
def realLinearInterpolator (z w : Complex) : Polynomial Real :=
  if hz : z.im = 0 then
    C w.re
  else
    C (w.re - (w.im / z.im) * z.re) +
      C (w.im / z.im) * X
```

For `z.im != 0`, prove equality by comparing real and imaginary parts.  For
`z.im = 0`, use the contract hypothesis `z.im = 0 -> w.im = 0`.

- [x] **Step 3: Define the annihilator and normalized polynomial**

```lean
def qPowerAnnihilator
    (q : Nat) (realNodes : Finset Real) (pairNodes : Finset Complex) : Polynomial Real :=
  realNodeFactor ((q : Real)⁻¹) *
    (∏ r ∈ realNodes, realNodeFactor r) *
    (∏ z ∈ pairNodes, conjugatePairFactor z)

def normalizedQPowerPolynomial
    (q : Nat) (realNodes : Finset Real) (pairNodes : Finset Complex)
    (z0 : Complex) : Polynomial Real :=
  let D := qPowerAnnihilator q realNodes pairNodes
  let w := (evalRealPolynomial D z0)⁻¹
  D * realLinearInterpolator z0 w
```

Before applying the interpolation theorem, prove that if a real polynomial is
evaluated at a real complex number then the result has zero imaginary part.
This supplies the branch compatibility hypothesis when `z0.im = 0`.

- [x] **Step 4: Prove exact response and annihilation**

Prove all four normalized-polynomial theorems in the contract.  The target
theorem uses `inv_mul_cancel₀`; each annihilation theorem uses the corresponding
zero factor before multiplication by the interpolator.

- [x] **Step 5: Define the detector evaluation**

```lean
def qPowerDetector (q : Nat) (H : Polynomial Real) (s : Complex) : Complex :=
  evalRealPolynomial H (qPowerNode q s)

def normalizedQPowerDetector
    (q : Nat) (realNodes : Finset Real) (pairNodes : Finset Complex)
    (s0 s : Complex) : Complex :=
  qPowerDetector q
    (normalizedQPowerPolynomial q realNodes pairNodes (qPowerNode q s0)) s
```

Keep `qPowerDetector_eq_polynomial_eval` as an explicit public theorem even
though its proof is `rfl`; later contour modules should depend on the named
interface rather than unfold the definition.  Prove
`qPowerDetector_eq_coeff_sum` from polynomial evaluation over `support`.  Then
prove `normalizedQPowerDetector_at_target` from the polynomial normalization
theorem, and `normalizedQPowerDetector_at_one` by rewriting `qPowerNode_one`
and applying the main-node annihilation theorem.

- [x] **Step 6: Run focused source and contract checks**

Run serially:

```bash
LEAN_NUM_THREADS=1 lake env lean PrimeNumberTheorem/QPowerDetectorAlgebra.lean
LEAN_NUM_THREADS=1 lake env lean Test/QPowerDetectorAlgebraContract.lean
```

Expected: both exit with status 0.

- [x] **Step 7: Commit the algebra layer**

```bash
git add PrimeNumberTheorem/QPowerDetectorAlgebra.lean Test/QPowerDetectorAlgebraContract.lean
git commit -m "feat: construct normalized q-power detector"
```

### Task 3: Lock and prove the exact negative-mass identity

**Files:**
- Create: `Test/QPowerDetectorMassContract.lean`
- Create: `PrimeNumberTheorem/QPowerDetectorMass.lean`

**Interfaces:**
- Consumes: `normalizedQPowerPolynomial` from Task 2.
- Produces: exact positive/negative coefficient masses and the half-weighted-L1 identity at any nonnegative vanished real node.

- [x] **Step 1: Create the failing mass contract**

```lean
import PrimeNumberTheorem.QPowerDetectorMass

open Polynomial
open scoped BigOperators

namespace PrimeNumberTheorem.PrimeSideDetector

#check (polynomialPositiveMassAt : Real → Polynomial Real → Real)
#check (polynomialNegativeMassAt : Real → Polynomial Real → Real)
#check (polynomialWeightedL1At : Real → Polynomial Real → Real)

#check (polynomial_eval_eq_positive_sub_negative :
  forall (r : Real) (p : Polynomial Real),
    p.eval r = polynomialPositiveMassAt r p -
      polynomialNegativeMassAt r p)

#check (@polynomialNegativeMassAt_eq_half_weightedL1At :
  forall {r : Real} {p : Polynomial Real},
    0 ≤ r → p.eval r = 0 →
    polynomialNegativeMassAt r p = polynomialWeightedL1At r p / 2)

#check (@normalizedQPowerPolynomial_negativeMass_eq_half :
  forall {q : Nat} {realNodes : Finset Real}
      {pairNodes : Finset Complex} {z0 : Complex},
    q ≠ 0 →
    polynomialNegativeMassAt ((q : Real)⁻¹)
        (normalizedQPowerPolynomial q realNodes pairNodes z0) =
      polynomialWeightedL1At ((q : Real)⁻¹)
        (normalizedQPowerPolynomial q realNodes pairNodes z0) / 2)

end PrimeNumberTheorem.PrimeSideDetector
```

- [x] **Step 2: Verify the mass contract fails**

Run:

```bash
LEAN_NUM_THREADS=1 lake env lean Test/QPowerDetectorMassContract.lean
```

Expected: failure because `QPowerDetectorMass` does not exist.

- [x] **Step 3: Implement coefficient masses**

```lean
def polynomialPositiveMassAt (r : Real) (p : Polynomial Real) : Real :=
  ∑ k ∈ p.support, max (p.coeff k) 0 * r ^ k

def polynomialNegativeMassAt (r : Real) (p : Polynomial Real) : Real :=
  ∑ k ∈ p.support, max (-p.coeff k) 0 * r ^ k

def polynomialWeightedL1At (r : Real) (p : Polynomial Real) : Real :=
  ∑ k ∈ p.support, |p.coeff k| * r ^ k
```

Use `Polynomial.eval_eq_sum_range` or the support-sum evaluation lemma already
available in Mathlib to prove the positive-minus-negative decomposition.

- [x] **Step 4: Prove the half-L1 identity**

For `r >= 0`, prove termwise

```text
|c| = max c 0 + max (-c) 0
```

after multiplication by `r^k`.  Combine this sum identity with vanished
evaluation, which makes positive mass equal negative mass.  Specialize it to
`normalizedQPowerPolynomial` using `normalizedQPowerPolynomial_eval_main`.

- [x] **Step 5: Run focused source and contract checks**

```bash
LEAN_NUM_THREADS=1 lake env lean PrimeNumberTheorem/QPowerDetectorMass.lean
LEAN_NUM_THREADS=1 lake env lean Test/QPowerDetectorMassContract.lean
```

Expected: both exit with status 0.

- [x] **Step 6: Commit the exact mass layer**

```bash
git add PrimeNumberTheorem/QPowerDetectorMass.lean Test/QPowerDetectorMassContract.lean
git commit -m "feat: quantify q-power detector negative mass"
```

### Task 4: Prove the explicit product bound

**Files:**
- Modify: `PrimeNumberTheorem/QPowerDetectorMass.lean`
- Modify: `Test/QPowerDetectorMassContract.lean`

**Interfaces:**
- Consumes: `polynomialWeightedL1At`, factor constructors, and normalized polynomial data.
- Produces: a closed-form coefficient-loss bound expressed only through the interpolation coefficients, real nodes, pair nodes, and `q`.

- [x] **Step 1: Extend the failing contract with the norm inequalities**

Add exact checks for:

```lean
#check (@polynomialWeightedL1At_mul_le :
  forall {r : Real} (hr : 0 ≤ r) (p q : Polynomial Real),
    polynomialWeightedL1At r (p * q) ≤
      polynomialWeightedL1At r p * polynomialWeightedL1At r q)

#check (polynomialWeightedL1At_realNodeFactor_le :
  forall {r : Real}, 0 ≤ r → forall u : Real,
    polynomialWeightedL1At r (realNodeFactor u) ≤ r + |u|)

#check (polynomialWeightedL1At_conjugatePairFactor_le :
  forall {r : Real}, 0 ≤ r → forall z : Complex,
    polynomialWeightedL1At r (conjugatePairFactor z) ≤ (r + Complex.abs z) ^ 2)
```

Also lock a final theorem named
`normalizedQPowerPolynomial_weightedL1_le` whose right-hand side is

```text
polynomialWeightedL1At r
    (realLinearInterpolator z0
      (evalRealPolynomial (qPowerAnnihilator q realNodes pairNodes) z0)⁻¹)
  * (r + ((q : Real)⁻¹))
  * (∏ u ∈ realNodes, (r + |u|))
  * (∏ z ∈ pairNodes, (r + Complex.abs z) ^ 2).
```

- [x] **Step 2: Verify the extended contract fails**

Run:

```bash
LEAN_NUM_THREADS=1 lake env lean Test/QPowerDetectorMassContract.lean
```

Expected: failure only on the newly introduced theorem names.

- [x] **Step 3: Prove weighted-L1 submultiplicativity**

Expand product coefficients with `Polynomial.coeff_mul`, bound each convolution
term by the triangle inequality, and exchange the finite sums.  Use `r >= 0`
to rewrite `r^(i+j)` as `r^i * r^j` without changing signs.

- [x] **Step 4: Prove factor bounds**

For `realNodeFactor`, inspect coefficients in degrees zero and one.  For
`conjugatePairFactor`, inspect degrees zero through two and use

```text
|re z| <= abs z,
normSq z = (abs z)^2.
```

The resulting quadratic coefficient bound is exactly bounded by
`(r + abs z)^2`.

- [x] **Step 5: Assemble the normalized detector bound**

Apply submultiplicativity to the annihilator products and the real linear
interpolator.  Use `Finset.prod_le_prod` with nonnegative factors to obtain
`normalizedQPowerPolynomial_weightedL1_le`.

- [x] **Step 6: Run focused source and contract checks**

```bash
LEAN_NUM_THREADS=1 lake env lean PrimeNumberTheorem/QPowerDetectorMass.lean
LEAN_NUM_THREADS=1 lake env lean Test/QPowerDetectorMassContract.lean
```

Expected: both exit with status 0.

- [x] **Step 7: Commit the explicit bound**

```bash
git add PrimeNumberTheorem/QPowerDetectorMass.lean Test/QPowerDetectorMassContract.lean
git commit -m "feat: bound q-power detector coefficient loss"
```

### Task 5: Wire exact contracts and axiom audits

**Files:**
- Create: `Test/QPowerDetectorAxiomAudit.lean`
- Modify: `Test/MultiplicityAxiomAudit.lean`
- Modify: `scripts/check_axiom_allowlist.py`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: all public theorems from Tasks 2-4.
- Produces: focused build targets, exact type locks, and standard-axiom evidence.

- [x] **Step 1: Add every public theorem to the dedicated audit**

Create `Test/QPowerDetectorAxiomAudit.lean` importing both new source modules
and add one `#print axioms` command for every public theorem named in both
contracts.  Definitions do not need `#print axioms` entries.

- [x] **Step 2: Wire Lake targets and central audit imports**

Add the two source modules beside `PrimeSideDetectorMainPole` in `lakefile.lean`.
Add the two contracts and dedicated audit beside the existing prime-side
detector tests.  Import both source modules in `Test/MultiplicityAxiomAudit.lean`
and append the same theorem list used by the dedicated audit.

- [x] **Step 3: Extend the central allowlist**

Add `Test.QPowerDetectorAxiomAudit` to the audit-module list in
`scripts/check_axiom_allowlist.py`.  Add every public theorem's fully qualified
name under `PrimeNumberTheorem.PrimeSideDetector` to the declaration allowlist.

- [x] **Step 4: Run focused builds serially**

After confirming global Lean is idle, run:

```bash
LEAN_NUM_THREADS=1 lake build +PrimeNumberTheorem.QPowerDetectorAlgebra:olean
LEAN_NUM_THREADS=1 lake build +PrimeNumberTheorem.QPowerDetectorMass:olean
LEAN_NUM_THREADS=1 lake build +Test.QPowerDetectorAlgebraContract:olean
LEAN_NUM_THREADS=1 lake build +Test.QPowerDetectorMassContract:olean
LEAN_NUM_THREADS=1 lake build +Test.QPowerDetectorAxiomAudit:olean
```

Expected: every command exits with status 0 and at most one Lean child is
active at any time.

- [x] **Step 5: Run the allowlist parser and central audit**

```bash
python3 scripts/check_axiom_allowlist.py
LEAN_NUM_THREADS=1 lake build +Test.MultiplicityAxiomAudit:olean
```

Expected: the parser reports no missing or stale declarations, and the central
audit exits with status 0.  If another task starts Lean, stop only this branch's
process and resume later from cache.

- [x] **Step 6: Commit audit wiring**

```bash
git add lakefile.lean Test/MultiplicityAxiomAudit.lean \
  Test/QPowerDetectorAxiomAudit.lean scripts/check_axiom_allowlist.py
git commit -m "test: audit q-power detector theorems"
```

### Task 6: Close the boundary note and verify the branch

**Files:**
- Modify: `docs/research/vk-edge-prime-side-q-power-detector-design.md`

**Interfaces:**
- Consumes: verified theorem names and actual axiom output.
- Produces: an honest milestone record and a reviewable small stacked PR.

- [x] **Step 1: Update the research note with exact proved results**

Record:

- the exact target normalization and annihilation theorems;
- the exact half-weighted-L1 identity;
- the explicit product bound;
- the selected-base theorem and real zeta response are not included;
- no strict `response - loss > 0` theorem has been claimed unless it was
  actually proved in a later independent plan.

- [ ] **Step 2: Run static baseline verification**

```bash
rg -n "sorry|admit|^axiom " PrimeNumberTheorem/QPowerDetectorAlgebra.lean \
  PrimeNumberTheorem/QPowerDetectorMass.lean Test/QPowerDetector*.lean
./scripts/verify-baseline.sh
git diff --check
git status --short
```

Expected: no forbidden placeholder or project axiom in the new files, baseline
verification passes, no whitespace error, and only intentional documentation
changes remain.

Focused/static verification and `git diff --check` passed.  The no-target full
repository baseline did not complete: it exited during ordinary build progress
near `8515/9191`, without a theorem error in the captured tail.  Keep this item
open; do not reinterpret the interrupted full rebuild as either a mathematical
failure or a completed baseline.

- [ ] **Step 3: Commit the verified boundary note**

```bash
git add docs/research/vk-edge-prime-side-q-power-detector-design.md
git commit -m "docs: record q-power detector boundary"
```

- [ ] **Step 4: Review branch scope**

```bash
git diff --stat research/vk-edge-prime-side-detector...HEAD
git log --oneline research/vk-edge-prime-side-detector..HEAD
```

Expected: only the two focused source modules, three test modules, central
wiring, one design note, and this plan are present.  No Gate B or unrelated
VK-edge file is modified.

## Self-Review

- Spec coverage: this plan implements the parameterized algebra and mass
  layers, including exact annihilation, target normalization, exact negative
  mass, and a closed-form product bound.
- Deliberate exclusions: collision-free integer base selection and the real
  zeta response-minus-loss inequality require separate mathematical review and
  separate PRs.
- Type consistency: both contracts use the namespace
  `PrimeNumberTheorem.PrimeSideDetector`; later tasks consume the exact names
  introduced in earlier tasks.
- Claim boundary: no task produces a repeatable Sharp surplus, Carlson growth,
  or RH statement.
