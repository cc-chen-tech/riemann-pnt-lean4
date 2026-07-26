# VK-edge Residual Amplification Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize the exact local second-moment budget of one zeta zero and its conjugate, prove a reusable reverse-triangle residual-energy theorem, and certify that the repository's current swept \(L^2\) lower bound is too small to force any additional zero contribution.

**Architecture:** Put the zeta-independent Hilbert-space argument in `MathlibAux/ResidualSecondMoment.lean`. Put the cosine-pair calculation, normalized target pair, residual definitions, constant comparison, and conditional zeta endpoint in `PrimeNumberTheorem/VKEdgeResidualAmplification.lean`. Fix every public signature with contract modules and audit public theorem axioms separately.

**Tech Stack:** Lean 4, Mathlib measure theory and `Lp` spaces, interval integrals, existing VK-edge swept \(L^2\) infrastructure, Lake contract targets, shell verification scripts.

## Global Constraints

- Work only in `/Users/luicy/AI/Riemann/riemann-pnt-lean4/.worktrees/vk-edge-residual-amplification` on `research/vk-edge-residual-amplification`.
- Do not modify `main`, `research/zero-forced-oscillation-next`, density/transfer shared cores, or the existing PR #24 files except for adding imports through the new module when strictly needed.
- Do not add `sorry`, `admit`, `axiom`, or a theorem-shaped `def ... : Prop`.
- Do not claim an additional zero, a zero-density contradiction, or RH. The unconditional result of this branch is an obstruction theorem.
- Add failing contract checks before implementation and commit after each passing task.
- Public zeta endpoints must retain analytic multiplicity through `analyticOrderNatAt riemannZeta rho`.

---

## Task 1: Generic Residual Second-Moment Interface

**Files:**
- Create: `MathlibAux/ResidualSecondMoment.lean`
- Create: `Test/ResidualSecondMomentContract.lean`
- Modify: `lakefile.lean`

- [x] Add `Test/ResidualSecondMomentContract.lean` with a `#check` for:

```lean
MathlibAux.integral_sq_sub_lower_of_integral_sq_bounds
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f p : α → ℝ} {A B L : ℝ}
    (hf : MemLp f 2 μ)
    (hp : MemLp p 2 μ)
    (hL : 0 ≤ L)
    (hA : 0 ≤ A)
    (hB : 0 ≤ B)
    (hAB : B < A)
    (hF : A * L ≤ ∫ x, f x ^ 2 ∂μ)
    (hP : (∫ x, p x ^ 2 ∂μ) ≤ B * L) :
    (Real.sqrt A - Real.sqrt B) ^ 2 * L ≤
      ∫ x, (f x - p x) ^ 2 ∂μ
```

- [x] Add the contract target to `lakefile.lean` and run:

```bash
lake build Test.ResidualSecondMomentContract
```

Expected result: failure because the module and theorem do not exist.

- [x] Implement `MathlibAux/ResidualSecondMoment.lean` using `MemLp.toLp`, `MemLp.toLp_sub`, the norm triangle inequality, and the identity between the \(L^2\) norm squared and `∫ x, f x ^ 2 ∂μ`.

- [x] If Mathlib's `Lp` coercions make the direct scaled theorem brittle, first expose and prove:

```lean
theorem sqrt_integral_sq_sub_lower
    (hf : MemLp f 2 μ) (hp : MemLp p 2 μ) :
    Real.sqrt (∫ x, f x ^ 2 ∂μ) -
        Real.sqrt (∫ x, p x ^ 2 ∂μ) ≤
      Real.sqrt (∫ x, (f x - p x) ^ 2 ∂μ)
```

and derive the scaled theorem by monotonicity of `Real.sqrt`, nonnegativity of square integrals, and squaring nonnegative sides.

- [x] Run:

```bash
lake build Test.ResidualSecondMomentContract
git diff --check
```

- [x] Commit:

```bash
git add MathlibAux/ResidualSecondMoment.lean Test/ResidualSecondMomentContract.lean lakefile.lean
git commit -m "feat: formalize residual second-moment lower bound"
```

## Task 2: Exact Cosine-Pair Energy

**Files:**
- Create: `PrimeNumberTheorem/VKEdgeResidualAmplification.lean`
- Create: `Test/VKEdgeResidualAmplificationContract.lean`
- Modify: `lakefile.lean`

- [x] Add contract checks for:

```lean
PrimeNumberTheorem.VKEdgePiOverTwo.cosineZeroPair

PrimeNumberTheorem.VKEdgePiOverTwo.intervalIntegral_cosineZeroPair_sq
    {m gamma phase a b : ℝ} (hgamma : gamma ≠ 0) :
    (∫ y in a..b, cosineZeroPair m gamma phase y ^ 2) =
      2 * m ^ 2 * (b - a) +
        m ^ 2 / gamma *
          (Real.sin (2 * gamma * b - 2 * phase) -
            Real.sin (2 * gamma * a - 2 * phase))

PrimeNumberTheorem.VKEdgePiOverTwo.integral_Icc_cosineZeroPair_sq_le
    {m gamma phase a b : ℝ}
    (hab : a ≤ b) (hgamma : gamma ≠ 0) :
    (∫ y in Set.Icc a b, cosineZeroPair m gamma phase y ^ 2) ≤
      2 * m ^ 2 * (b - a) + 2 * m ^ 2 / |gamma|
```

- [x] Add the source and contract targets to `lakefile.lean`, then run the contract and confirm it fails.

- [x] Define:

```lean
def cosineZeroPair (m gamma phase y : ℝ) : ℝ :=
  -2 * m * Real.cos (gamma * y - phase)
```

- [x] Prove the exact interval identity by differentiating:

```lean
fun y =>
  2 * m ^ 2 * y +
    m ^ 2 / gamma * Real.sin (2 * gamma * y - 2 * phase)
```

with `intervalIntegral.integral_eq_sub_of_hasDerivAt`.

- [x] Convert the interval integral to the `Set.Icc` integral with `intervalIntegral.integral_of_le hab`. Bound the sine difference by `2`, preserving the factor `m ^ 2 / |gamma|`.

- [x] Run:

```bash
lake build Test.VKEdgeResidualAmplificationContract
git diff --check
```

- [x] Commit:

```bash
git add PrimeNumberTheorem/VKEdgeResidualAmplification.lean Test/VKEdgeResidualAmplificationContract.lean lakefile.lean
git commit -m "feat: compute target zero-pair local energy"
```

## Task 3: Normalized Zeta Target Pair and Residual

**Files:**
- Modify: `PrimeNumberTheorem/VKEdgeResidualAmplification.lean`
- Modify: `Test/VKEdgeResidualAmplificationContract.lean`

- [x] Extend the contract with:

```lean
PrimeNumberTheorem.VKEdgePiOverTwo.normalizedTargetZeroPair
PrimeNumberTheorem.VKEdgePiOverTwo.normalizedPsiResidual
PrimeNumberTheorem.VKEdgePiOverTwo.measurable_normalizedTargetZeroPair
PrimeNumberTheorem.VKEdgePiOverTwo.measurable_normalizedPsiResidual
PrimeNumberTheorem.VKEdgePiOverTwo.integrableOn_normalizedTargetZeroPair_sq_Icc
PrimeNumberTheorem.VKEdgePiOverTwo.integrableOn_normalizedPsiResidual_sq_Icc
```

using definitions:

```lean
def normalizedTargetZeroPair (rho : ℂ) (y : ℝ) : ℝ :=
  cosineZeroPair
    (analyticOrderNatAt riemannZeta rho : ℝ)
    rho.im rho.arg y

def normalizedPsiResidual (rho : ℂ) (y : ℝ) : ℝ :=
  normalizedPsiError rho y - normalizedTargetZeroPair rho y
```

- [x] Confirm the extended contract fails, then implement the definitions.

- [x] Prove measurability from continuity of `Real.cos`, the existing definition of `normalizedPsiError`, and closure under subtraction.

- [x] Prove interval integrability of both squares on `Icc a b`. Use continuity for the target pair and the existing exponential-growth bound pattern for `normalizedPsiError`; derive residual integrability with `IntegrableOn.sub`.

- [x] Add the zeta-specialized target-pair bound:

```lean
theorem integral_Icc_normalizedTargetZeroPair_sq_le
    {rho : ℂ} {a b : ℝ}
    (hab : a ≤ b) (hgamma : rho.im ≠ 0) :
    (∫ y in Set.Icc a b, normalizedTargetZeroPair rho y ^ 2) ≤
      2 * (analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 * (b - a) +
        2 * (analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / |rho.im|
```

- [x] Run the focused contract and commit:

```bash
lake build Test.VKEdgeResidualAmplificationContract
git diff --check
git add PrimeNumberTheorem/VKEdgeResidualAmplification.lean Test/VKEdgeResidualAmplificationContract.lean
git commit -m "feat: define normalized zeta residual"
```

## Task 4: Prove the Current Swept Constant Is Below the Residual Gate

**Files:**
- Modify: `PrimeNumberTheorem/VKEdgeResidualAmplification.lean`
- Modify: `Test/VKEdgeResidualAmplificationContract.lean`

- [x] Add contract checks for helper inequalities:

```lean
one_div_pi_le_sharpenedMissingHarmonicDenominator
one_le_centeredSharpenedProjectedPsiKernelEnvelopeConstant
```

and the public comparison:

```lean
theorem centeredSharpenedSweptOrdinaryL2Constant_lt_targetPairHalfEnergy
    {epsilon : ℝ} {rho : ℂ} {k : ℕ}
    (hepsilon : 0 < epsilon)
    (hrho1 : rho ≠ 1)
    (hzero : riemannZeta rho = 0) :
    centeredSharpenedSweptOrdinaryL2Constant epsilon rho k <
      epsilon * (analyticOrderNatAt riemannZeta rho : ℝ) ^ 2
```

- [x] Confirm the contract fails.

- [x] Prove:

```lean
1 / Real.pi ≤ sharpenedMissingHarmonicDenominator k
```

from \((2k+1)^2 \ge 1\), positivity of `Real.pi`, and the denominator definition.

- [x] Prove:

```lean
1 ≤ centeredSharpenedProjectedPsiKernelEnvelopeConstant q rho k
```

from nonnegativity of both envelope terms.

- [x] Establish exact algebra for `epsilon / 2`:

```text
q = 64 * (epsilon + 4)^2 / epsilon^2
d = 64 * (epsilon + 4) / epsilon
q-d = 256 * (epsilon + 4) / epsilon^2
R-1 = epsilon/(epsilon+2)
```

using `field_simp`, `ring`, and positivity supplied by `hepsilon`.

- [x] Use:

```lean
ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero hrho1 hzero
Real.pi_lt_four
```

to prove:

```text
c2
  < pi * multiplicity^2 * epsilon * (epsilon+4) /
      (8*(epsilon+2))
  < epsilon * multiplicity^2.
```

- [x] Run the focused contract and commit:

```bash
lake build Test.VKEdgeResidualAmplificationContract
git diff --check
git add PrimeNumberTheorem/VKEdgeResidualAmplification.lean Test/VKEdgeResidualAmplificationContract.lean
git commit -m "theorem: certify swept L2 constant below pair energy"
```

## Task 5: Conditional Residual Endpoint

**Files:**
- Modify: `PrimeNumberTheorem/VKEdgeResidualAmplification.lean`
- Modify: `Test/VKEdgeResidualAmplificationContract.lean`

- [ ] Add a contract for an interval endpoint whose hypotheses explicitly require a total coefficient larger than the target-pair coefficient:

```lean
theorem integral_Icc_normalizedPsiResidual_sq_lower
    {rho : ℂ} {a b A B : ℝ}
    (hab : a ≤ b)
    (hgamma : rho.im ≠ 0)
    (hA : 0 ≤ A)
    (hB : 0 ≤ B)
    (hBA : B < A)
    (htotal :
      A * (b - a) ≤
        ∫ y in Set.Icc a b, normalizedPsiError rho y ^ 2)
    (hpair :
      (∫ y in Set.Icc a b, normalizedTargetZeroPair rho y ^ 2) ≤
        B * (b - a)) :
    (Real.sqrt A - Real.sqrt B) ^ 2 * (b - a) ≤
      ∫ y in Set.Icc a b, normalizedPsiResidual rho y ^ 2
```

- [ ] Confirm failure, then prove it by applying `MathlibAux.integral_sq_sub_lower_of_integral_sq_bounds` to `volume.restrict (Icc a b)`.

- [ ] Add a logarithmic-window corollary with a finite-\(\gamma\) correction in the pair coefficient:

```lean
B_Y =
  2 * multiplicity^2 +
    2 * multiplicity^2 / (abs rho.im * epsilon * log Y)
```

under `0 < epsilon`, `1 < Y`, and `rho.im ≠ 0`.

- [ ] Do not instantiate the total coefficient with `centeredSharpenedSweptOrdinaryL2Constant`; instead add a theorem or comment referencing the strict comparison from Task 4.

- [ ] Run the focused contract and commit:

```bash
lake build Test.VKEdgeResidualAmplificationContract
git diff --check
git add PrimeNumberTheorem/VKEdgeResidualAmplification.lean Test/VKEdgeResidualAmplificationContract.lean
git commit -m "feat: expose conditional zeta residual energy endpoint"
```

## Task 6: Axiom Audit and Research Record

**Files:**
- Create: `Test/VKEdgeResidualAmplificationAxiomAudit.lean`
- Create: `docs/research/vk-edge-residual-amplification-audit.md`
- Modify: `lakefile.lean`

- [ ] Add `#print axioms` for:

```lean
MathlibAux.integral_sq_sub_lower_of_integral_sq_bounds
intervalIntegral_cosineZeroPair_sq
integral_Icc_normalizedTargetZeroPair_sq_le
centeredSharpenedSweptOrdinaryL2Constant_lt_targetPairHalfEnergy
integral_Icc_normalizedPsiResidual_sq_lower
```

- [ ] Add the audit target to `lakefile.lean`.

- [ ] Record in the research audit:
  - the target-pair exact energy formula;
  - the current swept constant comparison;
  - why fixed-proportion large values do not imply another zero;
  - the precise new input needed: a total local \(L^2\) coefficient greater than the target-pair budget, or a detector annihilating the target pair while retaining a nonzero arithmetic main term;
  - that no RH or zero-density contradiction has been proved.

- [ ] Run:

```bash
lake build Test.ResidualSecondMomentContract
lake build Test.VKEdgeResidualAmplificationContract
lake build Test.VKEdgeResidualAmplificationAxiomAudit
rg -n "sorry|admit|^[[:space:]]*axiom " MathlibAux/ResidualSecondMoment.lean PrimeNumberTheorem/VKEdgeResidualAmplification.lean Test/ResidualSecondMomentContract.lean Test/VKEdgeResidualAmplificationContract.lean Test/VKEdgeResidualAmplificationAxiomAudit.lean
git diff --check
```

- [ ] Inspect the axiom output and accept only standard Lean/Mathlib logical axioms.

- [ ] Commit:

```bash
git add Test/VKEdgeResidualAmplificationAxiomAudit.lean docs/research/vk-edge-residual-amplification-audit.md lakefile.lean
git commit -m "test: audit residual zero-pair amplification gate"
```

## Task 7: Full Verification and Branch Readiness

**Files:**
- Modify only if verification reveals a defect in files created by this plan.

- [ ] Run the repository baseline:

```bash
./scripts/verify-baseline.sh
```

- [ ] Run a serialized complete build:

```bash
lake -Kjobs=1 build
```

- [ ] Confirm clean source and branch state:

```bash
git diff --check
git status --short
git log --oneline --decorate -8
```

- [ ] Compare against the PR #24 base:

```bash
git diff --stat 6cea1f4..HEAD
git diff --name-only 6cea1f4..HEAD
```

- [ ] Summarize the exact result:
  - completed: exact target-pair energy, generic residual theorem, conditional residual zeta endpoint, and formal obstruction for the existing swept constant;
  - not completed: positive residual energy, additional zeros, Carlson contradiction, or RH.

- [ ] Push only after all verification succeeds:

```bash
git push -u origin research/vk-edge-residual-amplification
```
