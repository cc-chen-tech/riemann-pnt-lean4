# Pintz--Carlson PNT Error Bridge Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Bound the actual normalized `chebyshevPsi0` error by the proved Pintz--Carlson finite-zero aggregate plus explicit contour, compact, and real-ordinate residuals at honestly selected good heights.

**Architecture:** A fixed-height certificate records exactly the truncated contour formula. A pure triangle-inequality theorem injects the existing finite-zero-sum bridge. A separate adapter converts the existing short-interval good-height theorem into these certificates, and a natural-point dynamic package evaluates them along `T(m)` without claiming a real-height formula.

**Tech Stack:** Lean 4, Mathlib complex norm and finite-sum APIs, existing `CofinalExplicitFormula`, `PNTFiniteZeroSum`, and `ZeroDensityLayerBudget*` modules.

## Global Constraints

- Never modify or stage `PrimeNumberTheorem/ZeroForcedOscillationComplementaryBound.lean`.
- Never modify VK-edge files or `research/zero-forced-oscillation-next`.
- Preserve real-ordinate, finite trivial-zero, logarithmic-derivative, and contour residuals explicitly.
- Do not claim a formula at every real height, a new numerical density exponent, RH, or unconditional `Omega_plus_minus`.
- Every public theorem receives a contract and `#print axioms` audit.

---

### Task 1: Fixed-height truncated PNT error certificate

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetPNTErrorBridge.lean`
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetPNTErrorBridgeContract.lean`
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetPNTErrorBridgeAxiomAudit.lean`

**Interfaces:**
- Consumes: `sum_pntFiniteZeroContribution_eq_neg_finiteNontrivialZeroSumWithMultiplicity`
- Consumes: `PositiveZeroBucketInput.norm_finiteNontrivialZeroSumWithMultiplicity_le_pintz`
- Produces: `TruncatedPNTErrorCertificate`
- Produces: `TruncatedPNTErrorCertificate.abs_chebyshevPsi0_sub_id_le`
- Produces: `TruncatedPNTErrorCertificate.abs_chebyshevPsi0_sub_id_le_pintz`
- Produces: `TruncatedPNTErrorCertificate.abs_relativeChebyshevPsi0Error_le_pintz`

- [ ] **Step 1: Define the fixed-height certificate and normalized error**

```lean
noncomputable def relativeChebyshevPsi0Error (x : ℝ) : ℝ :=
  (chebyshevPsi0 x - x) / x

structure TruncatedPNTErrorCertificate (x T : ℝ) : Type where
  trivialContribution : ℂ
  remainderBound : ℝ
  remainder_nonneg : 0 ≤ remainderBound
  formula_bound :
    ‖trivialContribution +
        ((x : ℂ) - deriv riemannZeta 0 / riemannZeta 0 +
          ∑ rho ∈ nontrivialZerosFinset T,
            pntFiniteZeroContribution x rho) -
        (chebyshevPsi0 x : ℂ)‖ ≤ remainderBound
```

- [ ] **Step 2: Prove the algebraic transfer**

Rewrite the per-zero sum using
`sum_pntFiniteZeroContribution_eq_neg_finiteNontrivialZeroSumWithMultiplicity`.
Rearrange the formula error to

```lean
((chebyshevPsi0 x - x : ℝ) : ℂ) =
  -formulaError + trivialContribution -
    deriv riemannZeta 0 / riemannZeta 0 -
    finiteNontrivialZeroSumWithMultiplicity x T
```

and apply `norm_add_le`/`norm_sub_le` to obtain

```lean
|chebyshevPsi0 x - x| ≤
  ‖finiteNontrivialZeroSumWithMultiplicity x T‖ +
  ‖deriv riemannZeta 0 / riemannZeta 0‖ +
  ‖certificate.trivialContribution‖ +
  certificate.remainderBound
```

- [ ] **Step 3: Inject the Pintz--Carlson finite-zero bound**

For `input : PositiveZeroBucketInput T n` and `hx : 1 ≤ x`, combine Step 2
with `input.norm_finiteNontrivialZeroSumWithMultiplicity_le_pintz hx`.
The theorem conclusion is:

```lean
|chebyshevPsi0 x - x| ≤
  x * (2 * pintzCarlsonClassicalAggregatedDensityLayerTerm
      (Finset.univ : Finset (Fin n)) input.sigma () x T +
    ‖∑ rho ∈ realOrdinateNontrivialZerosFinset T,
      pntRelativeZeroContribution x rho‖) +
  ‖deriv riemannZeta 0 / riemannZeta 0‖ +
  ‖certificate.trivialContribution‖ +
  certificate.remainderBound
```

- [ ] **Step 4: Normalize by positive `x`**

Use `abs_div`, `abs_of_pos`, and `div_le_iff₀` to prove:

```lean
|relativeChebyshevPsi0Error x| ≤
  2 * pintzCarlsonClassicalAggregatedDensityLayerTerm ... +
  ‖realOrdinateRelativeSum‖ +
  (‖deriv riemannZeta 0 / riemannZeta 0‖ +
    ‖certificate.trivialContribution‖ +
    certificate.remainderBound) / x
```

- [ ] **Step 5: Add contract and independent axiom audit**

The contract contains `#check` for the structure, normalized error, and three
public transfer theorems. The audit contains matching `#print axioms`.

- [ ] **Step 6: Build and commit Task 1**

Run:

```bash
lake build PrimeNumberTheorem.ZeroDensityLayerBudgetPNTErrorBridge
lake build PrimeNumberTheorem.ZeroDensityLayerBudgetPNTErrorBridgeContract \
  PrimeNumberTheorem.ZeroDensityLayerBudgetPNTErrorBridgeAxiomAudit
```

Expected: both builds complete successfully; printed axioms contain only
`propext`, `Classical.choice`, and `Quot.sound`.

Commit:

```bash
git add PrimeNumberTheorem/ZeroDensityLayerBudgetPNTErrorBridge*.lean
git commit -m "feat: transfer Pintz zero bounds to PNT error"
```

### Task 2: Existing good-height theorem adapter

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetPNTGoodHeightAdapter.lean`
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetPNTGoodHeightAdapterContract.lean`
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetPNTGoodHeightAdapterAxiomAudit.lean`

**Interfaces:**
- Consumes: `ExplicitFormulaResidues.exists_uniform_goodHeight_Icc_norm_nat_movingRight_truncatedExplicitFormula_sub_chebyshevPsi0_le`
- Produces: `cofinalTrivialZeroContribution`
- Produces: `cofinalPNTFormulaRemainderBound`
- Produces: `exists_uniform_goodHeight_truncatedPNTErrorCertificate`

- [ ] **Step 1: Define the exact trivial and remainder terms**

```lean
noncomputable def cofinalTrivialZeroContribution (m N : ℕ) : ℂ :=
  ∑ p ∈ ExplicitFormulaAux.finiteTrivialZeroSum (2 * (N : ℝ)),
    -((((m : ℝ) : ℂ) ^ p) / p)
```

Define `cofinalPNTFormulaRemainderBound C A T m N` by copying exactly the
right-hand side of the existing good-height theorem:

```lean
C * (m : ℝ) *
    ((1 + Real.log (m : ℝ)) ^ 2 +
      (1 + Real.log (A + 6)) ^ 2) / T +
  (((ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 +
      ‖Complex.log Real.pi‖ +
      2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
        Real.log (2 * (N : ℝ) + T + 4)) + Real.pi) *
      (m : ℝ) ^ (-(2 * (N : ℝ) + 1))) * (2 * T)) /
    (2 * Real.pi)
```

- [ ] **Step 2: Convert the existing theorem to certificates**

Prove:

```lean
∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 8 ≤ A →
  ∃ T ∈ Set.Icc A (A + 1),
    ExplicitFormulaAux.goodHeight T ∧
    ∀ m N : ℕ, 3 ≤ m →
      TruncatedPNTErrorCertificate (m : ℝ) T
```

The certificate uses `cofinalTrivialZeroContribution m N` and
`cofinalPNTFormulaRemainderBound C A T m N`. Prove remainder nonnegativity
from `C ≥ 0`, `m ≥ 3`, `A ≥ 8`, `T ≥ A`, and positivity of the remaining
factors. Prove `formula_bound` by `simpa` after unfolding
`pntFiniteZeroContribution` and `pntExplicitFormulaZeroTerm`.

- [ ] **Step 3: Add contract, audit, focused build, and commit**

Run:

```bash
lake build PrimeNumberTheorem.ZeroDensityLayerBudgetPNTGoodHeightAdapter
lake build PrimeNumberTheorem.ZeroDensityLayerBudgetPNTGoodHeightAdapterContract \
  PrimeNumberTheorem.ZeroDensityLayerBudgetPNTGoodHeightAdapterAxiomAudit
```

Commit:

```bash
git add PrimeNumberTheorem/ZeroDensityLayerBudgetPNTGoodHeightAdapter*.lean
git commit -m "feat: adapt cofinal good heights to PNT certificates"
```

### Task 3: Natural-point dynamic upper package

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetPNTDynamicUpper.lean`
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetPNTDynamicUpperContract.lean`
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetPNTDynamicUpperAxiomAudit.lean`

**Interfaces:**
- Consumes: `TruncatedPNTErrorCertificate.abs_relativeChebyshevPsi0Error_le_pintz`
- Produces: `NatDynamicPintzCarlsonPNTUpperInput`
- Produces: `NatDynamicPintzCarlsonPNTUpperInput.relative_error_bound`

- [ ] **Step 1: Define the dynamic natural-point input**

```lean
structure NatDynamicPintzCarlsonPNTUpperInput
    (height : ℕ → ℝ) (n : ℕ) : Type where
  bucket : ∀ m, PositiveZeroBucketInput (height m) n
  formula :
    ∀ m, 3 ≤ m →
      TruncatedPNTErrorCertificate (m : ℝ) (height m)
```

- [ ] **Step 2: Prove the pointwise dynamic bound**

For `3 ≤ m`, apply the fixed-height normalized theorem at
`x = (m : ℝ)`, `T = height m`, `bucket m`, and `formula m hm`.
Use `exact_mod_cast` to prove `1 ≤ (m : ℝ)`.

- [ ] **Step 3: Add contract, audit, focused build, and commit**

Run:

```bash
lake build PrimeNumberTheorem.ZeroDensityLayerBudgetPNTDynamicUpper
lake build PrimeNumberTheorem.ZeroDensityLayerBudgetPNTDynamicUpperContract \
  PrimeNumberTheorem.ZeroDensityLayerBudgetPNTDynamicUpperAxiomAudit
```

Commit:

```bash
git add PrimeNumberTheorem/ZeroDensityLayerBudgetPNTDynamicUpper*.lean
git commit -m "feat: add dynamic natural PNT upper package"
```

### Task 4: Public facade and aggregate audit

**Files:**
- Modify: `PrimeNumberTheorem/ZeroForcingUnifiedTransfer.lean`
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetAxiomAudit.lean`

**Interfaces:**
- Produces: public imports for all three new modules
- Produces: aggregate axiom evidence for all new theorem chains

- [ ] **Step 1: Add facade imports and aggregate audit entries**

Import the three modules in dependency order. Add `#print axioms` lines for:

```text
TruncatedPNTErrorCertificate.abs_chebyshevPsi0_sub_id_le
TruncatedPNTErrorCertificate.abs_chebyshevPsi0_sub_id_le_pintz
TruncatedPNTErrorCertificate.abs_relativeChebyshevPsi0Error_le_pintz
exists_uniform_goodHeight_truncatedPNTErrorCertificate
NatDynamicPintzCarlsonPNTUpperInput.relative_error_bound
```

- [ ] **Step 2: Run facade and aggregate validation**

Run:

```bash
lake build PrimeNumberTheorem.ZeroForcingUnifiedTransfer \
  PrimeNumberTheorem.ZeroDensityLayerBudgetAxiomAudit
```

Expected: successful build and no `sorryAx` in any new public theorem.

- [ ] **Step 3: Commit facade registration**

```bash
git add PrimeNumberTheorem/ZeroForcingUnifiedTransfer.lean \
  PrimeNumberTheorem/ZeroDensityLayerBudgetAxiomAudit.lean
git commit -m "feat: expose PNT error transfer bridge"
```

## Plan Self-Review

- The fixed-height theorem is separated from height existence.
- The good-height adapter preserves the exact `T ∈ [A, A + 1]` conclusion.
- The dynamic package is indexed by natural sample points because the current
  uniform contour theorem assumes `m : Nat`.
- Every residual remains visible.
- No task modifies an overlapping ownership path.
- Every produced public theorem has a named validation target.
