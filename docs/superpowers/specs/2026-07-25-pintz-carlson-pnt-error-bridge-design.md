# Pintz--Carlson PNT Error Bridge Design

## Purpose

Connect the proved Pintz--Carlson bound for
`finiteNontrivialZeroSumWithMultiplicity` to the actual normalized
prime-number-theorem error

```text
(chebyshevPsi0 x - x) / x.
```

The bridge must preserve the exact logical boundary of the existing contour
theorems: the project supplies a good height in a short interval, not a
truncated explicit formula at every real height. Real-ordinate zero
contributions, finite trivial-zero terms, the logarithmic-derivative constant,
and contour remainders remain explicit until separately bounded.

## Existing Inputs

- `ZeroDensityLayerBudgetFiniteZeroSumBridge.lean` proves
  `PositiveZeroBucketInput.norm_finiteNontrivialZeroSumWithMultiplicity_le_pintz`.
- `CofinalExplicitFormula.lean` proves
  `exists_uniform_goodHeight_Icc_norm_nat_movingRight_truncatedExplicitFormula_sub_chebyshevPsi0_le`.
- `ZeroDensityLayerBudgetBidirectional.lean` defines
  `DynamicExplicitFormulaUpperCertificate`.
- `ZeroDensityLayerBudgetDynamic.lean` and the finite-grid modules provide
  dynamic-height schedules and optimizer certificates.

The implementation does not alter
`ZeroForcedOscillationComplementaryBound.lean`, its audits, or any VK-edge
module.

## Chosen Architecture

### 1. Fixed-height error certificate

Create `ZeroDensityLayerBudgetPNTErrorBridge.lean` with a structure

```lean
structure TruncatedPNTErrorCertificate (x T : Real) where
  trivialContribution : Complex
  remainderBound : Real
  remainder_nonneg : 0 <= remainderBound
  formula_bound :
    norm
      (trivialContribution +
        ((x : Complex) -
          deriv riemannZeta 0 / riemannZeta 0 +
          sum rho in nontrivialZerosFinset T,
            pntFiniteZeroContribution x rho) -
        (chebyshevPsi0 x : Complex)) <=
      remainderBound
```

This records exactly the form supplied by the existing contour theorem.
It does not assert that every `T` is good.

### 2. Algebraic transfer to the real PNT error

Prove that a certificate implies

```text
abs (chebyshevPsi0 x - x)
  <= norm (finiteNontrivialZeroSumWithMultiplicity x T)
     + norm (deriv riemannZeta 0 / riemannZeta 0)
     + norm trivialContribution
     + remainderBound.
```

The proof is only rearrangement and triangle inequalities. It must reuse
`sum_pntFiniteZeroContribution_eq_neg_finiteNontrivialZeroSumWithMultiplicity`
rather than duplicate the finite-sum conversion.

### 3. Pintz--Carlson injection

For `input : PositiveZeroBucketInput T n` and `1 <= x`, combine the algebraic
transfer with
`input.norm_finiteNontrivialZeroSumWithMultiplicity_le_pintz`.
The resulting theorem bounds the actual PNT error by

```text
x * (2 * aggregatedDensityLayerTerm + realOrdinateResidual)
  + logarithmicDerivativeConstant
  + norm trivialContribution
  + remainderBound.
```

After division by positive `x`, expose a normalized theorem whose right-hand
side consists of:

- twice the Pintz--Carlson density aggregate;
- the real-ordinate relative zero residual;
- the compact and contour terms divided by `x`.

### 4. Dynamic schedule package

Create a second focused module
`ZeroDensityLayerBudgetPNTDynamicUpper.lean` only after the fixed-height
bridge is validated. It will package:

```lean
structure DynamicPintzCarlsonPNTUpperInput (height : Real -> Real) (n : Nat)
```

with fields supplying, for every relevant `x`:

- `PositiveZeroBucketInput (height x) n`;
- `TruncatedPNTErrorCertificate x (height x)`;
- the lower bound `1 <= x`.

Its public theorem produces a pointwise normalized PNT upper bound and an
adapter to `DynamicExplicitFormulaUpperCertificate` once decay of the
real-ordinate, trivial-zero, and contour terms is supplied.

### 5. Good-height adapter

The cofinal contour theorem selects

```text
T in [A, A + 1]
```

for each `A >= 8`. The adapter will therefore return an existential
good-height certificate. It will not manufacture a formula certificate at an
arbitrary requested height. A future dynamic selector may choose the returned
height using classical choice or a finite optimizer, but the existential
boundary remains visible in theorem statements.

## Alternatives Rejected

### Prove real-axis nonvanishing first

This would remove the real-ordinate residual but requires a separate
formalization of zeta nonvanishing on the real interval `0 < sigma < 1`.
The repository currently has no reusable theorem with that statement. It is
classical support work rather than the dynamic transfer innovation, so it is
deferred.

### Inline the entire PNT finite-zero proof

`PNTFiniteZeroSum.lean` contains a long theorem specialized to a particular
choice of height and asymptotic scale. Copying its local decomposition would
duplicate contour arithmetic and obscure which input is replaceable by a
stronger zero-density estimate. The certificate interface isolates exactly
that replaceable boundary.

### Claim a formula at every dynamic height

The current contour result proves existence of a good height in a unit
interval. Treating it as an arbitrary-height theorem would be a false
strengthening. The good-height adapter therefore remains existential.

## Verification

Each new module receives:

- a focused contract with `#check` for every public theorem;
- an independent `#print axioms` audit;
- registration in `ZeroForcingUnifiedTransfer.lean`;
- registration in `ZeroDensityLayerBudgetAxiomAudit.lean`.

Validation order:

1. focused build of the fixed-height bridge;
2. fixed-height contract and independent axiom audit;
3. focused build of the dynamic package;
4. dynamic contract and independent axiom audit;
5. facade and aggregate axiom audit.

The accepted axiom footprint is the existing standard
`[propext, Classical.choice, Quot.sound]`. Any `sorryAx` is a failure.

## Completion Boundary

This bridge is complete when the actual normalized `chebyshevPsi0` error is
bounded by the Pintz--Carlson aggregate plus explicit residuals along an
honestly selected good-height schedule.

It does not by itself:

- prove the real-axis residual vanishes;
- prove every height is good;
- establish a new numerical zero-density exponent;
- prove an unconditional signed oscillation theorem;
- imply RH.
