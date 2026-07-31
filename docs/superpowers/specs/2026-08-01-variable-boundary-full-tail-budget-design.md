# Variable-Boundary Full-Tail Budget Design

## Goal

Replace the sufficient but overly strong single-tail majorization interface of
stack104 with the constant-correct decomposition of the complete moving zeta
complement into positive, negative, and real-ordinate parts.

## Correct budget

For the moving equal-real-part package and target amplitude `A_m`, conjugation
gives

```text
|signed complement m| / A_m
  <= 2 * positiveNormalized m + realNormalized m.
```

The positive normalized term is then compared with

```text
lowMajorant m + variableBoundaryVisibleNormalizedKernelTail H beta m.
```

Thus decay of the low majorant, stack101 visible-tail decay, and decay of the
real-ordinate normalized tail imply decay of the complete signed complement.

## Public interfaces

- `variableBoundaryPositiveNormalizedSum`
- `variableBoundaryRealNormalizedSum`
- `VariableBoundaryVisiblePositiveTailMajorized`
- `abs_variableBoundaryComplement_div_le_two_positive_add_real`
- `variableBoundaryFullComplement_targetAmplitudeNegligible`
- `actualVariableBoundaryFullTailExplicitFormulaResidual_targetAmplitudeNegligible`

## Remaining concrete gaps

This stack does not yet prove the positive high-strip Finset-to-Carlson-index
comparison or moving real-ordinate decay. It names those two inputs separately
so neither is hidden by a full-complement certificate.

## Claim boundary

The result supplies the exact residual required by the existing moving PNT
sign-alternative assembler under the stated tail inputs. It does not construct
the moving main witness, prove both signs, or imply RH.
