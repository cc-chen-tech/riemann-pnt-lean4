# Half-Sharp Balanced Full-PNT Design

## Objective

Propagate the attained Carlson endpoint from stack 32 through the selected
moving zero layers and the complete natural-point explicit formula.

The final theorem must retain all three exact relations:

```text
gapRate = classicalAdmissibleBalancedRate b / 2
halfRate = gapRate / 2
halfRate = classicalAdmissibleBalancedRate b / 4.
```

It must also show that this rate strictly improves the previous verified
`classicalAdmissibleBalancedRate b / 8` rate.

## Reuse strategy

The compensated fixed-anchor majorant from stack 32 is definitionally the
stack 31 theta majorant at `theta = 1 / 2` with coefficient

```text
D = C * exp(gapRate / 2).
```

After this coefficient conversion, the existing theta middle, positive-tail,
full-zero-tail, and explicit-formula transfer interfaces apply unchanged.
Only the bridge from the compensated fixed-anchor theorem to selected moving
masses needs a new proof.

## Theorem chain

1. Convert the stack 32 fixed-anchor coefficient to the stack 31 theta
   coefficient.
2. Bound moving middle and strip masses at `theta = 1 / 2`.
3. Add the critical-half and low-strip bounds.
4. Use conjugation and the real-ordinate finite sum to bound the full zero
   tail.
5. Apply the complete explicit formula, closed real-axis estimate, and
   closed-form contour remainder.
6. Return an eventual bound on the actual
   `relativeChebyshevPsi0Error`.

## Public declarations

- `classicalDyadicCarlsonHalfClosedFormFullPNTErrorMajorant`
- `tendsto_classicalDyadicCarlsonHalfClosedFormFullPNTErrorMajorant_zero`
- `exists_selectedClassicalAdmissibleDyadicCarlsonHalfQuantitativeMassMajorant_of_zeroFree`
- `exists_selectedBalancedClassicalAdmissibleDyadicCarlsonHalfClosedFormFullPNTErrorMajorant`

## Scope and audit

This is the final upper-bound propagation for the classical balanced Carlson
input. It does not alter the lower oscillation chain, complementary-zero
module, or VK-edge modules. The contract must expose the endpoint identities,
and the axiom audit must contain only the repository-standard logical axioms.
