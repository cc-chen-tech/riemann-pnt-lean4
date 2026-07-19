# Riemann-von Mangoldt Count/Phase Identity Design

## Scope

This spike proves the exact bridge between the existing completed-zeta
rectangle count and the phase terms that already have quantitative estimates.
It does not prove the final Riemann-von Mangoldt asymptotic.

For good heights `4 <= U < T`, the target shape is

```text
pi * (N(T) - N(U))
  = verticalGammaUnwrappedPhase T - verticalGammaUnwrappedPhase U
    + zetaHalfPathArgument U T.
```

Here `zetaHalfPathArgument` consists of the two horizontal zeta argument
variations from `Re(s) = 1/2` to `Re(s) = 2`, together with the vertical zeta
argument variation on `Re(s) = 2`.

## Chosen Route

Reuse the proved argument-principle identity on `[0,1] x [U,T]` instead of
reclassifying zeros in a larger rectangle.

1. Prove conjugation symmetry of the completed zeta function and its
   logarithmic derivative.
2. Combine conjugation with `xi(s) = xi(1-s)` to fold the `[0,1]` boundary
   around `Re(s) = 1/2`.
3. Deform the right half-path through the zero-free rectangle
   `[1,2] x [U,T]`, moving the vertical edge from `Re(s) = 1` to `Re(s) = 2`.
4. Decompose `xi'/xi` into the elementary, Gamma, and zeta summands.
5. Use holomorphy on `[1/2,2] x [U,T]` to reduce the elementary and Gamma
   half-path contributions to their values on the critical line.
6. Identify the elementary contribution as zero and the Gamma contribution as
   the difference of `verticalGammaUnwrappedPhase`.

This is preferable to proving the argument principle again on `[-1,2]`: it
reuses `RectangleCount.lean`, avoids a second zero-classification proof, and
still places the remaining vertical zeta term in the absolutely convergent
half-plane.

## Components

### Completed-zeta symmetry

`CompletedZetaSymmetry.lean` proves:

- `xi(conj s) = conj (xi s)`;
- the corresponding derivative and logarithmic-derivative identities;
- `F(1 - conj s) = -conj(F s)` for `F = xi'/xi` away from zeros.

The value identity is first established where the zeta Dirichlet series
converges and then extended to the entire plane by analytic continuation.

### Boundary folding and deformation

`CountPhaseIdentity.lean` defines a generic half-boundary phase functional

```text
Im integral(bottom) - Im integral(top) + Re integral(right)
```

and proves two exact identities:

- the completed-zeta rectangle count is twice this functional on
  `[1/2,1]`;
- zero-freeness on `[1,2]` deforms it to `[1/2,2]`.

The signs are fixed by the existing orientation
`bottom - top + I*right - I*left`.

### Right vertical zeta argument

`RightVerticalZetaArgument.lean` proves that `zeta(2+it)` stays in the open
right half-plane. The principal complex logarithm is therefore a valid
primitive along the whole vertical segment. Its imaginary part remains in
`(-pi/2,pi/2)`, giving a uniform bound for

```text
Re integral_U^T (zeta'/zeta)(2+it) dt.
```

No pointwise integration of `|zeta'/zeta|` is used, since that would lose a
factor proportional to `T-U`.

## Public Interfaces

The spike exposes:

```text
zetaHalfPathArgument (U T : Real) : Real

riemannZeroCount_sub_eq_gammaPhase_add_zetaHalfPathArgument
  (hU : 4 <= U) (hUT : U < T)
  (hUgood : goodHeight U) (hTgood : goodHeight T)

exists_abs_zetaHalfPathArgument_le_log
```

The logarithmic estimate may use
`C * (1 + log (U+5) + log (T+5))`; the later good-height module will fix `U`
and absorb its contribution into one constant.

## Verification

Each public theorem gets a compile-time contract and an axiom audit. The
focused build must include the new modules and the aggregate
`PrimeNumberTheorem.RiemannVonMangoldt` module. Source scans must find no
`sorry`, `admit`, or project `axiom`; `#print axioms` may list only `propext`,
`Classical.choice`, and `Quot.sound`.

## Claim Boundary

Completing this spike proves an exact route identity and a logarithmic bound
for its zeta remainder. It does not by itself prove the good-height or
all-height Riemann-von Mangoldt formula, PNT, or RH.
