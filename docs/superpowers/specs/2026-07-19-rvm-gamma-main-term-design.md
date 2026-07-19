# Riemann-von Mangoldt Gamma Main Term Design

## Objective

Normalize the already verified vertical `GammaR` phase asymptotic to the exact
main term used in the Riemann-von Mangoldt formula, and expose a two-height
version whose additive phase constant cancels.

This stage proves the Gamma main term. It does not yet identify the completed
zeta rectangle integral with that phase difference, and it does not estimate
the remaining zeta boundary argument by `O(log T)`.

## Mathematical Interface

Define

```text
M(T) = T / (2*pi) * log (T / (2*pi)) - T / (2*pi).
```

The existing `HardyTheorem.thetaModel` satisfies exactly

```text
thetaModel(T) / pi = M(T) - 1/8.
```

Reuse
`HardyTheorem.exists_verticalGammaUnwrappedPhase_sub_thetaModel_tendsto_const_inv`
to prove

```text
exists kappa C >= 0, for T >= 1,
  |verticalGammaUnwrappedPhase(T) / pi - M(T) - kappa| <= C / T.
```

Then subtract the estimates at `T` and `U`; the unknown `kappa` cancels:

```text
exists C >= 0, for U,T >= 1,
  |(phase(T) - phase(U)) / pi - (M(T) - M(U))|
    <= C / U + C / T.
```

The second theorem is the public bridge for the later good-height count
formula.

## Boundary Correction

Do not integrate the Gamma summand from
`logDeriv_completedZeta_eq_zeta_add_gamma` around the whole positive-height
closed rectangle and call it the main term. That summand is holomorphic inside
the rectangle, so its closed contour integral is zero. The Gamma contribution
appears only after using the completed-zeta functional equation to relate
opposite boundary pieces and then expressing the resulting open-path argument
change through a continuous phase.

Therefore this package proves the normalized phase asymptotic only. A later
boundary-argument package must establish the exact count/phase identity and
isolate the zeta argument term.

## Files

- `PrimeNumberTheorem/RiemannVonMangoldt/GammaMainTerm.lean`
- `Test/RiemannVonMangoldtGammaMainTermContract.lean`
- `Test/RiemannVonMangoldtGammaMainTermAxiomAudit.lean`

## Verification

The focused module, contract, and axiom audit must build. Changed source may
not contain `sorry`, `admit`, or `axiom`; the audit allowlist remains
`propext`, `Classical.choice`, and `Quot.sound`.

