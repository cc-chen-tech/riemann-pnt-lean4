# Actual zero-package phase decomposition

For the actual finite package

```text
S(T,beta) = {rho : zeta(rho)=0, abs(Im rho)<=T, Re rho=beta},
```

the module defines

```text
P_T,beta(y)
  = sum_{rho in S(T,beta)}
      (m(rho)/rho) * exp(i Im(rho) y).
```

It proves the exact identities

```text
equalRealPartZeroPackageContribution x T beta
  = x^beta * P_T,beta(log x)
```

and

```text
actualEqualRealPartZeroPackagePNTMain x T beta
  = -x^(beta-1) * P_T,beta(log x)
```

for `x>0`.  When a dynamic height covers `T`, its visible complex PNT zero
sum equals this canonical main term.  Combined with finite-phase natural
sampling, this reduces natural-point discretization to elementary product
stability.
