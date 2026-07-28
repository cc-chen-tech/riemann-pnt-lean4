# Actual zero-package energy positivity

`ZeroDensityLayerBudgetActualZeroPackageEnergyPositive.lean` isolates the
elementary positivity step behind the equal-real-part package lower bound.

For the actual finite package `S(T,beta)`, write

```text
D = sum_{rho in S(T,beta)} |m(rho) / rho|^2
B = offDiagonalBound(S(T,beta))
E(L) = D - B / L.
```

The module proves:

1. `B < L * D` and `L > 0` imply `E(L) > 0`.
2. `D > 0` implies that some explicit positive `L` satisfies `E(L) > 0`.
3. The actual package/Carlson transfer can therefore choose `L` internally
   from the single hypothesis `D > 0`.

This is only an arithmetic closure of the mean-square coefficient.  It does
not prove that a particular zeta-zero package is nonempty, does not construct
the Carlson outside-cluster certificate, and does not imply an unconditional
Omega theorem or RH.
