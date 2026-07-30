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
3. A nonempty actual equal-real-part package has `D > 0`, because each zeta
   zero has positive analytic multiplicity and is nonzero.
4. A specified nontrivial zero `rho` with `|Im rho| <= T` makes the package
   at `(T, Re rho)` nonempty.
5. The actual package/Carlson transfer can therefore choose `L` internally
   from package nonemptiness.

This closes the elementary mean-square coefficient once a package member is
given.  It does not prove that a package exists at a prescribed `(T,beta)`,
does not construct the Carlson outside-cluster certificate, and does not
imply an unconditional Omega theorem or RH.
