# Dynamic-boundary explicit-formula transfer

This module puts the actual zero estimates and the exact PNT explicit formula
on the same target scale.

For

\[
S_m=\{\rho:\zeta(\rho)=0,\ |\Im\rho|\le H(m),\ \Re\rho=\beta\},
\]

it proves

\[
\frac{\left|
\frac{\psi_0(m)-m}{m}
-M_{S_m}(m)\right|}{m^{\beta-1}}
\longrightarrow0.
\]

The proof chain is:

1. Global `O(H log H)` multiplicity controls `Re rho <= sigma`.
2. Summable Carlson weights control `Re rho > sigma` by dominated
   convergence.
3. Conjugation restores negative ordinates.
4. Finite dominated convergence controls real-ordinate zeros, including
   boundary zeros eventually absorbed by `S_m`.
5. Existing target-normalized closed-real-axis and contour estimates complete
   the exact explicit formula.

The quantitative conditions are

\[
\frac12<\sigma<1,\qquad
H(m)\le m^\alpha,\qquad
\sigma-\beta+\alpha+\varepsilon<0,
\]

together with the non-strict right-edge bounds for positive and real-ordinate
zeros.

This is a complete remainder transfer around a moving boundary package. It
does not itself prove an Omega theorem because no anti-cancellation theorem
for the moving main term is asserted.
