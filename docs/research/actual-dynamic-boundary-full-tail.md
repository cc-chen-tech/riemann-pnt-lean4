# Actual dynamic-boundary full tail

This module turns the dominated-convergence Carlson tail into control of the
genuine complementary zero term in the explicit formula.

The moving package is

\[
S_m=\{\rho:\zeta(\rho)=0,\ |\Im\rho|\le H(m),\ \Re\rho=\beta\}.
\]

For a fixed split point `sigma`, the positive-ordinate complement is bounded
by

\[
\frac{\|\text{low}_{m,\sigma}\|}{m^{\beta-1}}
+
\sum_{\substack{\Im\rho>0\\ \Re\rho>\sigma\\ \rho\notin S_m}}
\frac{m(\rho)}{|\rho|}m^{\Re\rho-\beta}.
\]

The first term is an explicit input named `hlow`. The second tends to zero by
the summable-weight dominated-convergence theorem from
`ZeroDensityLayerBudgetActualDynamicBoundaryDominatedTail`.

Conjugation restores the negative ordinates. A separate real-ordinate
normalized decay input then yields decay of the complete zero tail. Finally,
the real part of the signed outside-cluster sum is bounded by that full norm,
so the actual explicit-formula complement satisfies

\[
\frac{|R_{\mathrm{zeros}}(m)|}{m^{\beta-1}}\longrightarrow 0.
\]

This closes the high-tail and signed-complement transfer for a dynamic
boundary package. It does not prove an Omega theorem: one must still supply
low-layer decay, real-ordinate decay, contour decay, and an anti-cancellation
witness for the moving package main term.
