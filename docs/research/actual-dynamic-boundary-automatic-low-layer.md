# Automatic dynamic-boundary low layer

The dynamic boundary package changes with the natural scale, so a theorem
whose cluster is a fixed `Finset` cannot be applied directly. The global
zero-multiplicity estimate is nevertheless uniform in the deleted cluster.

This module uses the canonical two-strip classification

\[
\Re\rho\le \sigma,\qquad \Re\rho>\sigma
\]

outside

\[
S_m=\{\rho: |\Im\rho|\le H(m),\ \Re\rho=\beta\}.
\]

For the low layer it proves

\[
\frac{\|\sum_{\Re\rho\le\sigma,\ \rho\notin S_m}
 m(\rho)m^{\rho-1}/\rho\|}{m^{\beta-1}}\longrightarrow0
\]

from

\[
H(m)\le m^\alpha,\qquad
\sigma-\beta+\alpha+\varepsilon<0.
\]

The kernel denominator guard is constructed automatically from the finite
height-one base set. The proof then uses the global `O(H log H)` analytic
multiplicity bound and the existing logarithmic power absorber.

Combining this result with the summable Carlson high tail removes the explicit
`hlow` hypothesis from positive-ordinate dynamic-boundary decay.
