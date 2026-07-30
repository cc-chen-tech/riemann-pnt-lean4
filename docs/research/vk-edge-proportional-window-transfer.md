# Proportional-window full moving energy transfer

## New analytic bridge

Let \(\rho=\beta+i\gamma\) be a zeta zero with

\[
\frac12<\beta<1,\qquad \gamma>0.
\]

Choose a fixed \(\varepsilon>0\) satisfying

\[
(1-\beta)\varepsilon<\beta-\frac12.
\]

The finite-height explicit-formula remainder on
\([a,(1+\varepsilon)a]\) has a leading envelope of the form

\[
\exp\left(
  \left(\frac12-\beta+(1-\beta)\varepsilon\right)a
\right)
\operatorname{poly}(a).
\]

The displayed condition makes the exponent negative.  The remaining two
pieces decay like \(\exp((1/2-\beta)a)\operatorname{poly}(a)\) and
\(\exp(-\beta a)\operatorname{poly}(a)\).  Hence one height

\[
T\in[\exp(a/2),\exp(a/2)+1]
\]

controls the finite-height approximation uniformly on the entire
proportional window.

Lean endpoints:

- `tendsto_normalizedWindowRemainderEnvelope_proportional_atTop_nhds_zero`;
- `eventually_exists_uniform_goodHeight_normalized_proportional_window_remainder_lt`.

## Full complementary-zero energy

The previous checkpoint proves that an off-critical-line zero forces a
uniform positive Gaussian energy \(R_{\varepsilon,\rho,k}\) in the true
empty-cluster residual.  The full-moving decomposition gives

\[
\frac13R_{\mathrm{residual}}
 -\eta^2
 -\left(e^{-\beta a}B_{\mathrm{closed}}\right)^2
\le E_{\mathrm{full}}.
\]

Set

\[
\eta=\min\left(1,\frac{R_{\varepsilon,\rho,k}}{12}\right).
\]

For sufficiently large \(a\), the closed-term square is also smaller than
\(R_{\varepsilon,\rho,k}/12\).  Therefore

\[
\frac{R_{\varepsilon,\rho,k}}6
<
E_{\mathrm{full}}.
\]

The theorem
`exists_eventually_emptyClusterFullMovingGaussianSecondMoment_gt`
formalizes this statement on every sufficiently late window
\([Y,Y^{1+\varepsilon}]\).  Its packet uses the canonical full bucket set, so
it contains every finite-height complementary zero exactly once.

## Mathematical value

This closes the earlier mismatch between:

1. a true residual lower bound available only on a growing logarithmic
   window; and
2. a full-moving transfer previously discharged only on fixed windows.

Thus the chain now reaches

\[
\text{off-line zero}
\Longrightarrow
\text{uniform full complementary-zero energy on every late window}.
\]

This is stronger than a cosine model or an arbitrary finite-bucket
statement.

## Exact remaining boundary

The theorem does not prove that the energy comes from new zeros at each
window.  The height \(T\) and the canonical packet vary with the window, and
the same zero may contribute repeatedly.

Still missing:

1. extract a quantitatively large maximal real-part layer from the full
   energy;
2. iterate the extraction with an injective or otherwise duplicate-free
   packet assignment;
3. compare the number of distinct forced packets with Carlson or the newer
   zero-density layer-budget upper bounds;
4. derive an actual contradiction.

No zero exclusion, RH, or unconditional square-root PNT estimate is claimed.
