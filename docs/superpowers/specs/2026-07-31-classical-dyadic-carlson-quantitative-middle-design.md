# Classical dyadic Carlson quantitative middle-mass design

## Objective

Quantify the complete moving-middle zero mass by combining two already
separated mechanisms:

1. a fixed low-real-part strip controlled by the global analytic-multiplicity
   estimate;
2. the right-hand dyadic layers controlled by Carlson density.

This is the next bounded layer above the explicit Carlson majorant.  It does
not quantify every term in the full explicit formula.

## Low-strip majorant

At the classical selected height, compare the truncation height eventually to
`m^(1/64)`.  For zeros with real part at most `7/8`, the relative kernel and
global multiplicity estimate give

\[
L_{C,\kappa}(m)
 = C\kappa^{-1}\left(2+\frac1{64}\right)
   m^{-7/64}(\log m)^4.
\]

The Lean definition reuses
`actualHybridLowNormalizedLogPowerMajorant` at
`beta=1`, `tau=7/8`, and `alpha=1/64`, then proves the displayed identity and
convergence to zero.

## Combined middle majorant

With the stack-21 Carlson term

\[
M_{D,r}(m)=\exp\!\left(
  \log D-3\log r+11\log(1+\sqrt{\log m})
  -\frac r4\sqrt{\log m}
\right),
\]

define

\[
Q_{C,\kappa,D,r}(m)=L_{C,\kappa}(m)+M_{D,r}(m).
\]

Both summands tend to zero.  The existing moving-middle decomposition then
gives an eventual bound by `Q`.

## Quantifier boundary

The Carlson constants `rate` and `D` are global across all uniform good-height
selectors.  The currently available norm-separation certificate is generated
from the chosen height function, so the low-strip constants `C` and `kappa`
remain inside `forall selection`.  Moving them outside would require a new
uniform norm-separation lemma and is intentionally not assumed here.

## Honest boundary

This stack quantifies the complete moving-middle positive-zero mass.  It does
not yet give one explicit majorant for the critical-half contribution, the
real-ordinate contribution, the contour remainder, or the full natural
explicit-formula remainder.  It therefore does not claim an optimal PNT rate,
a new Carlson estimate, an unconditional Omega theorem, or RH.
