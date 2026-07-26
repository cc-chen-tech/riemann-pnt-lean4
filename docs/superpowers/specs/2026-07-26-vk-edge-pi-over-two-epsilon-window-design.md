# VK-edge Pi-over-two Epsilon-window Design

## Goal

For every fixed `ε > 0`, replace the current power-seven localization by a
verified theorem locating the same strict pi-over-two oscillation in every
sufficiently late interval

\[
[Y,Y^{1+\varepsilon}].
\]

The final theorem must preserve:

- the factor `analyticOrderNatAt riemannZeta rho`;
- the coefficient `strictPiOverTwoOscillationConstant k > pi / 2`;
- the scale `x ^ rho.re / ‖rho‖`;
- the existing Carlson argument that selects a missing odd harmonic.

The starting threshold may depend on `ε`, the fixed zero `rho`, and the
selected harmonic. No uniformity in those parameters is claimed.

## Why the Existing Scale Cannot Simply Be Cropped

The current Gaussian has variance parameter `m`, center `16m`, and window
radius `12m`. Its endpoint ratio is therefore

\[
\frac{16+12}{16-12}=7.
\]

Replacing `12` by a small radius while retaining the center `16m` does give a
formal endpoint ratio close to one, but it breaks the analytic tail estimate.
The normalized error is only bounded trivially by a multiple of

\[
\exp((1-\operatorname{Re}\rho)y),
\]

whereas at a radius `dm` the Gaussian contributes approximately
`exp(-d^2 m / 4)`. For small `d`, the latter cannot dominate the former.
Consequently, a short-window theorem cannot be obtained by changing only the
final logarithmic substitution.

## Chosen Parameterization

Introduce a center coefficient `q` and a window-radius coefficient `d`:

\[
G_m(qm-y),\qquad
[(q-d)m,(q+d)m].
\]

For `ε > 0`, use

\[
q_\varepsilon
=64\frac{(2+\varepsilon)^2}{\varepsilon^2},
\qquad
d_\varepsilon
=64\frac{2+\varepsilon}{\varepsilon}.
\]

These satisfy

\[
0<d_\varepsilon<q_\varepsilon,\qquad
64<q_\varepsilon,
\frac{q_\varepsilon+d_\varepsilon}
     {q_\varepsilon-d_\varepsilon}
=1+\varepsilon,
\]

and the deliberately loose tail margin

\[
d_\varepsilon^2\ge 32(q_\varepsilon+d_\varepsilon).
\]

With

\[
m_\varepsilon(Y)
=\frac{\log Y}{q_\varepsilon-d_\varepsilon},
\]

the logarithmic window is exactly

\[
[\log Y,(1+\varepsilon)\log Y].
\]

The large numerical factor `64` is not intended to be sharp. It makes the
tail inequalities stable under the polynomial-Gaussian envelope
`exp(|t| / sqrt m)` and avoids obscuring the theorem with optimized constants.

The larger center also changes the residue envelope.  A zero with real-part
offset `a` contributes the exponential factor

\[
\exp(m(a^2-(\Delta\gamma)^2+q a)).
\]

Since `|a| ≤ 1`, the old fixed pole radius `5` is not sufficient when `q`
is large.  Use the fixed-for-`ε` annihilation radius

\[
B(q)=q+5.
\]

Then `B(q) ≥ 5` and, for `q > 0`,

\[
a^2+qa-B(q)^2\le -8.
\]

All zeros inside this larger finite vertical band are removed by the
polynomial filter.  Its degree and constants may depend on `ε`; they remain
fixed as the Gaussian scale tends to infinity.

## Architecture

### 1. Parametric Window and Transfer

Add definitions:

```lean
def localizedGaussianLogWindow (q d m : ℝ) : Set ℝ :=
  Set.Icc ((q - d) * m) ((q + d) * m)

def powerOnePlusEpsilonWindow (ε Y : ℝ) : Set ℝ :=
  Set.Icc Y (Y ^ (1 + ε))

def epsilonCenterCoefficient (ε : ℝ) : ℝ :=
  64 * (2 + ε) ^ 2 / ε ^ 2

def epsilonRadiusCoefficient (ε : ℝ) : ℝ :=
  64 * (2 + ε) / ε

def epsilonGaussianScale (ε Y : ℝ) : ℝ :=
  Real.log Y /
    (epsilonCenterCoefficient ε - epsilonRadiusCoefficient ε)

def centeredPoleRadius (q : ℝ) : ℝ :=
  q + 5
```

Prove the exact logarithmic-window identity and a general transfer theorem
from a normalized-error witness to a standard `chebyshevPsi` witness in
`powerOnePlusEpsilonWindow ε Y`.

### 2. Center-parametric Gaussian and Mellin Layer

Add center-parametric versions of the existing objects while retaining the
current center-16 definitions as wrappers:

```lean
localizedGaussianWeightAtCenter
localizedPsiGaussianAverageAtCenter
localizedZeroResidueSumAtCenter
localizedContourRemainderAtCenter
projectedPsiKernelAtCenter
relativeProjectedPsiKernelAtCenter
```

The inverse Gaussian and polynomial derivative estimates are translation
invariant. Their constants remain fixed-polynomial constants and do not gain
dependence on the center `q`.

### 3. Parametric True-zeta Contour

Generalize the exact weighted rectangle identity to the multiplier

\[
A(z-w)\exp(m(z-w)^2+qm(z-w)).
\]

The selected good height may continue to have the form

\[
T\in[12m+|v|,12m+|v|+1].
\]

The center coefficient `q` is fixed while `m` tends to infinity.  The
parametric decay layer assumes `16 ≤ q`.  On the left edge this retains the
existing `exp(-15m)` saving; on the horizontal edges, the old constant `36`
is replaced by `4+2q`, and the negative Gaussian term in `T^2` dominates this
fixed `q`-dependent term. Every resulting constant may depend on `q`.

The selected height eventually exceeds the fixed radius
`centeredPoleRadius q`; this is sufficient for the enlarged finite-pole
filter and does not require changing the linear good-height scale.

### 4. Radius-parametric Psi Tail

Define the true-error tail outside
`localizedGaussianLogWindow q d m`. Prove a bound under explicit hypotheses

```lean
0 < u
u < 1
0 < d
d < q
16 * (q + d) ≤ d ^ 2
```

of the form

\[
R_{A,u,v,q,d}(m)
\le C_{A,u,v,q,d}\exp(-c_d m),
\]

for all sufficiently large `m`, with `c_d > 0`.

The proof must account for all three exponential factors:

- growth of `normalizedPsiError`;
- the polynomial-Gaussian envelope `exp(|t| / sqrt m)`;
- Gaussian decay `exp(-t^2/(4m))`.

No tail theorem may be accepted if it bounds only the bare Gaussian mass.

### 5. Parametric Localized Contour Data

Introduce a radius-aware data structure, or parameterize the existing one,
so that its supremum and upper-bound fields refer to
`localizedGaussianLogWindow q d m`.

Install the target and missing-harmonic contour pair exactly as in
`sharpenedConcreteLocalizedContourData`. The coefficient limit remains

\[
2\,\texttt{sharpenedMissingHarmonicDenominator}(k),
\]

because the periodic Gaussian convergence is uniform in its center. Thus the
strict pi-over-two constant is unchanged.

Both target and missing-harmonic filters must use
`centeredPoleRadius q`, not the old hard-coded radius `5`.

### 6. Final Theorems

First prove the fixed missing-harmonic version:

```lean
theorem eventually_exists_psiError_in_powerOnePlusEpsilonWindow_gt_strictPiOverTwo
    {rho : ℂ} {k : ℕ} {ε : ℝ}
    (hε : 0 < ε)
    (hrhoRe0 : 0 < rho.re) (hrhoRe1 : rho.re < 1)
    (hgamma : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (hmissing :
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0) :
    ∀ᶠ Y : ℝ in Filter.atTop,
      ∃ x ∈ powerOnePlusEpsilonWindow ε Y,
        (analyticOrderNatAt riemannZeta rho : ℝ) *
              strictPiOverTwoOscillationConstant k *
              (x ^ rho.re / ‖rho‖) <
          |chebyshevPsi x - x|
```

Then prove the Carlson-selected version with the same assumptions currently
used by
`exists_eventually_psiError_in_powerSevenWindow_gt_strictPiOverTwo`.

## Rejected Alternatives

### Independent center and variance parameters

Using an arbitrary center `L` and variance `h` is analytically clean, but it
would force every contour API to carry two real scales. The dimensionless
`q` parameter gives the same freedom with less API churn.

### Cropping the current center-16 Gaussian

This fails for small `ε`: the true normalized-error tail need not tend to
zero. A successful proof of only the set-theoretic transfer would therefore
be misleading and is explicitly outside scope.

### Importing a short-interval oscillation theorem

Schlage-Puchta-type results do not directly provide the present strict
pi-over-two coefficient with analytic multiplicity. They cannot be used as
an unproved project axiom.

## Verification

Each new public layer receives:

- a contract file pinning the intended theorem signatures;
- a `#print axioms` audit;
- a scan excluding `sorry`, `admit`, and project-defined `axiom`.

The final branch must pass:

```bash
lake build
./scripts/verify-baseline.sh
```

The result remains a conditional consequence of the existence of the fixed
off-critical-line zero. It is not an unconditional square-root upper bound
and does not prove RH.
