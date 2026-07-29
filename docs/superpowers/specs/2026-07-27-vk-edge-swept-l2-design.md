# Swept Gaussian Local L2 Design

## Objective

Strengthen the ordinary local second-moment endpoint from PR #22 from

\[
  c_{\varepsilon,\rho}\sqrt{\log Y}
  <
  \int_{\log Y}^{(1+\varepsilon)\log Y}
    |F_\rho(y)|^2\,dy
\]

to an explicit lower bound on the full window-length scale:

\[
  c'_{\varepsilon,\rho}\log Y
  <
  \int_{\log Y}^{(1+\varepsilon)\log Y}
    |F_\rho(y)|^2\,dy.
\]

Here

\[
  F_\rho(y)
  =
  |\rho|e^{-\operatorname{Re}(\rho)y}
  \bigl(\psi(e^y)-e^y\bigr),
\]

and the theorem remains conditional on a hypothetical zeta zero
\(\rho\) with \(1/2<\operatorname{Re}(\rho)<1\).

This milestone does not assume a fourth-moment estimate and does not claim
RH. Its purpose is to put the forced second moment on the same linear scale
as the logarithmic window. That is the scale required before a fourth-moment
bound of order \(\log Y\) could imply a fixed-proportion large-value set by
Paley--Zygmund.

## Mathematical mechanism

For every sufficiently large Gaussian scale \(m\), the existing contour
theorem gives

\[
  C_2
  <
  \int |F_\rho(y)|^2 |K_m(y)|\,dy,
\]

where \(K_m\) is centered at \(qm\), has width comparable with \(\sqrt m\),
and \(C_2>0\) is explicit.

Instead of using one value of \(m\), integrate this inequality over

\[
  m\in[M,RM],\qquad R>1.
\]

The centers \(qm\) sweep an interval of length \(q(R-1)M\). Completing the
square gives the pointwise envelope

\[
  e^{|qm-y|/\sqrt m}G_m(qm-y)
  \le
  \frac{e^2}{2\sqrt{\pi M}}
  \exp\!\left(
    -\frac{(qm-y)^2}{8RM}
  \right)
\]

for \(M\le m\le RM\), \(M\ge1\), and \(R\ge1\). Integrating the right side
in \(m\), then extending to the whole real line after the affine change
\(u=qm-y\), gives

\[
  \int_M^{RM}
    e^{|qm-y|/\sqrt m}G_m(qm-y)\,dm
  \le
  \frac{e^2\sqrt{2R}}{q}.
\]

The bound is independent of \(M\) and \(y\). Fubini therefore yields

\[
  C_2(R-1)M
  \le
  B_{q,\rho,k,R}
  \int_{\text{global window}} |F_\rho(y)|^2\,dy.
\]

This is linear in \(M\), unlike the single-kernel
\(\sqrt M\) lower bound.

## Window geometry

Use the existing epsilon-window parameters at the narrower value
\(\varepsilon/2\):

\[
  q=q_{\varepsilon/2},\qquad
  d=d_{\varepsilon/2}.
\]

Define

\[
  R_\varepsilon
  =
  \frac{1+\varepsilon}{1+\varepsilon/2}>1,
  \qquad
  M_\varepsilon(Y)
  =
  \frac{\log Y}{q-d}.
\]

For every \(m\in[M_\varepsilon(Y),R_\varepsilon
M_\varepsilon(Y)]\),

\[
  [(q-d)m,(q+d)m]
  \subseteq
  [\log Y,(1+\varepsilon)\log Y].
\]

Thus all swept weighted moments lie inside one target epsilon window.

## Lean modules and interfaces

Add one focused module:

```text
PrimeNumberTheorem/VKEdgePiOverTwoSweptL2.lean
```

The public API will include:

```lean
def sweptGaussianEnvelope ...

theorem exp_scaled_abs_mul_normalizedGaussian_le_sweptEnvelope ...

theorem integral_sweptGaussianEnvelope_le ...

theorem ordinarySecondMoment_linear_lower_of_sweptWeightedLower ...

def epsilonSweepRatio (ε : ℝ) : ℝ

def centeredSharpenedSweptOrdinaryL2Constant
    (ε : ℝ) (rho : ℂ) (k : ℕ) : ℝ

theorem exists_eventually_ordinarySecondMoment_in_epsilonLogWindow_gt_linear
    ...
```

The final theorem must select the missing odd harmonic through Carlson,
retain `analyticOrderNatAt` multiplicity, prove the named constant is
strictly positive, and conclude

```lean
constant * Real.log Y <
  ∫ y in Set.Icc (Real.log Y) ((1 + ε) * Real.log Y),
    normalizedPsiError rho y ^ 2
```

eventually as `Y -> atTop`.

## Measurability and Fubini boundary

The two-variable Fubini integrand will use the explicit Gaussian envelope,
not the true projected kernel. This avoids proving joint measurability of
the iterated-derivative kernel in `(m,y)`.

For each fixed `m`, the true weighted moment is first majorized by the
explicit envelope using the existing pointwise kernel bound. The envelope
is jointly measurable on the compact rectangle because it is assembled
from continuous real operations with `m >= M >= 1`. The normalized error
is measurable and bounded on the compact target y-window, so the product is
integrable and ordinary Fubini applies.

## Explicit constants

No `Classical.choose` may be used to define a public constant. A valid
choice is a strict half of the raw sweep ratio:

\[
  c'_{\varepsilon,\rho,k}
  =
  \frac{1}{2}
  \frac{C_2(R_\varepsilon-1)}
       {(q-d)B_{q,\rho,k,R_\varepsilon}},
\]

with

\[
  C_2
  =
  \frac{m(\rho)^2}
       {\operatorname{denominator}(k)}
\]

and

\[
  B_{q,\rho,k,R}
  =
  K_{q,\rho,k}
  \frac{e^2\sqrt{2R}}{q}.
\]

The factor \(1/2\) turns the non-strict integrated comparison into a strict
public lower bound without needing a delicate strict-integral lemma.

## Testing and acceptance

TDD order:

1. Add a contract importing the absent swept-L2 module and checking the
   final theorem signature. Verify that it fails because the module does
   not exist.
2. Prove the Gaussian completion-of-square and sweep-mass lemmas.
3. Prove the abstract finite-rectangle Fubini transfer.
4. Prove epsilon geometry and the zeta specialization.
5. Add an axiom audit.

Acceptance:

- focused module, contract, and axiom-audit builds pass;
- `#print axioms` shows only standard Lean/Mathlib logical axioms;
- no `sorry`, `admit`, or project `axiom`;
- `git diff --check`;
- `./scripts/verify-baseline.sh`;
- documentation states that a fixed-proportion result still requires a
  compatible fourth-moment upper bound of linear order.

## Failure boundary

If the sweep mass cannot be bounded independently of \(M\), the linear
upgrade fails and the exact growth loss must be recorded. If Fubini can
only be closed by assuming a new analytic property of the true PNT error,
that property must remain an explicit hypothesis rather than being hidden
in a selected object or route interface.
