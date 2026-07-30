# Theta-sharp classical Carlson rate design

## Objective

Remove the conservative fixed factor `1/4` in the classical Carlson
square-root-log exponent.  The existing proof bounded

\[
\frac{r}{2(1+s)}s^2
\]

below by `(r/4)s`, where `s = sqrt(log m)`.  Asymptotically the coefficient is
`r/2`, so the fixed quarter loses a factor two.

## Theta family

For

\[
0<\theta<\frac12,
\]

define

\[
M_{C,r,\theta}(m)=\exp\!\left(
 \log C-3\log r+11\log(1+s)-\theta r s
\right).
\]

The key eventual inequality is

\[
\theta r s\le \frac{r}{2(1+s)}s^2.
\]

After cancelling positive factors, this is equivalent to

\[
2\theta(1+s)\le s,
\]

which holds whenever

\[
s\ge\frac{2\theta}{1-2\theta}.
\]

This proves the layered coarse ratio, and then the genuine multiplicity-aware
fixed-anchor zeta mass, is eventually bounded by `M(C,r,theta)`.

## Decay

The majorant has the exact form

\[
e^{\log C-3\log r}(1+s)^{11}e^{-\theta r s}
\]

and tends to zero for every positive `theta` and `r`.

## Strict rate improvement

At the balanced height

\[
\alpha_*=\min(1,\sqrt b),
\qquad r=\alpha_*/2,
\]

the theta-family verified rate is

\[
r_\theta=\theta\frac{\alpha_*}{2}.
\]

The previous `alpha*/8` rate is exactly the case `theta=1/4`.  Therefore every

\[
\frac14<\theta<\frac12
\]

strictly improves the old rate, and the verified rates can approach

\[
\frac{\alpha_*}{4}
\]

arbitrarily closely from below.

## Why the endpoint remains strict

At `theta=1/2`, the required inequality becomes `1+s <= s`, which is false.
Thus the current pointwise argument naturally proves every strict rate below
the asymptotic limit, not the endpoint itself.  This is a mathematical
boundary rather than a tactic artifact.

## Honest boundary

This improves the actual Carlson fixed-anchor mass rate and removes the
previous factor-two slack.  Downstream balanced full-PNT assemblers still use
the old majorant until they are parameterized by `theta`.  The result does not
prove an unconditional Omega theorem or RH.
