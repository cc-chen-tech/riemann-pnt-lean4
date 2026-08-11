# Third-order Perron kernel prerequisite

## Scope

This slice supplies the missing analytic prerequisite behind the actual-cubic
Carlson energy chain. It constructs a genuine reciprocal-cubic Perron kernel;
it does not alter Sharp oscillation, half-isolated Gram/Schur, VK-edge, or
complementary-bound modules.

## Theorem chain

For \`Re(a) < 0\`:
\[
  \int_0^\infty \frac{u^2}{2}e^{au}\,du=-\frac1{a^3}.
\]

Consequently, for \`c > 0\`, the Fourier transform of
\[
  \frac{\max(u,0)^2}{2}e^{-c\max(u,0)}
\]
is exactly
\[
  \frac1{(c+2\pi i w)^3}.
\]

Fourier inversion gives
\[
  \int_{\mathbb R}\frac{e^{(c+2\pi i w)u}}
    {(c+2\pi i w)^3}\,dw
  =\frac{\max(u,0)^2}{2}.
\]
The finite-sum interface specializes this identity to the von Mangoldt
coefficients and defines the corresponding second Riesz mean.

## Explicit truncation loss

For \`W > 0\`, each one-sided tail is bounded by
\[
  \frac{e^{cu}}{16\pi^3W^2},
\]
and therefore
\[
 \left|\int_{-W}^{W}\frac{e^{(c+2\pi i w)u}}
 {(c+2\pi i w)^3}\,dw-\frac{\max(u,0)^2}{2}\right|
 \le \frac{e^{cu}}{8\pi^3W^2}.
\]

This is the required improvement from the existing second-order
\`W^{-1}\` contour loss to a true third-order \`W^{-2}\` loss.

## Boundary

The module does not yet prove the zeta contour residue identity
\`-m(rho) x^rho / rho^3\`. The next independent slice must combine this
kernel with the von Mangoldt L-series and the regularized zeta contour. Thus
this result removes the kernel/truncation obstruction but does not by itself
complete the PNT upper/lower transfer or prove an Omega theorem.
