# Initial true residual Gaussian energy

## Closed theorem

Assume that

\[
\rho=\beta+i\gamma,\qquad
\zeta(\rho)=0,\qquad
\gamma>0,\qquad
\frac12<\sigma<\beta<1.
\]

For every fixed \(\varepsilon>0\), the swept local \(L^2\) theorem supplies
a missing odd harmonic \(k\) and a positive constant \(C_{\varepsilon,\rho,k}\)
such that, on every sufficiently late logarithmic window,

\[
C_{\varepsilon,\rho,k}\log Y
<
\int_{\log Y}^{(1+\varepsilon)\log Y}
  \left|\rho\,e^{-\beta y}
    \left(\psi(e^y)-e^y\right)\right|^2\,dy.
\]

This checkpoint chooses the forward Gaussian variance

\[
m=(\varepsilon\log Y)^2.
\]

The Gaussian minimum on the full window is exactly

\[
\frac{e^{-1/4}}
 {2\sqrt{\pi}\,\varepsilon\log Y}.
\]

It cancels the linear \(\log Y\) factor in the ordinary second moment.
Consequently the true empty-cluster no-jump residual has a uniform positive
Gaussian second moment for every truncation height \(T\):

\[
\frac{e^{-1/4}C_{\varepsilon,\rho,k}}
 {2\sqrt{\pi}\,\varepsilon|\rho|^2}
<
\int_0^{\varepsilon\log Y}
  w_{(\varepsilon\log Y)^2}(t)
  \left|R_{\varnothing,T,\beta}(\log Y+t)\right|^2\,dt.
\]

The endpoint is
`exists_eventually_emptyClusterResidualForwardGaussianSecondMoment_gt` in
`PrimeNumberTheorem/VKEdgeInitialFullMovingEnergy.lean`.

## Why the residual is genuine

For the empty selected cluster, the explicit-formula identity gives almost
everywhere

\[
R_{\varnothing,T,\beta}(y)
=-e^{-\beta y}\left(\psi(e^y)-e^y\right).
\]

Therefore the lower bound is independent of \(T\).  It is not a cosine
model, a route predicate, or an external fourth-moment hypothesis.

## Exact boundary

This theorem closes the previously missing lower bound for the true initial
residual energy.  It does not yet imply a lower bound for the canonical full
moving complementary-zero packet on the growing
\(\varepsilon\log Y\) window: the available good-height approximation
transfer is currently uniform only on fixed logarithmic windows.

Still missing:

1. control the finite-height approximation on the growing window, or extract
   a fixed subwindow carrying a uniform amount of the ordinary \(L^2\) mass;
2. transfer the resulting residual energy to the full moving complement;
3. iterate maximal-layer absorption without counting the same zero twice;
4. compare the distinct packets with a zero-density upper bound.

No zero-density contradiction, zero exclusion, RH, or unconditional
square-root PNT estimate is claimed.
