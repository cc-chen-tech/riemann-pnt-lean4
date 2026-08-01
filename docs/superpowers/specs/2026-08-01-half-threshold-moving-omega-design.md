# Half-threshold reciprocal moving Omega design

## Objective

Replace the `beta > 2/3` window in the automatic actual-package moving Omega
chain by the natural Carlson threshold `beta > 1/2`.

## Canonical geometry

For `1/2 < beta < 1`, set

```text
sigma = (1/2 + beta) / 2
tau = (sigma + beta) / 2
alpha = 1 - beta / 2
```

Then `1/2 < sigma < tau < beta`, `1-beta < alpha`, and `0 < alpha <= 1`.
The fixed-package moving extension is controlled by reciprocal absolute mass
under `sigma < beta`.  The moving-cluster complement is reciprocal-negligible
under `tau < beta`.  The selected contour remainder is negligible because the
chosen `alpha` lies in the explicit-formula window.

For package energy `E`, sampling fraction `q`, and residual boundary mass `B`,
the automatic package budget proves `2*B < q*sqrt(E)`.  The dynamic transfer
retains the explicit positive coefficient

```text
(q*sqrt(E) - 2*B) / 4.
```

## Claim boundary

The attained-edge facade still assumes explicit attainment of a global
maximal zero real part and `beta < 1`.  The result is unsigned Omega at the
exact `x^beta` scale.  It does not prove attainment, simultaneous signed
Omega, or RH.
