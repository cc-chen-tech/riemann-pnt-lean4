# Third-order L-series and explicit-formula bridge

## Result

This slice closes the finite-height bridge from the genuine cubic Perron kernel
to the actual zeta contour and the second Riesz mean.

The final theorem produces the zeta poles in a rectangle with residues

`-analyticOrderNatAt riemannZeta rho * x^rho / rho^3`

and proves

`norm (sum residues - thirdOrderContourRemainder - secondSmoothedChebyshevPsi x)`

is bounded by

`tsum n, vonMangoldt n * (x / n)^c / (8 * pi^3 * W^2)`.

## Theorem chain

1. `intervalIntegral_vonMangoldt_LSeries_thirdOrder_eq_tsum` proves absolute
   termwise integration on every finite vertical segment with `1 < c`.
2. `intervalIntegral_neg_logDeriv_riemannZeta_thirdOrder_eq_vonMangoldt_tsum`
   rewrites the L-series as `-zeta'/zeta`.
3. `norm_intervalIntegral_thirdOrderPerronTerm_sub_sq_le` applies the genuine
   cubic kernel to each von Mangoldt term and retains the exact `W^-2` loss.
4. `norm_truncated_neg_logDeriv_riemannZeta_thirdOrder_sub_secondSmoothedPsi_le`
   sums the errors and identifies the finite-support main term with
   `secondSmoothedChebyshevPsi`.
5. `exists_thirdOrderExplicitFormula_secondSmoothedPsi_error_le` combines that
   estimate with the cubic zeta residue identity from the prerequisite PR.

## Scope boundary

This resolves the previous reciprocal-height obstruction on the right Perron
boundary by replacing `W^-1` with `W^-2`. It does not estimate the top, bottom,
or left contour edges contained in `thirdOrderContourRemainder`; therefore it
does not yet prove a PNT error rate, an Omega theorem, or any zero-free region.
