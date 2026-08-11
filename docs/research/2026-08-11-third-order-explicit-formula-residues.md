# Third-order explicit-formula residues

## Scope

This slice connects the genuine cubic Perron kernel to the zeta contour. It does
not yet prove the cubic L-series interchange or identify the right-hand vertical
integral with `secondSmoothedChebyshevPsi` at finite height.

## Theorem chain

1. `exists_analyticOnNhd_div_id_regularization` proves a reusable transfer:
   dividing a finite simple-pole regularization by `z` preserves analyticity on
   compact sets separated from zero and replaces every residue `r(p)` by
   `r(p) / p`.
2. `exists_explicitFormula_regularization_without_zero` removes the artificial
   zero pole from the existing first-order zeta regularization.
3. Applying the transfer twice gives
   `exists_thirdOrderExplicitFormula_analytic_regularized_remainder`, whose
   nontrivial-zero residue is exactly
   `-analyticOrderNatAt riemannZeta rho * x^rho / rho^3`.
4. `exists_boundaryRectIntegral_thirdOrderExplicitFormulaIntegrand_eq_residue_sum`
   converts that local regularization into a full rectangle residue identity.
5. `exists_scaledRightIntegral_eq_residue_sum_sub_thirdOrderContourRemainder`
   rescales the right boundary to Perron frequency and isolates the top, bottom,
   and left edges in `thirdOrderContourRemainder`.

## Mathematical consequence

The extra smoothing is now present in the actual zeta zero term, not only in an
abstract kernel: every nontrivial zero carries the cubic factor `1 / rho^3`.
This is the contour-side input needed to exploit the quadratic-height gain from
the third-order Perron tail.

## Remaining bridge

The next independent slice should prove the cubic analogue of the existing
L-series interval-integral interchange. Combined with the current scaled
contour identity and the third-order Perron theorem, that will produce a
finite-height explicit formula for `secondSmoothedChebyshevPsi`. No PNT error
bound or oscillation theorem is claimed here.
