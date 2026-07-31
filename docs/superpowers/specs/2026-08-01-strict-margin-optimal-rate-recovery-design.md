# Strict-margin recovery of the optimal PNT rate

## Goal

Quantify the loss caused by the necessary strict factor `0 < theta < 1` in
the actual `log (T + 6)` zero-free-width calculation.

## Arithmetic theorem

For `0 <= theta <= 1` and `b >= 0`, prove

`theta * classicalAdmissibleBalancedRate b <=
  classicalAdmissibleBalancedRate (theta * b)`.

Thus for every `q > 1`, taking `theta = 1 / q` gives

`classicalAdmissibleBalancedRate b / q <=
  classicalAdmissibleBalancedRate (b / q)`.

The right side is the actual strict-margin grid rate, so every finite
multiplicative approximation to the formal non-strict optimum is attainable
without setting `theta = 1`.

## Automatic PNT theorem

Instantiate the automatic actual PNT grid theorem at `theta = 1 / q`. Return
the actual grid, its rate/base identities, the explicit lower bound by the
non-strict optimum divided by `q`, the selector identity, and the real relative
PNT error majorant.

## Claim boundary

The theorem gives every finite `q > 1`; it does not claim the forbidden
endpoint `theta = 1`, an optimal numerical constant, VK sharpness, an Omega
theorem, or RH.
