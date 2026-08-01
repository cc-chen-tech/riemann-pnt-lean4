# Stack 181: Actual third-order Perron inversion

## Goal

Upgrade the cubic-kernel foundation from Stack 178 to an actual all-height
Perron inversion theorem recovering the second Riesz ramp.

## New analytic chain

1. Prove the complex second-moment Laplace identity

   ```text
   integral_0^infinity u^2 exp(a u) du = -2 / a^3
   ```

   for `Re(a) < 0`.
2. Define the one-sided quadratic ramp

   ```text
   R2_c(u) = max(u,0)^2 / 2 * exp(-c max(u,0)).
   ```
3. Compute its Fourier transform exactly as

   ```text
   Fourier(R2_c)(w) = 1 / (c + 2 pi i w)^3.
   ```
4. Prove both the ramp and its Fourier transform are integrable.  Cubic
   transform integrability is dominated by the already formalized square
   transform using `c <= norm(c + 2 pi i w)`.
5. Apply Fourier inversion and remove the exponential damping to obtain

   ```text
   integral_R exp((c + 2 pi i w) u) / (c + 2 pi i w)^3 dw
     = max(u,0)^2 / 2.
   ```

## Significance

This is the actual scalar inversion theorem needed to define the second Riesz
mean from the cubic zeta kernel.  Together with Stack 178's `H^-2` tail order
and Stacks 179-180's two-difference amplitude retention, it supplies all scalar
kernel identities required before inserting von Mangoldt coefficients.

## Claim boundary

This stack does not yet interchange the cubic Perron integral with the full
von Mangoldt Dirichlet series, define the arithmetic second Riesz mean, shift
the cubic zeta contour, or estimate the twice-differenced remainder.  It is an
actual Perron inversion theorem, but not yet a complete zeta explicit formula
or an unconditional Omega theorem.
