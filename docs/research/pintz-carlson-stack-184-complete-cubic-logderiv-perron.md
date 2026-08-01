# Stack 184: Complete cubic zeta log-derivative Perron formula

## Goal

Replace Stack 183's finite arithmetic Perron sum by the full von Mangoldt
Dirichlet series and the actual zeta logarithmic derivative on `Re(s)>1`.

## New theorem chain

1. Prove a cubic-denominator dominated-convergence theorem that interchanges
   the finite vertical integral with the full von Mangoldt L-series.
2. Use the established identity

   ```text
   L_vonMangoldt(s) = -zeta'(s) / zeta(s)
   ```

   on `Re(s)>1` to obtain the actual cubic zeta integral.
3. Apply Stack 182's scalar `W^-2` truncation estimate termwise.
4. Identify the finite-support center with Stack 183's
   `secondRieszChebyshevPsi` and sum the errors absolutely.

The final estimate is

```text
norm(truncated integral of x^s (-zeta'/zeta)(s) / s^3 - Psi_2(x))
  <= tsum_n Lambda(n) (x/n)^c / (8 pi^3 W^2).
```

## Significance

The explicit quadratic Perron remainder now controls the actual zeta
logarithmic derivative and the actual PNT second Riesz mean in one theorem.
This removes the finite-support kernel abstraction from the analytic input to
the future cubic contour shift.

## Claim boundary

The contour has not yet been shifted through zeta zeros.  Therefore this stack
does not yet provide the zero residue sum, the twice-differenced contour
remainder, or an unconditional Omega theorem.
