# Third-order contour-remainder budget

## Result

This slice supplies the missing quantitative estimate for all three non-right
edges of the genuine cubic zeta contour.

At a selected good height `T` in every interval `[A,A+1]`, on the rectangle
with left edge `Re(s)=-1`, right edge `Re(s)=c` and `1<c<=2`, it proves

`norm (thirdOrderContourRemainder x (-1) c (T/(2*pi)))`

is at most

`(2 * C*x^2*(1+log(A+6))^2*(c+1)/T^3
   + 2*T*thirdOrderOddVerticalBound x 0 T) / (2*pi)`.

## Mathematical content

The third-order kernel contributes one extra reciprocal height compared with
the existing second-order contour:

- each good-height horizontal point has size `O(x^2 log^2(A) / T^3)`;
- the integrated top and bottom edges retain the full `T^-3` factor;
- the negative-odd left edge gains a second reciprocal distance factor;
- choosing the fixed left line `Re(s)=-1` avoids trivial zeros and introduces
  the power factor `x^-1`.

Consequently, for a dynamic height `T` of order `x^alpha`, the displayed
polynomial parts behave like `x^(2-3*alpha)` horizontally and
`x^(alpha-1)` on the left. Both exponents are strictly negative precisely in
the nonempty window `2/3 < alpha < 1` (up to logarithmic factors).

## Scope boundary

This theorem bounds the actual contour remainder from the preceding cubic
explicit-formula PRs. It does not yet choose `A=x^alpha` inside Lean or prove
the resulting asymptotic limit; that parameter specialization should be a
separate small PR. No PNT error rate, Omega theorem, zero-free region, or RH
consequence is claimed here.
