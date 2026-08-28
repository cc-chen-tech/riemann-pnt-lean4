# Littlewood left-boundary tail limit

## Mathematical statement

Let `x_n > x_0`, `x_n < c`, and `x_n -> x_0`, with every vertical line
`Re s = x_n` free of zeros.  Write

\[
 A_n=2\pi(c-x_n)M_{\ge c},\qquad
 R_n=R_{\mathrm{nonleft}}(x_n).
\]

The reverse-Fatou checkpoint proves that for every `delta>0` there is some
index `n` such that

\[
 A_n\le I(x_0)+\delta+R_n.
\tag{1}
\]

The existential index in (1) is not automatically late enough to use
`A_n -> A_0` and `R_n -> R_0`.  The correct repair is to apply (1) to every
tail `x_{k+N}`.  Its selected index is then at least `N` in the original
sequence.

Given `epsilon>0`, choose `N` so that for every `n>=N`,

\[
 |A_n-A_0|<\epsilon/3,
 \qquad |R_n-R_0|<\epsilon/3.
\]

Apply (1) to the `N`-tail with `delta=epsilon/3`.  For its selected index,

\[
 A_0\le A_n+\epsilon/3
 \le I(x_0)+R_n+2\epsilon/3
 \le I(x_0)+R_0+\epsilon.
\]

Letting `epsilon` decrease to zero gives the exact limiting inequality

\[
 \boxed{2\pi(c-x_0)M_{\ge c}\le I(x_0)+R_{\mathrm{nonleft}}(x_0).}
\]

This uses only one-sided upper semicontinuity of the left logarithmic
integral.  It does not assume full `L^1` convergence across boundary zeros.

## Conrey specialization boundary

At `x_0=1/2-R/L` and `c=1/2`, the coefficient is exactly `R/L`.  The two
selected horizontal segments supply the zero-free hypotheses and the
previous edge estimates control `R_nonleft(x_0)`.  What remains after this
generic theorem is to instantiate the finite zero divisor and the
right-shifted zero-free lines for the actual product `V_1(s)B(s)`.
