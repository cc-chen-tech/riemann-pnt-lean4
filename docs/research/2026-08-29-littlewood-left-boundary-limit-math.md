# Littlewood's lemma with zeros on the limiting left edge

## Scope

This checkpoint removes the artificial hypothesis that the limiting left
edge of Conrey's Littlewood rectangle is zero-free.  It proves a general
epsilon upper bound for an analytic function with a finite zero divisor on a
closed rectangle.  It does **not** yet prove Conrey's equation (37): the
non-left boundary remainder is retained at a shifted left edge, and its
ordinary convergence back to the limiting edge is the next contour lemma.

## Correct direction of the shift

Let the limiting rectangle be

\[
 [x_0,x_1]\times [y_0,y_1],\qquad x_0<c<x_1,
\]

where only zeros with real part at least `c` are to be counted.  The safe
approximation moves the left edge **from the right**:

\[
 x_n>x_0,\qquad x_n<c,\qquad x_n\longrightarrow x_0,
\]

through vertical lines containing no zeros.  This excludes possible zeros
on `Re s=x_0` from every approximating rectangle, while every target zero
with `Re rho >= c` remains inside.  The target multiplicity mass is therefore
unchanged after filtering the finite divisor by `x_n<Re rho`.

Moving to `x_0-epsilon` is unnecessary and would require analyticity on a
larger rectangle.  The earlier route note used that direction; it is
corrected here.

## Why full L1 convergence is unnecessary

Write

\[
 I(x)=\int_{y_0}^{y_1}\log|f(x+it)|\,dt.
\]

Continuity on the compact rectangle gives a common upper bound
`log|f| <= C`.  At every ordinate which is not the imaginary part of a zero
on the limiting line,

\[
 \log|f(x_n+it)|\longrightarrow\log|f(x_0+it)|.
\]

The exceptional ordinate set is finite.  Apply Fatou's lemma to the
nonnegative functions

\[
 C-\log|f(x_n+it)|.
\]

Since logarithms of norms of real-meromorphic functions are interval
integrable even at zeros, this yields exactly the one-sided statement needed
for an upper zero count:

\[
 \forall\delta>0\quad\exists n\quad
 I(x_n)\le I(x_0)+\delta.
\]

No lower dominating function and no claim of full `L1` convergence is used.

## Littlewood inequality on the shifted rectangle

Let `P_n={rho in P : x_n<Re rho}`.  The zero-free shifted left line and the
strict bottom, top, and right divisor inequalities make every member of
`P_n` strictly interior to the shifted rectangle.  The existing exact
Littlewood identity applies to `P_n`.  Every zero with `Re rho>=c`
contributes at least `c-x_n`, so for the index selected by reverse Fatou,

\[
 2\pi(c-x_n)M_{\ge c}
 \le I(x_0)+\delta+R_{\mathrm{nonleft}}(x_n).
\]

This is the theorem
`exists_littlewoodRectangle_mass_le_logNormEdges_of_leftBoundaryZeros`.
Its support lemmas separately establish the reverse-Fatou epsilon principle,
interval integrability at vertical zeros, and almost-everywhere convergence
away from the finite exceptional ordinate set.

## Remaining ledger

1. Prove `R_nonleft(x_n) -> R_nonleft(x_0)` from zero-freeness of the selected
   horizontal sides and the fixed right side.
2. Apply the theorem to a tail sequence, so the Fatou-selected index is also
   far enough out for the remainder and `c-x_n` to be close to their limits.
3. Instantiate the finite divisor and a right-shifted zero-free sequence for
   the actual product `V1(s)B(s)` at the two selected heights.
4. Only then assemble equation (37), followed by equations (38)--(41) and the
   long mollified second moment.

