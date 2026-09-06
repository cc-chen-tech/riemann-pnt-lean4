# Conrey moving-right argument variation: paper-first closure

## 1. Exact remaining term

Write

\[
 A=2\log L,\qquad
 F(s)=V_1(s)B(s),\qquad 40000\le L.
\]

After the two selected horizontal terms are controlled, the last boundary
term in the repository's exact form of Conrey's equation (37) is

\[
 (A-\sigma_0)\int_{t_0}^{t_1}
   \operatorname{Re}{F'\over F}(A+it)\,dt.                 \tag{RA-37}
\]

The global estimate for `integral |log |F||` does not control this integral:
the latter is argument variation, not modulus variation.

## 2. Right-half-plane route

It is unnecessary to estimate `|F'/F|` pointwise.  The already proved
approximations force the image of the complete right edge into the open right
half-plane.

### Low part

For `1 <= t <= A`, the existing theorems give

\[
 |V_1(A+it)-49/100|\le 1/50,
 \qquad |B(A+it)-1|\le 3/L.
\]

Since `|B| <= 1+3/L <= 2`,

\[
 |V_1B-49/100|
 \le |V_1-49/100|\,|B|+{49\over100}|B-1|
 \le {1\over20}.
\]

Consequently `Re F(A+it) >= 49/100-1/20 > 2/5`.

### High part

For `A <= t <= exp L`, the height main term `a_L(t)` is real and satisfies

\[
 a_L(t)\ge {1\over3},\qquad |F(A+it)-a_L(t)|\le {79\over L}.
\]

At `L >= 40000`, `79/L <= 1/30`; hence

\[
 \operatorname{Re}F(A+it)\ge {1\over3}-{1\over30}={3\over10}.
\]

Splitting at `A` therefore proves the uniform global statement

\[
 {3\over10}\le \operatorname{Re}F(A+it)
 \quad(1\le t\le e^L).                                  \tag{RA-positive}
\]

This estimate is stronger than mere nonvanishing and fixes one logarithm
branch on the entire edge.

## 3. Fundamental theorem of calculus

The actual product is analytic at every `A+it` in this interval.  By
`RA-positive` its values lie in the slit plane, so the principal complex
logarithm is differentiable along the path.  The existing vertical derivative
identity gives

\[
 {d\over dt}\operatorname{Im}\log F(A+it)
   =\operatorname{Re}{F'\over F}(A+it).
\]

The fundamental theorem of calculus then yields the exact identity

\[
 \int_{t_0}^{t_1}\operatorname{Re}{F'\over F}(A+it)\,dt
 =\arg F(A+it_1)-\arg F(A+it_0).                         \tag{RA-FTC}
\]

Every number with nonnegative real part has principal argument in
`[-pi/2,pi/2]`.  Thus

\[
 \left|\int_{t_0}^{t_1}\operatorname{Re}{F'\over F}(A+it)\,dt\right|
 \le\pi.                                                  \tag{RA-bound}
\]

Using the already proved width bound `A-sigma0 <= 2L`, the contribution in
`RA-37` is at most `2 pi L <= 8L`.  Finally

\[
 {8L\over e^L/L}=8L^2e^{-L}\longrightarrow0.
\]

Hence the far-right argument term is `o(e^L/L)` without spending any
cancellation used by the horizontal Jensen estimates.

## 4. Formal interfaces

The Lean layer should expose, in this order:

1. low-part product distance from `49/100`;
2. low, high, and global real-part lower bounds;
3. the exact `RA-FTC` identity for the actual product;
4. `RA-bound`, followed by the width-weighted polynomial bound and its
   exponential smallness.

This closes only the far-right argument term.  The exact equation-(37)
assembly, selected-height-to-all-height transfer, equations (38)--(41), and
the long mollified second moment remain separate gates.
