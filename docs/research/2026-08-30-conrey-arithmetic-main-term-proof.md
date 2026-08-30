# Conrey 算术主项：统一加性渐近与初等外层求和

这一轮把算术主项的纸面证明补成了可逐项检查的推导：外层乘法权重
可以用 Dirichlet 卷积和调和和比较处理，不必再做一次 Perron 移线。
Euler 主常数的偏差还具有两个移位的乘积因子。内层 tapered Möbius
和仍明确使用 Conrey 1983 Lemma 10；这项已发表的解析输入尚未在本库
完成原生证明。因此下文是数学证明及形式化路线，不是整个算术渐近式
或 Conrey 40% 已经通过 Lean 的声明。

Sources: [Conrey 1983, Lemmas 10–11, printed pp. 54–57](https://aimath.org/~kaur/publications/3.pdf)
and [Conrey 1989, Lemma 1, printed pp. 12–13](https://aimath.org/~kaur/publications/24.pdf).
The relevant complete pages were visually checked. The outer convolution
argument below replaces the contour argument of the older Lemma 11.

Subsequent update: the [inner Möbius contour proof](2026-08-30-conrey-inner-mobius-contour-proof.md)
reconstructs the needed zero-order input from zero-free-region, Perron,
and Cauchy estimates instead of leaving Lemma 10 as a paper black box.
It also gives an exact Volterra reduction to the existing degree-one
Perron kernel. The native inner-sum theorem itself is still unfinished;
the new native analytic endpoint is the actual reciprocal-zeta strip bound.

## 1. Parameters and the smaller source-compatible neighborhood

Set `L=log T`, `theta=571/1000`, `y=T^theta`, `H=log y=theta L`,
`R=6/5`, `alpha=a/L`, `beta=b/L`. Keep fixed real polynomials `P_i`
with `P_i(0)=0`. On the two closed bidiscs centered at `(-R,-R)`
and `(R,R)`, use outer radius `21/40`; for Cauchy differentiation use
inner radius `1/2`. Then

\[
 \theta(R+21/40)=39399/40000<1,
\]

so both `|alpha|` and `|beta|` are strictly between `0` and `1/H`.
This matches Lemma 10's printed domain directly; no continuation through
zero shift or enlargement of that lemma is needed here.

The radius `3/5` in the earlier uniformity audit remains valid for the
abstract Cauchy reduction, but `theta(R+3/5)=5139/5000>1` would require
enlarging the source lemma. We choose the smaller disk to avoid that task.
On the inner negative disk, `|a+b|>=7/5` and `|exp(-a-b)|<=exp(17/5)`.
The degree-one Cauchy error multiplier is now

\[
 (1+(51/50)/(1/2))^2=5776/625.
\]

All following estimates are for sufficiently large `H`, uniformly on
these disks. Constants may depend on the fixed polynomials, not on the
shifts or the divisor index.

## 2. Exact gcd decomposition before any estimate

Write

\[
 F(d,s)=\prod_{p\mid d}(1-p^{-s}),\quad
 t_d=\frac{\log(y/d)}H,
\]

\[
 G_{i,d}(1+\alpha)=
 \sum_{\substack{n\le y/d\\(n,d)=1}}
 \frac{\mu(n)}{n^{1+\alpha}}
 P_i\!\left(\frac{\log(y/(dn))}H\right).
\]

The positive-real bases of complex powers use their real logarithms.
The actual finite arithmetic sum is

\[
 \Sigma(\alpha,\beta)=\sum_{1\le h,k\le y}
 \frac{\mu(h)\mu(k)\gcd(h,k)^{1+\alpha+\beta}}
      {h^{1+\alpha}k^{1+\beta}}\,
 P_1\!\left(\frac{\log(y/h)}H\right)
 P_2\!\left(\frac{\log(y/k)}H\right).
\]

Möbius inversion gives `g^s=sum_(d|g) d^s F(d,s)`. Substituting this
for `g=gcd(h,k)`, changing the finite summation order, and writing
`h=dn`, `k=dm` gives the exact identity

\[
 \Sigma(\alpha,\beta)=
 \sum_{d\le y}\frac{\mu(d)^2}{d}F(d,1+\alpha+\beta)
 G_{1,d}(1+\alpha)G_{2,d}(1+\beta).
\tag{S}
\]

The power of `d` is exactly `1/d`: the numerator `d^(1+alpha+beta)`
cancels both denominator shifts. The coprimality restrictions are necessary;
they follow from `mu(dn)=mu(d)mu(n)` on coprime inputs and vanishing when a
prime is repeated. No coprimality or squarefree stratum is discarded.

## 3. A uniform convolution averaging lemma

Suppose a multiplicative complex weight has local values

\[
 w(p)=f_p,\quad w(p^k)=0\ (k\ge2),\quad
 |f_p-1|\le A p^{-3/4},\quad |f_p|\le B.
\]

Let `h=w*mu` (Dirichlet convolution), so `w=1*h`. At prime powers,

\[
 h(p)=f_p-1,\quad h(p^2)=-f_p,\quad h(p^k)=0\ (k\ge3).
\]

The nonnegative Euler products, or their increasing finite products, give

\[
 \sum_{n\ge1}\frac{|h(n)|}{n^{3/4}}
 =\prod_p\left(1+\frac{|f_p-1|}{p^{3/4}}
                    +\frac{|f_p|}{p^{3/2}}\right)
 \le\exp\left((A+B)\sum_{n\ge2}n^{-3/2}\right).
\tag{M}
\]

Thus `sum |h(n)|(1+log n)/n` is bounded by a constant depending only
on `A,B`, even for a varying family of weights.

For `q` a complex `C^1` function on `[0,1]`, let `M_q` be the sum of
the suprema of `|q|` and `|q'|`. Finite reindexing gives

\[
 \sum_{n\le y}\frac{w(n)}n q(t_n)
 =\sum_{d\le y}\frac{h(d)}d
   \sum_{m\le y/d}\frac1m
      q\!\left(\frac{\log(y/d)-\log m}H\right).
\]

For `X=y/d>=1`, sum/integral comparison bounds the inner sum by

\[
 H\int_0^{\log X/H}q(u)\,du+O(M_q).
\]

Indeed the derivative of `q((log X-log x)/H)/x` has absolute value
at most `(||q||_infty+||q'||_infty/H)/x^2`; its integral over `[1,X]`
and the endpoint error are uniformly bounded. The change of variable
in the integral is exact. Replacing the upper limit by `1` costs at
most `||q||_infty log d`. Extending the coefficient sum from `d<=y`
to all `d` costs at most `||q||_infty sum_(d>y)|h(d)| log d/d`,
because `H<=log d` there. By (M),

\[
 \sum_{n\le y}\frac{w(n)}n q(t_n)
 =C_f H\int_0^1q(u)\,du+O_{A,B}(M_q),
\quad
 C_f=\sum_{d\ge1}\frac{h(d)}d
     =\prod_p(1-p^{-1})(1+f_p/p).
\tag{A}
\]

All series manipulations are justified by (M). This proves the needed
outer averaging statement without a zero-free region or a contour shift.

## 4. The actual complex weight and its double cancellation

For the weight arising after substitution of the inner main terms, put

\[
 f_p=\frac{1-p^{-1-\alpha-\beta}}
          {(1-p^{-1-\alpha})(1-p^{-1-\beta})},\qquad
 w(d)=\mu(d)^2\prod_{p\mid d} f_p.
\]

For `|alpha|,|beta|<=1/8`, all denominators are uniformly separated
from zero, `|f_p|` is uniformly bounded, and `|f_p-1|=O(p^(-3/4))`.
Thus (A) applies uniformly. If
`C_p=(1-1/p)(1+f_p/p)`, direct algebra gives

\[
 C_p-1=
 -\frac{p^{-2}(1-p^{-\alpha})(1-p^{-\beta})}
 {(1-p^{-1-\alpha})(1-p^{-1-\beta})}.
\tag{C}
\]

In particular either zero shift makes `C_p=1` exactly. Using
`|1-exp z|<=|z|exp|z|` gives the explicit bound

\[
 |C_p-1|\le16|\alpha\beta|(\log p)^2p^{-7/4}
 \qquad(p\ge2,\ |\alpha|,|\beta|\le1/8).
\tag{Q}
\]

For the denominator constant, each `|p^(-1-alpha)|<=3/4`, so the
two inverse factors cost at most `16`. The two exponential difference
bounds cost `|alpha beta|(log p)^2 p^(|alpha|+|beta|)`.

The prime majorant in (Q) is summable. The finite-product bound
`|prod(1+u_p)-1|<=exp(sum |u_p|)-1`, followed by its absolutely
convergent limit, proves

\[
 C_f=1+O(|\alpha\beta|)=1+O(H^{-2}).
\tag{CC}
\]

This is an additive statement, valid even when the eventual profile
integral vanishes. It is not obtained by dividing by that integral.

## 5. Uniform positive majorants for the inner error

Let `ell=log H`, `delta_0=1/ell`, and `b_0=1/(M ell)` for the fixed
sufficiently large constant `M` in Lemma 10. Take `H` sufficiently large
that `ell>=16` and `0<2b_0<=1`. Define

\[
 A_k(d)=\mu(d)^2 F_1(d,1-2/\ell)^k,\quad
 F_1(d,s)=\prod_{p\mid d}(1+p^{-s}).
\]

For each fixed `k`, its prime values are `1+O_k(p^(-7/8))`, uniformly
in this range of `ell`; (M) therefore applies with uniform constants.
The convolution argument and `sum_(m<=X) m^(b-1)<=X^b/b` imply

\[
 \sum_{d\le y}\frac{A_k(d)}d\ll_k H,\qquad
 \sum_{d\le y}\frac{A_k(d)}d(d/y)^b\ll_k b^{-1}
 \quad(0<b\le1).
\tag{P}
\]

The second bound follows after taking absolute values of the convolution
coefficients and using their uniformly bounded `sum |h(d)|/d`.
It does not require positivity of those convolution coefficients.

Also, for the retained shifts and sufficiently large `H`,
`|F(d,1+alpha+beta)|<=F_1(d,1-2/ell)` and
`|F(d,1+alpha)^(-1)|<<F_1(d,1-2/ell)` uniformly.
For the latter, bound the extra product of `(1-p^(-2s))^(-1)` by a
convergent Euler product with `s` bounded away from `1/2`.

## 6. Insert Lemma 10 and sum both error terms

The printed Lemma 10, with source parameter `1+alpha`, gives

\[
 G_{i,d}(1+\alpha)
 =\frac{\alpha P_i(t_d)+P_i'(t_d)/H}{F(d,1+\alpha)}
 +O\!\left(H^{-2}\ell^2[1+H(d/y)^{b_0}]
                F_1(d,1-2/\ell)\right).
\tag{G}
\]

Use it separately for the two fixed polynomials. Their main terms have
absolute size `O(H^(-1) F_1)`. Multiplying in (S), the absolute
main-times-error contribution is bounded by

\[
 H^{-3}\ell^2
 \sum_{d\le y}\frac{A_3(d)}d[1+H(d/y)^{b_0}]
 \ll H^{-2}\ell^3.
\]

The error-times-error contribution is bounded by

\[
 H^{-4}\ell^4
 \sum_{d\le y}\frac{A_3(d)}d
 [1+2H(d/y)^{b_0}+H^2(d/y)^{2b_0}]
 \ll H^{-2}\ell^5.
\]

These bounds use (P) at both `b_0` and `2b_0`, before dropping any
error. The boundary layer `d` near `y` cannot be neglected pointwise.

The product of the two main terms in (S) is

\[
 H^{-2}\sum_{d\le y}\frac{w(d)}d q(t_d),\qquad
 q=(P_1'+\alpha H P_1)(P_2'+\beta H P_2).
\]

This `q` has uniformly bounded `C^1` norm. Applying (A) and (CC) proves
the required **uniform additive arithmetic asymptotic**:

\[
 \boxed{\displaystyle
 \Sigma(\alpha,\beta)=\frac1H\int_0^1
 (P_1'+\alpha H P_1)(P_2'+\beta H P_2)\,dx
 +O(H^{-2}(\log H)^5).}
\tag{Final-A}
\]

Since `H=theta L`, this is the `o(1/L)` required by the shifted-moment
reduction. The fixed bidisc margin permits subsequent Cauchy
differentiation. The small parameters here are unrelated to the DI
dyadic parameters in the previous error-budget module.

## 7. Exact formalization boundary

`HardyTheorem.ConreyArithmeticEulerFactor` now proves the unconditional,
literal complex Euler-factor bound (Q), including actual denominators and
both shifts; its proof first establishes (C), denominator separation,
and exponential difference bounds.
It is not an axiom or a restatement of an assumed arithmetic asymptotic.

The full convolution averaging argument, its specialization to the
varying multiplicative weights, the exact finite identity (S), and the
analytic content of (G) still need native Lean implementations. The paper
argument above uses the published Lemma 10 as a proved mathematical input;
the future Lean theorem must prove it, not import it as an axiom.

The actual Gaussian/Estermann reduction, DI/Weil estimates, desmoothing,
integer-cutoff normalization, and final simple-zero limiting argument
remain outside this arithmetic result and remain unfinished.

## 8. Verification of this bounded implementation

- The original exact bound contract failed on the missing theorem before
  implementation. The completed contract also checks the exact identity,
  denominator lower bound, and each zero-shift specialization.
- `nice -n10 lake build Test.ConreyArithmeticEulerFactorContract
  Test.ConreyLongMomentErrorBudgetContract
  Test.ConreyV1MeanSquareTransferContract
  Test.ConreySelectedEtaMainCountContract
  Test.ConreyExplicitIntegralBridgeContract`: exit 0, 8871 jobs.
- The three new public endpoints use only `propext`, `Classical.choice`,
  and `Quot.sound`. The production module imports only Mathlib; there is
  no Zeta23 dependency or extra analytic axiom.
- Full Python regression: 546 passed. Target-inventory and chain-gap
  checks passed. Both new Lean files are default Lake roots.
- Independent paper and implementation reviews found no actionable issue.

These are targeted Lean checks, not a fresh whole-repository Lean baseline
or a claim that the paper's remaining analytic inputs have been formalized.
