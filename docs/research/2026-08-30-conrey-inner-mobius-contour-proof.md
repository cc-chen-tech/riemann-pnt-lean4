# Conrey 内层 Möbius 和：从现有零点自由区输入重建移线证明

上一轮的算术主项推导引用了 Conrey 1983 Lemma 10。本轮把所需的
零阶版本重新拆成完整的 Perron、留数和路径误差计算：现有零点自由区
内的 `logDeriv` 界已经足够，不必先证明独立的强 Mertens 定理，也不必
先达到原文所用的最强倒数 ζ 对数界。新的原生 Lean 输入选为下文 (Z)：
它控制实际的 `1/zeta`，不是把内层和或均方上界作为假设。

Source for comparison: [Conrey 1983, Lemma 10, printed pp. 54–56](https://aimath.org/~kaur/publications/3.pdf).
The full contour and residue pages were visually checked. The following
proof keeps only the zero-order statement needed by the arithmetic sum;
subsequent shift differentiation uses a fixed Cauchy neighborhood.

## 1. Choice of route and existing native inputs

One could first remove coprimality by convolution with integers supported
on primes dividing `d`. That route still needs a quantitative global
Möbius-sum estimate and uniform logarithmic moments of the extra factors.
There is no need to construct that additional route here: the existing
native zero-free-region and horizontal Grönwall theorems apply directly
to the Mellin integrand with its finite Euler factors retained.

The relevant existing theorems are:

- `ZeroFreeRegion.exists_riemannZeta_ne_zero_and_norm_logDeriv_le_log_sq_on_inner_zeroFreeRegion`;
- `HardyTheorem.norm_inv_riemannZeta_selbergS12MovingRightPoint_le`;
- `HardyTheorem.norm_selbergS12ReciprocalAlong_le_mul_exp`.

They give constants `c0>0`, `C>=0`, `T0>=2` such that
`zeta(sigma+it)!=0` and `|zeta'/zeta|<=C log^2|t|` when
`T0<=|t|` and `1-c0/(2 log|t|)<=sigma<=2`.
The absolutely convergent right point `1+a/log|t|` has reciprocal bound
`1+log|t|/a`.

Choose

\[
 c=\min\{c_0/2,\,1/(8(C+1))\},\qquad
 T_1=\max(T_0,e^c).
\]

Then `0<c<=1`, and for `|t|>=T1`, `L_t=log|t|` is positive with
`c<=L_t`. If `1-c/L_t<=sigma<=1+c/L_t`, the horizontal distance
from the right point is at most `2c/L_t`. The entire segment is in
the inner zero-free strip. Grönwall therefore costs at most

\[
 \exp(C L_t^2\,2c/L_t)\le\exp(L_t/4).
\]

For `1+c/L_t<=sigma<=2`, absolute convergence itself gives the same
bound without that exponential loss. In both cases,

\[
 \boxed{\zeta(\sigma+it)\ne0,\qquad
 |\zeta(\sigma+it)^{-1}|
 \le(1+\log|t|/c)\exp(\log|t|/4)}
\tag{Z}
\]

uniformly for `|t|>=T1`, `1-c/log|t|<=sigma<=2`.
Both signs of `t` and both endpoints are included. This is the selected
Lean endpoint; no norm bound for the actual Möbius sum is an input.

## 2. Parameters and the actual inner sum

Let `H=log y`, `ell=log H`, `delta=1/ell`, and fix a polynomial `P`
with `P(0)=0`. For integers `1<=d<=y`, first allow any `1<=X<=y`
and set `t_d=log X/H`; the application takes `X=y/d`.
Let the complex shift satisfy `|alpha|<=1/H`. Write

\[
 F_d(s)=\prod_{p\mid d}(1-p^{-s}),\quad
 B_d=\prod_{p\mid d}(1+p^{-(1-2\delta)}),
\]

\[
 G_d(\alpha)=\sum_{\substack{1\le n\le X\\(n,d)=1}}
 \frac{\mu(n)}{n^{1+\alpha}}
 P\!\left(\frac{\log(X/n)}H\right).
\]

All positive-base powers use real logarithms. All thresholds below are
absolute or depend only on `P`, never on `d`, `X`, or `alpha`.
Take `H` sufficiently large and set

\[
 K=H^4,\qquad b=\frac{c}{4\log K}=\frac{c}{16\ell},\qquad u=2/H.
\]

We may require `ell>=16`, `1/H<=b`, and `b+1/H` smaller than a
fixed zero-free width at bounded height. At high height, throughout
the rectangle `-b<=Re w<=u`, `|Im w|<=K`, the point
`s=1+alpha+w` has `|Im s|<=K+1` and

\[
 \Re s\ge1-2b\ge1-c/\log(K+1).
\]

Thus (Z) applies wherever `|Im s|>=T1`. Compact-height zero-freeness
around the one-line and the regularized simple pole handle the remaining
bounded portion. There are no zeta zeros in this rectangle. The apparent
singularity of `1/zeta(1+z)` at `z=0` is removable, with value zero.

## 3. Finite Euler factors and residue bounds

For `Re s>=1-2delta>=7/8`, reverse triangle inequality and
`(1-r)^(-1)=(1+r)/(1-r^2)` give

\[
 |F_d(s)^{-1}|\le
 B_d\prod_p(1-p^{-7/4})^{-1}\ll B_d.
\tag{F}
\]

This bound is uniform in `d`; replacing the finite product by the full
convergent positive Euler product just supplies an absolute constant.

Define `W_d(z)=(zeta(1+z) F_d(1+z))^(-1)` on the zero-free shifted
rectangle and the right half-plane, with its removable value `W_d(0)=0`.
This is the global function used on the Perron path. Near zero only,
write the holomorphic regularization as
`1/zeta(1+z)=z U(z)`, where `U(0)=1`. On a fixed small disk,
`U,U'` are bounded and `U(z)-1=O(|z|)`.
Set `E_d(z)=1/F_d(1+z)`; then locally `W_d(z)=z U(z) E_d(z)`.
The disk centered at `alpha` of radius `delta` is inside `|z|<=2delta`
for large `H`; (F) bounds `E_d` there. Cauchy's estimate yields
`E_d'(alpha)=O(B_d/delta)` and, for each fixed `r>=2`,

\[
 W_d(\alpha)=\alpha E_d(\alpha)+O(H^{-2}B_d),
\]

\[
 W_d'(\alpha)=E_d(\alpha)+O(H^{-1}\delta^{-1}B_d),\qquad
 \frac{|W_d^{(r)}(\alpha)|}{r!}\ll_P B_d\delta^{1-r}.
\tag{R}
\]

For the higher derivatives use `|W_d(z)|<<delta B_d` on that circle.
The first derivative estimate follows by differentiating `z U(z) E_d(z)`;
no prime-sum estimate for `F_d'/F_d` is required.

## 4. Perron identity and exact residue

Write `P(v)=sum_(j=1)^J p_j v^j`. Absolute convergence on `Re w=u`
and the log-power Perron kernel give the actual identity

\[
 G_d(\alpha)=\sum_{j=1}^J\frac{p_j j!}{H^j}\frac1{2\pi i}
 \int_{u-i\infty}^{u+i\infty}
 \frac{X^w W_d(\alpha+w)}{w^{j+1}}\,dw.
\tag{P}
\]

The coprime Dirichlet series is exactly `1/(zeta(s) F_d(s))` for
`Re s>1`. At `n=X`, if that endpoint is an integer, the kernel is zero
because `j>=1`; no half-weight convention changes the identity.

Move each truncated integral to `Re w=-b`. The only possible integrand
pole is at `w=0`; the zero at `w=-alpha` does not create a pole.
The sum of residues, including all factorials and powers of `H`, is

\[
 \sum_{r=0}^J \frac{P^{(r)}(t_d)}{r! H^r}W_d^{(r)}(\alpha).
\]

Using (R), `H delta>=1`, and bounded polynomial derivatives on `[0,1]`,
this becomes

\[
 \frac{\alpha P(t_d)+P'(t_d)/H}{F_d(1+\alpha)}
 +O_P(H^{-2}\ell B_d).
\tag{M}
\]

## 5. All path errors, including the near-y boundary layer

On the original right line, `Re(1+alpha+w)>=1+1/H` and absolute
convergence gives `|1/zeta|<<H`. Since `X^u<=e^2`, the omitted tails
for the `j`th kernel cost

\[
 O_P(B_d H^{1-j}K^{-j})=O_P(B_d H^{-4})\quad(j\ge1).
\]

On the two horizontal connectors, (Z) is
`O(K^(1/4) log K)`; the connector length is bounded, `|w|>=K`,
and `X^(Re w)<=e^2`. Their cost after the factor `H^(-j)` is

\[
 O_P(B_d H^{-j}K^{-j-3/4}\log K)=O_P(B_d H^{-2}).
\]

On `w=-b+iv`, `X^(Re w)=X^(-b)`. For small fixed `|v|`, regularity
at the zeta pole and `|alpha|<=b<=|w|` imply
`|W_d(alpha+w)|<<B_d |w|`. Thus the `j=1` local integral is
`O(B_d(1+log(1/b)))`, and each `j>=2` local integral is
`O_P(B_d b^(1-j))`. The bounded-height part away from zero contributes
`O_P(B_d)`. On the high-height part, (Z) gives the integrable majorant

\[
 B_d(1+|v|)^{-j-3/4}\log(3+|v|).
\]

Consequently the entire left edge, with the polynomial factors restored,
costs `O_P(B_d H^(-1) ell X^(-b))`, since `Hb>=1` for large `H`.
No pointwise smallness is asserted when `d` is near `y`.

Combining the exact identity, residues, and all five path pieces proves
the following paper estimate, including `alpha=0`:

\[
 \boxed{G_d(\alpha)=
 \frac{\alpha P(t_d)+P'(t_d)/H}{F_d(1+\alpha)}
 +O_P\!\left(B_d[H^{-2}\ell+H^{-1}\ell X^{-b}]\right).}
\tag{G0}
\]

At `X=y/d` this implies the weaker `H^(-2) ell^2 [1+H(d/y)^b] B_d`
form used in the preceding arithmetic main-term audit. The positive
majorant sums there remain applicable, with `1/b=16ell/c=O(ell)`.

## 6. Avoiding new higher-order Perron kernels in the native route

The paper calculation above handles all monomials, but native code need
not introduce a new Mellin inversion theorem for every power. The existing
degree-one kernel suffices via the following exact Volterra identity.
For fixed `d,alpha,H`, write

\[
 S_{1,d}(v)=\sum_{\substack{1\le n\le v\\(n,d)=1}}
       \frac{\mu(n)}{n^{1+\alpha}}\log(v/n).
\]

For any fixed `C^2` profile with `P(0)=0`, Taylor's integral formula and
finite sum/integral interchange give

\[
 G_d(\alpha;X)=\frac{P'(0)}H S_{1,d}(X)
 +\frac1{H^2}\int_1^X
 P''\!\left(\frac{\log(X/v)}H\right)S_{1,d}(v)\,\frac{dv}{v}.
\tag{V}
\]

For each summand, the substitution `u=log(X/v)/H` turns the integral
into `int_0^t P''(u)(t-u) du`, where `t=log(X/n)/H`.
Terms vanish at `v=n`, so cutoffs and integer endpoints cause no correction.
The sums are finite on `[1,X]`; continuity of the logarithmic taper
supplies ordinary integrability.

The `P(t)=t` case of Sections 2–5 is uniform for every `1<=v<=y`,
with the original `H,d,alpha,b` unchanged. After multiplying it by `H`,

\[
 S_{1,d}(v)=\frac{\alpha\log v+1}{F_d(1+\alpha)}
 +O\!\left(B_d[H^{-1}\ell+\ell v^{-b}]\right).
\]

Its main term in (V) is exactly
`(alpha P(t_d)+P'(t_d)/H)/F_d(1+alpha)`.
Indeed, set `r=log v/H` in the integral; the two identities
`int_0^t P''(t-r) dr=P'(t)-P'(0)` and
`int_0^t r P''(t-r) dr=P(t)-t P'(0)` cancel the extra endpoint terms.

For the error, `log X<=H` and
`int_1^X v^(-b) dv/v=(1-X^(-b))/b<=1/b` show that (V) costs at most

\[
 O_P\!\left(B_d[H^{-2}\ell^2+H^{-1}\ell X^{-b}]\right).
\tag{GV}
\]

Here `1/b=O(ell)`; no varying profile or varying shift is introduced.
This is slightly weaker than the direct polynomial bound (G0), but
implies exactly the error form required by the arithmetic sum. The
native implementation can therefore use the already-proved degree-one
Perron kernel, followed by the finite identity (V).

## 7. Native proof boundary

The mathematical argument reconstructs the needed inner estimate from
zero-free-region, Perron, Cauchy, and elementary finite Euler products.
It does not assume the inner estimate, a Mertens estimate, or a mollified
mean-square theorem.

`HardyTheorem.ConreyReciprocalZetaStrip` now proves (Z) from the three existing
native inputs in Section 1. The existing `SelbergPerronKernel` and
`SelbergPerronLSeries` already provide the degree-one logarithmic kernel
and absolute L-series interchange; those are reusable, not new gaps.
Native implementations of the finite Volterra profile transfer and actual
coprime Perron identity, local residue/Cauchy calculation, all path
integrability and contour transfers, and their assembly into (GV)
remain necessary. The previous arithmetic outer average and the actual
Gaussian/Estermann/DI mean-square chain also remain unfinished.

## 8. Verification

- After building the required existing dependencies, the exact contract
  failed on the missing `exists_conrey_reciprocal_zeta_quarterPower_strip`.
  The earlier missing-import failure was not counted as the RED check.
- `nice -n10 lake build Test.ConreyReciprocalZetaStripContract
  Test.ConreyArithmeticEulerFactorContract
  Test.ConreyLongMomentErrorBudgetContract
  Test.ConreyV1MeanSquareTransferContract
  Test.ConreySelectedEtaMainCountContract`: exit 0, 8874 jobs.
- The new endpoint depends only on `propext`, `Classical.choice`, and
  `Quot.sound`. Its nine local-module import closure has no Zeta23;
  the only external root is Mathlib. Both module and contract are Lake roots.
- Full Python regression: 546 passed. Target inventory and chain-gap
  checks passed; `git diff --check` was clean.
- Independent mathematical and source review found no remaining issue
  after clarifying the global regularized function and the native (GV) target.

These are targeted Lean checks, not a new full-repository baseline or a
claim that the complete inner sum or Conrey mean value has been formalized.
