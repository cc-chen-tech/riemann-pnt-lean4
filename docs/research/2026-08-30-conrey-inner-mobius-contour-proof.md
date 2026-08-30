# Conrey 内层 Möbius 和：从现有零点自由区输入重建移线证明

上一轮的算术主项推导引用了 Conrey 1983 Lemma 10。本轮把所需的
零阶版本重新拆成完整的 Perron、留数和路径误差计算：现有零点自由区
内的 `logDeriv` 界已经足够，不必先证明独立的强 Mertens 定理，也不必
先达到原文所用的最强倒数 ζ 对数界。新的原生 Lean 输入选为下文 (Z)：
它控制实际的 `1/zeta`，不是把内层和或均方上界作为假设。

后续推进已原生证明下文 (P1)：任意复移位和正实数截断下，实际互素
Möbius 有限和等于真实 Euler 因子被积函数的 Perron 积分，且该积分
绝对可积。这一步补齐移线的起点，不代表完整移线或渐近已经形式化。

再下一步已原生证明 (R0) 与 (RC)：统一于互素参数的解析正规化、二次局部
误差及实际圆周留数，包括零移位。第 12 节进一步构造任意大高度下的
实际无零矩形并证明精确留数恒等式。整线尾积分拼接、移位导数误差和
路径大小估计仍未闭合，完整内层渐近尚未完成。

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
Let `0<kappa<=c` be the uniform compact/high-height constant constructed
in Section 12. Take `H` sufficiently large and set

\[
 K=H^4,\qquad b=\frac{\kappa}{4\log K}=\frac{\kappa}{16\ell},\qquad u=2/H.
\]

We may require `ell>=16` and `1/H<b`. Section 12 then gives the full
zero-free rectangle, including bounded heights. At high height, throughout
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

The degree-one identity needs only `d>=1`, `X>0`, `u>0` and
`Re(alpha)+u>0`, without the later large-`H` restrictions. Explicitly,

\[
 \frac1{2\pi}\int_{\mathbb R}
 \frac{X^{u+it}}{(u+it)^2\zeta(1+\alpha+u+it)F_d(1+\alpha+u+it)}\,dt
 =\sum_{\substack{1\le n\le\lfloor X\rfloor\\(n,d)=1}}
 \mu(n)n^{-1-\alpha}\log(X/n).
\tag{P1}
\]

This is the unnormalized logarithmic sum `S_1`, not `G`:
the linear profile `P(v)=v` adds the factor `1/H` only afterwards.
The principal character modulo `d` is the coprimality indicator, and
its Möbius twist is the reciprocal principal-character L-series.
Absorbing `n^(-1-alpha)` into its coefficients gives the exact shift
`s=1+alpha+w`, including complex `alpha`.

On the vertical line the sum of absolute term norms is bounded by

\[
 \frac{X^u}{u^2+t^2}
 \sum_{\substack{n\ge1\\(n,d)=1}}\frac{|\mu(n)|}{n^{1+\Re\alpha+u}}.
\]

The numerical series converges and the displayed function is integrable
in `t`. Thus the full integrand is absolutely integrable, independently
of conventions for totalized Bochner integrals. The logarithmic kernel
is zero beyond `X` and equals `log(X/n)` below it. At `X=n` it is zero;
for `0<X<1` the finite sum is empty, and at `X=1` it is also zero.
The `dt/(2*pi)` normalization follows from `dw=i dt` on the upward line.

For the exact local residue, use the already constructed analytic pole unit
`Q(s)`, with `Q(1)=1` and `Q(s)=(s-1)zeta(s)` away from `0,1`.
Define actual functions

\[
 U(z)=Q(1+z)^{-1},\qquad E_d(z)=F_d(1+z)^{-1},\qquad
 W_d(z)=zU(z)E_d(z).
\]

Analyticity at zero and `U(0)=1` select `r>0`, `r<=1/4` and `C>0`
such that `U` is analytic and `|U(z)-1|<=C|z|` on `|z|<=r`.
The radius and constant are selected **before d**. Every finite Euler
factor is nonzero when `Re(1+z)>0`, since `|p^(-1-z)|<1`.
Hence every `W_d` is analytic on that same closed disk and

\[
 W_d(0)=0,\qquad W_d'(0)=E_d(0),\qquad
 |W_d(z)-zE_d(z)|\le C|z|^2|E_d(z)|.
\tag{R0}
\]

For `X>0`, `|alpha|<rho` and `|alpha|+rho<=r`, Cauchy's derivative
formula for `f(w)=X^w W_d(alpha+w)` gives

\[
 \oint_{|w|=\rho}
 \frac{X^w}{w^2\zeta(1+\alpha+w)F_d(1+\alpha+w)}\,dw
 =2\pi i\{\log X\,W_d(\alpha)+W_d'(\alpha)\}.
\tag{RC}
\]

The circle integrand is integrable by continuity on the circle.
Its equality with the regularized kernel holds at every boundary point:
`|alpha|<rho` excludes `alpha+w=0`, and the disk lies in `Re(1+z)>0`.
One must not identify the raw totalized Lean reciprocal at `z=0`
with this analytic extension. At `alpha=0`, (RC) correctly reduces
to `2*pi*i*E_d(0)`. It does not yet replace the exact residue by
the shifted approximate main term or justify the rectangular contour transfer.

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
majorant sums there remain applicable, with `1/b=16ell/kappa=O(ell)`.

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
`HardyTheorem.ConreyCoprimeMobiusPerron` now proves (P1), including
absolute integrability of the actual Euler integrand, arbitrary complex
shift with `Re(alpha)+u>0`, and every positive real cutoff. The generic
full-line integrability theorem is added to `SelbergPerronLSeries` and
derived from actual summability, not assumed. The native endpoint
expands the actual finite coprime Möbius sum, not an abstract series.

`HardyTheorem.ConreyCoprimeMobiusResidue` now proves (R0) and (RC),
with the common radius and quadratic-error constant chosen before `d`.
The actual Euler integrand is identified on every circle boundary point;
no equality with the raw totalized reciprocal at `z=0` is claimed.

The rectangle derivative formula and actual local-rectangle residue are
implemented in Section 11. Section 12 additionally proves the high-rectangle
zero-free assembly and exact actual residue. Native implementations of the
finite Volterra profile transfer, shifted derivative/Cauchy error bounds,
the path norm estimates and full-line tail assembly, and their combination
into (GV) remain necessary. The eventual specialization of the geometric
parameters in Section 12 is presently a paper calculation.
The previous arithmetic outer average and the actual
Gaussian/Estermann/DI mean-square chain also remain unfinished.

## 8. Verification: reciprocal strip

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

## 9. Verification: actual coprime Perron identity

- The new literal contract first failed only on the two missing intended
  endpoints, after the existing dependencies had been built successfully.
- `nice -n10 lake build Test.ConreyCoprimeMobiusPerronContract
  HardyTheorem.SelbergS12PerronIdentity
  Test.ConreyReciprocalZetaStripContract
  Test.ConreyArithmeticEulerFactorContract`: exit 0, 8721 jobs.
- Both `conrey_coprime_mobius_log_perron` and the generic
  `integrable_selbergPerronLSeriesIntegrand` use only `propext`,
  `Classical.choice`, and `Quot.sound`. The new module's eleven-local-module
  import closure contains no Zeta23; the only external root is Mathlib.
- The existing `Test/SelbergPerronLSeriesContract.lean` and
  `Test/SelbergS12PerronIdentityContract.lean` were each checked separately
  with `lake env lean`: both exit 0. The new module and contract are Lake roots.
- Final Python regression: 546 passed (12.76s). Target inventory and
  chain-gap checks passed; `git diff --check` was clean.
- Independent read-only review found no remaining issue in the actual
  coefficient, complex shift, integrability, real floor cutoff, endpoints,
  normalization, or distinction between `S1` and `G=S1/H`.

Only targeted Lean verification is claimed, not a fresh whole-repository
baseline or a proof of the complete inner asymptotic or Conrey theorem.

## 10. Verification: actual regularization and circle residue

- The fully expanded new contract first failed only on the missing
  `exists_conrey_coprime_mobius_local_residue` endpoint.
- `nice -n10 lake build Test.ConreyCoprimeMobiusResidueContract
  Test.ConreyCoprimeMobiusPerronContract
  Test.ConreyReciprocalZetaStripContract
  Test.ConreyArithmeticEulerFactorContract`: exit 0, 8722 jobs.
- The endpoint and the actual Euler-reciprocal correspondence use only
  `propext`, `Classical.choice`, and `Quot.sound`. The module's six-local-module
  import closure contains no Zeta23; its only external root is Mathlib.
  Both new module and contract are Lake roots.
- Python regression: 546 passed (13.43s). Target inventory and chain-gap
  checks passed; the diff whitespace check was clean.
- Independent read-only review verified the uniform quantifiers, the
  actual pole unit, retained `|E_d|` error factor, circle boundary
  correspondence, integrability, normalization, and zero-shift case.

These checks do not prove the rectangular contour transfer, the shifted
derivative error, or the full inner/outer/long-moment asymptotics.

## 11. 从圆周留数到矩形公式：精确完成范围

这一步证明任意包含零的矩形上的二阶 Cauchy 核公式，并将它接到
实际互素 Möbius 被积函数。实际特化目前只覆盖统一解析小圆盘内的
矩形；**不是**高度 `K=H^4` 的长矩形移线或其误差界。

Let `R=[a,b]+i[c,d]`, with `a<0<b` and `c<0<d`, and let `f` be
holomorphic on `R`. Twice removing a divided difference gives a holomorphic
function `g` on `R` satisfying, for `w != 0`,

\[
 \frac{f(w)}{w^2}
 =g(w)+\frac{f'(0)}w+\frac{f(0)}{w^2}.
\]

The first integral is zero by Cauchy–Goursat. The second is
`2*pi*i*f'(0)` by the proved simple-pole rectangle formula. The last has
the single-valued primitive `-f(0)/w` on every edge. The real fundamental
theorem on each affine edge gives cancellation at all four corners.
All four edge integrals are integrable; orientation is bottom minus top
plus `i` times right minus `i` times left. Thus

\[
 \oint_{\partial R}\frac{f(w)}{w^2}\,dw=2\pi i f'(0).
 \tag{RD}
\]

`MathlibAux.RectangleCauchyDerivative` proves (RD) with no assumption
that `f(0)=0` and without using the unproved general meromorphic-residue
proposition. In particular the independent polynomial check
`f(w)=3+7w+11w^2` on `[-2,3]+i[-4,5]` has integral `2*pi*i*7`.

For the actual function take `f(w)=X^w W_m(alpha+w)`, with `X>0`.
Choose the common radius from (R0) **before** choosing `m`. Assume only
the geometric conditions `alpha+R` lies in that disk, and both `0` and
`-alpha` are strictly inside `R`. The latter keeps every boundary point
away from the raw reciprocal's removable point; it does not exclude
`alpha=0`. On the boundary the actual Euler expression agrees with `W_m`,
so (RD) gives

\[
 \oint_{\partial R}
 \frac{X^w}{w^2\zeta(1+\alpha+w)F_m(1+\alpha+w)}\,dw
 =2\pi i\bigl(\log X\,W_m(\alpha)+W_m'(\alpha)\bigr).
 \tag{RL}
\]

`HardyTheorem.ConreyCoprimeMobiusRectangle` proves (RL) with the actual
Euler expression and actual pole-unit regularization, not a supplied
surrogate. The geometric premises are nonvacuous: at `alpha=0`, the square
`[-r/4,r/4]+i[-r/4,r/4]` is contained in the common disk, for every `m`.
Section 12 extends analyticity to the high rectangle. Estimating its edges
and attaching the full-line tails is still required before these identities
give the full shifted Perron estimate.

Verification of this local step:

- Both exact contracts first failed on the intended missing theorem names,
  with the existing imports already built. The generic contract also checks
  the nonzero constant term and nonsymmetric rectangle above.
- `nice -n10 lake build Test.RectangleCauchyDerivativeContract
  Test.ConreyCoprimeMobiusRectangleContract
  Test.ConreyCoprimeMobiusResidueContract
  Test.ConreyCoprimeMobiusPerronContract`: exit 0, 8721 jobs.
- Both new endpoints use only `propext`, `Classical.choice`, and `Quot.sound`.
  The actual endpoint has ten local modules in its import closure, no Zeta23,
  and only Mathlib as an external root. Both modules and contracts are Lake roots.
- Python regression: 546 passed. Target inventory and chain-gap checks
  passed; the diff whitespace check was clean.
- Independent read-only review found no issue in the decomposition, corner
  cancellation, integrability, actual Euler correspondence, uniform radius,
  zero shift, or restricted local scope.

Only targeted Lean verification is claimed; this is not a whole-repository
baseline, GitHub CI pass, or completion of the full shifted contour estimate.

## 12. 任意大高度的无零矩形与实际留数

这一步解除第 11 节的小圆盘限制。统一常数在高度和互素模数之前选取；
完整矩形上的解析性由实际 ζ 的性质推出，不作为调用方假设。

Write `Q(s)=(s-1)zeta(s)` with its analytic value `Q(1)=1`.
For each fixed `T`, the segment `{1+it: |t|<=T}` is compact and lies
in the open set `{s: Re s>0, Q(s)!=0}`. An open thickening contains
the segment, so there is `delta_low>0`, `delta_low<=1/4`, such that
`Q(sigma+it)!=0` when `|t|<=T` and `1-delta_low<=sigma<1`.
The existing one-line/right-half-plane theorem covers all `sigma>=1`.

Take the height `T` and constant `c` from (Z), and set
`kappa=min(c,delta_low)`. For every `K>=2`, put

\[
 q_K=\frac{\kappa}{1+\log(K+2)}.
\]

We have `q_K<=delta_low`. If `T<=|t|<=K`, monotonicity of the positive
logarithm gives `q_K<=c/log|t|`. Thus low and high estimates cover the
entire closed rectangle `1-q_K<=Re s<=2`, `|Im s|<=K`. In particular
`Q(s)!=0`, including `s=1`. Finite Euler factors have no zero for
`Re s>0`, so the actual `W_m(z)=z/Q(1+z)/F_m(1+z)` is analytic at
every point

\[
 -q_K\le\Re z\le1,\qquad |\Im z|\le K.
 \tag{HA}
\]

The theorem `exists_conrey_coprime_mobius_analytic_rectangles` proves
(HA) and the actual pole-unit nonvanishing, with one `kappa` for all
heights and moduli.

For the shifted rectangle `R=[-b,u]+i[-K,K]`, assume

\[
 K\ge2,\quad X>0,\quad |\alpha|<\min(b,u),\quad
 b+|\alpha|\le\frac{\kappa}{1+\log(K+3)},\quad u+|\alpha|\le1.
\]

These inequalities imply `|alpha|<=1`, so the imaginary shift fits in
height `K+1`. Applying (HA) at that height proves actual analyticity
on `alpha+R`. Both `0` and `-alpha` are strictly inside `R`. The common
contour calculation from Section 11 then proves

\[
 \oint_{\partial R}
 \frac{X^w}{w^2\zeta(1+\alpha+w)F_m(1+\alpha+w)}\,dw
 =2\pi i\bigl(\log X\,W_m(\alpha)+W_m'(\alpha)\bigr).
 \tag{HR}
\]

`exists_conrey_coprime_mobius_high_rectangle_residue` proves both the
analyticity and (HR). The refactored helper is conditional only as a
shared calculation; both local and high callers discharge all its
analytic assumptions for the fixed actual function.

The Section 2 parameters meet these conditions eventually: with
`K=H^4`, `u=2/H`, `b=kappa/(16log H)`, and `|alpha|<=1/H`, choose
`H>=3`, `log H>=1`, and `1/H<b`. Then
`1+log(H^4+3)<=8log H`, hence
`b+|alpha|<2b<=kappa/(1+log(K+3))`, while
`u+|alpha|<=3/H<=1`. This eventual parameter specialization is a
paper check, not yet a separate native endpoint. No path norm bound,
Perron tail limit, Volterra estimate, or full inner asymptotic is claimed here.

Verification of the high-rectangle step:

- The two literal contracts first failed only on their intended missing
  theorem names. The existing baseline and refactored local contract passed.
- `nice -n10 lake build Test.ConreyCoprimeMobiusHighRectangleContract
  Test.ConreyCoprimeMobiusRectangleContract
  Test.ConreyCoprimeMobiusResidueContract
  Test.ConreyReciprocalZetaStripContract
  Test.ConreyCoprimeMobiusPerronContract`: exit 0, 8733 jobs.
- Both new endpoints, the shared actual contour helper, and the now-public
  finite Euler analyticity lemma use only the three standard axioms.
  The high endpoint's 21-local-module closure contains no Zeta23; Mathlib is
  the only external root. New module and contract are explicit Lake roots.
- Python regression: 546 passed. Inventory, chain-gap and whitespace checks
  passed. Independent read-only review confirmed the compact/high split,
  common constant, inequality directions, shifted height, discharged helper
  assumptions, raw pole handling and the paper parameter calculation.

This is targeted Lean verification, not a fresh full-repository baseline
or a GitHub CI result. (GV), the outer arithmetic mean, the actual long
mean square/DI chain, and the final strict two-fifths conclusion remain open.
