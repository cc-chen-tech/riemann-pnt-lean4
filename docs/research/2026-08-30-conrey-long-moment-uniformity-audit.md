# Conrey 长均方：复移位邻域与可求和的误差预算

这次推进修正了长均方证明的一个具体拼接风险：必须先保证无限
dyadic 求和收敛，再吸收 Gaussian 窗口和对数损失。不能把原文中
可重命名的“小参数”当作始终相同的数。同时，我们实际只需在
`a=b=-6/5` 附近求导，可以避开 `a+b=0`。

**证明边界没有改变为“长均方已证”。** 下文给出独立的误差重组推导；
Lean 验证其显式级数和衰减包络，不假设或证明 DI 谱估计，也没有把
这个包络偷换成实际 ζ 移位积分的误差。算术主项、实际积分的解析变换、
DI/Weil 输入及去平滑仍需各自证明。

Primary source: [Conrey 1989](https://aimath.org/~kaur/publications/24.pdf),
printed pp. 11–13 and 20–21. Equations were checked against rendered pages,
not just OCR. The calculations below keep all small parameters separate.

## 1. The fixed negative-shift bidisc suffices

Subsequent arithmetic audit: the radii in Sections 1–2 below are valid
for the abstract Cauchy reduction, but direct use of Conrey 1983 Lemma 10
requires a smaller neighborhood. The [arithmetic main-term proof](2026-08-30-conrey-arithmetic-main-term-proof.md)
uses outer radius `21/40`, inner Cauchy radius `1/2`, and multiplier
`5776/625`, since `theta(R+21/40)<1` whereas `theta(R+3/5)>1`.
The dyadic error budget in Sections 3–6 is unchanged.

Write `L=log T`, `R=6/5`, `rho=3/5`, and

\[
 D_- = \{(a,b): |a+R|\le\rho,\ |b+R|\le\rho\}.
\]

On this closed bidisc, `Re(a+b)<=-6/5`, hence

\[
 |a+b|\ge6/5,\qquad |e^{-a-b}|\le e^{18/5}.
\]

Use an open neighborhood, for example the bidisc of radius `9/10<R`,
for analyticity. The finite arithmetic sum is entire in the shifts. For
the smoothed ζ integral, analyticity still requires locally uniform
integrable domination; it is not supplied by a formal `deriv` expression.

Remove the source's scaled/unscaled notational ambiguity by defining

\[
 S_T(a,b)=L\Sigma_T(a/L,b/L),\qquad
 A(a,b)=\frac1\theta\int_0^1
 (P_1'+a\theta P_1)(P_2'+b\theta P_2)\,dx.
\]

The required arithmetic statement is **additive and uniform**:
`sup |S_T-A| <= u_T -> 0` on both `D_-` and its sign-reflected bidisc
`D_+`. A relative asymptotic is unsuitable when `A` vanishes. The two
signs are needed because the main-term combination is

\[
 C_T(a,b)=\frac{S_T(b,a)-e^{-a-b}S_T(-a,-b)}{a+b}.
\]

For `P_1(0)=P_2(0)=0`, direct expansion and the fundamental theorem of
calculus give

\[
 A(b,a)-A(-a,-b)
 =(a+b)\int_0^1(P_1'P_2+P_1P_2')\,dx
 =(a+b)P_1(1)P_2(1).
\]

Consequently the limiting main term is

\[
 G(a,b)=P_1(1)P_2(1)
       +\left(\int_0^1e^{-(a+b)v}\,dv\right)A(-a,-b),
\]

and throughout `D_-`,

\[
 |C_T-G|\le\frac56(1+e^{18/5})u_T.
\]

This proves neither the arithmetic estimate nor its uniformity. It says
exactly which estimate is sufficient, with no division by a small
`a+b` at our evaluation point. A global removable-singularity theorem
is unnecessary for the explicit two-fifths parameters.

## 2. Differentiating an error needs a complex neighborhood

For a holomorphic error `E_T(a,b)` with `sup_(D_-) |E_T| <= e_T`, the
two Cauchy circles of radius `rho=3/5` give, at `a=b=-R`,

\[
 |\partial_a^i\partial_b^j E_T|
 \le e_T\rho^{-i-j}\quad (i,j\in\{0,1\}).
\]

Here `Q(z)=1-kz`, `k=51/50`, so the relevant operator is
`(1+k partial_a)(1+k partial_b)`, with **plus** signs. Its error is at most

\[
 (1+k/\rho)^2e_T=\frac{729}{100}e_T.
\]

Thus a uniform additive `o(1)` on a fixed complex bidisc suffices; a
pointwise real-shift `o(1)` does not. For real `P_1=P_2=P`, applying this
operator to `G` produces the already-certified Conrey double integral.
Passing the operator through the actual smoothed integral remains an
analytic domination step, not a consequence of this main-term algebra.

## 3. Separate the two epsilon losses before summing

Use `delta>0`, `eta>0`, and two independent positive losses `eps_K`,
`eps_M`. Put `Delta=T^(1-delta)`, `y=T^theta`. The estimates to be proved
for the actual kernel and arithmetic sums have the respective forms

\[
 K_c\ll\Delta^{-c-5/2}T^{5/2+\eta+\varepsilon_K},
\]

\[
 \frac{|\mathcal M|}{1+|s|}
 \ll T^{\varepsilon_M}N^{\varepsilon_M-\eta}
 y^{2\eta}T^c
 (T^{-1/2}y^{7/8}+T^{-1}y^{7/4}),
\]

where `c=eta` if `UV>=TN`, and `c=1+eta` otherwise. Multiplication,
using `T>=1` and `c<=1+eta`, bounds each integrated dyadic box by

\[
 N^{\varepsilon_M-\eta}T^{\lambda_0}
 (T^{-1/2+7\theta/8}+T^{-1+7\theta/4}),
\tag{B}
\]

with the complete common loss

\[
 \lambda_0=\frac72\delta+(1+\delta+2\theta)\eta
              +\varepsilon_K+\varepsilon_M.
\tag{L}
\]

In particular, the `delta*eta` term is retained: replacing `c` by `1`
inside `Delta^(-c-5/2)` would drop a positive loss.

The `N=2^j` sum is infinite. Its convergence requires

\[
 0<\varepsilon_M<\eta,\qquad
 \sum_{j\ge0}(2^j)^{\varepsilon_M-\eta}
 =\frac1{1-2^{\varepsilon_M-\eta}}.
\tag{D}
\]

The printed transition after (75) writes `eta=epsilon/2`. If that
`epsilon` is literally the exponent in the preceding infinite
`N^(epsilon-eta)` sum, the terms grow and the sum diverges. We do **not**
use that literal substitution. Allowing independently chosen small
losses fixes this bookkeeping without strengthening the spectral
estimate. This observation does not refute the paper's theorem.

For each `g`, there are `O((1+log T)^2)` choices of `U,V`; the remaining
`sum_(g<=y) 1/g` is `O(1+log T)`. Hence the continuous-contour errors in
(B), once their actual analytic estimates have been proved uniformly,
are bounded by a fixed multiple of

\[
 \mathcal E(T)=D(1+\log T)^3T^{\lambda_0}
 (T^{-1/2+7\theta/8}+T^{-1+7\theta/4}),
\quad D=(1-2^{\varepsilon_M-\eta})^{-1}.
\tag{E}
\]

The contour-shift residues are separate. If the source's uniform
`O(T^-10)` per-box estimate is proved, only `N<=UV/T<=y^2/T` crosses
the pole. There are then `O((1+log T)^4)` weighted choices in total,
so these residues are negligible as well. They are not silently
included in the Lean envelope theorem.

## 4. Explicit admissible parameters and retained power saving

Choose once and for all

\[
 \theta=571/1000,\quad\delta=\eta=1/100000,\quad
 \varepsilon_K=\varepsilon_M=1/200000.
\]

The two base exponents are `-3/8000` and `-3/4000`, and

\[
 \lambda_0=\frac{664201}{10^{10}}.
\]

After also scaling the error by `T^(1/4000)`, the two exponents are

\[
 \lambda_0-3/8000+1/4000=-\frac{585799}{10^{10}}<0,
\qquad
 \lambda_0-3/4000+1/4000=-\frac{4335799}{10^{10}}<0.
\]

Thus `E(T)=o(T^(-1/4000))`. In particular the logarithmic counting
loss is harmless **after** these strict margins and convergence have
been established. Equivalently, with `L=log T`, a cubic polynomial
times each of two strictly decaying exponentials tends to zero.

`HardyTheorem.ConreyLongMomentErrorBudget` verifies the actual infinite
geometric series and this scaled limit for the explicitly defined
envelope. Its contract spells out all rational parameters independently.
It does not infer a bound for an unspecified error from its name.

## 5. Next mathematical inputs, not additional conditional wrappers

1. Prove the uniform additive arithmetic estimate on the two bidiscs,
   starting from the actual finite gcd/Mobius sum.
2. Establish the actual Gaussian/Estermann contour decomposition and
   the kernel estimate with all poles and residues accounted for.
3. Prove the Vaughan/DI/Weil arithmetic bounds uniformly in the retained
   parameters and gcd/dyadic strata; only then apply (B)–(E).
4. Prove differentiation under the actual integral, desmoothing, and
   the already-identified integer-cutoff normalization correction.

The fixed finite `V1B -> VB` transfer already on this branch can consume
these mean values afterward. Neither it nor the present envelope closes
the genuine Conrey simple-zero proportion theorem by itself.

## 6. Verification of this bounded result

- The exact Lean contracts first failed on the three missing theorem
  names, then passed after implementation. The series has a genuine
  `HasSum` proof before its `tsum` is evaluated.
- `lake build Test.ConreyLongMomentErrorBudgetContract
  Test.ConreyV1MeanSquareTransferContract
  Test.ConreySelectedEtaMainCountContract
  Test.ConreyExplicitIntegralBridgeContract`: exit 0, 8869 jobs.
  All three new public endpoints use only `propext`, `Classical.choice`,
  and `Quot.sound`.
- Full Python regression: 546 passed; target inventory and chain-gap
  checks pass. The new production module and exact contract are Lake roots.
- Independent read-only mathematical and implementation reviews found
  no outstanding issue after the uniformity and parameter corrections.
- This is targeted Lean verification, not a fresh full-repository Lean
  baseline or evidence that the outstanding analytic input has been proved.
