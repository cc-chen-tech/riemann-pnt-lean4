# Weil Loewner–秩二全局核接口

## CCM 路线的全局结构

令

\[
L(p,p')_{mn}=
\begin{cases}
p'(n),&m=n,\\[4pt]
\dfrac{p(m)-p(n)}{m-n},&m\ne n.
\end{cases}
\]

CCM 路线可以写成

\[
K_c^{\mathrm{CCM}}(m,n)
=L(p_0,p_0')(m,n)
+2c_mc_n-2s_ms_n.
\]

其中

\[
p_0=\alpha+p_{\mathrm{prime}},
\qquad
p_0'=\alpha'+p_{\mathrm{prime}}'.
\]

因此

\[
K_c^{\mathrm{CCM}}
=L(\alpha,\alpha')
+L(p_{\mathrm{prime}},p_{\mathrm{prime}}')
+2cc^{\mathsf T}-2ss^{\mathsf T}.
\]

## 已完成的 Lean 结果

`WeilLoewnerKernel.lean` 已证明：

- Loewner 差商核对称；
- Loewner 核对 value/derivative 数据可加；
- 极点项是显式的秩二核且对称；
- CCM 全局核对称；
- archimedean、prime、pole 三源精确分解；
- CCM cutoff 自动 centered nesting；
- 一个 cutoff 的严格正定性传递到所有较小 cutoff；
- 两个全局核逐项相等即可推出所有有限 cutoff 矩阵相等。

## 素数幂块已经闭合

`WeilPrimeLoewner.lean` 已将每个素数幂抽象成权重 \(w_q\) 和相位
\(a_q=\log q/\log c\)，并严格证明

\[
\sin\!\bigl(2\pi n(1-a_q)\bigr)
=-\sin(2\pi n a_q),
\qquad
\cos\!\bigl(2\pi n(1-a_q)\bigr)
=\cos(2\pi n a_q)
\]

对所有 \(n\in\mathbb Z\) 成立。由此得到：

- 单个素数幂的辅助路线 Guinand--Weil 块等于 CCM Loewner 块；
- 任意有限素数幂和仍然逐项相等；
- 该结论同时覆盖对角导数项与非对角差商项；
- 结论是精确实数恒等式，不依赖 Arb 精度或有限 cutoff。

因此双路线的 prime-power source 已不再是待证明桥。

## Archimedean 矩阵恒等式已降为两个标量恒等式

`WeilArchimedeanLoewner.lean` 定义

\[
a_{\mathrm{aux}}(n)=\frac{S_c(n)}{\pi}
\]

以及辅助路线已经带入最终符号的对角标量 \(d_{\mathrm{aux}}(n)\)，并证明

\[
K_c^{\mathrm{aux,arch}}(m,n)
=L(a_{\mathrm{aux}},d_{\mathrm{aux}})(m,n).
\]

所以不再需要直接证明一个二维矩阵恒等式。只需证明对所有
\(n\in\mathbb Z\)：

\[
\alpha(n)=\frac{S_c(n)}{\pi},
\qquad
\alpha'(n)=d_{\mathrm{aux}}(n).
\]

在实验脚本的记号下，第二条具体为

\[
-2\bigl(\gamma(n)-\beta(n)\bigr)
=-\left(
\kappa+2CC(|n|)+J-\frac{2XC(|n|)}{\log c}
\right).
\]

Lean 定理
`auxiliaryGlobalKernel_eq_ccm_of_archimedean_scalar_identities`
已经证明这两条标量恒等式足以推出完整全局核恒等式；对应的 cutoff
定理也已经给出。

## 极点块已经完成代数识别

`WeilPoleKernelIdentity.lean` 定义共同分母

\[
D_L(n)=L^2+16\pi^2n^2
\]

并证明当 \(r^2=L\) 时，CCM 的两个归一化因子

\[
c_n=\frac{4Lr\sinh(L/4)}{D_L(n)},\qquad
s_n=\frac{16\pi rn\sinh(L/4)}{D_L(n)}
\]

满足

\[
2(c_mc_n-s_ms_n)
=\frac{
32L\sinh^2(L/4)(L^2-16\pi^2mn)
}{
D_L(m)D_L(n)
}.
\]

这正是辅助路线的展开极点公式。模块还证明了 \(L>0\) 时取
\(r=\sqrt L\) 的全整数版本。

## 双路线剩余解析恒等式

auxiliary 路线当前采用

\[
K_c^{\mathrm{aux}}(m,n)
=P_c(m,n)-A_c(m,n)-R_c(m,n).
\]

最终需要证明

\[
K_c^{\mathrm{aux}}(m,n)
=K_c^{\mathrm{CCM}}(m,n)
\]

对所有整数 \(m,n\) 成立。

极点项已经完成展开式与秩二式的代数识别，素数幂项也由
`WeilPrimeLoewner.lean` 完成。因此现在完整恒等式被严格归约为上述
两个一维 archimedean 目标：

\[
K_c^{\mathrm{aux,arch}}(m,n)
=L(\alpha,\alpha')(m,n).
\]

其中 \(\alpha\) 是 CCM 的 hypergeometric/Lerch 表达式。现有归约
定理证明：只要两个标量 archimedean 恒等式成立，完整全局核恒等式
和所有 cutoff 矩阵等式就自动成立。

目前双路线区间严格重叠为固定有限范围提供计算认证，但不是上述
全整数 archimedean 特殊函数恒等式的 Lean 证明。方法论文可以准确区分：

- 固定有限范围：双路线 Arb overlap；
- 一般 \(m,n\) 的 prime-power 块：已形式化证明；
- 一般 \(m,n\) 的 pole 块：已形式化证明；
- archimedean 块：已降为两条一维特殊函数恒等式。

## 对有限证书的影响

现有 `c=13,N=200` source artifact 已直接计算

\[
m,n=-200,\ldots,200.
\]

一旦将其 CCM route 识别为此处的 `ccmIntegerKernel` cutoff，centered
nesting 不再依赖额外数值实验，201 个较小截面的传递成为纯代数结果。

## 尚未完成

- CCM 的 hypergeometric/Lerch `alpha` 数据到 Lean 的具体定义；
- auxiliary 与 CCM 的全整数 archimedean 特殊函数恒等式；
- \(N>200\) 的正性；
- 无限维 Weil 判据和 RH。
