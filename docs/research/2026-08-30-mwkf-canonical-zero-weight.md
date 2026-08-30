# Canonical 零模公共权的求值：移动 gamma 极点与单侧控制

白话结论：固定连续延拓后，canonical 零模的公共权可以显式求值；它最终为正，因而零模二次型的负部已经在允许量级内。但正部仍是一个长度可达 \(T^3\) 的 Möbius 多项式均方问题。本文没有证明这个均方上界，更没有证明完整 twisted moment 或 coupled-kernel gate。

本文沿用 [physical adapter](2026-08-30-mwkf-physical-reflection-adapter.md) 的 (PA9)，只求值该特定 canonical 零核，不把它等同于所有 resonant 项。所有结论均保留配对的非零频补集；改变延拓时必须同时按 (PA8) 修改补集。

后续 [SF12–SF18](2026-08-30-mwkf-shifted-frequency-adapter.md) 进一步求值配对的零差整条格点频率带：完整权为 W(t/T)(λ(t)+2γ+O_A(t^{-A}))，其中非零格点频率精确补偿 κχ。λ(t) 不抵消，正部长 Möbius 均方仍未控制。

## 1. 精确公共权与原点的二重极点

固定 \(N\ge2,T\ge2\)、实值 \(W\in C_c^\infty([1,2])\)。令 \(s_t=1/2+it\)，并使用原 AFE 的全部因子

\[
\begin{aligned}
G_t(z)&=e^{z^2}(1-4z^2)(1-z^2/s_t^2)(1-z^2/(1-s_t)^2),\\
g_t(z)&=\pi^{-z}\frac{\Gamma((s_t+z)/2)\Gamma((1-s_t+z)/2)}
 {\Gamma(s_t/2)\Gamma((1-s_t)/2)},\\
V_t(x)&=\frac1{2\pi i}\int_{(2)}G_t(z)g_t(z)x^{-z}\frac{dz}{z},\\
\lambda(t)&=-\log\pi+\operatorname{Re}\psi(1/4+it/2).
\end{aligned}
\tag{ZW1}
\]

固定光滑 \(0\le\chi\le1\)，使 \(\chi(u)=0\) 于 \(u\le1/4\)、\(\chi(u)=1\) 于 \(u\ge1/2\)。设

\[
J_\chi(t)=\int_0^\infty\chi(u)^2V_t(u^2)\frac{du}{u},
\qquad \Omega_\chi(t)=2W(t/T)J_\chi(t).
\tag{ZW2}
\]

对 \(\operatorname{Re}z>0\)，其截断 Mellin 因子为

\[
M_\chi(z)=\int_0^\infty\chi(u)^2u^{-2z}\frac{du}{u}
=\frac{2^{2z}}{2z}+\int_{1/4}^{1/2}\chi(u)^2u^{-2z}\frac{du}{u}.
\tag{ZW3}
\]

右式把它延拓到全平面，唯一极点在 0。记

\[
c_\chi=\log2+\int_{1/4}^{1/2}\chi(u)^2\frac{du}{u},
\quad \kappa_\chi=2c_\chi\in[\log4,\log16].
\tag{ZW4}
\]

在直线 \(\operatorname{Re}z=2\) 上，Gaussian 衰减及 \(\int_{1/4}^\infty u^{-5}du<\infty\) 保证 Fubini 绝对收敛，故

\[
J_\chi(t)=\frac1{2\pi i}\int_{(2)}G_t(z)g_t(z)M_\chi(z)\frac{dz}{z}.
\tag{ZW5}
\]

由 \(G_t(0)=g_t(0)=1,G'_t(0)=0,g'_t(0)=\lambda(t)\)，原点展开为

\[
\frac{G_t(z)g_t(z)M_\chi(z)}z
=\frac1{2z^2}+\frac{c_\chi+\lambda(t)/2}{z}+O_t(1).
\tag{ZW6}
\]

因此原点留数对 \(2J_\chi\) 的贡献是 \(\lambda(t)+\kappa_\chi\)，没有遗漏因子 2，也没有 \(2\gamma\)：后者来自原 AFE 对角的 \(\zeta(1+2z)\)，并不在 (ZW5) 内。

## 2. 移动 gamma 极点：不能在深移线时全部丢掉

取正整数 \(B\)，从直线 2 移到 \(-B\)。除了 0，候选极点是

\[
z=-s_t-2k,\qquad z=-(1-s_t)-2k,\qquad k=0,1,\ldots.
\tag{ZW7}
\]

两条序列的 \(k=0\) 项被 \(G_t\) 消去；\(k\ge1\) 项不能这样消去。令 \(K_B=\{k\ge1:2k+1/2<B\}\)，\(z_k=-s_t-2k\)。利用 gamma 在 \(-k\) 的留数 \((-1)^k/k!\) 及变量缩放的因子 2，定义

\[
r_{k,\chi}(t)=\frac{2(-1)^k}{k!}
\frac{G_t(z_k)\pi^{-z_k}\Gamma(-k-it)}
 {\Gamma(s_t/2)\Gamma((1-s_t)/2)}\frac{M_\chi(z_k)}{z_k}.
\tag{ZW8}
\]

另一条序列给出其复共轭。于是准确的移线式是

\[
\begin{aligned}
2J_\chi(t)&=\lambda(t)+\kappa_\chi+E_\chi(t),\\
E_\chi(t)&=\frac{2}{2\pi i}\int_{(-B)}G_t(z)g_t(z)M_\chi(z)\frac{dz}{z}
 +4\operatorname{Re}\sum_{k\in K_B}r_{k,\chi}(t).
\end{aligned}
\tag{ZW9}
\]

所用 gamma 极点及留数见 [NIST DLMF §5.2(i)](https://dlmf.nist.gov/5.2#i)。固定 \(t,B\) 后，可沿高度 \(Y>t+1\) 的矩形令 \(Y\to\infty\)；\(e^{z^2}\) 使水平边积分趋零。\(-B\) 是整数，不通过任何实部为 \(-1/2-2k\) 的 gamma 极点。

下面给出一致误差而不把数值积分当作证明。由 (ZW3)，\(M_\chi(-B+iv)\ll_{B,\chi}1\)。在 \(|v|\le t/2\) 上，带导数的 Stirling 估计给出

\[
\left|\partial_t^j(G_tg_t)(-B+iv)\right|
\ll_{B,j}t^{-B-j}(1+|v|)^{C_{B,j}}e^{-v^2/2}.
\tag{ZW10}
\]

在 \(|v|>t/2\) 上，gamma 参数实部为固定非整数四分之一格点，故即使 \(v\approx\pm t\) 也不碰极点。分子/分母的指数比是

\[
\exp\!\left[-\frac\pi4
 (|t+v|+|t-v|-2t)\right]\le1.
\tag{ZW11}
\]

余下因子及其任意固定阶 \(t\) 导数至多多项式增长；在此区间用半个 Gaussian 吸收该多项式和 \(t^{B+j}\)，仍得可积的 (ZW10) 型界。故新直线积分的 \(j\) 阶导数为 \(O_{B,j,\chi}(t^{-B-j})\)。这些 Stirling 估计使用 [DLMF §5.11](https://dlmf.nist.gov/5.11)；内区的额外 \(t^{-j}\) 来自带导数的 Stirling 展开（等价地，分子与分母的 polygamma 差）；尾区所需的多项式导数界可在避开极点的固定小圆上由 Cauchy 公式得到。

每个移动留数中的 Gaussian 为
\(e^{(2k+1/2)^2-t^2}\)，其余因子及 \(t\) 导数至多多项式增长。因此有限个留数连同任意固定阶导数都是任意幂次小。给定 \(A>0,j\ge0\)，选择整数 \(B>A\)，得到

\[
E_\chi^{(j)}(t)\ll_{A,j,\chi}t^{-A-j}\quad(t\ge2),
\qquad
\boxed{\Omega_\chi(t)=W(t/T)
       \bigl(\lambda(t)+\kappa_\chi+E_\chi(t)\bigr)}.
\tag{ZW12}
\]

这里仅移 gamma 的 Mellin 线，不涉及 zeta 零点或 \(\zeta'(\rho)\) 的负矩。

一个方便的完全光滑选择是：令 \(\eta(y)=e^{-1/y}\) 于 \(y>0\)、否则为 0，\(\rho(y)=\eta(y)/(\eta(y)+\eta(1-y))\)，再令 \(\chi(u)=\sqrt{\rho(\log_2(4u))}\) 于过渡区，区外接 0、1。端点的平坦性保证平方根仍光滑，而 \(\rho(y)+\rho(1-y)=1\) 给出

\[
\kappa_\chi=3\log2=\log8.
\tag{ZW13}
\]


## 3. 有限二次型与补回的对角

对任意实系数 \(a_d\)，定义有限和

\[
m_N(t)=\sum_{d\le N}\frac{a_d}{d^{1/2+it}},\qquad
S_N=\sum_{d\le N}\frac{a_d^2}{d},\qquad
Z_\chi=a^TG_\chi a,\qquad
D_\chi=S_N\int\Omega_\chi(t)\,dt.
\tag{ZW14}
\]

这里 \(G_\chi\) 准确地是 (PA9)。有限求和与积分交换立即给出

\[
Z_\chi+D_\chi
=\int W(t/T)(\lambda(t)+\kappa_\chi+E_\chi(t))|m_N(t)|^2dt.
\tag{ZW15}
\]

这是补回 **mollifier 的 \(d=e\) 对角**；原 AFE 的 \(me=nd\) 对角没有在此被替换、抵消或重新估计。两个 AFE 方向已在 \(\Omega_\chi\) 的因子 2 内。

在 \(Z_\chi\) 中丢去 \(E_\chi\) 所造成的总误差满足

\[
|\mathrm{Err}_{A,N,T}|
\ll_{A,W,\chi}T^{1-A}
 \left(\sum_{d\le N}\frac{|a_d|}{\sqrt d}\right)^2.
\tag{ZW16}
\]

对 Selberg 系数 \(a_d=\mu(d)(1-\log d/\log N)\)，\(|a_d|\le1\)，括号平方不超过 \(4N\)。故 \(N\le T^3\) 时误差为 \(O(T^{4-A})\)，选择 \(A\ge L+4\) 即得 \(O(T^{-L})\)。这里原求和是有限的，没有 Perron 端点半权；若 \(N\) 为整数，其末项权本来就是 0。\(W\) 的紧支撑排除了 \(t\) 的边界项。

## 4. 正性、负部控制与一个可求出的对角常数

本节增加 **\(W\ge0\)** 的假设。由
\(\lambda(t)=\log(t/(2\pi))+O(t^{-2})\) 和 (ZW12)，存在只依赖固定权的 \(T_0\)，使 \(T\ge T_0\)、\(t\in[T,2T]\) 时

\[
\tfrac12\log T\le \lambda(t)+\kappa_\chi+E_\chi(t)
\le2\log T.
\tag{ZW17}
\]

所以补齐的 Gram 最终为正半定，尽管 \(V_t\) 本身未被假设处处非负。对 Selberg 系数，由 \(S_N\le1+\log N\)，

\[
Z_\chi\ge-D_\chi\ge-C_{W,\chi}T\log T\log(2N).
\tag{ZW18}
\]

这无条件控制了 \(Z_\chi\) 的负部，不控制其正部；有限 \(2\le T<T_0\)、\(N\le T^3\) 的情形可扩大常数吸收最后这个负部下界，但不宣称该范围也有 Gram 正性。

对本题的 Selberg 系数，还可初等求值补回的对角。恒等式
\(\mu^2(n)=\sum_{d^2\mid n}\mu(d)\) 给出
\(\sum_{n\le x}\mu^2(n)=x/\zeta(2)+O(\sqrt x)\)。对
\(f_N(x)=(1-\log x/\log N)^2/x\) 作 Abel 求和，其主积分为 \(\log N/3\)。上端 \(f_N(N)=0\)，下端为 \(O(1)\)，误差积分
\(\int_1^N\sqrt x\,|f_N'(x)|dx\ll1\) 一致有界。因此

\[
S_N=\frac{\log N}{3\zeta(2)}+O(1).
\tag{ZW19}
\]

记 \(\omega_W=\int W(u)du\)。固定 \(\theta>0\)，若 \(N=T^\theta\) 或其整数部分，则

\[
D_\chi=\frac{\theta\omega_W}{3\zeta(2)}T(\log T)^2
       +O_{\theta,W,\chi}(T\log T).
\tag{ZW20}
\]

在 \(\theta=3\) 时，系数是 \(\omega_W/\zeta(2)=6\omega_W/\pi^2\)。它只是 **人为补回的 mollifier 对角** 的常数，既不是完整 \(Z_\chi\) 的主常数，也不是完整 twisted moment 的新次主项。\(\kappa_\chi\) 的选择只影响此展开的低阶项。

## 5. 剩余正部恰好是什么；什么没有被证明

仍设 \(W\ge0\)，并令 \(F_{N,W}(T)=\int W(t/T)|m_N(t)|^2dt\)。由 (ZW15)、(ZW17)，

\[
\tfrac12\log T\,F_{N,W}(T)
\le Z_\chi+D_\chi
\le2\log T\,F_{N,W}(T).
\tag{ZW21}
\]

结合 (ZW18) 和 \(N\le T^3\)，以下三个“对每个 \(\varepsilon>0\)”的统一上界互相等价：

1. \(|Z_\chi|\ll_{\varepsilon,W,\chi}T^{1+\varepsilon}\)；
2. 仅上侧的 \(Z_\chi\le C_{\varepsilon,W,\chi}T^{1+\varepsilon}\)；
3. \(F_{N,W}(T)\ll_{\varepsilon,W}T^{1+\varepsilon}\)。

证明只是 (ZW21)、\(D_\chi\ll T\log T\log(2N)\) 和将 \(\log T\) 吸收进 \(T^\varepsilon\)。**本文没有证明这三个上界中的任何一个。** 更重要的是，它们并非完整余项小的必要条件：物理分解 \(\mathcal R=Z_\chi+a^TJ_\chi^{\rm comp}a\) 仍可能在两个有符号项之间抵消；这里 \(J_\chi^{\rm comp}\) 指 (PA18) 的补集矩阵，不是标量积分 (ZW2)。不能把单独控制 \(Z_\chi\) 强加为原命题的新必要门槛。

对照 [Matomäki–Teräväinen, arXiv:1911.09076, Theorems 1.1 and 1.5](https://arxiv.org/pdf/1911.09076)，全短区间的 Möbius 和（含线性加性扭曲）可获对数消去。在 \(x=T^3,H=T^2\) 处，长度条件满足，但这些结论本身不提供平方根级短区间能量；不能据此填上 (ZW21) 的多项式长度均方缺口。主笔记已有更一般短区间结果的覆盖审计，本节没有因此新增 coupled-kernel 参数覆盖。

## 6. 可复核边界

- (ZW5)、(ZW9) 是带全部移动极点的精确连续恒等式；(ZW12) 是其解析误差证明。
- (ZW14)–(ZW16)、(ZW18)、(ZW21) 是可直接转为有限和/积分命题的结论；它们不依赖未经证明的 Möbius 相关假设。
- 一个 55 位浮点的非认证辅助检查，用对数线性过渡 \(\chi^2\) 比较直线 2 与直线 \(-4\) 加 \(k=1\) 留数，在 \(t=2,5,12\) 的差均小于 \(4\times10^{-53}\)。这只检查留数符号和因子；该诊断过渡不光滑，数值也不是区间证明，均不作为上述定理的依据。
- 此次没有修改 Lean 源码，没有把连续解析结论伪装成已经 Lean 验证的定理。补集、两个 reflection 交叉项和原 AFE 对角仍按 physical adapter 保留。
- 进展是公共权的显式求值、最终正性和负部控制；剩余正部均方、中心化非零频的联合谱估计及 coupled-kernel gate 仍未证明。
