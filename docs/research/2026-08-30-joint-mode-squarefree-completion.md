# 联合模式重组与保留平方自由支撑的完成式

这次尝试把外变量和 Poisson 频率一起求和，争取前次审计仍缺的幂次收益。
得到一个真实的零模式消去和一个可直接使用的带权完成公式；但完整除数
恒等式并没有消掉真实的全部非零模式。更上游的平方自由支撑必须一致处理，
不能既把 quotient 当作无权整数，又无条件断言它的外因子平方自由。

本笔记承接[物理归一化审计](2026-08-30-coprime-comb-physical-normalization.md)。
这里只证明下述恒等式、尾界及其适用边界，不证明 MMKLS、长 mollifier
渐近式或任何新的零点界。没有修改 Lean。

## 1. 先完整消去真正可以消去的零模式

取一个完整的光滑分离张量
\(F_{A,m}(s)u(h/H)v(\delta/L)\)，其中 \(u,v\in C_c^\infty((1,2))\)。
假设对固定 \(A,s\)，函数 \(m\mapsto F_{A,m}(s)\) 光滑紧支撑；
以下只讨论这个张量，不预设任意算术权都能如此分离。
固定 \(s=de\) 后，以 \(m=dc-Akl\) 参数化整除条件，再在 \(c\) 上 Poisson。
其 \(j=0\) 模式没有 \(kl\) 相位，\(m\)-积分也不再依赖 \(k,l\)。
具体地，若 \(G(m)=F_{A,m}(s)\)，则
\(\sum_cG(dc-Akl)=d^{-1}\sum_j\widehat G(j/d)e(-jAkl/d)\)，
零模式正是 \(d^{-1}\int G\)，与 \(k,l\) 无关。
因此该模式中完整的双频率因子是

\[
 \left(\sum_{k\in\mathbb Z}\widehat u(kH/s)\right)
 \left(\sum_{l\in\mathbb Z}\widehat v(lL/s)\right).
 \tag{1}
\]

精确 inverse Poisson 给出

\[
 \sum_k\widehat u(kH/s)=\frac sH\sum_{a\in\mathbb Z}u(as/H).
 \tag{2}
\]

若 \(s\ge2H\)，右侧每个样本都在支集外，故等于零；\(s\ge2L\) 的另一因子
同理。因此任一条件成立即足以杀掉 (1)。在平衡硬尺度
\(s\asymp T^3,H=L=T^{5/2}\) 上，足够大 \(T\) 自动满足这点。

这不是 Möbius PNT 的小量界，而是完整张量上的精确零。负号支集也可同样
处理。但必须先重组所有双频率；有限截断的 \(k,l\) 和还有对应的 Fourier
尾，不能直接写成零。若仍有依赖 \(h,\delta\) 的非光滑算术限制，也须先
完成其合法重组，不能仅以光滑张量的符号代替它。

## 2. 为什么 \(n=jA\) 并未消掉全部非零模式

令 \(Q\ge1\) 为整数。对有限支撑序列 \(F(n)\)，确有

\[
 \sum_{\substack{A\ge1\\(A,Q)=1}}\alpha(A)\sum_{j\ge1}F(jA)
 =\sum_{n\ge1}F(n)
     \sum_{\substack{A\mid n\\(A,Q)=1}}\alpha(A).
 \tag{3}
\]

但是，除数系数由真实 \(\alpha\) 决定。记
\(n^{(Q)}=n/\prod_{p\mid Q}p^{v_p(n)}\)，则

\[
 \sum_{\substack{A\mid n\\(A,Q)=1}}\mu(A)
 =\mathbf1_{n^{(Q)}=1}, \tag{4}
\]

而不是一般的 \(\mathbf1_{n=1}\)。\(Q\)-smooth 频率仍然存在。
对完整双 Möbius 系数 \(\alpha=\mu*\mu\)，则有

\[
 \sum_{\substack{A\mid n\\(A,Q)=1}}(\mu*\mu)(A)
 =\mu(n^{(Q)}). \tag{5}
\]

这由局部因子 \((1-x)^2/(1-x)=1-x\) 立即得到；\(Q\) 内的素数只保留
\(A=1\) 的局部项。若错误地把 \(A\) 限制为平方自由，局部因子改为
\((1-2x)/(1-x)\)，从而 (5) 的右侧变成
\(\mu(\operatorname{rad}(n^{(Q)}))\)。例如 \(Q=1,n=4\)，正确值为零，
而丢掉 \(A=4\) 的贡献后为 \(-1\)。

(5) 只是完整卷积的基准，并不宣称当前截断 Type 系数恰为 \(\mu*\mu\)。
对实际依赖 \(A,j\) 的权重，(3) 的右侧必须写成
\(\sum_{A\mid n,(A,Q)=1}\alpha(A)F_A(n/A)\)；原始 Type 端点和 taper
没有消失。本次检验没有得到额外的 \(S^{-1}\) 因子。

## 3. 原始 Type 恒等式中的两种合法支撑

旧稿 commit `7cc472d4` 的 (4.833) 对每个 \(r>U\) 给出

\[
 \mu(r)=-\sum_{\substack{abv=r\\a\le U,\ av>U}}\mu(a)\mu(b).
 \tag{6}
\]

证明可从 \(c_U=\mu_{\le U}*1\) 及 \(c_U*\mu=\mu_{\le U}\) 得到。
完整 \(a\le U\) 三重和在 \(r>U\) 时为零；其 \(av\le U\) 部分，令
\(n=av\)，恰为 \(\sum_{n\mid r,n\le U}\mu(r/n)\sum_{a\mid n}\mu(a)=\mu(r)\)。
相减便得到 (6)。
本文用 \(v\) 表示 quotient，避免和前文 cofactor \(e\) 混淆。

若保留 (6) 的全部整数项，\(v\) 确实无权，但外因子 \(A=ab\) 未必平方自由。
例如 \(U=2,r=8\)，非零项为

| \((a,b,v)\) | \(A=ab\) | 内层权 \(\mu(a)\mu(b)\) |
|---|---:|---:|
| \((1,1,8)\) | 1 | 1 |
| \((1,2,4)\) | 2 | -1 |
| \((2,1,4)\) | 2 | -1 |
| \((2,2,2)\) | 4 | 1 |

完整内层和为零。删掉 \(A=4\) 后，计入 (6) 的外层负号得到一，而
\(\mu(8)=0\)。这反驳的是两种支撑的混用，不是 (6)。

也可以在每个分解项保留原有的 \(\mu^2(r)\)，因为
\(\mu^2(r)\mu(r)=\mu(r)\)。在 \(\mu(a)\mu(b)\ne0\) 时，额外支持恰为

\[
 \mu^2(abv)=\mathbf1_{(a,b)=1}\,
            \mu^2(v)\mathbf1_{(v,ab)=1}. \tag{7}
\]

这时 \(A\) 平方自由，但 \(v\) 不再无权。旧稿 §4.14 的 (4.119) 曾明确
保留此条件；§4.109g 的无权 quotient Poisson (4.845ao) 与后面的
“\(A\) 平方自由，所以 \(c_A(m)\ne0\)”不能在没有修复时同时使用。

例如 \(A=4,m=1,s=3\)，有

\[
 c_4(1)=0,\quad S(1,-1;3)=2,\quad S(1,-4;12)=0. \tag{8}
\]

CRT 的乘法等式仍然正确，但不能除以 \(c_4(1)\) 恢复左边。
保留所有 \(A\) 时，可以改用不作该除法的跨 cusp 表示：
[Kıral–Young，Proposition 2.6](https://arxiv.org/pdf/1710.00914)
要求的是 \(N=rs,(r,s)=1\)，并没有要求两个因子平方自由。
这提供合法的表示方式，不自动提供所需的谱估计。

## 4. 保留平方自由 quotient 的完整 Poisson 公式

令 \(A,s\) 为正整数，\(s\ge2,(A,s)=1\)，\(h\in\mathbb Z\)，\(E\ge1\)，
\(U_0\in C_c^\infty((1,2))\)。定义

\[
 \mathcal Q_A(E;h,s)=
 \sum_{v\ge1}\mu^2(v)\mathbf1_{(v,As)=1}
 U_0(v/E)e\left(-\frac{h\overline{Av}}s\right).
 \tag{9}
\]

使用 \(\widehat U_0(\xi)=\int U_0(x)e(-x\xi)dx\)。完整公式为
（本文 \(e(x)=\exp(2\pi i x)\)，且
\(S(a,b;s)=\sum_{x\bmod s,(x,s)=1}e((ax+b\bar x)/s)\)）：

\[
 \boxed{\begin{aligned}
 \mathcal Q_A(E;h,s)
 =\frac Es\sum_{\substack{t\le\sqrt{2E}\\(t,As)=1}}
 \frac{\mu(t)}{t^2}
 \sum_{b\mid A}\frac{\mu(b)}b
 \sum_{m\in\mathbb Z}
 \widehat U_0\left(\frac{mE}{t^2bs}\right)
 S\left(\overline{At^2b}\,m,-h;s\right).
 \end{aligned}} \tag{10}
\]

证明完全保留原系数。先插入
\(\mu^2(v)=\sum_{t^2\mid v}\mu(t)\)，令 \(v=t^2w\)。原互素限制强制
\((t,As)=1\)。再用
\(\mathbf1_{(w,A)=1}=\sum_{b\mid A,b\mid w}\mu(b)\)，令 \(w=bn\)。
余下条件为 \((n,s)=1\)，其无权 residue-class Poisson 是

\[
 \sum_{(n,s)=1}U_0(t^2bn/E)
 e\left(-\frac{h\overline{At^2bn}}s\right)
 =\frac E{t^2bs}\sum_m
 \widehat U_0\left(\frac{mE}{t^2bs}\right)
 S\left(\overline{At^2b}m,-h;s\right).
 \tag{11}
\]

有限 \(t,b\) 求和给出 (10)。每个 \(m\)-级数绝对收敛，但不是有限恒等式。
所有逆元都存在：\((A,s)=(t,s)=1\)，且 \(b\mid A\)。公式本身甚至不要求
\(A\) 平方自由；在 (7) 的应用中，外面另有相应支撑。

## 5. 平方因子尾可以先在原变量中估计

令 \(J\ge1\) 为整数，\(\mathcal Q_A^{(\le J)}\) 表示只保留平方除数
\(t\le J\) 的完整贡献。在展开 \(b\mid A\) 之前保留互素示性函数，则

\[
 \begin{aligned}
 |\mathcal Q_A-\mathcal Q_A^{(\le J)}|
 &\le\|U_0\|_\infty\sum_{t>J}
       \#\{w\ge1:E<t^2w<2E\}\\
 &\le2E\|U_0\|_\infty\sum_{t>J}t^{-2}
 \le\boxed{\frac{2E}{J}\|U_0\|_\infty}.
 \end{aligned} \tag{12}
\]

第二行用 \(\#\{w:t^2w<2E\}\le2E/t^2\)，故没有额外的整数端点项。
该界对 \(A,s,h\) 一致，也没有 \(\tau(A)\) 因子。若 \(J\ge\sqrt{2E}\)，
尾项精确为零。对幂次增长的 \(E\)，取 \(J\asymp E^\eta\) 给原变量中
相对于平凡 \(E\) 尺度的幂次节省；但外部聚合仍需单独核算。

小 \(t\) 的完成式也不是免费的密度替换。其 Fourier 频率尺度为

\[
 |m|\lesssim\frac{t^2bs}{E}(\log T)^C,\qquad
 \frac E{t^2bs}\cdot\frac{t^2bs}E=1. \tag{13}
\]

Jacobian 的 \((t^2b)^{-1}\) 伴随模式数的同等扩张；不能只保留前者。
而且即便 \(A\) 平方自由，\(At^2b\) 通常也不是平方自由，不能再次对它
无条件使用非零 Ramanujan 除法。

## 6. 本次探索改变了什么

获得了两项可直接复用的操作：完整张量上的 \(j=0\) 精确消去，以及保留
平方自由支撑的 (10)–(12)。联合非零模式的除数求和则必须使用真实系数与
端点，不能用 \(\mu*1=\varepsilon\) 宣称全部消失。

因此后续幂次估计应选择一个一致的表达式：保留非平方自由 \(A\) 并处理
完整 Type 权，或保留 (7) 并估计含 \(t,b,m\) 的共同核。原有 \(HL\) 与
\(HL/S\) 的差异仍须保留；上述恒等式没有补上该缺口，也没有验证高高度
\(14/17\) 或 \(2/3\)。

有限核算由 `scripts/check_joint_outer_mode_reassembly.py` 提供：它检查
Type 支撑、频率重组、平方自由完成的离散版本、原变量尾和零分母见证。
检查不替代连续 Poisson、谱估计或最终零点证明。

### English scope summary

Joint mode summation removes the full smooth-tensor zero mode, but the true
divisor coefficients and coprimality prevent a blanket annihilation of all
nonzero modes. We retain either all outer factors or the squarefree quotient
weight consistently, derive its exact weighted Poisson completion, and prove
a uniform original-variable square-divisor tail bound. No missing global
power saving or zero-free theorem is claimed.
