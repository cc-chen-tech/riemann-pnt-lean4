# 共同频率核：有理点的无限阶消去与不能略过的过渡区

这次继续攻非零模式，得到的结果不只限于零频率：光滑共同核在一族小分母
有理相位上精确为零，而且所有阶导数都为零。足够深的有理邻域可以在
完整平方自由 quotient 模型里消去，包括所有平方因子和所有余因子。
但到达自然振荡尺度后，同一核可以恢复到平凡大小；算术抵消仍不可省略。

本文接续[平方自由完成式](2026-08-30-joint-mode-squarefree-completion.md)，
保留[物理归一化审计](2026-08-30-coprime-comb-physical-normalization.md)中的
外因子。证明对象是下面明确声明的光滑核类；没有默认原始 Type 硬端点、
额外算术限制和所有物理核已经满足这些条件。不证明 MMKLS、长 mollifier
渐近式、高高度 `14/17` 或 `2/3`，不修改 Lean。

## 1. 不必拆成两个单变量的共同核

记 \(e(x)=\exp(2\pi i x)\)，取 \(P,Q\ge1\) 及
\(\Phi\in C_c^\infty((1,2)^2)\)。这里 \(P,Q\) 是两个频率尺度，
不是互素条件中的模数。定义

\[
 \widehat\Phi(\xi,\eta)=\iint\Phi(x,y)e(-x\xi-y\eta)\,dxdy,
 \qquad
 \mathcal K_{P,Q;\Phi}(\theta)
 =\sum_{k,l\in\mathbb Z}\widehat\Phi(k/P,l/Q)e(-\theta kl).
 \tag{1}
\]

所有求和绝对收敛；任意固定阶数的 \(\theta\) 导数也可逐项求和。
\(\Phi\) 可以是真正的双变量函数，不要求可分离。

**有理点公式。** 若 \((a,q)=1,q\ge1\)，则

\[
 \boxed{\mathcal K_{P,Q;\Phi}(a/q)
 =\frac{PQ}{q}\sum_{h,v\in\mathbb Z}
       e(\bar a hv/q)\Phi(Ph/q,Qv/q).} \tag{2}
\]

\(q=1\) 时右侧相位按一理解。证明是先按 \((k,l)\bmod q\) 分组，再作
二维 Poisson；有限残数和为

\[
 \sum_{r,t\bmod q}e((-art-rh-tv)/q)
 =q\,e(\bar a hv/q). \tag{3}
\]

其中模数平方分母来自两个 Poisson，而残数和恢复一个 \(q\)，所以
外因子是 \(PQ/q\)，不是 \(PQ/q^2\)。

## 2. 有理点上的零不只是一阶消去

如果

\[
 \boxed{q\le\tfrac12\max(P,Q),} \tag{4}
\]

则 (2) 中至少一个坐标的格距不小于二，没有任何采样点进入 \((1,2)^2\)。
因此 \(\mathcal K(a/q)=0\)。注意条件是 **max**：只须一个坐标避开支集。

乘上 \((kl)^r\) 对应于对 \(\Phi\) 作 \(r\) 次、\(r\) 次混合偏导；
这些导数的支集仍在原矩形内。因此对每个整数 \(r\ge0\)，

\[
 \boxed{\mathcal K^{(r)}_{P,Q;\Phi}(a/q)=0.} \tag{5}
\]

这依赖完整的无限 Schwartz 求和，不能用有限频率截断的三角多项式代替。
有限截断具有截断尾；它通常不具有 (5) 的无限阶消去。

Schwartz 估计还给出，对每个固定 \(r\)，

\[
 \sup_\theta|\mathcal K^{(r)}(\theta)|
 \le (2\pi)^r\sum_{k,l}|kl|^r|\widehat\Phi(k/P,l/Q)|
 \ll_{r,\Phi}(PQ)^{r+1}. \tag{6}
\]

结合 Taylor 余项，对任何满足 (4) 的约分有理数有

\[
 \boxed{|\mathcal K_{P,Q;\Phi}(a/q+\eta)|
 \ll_{r,\Phi}PQ\,(PQ|\eta|)^r.} \tag{7}
\]

负号支集，例如 \((1,2)\times(-2,-1)\)，同样满足这些结论。

若 \(\Phi_\lambda\) 的相关半范数满足
\((1+|\lambda|)^{-M}(\log T)^{C_{M,r}}\) 界，则 (7) 的右侧也带该因子。
这里必须**在每个给定 \(\lambda\) 冻结 \(\Phi_\lambda\)，再对相位变量
\(\theta\) 使用 Taylor**；并没有把依赖 \(\lambda\) 的核误当成常数求导。

## 3. 与修正后的平方自由 quotient 共同完成

令 \(S\ge1\)、\(0<H,L\le S\)，并取一个有限的外变量集合 \(\mathcal A\)。
对每个 \(A\)，平方除数 \(t\) 取原问题给定的有限范围，\((t,A)=1\)，
而 \(b\mid A\)。写

\[
 C=At^2b.
\]

设 \(\Psi_{A,t,b,s}(y,z,w)\) 在 \(y\) 上为 Schwartz 函数，在 \((z,w)\)
上光滑且支集位于同一固定紧集 \(K\Subset(1,2)^2\)，在 \(s\) 上只保留
\(S<s<2S\)。所有所需加权 \(y\) 范数和混合导数范数对外参数一致至多
损失固定对数幂。这是本节的显式假设，尤其包括 \(t,b\) 的一致性。

采用 \(S(a,b;s)=\sum_{x\bmod s}^{*}e((ax+b\bar x)/s)\)。考虑

\[
 \begin{aligned}
 \mathcal M_\square
 ={}&\sum_{A\in\mathcal A}\alpha(A)
 \sum_t\mu(t)\sum_{b\mid A}\frac{\mu(b)}C
 \sum_{\substack{S<s<2S\\(s,C)=1}}\frac{\mu(s)}s\\
 &\quad\cdot\sum_{m,h,v\in\mathbb Z}
 \Psi_{A,t,b,s}(m/C,h/H,v/L)
 S(\bar C m,-hv;s).
 \end{aligned} \tag{8}
\]

这个 \(1/C=1/(At^2b)\) 正是保留平方自由 quotient 的 Poisson 权：
前次公式中的 \(E/(t^2bs)\)，连同 \(E=R/A\) 及除以 \(R\) 的归一化。
它不是临时加上的额外节省。

记

\[
 \Phi_{A,t,b,s;\lambda}(z,w)
 =\int_{\mathbb R}\Psi_{A,t,b,s}(y,z,w)e(-\lambda y)\,dy,
 \quad P=de/H,\quad Q=de/L,\quad \lambda=jC/d.
\]

双 Poisson、\(s=de\) 的 Ramanujan 展开以及 \(m=dc-Ckl\) 上的
\(c\)-Poisson 给出精确式

\[
 \boxed{\begin{aligned}
 \mathcal M_\square
 ={}&HL\sum_A\alpha(A)\sum_t\mu(t)\sum_{b\mid A}\mu(b)\\
 &\cdot\sum_{\substack{S<de<2S\\(d,e)=1\\(de,C)=1}}
 \frac{\mu(d)\mu^2(e)}{d^2e^2}
 \sum_{j\in\mathbb Z}
 \mathcal K_{P,Q;\Phi_{A,t,b,de;\lambda}}(\lambda).
 \end{aligned}} \tag{9}
\]

归一化链是
\(C^{-1}\times HL\mu(d)/(de^2)\times C/d\)：
\(c\)-Poisson 的 Jacobian 消去外面的 \(C^{-1}\)，最终是 (9)，没有
额外 \(S^{-1}\)。原来的 \(A\) 不要求平方自由；平方自由 Type 支撑若有
额外限制，只须保留在外系数与求和集合中。

对每个有限外变量组先作完整频率求和。以下不会在消去零模式前擅自把
有限 \(t\) 求和换成一个条件收敛的无限和。

## 4. 深有理邻域：所有平方因子、所有余因子均可保留

固定 \(\delta>0\)。在 (9) 中选取满足

\[
 \lambda\in\mathfrak B_\delta(P,Q;T):=
 \bigcup_{\substack{(a,q)=1\\1\le q\le\max(P,Q)/2}}
 \left\{\lambda:\left|\lambda-\frac aq\right|
              \le\frac{T^{-\delta}}{PQ}\right\} \tag{10}
\]

的模式，记其完整贡献为 \(\mathcal M_{\square,\mathrm{deep}}\)。这只是
精确模式划分，不把邻域的补集省略。定义实际外系数的质量

\[
 \mathcal B_\alpha=
 \sum_{A\in\mathcal A}\frac{|\alpha(A)|}A\sigma_{-1}(A),
 \qquad \sigma_{-1}(A)=\sum_{b\mid A}b^{-1}.
 \tag{11}
\]

**命题。** 对每个固定整数 \(r\ge1\)，在本节显式核条件下，

\[
 \boxed{|\mathcal M_{\square,\mathrm{deep}}|
 \ll_r S^2\mathcal B_\alpha\,
 T^{-r\delta}(\log T)^{C_r}.} \tag{12}
\]

该界不依赖平方除数截断点，也不要求 \(e\) 很小，更不需要 Möbius 消去。

证明的关键是先删除真正为零的 \(j=0\)。若 (10) 非空，则
\(\max(P,Q)\ge2\)，\(j=0\) 由 (5) 精确消去；否则该模式不在深邻域中。
所以只剩非零 \(j\)。固定 \(M>1\)，有

\[
 \sum_{j\ne0}(1+|j|C/d)^{-M}
 \le\frac{2d}{C(M-1)}, \tag{13}
\]

这是单调积分比较，对所有 \(C/d>0\) 成立，**没有 \(+1\)**。
由 (7)，每个选中模式的界为
\(PQ T^{-r\delta}(1+|\lambda|)^{-M}(\log T)^{C_r}\)。而

\[
 \frac{HL}{d^2e^2}PQ=1. \tag{14}
\]

先用 (13)，再在有限原范围内取绝对值并向上延长正项，得到

\[
 \sum_t\sum_{b\mid A}\frac{d}{At^2b}
 \le\frac dA\zeta(2)\sigma_{-1}(A). \tag{15}
\]

最后所有余因子的代价也可直接支付：

\[
 \sum_{e\ge1}\sum_{S/e<d<2S/e}d
 \le6S^2\sum_{e\ge1}e^{-2}=6\zeta(2)S^2. \tag{16}
\]

内和非空时 \(e<2S\)，因而 \(D=S/e>1/2\)。用
\(\#\{d:D<d<2D\}\le D+1\le3D\) 和 \(d<2D\) 即得常数六，
包括 \(D\) 接近整数间距的端点。这证明 (12)。

例如 \(\mathcal A\subset[1,S]\)、\(|\alpha(A)|\le\tau(A)\) 时，
\(\sigma_{-1}(A)\le1+\log S\) 及
\(\sum_{A\le S}\tau(A)/A\le(1+\log S)^2\) 给
\(\mathcal B_\alpha\le(1+\log S)^3\)。有限 Type 双 Möbius 系数的绝对值
确实至多是相应的除数数目；不能把 (12) 用于没有质量约束的任意系数。

因此当 \(S\le T^3\)、外系数质量至多为对数幂时，选足够大的固定 \(r\)
可使深邻域贡献为任意指定的负幂 \(T^{-B}\)。这个结论覆盖声明模型中的
全部 \(t,b,e\)，但不把尚未核验的真实硬端点等自动纳入光滑核类。

## 5. 自然宽度不能沿用上述幂次消去

以下给出核层面的明确边界，而不是完整算术和的反例。
固定 \(c>0\)，令 \(P,Q\to\infty\)。二维 Riemann 求和（或对 Schwartz
函数再作 Poisson）给出

\[
 \begin{aligned}
 \frac1{PQ}\mathcal K_{P,Q;\Phi}\!\left(\frac c{PQ}\right)
 &\longrightarrow
 I_c:=\iint\widehat\Phi(\xi,\eta)e(-c\xi\eta)\,d\xi d\eta\\
 &=\frac1c\iint\Phi(x,y)e(xy/c)\,dxdy.
 \end{aligned} \tag{17}
\]

最后一个等式可以用一次 Fourier 反演后换元严格得到，不需要把未正则化
的分布积分当作绝对积分。具体地，先在 \(\eta\) 上反演，再令
\(y=-c\xi\)，余下 \(x,y\) 积分给右侧。固定 \(c\) 时，Riemann 误差为
\(O_{N,c,\Phi}(P^{-N}+Q^{-N})\)，对每个固定 \(N\) 成立。

取 \(c=16\)，以及非负非零的 \(\Phi\in C_c^\infty((1,2)^2)\)。由于
\(0<2\pi xy/16<\pi/2\)，有 \(\Re I_{16}>0\)。故

\[
 \boxed{\left|\mathcal K_{P,Q;\Phi}(16/(PQ))\right|\asymp_\Phi PQ.}
 \tag{18}
\]

深邻域 \(|\eta|\le T^{-\delta}/(PQ)\) 与自然尺度
\(|\eta|\asymp1/(PQ)\) 之间不能抹掉这一个 \(T^{-\delta}\)。
(5) 的无限阶零不意味着整个自然宽度邻域内都有幂次节省。

这确实接触原问题的平衡尺度，而非不可达的参数：取任意趋于无穷的素数
\(d\)，令 \(T=d^{1/3}\)、\(S=3d/4\)、\(e=t=b=j=1\)、
\(H=L=d^{5/6}\)、\(A=\lceil16d^{2/3}\rceil\)。则

\[
 P=Q=T^{1/2},\quad (A,d)=1,\quad\mu(d)=-1,\quad
 \lambda PQ=\frac A{d^{2/3}}\longrightarrow16. \tag{19}
\]

足够大时 \(1\le A<d\)，故互素性成立。取
\(\Psi(y,z,w)=g(y)\Phi(z,w)\)，其中 \(g\) 光滑紧支撑且积分为一，则
\(\Phi_\lambda=\widehat g(\lambda)\Phi\)、\(\widehat g(\lambda)\to1\)，
仍有 (18) 的大小。这里只说明合法几何范围、互素性和 \(\mu(d)\ne0\)
不能迫使逐模式核很小；没有声称实际 \(\alpha(A)\) 或完整外和具有正下界。

## 6. 对真实证明下一步的约束

本次已经消去的是 (10) 中的深有理邻域，并且在声明光滑模型内不遗漏
平方因子、频率密度或大余因子。这比只处理 \(j=0\) 更强。

但自然尺度过渡区与其余非零模式仍须保留。特别是
\(j=1,A\asymp T^2,d\asymp T^3\) 的共同核不能仅凭光滑性获得统一幂次
小量；下一步必须利用真实 Type 系数、Möbius 符号或跨模式抵消。
把深邻域的界套到整个大弧，或把两侧独立取绝对值后再重复计算收益，
都不是 (12) 的推论。

`scripts/check_joint_kernel_rational_flatness.py` 检查有限残数和、非分离
二维离散完成、支集空采样、模式密度及完整正项聚合的归一化。
它不以有限三角多项式验证无限阶消去，也不代替 (17) 的连续极限证明。

### English scope summary

The coupled smooth kernel is flat to every order at reduced rational phases
whose denominator is at most half the larger frequency scale. Deep rational
neighborhoods are negligible in the stated squarefree-quotient model, with
all square divisors and all cofactors retained. Removing the exact zero mode
is essential to the summable nonzero-mode density. At the natural transition
width, however, admissible kernels can attain their trivial size. No global
power saving or zero-free theorem is claimed.
