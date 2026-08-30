# 全 B 重组：除数塌缩与真实端点回返

白话结论：把所有 B 分片放回同一个 signed 和后，新增的
primitive h 家族可以整体压缩为一个负号的 h=−1 边界项。
这一步保留真实核、两边 Möbius 权、原 q 单位条件和完整变换尾。
**它是反向 Type 重组，没有新增幂次节省或参数覆盖。**
因此不能在已经使用这次全 B 抵消以后，又把同一个 h 家族当作
独立平均来支付缺失的 T²。下一估计仍须处理压缩后的联合核。

后续 [短区间转移 SR1–SR12](2026-08-30-mwkf-short-row-transfer.md)
在原单位掩码下将经典短区间输入接到 GB7，并恢复完整 q 壳。
它仅在指定内部族给出亚幂次衰减，不减少顶层缺失的固定 T²。

范围沿用 [PQ1–PQ9](2026-08-30-mwkf-physical-q-shell-coverage.md)：
R≥S、α=R/S、X=R/K、P=Kmin Kmax、Z=RP/S、J=Z/K、
F=αJ=ZX/S、C=HL/R，Z 和 K/α 至少为固定正幂。
本节再显式限制实际求和整数 **M>1**；X>1 本身不够排除 M=1。
固定 q 为 T 的多项式，q₀=rad(q)。M=1，尤其 M=q₀=1 的 h=0
项，以及 K/α 端点、零斜率、硬 mollifier 边界和独立 AFE/reflection
物理尾均不由本节控制。M>1 包含 PQ 的三个具体物理例子。

## 1. 全 B 才成立的有限除数命题

对任意正整数 M,q,r，令
\[
 c_{M,q}(r)=\sum_{B\mid r\atop(B,q)=1,\ (r/B,Mq)=1}\mu(B).
\]
精确地
\[
 c_{M,q}(r)=\mu(r)\mathbf1_{r\mid M}\mathbf1_{(r,q)=1}.
                                                               \tag{GB1}
\]
逐素因子证明：q 的素因子不能进入 B 或 r/B；M 中不整除 q
的素因子必须全部进入 B，故只容许指数1并贡献−1；其余素因子
在 B 的指数0、1之间产生 1−1 抵消。此式甚至不要求 M 平方自由。

故对任意整数 V≥1、任意复函数 f，字面有限恒等式为
\[
 \sum_{B\ge1,\ h\ne0\atop B|h|\le V,\ (B,q)=1,\ (h,Mq)=1}
       \mu(B)f(Bh)
 =\sum_{r\mid M,\ r\le V\atop(r,q)=1}
       \mu(r)[f(r)+f(-r)].                                    \tag{GB2}
\]
闭端点 B|h|=V 保留。M=q=1 时，这只是一条去掉 h=0 的恒等式，
不能用来还原含 h=0 的原单位和；下面的解析使用已排除它。
反例：M=6、q=1、r=35，完整系数为0，但单独 B=7 的系数为−1。
所以不能把 GB1 用于一个 B-shell、固定 e 子和或任意 B 相关权。

## 2. 移除 quotient 截断后的全和快速衰减

在 GE4 的实际幅度中写
\[
 \mathfrak a_\chi(t,x)=\mathfrak a_0(t,x)\chi(Sx/B),\quad
 \mathfrak a_0=\frac{w(t)}x
 \widetilde G(tKM/R,x,kH/(Sx),lL/(Sx)).
\]
χ(t)=0 对 t≤1，χ(t)=1 对 t≥2，光滑；x 支撑于 (1,2)。
令 Ψ^χ 是完整 JT4 symbol，Ψ⁰ 则把 χ 换成1。后者**不依赖 B**。
当 B≤S/2 时二者精确相同，但不能据此忽略 B>S/2。

在 PQ7 中先对 bare symbol Ψ⁰ 求全 B≥1 和全 h≠0。用 GB2
并令 V→∞，得到
\[
 \mathcal P^0=C\sum_M\frac{\mu(M)}M\sum_{k,l}
 \sum_{|j|\asymp J}\frac F{|j|}
 \sum_{r\mid M\atop(r,q_0)=1}\mu(r)
 \left[\widehat\Psi^0\!\left(F(r/M+kl/j)\right)
       +\widehat\Psi^0\!\left(F(-r/M+kl/j)\right)\right].
                                                               \tag{GB3}
\]
因 M>1，h=0 本来不在单位和中。对固定有限外层，原 B/h 和的
绝对收敛由 Σ_r τ(r)(1+Fr/M)^{−L₀} 保证；不是条件重排。

critical j 与 kl 同号，kl/j≈S/M≈K/α，r≤M。因此充分大 T 时
两种符号的频率均有绝对值≳FP/J=αP=Z。Ψ⁰ 的统一 Schwartz
界及除数界给任意 A₀>0
\[
 |\mathcal P^0|\ll T^\varepsilon CPF Z^{-A_0}.
                                                               \tag{GB4}
\]
完整 j 的 F/|j| 总质量是 O(F)，这里没有把 j 视为固定个数。
所以 bare 全和不留下一个巨大零模；但实际 χ 端点仍必须放回。

## 3. 精确 symbol 如何读取整数端点

设 z₀=KMkl/S、η=jK/z₀，a=FS/M≈Z，
θ(u)=θ(η,t₀(u)) 为 JT 的原 critical cutoff，Θ=widehat θ。
θ 的 u 支撑在固定紧集且离开0；其参数导数统一受控。
由 JT4/5 本身，而不是驻相 leading term，有
\[
 \begin{split}
 &\widehat\Psi^\chi\left(F(Bh/M+kl/j)\right)\\
 &\quad=|j|K\iint \mathfrak a_0(t,x)\chi(Sx/B)
       e(z_0t/x-jKt)\,
       \Theta\bigl(a(x+Bh/S)\bigr)\,dt\,dx .
 \end{split}                                                   \tag{GB5}
\]
核验：Ψ(u)=|j|K θ(u)e(au/η)∬𝔞χ e(z₀t/x−jKt−aux)；
a/η=Fkl/j，代入 Fourier 频率后两项载波精确抵消。
**外因子 |j|K 保留。** 原 AFE hδ 仍在 𝔞₀ 内，GB5 的 h 只是
新增 Fourier 标签，不能混淆。

可以将 GB5 中的 χ(Sx/B) 换成 χ(−h)。理由不是形式上的
delta 函数，而是 χ 在每个整数处平坦以及 Θ 的 Schwartz 衰减。
完整误差如下：

- B≤S/2 时 χ(Sx/B)=1。对 h≤−2 差精确为0；h=−1 时
  x−B/S≥1/2，h≥1 时 x+Bh/S≥1+Bh/S。积分后对这些 h,B
  求和至多为 O_N(T^ε |j|K S log(2S) Z^{−N})。
- B>S/2 时，χ 的全部正阶导数在整数 −h 处为0。Taylor
  余项给
  |χ(Sx/B)−χ(−h)|≤C_N(S/B)^N|x+Bh/S|^N。
  合并 Θ(a(x+Bh/S)) 的任意阶衰减，再按格距 B/S 求 h 和，
  对所有 B>S/2 的总成本≤O_N(T^ε |j|K S Z^{−N})。
  大 B 或大 |h| 的尾均已包含；没有把无限 B 和当成有限个。

恢复 M,k,l,j 的完整外层，用 |j|K≈Z，得到保守误差
\[
 \mathcal E_{\rm end}
 \ll_N T^\varepsilon CPF S\log(2S)Z^{1-N}.                  \tag{GB6}
\]
所有尺度为固定幂，Z≥T^δ，故 N 可选得足够大以支付任意指定
的物理外权。有限 T 调整常数；Z≈1 不在此结论内。

## 4. 整个 B/h 家族只留下负号的 h=−1

整数上 χ(−h)=1_{h≤−2}。GB3 的 bare 全和包含所有 h≠0；
其中 h≥1 因两项频率同号快速衰减，h=0 由 M>1 排除。因此
实际全部 B 的 critical core 满足
\[
 \boxed{\quad
 \mathcal P_{K,q,\rm crit}
 =-C\sum_M\frac{\mu(M)}M
   \sum_{B\ge1\atop(B,q_0)=1}\mu(B)
   \sum_{k,l}\sum_{|j|\asymp J}\frac F{|j|}
   \widehat\Psi^0_{M,j,k,l}\left(F(kl/j-B/M)\right)
   +\mathcal E_{\rm bare}+\mathcal E_{\rm end}.
 \quad}                                                       \tag{GB7}
\]
这里 E_bare 由 GB4 支付；正 h 的尾可并入 GB6。
h=−1 与 Mq₀ 自动互素，但 **(B,q₀)=1 不得删除**。
M 与 B 仍可共有素因子。负号来自补掉 h=−1，而不是猜测某个
canonical 零模与 diagonal 抵消。

GB5 对 bare symbol 同样成立，故可在 GB7 乘固定光滑
v(B/S)，v=1 于 [1/2,3]、支撑于 [1/4,4]；外部 B 尾与 GB6
同阶。原 χ 全和的 B<2S，bare 延伸的 B≥2S 及再次截断都已
单独支付。j 是 critical 有限集；k,l 为给定紧支撑分片，M、B
亦有限。因此截断后的式子是保留 µ(M)µ(B) 的有限 signed 矩阵。
它不被声称有零行和/零列和或达到目标的全体向量算子范数。

若再按 jB=Mkl 与 jB≠Mkl 分开，两项仍须加回 GB7；这只是
新的 primitive 零/非零 determinant 分解，**不是 canonical
zero Gram 的求值，也不删除两个 reflection mixed 项**。

## 5. 为什么这是反向 Type 重组，而非新的 saving

在还没有展开 µ(d) 的 IC2 中，已经有一个更短的有限证明。
令 M=Ae、s=ed。对所有非零 Möbius 项，e=(M,s) 唯一，
原 (e,Aq)=(d,Aeq)=1 等价于 M,s 平方自由及 (s,q)=1，而且
\[
 \sum_{e\mid(M,s)\atop(e,(M/e)q)=1,\ (s/e,Mq)=1}
    \frac{\mu(M/e)\mu^2(e)\mu(s/e)}s
   =\frac{\mu(M)\mu(s)}s\mathbf1_{(s,q)=1}.                  \tag{GB8}
\]
此处 (s/e,Mq)=(d,Aeq)，不补 (M,q)=1 或 (M,s)=1。
GB8 也适用于非平方自由父项：所有可能非零 allocation 自己
强制父项平方自由。保持 K>2，κ=e=1 纠正不出现，于是原全 e
bulk 精确化为
\[
 -C\sum_{M,s}\frac{\mu(M)\mu(s)}s\mathbf1_{(s,q)=1}
 \sum_{\kappa,k,l}w(\kappa/K)
 \widetilde G(\kappa M/R,s/S,kH/s,lL/s)e(\kappa Mkl/s).
                                                               \tag{GB9}
\]
M≈X、s≈S。GB9 的 s 是原物理模数，**不是**中间 Type 因子
B=eb；全 B/h 重组后 GB7 的 B 才回到这一物理尺度。

所以 GB7 不是凭空得到的第三个独立消去：它在精确 critical
symbol 上撤销 µ(d)=−Σ_{bm=d,m>1}µ(b)，回到 GB9 的同一信息。
在 q=1、R=S≈T³、K≈P≈T 的内部模型，固定 M,k,l,j 时 GB7
的有效 B 窗口宽度为 O(X)，X≈T²；全部 B 支持仍约为 S。
完整绝对值成本仍为 CPX≈T⁵，而 normalized 目标是 S≈T³。
采用固定比例 R=S=N/8 可确保原 mollifier 内部；不需要违反
qR,qS≲N 的例子。K/α 正幂条件不覆盖 K≈1 的剩余端点。

## 6. 对已发表 determinant 输入的准确定位

[Bettin–Chandee, Corollary 1, (1.4)](https://arxiv.org/pdf/1502.00769)
给固定非零 determinant 的主项加误差，容许两组算术系数、
另两组光滑权；它不是总和自动为小量的断言。该文也明确区分
固定 determinant 与对 determinant 平均的情形。

以下是将该固定式用于 GB7 的成本推导，**不声称论文已处理
当前完整核**。在 q=1、顶层 J≈1、X≈T²、S≈T³，固定正 k≈T^u
和一个 j（先写 j=1），非零 determinant 为 B−kMl=Δ。
取 n₁=kM、n₂=B、m₁=1、m₂=l；m₁ 可用只在整数1非零的
固定光滑权表示。M/B/l 联合权可先用其有界归一化导数作
光滑分离；固定 Δ≈X 的 Ψ⁰hat(−Δ/M) 不损失固定 T 幂。
α_{kM}=µ(M)/M、β_B=µ(B) 给范数乘积≤sqrt(S/X)。
Corollary 的乘积比率 R_bc≈1，故它的每个 Δ,k 误差成本为
\[
 T^\varepsilon C\sqrt{S/X}\,(kXS)^{7/20}(kX+S)^{1/4}
       \asymp T^{5+7u/20+\varepsilon}.
\]
对 k 的 T^u 个整数及宽度 X 的 Δ 作绝对值求和得到
T^{7+27u/20+ε}，比直接 T⁵ 更差。Schwartz 的远 Δ 尾可按
dyadic 壳支付；不能把同一个 Δ 的数量再免费取消。
此外此 corollary 的显式主项仍须求值，不能直接删掉。

因此这一路固定-Δ 调用不新增覆盖。对 Δ 的联合谱估计或更早
的跨 κ/AFE 重组并未被排除，但其完整权重和两边 Möbius 必须
保留。GB7 已消耗全 B/h 的除数恒等式，不能再把原来的 h
平均乘作独立 saving；也不能与 PQ 或 BBLR 的界相乘。

## 7. 验证与未完成目标

有限测试检验 GB1/GB2/GB8 的不同素因子层、非平方自由父项、
q 高素数幂、正负 h、闭乘积端点、局部 B-shell 反例及 h=0
例外。它们不检验或证明连续 Θ 尾；后者由 GB5/GB6 的积分
论证负责。没有用数值样本宣称幂次消去。

本轮确立的是全 B 重组的精确解析含义及其端点，不是新参数
覆盖。此前 PQ 子域结果保持原范围。GB7/GB9 的联合 µ(M)µ(s)
估计、完整 κ 与 AFE 参数重组、canonical zero Gram、非零补集、
reflection 交叉项和独立物理尾的目标界仍未证明。
**完整 coupled-kernel gate 与 twisted moment 未完成。**
