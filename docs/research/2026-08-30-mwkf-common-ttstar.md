# 全共同频率的跨模数 TT*：诱导 determinant 与不能删除的中间单位

白话结论：将两条长模数行通过同一条短模数行配对后，短模数确实能从
共同位移中消去。但配对仍须通过一个合法的共同单位；只保留新位移会
多算一批项。零频与非零频的交叉项也不消失。下面把这些项全部写出，
并证明新 determinant 的 gcd 坏因子在**无权完整短移位平均**中仅有亚幂次
损失。这还不是实际双 Möbius 加权平均的 saving。

**状态。** (CT1)–(CT13) 是有限恒等式或带证明的算术界；最后的谱覆盖
表是适用性审计。没有证明稠密共同字符族、原占据能量的相对 saving，
或完整 twisted moment。未恢复此前撤回的 Type-I companion 删格。

## 1. 与完整物理 adapter 的接口

[物理 adapter](2026-08-30-mwkf-physical-reflection-adapter.md) 的
(PA3)–(PA16) 已经把 (4.5) 接回共同截断的四项 reflection；必须先在每个
有限 box 重组全部 Poisson `h`，再恢复整数格。其余项核在原 mollifier
坐标是 `R=H-L=Gχ+Jχ`。本节的共同模数零频 `J₀` **不是** `Gχ`；这里
的有限 Gram 也不是原 AFE 对角。不能用本节的某个正能量项抵消原对角。

本节直接接 [共同相位 adapter](2026-08-30-mwkf-common-phase-adapter.md)
及 [联合共同频率](2026-08-30-mwkf-joint-common-frequency.md) 的 (JF2)。
它计算 prime active face 上一次 Cauchy 后的真实核，不声明所有 AFE
packet 的占据范数已与 (PA18) 等价。所有还未转移的范数成本仍在账本上。

固定平方自由 `g>1`，记 `U=U(g)`、`n=φ(g)`。固定短素数 `q`、两个
长素数 `p₁,p₂`，满足 `(gp₁p₂,q)=(p₁p₂,g)=1`；允许 `p₁=p₂`。
令 `(D,qp₁p₂)=1`，但**不要求** `(D,g)=1`。按 (JF1) 记

\[
 a_i=D\overline{p_iq}\pmod g,\quad
 A_i=C_i\overline{p_i^2}\pmod g,\quad
 \theta_i(z)=e_g(A_i\bar z),\quad (C_i,g)=1.
\tag{CT1}
\]

两条边的同一短行相位记为 `θq(w)`。设
\[
 J_i(z,w)=\theta_i(z)\overline{\theta_q(w)}
                 {\bf1}_{z-w=a_i},\qquad
 J_{i0}(z,w)={\theta_i(z)\overline{\theta_q(w)}\over g},
 \qquad J_{i\ne0}=J_i-J_{i0},\quad z,w\in U.
\tag{CT2}
\]
这只组合确实共享同一短行的两条边；若还有改变短行相位的 packet
标签，必须保留标签间的相位比，不能直接应用下面的相位消去。

## 2. 伴随合成有一个额外单位掩码

置 `b=a₁-a₂`、`r_i(z)=1_{(z-a_i,g)=1}`，并令
`Θ(z,v)=θ₁(z) overline(θ₂(v))`。有限矩阵乘法给出

\[
 \begin{aligned}
 (J_1J_2^*)(z,v)&=\Theta(z,v)
       {\bf1}_{z-v=b}\,r_1(z),\\
 (J_1J_{20}^*)(z,v)&=\Theta(z,v){r_1(z)\over g},\\
 (J_{10}J_2^*)(z,v)&=\Theta(z,v){r_2(v)\over g},\\
 (J_{10}J_{20}^*)(z,v)&=\Theta(z,v){n\over g^2},\\
 K_{\ne0}(z,v):=(J_{1\ne0}J_{2\ne0}^*)(z,v)
 &=\Theta(z,v)\left\{
 {\bf1}_{z-v=b}r_1(z)-{r_1(z)\over g}
       -{r_2(v)\over g}+{n\over g^2}\right\}.
 \end{aligned}
\tag{CT3}
\]

**证明。** 第一行的唯一可能中间变量是 `w=z-a₁=v-a₂`，它仍须在 `U`。
两条短行相位乘为 1。第二、三行各有至多一个中间变量；最后一个
零–零项有恰好 `φ(g)` 个中间变量。展开两个差即得第五行。没有换序
误差，没有假定不同频率在单位子集上正交。

素数 `g` 且 `a₁,a₂≠0` 时，第一行去相位后的矩阵是
\[
 S_b-e_{a_1}e_{a_2}^{T},\qquad
 S_b(z,v)={\bf1}_{z-v=b}\quad(z,v\in U).
\tag{CT4}
\]
这一个 rank-one 项不能丢掉。例如 `g=5,a₁=1,a₂=2,z=1,v=2`，位移
条件成立，但中间变量是 0，完整 Gram 项为 0；非零频 Gram 项却有
绝对值 `4/25`，来自零–零交叉账本。`g=2,a₁=a₂=1` 时完整边为空，
非零频 Gram 为 `1/4`。这些都不是可忽略的端点。

## 3. 一次整体 Cauchy 的有限短行能量

取有限长素数集合 `𝒫`。预相位长行在实际 active 横截面上的值写为
\[
 L_{p,q}(z)=\sum_{h,\delta,n'}w_p(h,\delta,n')\lambda(n')
 {\bf1}_{(h\delta n',gp)=1}
 {\bf1}_{h\delta+pzn'=0\ (g)}
 \left({\bf1}_{p\mid qh\delta+Dn'}-{1\over p-1}\right).
\tag{CT5}
\]
支持、平滑权、另一侧标签及精确 Type 分解均保持原样；`λ` 可以是
原 Möbius 或其 (JF13) 的一个分量，分量须先带符号重组。
外层复权记为 `H(p,q)`，包含原逆 totient、Möbius 与核权，不能默认
为 1。以下有限恒等式其实对任意已供应的 `L,H` 成立，但物理 saving
若要利用 Möbius，必须使用 (CT5) 的真实系数。

令 `y_p=-D overline(p) mod q`，`⋆∈{all,0,≠0}`，并定义
\[
 \begin{aligned}
 F_{q,\star}(y,w)&=\sum_{p\in\mathcal P}H(p,q)
    {\bf1}_{y=y_p}\sum_{z\in U}L_{p,q}(z)J_{p,q,\star}(z,w),\\
 F_{q,\star}^{\circ}(y,w)&=F_{q,\star}(y,w)
            -{1\over q-1}\sum_{u\in U(q)}F_{q,\star}(u,w),\\
 E_{q,\star}&=\sum_{y\in U(q),w\in U}|F_{q,\star}^{\circ}(y,w)|^2.
 \end{aligned}
\tag{CT6}
\]
长模数和在平方**里面**。若短行 `B_q(y,w)` 在 active `y` 上零和，则
与它的配对不受 `F→F°` 影响。对全部 `q,y,w` 只做一次 Cauchy 得到
\[
 \left|\sum_{q,y,w}F_{q,\star}(y,w)\overline{B_q(y,w)}\right|^2
 \le\left(\sum_q v_qE_{q,\star}\right)
       \left(\sum_q v_q^{-1}\|B_q\|_2^2\right),\quad v_q>0.
\tag{CT7}
\]
这里没有将短行替换成无符号计数。若还要投影到共同字符补集，应在
(CT6) 配对空间保留那个投影；直接使用完整 `E` 只是一个上界，不是
投影能量的等式。不同 `ω` 标签的联合重组及其范数比较也不能免费加入。

设 `K_{12,⋆}=J_{p₁,q,⋆}J_{p₂,q,⋆}*`，并缩写
\[
 V_{12,\star}=H(p_1,q)\overline{H(p_2,q)}
   \sum_{z,v\in U}L_{p_1,q}(z)\overline{L_{p_2,q}(v)}K_{12,\star}(z,v).
\]
由 `(D,q)=1`，`y_{p₁}=y_{p₂}` 等价于 `p₁=p₂ mod q`。因此
\[
 \boxed{E_{q,\star}
  =\sum_pV_{pp,\star}
   +\sum_{\substack{p_1\ne p_2\\q\mid p_2-p_1}}V_{12,\star}
   -{1\over q-1}\sum_{p_1,p_2}V_{12,\star}.}
\tag{CT8}
\]
这是**未乘 `φ(q)`** 的规范化；若使用主笔记 (9.1243) 的能量，则整式
乘 `φ(q)`，不能只给第一项乘。末项为一个非负平方和的负号，但其
内部仍有全部共同频率、Type 交叉项；不应单独取绝对值收费。

## 4. incidence 上的短模数消去及 gcd 平均

只有 (CT8) 中 `q|(p₂-p₁)` 的 incidence 项，才能置 `p₂-p₁=jq`。
对其中的 **`p₁≠p₂`** 项，两个 active 逆元均存在，于是
\[
 \boxed{b=Dj\overline{p_1p_2}\pmod g,\qquad
 D\bar q\equiv Dj\overline{p_2}\pmod{p_1},\qquad
 D\bar q\equiv-Dj\overline{p_1}\pmod{p_2}.}
\tag{CT9}
\]
证明只需代入 `p₂-p₁=jq`；没有除以 `j`，所以 `j` 非单位也成立。
`j=0` 即原长模数对角，必须单列：此时仅共同位移等式仍成立，
不能写 `overline(p₂) mod p₁`。若 `p_i∈(P,2P]`、`q∈(Q,2Q]`，
则 `|j|<P/Q`，但每个 `p_i` 与素数 `q=(p₂-p₁)/j` 都保留字面支持。
当 `Q²>P` 时，一个非零差 `|p₂-p₁|<P` 至多被一个 `q>Q` 的素数
整除，因为两个不同这样的素数的乘积已超过该差。这是稀疏性，
不是带符号消去。

**不能省掉的限制：** density 项中的任意 `p₁,p₂` 未必满足 incidence，
所以不能对那一项使用整数 `j` 或以 `Dj` 替换 `D`。此外 (CT3) 的
`r₁,r₂` 仍依赖 `q`。因此 (CT9) 不将完整能量自动变成一个独立的
balanced long–long Kloosterman 和。

不过新 determinant 的坏 gcd 可以精确平均。令 `d₀=(g,D)`、`g₀=g/d₀`，
平方自由性给出 `(g,Dj)=d₀(g₀,j)`。对整数 `J≥0`，
\[
 \begin{aligned}
 \sum_{1\le j\le J}\sqrt{(g,Dj)}
 &=\sqrt{d_0}\sum_{d\mid g_0}
       \prod_{\ell\mid d}(\sqrt\ell-1)\left\lfloor{J\over d}\right\rfloor\\
 &\le J\sqrt{d_0}\prod_{\ell\mid g_0}
               \left(1+{\sqrt\ell-1\over\ell}\right)
 \ll_\varepsilon J\sqrt{d_0}\,g^\varepsilon.
 \end{aligned}
\tag{CT10}
\]
**证明。** `√(g₀,j)=Σ_{d|(g₀,j)}∏_{ℓ|d}(√ℓ-1)` 是逐素数恒等式；
所有系数非负，换序后保留确切 floor，再以 `J/d` 上界。Euler 因子
对大素数小于 `ℓ^ε`，有限小素数吸入常数。`J=0` 时两边为 0；负
`j` 同样计算，双向和乘 2，不包括 `j=0`。这既不产生常数级假设，
也不产生额外 `J^{1/2}` 的最坏 gcd 损失。

可直接形式化的整数版本是：对每个 `d|g₀`，
\[
 \#\{1\le j\le J:(g,Dj)=d_0d\}
       =\sum_{e\mid g_0/d}\mu(e)\left\lfloor{J\over de}\right\rfloor.
\tag{CT11}
\]
脚本用 (CT11) 产生精确整数 histogram，并以独立逐 `j` 计数作回归。
(CT10) 只针对无权完整平均；若真实系数集中在坏 `j`，不能除以 `J`
后将此平均乘到加权范数上。带物理权的占据分布仍须证明。

## 5. 混合 Weil 界仍成立，但没有稠密族的免费 saving

将 (CT3) 按 (JF4) 的 convention 变到单位字符基。对 `ℓ|g, ℓ∤b`，
完整 Gram 的有理相位仍有两个不同简单极点；比 (JF4) 只多删除一个
可能的普通点 `z=a₁`。所以同一混合 Weil 界仍为 `O(√ℓ)`。若 `ℓ|b`，
使用平凡 `ℓ-1` 界。CRT 和 `φ(g)` 归一化给出
\[
 |(\mathcal U^T K_{\mathrm{all}}\overline{\mathcal U})_{\eta,\xi}|
       \ll_\varepsilon g^{-1/2+\varepsilon}\sqrt{(g,b)}.
\tag{CT12}
\]
这里 `𝒰` 表示单位字符的酉矩阵。混合 Weil
输入及来源与 (JF5) 相同。两条 mixed-zero 项分离成一个少去至多
一个点的 Gauss 和与一个 Gauss 和；逐素数都是 `O(√ℓ)`，故三个零频
修正的规范化矩阵元均 `≪g^{-1+ε}`。因此 (CT12) 也适用于 `K≠0`。
在 incidence 上 `(g,b)=(g,Dj)`，(CT10) 可以控制**无权**短移位和中
的这一个坏因子；它没有控制 (CT5) 的稠密字符系数和。

这种区分必要：若 `g≥7` 为素数、`a₁,a₂` 为不同非零元，则完整 Gram
有 `g-3` 个等距方向。(CT3) 的零频修正的秩至多 2。与其核相交后
仍至少有 `g-5` 个等距方向，而两个非零频边均为收缩。因此
\[
                 \|J_{1\ne0}J_{2\ne0}^*\|=1.
\tag{CT13}
\]
这排除再次声称任意稠密系数有小范数；不反驳实际 Selberg 系数目标。

## 6. 已发表输入与现在真正缺的 adapter

| 输入 | 本节真实对象的缺口 | 可记入的结论 |
|---|---|---|
| [Pascadi, Theorem 3](https://arxiv.org/html/2404.04239v3)：特定光滑 dispersion 系数的大筛 | (CT5) 的双 Möbius、prime quotient 支持和 moving residue 不是该定理指定的光滑系数；还需其 level/斜率限制 | 不能仅因出现短 `j` 就登记 saving |
| [Pascadi, Theorem 9.4](https://link.springer.com/article/10.1007/s00039-026-00746-0)：composite level 谱大筛 | 它确实允许逐 level 使用不同系数；仍须先由 (CT8) 导出指定谱和，保留权、归一化和范数 | 不能用“系数随 level 变化”一概排除，也不能视为 adapter 已有 |
| [Blomer–Pascadi, Theorem 1.1](https://arxiv.org/html/2607.24311v1#S1.Thmtheorem1)：固定模数 Kloosterman 双线性型 | `Dj` 同时进入位移、active 横截面和 prime quotient，另有中间单位与 density 补偿 | 此前平方根长度的 `c^{-1/32}` 是模型输入，不是本题覆盖 |
| (CT9)–(CT12) 的 induced determinant/gcd 计算 | 不含真实加权移位占据界，也未给出 Kuznetsov adapter | 已证无权 gcd 平均只需亚幂次损失；没有新稠密格覆盖 |

下一项要攻的是 **(CT8) 的两项联合 remainder**：非零短移位项减去
完整 density 项，连同 (CT3) 的所有零频交叉项，在真实 (CT5) 系数上
达到对角规模。或者回到 (PA18) 的全 signed 核，证明一个不经此正
能量的更弱充分界。两条路线都不能把有限重写当作未证 saving。

验证范围：`common_frequency_gram_kernel` 检查 (CT3) 与独立 Fourier
构造的四个乘积；`centered_common_fiber_energy` 比较先全局合成再
中心化的直接能量与 (CT8)；`induced_shift_gcd_histogram` 检查 (CT11)。
有限复数核使用浮点误差容限，histogram 为精确整数。测试不验证
连续 AFE 积分、混合 Weil 定理或完整 twisted moment。
