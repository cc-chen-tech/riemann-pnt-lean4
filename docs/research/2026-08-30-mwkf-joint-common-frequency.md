# 联合共同频率：小字符族覆盖与稠密族的精确范数障碍

白话结论：共同零频之外也能得到一块真正的覆盖。办法不是把每个频率
分别估计，而是先将全部共同频率重组成双极点核，再保留共同字符族的
实际大小。Weil 的平方根节省在字符族足够小时不会被重组成本吃掉。
但只删零频、再删两侧主字符，并不能让整个稠密字符空间的算子范数变小。

**状态。** 下述联合恒等式、小共同字符族范数界及其与已登记 active
大筛/行能量的组合已证明；包含非零共同频率补集。完整 coupled-kernel
gate、稠密共同字符族和完整 twisted moment 仍未证明。本节不恢复
[共同相位修正](2026-08-30-mwkf-common-phase-adapter.md) 撤回的 Type-I 删格。

## 1. 在取绝对值之前重组共同频率

固定原 packet 标签、平方自由共同模数 \(g>1\)、active 模数
\(r_1,r_2\)（均与 \(g\) 互素）和非零整数 determinant \(D\)。令
\[
 \Delta=D\overline{r_1r_2}\pmod g,\quad
 A=C_1\overline{r_1^2},\quad B=C_2\overline{r_2^2},\quad
 (C_1C_2,g)=1,\quad n_g=\varphi(g).
\tag{JF1}
\]
记 \(Z_i(z)\) 为 (CG2) 在 \(s=r_i z\) 上的**预相位**行；它保留
全部 \(h\delta\)、Type、active 与平滑标签，并在非单位处延零。
置 \(\theta_1(z)=e_g(A\bar z)\)、\(\theta_2(z)=e_g(B\bar z)\)。
于是 (9.1114) 给出精确有限恒等式
\[
 \begin{aligned}
 \mathscr B&={1\over g}\sum_{\nu\bmod g}
  \widehat{\theta_1Z_1}(\nu)
  \overline{\widehat{\theta_2Z_2}(\nu)}e_g(\nu\Delta)\\
 &=\sum_{z,w\in U(g)}Z_1(z)\overline{Z_2(w)}J(z,w),\\
 J(z,w)&=\theta_1(z)\overline{\theta_2(w)}
             {\bf1}_{z-w=\Delta\ (g)}.
 \end{aligned}
\tag{JF2}
\]
共同零频与非零共同频率的核分别为
\[
 J_0(z,w)={\theta_1(z)\overline{\theta_2(w)}\over g},\qquad
 J_{\ne0}=J-J_0.
\tag{JF3}
\]
所有轴、模数非单位和空支持均由这些有限公式处理，没有截断误差。
这里的零频仍不是 canonical reflection Gram；不得改名后混同。

采用标准内积 \(\langle u,v\rangle=\sum\bar u v\) 时，物理双线性式
是 \(\langle\bar Z_1,J\bar Z_2\rangle\)。设
\(e_\eta(z)=\eta(z)/\sqrt{n_g}\) 且 \(Z_i=\sum_\eta a_{i,\eta}e_\eta\)，
实际字符矩阵元为
\[
 M_{\eta,\xi}={1\over n_g}
   \sum_{\substack{z\bmod g\\(z(z-\Delta),g)=1}}
   \eta(z)\overline{\xi(z-\Delta)}
   e_g(A\bar z-B\overline{z-\Delta}).
\tag{JF4}
\]
因此 \(\mathscr B=\sum_{\eta,\xi}a_{1,\eta}\bar a_{2,\xi}M_{\eta,\xi}\)。
矩阵关系是 \(M=U^TJ\bar U\)，不是 \(U^*JU\)；两边变换仍为酉矩阵。

## 2. Weil 节省与共同字符计数必须一起记账

令 \(d_0=(g,D)=(g,\Delta)\)。在素数 \(\ell\mid g\)、\(\ell\nmid D\)
处，(JF4) 的加性有理函数有两个不同的简单极点且残数非零。
乘性字符任意，包括 principal；加性非退化性保证混合 Weil 界的常数
与字符阶无关。若 \(\ell\mid D\)，安全地使用平凡界 \(\ell-1\)。
CRT 后得到
\[
 |M_{\eta,\xi}|\ll_\varepsilon
       g^{-1/2+\varepsilon}d_0^{1/2}.
\tag{JF5}
\]
这是主笔记 (9.1052) 的规范化形式。其输入是经典混合有理字符和
Weil 界，可参见已发表的
[Cochrane–Pinner, JNT 116 (2006), 270–292](https://doi.org/10.1016/j.jnt.2005.04.001)；
所用极点计数版本也明确写在
[Cochrane–Granville, (1.4) 与 §4](https://arxiv.org/html/2604.02614v1#S4)。
这里只用平方自由 CRT；没有套用该文的 prime-power 新估计。
\(\ell=2\) 直接平凡处理，常数仍为 \(g^\varepsilon\)。

零频核不能遗漏。平方自由 Gauss 和满足
\(\left|\sum_{z\in U(g)}\eta(z)e_g(A\bar z)\right|\le\sqrt g\)，
包括 imprimitive 字符。因此
\[
 |(M_0)_{\eta,\xi}|\le {1\over\varphi(g)},\qquad
 |(M_{\ne0})_{\eta,\xi}|
 \ll_\varepsilon g^{-1/2+\varepsilon}d_0^{1/2}.
\tag{JF6}
\]
这一步先保留全部频率，再准确减去 \(\nu=0\)，不是逐非零频率使用
同一个 Weil 界后把 \(g\) 个频率免费求和。

固定共同字符族 \(E_L,E_S\)，大小为 \(K_L,K_S\ge1\)。它们可依赖
已固定的 \(\omega,g,D\)，但在同一个 active 模数平均中必须是共同的
族；若随 active 模数变化，\(K_i\) 必须计其并集，而非逐行最大值。
由矩阵元界、两次有限 Cauchy 及酉性，
\[
 \|U_{E_L}^{T}J_\star\overline{U_{E_S}}\|\ll_\varepsilon
 \min\!\left(1,
      g^{-1/2+\varepsilon}d_0^{1/2}\sqrt{K_LK_S}\right),
 \qquad \star\in\{\mathrm{all},\ne0\}.
\tag{JF7}
\]
这里 \(U_E\) 的列为 \(\eta/\sqrt{\varphi(g)}\)、\(\eta\in E\)，是
字符坐标的等距嵌入；等价地直接限制
(JF4) 的行列指标即可。常数 1 来自完整共同 Fourier 变换中删除或
保留频率后再施加单位平移相位，故 \(J\) 与 \(J_{\ne0}\) 均为收缩。
空字符族的双线性式恒为零，另行计账即可。

## 3. 与 active 模数平均组合：新的覆盖多面体

不能只证明 (JF7) 就宣称它已穿过 active 平均。现给出组合步骤。
设 \(a_{c,\psi,\eta},b_{d,\chi,\xi}\) 是包含原逆 totient 归一化
之后的实际行系数。对每一个固定 \((\eta,\xi)\)，(JF5) 或 (JF6)
是与 active 字符 \(\psi,\chi\) 无关的标量模数乘子上界。因此
主笔记 (9.1117) 接受
\(H(c,d)=M_{\eta,\xi}(c,d)\) 除以该统一上界。
应用该定理后，剩余共同标签和满足
\[
 \sum_{\eta\in E_L,\xi\in E_S}
  \|a_\eta\|_2\|b_\xi\|_2
 \le\sqrt{K_LK_S}\,
    \left(\sum_\eta\|a_\eta\|_2^2\right)^{1/2}
    \left(\sum_\xi\|b_\xi\|_2^2\right)^{1/2}.
\tag{JF8}
\]
共同预相位投影与 active 字符变换交换。共同 Parseval、投影收缩及
单位相位保证 (JF8) 中的两个范数仍为 §9.144 已登记行能量的子能量。
这证明 (JF7) 的第二个因子能乘进 **同一个** active 大筛账本。
不用小族时原 (9.1114)–(9.1119) 提供第一个因子 1；取两者较小值。

写
\[
 g=T^\gamma,\quad d_0=T^\delta_0,\quad K_i\le T^{\kappa_{E_i}+o(1)},
 \quad 0\le\delta_0,\kappa_{E_i}\le\gamma.
\]
额外的线性节省指数为
\[
 s_E={1\over2}
       (\gamma-\delta_0-\kappa_{E_L}-\kappa_{E_S})_+.
\tag{JF9}
\]
保留完整 \(\eta_{\rm imb}\)，不减去已撤回的 short-Type-I gain，得到
\[
 \boxed{\kappa_{E_L}+\kappa_{E_S}+2\eta_{\rm imb}
                 \le\gamma-\delta_0.}
\tag{JF10}
\]
在此条件下，选定共同字符子空间的**全共同频率**以及单独的
**非零共同频率补集**均在原 bounded-determinant 目标内。
\(|D|\le T^{o(1)}\) 时 \(\delta_0=o(1)\)，其有限求和成本包含在
原 bounded-\(D\) 账本中。这里只用已有 active \(\kappa_i\) 余量；
没有再次扣除共同导子的 \(g/f\)，没有把两次 PV 节省再乘一次。

具体取 \(E_B(g)=\{\eta:\eta^B=1\}\)、固定 \(B\)，则
\[
 |E_B(g)|=\prod_{\ell\mid g}(B,\ell-1)
          \le B^{\omega(g)}=g^{o(1)}.
\tag{JF11}
\]
故两侧固定阶共同字符族在 \(\gamma\ge2\eta_{\rm imb}\) 时覆盖。
这不是“低导子”假设：素数 \(g\) 上的二次共同字符具有导子 \(g\)。
在极端 \(g\asymp T,\eta_{\rm imb}=1/4\) 上，它新增覆盖两侧二次
共同字符的非零共同频率，哪怕 active 字符仍高阶且 near-primitive。
更一般地，\(\kappa_{E_L}+\kappa_{E_S}\le1/2\) 的指定小族可覆盖。

不能把完整字符集切成许多小族，然后无成本相加。(JF8) 的共同标签
Cauchy 会恢复全部族的计数；稠密的 \(K_L,K_S\asymp g\) 没有此增益。

## 4. 原双 Möbius Type 结构没有被替换

共同坐标由 \(z=-m\overline{r n}\)、\(m=h\delta\) 消去时，
\[
 \bar\eta(z)=\bar\eta(-1)\eta(r)\bar\eta(m)\eta(n).
\tag{JF12}
\]
若采用 (CG13) 的 active 字符标签，则真实组合仍为
\(\Xi=\chi_{\rm active}\bar\eta\)，同时保留 (JF12) 的单位扭曲。
它与 \(h\delta\) 的分解为
\(\Xi(h)\Xi(\delta)\)；不能替换为一个任意乘积标签系数。

对每一侧的原 Type 变量，定义 \(M=\max(U,V)\)：
\[
 \begin{aligned}
 \lambda_0(n)&=\mu(n){\bf1}_{n\le M},\\
 \lambda_I(n)&=-{\bf1}_{n>M}
       \sum_{bcr=n; b\le U,c\le V}\mu(b)\mu(c),\\
 \lambda_{II}(n)&={\bf1}_{n>M}
       \sum_{bcr=n; b>U,c>V}\mu(b)\mu(c),\\
 \mu(n)&=\lambda_0(n)+\lambda_I(n)+\lambda_{II}(n).
 \end{aligned}
\tag{JF13}
\]
这是此前已证明的有限 two-cutoff 恒等式；所有等号端点与小项保留。
原 \(\mu(n_1)\mu(n_2)\) 因而给出九个有序块，全部使用同一个
\(J\) 或 \(J_{\ne0}\)、共同字符投影、原 \(h_i,\delta_i\) 支持及单位
掩码，完整 signed 和先重组才使用 (JF8)。若还分解 active conductor
的 Möbius 权，依 §9.168 保留相应短 cofactor 与额外四个 I/II 块。
没有把一个 Type 块的行能量等同于原重组 Möbius 行能量；覆盖断言只
针对选定字符族上的重组和。

## 5. 为什么稠密族不能只靠再中心化解决

对奇素数 \(g\)、\(\Delta\ne0\)，\(J\) 有 \(g-2\) 个非零奇异值，
全为 1。去掉两侧单位相位并排列行列后，\(J_{\ne0}\) 酉等价于
\[
 \operatorname{diag}(I_{g-2},0)-{1\over g}{\bf1}{\bf1}^T.
\tag{JF14}
\]
在前 \(g-2\) 个坐标的零和子空间上特征值为 1；余下二维矩阵为
\[
 {1\over g}\begin{pmatrix}2&-\sqrt{g-2}\\-\sqrt{g-2}&-1\end{pmatrix}.
\]
故全部奇异值恰为
\[
 \boxed{1\ (g-3\text{ 次}),\qquad
     {\sqrt{1+4g}+1\over2g},\qquad
     {\sqrt{1+4g}-1\over2g}.}
\tag{JF15}
\]
\(g=3\) 的第一族为空；\(g=2,\Delta=1\) 单独为奇异值 \(1/2\)。
后者的完整单位 shift 为空，但零频与非零频分别非零且精确抵消。

再令 \(P=I-{f1}{\bf1}^T/(g-1)\)，删除两侧预相位共同主字符。
(JF15) 的等距子空间有维数 \(g-3\)。附加
\(v\perp{f1}\)、\(J_{\ne0}v\perp{f1}\) 至多各损失一维。
因此对 \(g\ge7\)，
\[
 \boxed{\|P J_{\ne0}P\|=1,\qquad
    \text{等距方向至少有 }g-5\text{ 维}.}
\tag{JF16}
\]
这是任意系数空间的障碍，不是 Selberg 系数的反例。它证明“删零频＋
两侧删主字符”仍不足以给出统一的小算子范数；新的分析必须利用
真正的 Type/hδ 系数或跨 active 模数联合抵消。

## 6. 与已发表估计的覆盖表及剩余目标

| 实际对象或区域 | 核验的输入 | 结论 |
|---|---|---|
| 所有共同频率，active imbalance 已由 active cofactor 余量补偿 | §9.168 互字符大筛与 Parseval | 原覆盖保持 |
| 指定共同字符族，(JF10) 成立 | 混合 Weil＋(JF8)，原行能量 | 新增全频率及非零频补集覆盖 |
| \(\nu=0\)、低共同导子 | (CG20)–(CG23) 精确投影范数 | 上一轮覆盖保持；不与 (JF10) 免费相乘 |
| 稠密共同字符族 | 完整矩阵元虽有 Weil 界，(JF16) 的范数仍为 1 | 无统一幂次覆盖 |
| 固定模数、已是 \(S(am,n;c)\) 的独立区间 Type-II 和 | [Blomer–Pascadi, Theorem 1.1](https://arxiv.org/html/2607.24311v1#S1.Thmtheorem1) | 临界平方根长度节省 \(c^{-1/32}\)；未给出本题变化的两侧 residue profiles adapter |
| 有合适因子分解的固定模数 Kloosterman Type-II 和 | [Pascadi, Theorem 1.2](https://link.springer.com/article/10.1007/s00039-026-00746-0) | 两个同规模素因子的情形可节省 \(c^{-1/12}\)；不能与前一行重复消费同一个和的节省 |
| 原稠密双 Möbius moving-level 和 | (JF2)、(JF12)、(JF13) 精确保留其输入 | 联合谱/dispersion 界仍未证明 |

此表不把“某个固定 Kloosterman 形式有节省”当作物理覆盖。即使在
\(g=T\) 且假设理想 adapter 的平方根长度模型中，上述两个数字分别
只有 \(1/32\)、\(1/12\)，也均不足以单独支付极端 \(\eta_{\rm imb}=1/4\)。
对于实际 moving-level 系数，adapter 本身尚需证明，不能先记这些幂次。

下一项真正未证的输入是 (JF10) 之外的**稠密共同字符、active imbalance**
投影上，保留 (JF13) 双 Möbius 和 \(h\delta\) 后的 signed 联合界。
本节缩小了它的支撑，但没有证明该输入或完整 gate。
