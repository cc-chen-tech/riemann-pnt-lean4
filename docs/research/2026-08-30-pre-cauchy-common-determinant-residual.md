# Pre-Cauchy 长素数平均：共同频率、整数零层与射线剩余相位

白话结论：共同 Fourier 平均不会自动冲掉拥挤项。它强制一个明确的
整数 \(R\) 被共同模数 \(g\) 整除，而 \(R=0\) 的项全部同相叠加。
用这个整数可以同时分解两侧中心化产生的四项，不必给密度减项虚构
整数商。零层中的双 incidence 部分还能重组为两个保留 Möbius 符号的
伸缩和；共同算术相位在每条射线上不随伸缩变化，但随长素数变化。
进一步检查双边 dyadic 支持后发现：当两侧物理比率可比而长短素数
相差一个固定幂次时，这个整数零层可以直接为空。特别是旧极端
尺度的真正双边子块满足该条件；这不删除共同 Fourier 零频本身。

**证明边界。** 本文证明有限恒等式、零层的完整定义、射线权重公式，
以及固定射线/固定相位参数的完整剩余类平均公式。实际加权长素数
色散、零层与原 AFE/reflection 主项的抵消、\(14/17\) 与 \(2/3\)
零点排除仍未证明。没有 Lean 修改。有限检查仅用于防止符号和归一化错误。

## 1. 来源、原物理权重与共同相位

来源是 docs-mobius-weighted-offdiagonal-20260824 worktree，读取版本
678e8eb8 的主笔记 §§9.168–9.190，及同版本
2026-08-30-mwkf-common-phase-adapter.md 的 (CG3)、(CG4)、(CG18)。
本篇补充旧 determinant/ray 分解；不恢复共同相位修正已撤回的 Type-I
覆盖，也不把已有共同字符族 Weil 节省再记一次。

固定一个原有限平滑 atom 及其外标签。设 \(g>1\) 平方自由，\(p\ne q\)
为素数，准确条件为

\[
 (g,pq)=1,\qquad (D,pq)=1,\quad D\ne0,\qquad (C_1C_2,g)=1.
\tag{R1}
\]

不假设 \((D,g)=1\)。两侧单位条件是 \((mn,gp)=(uv,gq)=1\)，
没有偷偷加入交叉条件 \((v,p)=(n,q)=1\)。原权重记为

\[
 w_{p,q}(m,n,u,v)
 =\mathfrak w(p,q) f_p(m)b_p(n)\overline{f_q(u)b_q(v)}.
\tag{R2}
\]

\(f_p(m)\) 仍是全部 \(m=h\delta\) 的原有限和，不是任意选择的新系数。
所有剩余单位掩码、支持、AFE/reflection 标签保留于原和中。一般不分离
的额外权也可留在 \(w\)；只有 §4 的乘积公式要求 (R2) 的 atom 分离。
若 \(C_i\) 随标签变化，以下先逐原标签使用恒等式。§4 在伸缩求和
之前就要求 \(C_i\bmod g\) 固定，且该限制不引入额外的两侧耦合；
否则只能保留带 \(C_i(a,b)\) 的双和，不能宣称相位与伸缩无关。
§5–§6 还要求在素数平均中固定这两个剩余类，其重新求和成本不视为免费。

置 \(I_p={\bf1}_{p\mid qm+Dn}\)、\(I_q={\bf1}_{q\mid pu-Dv}\)，以及

\[
 \Delta_p=I_p-\frac1{p-1},\quad
 \Delta_q=I_q-\frac1{q-1},\qquad
 \Phi=-C_1\overline p\,n\overline m
          +C_2\overline q\,v\overline u\pmod g.
\tag{R3}
\]

从 (CG3) 得到，乘上共同 Fourier 平移因子后，单个四元组的完整贡献是

\[
 w\Delta_p\Delta_q e_g(\Phi)\frac1g\sum_{\nu\bmod g}
 e_g\left(\nu\left[\frac D{pq}+\frac m{pn}-\frac u{qv}\right]\right).
\tag{R4}
\]

所有分式在模 \(g\) 中解释，分母均为单位。右行共轭已进入两个负号；
共同零频本身的贡献为 \(g^{-1}w\Delta_p\Delta_q e_g(\Phi)\)。
这不是把用户的零频平均改换目标，而是在其原共同频率母式中核查
哪些项可跨频率重装配。若只估计原 \(\nu=0\) 子式，必须保留 \(1/g\)。

## 2. 一个整数同时组织全部四项

定义

\[
 \boxed{R=pnu-qmv-Dnv.}
\tag{R5}
\]

则方括号恰为 \(-R/(pqnv)\)。有限正交性立即给出

\[
 \boxed{\mathscr S_{\rm all}
 =\sum w e_g(\Phi)\Delta_p\Delta_q\, {\bf1}_{g\mid R}.}
\tag{R6}
\]

因此得到**包含全部密度减项**的精确分解

\[
 \begin{aligned}
 \mathscr M_0&=\sum_{R=0} w e_g(\Phi)\Delta_p\Delta_q,\\
 \mathscr E_{\ne0}&=\sum_{R\ne0,\ g\mid R}
                w e_g(\Phi)\Delta_p\Delta_q,\\
 \mathscr S_{\rm all}&=\mathscr M_0+\mathscr E_{\ne0}.
 \end{aligned}
\tag{R7}
\]

这里“main”仅指明确的 residual 候选，不意味着已证明它大、已算出
渐近式，或已与 AFE 对角匹配。

展开 \(\Delta_p\Delta_q=I_pI_q-I_p/(q-1)-I_q/(p-1)
+1/((p-1)(q-1))\)，四项使用同一个 \(R=0\) 判据。
若仅 \(I_p=1\)，写 \(pr=qm+Dn\)，则 \(R=p(nu-rv)\)；
若仅 \(I_q=1\)，写 \(qs=pu-Dv\)，则 \(R=q(ns-mv)\)。
无 incidence 的项仍使用 (R5)，不引入不存在的整数商。

双 incidence 上，因 \((D,q)=1\)，

\[
 t=\frac{nu-rv}{q}=\frac{rs-mu}{D}\in\mathbb Z,
 \qquad R=pq\,t.
\tag{R8}
\]

第二个等式来自 \(q(rs-mu)=D(nu-rv)\)。所以双 incidence 的共同
条件恰为 \(g\mid t\)，而不是额外乘一个 \(1/g\)。在 \(t=0\) 上
(R4) 每一个 \(\nu\) 的相位均相同：相对于仅取 \(\nu=0\)，恢复全部
频率恰恢复 \(g\) 倍。原 Fourier \(1/g\) 已被求和花掉。

**中心化不会逐点删除零层。** 若再限制交叉单位子区

\[
 (v,p)=(n,q)=1,
\tag{R9}
\]

则 \(R=0\) 模 \(p\)、模 \(q\) 分别强制 \(I_p=I_q=1\)，故其中心化
因子为 \((1-1/(p-1))(1-1/(q-1))\)，对 \(p,q>2\) 严格正。
这是核因子的符号，不是带复权和的下界。补区不能丢掉。
例如 \(g=5,p=7,q=3,D=1,m=2,n=u=v=1,C_1=C_2=1\) 的零层贡献为

\[
 \frac5{12}e_5(3)\ne0.
\tag{R10}
\]

## 3. 原高阶 active 投影必须保留

(R6)–(R7) 首先针对 principal-centered 母式。若用户的 \(A_p,B_q\)
采用 \(P_{>B}\)，则在这母式上减去实际固定阶 active 字符投影。
不能把 \(\mathscr M_0\) 直接称为已经高阶投影后的完整主项，也不能
在投影后逐点套用 (R9)。原稀疏投影已有的能量界与这里的整数零层
分解是不同步骤；其 \(R=0\) 限制未被该全和能量界自动控制。

因此当前可用的原式组织是：完整中心化母式 \(\mathscr M_0+\mathscr E_{\ne0}\)，
再保留全部实际 sparse correction。对单独零频，零层则是

\[
 \mathscr M_{0,\nu=0}=g^{-1}\mathscr M_0.
\tag{R11}
\]

## 4. 双 incidence 零层：原 Möbius 符号的射线重装配

为明确写出一条无符号歧义的参数化，本节限制 \(m,n,u,v>0\)，且
双 incidence、\(R=0\)。这时 \(r=nu/v>0,s=mv/n>0\)。其他符号支持
仍由 (R7) 精确保留，不从本节获得额外估计。

三维向量 \(X=(r,m,n)\)、\(Y=(u,s,v)\) 满足

\[
 X\times Y=(-pt,qt,Dt).
\]

故唯一存在正整数 \(a,b\) 及原始正整数向量 \((x,y,z)\)，使

\[
 X=a(x,y,z),\quad Y=b(x,y,z),\quad
 (x,y,z)=1,\quad px-qy=Dz.
\tag{R12}
\]

**这里不要求 \((a,b)=1\)**；原始向量规范化与旧的“伸缩因子互素”
规范化不同，不能把两个条件同时加上。由原单位掩码，\(a,b,x,y,z\)
都是模 \(g\) 的单位，且 \(ay,az\) 是模 \(p\) 的单位，\(bx,bz\) 是
模 \(q\) 的单位。代入 (R3) 得

\[
 \boxed{\Phi_0=-C_1\frac{z}{py}+C_2\frac{z}{qx}\pmod g.}
\tag{R13}
\]

它与 \(a,b\) 无关。这只在固定射线上恢复共同相位的可分离性；
一般四变量的共同相位仍不可免费分离。

先将所有原 Type 块按点重装配为

\[
 b_p(n)=\mu(n)\widetilde b_p(n),\qquad
 b_q(v)=\mu(v)\widetilde b_q(v).
\]

定义仍含原支持及单位掩码的两个有限伸缩和

\[
 \begin{aligned}
 L_p(y,z)&=\sum_{a\ge1,(a,z)=1}
       \mu(a) f_p(ay)\widetilde b_p(az),\\
 L_q(x,z)&=\sum_{b\ge1,(b,z)=1}
       \mu(b) f_q(bx)\widetilde b_q(bz).
 \end{aligned}
\tag{R14}
\]

由 \(\mu(az)=\mu(a)\mu(z){\bf1}_{(a,z)=1}\)，双 incidence 零层
的**未中心化 \(I_pI_q\) 项**恰为

\[
 \boxed{\mathscr M_{11,0}=
 \sum_{p,q,D}\mathfrak w(p,q)
 \sum_{\substack{x,y,z>0\text{ primitive}\\px-qy=Dz}}
 \mu(z)^2 e_g(\Phi_0)L_p(y,z)\overline{L_q(x,z)}.}
\tag{R15}
\]

未满足两侧核心单位条件的射线贡献定义为零。一般不分离的原 atom
改用同一个 \(a,b\) 双和，(R13) 仍成立，不能强行写成 (R15)。
其余三个密度零层仍是 (R7) 的显式限制；(R15) 不取代它们。

这给出两个具体结论：共同相位不妨碍同射线伸缩求和；公共原始
坐标 \(z\) 上的 Möbius 权变成 \(\mu(z)^2\)，消去仍须来自两条
伸缩和或跨射线/跨素数耦合，不能再期待 \(\mu(z)\) 的符号。
一般 \(p,q\) 的两条和不相等，(R15) 也不是已知的正定 LCM 平方。

## 5. 射线上的长素数相位：完整剩余类平均可精确算出

先固定射线及 \(C_1,C_2\bmod g\)。在任一 \(\ell\mid g\) 上，
所有 \(x,y,z,C_i\) 均为单位。由 \(q=(px-Dz)/y\)，置

\[
 a_0=Dz/x,\quad \alpha=-C_1z/y,\quad
 \beta=C_2zy/x^2.
\tag{R16}
\]

则 \(\Phi_0(p)=\alpha/p+\beta/(p-a_0)\)。这里局部求和变量记作
\(P\in\mathbb F_\ell\)，它是**剩余类，不是素数集合**。
CRT 分解 \(e_g\) 时的局部单位系数同时乘入 \(\alpha,\beta\)。

若 \(\ell\nmid D\)，则 \(a_0\ne0\)。变换 \(U=P/(P-a_0)\) 把
\(P\notin\{0,a_0\}\) 双射到 \(U\notin\{0,1\}\)，给出

\[
 \begin{aligned}
 K_\ell
 &=\sum_{P\ne0,a_0}e_\ell(\alpha/P+\beta/(P-a_0))\\
 &=e_\ell((\alpha-\beta)/a_0)
   S(\beta/a_0,-\alpha/a_0;\ell)-1,\\
 S(A,B;\ell)&=\sum_{U\ne0}e_\ell(AU+B/U).
 \end{aligned}
\tag{R17}
\]

由经典 Kloosterman Weil 界，\(|K_\ell|\le2\sqrt\ell+1\)。这里只
调用该标准完整和界；参见 [Kowalski–Sawin, Kloosterman paths,
§2](https://arxiv.org/pdf/1410.7892)。
没有将论文中的其他平均定理套给当前物理系数。

若 \(\ell\mid D\)，两个极点合并，直接正交性给出更精确的分类

\[
 K_\ell=
 \begin{cases}
 \ell-1,& C_2y^2=C_1x^2\pmod\ell,\\
 -1,& C_2y^2\ne C_1x^2\pmod\ell.
 \end{cases}
\tag{R18}
\]

因此使这个**有理函数恒等为零**的局部退化模式位于
\(\ell\mid D\) 且 \(C_2y^2=C_1x^2\)，不能仅因 \(t=0\) 就称所有
剩余相位都消失。这是有理函数的退化分类，不声称小素数上有限采样
总有振荡（例如模 3 的双极点补集可能只有一个点）。
若 \(D\) 为非零小整数，碰撞素因子只来自 \(D\)。
模 2 的空支持由 (R17) 直接处理，无需排除。

令 \(\Omega_g=\{P\bmod g:(P(Px-Dz),g)=1\}\)，\(N_g=|\Omega_g|\)，
\(K_g=\sum_{P\in\Omega_g}e_g(\Phi_0(P))\)。CRT 给出上述局部完整和
的乘积。特别是 \(d=(g,D)\) 时

\[
 |K_g|\ll_\varepsilon g^{1/2+\varepsilon}d^{1/2}.
\tag{R19}
\]

这与已有共同核 Weil 的量级一致，**不是第二份可相乘的节省**。
若 \(N_g=0\)，该射线的实际支持为空。

## 6. 真正剩下的长素数估计已经可写在物理权重上

固定一条射线及 \(C_1=c_1,C_2=c_2\bmod g\)，将 (R15) 中同一剩余类
的全部原权重收集成（简写 \(W=W_{c_1,c_2}\)）

\[
 W(P)=\sum_{\substack{p\equiv P\ (g),\ p,q\text{ prime}\\
                       px-qy=Dz}}
       \mathfrak w(p,q)\mu(z)^2 L_p(y,z)\overline{L_q(x,z)}.
\tag{R20}
\]

原 dyadic 支持、\(p\ne q\)、掩码、平滑权及所有外标签都保留。
这不是两条无权素数计数函数。对 \(N_g>0\)，记
\(W_{\rm av}=N_g^{-1}\sum_{P\in\Omega_g}W(P)\)。精确恒等式是

\[
 \boxed{\sum_P W(P)e_g(\Phi_0(P))
 =W_{\rm av}K_g+
   \sum_P(W(P)-W_{\rm av})e_g(\Phi_0(P)).}
\tag{R21}
\]

第一项的局部完整相位已由 (R17)–(R19) 控制；第二项才是尚待证明的
**实际跨剩余类色散**。即便第一项逐射线有平方根界，其伸缩和、
射线数与外参数求和仍须纳入原能量账本，不能直接宣布全局覆盖。

单纯知道完整和小不够：取任意模型 \(W(P)=e_g(-\Phi_0(P))\)，则
左端为 \(N_g\)。这只反驳“任意权可免费继承完整和界”的推理，不是
物理 Möbius 权的反例。对实际 \(W\)，直接 Cauchy 仅给

\[
 \left|\sum_P(W(P)-W_{\rm av})e_g(\Phi_0(P))\right|
 \le\sqrt{N_g}\left(\sum_P|W(P)-W_{\rm av}|^2\right)^{1/2}.
\tag{R22}
\]

这正是用户要求避免先花掉的色散；本文没有把右端假设成小量。
同样，\(g\mid t\ne0\) 的格点稀疏性并不自动给原有符号和 \(g^{-1}\)
节省，因为 \(t=0\)、三个密度项及同一行能量归一化必须一起记账。

下一项具体数学任务是同时处理 (R7) 的原始 residual 与
(R20)–(R21) 的**联合**射线平均：从原 AFE/reflection 权证明主项
匹配，或在伸缩和尚未逐项取绝对值时证明长素数跨剩余类消去。
当前尚未获得原极端不平衡面要求的 \(T^{-1/4}\) 线性节省。

## 7. 支持反查：真正不平衡的双边子块可以没有整数零层

上文的分解不要求 \(R=0\) 真有贡献。现在直接从原整数变量的大小
检查它是否存在。设一个实际 dyadic 子块满足

\[
 \begin{gathered}
 P\le p\le2P,\quad Q\le q\le2Q,\quad
 M\le|m|\le2M,\quad N\le n\le2N,\\
 U\le|u|\le2U,\quad V\le v\le2V,\qquad |D|\le D_0.
 \end{gathered}
\tag{R23}
\]

\(m,u\) 可分别为正或负。三角不等式逐项给出

\[
 \boxed{|R|\ge PNU-8QMV-4D_0NV.}
\tag{R24}
\]

所以只要

\[
 \frac{PU}{V}>8\frac{QM}{N}+4D_0,
\tag{R25}
\]

整个子块的 \(\mathscr M_0\) 精确为零，**包括三个密度项**，不依赖
任何相位、Möbius 估计或 sparse 投影能量界。交换两侧可得反向版本。
必须是 (R23) 的双边实际支持，仅凭上界长度不能使用 (R24)。

旧 §9.175 在最大 ambient row 给出的指数是

\[
 P=T^2,\quad Q=T^{3/2},\quad M=U=T^5,\quad N=V=T^3.
\tag{R26}
\]

对确实满足这些双边 dyadic 支持的块，第一项为 \(T^{10}\)，第二项
至多 \(8T^{19/2}\)，第三项至多 \(4D_0T^6\)。例如明确给定
\(D_0\le T,T\ge100\)，就有

\[
 |R|\ge T^{10}(1-8T^{-1/2}-4T^{-3})>\tfrac18T^{10}.
\tag{R27}
\]

同样 \(|R|<9T^{10}\)。在双 incidence 上因此

\[
 \tfrac1{32}T^{13/2}<|t|<9T^{13/2}.
\tag{R28}
\]

若还 \(T\le g\le2T\)，全共同频率筛出的非零整数 \(t=gk\) 满足
\(T^{11/2}/64<|k|<9T^{11/2}\)。这定位了实际非零行列式区间，
不把一个长区间的整除条件误当成消去定理。

这里 \(T\ge100\) 只是采用 (R23)、(R26) 精确端点的算术例子，不是
原 AFE 的有效高度门槛。若原平滑支持有别的固定常数，应先保留这些
常数再用 (R24)；固定指数差仍使零层在足够大 \(T\) 时消失。若只有
长度上界、较低 \(m,u,n,v\) 子块、变换尾或依赖参数的支持常数，则须
逐块验证 (R25)，不能推广到整个物理包。

来源的双边支持可再追到主笔记 \(H\le|h|\le2H\)、
\(L\le|\delta|\le2L\) 及 §9.138 的 \(h\delta/(d_1d_2)\) lift：
固定 inactive cofactor 后是宽度因子 4 的乘积区间，可在仍保留
原 \(h,\delta\) 和的情况下分成倍二子块。§9.189 的 \(n=w\) 识别
保留原 G/Type 自变量。这里没有把 active 素模当作 lift 的长度。

**必须区分三件事：** 原短 determinant \(D\ne0\)、共同 Fourier
频率 \(\nu=0\)、以及新整数 \(R=0\) 不是同一个“零”。
(R27) 排除最后一个，并不排除第一个或第二个。单独的 \(\nu=0\)
仍含全部 \(R\ne0\) 四元组，不受 \(g\mid R\) 限制；该整除条件只有
恢复全部共同频率才出现。于是，在这些真正不平衡子块中，不能靠
“算掉 \(R=0\) 主项”补足 missing gain，仍须攻原物理非零行列式
上的跨剩余类色散。可比比率或不平衡的 lift 支持则仍可能有 (R7)
的 residual，另行保留，不能一刀切删除。

## 8. 有限检查与独立审查

[有限检查脚本](../../scripts/check_pre_cauchy_common_determinant.py) 的
25 项检查通过，并经过独立数学与文件级复核。根单位恒等式在
\(\mathbb Q[X]/\Phi_g(X)\) 中比较；唯一数值不等式检查只是小素数
Weil 界的 sanity check，解析输入仍来自已注明的标准定理。
检查覆盖原 CRT 行、共同相位、四个密度项、完整射线权重重组、
碰撞模数、signed 支集端点和三种“零”的区别。未运行 Lean。

## English summary

The common-frequency sum enforces divisibility of the single integer
\(R=pnu-qmv-Dnv\) by \(g\). This organizes all four active-centered terms,
including their density corrections. On double incidence, \(R=pqt\), so
the rank-one layer survives every common frequency coherently. Its residual
phase is independent of both dilation variables; after Type reassembly the
common primitive coordinate carries \(\mu(z)^2\), while two signed Möbius
dilation sums remain. Complete residue averaging of the ray phase reduces
exactly to a Kloosterman sum minus one, with explicit pole-collision modes
at primes dividing \(D\). Transferring this complete-sum cancellation to the
actual weighted long-prime family, and matching the entire residual with
the AFE/reflection main term, are still open. A two-sided support inequality
also excludes the integer-zero layer on genuinely unbalanced dyadic cells,
including the explicitly normalized top-scale example. This is not deletion
of the common Fourier zero frequency. No zero-free theorem is claimed.
