# 全 B 重组后的短区间输入：真实亚幂次衰减，不是 gate 覆盖

白话结论：全 B 重组后，已发表的 Möbius 短区间定理可以作用于实际光滑核，而不是只在一个示意模型里比较长度。原 (B,q)=1 条件可统一保留。不过，恢复全部外层后只获得亚幂次衰减；平衡顶层仍是 T^{5−o(1)} 的上界，目标是 T³。本篇不增加 coupled-kernel 覆盖，不另设一个“已完成”的较小目标。

记号与范围取自 [GB](2026-08-30-mwkf-global-b-boundary.md)、[PQ](2026-08-30-mwkf-physical-q-shell-coverage.md)：

\[
 \alpha=R/S,\quad X=R/K,\quad P=K_{\min}K_{\max},\quad
 Z=RP/S,\quad J=Z/K,\quad F=ZX/S,\quad C=HL/R.                \tag{SR1}
\]

仍要求实际 M>1、Z 和 K/α 有固定正幂余量，全部尺度及 q 为 T 的固定幂。只在原 mollifier 的内部光滑箱工作；零斜率、κ=e=1、硬端点、canonical 零 Gram、reflection 两个 mixed 项和独立物理尾不被删除。本篇的 χ 不新增到 GB 的 bare symbol。

## 1. 哪些论文输入真正适用

以下均核对原论文或原作者研究论文的明确陈述，不使用已撤回的 arXiv:2601.00292。

| 输入 | 明确长度与输出 | 对当前余项的意义 |
|---|---|---|
| [Matomäki–Teräväinen, Theorem 1.1](https://arxiv.org/html/1911.09076v2#S1.Thmtheorem1.1) | H≥x^θ，θ>11/20；输出 H(log x)^{−1/3+ε} | 长度可满足，但不是固定幂次节省；不能吸收任意 polylog 核范数后仍宣称相对节省 |
| [Motohashi 的短区间定理](https://www.jstage.jst.go.jp/article/pjab1945/52/9/52_9_477/_pdf)；[Matomäki–Teräväinen §2.1 所列经典定量版本](https://arxiv.org/html/1911.09076v2#S2.SS1) | θ>7/12 时 H exp[−c(log x/log log x)^{1/3}] | 本篇使用的输入；比任意 log 幂强，但仍不是 x^{-δ} |
| [Pascadi, Theorems 1.1–1.2](https://arxiv.org/html/2511.08445v2#S1.SS2)、[Blomer–Pascadi](https://arxiv.org/html/2607.24311v1) | 固定模数的 Kloosterman 双线性形式 | GB7 不是该核；全外层相关的系数转换和联合估计仍缺，不能直接填入覆盖表 |

经典定量式下面简称 MR（Motohashi–Ramachandra），不是 Matomäki–Radziwiłł 定理。固定 7/12<θ≤1，并取 x 充分大，令

\[
 E_c(x)=\exp[-c(\log x/\log\log x)^{1/3}],\qquad
 \sum_{x<n\le x+H}\mu(n)\ll_\theta H E_c(x)
 \quad(x^\theta\le H\le x).                                \tag{SR2}
\]

## 2. 随 q 变化的单位掩码：不能免费删除，也不需要逐字符估计

对任意正整数 q，令 S(q) 为所有素因子均整除 q 的正整数集合（包含1）。逐素因子有精确有限恒等式

\[
 \mu(n)\mathbf1_{(n,q)=1}=\sum_{d\mid n,\ d\in S(q)}\mu(n/d).
                                                               \tag{SR3}
\]

d 必须包括 q 的素数幂，不仅是 d|q。仓库既有 `restricted_smooth_ledger` 已检验此式。现在证明：对任意固定 7/12<θ≤1、C₀>0，SR2 可统一提升为

\[
 \sum_{x<n\le x+H\atop(n,q)=1}\mu(n)
 \ll_{\theta,C_0} H E_{c'}(x),\qquad q\le x^{C_0},\quad
 x^\theta\le H\le x,                                      \tag{SR4}
\]

其中 c′>0 固定，允许比 SR2 的 c 小。

**小 d。** 取 7/12<θ₀<θ，以及固定 0<δ<(θ−θ₀)/(1−θ₀)，令 D=x^δ。由 SR3，d≤D 的内和是 (x/d,(x+H)/d] 上的 μ 和。因为 H/d≥(x/d)^θ₀ 且 log(x/d)≈log x，SR2 给 HE_{c₁}(x)/d。全部小 d 的调和质量≤∏p|q(1−1/p)^{-1}≪(log x)^4，一致于 q≤x^{C₀}。这个粗 polylog 界也可初等得到：把 p 分在 p≤(log x)² 与其补集，前者用调和和，后者用 ω(q)≤log q/log2。故仍为 HE_{c₂}(x)。

**大 d 及整数 +1。** 对每个固定 0<a<1，

\[
 P_a(q):=\prod_{p\mid q}(1-p^{-a})^{-1}=x^{o(1)}
 \quad(q\le x^{C_0}),                                     \tag{SR5}
\]

且这个 o(1) 一致。证明：在 p≤log x 上用所有整数的 p^{-a} 和，在 p>log x 上用 ω(q)≪log x，得到 log P_a(q)≪a,C₀ (log x)^{1−a}=o(log x)。因此

\[
 \begin{split}
 \sum_{d>D,\ d\in S(q)}H/d&\le H D^{-1/2}P_{1/2}(q),\\
 \#\{d\le2x:d\in S(q)\}&\le(2x)^a P_a(q).
 \end{split}                                               \tag{SR6}
\]

用内和的字面计数≤H/d+1，取 a=θ/2，全部大 d 至多
H x^{−δ/2+o(1)}+x^{θ/2+o(1)}=o(HE_{c₂}(x))。这明确支付了每个 d 的 +1，也包括 x<d≤x+H 的商为1端点。无 Perron 半权或遗漏尾，SR4 得证。

## 3. 两个真实短窗口，不是两次可乘的 saving

在 GB7 恢复完整 B 后，固定 M,j,k,l，裸核的 Fourier 自变量为

\[
 \xi=F(kl/j-B/M),\qquad B_0=Mkl/j\asymp S.
\]

它的 B 窗口宽度与反向 M 窗口宽度分别是

\[
 H_B=M/F\asymp S/Z,\qquad H_M=X/Z.                         \tag{SR7}
\]

第二式来自 |∂M ξ|=FB/M²≈Z/X；第一式**不依赖 K**，不能在非顶层直接把窗口宽度写成 X。保持全部外层，定义

\[
 A_4=\sup_{M,j,k,l}\sum_{r=0}^1\sup_y
      (1+|y|)^4|\partial_y^r\widehat\Psi^0_{M,j,k,l}(y)|.
                                                               \tag{SR8}
\]

这是实际 GB/JT symbol 的 Schwartz 范数，不是任意供应系数。固定的 v(B/S) 截断成本也并入 A₄。若 S/Z≥S^{7/12+η}，η>0 固定，则 SR4 和一维 Abel 求和给

\[
 \sum_{B\ge1,(B,q)=1}\mu(B)v(B/S)
          \widehat\Psi^0\bigl(F(kl/j-B/M)\bigr)
 \ll A_4\,{M\over F}\,E_c(S).                             \tag{SR9}
\]

证明的端点与远窗细节：先把 |B−B₀| 按 H_B、2H_B、4H_B,… 分壳，与支撑 [S/4,4S] 相交，并拆成固定个数的半开区间使各自长度不超过左端点。长度低于 S^{θ₀} 的 Abel 前缀用平凡计数，θ₀ 取在 7/12 与 7/12+η 之间，故被 H_BE_c(S) 吸收；较长前缀用 SR4（必要时略缩 θ₀ 以支付固定尺度常数）。第 v 壳的长度至多 O(2^v H_B)，权上界为 O(A₄2^{-4v})；SR8 只给总变差 O(A₄2^{-3v})，因为 y 区间长度为 O(2^v)。故长前缀的整壳贡献为 O(A₄H_BE_c(S)2^{-2v})，短前缀贡献至多 O(A₄S^{θ₀}2^{-3v})，都可求和。硬半开整数端点按 Abel 的两端值保留；不把一条短前缀错误地当作满足 SR4。

恢复 GB7 的系数后，M/F 与 F/|j|、1/M 精确消去；Σ|j|≈J 1/|j|≪1，#(k,l)≪P，#M≈X。因此

\[
 \boxed{|\mathcal P_{K,q,\mathrm{crit}}|
   \ll A_4 CPX E_c(S)+|\mathcal E_{\rm bare}|+|\mathcal E_{\rm end}|.}
                                                               \tag{SR10}
\]

两项原误差仍用 GB4/GB6，并可选足够高的固定衰减阶。到 SR9 以前两边 Möbius 和真实 hδ 核一直保留；最后这条上界付掉外侧 μ(M)，所以不再拥有一次独立的 M 抵消。不能把 SR9 与对反向窗口的单行界直接相乘。

如果只知道 A₄≪ε T^ε，SR10 就必须保留该范数，不能宣称相对亚幂次改善。以下 PQ10 的内部箱满足 Tλ₀≈1、ω₀≈1、χ₀≲1，固定阶原核导数一致受控；紧支撑 Fourier 变换及 JT3–JT4 的精确 symbol 保持此控制（或至多固定 log 幂）。故在这些箱中 A₄ 的成本被 E_c(S) 吸收。此结论**不推广到任意 power-enlarged upper-bound core**。

具体地，在原 (5.13b) 上逐项微分时，精确 logarithm 的导数只花有界的 Tλ₀，另外两个相位/AFE 比率由 ω₀、χ₀ 控制；内部 mollifier 的归一化正阶导数为 O(1/log N)。随后两个紧支撑 Fourier 坐标在 PQ10 的自然尺度上保持有界。JT4 中 η、σ 属于固定紧集，Λ≥1；其积分以 (1+|u|)^{-L} 一致主控，对 u/Λ 的微分不带 Λ 正幂。得到有限阶 Ψ⁰ 导数范数后，在它的固定紧支撑上分部积分，便给 SR8 的 A₄。这里没有从任意小正幂界偷换为对数幂界。

## 4. 原 q 壳与未覆盖的顶层窗口

在 PQ10 的非空内部族，q≈Q=T^γ、R=S=N/(8Q)≈T^{3−γ}、P≈Z≈T、K≈T^ν，0<ν≤1。于是

\[
 X\asymp T^{3-\gamma-\nu},\quad
 H_B\asymp T^{2-\gamma},\quad
 H_M\asymp T^{2-\gamma-\nu}.                               \tag{SR11}
\]

MR 对 B 行的固定余量条件等价于 γ<3/5；对反向 M 行则要求 γ+ν<3/5。若只比较 Matomäki–Teräväinen Theorem 1.1 的长度门槛，两者分别是 γ<7/9 和 γ+ν<7/9；这仅为输入长度条件，不是任何 gate 覆盖。

在 γ<3/5 的族，CP≈S，由 SR10 并按原乘数 2T/(qS) 恢复物理外层，

\[
 \sum_{Q\le q<2Q}\mu^2(q)
 \left|{2T\over qS}\mathcal P_{K,q,\mathrm{crit}}\right|
 \ll T^{4-\gamma-\nu}E_c(T)+O(T^{-A}).                     \tag{SR12}
\]

这里用 ΣQ≤q<2Q 1/q≤1，保留了整个 q 壳；并未把 1/q 再当作另一个 Q^{-1} saving。K 是固定 dyadic 族，未额外把所有 K 的数量/最大尺度视为免费。

特别是 γ=0、ν=1：normalized 界为 T⁵E_c(T)，物理界为 T³E_c(T)，各自目标是 T³、T。E_c(T)=T^{-o(1)}，故缺失的固定两次幂**没有减少**。此时 M≈T²、H_M≈T，反向单行长度恰为平方根；上述两项已发表短区间定理都不能控制它到所需尺度。

本轮完成的是已有文献到真实核的受限转移及外层账本。它不改动 PQ 已覆盖区域，不估计全部 q、κ 端点或统一零/非零 signed operator。下一步仍须联合处理外层参数与两边 Möbius，不能继续靠分别估计这些短行来支付 T²。没有证明完整 coupled-kernel gate 或 twisted moment。

验证：本轮可运行 Python 套件 1434 passed、1 skipped；缺少 Flint 的 `test_weil_interval_auxiliary.py` 与 `test_weil_interval_ccm.py` 两模块明确排除。独立数学复核确认 SR4 的单位掩码转移、SR9 的真实核范数及 SR12 的物理指数，并修正了 Abel 壳总变差的指数。未新增或修改 Lean/Python 实现；已有有限检查不替代 SR2 的已发表解析输入或完整 twisted-moment 证明。
