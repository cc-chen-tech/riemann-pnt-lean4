# MWKF-PHYS-v1：三条研究线共用的原式、归一化与适配边界

白话结论：本文件只冻结已经存在的物理对象，并给出一个可从原式逐项
筛出的 genuine-gcd 子族。它不新增参数覆盖，不把模型节省计入原问题。
跨 genuine gcd 的共同频率/共同系数适配仍需逐项证明；`dtf=1` 本身
不是证书。PR 的阶段性交付与完整 twisted-moment 定理必须分开。

## 1. 不随活动分支漂移的上游版本

版本名 **MWKF-PHYS-v1** 的定义来源固定在研究提交
`49cfacd70c60372757280177c7b63fd4f7760817`，不是后续移动的分支名。
下列公式号均指该提交中的文件；本文件只是索引、命名消歧及窄域筛选。

| 对象 | 固定源文件和公式 |
|---|---|
| 原积分、精确 AFE、原 Poisson 原子 | `2026-08-24-mobius-weighted-off-diagonal.md` (1.1), (2.0)–(2.7), (4.4)–(4.5) |
| 真实支持、无量纲核与外权 | 同文件 (5.1)–(5.15), (6.0) |
| Type 频率下降及全部 CRT 相位 | 同文件 §9.151, (9.1007)–(9.1014) |
| 共同频率的逆比率相位与短侧范数 | `2026-08-30-mwkf-common-phase-adapter.md` CG1–CG17 |
| 原整数格与完整 reflection | `2026-08-30-mwkf-physical-reflection-adapter.md` PA3–PA20 |
| canonical 零点、全部频率与共同算子 | `2026-08-30-mwkf-shifted-frequency-adapter.md` SF1–SF19 |
| 已证的指定物理 q 壳子族 | `2026-08-30-mwkf-physical-q-shell-coverage.md` PQ10–PQ13 |

跨任务不重新定义原 AFE 权。固定
\(e(x)=\exp(2\pi i x),s_t=1/2+it,\gamma(s)=\pi^{-s/2}\Gamma(s/2)\)，
\(G_t(z)=e^{z^2}(1-4z^2)(1-z^2/s_t^2)(1-z^2/(1-s_t)^2)\)，
\(g_t(z)=\gamma(s_t+z)\gamma(1-s_t+z)/(\gamma(s_t)\gamma(1-s_t))\)，
\(V_t(x)=(2\pi i)^{-1}\int_{(2)}G_t(z)g_t(z)x^{-z}dz/z\)。
这是两个对称 AFE 方向已经合计的版本，没有可再添加的第二个因子 2。
固定原 dyadic partition F、实权 W、及 SF/PA 使用的正则化 χ。

## 2. Literal 原子及目标：不得改用代理系数

为防止三个不同 gcd 共用字母，原 mollifier 指标写作 \(d_0,e_0\)，
\(q_0=(d_0,e_0),d_0=q_0r,e_0=q_0s\)；**本文件 q₀ 是原 gcd，
不是其他文件中 rad(q) 的缩写**。原 AFE 尺度写作 \(K_z,M_z\)，
\(h,\delta\) 是 (4.5) 的两个原标签，不是后续 Poisson 标签。

\[
 \begin{split}
 \mathscr K(r,s;\delta,h)
 &=\int_0^\infty
 {F_{M_z}(x)F_{K_z}((xr+\delta)/s)\over\sqrt{x(xr+\delta)/s}}
 e(-hx/s)\int W(t/T)V_t(x(xr+\delta)/s)
 e^{it\log(1+\delta/(xr))}\,dt\,dx,\\
 O_{q_0}&={2\over q_0}\sum_{(r,s)=1}
 {a_N(q_0r)a_N(q_0s)F_R(r)F_S(s)\over\sqrt{rs}\,s}
 \sum_{\delta\ne0,h\ne0}e(-h\delta\bar r/s)\mathscr K(r,s;\delta,h).
 \end{split} \tag{FP1}
\]

积分在 \(x>0,xr+\delta>0\) 外为零；所有原 mollifier 支持保留。
\(a_N(n)=\mu(n)(1-\log n/\log N)1_{n\le N}\)，非零项要求
\(q_0,r,s\) 平方自由且两两互素。外面原 \(\mu^2(q_0)\) 若不限制
q₀ 平方自由便必须显示。**以下 FP2–FP7 均只取平方自由 q₀**。
两个 Möbius 符号是 \(\mu(r)\mu(s)\)。

在一个 h/δ 光滑壳中，令 \(u=r/R,v=s/S,\alpha=\delta/L,\beta=h/H\)。
原 (5.13b) 的 **完整** \(\Psi^\circ(u,v,\alpha,\beta)\) 定义不变；
它保留精确 logarithm、原 V、W、F。将 \(F(u)F(v)u^{-1/2}v^{-3/2}\)
和选定 h/δ cutoff 乘进去得到 Ψ。于是严格为

\[
 O_{q_0;R,S,K_z,M_z,L,H}={2T\over q_0RS}\mathfrak S_{q_0}[\Psi],
 \quad
 \mathfrak S_{q_0}[\Psi]=\sum_{r,s,h,\delta}
 \mu(r)\mu(s)p_N(q_0r)p_N(q_0s)\Psi(u,v,\alpha,\beta)
 e(-h\delta\bar r/s),                                    \tag{FP2}
\]

其和域就是 (6.0)，包括 \(q_0r,q_0s\le N\)、\((r,s)=(q_0,rs)=1\)。
若记 normalized core \(\mathcal P=\mathfrak S/R\)，外权变成
\(2T/(q_0S)\)，不允许同时保留旧的 RS 分母。
局部充分预算为 \(|\mathfrak S|\ll RS T^\varepsilon\)，即
\(|\mathcal P|\ll S T^\varepsilon\)；全问题还需同一预算下的实际外层
重组和未估计物理尾。更弱的全局目标是直接估计原有符号和与余项，
不要求每块分别达标。

对实际原 mollifier 向量，最终目标是
\(|a^*(H-L_{\rm LCM})a|\ll T^{1+\varepsilon}\)。这不等价于对所有
向量的通用算子范数界。只有在指定输入空间、实际权重和行范数后，
才能提出更强的充分 norm gate；本文件不把通用 norm gate 当作已证。

## 3. 非空尺度及统一实光滑预算

一般 core 必须满足原 (5.3)–(5.10)，特别是
\(q_0R/2,q_0S/2\le N\)、\(K_zM_z\lesssim T\log^B(2T)\)、
\(K_zS/(M_zR)\in[1/16,16]\)、
\(1\le L\lesssim M_zR/T\)、\(1\le H\lesssim S/M_z\)，最后两式
可带原已登记的 log 窗口。仅给指数可行点不保证某个任意选定权非零。

一个没有 mollifier 截断角点的内部族是 PQ10：
\(q_0\in[Q_0,2Q_0),R=S=N/(8Q_0),K_z\asymp M_z\asymp T^u\)，
\(H\asymp S/T^u,L\asymp RT^{u-1},0\le u\le1/2\)。
此时 \(q_0r,q_0s\le N/2\)，实际核参数
\(T\lambda_0\asymp1,\omega_0\asymp1,\chi_0\lesssim1\)。
对固定 J 定义 \(\mathcal A_J=\max_{|\mathbf j|\le J}
\|\partial^{\mathbf j}\Psi\|_\infty\)。此内部族有一致的
\(\mathcal A_J\ll_{J,W,F}1\)；加入平滑内部 taper 也保持该预算。
更大的 log core 必须支付原 (5.14) 的半范数，不能免费称为固定常数。
若分离四变量，仅允许在固定紧集上使用由足够高阶 \(\mathcal A_J\)
控制的 Fourier/Mellin L¹ 系数预算；算术逆元相位不属于此实光滑预算。

### 3.1 可逐项提取的 genuine-gcd 子族（不是新覆盖）

固定平方自由整数 \(Q_*>1\)，限制 \((q_0,Q_*)=1\)。在 FP2 中选择

\[
 s=eQ_*,\quad r=n,\quad h=eu,\quad\delta=ev,
 \quad e\text{ 平方自由},\quad(e,q_0Q_*)=1,
 \quad(n,q_0eQ_*)=(uv,Q_*)=1.                         \tag{FP3}
\]

这里 e 是新的 genuine-gcd 指标，不是原 mollifier 指标 e₀。
那么 \((|h\delta|,s)=e\)，约化模数恰为固定的 Q*，且逐项有

\[
 e(-h\delta\bar n/s)=e_{Q_*}(-euv\bar n),\qquad
 \mu(n)\mu(eQ_*)=\mu(Q_*)\mu(e)\mu(n).                 \tag{FP4}
\]

所以该子族原始系数完整为
\(\mu(Q_*)\mu(e)\mu(n)p_N(q_0n)p_N(q_0eQ_*)\)，外权仍为
\(2T/(q_0RS)\)，实权恰为
\(\Psi(n/R,eQ_*/S,ev/L,eu/H)\)。e≈E₀、Q*≈S/E₀ 时，
u≈H/E₀、v≈L/E₀；归一化变量代换只由固定有界比例组成，故保留
§3 的四变量半范数预算。所有整数端点取原支持的交集，无额外半权。
\((e,n)=1\) 不许删除：其容斥 \(\sum_{f\mid(e,n)}\mu(f)\)
会产生 n=fm；没有额外论证便不能将这些不同 f 的 n 系数称作同一列。

真实整数见证：T=64,N=T³,q₀=1,R=S=N/8=32768,Kz=Mz=8,
H=L=4096,Q*=6007，取 e=5,7，n=30011，u=v=850。
则 s=30035,42049；h=δ=4250,5950；均落在原 [H,2H]、[L,2L] 壳中，
所有互素条件及 genuine gcd=e 成立，原连续 x=8 时
\((xn+\delta)/s\in[4,16]\)。这证实域非空，不宣称任意 W/F
在该点的积分必不为零，也不宣称一个渐近正密度定理。

FP3 确实给出随 genuine e 变化但约化 Q* 不变的族。它尚不是
另一个任务要求的完整共同-g、共同-n 系数的 paired operator：
真实单位掩码、Type 变换系数、外层及 principal/反射分账仍须同步映射。
FP4 的模逆元比率也不等于把实数 euv/n 直接代入一个自由选择的周期函数。

**与 signed overlap 的容斥分项不同。** FP3 是原式的真实 d=e 层，
其系数是 µ(e)，不能改成 µ²(e)。逐素数有
\(-1_{p\mid h\delta}=-1_{p\mid h}-1_{p\mid\delta}
+1_{p\mid h,\ p\mid\delta}\)。两边同时整除时，三个项
−1−1+1 才合成 −1。下游 O2 的正交叠项来自第三个容斥项，
不是 FP3 子族自身；若要使用该项的无符号平方自由 e 界，必须同时
映射另外两个项、每素数的全部分配掩码及原外权，不能仅挑出正项。

### 3.2 该子族的实际 Type residue packet：额外依赖在哪里

在固定 e,u,v,Q* 后，缩写原平滑/taper 权为
\(w_{e,u,v}(n)=p_N(q_0n)\Psi(n/R,eQ_*/S,ev/L,eu/H)\)。
把 e 侧外系数暂留在外，(9.994) 所需的 literal residue packet 可以取
如下形式；所有 n 及后面的 fm 都继承 FP2 的正整数和 \(q_0n\le N\)
支持，w 在该支持外置零（在 §3 内部箱里截断不触及光滑支持）：

\[
 \begin{split}
 G_{e,u,v;Q_*}(w)&=\sum_{n\equiv w\ (Q_*)\atop(n,q_0e)=1}
                   \mu(n)w_{e,u,v}(n),\quad w\in U(Q_*),\\
 \widehat G_{e,u,v;Q_*}(k)&=
 \sum_{(n,q_0eQ_*)=1}\mu(n)w_{e,u,v}(n)e_{Q_*}(-kn).
 \end{split}                                                   \tag{FP6}
\]

此处没有额外的 e 逆元可凭空加入。已有 e 依赖恰是实际联合光滑权
和单位掩码 \((n,e)=1\)。四变量平滑分离可令每个固定分离 atom 的
n 光滑因子共同，却不会消除单位掩码。对平方自由 e 的精确容斥给

\[
 \widehat G_{e,u,v;Q_*}(k)
 =\sum_{f\mid e}\mu(f)^2
   \sum_{(m,fq_0Q_*)=1}\mu(m)w_{e,u,v}(fm)e_{Q_*}(-kfm).
                                                               \tag{FP7}
\]

\(\mu(f)^2\) 来自容斥符号与 \(\mu(fm)\) 的乘积，不能留成一个
未经核对的单 \(\mu(f)\)。实际周期因子因而是 \(e_{Q_*}(-kfm)\)，
另有 \((m,f)=1\)、fm 支持和各 f 的归一化权。若固定 f 再估计，必须
把所有 f 的费用和 signed e 外和重新放回；这里没有完成该联合估计。

此外，(9.997) 的 n 是 **完成后的模 q 列标签**，不是 FP6 的原
Möbius 整数 n。为区分，将其改名 ξ：本子族每个 A=euv 的贡献进入
\(\xi\equiv-euvk\pmod{Q_*}\) 这一列。固定 Q*,k 并不固定此列。
这解释了为何保留 (e,u,v,k) 的未合并形式是必要的；不能先以 ξ 合并，
再把 \(b_{Q_*}(\xi)\) 声称为不依赖 e 的原 Möbius 系数。
FP6/FP7 对本子族精确，不自动认证完整反射/共同-g 成对算子。

## 4. dtf=1 的有效结论与不能推出的结论

原 §9.151 的 qᵢ 是进入 Type completion 的平方自由模数。另记
\(d_{{\rm tf},i}=(k_i,q_i),Q_i=q_i/d_{{\rm tf},i},K_i=k_i/d_{{\rm tf},i}\)。
其精确相位系数为

\[
 C_1=-K_1\overline{d_{{\rm tf},1}}\pmod{Q_1},\qquad
 C_2= K_2\overline{d_{{\rm tf},2}}\pmod{Q_2}.             \tag{FP5}
\]

还有 (9.1013) 的 inactive traces η₁−η₂、(9.1014) 的共同-g trace
及 cofactor reciprocity 相位。它们必须一起保留。固定 Qᵢ、dtfᵢ、
Kᵢ 后，FP5 当然不依赖 e；dtfᵢ=1 且固定 kᵢ 是其中一个子区。
FP3 提供固定约化模数的原式子族，但单独固定 dtfᵢ=1 并未固定
qᵢ、Qᵢ、g=(Q₁,Q₂)、cofactor 和 Type amplitude。

两个有限障碍：

- 固定 ambient v=105 而 genuine d=3 或 5，会得到约化模数 35 或21；
  与另一行 Q₂=15 配对时，共同 g 分别是5或3。即便两边 dtf=1、k=1，
  共同频率空间本身也已经改变，不能使用一个未变的 f_gc。
- 即便固定 Q=5、K=1，dtf=2 与3 给左 C 分别为2与3 mod5。
  因此 genuine 层若令 dtf 改变，公共相位常数也会改变。

固定 CG3 的 g,p,C,ν 后，其完整行相位确实是
\(e_g(-C\bar p\,n\bar m+\nu\bar p\,m\bar n)\)，
\(m=h\delta\)。代换为一个 ratio 变量只认证该有限行内的代数。
跨 genuine e 的共同 \(f_{gc},s_{gc}\)、共同 n 系数及统一四变量实权
需要上述数据都在同一族中固定或付费重组；目前不提供这一全套证书。
因此 469/40、489/40 与 \(\min(E,\sqrt E q'^{1/4})\) 只保留为下游
模型账本，不能在 FP2 上记录净节省。

## 5. 主角色、零 Gram、reflection：只分一次账

原 AFE 对角是 \(m_1s=m_2r\)，SF 的等频带是 \(m_1=m_2\)，
mollifier 对角是 \(d_0=e_0\)，三者不同。SF7 的删轴为
\(P-H_0-D_0+O_0\)；加回原零频与 AFE 对角才恢复 P。
PA8 的延拓补偿不能删除。canonical 零点只在固定 χ 后定义。

在原 a 向量上，以 SF8 的实际 A(j,k) 定义 SF16 的矩阵，严格为
\(R=H-L_{\rm LCM}=G_\chi+J_\chi=K_{\rm eq}+K_{\ne}-L_{\rm LCM}\)。
\(K_{\rm eq}\) 权为 \(W(t/T)(\lambda(t)+2\gamma+E_{\rm eq}(t))\)，
保留 logT，不因补齐 k≠0 自动消失。令 E=Keq−LLCM、C=Kne，
只能对同一总核使用 \(RR^*=EE^*+EC^*+CE^*+CC^*\)。
若再中心化 C，必须把低秩边际保留在 E 中。

Ramanujan principal 是平均逆相位的常数角色；它不是 canonical 双零
频率点，也不是下游另一个可再次减去的次主项。FP3 的固定 Q* 行中
\((euv,Q_*)=1\)，该平均为 \(\mu(Q_*)/\varphi(Q_*)\)；完整行等于
此密度加中心化逆相位，两个部分仍用同一 e,n,u,v 权。

reflection 必须按 PA3 恢复全部整数格后，在共同 x,y≤X 和全部
Mellin z 上使用 PA13 的 FF−FR−RF+RR；没有逐频率的整数反射。
严格端点 D>N、kN<x 保留。SF11 频率尾为
\(O(NT^{2a+2}Y^{1-a})\)，PA15 组合反射尾为
\(O(T^3N^{5/2}X^{-3/2})\)；Y=⌈T⁴⌉、a≥(B+9)/2、
X≥T^{7+2B/3} 足以给 O(T⁻ᴮ)。这些不证明原 log-core 尾已达标。

## 6. 本轮交付与验收

本文件新增覆盖 **无**，净幂次节省 **0**。已存在的真实子族覆盖只按
PQ12/PQ13 登记，未覆盖的 q/尺度、长 b、大 e、principal/零 Gram、
完整 mixed 能量及物理尾仍开放。下一轮算术估计应输出同一 FP2 原子
上的区域、完整聚合成本和净 saving；有限恒等式或模型大筛不单独计数。

本线维护 FP1/FP2/SF/PA 的上游适配；“大于2/3没有零点”任务只攻击
该上游认证范围内的共同频率 gcd 重叠；14/17 线复用同一归一化并
显式登记其零点应用所需的额外输入。局部 PR 合并不推出任一全局定理。
