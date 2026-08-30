# 从固定直线二阶矩到统一高高度排除：条件转移与旧账本复核

通俗地说：本笔记证明了一个“如果误差真的足够小，那么零点不能出现”的
分析转移引理。它减少了原路线需要证明的输入，但**没有证明误差足够小**。
旧笔记的 `7/289` 仍只是条件性指数模型的余量，不能据此宣布最终高高度
`14/17` 定理成立。本次不修改 Lean，也不把数值检查作为解析证明。

## 1. 旧结果中哪些可以使用

已重新读取以下两个独立 worktree 中的实际文件，而非只依赖分支名称：

- `prove-14-over-17-math-20260824` 的
  `docs/research/2026-08-24-reciprocal-lcm-dual-zero-amplifier.md`，
  尤其 §§206–208、269、318–319。
- `prove-eventual-14-over-17-20260826` 的
  `docs/research/2026-08-26-eventual-14-over-17-mwkf-proof-audit.md`，
  尤其 §§0–5、23.5、108。

这些旧研究稿未被修改。当前笔记及核算脚本构成可独立阅读的检查点；
下文的数学证明不需要访问未提交的旧文件。

### 1.1 `7/289` 是什么

旧 §208 取

\[
 \sigma=14/17,\quad\theta=30/17,\quad w=13/34,
 \quad m=\theta(2\sigma-1)-1=41/289.
\]

记

\[
 q_0=551/578,\quad q_f=47/34,\quad
 \kappa=w-\Delta,\quad x=q-w-\Delta,
\]

并在紧多面体

\[
 q_0\le q\le q_f,\quad
 0\le\Delta\le\min(w,q_f-q),\quad 0\le\tau\le x
 \tag{1}
\]

上定义纯代数模型

\[
 \begin{split}
 p&=\min(2\kappa,q+2\kappa-2\tau),\\
 r&=\min(\tau,q+\kappa-\tau),\qquad s=\max(p,r),\\
 d(q)&=\min(2q-\theta,\theta-1)-m.
 \end{split}
\]

该模型的中心项和混合项最小值分别是

\[
 \min(s+\Delta-d)=7/289,\qquad
 \min\left((s+\Delta)/2+(2q-\theta)/2-d\right)=24/289.
 \tag{2}
\]

两者均在 \((q,\Delta,\tau)=(43/34,2/17,0)\) 取到。
另有独立外边界模型

\[
 (2\sigma-1)-2(1-\sigma)\theta=7/289. \tag{3}
\]

附带脚本以有理数枚举四个二分选择产生的全部 16 个线性区域、各区域的
顶点并核对 (2)。紧多面体上仿射函数的最小值在顶点取得；分支相等时允许
重复归属，因此这不是只检查离散网格。它复核的是模型，不是把实际算术包
放入模型所需的估计。

### 1.2 为什么不能只补常数

旧 §319 已撤回 §318 的完整探测器组装结论：在低系数抵消前分开取范数，
会把本应抵消的低端对角重新计入。若 \(D=N/T\)，错误对角与目标对角之比为

\[
 \frac{T D^{1-2\sigma}}{T N^{1-2\sigma}}
 =(N/D)^{2\sigma-1}=T^{2\sigma-1}. \tag{4}
\]

在 `14/17` 线上它是 \(T^{11/17}\)，不是可并入常数的损失。
有限系数投影必须在第一次范数之前完成，而且投影后的耦合截断需重新估计。
§319 本身讨论的 `41/50` 例子对应 \(T^{16/25}\)；(4) 是同一代数障碍的
一般形式，不声称两个参数下所有包的分析都相同。

后来独立审计还记录了错误 cusp 适配、原模数三变量 shear 预算不足及
共同有限重组的开放项。它们不是同一条估计，也不能把一条路线的余量用于
支付另一条路线的缺口。特别是不能把错误适配的修正称为对 (2) 的反例：
(2) 的有理数计算正确，未证明的是它与完整物理二阶矩的联系。

## 2. 固定直线转移定理

固定 \(1/2<\sigma<1\)、\(\theta>0\)。对每个足够大的 dyadic
\(T\)，在整个本节中固定同一个整数 \(N=\lfloor T^\theta\rfloor\)，令

\[
 M_N(s)=\sum_{n\le N}\mu(n)n^{-s},\qquad
 E_N(s)=\zeta(s)M_N(s)-1,
\]

\[
 I_\sigma(T)=\int_{T/2}^{5T/2}|E_N(\sigma+it)|^2\,dt. \tag{5}
\]

**条件转移定理。** 若

\[
 I_\sigma(T)=o(1/\log T), \tag{6}
\]

则存在单个有限 \(T_0\)，对每个非平凡零点
\(\rho=\beta+i\gamma\)，有

\[
 |\gamma|\ge T_0\quad\Longrightarrow\quad\beta<\sigma. \tag{7}
\]

特别地，存在固定常数 \(C>0,\delta>0,B\ge0\) 使

\[
 I_\sigma(T)\le C T^{-\delta}(\log T)^B \tag{8}
\]

足以推出 (7)。若原对数幂为负数，可放宽为 \(B=0\)。这里要求的是
**未除以 \(T\) 的积分**；\(I_\sigma(T)/T=o(1)\) 不够。
只在某个依赖目标零点的高度以后成立、或只对每个固定正实部间隙分别成立
的估计，也不是本定理的输入。

### 2.1 消极点与统一多项式界

设 \(a_0=\sigma/2\)、\(d=\sigma-a_0\)、\(\ell=\log T\)、
\(H=T/\ell\)，固定任意 \(\gamma\in[T,2T]\)。定义

\[
 Q(s)=\frac{s-1}{s+1},\qquad
 F_\gamma(s)=Q(s)E_N(s)
       \exp\left(\frac{(s-i\gamma)^2}{H^2}\right). \tag{9}
\]

在 \(s=1\) 取可去延拓；其值为
\(M_N(1)\exp((1-i\gamma)^2/H^2)/2\)。因此 \(F_\gamma\) 在
\(\Re s>0\) 全纯。没有沿未知零点移动 \(1/\zeta\) 的积分线。

由 Euler 积分

\[
 \zeta(s)=\frac{s}{s-1}
   -s\int_1^\infty\{u\}u^{-s-1}\,du\quad(\Re s>0)
 \tag{10}
\]

得 \(|Q(s)\zeta(s)|\le1+|s|/\Re s\)。这个公式也见
[NIST DLMF 25.2.8](https://dlmf.nist.gov/25.2#E8)。
对 \(x\in[a_0,2]\)，\(|Q(x+it)|\le1\)，且

\[
 |Q(x+it)E_N(x+it)|
 \le C_0 N^{1-a_0}(1+|t|),\quad
 C_0=\left(1+\frac2{a_0}\right)
       \left(1+\frac1{1-a_0}\right)+1. \tag{11}
\]

这里仅使用 \(|\mu(n)|\le1\)、
\(\sum_{n\le N}n^{-a_0}\le1+N^{1-a_0}/(1-a_0)\)。
高斯因子的模平方为
\(\exp(2x^2/H^2-2(t-\gamma)^2/H^2)\)，故全直线积分

\[
 J(x)=\int_\mathbb R|F_\gamma(x+it)|^2dt
\]

在固定条带中收敛。设

\[
 A=3+2\theta(1-a_0),\quad
 C_L=19\sqrt{\pi/2}\,e^8 C_0^2,\quad
 C_G=19\sqrt\pi\,e^8 C_0^2.
\]

当 \(T\ge e^2\) 时，\(H\ge1\)，并有

\[
 J(a_0)\le C_L T^A. \tag{12}
\]

例如用 \((1+|t|)^2\le2(1+\gamma)^2+2(t-\gamma)^2\) 积分，得到
\(\sqrt{\pi/2}H[2(1+\gamma)^2+H^2/2]\le19\sqrt{\pi/2}HT^2\)。
因此 (12) 甚至可以多保留一个 \(1/\log T\)，但下文不需要。

### 2.2 固定线外的尾项不需要算术输入

在 (5) 的区间外，\(|t-\gamma|\ge T/2\)。将高斯分成两个因子，得到

\[
 J(\sigma)\le 2I_\sigma(T)
       + C_G T^A e^{-\ell^2/4}=:\mathcal Q_T. \tag{13}
\]

常数统一于所有 \(\gamma\in[T,2T]\)。尾项小于任意固定负幂；
这里没有对区间外的其他高度使用不同长度的 mollifier。

### 2.3 全直线 \(L^2\) 对数凸性

对 \(a=(1-\alpha)\sigma+\alpha a_0\)、\(0\le\alpha\le1\)，有

\[
 J(a)\le J(a_0)^\alpha J(\sigma)^{1-\alpha}. \tag{14}
\]

为明确其适用性，采用酉 Fourier 变换
\(\widehat F_x(u)=(2\pi)^{-1/2}\int F_\gamma(x+it)e^{-iut}dt\)。
Cauchy–Riemann 方程和分部积分给出
\(\partial_x\widehat F_x=u\widehat F_x\)，从而

\[
 \widehat F_x(u)=e^{u(x-a_0)}\widehat F_{a_0}(u).
\]

高斯与 (11) 保证快速衰减；导数的同类界可在稍宽的正实部条带内由
Cauchy 估计获得，所以微分与积分交换合法。对该表达式用 Plancherel 和
Hölder 即得 (14)。这不是依赖未证明谱正性的插值。

高斯消极点权与该类积分凸性是经典工具；参见 Kadiri–Lumley–Ng 的
[式 (2.16) 与 Lemma 4.4](https://www.cs.uleth.ca/~kadiri/articles/Explicit-zero-density-for-the-Riemann-zeta-function-JMAA-May2018.pdf)。
本节给出本任务所需的平移高斯、局部输入和统一端点版本，不宣称发明新的
凸性定理，也不把那篇论文的零点密度估计当作 (6) 或 (8)。

### 2.4 条带点值上界与零点的确定下界

在右边界 \(\Re s=2\)，绝对收敛给出精确恒等式

\[
 E_N(s)=-\zeta(s)\sum_{n>N}\mu(n)n^{-s},\qquad
 \sup_t|F_\gamma(2+it)|^2
 \le e^{8/H^2}\zeta(2)^2/N^2=:\mathcal R_T. \tag{15}
\]

取 \(a<\beta<2\)、\(L=2-a\)、\(r=\beta-a\)。左边界 Poisson 核为

\[
 P_{L,r}(v)=\frac{\sin(\pi r/L)}
 {2L[\cosh(\pi v/L)-\cos(\pi r/L)]}.
\]

它非负，且

\[
 \sup_vP_{L,r}(v)=\frac1{2L}\cot\frac{\pi r}{2L}
 \le\frac1{\pi r}. \tag{16}
\]

用此核延拓左边界数据，再加常数 \(\mathcal R_T\)，即为
\(|F_\gamma|^2\) 的调和上界。对有限矩形先用次调和最大值原理，再令
上下边趋于无穷；固定 \(T,\gamma\) 时高斯消除了水平边贡献。因此

\[
 |F_\gamma(\beta+i\gamma)|^2
 \le \frac{J(a)}{\pi(\beta-a)}+\mathcal R_T. \tag{17}
\]

若 \(\rho=\beta+i\gamma\) 是非平凡零点，则 \(E_N(\rho)=-1\)，且

\[
 |F_\gamma(\rho)|^2
 =\frac{(\beta-1)^2+\gamma^2}{(\beta+1)^2+\gamma^2}
       e^{2\beta^2/H^2}
 \ge\frac{T^2}{T^2+4}. \tag{18}
\]

这里仅用了 \(0<\beta<1\)。这个下界没有 \(\beta-\sigma\) 因子。

### 2.5 同一个 \(T_0\)，包括闭边界

令 \(a=\sigma-1/\ell\)、\(\alpha=1/(d\ell)\)，取 \(T\) 足够大
使 \(a>a_0\)。若 \(\beta\ge\sigma\)，则由 (12)–(18)

\[
 \frac{T^2}{T^2+4}
 \le \frac\ell\pi(C_LT^A)^\alpha
                   \mathcal Q_T^{1-\alpha}+\mathcal R_T. \tag{19}
\]

在 (6) 下，\(\ell\mathcal Q_T\to0\)，而

\[
 (C_LT^A)^\alpha=C_L^\alpha e^{A/d}=O(1),\qquad
 \ell\mathcal Q_T^{1-\alpha}
 =\ell^\alpha(\ell\mathcal Q_T)^{1-\alpha}\to0.
\]

同时 \(\mathcal R_T\to0\)，与 (19) 矛盾。在更强的 (8) 下，上界可写成

\[
 O_{\sigma,\theta,C,\delta,B}
       (T^{-\delta}\ell^{B+1}+T^{-2\theta}). \tag{20}
\]

所有常数和起始高度均与 \(\beta,\gamma\) 无关。dyadic 区间覆盖正高度，
共轭对称处理负高度，得到 (7)。在 (8) 的常数与起始高度有效时，(19) 还给出
一个可计算阈值的充分判据；对于较弱的 (6)，另需有效的 little-o 收敛模。
本笔记没有假设未知算术输入的常数或收敛模自动有效。

## 3. 幂次余量还能条件性地换成一点固定左移

在 (8) 下令

\[
 d_*:=\frac{d\delta}{A+\delta}>0. \tag{21}
\]

固定 \(0<h<d_*\)，在 (14) 中取 \(a=\sigma-h\)、\(\alpha=h/d\)，则

\[
 J(a)\ll
 T^{-\delta+(A+\delta)h/d}(\log T)^{B(1-h/d)}. \tag{22}
\]

幂指数严格为负。对任意固定 \(0\le\eta<h\)，目标
\(\beta\ge\sigma-\eta\) 满足 \(\beta-a\ge h-\eta>0\)，故 (17)–(18)
再次矛盾。因此 (8) 蕴含：对每个固定 \(\eta<d_*\)，存在一个统一高度，
其以上的非平凡零点满足 \(\beta<\sigma-\eta\)。不能把
\(\eta<d_*\) 未经证明改成 \(\eta=d_*\)。

**仅作条件算例。** 假如未来真正证明 (8)，并且其参数是
\((\sigma,\theta,\delta)=(14/17,30/17,7/289)\)，则

\[
 A=1467/289,\quad d_*=49/25058.
\]

取 \(h=d_*/2\)、\(\eta=d_*/4\)，(22) 保留 \(\delta/2\) 的衰减，
并条件性地排除

\[
 \beta\ge\frac{14}{17}-\frac{49}{100232}
       =\frac{82495}{100232}. \tag{23}
\]

这**不是新的无条件零点界**。若仅有
\(I\ll_\varepsilon T^{-7/289+\varepsilon}\)，必须先固定
\(0<\varepsilon<7/289\)；例如取有效 \(\delta=7/578\)，则
\(d_*=49/49997\)、\(\eta=d_*/4=49/199988\)，而不是照用 (23)。

## 4. 这次减少的义务、仍未完成的义务

- 新增的可用结论是 (6)–(7) 的完整条件转移证明，以及 (21)–(23) 的
  条件左移。固定线输入足够，不必额外证明移动直线族的算术一致性。
- **未完成的关键输入仍是 (6)，或更强的 (8)。** 必须对同一个完整
  \(E_N=\zeta M_N-1\) 证明，而非单个盒、对角、中心投影或删掉交叉项的模型。
- 将已有光滑二阶矩用于 (5) 时，要有覆盖该高度区间的非负权下界，且保持
  同一个 \(N\)。相邻 dyadic 块使用不同 \(N\) 时，不能无解释地拼接。
- 本结果不填补有限高度区间；不说明 \(T_0\) 低于任何已验证零点高度。
- 独立数学审阅核对了极点、Fourier 符号、对数凸性、Poisson 归一化、统一
  量词和固定左移分数，并指出固定左移须保留正确的对数幂；正文已处理。

## 5. 验证范围

`scripts/check_fixed_line_eventual_transfer.py` 只检查有理数模型的全部顶点、
条件左移分数、有限 Möbius 抵消、极点消除的代数下界，以及高斯模型中的
Fourier 符号与 Poisson 核归一化的数值回归。有限数值回归不是条带定理的
证明；证明在 §§2–3。脚本不含“零点界已证明”的状态布尔量。

没有 Lean 源码变更，也没有声称通过全仓 Lean 构建。
