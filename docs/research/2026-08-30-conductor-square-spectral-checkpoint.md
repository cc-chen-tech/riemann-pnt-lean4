# 平方导子局部筛与普通谱 7/71 指数：数学研究检查点

2026-08-30。本文只整理数学推导；没有新增 Lean 定理或改动证明边界。

用普通话说：我们构造了一个能区分局部导子层的有限测试，
算出了它经互反变换后的每一行，并把复合模数的不同导子层一起估计。
这给出可核验的局部代数，以及在明确列出的局部/矩输入下，
普通尖点谱主控量的指数 $2+7/71$。
**它不是完整第五矩定理，更不是 $14/17$ 或 $\Re\rho\le2/3$ 的证明。**

English scope: a central local-projector calculation and a conditional
ordinary-cuspidal-spectrum estimate, with an explicit analytic dependency
ledger. No unconditional fifth moment or zero-free theorem is claimed.

## 1. 结论与依赖分级

| 内容 | 本文状态 |
|---|---|
| 给定中央局部周期表后的筛除、对偶表与 Hecke 主项分解 | 精确恒等式；附清分母多项式核验 |
| 局部周期表来自指定向量/内积的识别 | 给出深度 0–2 的计算；不等同于全局互反 |
| 任意深度局部主控 (L-depth) | 记录推导结构；完整单位 Gram 常数审计是独立分析输入 |
| 由 L-depth、M4、M6、H2 推出普通尖点谱指数 | 本文的条件命题，证明见 §5 |
| AFE Gamma/伴随 Gamma 抵消 | 精确递推恒等式 |
| AFE 向量的变换后加权周期统一性 (A-arch) | 提出具体构造与证明路线；本检查点仍保留为分析条件 |
| 非尖点全局互反及完整边界 (G-reg/B-AFE) | 未完成 |
| 奇 Maaß 源谱、全谱第五矩、QCT、零点排除 | 未完成 |

这里“条件”不是把目标改写成一个 Prop 后宣布完成。
§5 的条件只涉及明确的局部估计及已知矩输入；§6–7 把它接回
原第五矩所需的额外分析条件单列，不将边界定义成谱差冒充互反证明。

## 2. 中央局部约定与深度 0–2 表

固定素数 $p$，$\Pi_p=1\boxplus1\boxplus1$，GL(2) 中心特征平凡，
加性特征导子为 $\mathbb Z_p$；球 Whittaker 向量在单位元取值 1。
紧群 Haar 体积为 1，$\operatorname{vol}K_0(p^d)=1/[p^{d-1}(p+1)]$
（$d\ge1$）。两个 Rankin 参数均为 $1/2$。

采用 [Nunes 的局部周期约定](https://arxiv.org/abs/2002.01993)，
尤其源码标签 whitt-IP、Whittaker-product、Hv-for-l：
naive 因子按局部标准 L 的参数构造，伴随因子是 naive 自 Rankin 因子
除以 $\zeta_p(s)$。记它在 1 的值为 $A_p^N$，则
$
 \vartheta_N(W,W')=\frac{\zeta_p(2)}{\zeta_p(1)A_p^N}
     \int_{\mathbb Q_p^\times}W(a(y))\overline{W'(a(y))}\,d^\times y,
 \qquad a(y)=\operatorname{diag}(y,1).
$
局部相对权是对此内积的正交单位基求和：
$
 H(\Phi;\sigma)=
 \sum_W\frac{\Psi(1/2,W_\Phi,\overline W)\Psi(1/2,W)}
 {L_p^N(1/2,\Pi\times\sigma)L_p(1/2,\sigma)}.
$
这里 $\Psi(s,W)=\int W(a(y))|y|^{s-1/2}d^\times y$；
第一个 $\Psi$ 为 GL(3)×GL(2) Rankin 积分，行列式权为
$|\det g|^{s-1/2}$。这一定义固定了“中央”含义和基的尺度。

置
$
 r=p^{-1},\quad u=p^{-1/2},\quad h=1-r,\quad
 z=u\lambda_\sigma(p),\quad \ell=1+r+z.
$
令 $v_0$ 为球向量，$w_{23}$ 交换后两个坐标，
$
 V_m=\sum_{b\bmod p^m}\Pi(u_{13}(b/p^m))v_0,\quad
 R=\Pi(w_{23}),\quad U_m=RV_m,\quad
 C_m=H(V_m),\quad D_m=H(U_m).
$
这些是**未平均**的向量和，$R^2=1$。$C_0=1$ 于未分歧谱，
在其他导子层为零。对未分歧谱，
$
 D_m=p^{m/2}\{\lambda(p^m)-p^{-1/2}\lambda(p^{m-1})\}\quad(m\ge1);
$
在分歧谱上 $D_m=0$。特别是 $D_1=z/r-1$、
$D_2=z^2/r^2-(1+z)/r$。

深度二计算不能用虚维数相减替代。令 $t=\lambda(p)$，
$s_0=1+r-z$，$F(y)=(1-ty+y^2)^{-1}$，则
$
 E_0=s_0^{-1},\quad E_1=(z-2r)s_0^{-2},\quad
 E_2=(z-4r)s_0^{-2}+2(z-2r)^2s_0^{-3}.
$
GL(3) 系数为 $A(i,b)=(i+1)(b+1)(i+b+2)/2$。定义
$
 S_{v,k}=\frac{v+1}{2}
 [E_2+(2k+v+3)E_1+(k+1)(k+v+2)E_0],\qquad
 T_m=\sum_{j\ge0}r^jS_{m+j,0}.
$
用单位平移 $v_j=\sigma(\operatorname{diag}(1,p^j))v_0$ 的
Gram 逆与中央第二周期的常数向量配对，得到
$
\begin{split}
 C_0&=s_0^3T_0=1,\\
 C_1&=s_0^3[T_1+(S_{0,0}+S_{0,1})/\ell],\\
 C_2&=s_0^3[T_2+(S_{1,0}+S_{1,1})/\ell
 +(S_{0,0}+(1-z-r)S_{0,1}+S_{0,2})/(h\ell)].
\end{split}
$
上述 Gram 配对可以独立核对。未分歧单位平移的相关系数为
$\rho_1=z/(1+r)$、$\rho_2=(z^2-r-r^2)/(1+r)$，
深度二 Gram 矩阵是 $G_{ij}=\rho_{|i-j|}$（$\rho_0=1$）。
深度一和二分别满足
$
 G_1^{-1}{\bf1}=\frac{1+r}{\ell}(1,1)^T,\qquad
 G_2^{-1}{\bf1}=\frac{1+r}{h\ell}(1,1-r-z,1)^T.
$
与 $p^d\operatorname{vol}K_0(p^d)=1/(1+r)$（$d\ge1$）
相乘，正好给前式各深度单元的系数，而不是借用未校正的旧基公式。

这里 $T_m$ 是必须保留的深度零单元；用几何级数及其前两次
Euler 导数求和化简，得
$
 C_1=\frac{7-r-z}{\ell},\qquad
 C_2=\frac{-z^3+(7-r)z^2+(9r-21)z+r^2-20r+27}{h\ell}.       \tag{2.1}
$
对 $\sigma=\chi\mathrm{St}$，$\chi$ 未分歧二次，
$\epsilon=\chi(p)\in\{1,-1\}$，则
$
 C_1=h,\qquad C_2=h\frac{7-\epsilon r}{1+\epsilon r}.        \tag{2.2}
$
可用生成函数
$\sum A(n,0)z^n=(1-z)^{-3}$、
$\sum A(n+1,0)z^n=(3-3z+z^2)(1-z)^{-3}$、
$\sum A(n,1)z^n=(3-z)(1-z)^{-3}$ 核对：
在此处将 $v_0$ 取为单位范数新向量，$v_1$ 为其单位平移；
新增单位旧向量为 $(v_1-zv_0)/\sqrt{1-r^2}$，
其中央配对贡献为 $(S_1-zS_0)/(1+z)$，而非独立正平方。

导子恰为 2 时新向量单元给 $C_2=h$；
导子大于 $m$ 时 $C_m=0$。这都是上述 naive 约定下的局部表。

## 3. 有限筛与完整中央对偶表

令
$
 w_p=\begin{pmatrix}0&1\\-p&0\end{pmatrix},\quad
 J_p=-\sigma(w_p),\quad
 V_1^J=-\Pi(\operatorname{diag}(w_p^{-1},1))V_1.
$
中央换元没有额外行列式因子，故 $H(V_1^J)=C_1^J$。
在未分歧 Iwahori 旧空间 $J_p$ 是负交换；
在 Steinberg 新向量上其特征值是 $\epsilon$，参见
[Schmidt, Proposition 3.1.2](https://www2.math.ou.edu/~rschmidt/papers/gl2.pdf)。
于是 $C_1^J=-C_1$（导子零），$C_1^J=\epsilon h$（导子一）。

定义
$
 a=\frac{7+r^2}{1-r^2},\quad b=-\frac{8r}{1-r^2},\quad
 P=\frac{-z^2+8z+2r-22}{h},\quad A=9r-r^2-22,\quad B=r(8-r).
$
两项关键消去为
$
 \frac{7-\epsilon r}{1+\epsilon r}=a+b\epsilon,\qquad
 C_2-(a-b)C_1=P.                                      \tag{3.1}
$
后一式的清分母恒等式是
$
 [-z^3+(7-r)z^2+(9r-21)z+r^2-20r+27]
 -(7+r)(7-r-z)=\ell(-z^2+8z+2r-22).
$
因此 $P=[(r-22)+8u\lambda(p)-r\lambda(p^2)]/h$，
是有限 Hecke 多项式，不是截断的无穷级数。

取实际向量
$
 V_P=(Av_0+BU_1-r^2U_2)/h,\qquad
 Q_p=(V_2-aV_1-bV_1^J-V_P)/h.                           \tag{3.2}
$
则逐导子层有 $H(Q_p)=\mathbf1_{c_p(\sigma)=2}$。
此为相对周期筛，不是作用于整个表示空间的正交投影。

新增 $J_p$ 包也必须变换。令
$g_b=\left(\begin{smallmatrix}p^{-1}&0&0\\0&1&0\\0&b/p&1\end{smallmatrix}\right)$，
则直接矩阵分解给
$
 R(V_1^J)=-\sum_{b\bmod p}\Pi(g_b)v_0
 =-\Pi(\operatorname{diag}(p^{-1},1,1))v_0
  -\Pi(\operatorname{diag}(w_{p^2},1))(V_1-v_0).          \tag{3.3}
$
第二个等号是**完整剩余类包**的等式，不能误读为逐项相等。
对 $b\ne0$，可核对
$
 k_b=\begin{pmatrix}1&0&0\\0&p&b^{-1}\\0&-b&0\end{pmatrix}\in GL_3(\mathbb Z_p),
 \quad p g_b k_b=
 \begin{pmatrix}1&0&0\\0&p^2&p/b\\0&0&1\end{pmatrix},
$
再用 $b\mapsto b^{-1}$、球不变性及平凡中心特征。
把嵌入 GL(2) 的平移移至中央周期，得到
$H(RV_1^J)=C_1^J$；不是声称向量本身相等。

由 $R^2=1$，
$
 H(RQ_p)=\frac{D_2-aD_1-bC_1^J}{h}
          -\frac{AC_0+BC_1-r^2C_2}{h^2}.               \tag{3.4}
$
置 $K=8r(r^2+r-1)/[h(1-r^2)]$，完整分层为：

| $c_p(\sigma)$ | $H(Q_p)$ | $H(RQ_p)$ |
|---|---|---|
| 0 | 0 | (3.4) 的显式未分歧有理权 |
| 1，$\chi\mathrm{St}$ | 0 | $K(1-\epsilon)$ |
| 2 | 1 | $r^2/h=1/[p(p-1)]$ |
| $>2$ | 0 | 0 |

$K<0$，但两个负的 Steinberg 行张量后会为正；
不能靠素数情形的符号从复合模数谱中删项。

未分歧行可进一步精确写成
$
 H(RQ_p)=\frac{p\lambda(p^2)-8\sqrt p\,\lambda(p)/(1-r^2)}h
       +\mathcal R_p,\quad
 \mathcal R_p=\frac ah-\frac A{h^2}+\frac{r^2P}{h^2}+\frac{2K}hC_1.       \tag{3.5}
$
若 Satake 参数满足 $|\alpha^{\pm1}|\le p^\theta$，$\theta<1/2$，
则 $\ell=(1+\alpha/\sqrt p)(1+\alpha^{-1}/\sqrt p)$ 统一远离零，
$\mathcal R_p=O_\theta(1)$。于是
$
 |H(RQ_p)|_{c_p=0}\ll_\theta
 1+\sqrt p|\lambda(p)|+p|\lambda(p^2)|.                 \tag{3.6}
$
主 Hecke 项不能误界为 $O(1)$。

### 伴随权不能无声替换

记 $\mathscr R_p=A_p^{\rm std}/A_p^N$。改变内积归一化后，
$
 \vartheta_{\rm std}=\vartheta_N/\mathscr R_p,\quad
 H_{\rm std}=\mathscr R_p H_N,\quad
 H_{\rm std}/L(1,\mathrm{Ad}_{\rm std})=H_N/L(1,\mathrm{Ad}_N).
$
所以标准伴随测度中的同一 $Q_p$ 权是 $\mathscr R_p\mathbf1_{c_p=2}$，
不是裸指标。由固定 $\theta<1/2$ 的 Euler 根界，有限坏素数乘积
$\mathscr R$ 及逆均 $\ll_\varepsilon(Cn)^\varepsilon$。
这允许在正主控量中比较测度，不允许在带符号迹中直接删权。
连续谱的极点分配也不能由这一中央正量比较自动解决。

## 4. 任意深度和外部矩输入

对 $(n,C)=1$，定义有限测试
$
 T_n=\bigotimes_{q^m\parallel n}q^{-m/2}\sum_{j=0}^m U_j .
$
望远镜求和给 $H(T_n)=\lambda(n)$，支持 $n$ 处未分歧谱。
$RT_n$ 支持 $n$ 处导子整除 $n$。§5 使用的局部分析输入是
$
 |H(RT_n)(f)|\ll_{\theta,\varepsilon}n^{-1/2+\varepsilon}
 \mathbf1_{\operatorname{cond}_{q\mid n}(f)\mid n}.       \tag{L-depth}
$
一个足够的更原始版本是 $|C_m|\ll_\theta(m+1)^6$，与素数统一。
推导结构如下：单位 Gram–Schmidt 每行至多三个非零系数，
固定 $\theta<1/2$ 时系数有界；中央第二周期在单位平移上相同。
第一周期换元 $\nu_2=v+k$ 抵消平移的 $p^{k/2}$，留下
$A(v+k,\nu_1)\lambda(p^v)p^{-v/2}$。
在 $\min(\nu_1,m)=b_0$、$b_0+d=m$ 单元中，
$p^m\operatorname{vol}(K_0(p^d))p^{-\nu_1}\le p^{b_0-\nu_1}$。
两个深度索引和三次多项式，配合
$\sum(v+1)^j p^{-(1/2-\theta)v}$ 的一致收敛，给出上述宽松次数。
**本检查点未写全所有分歧 Gram 常数；§5 明列 L-depth 为输入，
不把有限深度实验说成任意深度的证明。**

固定非负、足够快速衰减的谱权 $h_0$，所有和只取平凡中心特征
Maaß 新形式，采用标准伴随权。记 $M_j(q)$ 为下式将四次幂换成
$j$ 次幂后的同一加权矩（$j=4,6$）。所用矩输入是
$
\begin{aligned}
 M_4(q)&=\sum_{f\ {\rm new}(q)}
   \frac{|L(1/2,f)|^4h_0(f)}{L(1,\mathrm{Ad}f)}
   \ll q^{1+\varepsilon}, &(M4)\\
 \sum_{q\le Q}M_6(q)&\ll Q^{2+\varepsilon}, &(M6)\\
 \sum_{f\ {\rm new}(q)}\frac{|\lambda_f(k)|^2h_0(f)}{L(1,\mathrm{Ad}f)}
   &\ll(qk)^\varepsilon(q+\sqrt k),\quad(q,k)=1. &(H2)
\end{aligned}
$
(M6) 为 [BHKM, Theorem 2](https://arxiv.org/pdf/1902.07042) 的
快速衰减权版本，谱高度代价用 dyadic 分块吸收；
(H2) 对应同文 **Lemma 3**，不是 Lemma 1。
不将尖点六次矩用于 Eisenstein 谱，也不假设导子等差子族有更强六次矩。

(M4) 的标准推导是谱大筛作用于 $L(s,f)^2$ 的 AFE。
Euler 恒等式为
$L(s,f)^2=\zeta^{(q)}(2s)\sum_m\tau(m)\lambda_f(m)m^{-s}$。
在有界谱高度，长度为 $q^{1+\varepsilon}$；
按 $d^2m$ 展开，$d$ 权为 $1/d$，每段大筛为
$(q+N)(qN)^\varepsilon\sum|a_m|^2$，Minkowski 只损失对数。
谱高度通过 $h_0$ 吸收。本文把这个指定权/全新谱版本明列为矩输入，
没有为相关大筛增加更强的导子平均断言。

## 5. 条件普通尖点谱命题及证明

**命题。** 设 $C\ge2$ 平方自由，$X\ge C$，并假设
§2–3 的局部识别、L-depth、M4、M6、H2，以及
$|\lambda_f(k)|\ll_\varepsilon k^{\theta+\varepsilon}$，$0\le\theta<1/2$。
定义普通中央谱主控量
$
 Z(C;X)=\sum_{\substack{n\le X\\(n,C)=1}}n^{-1/2}
 \sum_f\frac{|L(1/2,f)|^4h_0(f)}{L(1,\mathrm{Ad}f)}
       |H_N(RQ_C;f)H_N(RT_n;f)|,\quad Q_C=\bigotimes_{p\mid C}Q_p .
$
这里两个 $H_N$ 分别只表示 $p\mid C$、$q\mid n$ 上的局部权乘积，
不是各自补齐其他素数球测试后的两个全局权；在 $Cn$ 之外仅放置一次球测试。
因此 $f$ 在 $Cn$ 外未分歧，有限导子由这些支撑限制；不含移动极点留数。
则
$
 Z(C;X)\ll_{\varepsilon,\theta,h_0}
 X C^{1+\theta/(1+\theta)+\varepsilon}X^\varepsilon.      \tag{5.1}
$
特别地 $X=C$、$\theta=7/64$ 时
$Z(C;C)\ll C^{2+7/71+\varepsilon}$。
将多个小 $\varepsilon$ 重新分配，才得到最后的单一 $\varepsilon$。

**证明。** 按局部导子指数分解 $C=DEF$，三者两两互素，
分别对应指数 2、1、0。置 $b=D^2E$。由局部表，$D,E$ 两行给
$\ll C^\varepsilon/b$，$F$ 行给
$
 C^\varepsilon\sum_{k\mid F^2}\sqrt{k}|\lambda_f(k)|.
$
总导子为 $ba$，$a\mid n$、$(a,C)=1$。写 $n=av$，
L-depth 与外部 $n^{-1/2}$ 给 $n^{-1+\varepsilon}$；
对 $v$ 求和并将 $a$ 分成 dyadic 段 $a\asymp A$，得到
$
 Z_{D,E,F}\ll\frac{(CX)^\varepsilon}{b}\max_{A\le X}\frac1A
 \sum_{\substack{a\asymp A\\(a,C)=1}}\sum_{f\ {\rm new}(ba)}
 \frac{|L(1/2,f)|^4h_0(f)}{L(1,\mathrm{Ad}f)}
 \sum_{k\mid F^2}\sqrt k|\lambda_f(k)|.                  \tag{5.2}
$
除数和、$3^{\omega(C)}$、dyadic 对数均可吸入 $\varepsilon$。

第一条界用 M4 和逐点 Hecke 界：
$
 Z_{D,E,F}\ll(CX)^\varepsilon X F^{1+2\theta}.            \tag{I}
$
第二条界保留 $k$，用 Hölder $(3/2,3)$。
$q=ba$ 只是 $q\le2bA$ 的子集，所以 M6 给 $(bA)^{2+\varepsilon}$；
H2 及 $|\lambda(k)|^3\le k^{\theta+\varepsilon}|\lambda(k)|^2$
给 Hecke 三次权和
$\ll(CX)^\varepsilon k^\theta(bA^2+A\sqrt k)$。
因此每个 $k$ 的贡献至多
$
 \frac{(CX)^\varepsilon}{b}\max_{A\le X}
 \sqrt k\,A^{-1}(bA)^{4/3}
       [k^\theta(bA^2+A\sqrt k)]^{1/3}.
$
表达式随 $A$ 增加。用 $k\le F^2$ 及 $bX\ge F$，得
$
 Z_{D,E,F}\ll(CX)^\varepsilon X F^{1+2\theta/3}b^{2/3}.  \tag{II}
$
这里 $b^{2/3}$ 不能省略，正是复合导子分层的代价。

代回 $F=C/(DE)$，两界（略去 $(CX)^\varepsilon X$）为
$
 \min\{C^{1+2\theta}(DE)^{-1-2\theta},
 C^{1+2\theta/3}D^{(1-2\theta)/3}E^{-(1+2\theta)/3}\}.
$
对 I 取 $\alpha=(1-2\theta)/(4+4\theta)$ 次幂，
对 II 取 $1-\alpha$ 次幂。$D$ 指数恰好为零，
$E$ 指数为 $-(1+2\theta)/(2+2\theta)$，
$C$ 指数为 $1+\theta/(1+\theta)$。求和所有分层即 (5.1)。
这是不等式插值，没有重复花费同一次消去。

当 $\theta=7/64$ 时，$\alpha=25/142$、$\theta/(1+\theta)=7/71$。
若 $C=p$ 为素数，未分歧主行可单用 II，
得到更小的普通谱 excess $2\theta/3=7/96$；
不能把这个素数指数直接张量到复合 $C$。

## 6. AFE 实处家族：可检查的构造与尚待闭合的统一性

本节只覆盖**偶的 O(2)-球源谱**。用
$\Gamma_\mathbb R(z)=\pi^{-z/2}\Gamma(z/2)$，定义
$
 \gamma_s(t)=\Gamma_\mathbb R(1/2+s+it)\Gamma_\mathbb R(1/2+s-it),
 \quad\gamma(t)=\gamma_0(t),\quad
 A_\infty(t)=\frac{\gamma(t)^4}
 {\Gamma_\mathbb R(1)\Gamma_\mathbb R(1+2it)\Gamma_\mathbb R(1-2it)}.
$
预期在匹配的实处归一化下球原始相对周期是 $A_\infty$；
该匹配及其可能的固定正标量须在 A-arch 中一并核对。

取固定非负整数 $M,J$，$a_j=1/2+2j$，
$
 P_M(s,t)=\prod_{j=0}^M[((a_j+s)^2+t^2)((a_j-s)^2+t^2)],
 \quad Q_J(t)=\prod_{j=0}^J[(j+1/2)^2+t^2].
$
$W(t)=e^{-t^2}Q_J(t)P_M(0,t)$ 在实谱及
$t=i\nu,|\nu|\le\theta<1/2$ 上正，并主控固定倍数的 $e^{-t^2}$。
AFE 函数 $G_M(s,t)=e^{s^2}P_M(s,t)/P_M(0,t)$ 对 $s$ 为偶，
$G_M(0,t)=1$。相应候选 Selberg 乘子为
$
 H_s(t)=e^{-t^2}Q_J(t)P_M(s,t)
              \frac{\gamma_s(t)}{\gamma(t)A_\infty(t)}. \tag{6.1}
$
必须保留伴随 Gamma，不能只抵消标准 L 的 Gamma。

由 [Gamma 递推](https://dlmf.nist.gov/5.5)，有准确恒等式
$
\begin{split}
 \prod_{j=0}^M[(a_j+s)^2+t^2]\gamma_s(t)
  &=(2\pi)^{2M+2}
    \Gamma_\mathbb R(2M+5/2+s+it)\Gamma_\mathbb R(2M+5/2+s-it),\\
 Q_J(t)\Gamma_\mathbb R(1+2it)\Gamma_\mathbb R(1-2it)
  &=\pi^{2J+2}
    \Gamma_\mathbb R(2J+3+2it)\Gamma_\mathbb R(2J+3-2it).
\end{split}                                                    \tag{6.2}
$
对 $s=\delta+i\tau$，带宽小于
$\min(2M+5/2+\delta,J+3/2)$ 时右侧没有极点；
$1/\gamma(t)^5$ 为整函数。Stirling 配合 $e^{-t^2}$，
在每个更小闭带上给有限阶导数界
$\ll(1+|\tau|)^A e^{-(\Re t)^2/2}$，常数与 $C,n$ 无关。

这导向可计算的逆变换，而非“互反不改变无穷权”的假设：
$
 g_s(u)=\frac1{2\pi}\int_\mathbb R H_s(t)e^{itu}dt,\qquad
 k_s(r)=-\frac1{\pi\sqrt2}\int_r^\infty
             \frac{g_s'(u)}{\sqrt{\cosh u-\cosh r}}du .
$
中心方向取积分为 1 的固定紧支撑核，构造
$\Phi_s=\int_{GL_2(\mathbb R)}\Pi(i(g))v_0h_s(g^{-1})dg$。
实际对偶测试必须是 $R\Phi_s$。

仍须建立的 **A-arch** 是：对此真实向量及必要的参数导数，
$
 |H_{\rm raw}(R\Phi_{\delta+i\tau};\sigma)|
 \ll_N(1+|\tau|)^{A_N}(1+\kappa_\sigma)^{-N},            \tag{A-arch}
$
并证明原周期恰为 (6.1) 所规定的乘子。
可攻的路线是单位 Kirillov 模型的 Whittaker ODE、小端
$|a|^{1/2-\eta}$ 界（$\theta<\eta<1/2$）、K 分部积分和 Casimir
迁移，再用加权 GL(3) Whittaker 半范数控制卷积。
必须检查离散系列、所有 K-type 的常数及右平移增长，
不能用抽象 Hilbert 范数的“限制算子有界”代替这一论证。
本 PR 不把这份路线说明升级为完整证明。

## 7. 从普通谱返回第五矩：不得删除的条件

即使 A-arch 成立，仍要构造 **G-reg**：
$\Pi=1\boxplus1\boxplus1$ 的完整非尖点正则化互反，
包括同一归一化下的泛型项、三个 Weyl 项、全部实际移线留数、
一致的有限部和非紧支撑 $h_s$ 的截断极限。
Nunes 的全局尖点假设不能在这里直接去掉。

真实 AFE 的正确组织是先在正的完整源第五矩上展开，保留普通连续谱；
再对有限主和用互反，而不是先减连续谱后逐 $n$ 取绝对值。
导子 $C^2$、平凡中心特征在 $p\mid C$ 有 $L_p=1$，所以 $(n,C)=1$。
取 $X=C^{1+\eta_0}$，源第四矩与右移 AFE 直线给尾界
$
 C^{2+\varepsilon}C^A X^{1/2+\theta-A};
$
固定 $\eta_0>0$ 后取 $A$ 大，可使尾项为任意指定负幂。
中央函数方程使根数在乘 $L(1/2,\sigma)^4$ 后变为 1；
这不许可删掉对偶有限权的符号。

若 L-depth、矩输入、A-arch、G-reg、源正性/伴随测度匹配，
以及普通连续谱/对偶离散谱的同等级主控均建立，
§5 经 $\Re s=\delta$ 的 Gaussian Mellin 积分，
令 $\delta+\eta_0$ 足够小，给出**条件性**形状
$
 M_{5,\mathrm{even,cusp}}(C;e^{-t^2})
 \ll C^{2+7/71+\varepsilon}+\mathcal E_{\rm AFE}(C).      \tag{7.1}
$
$\mathcal E_{\rm AFE}$ 必须是 G-reg 实际推导出的边界泛函经 AFE
积分后的绝对主控，**不是通过定义为谱差来建立 G-reg**。
还需证明 **B-AFE**：$\mathcal E_{\rm AFE}(C)\ll C^{2+\varepsilon}$。
普通连续谱和对偶离散谱的统一主控也须单列完成；
§5 的 Maaß 尖点命题未替它们作证明。

最后仍有源奇 Maaß 非球测试、完整第五矩向所需 QCT 的转化、
以及全部零点排除组装。不得从 (7.1) 跳到 $14/17$ 或 $2/3$。

## 8. 复现与审阅范围

运行标准库检查，不需要 Lean、第三方 Python 包或网络：

    python3 -B scripts/check_conductor_square_spectral_checkpoint.py

脚本检查：一般变量上的清分母恒等式、局部有限向量/分层公式、
精确分数与矩阵样例、插值指数和 Gamma 移位多项式。
它不检查无限谱求和、大筛、正则化边界或 Whittaker 统一性，
不能作为这些分析命题的证明。

本稿摘取并重新组织既有研究工作树
research/pintz-carlson-actual-cubic-two-height-l2-tail
的局部推导及后续普通谱/AFE 研究，不改写该工作树的未提交材料。
本 PR 不含原始长日志中的历史第五矩“完成”断言。
审阅重点是 §2 的归一化、§3 的实际向量而非裸谱乘子、
§5 的 $b^{2/3}$ 因子，以及 §6–7 尚未核验的分析接口。
