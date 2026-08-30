# 完整 h/δ 重组：原 Ramanujan 校正的独立费用

白话结论：固定一个内部 AFE 核，把全部 h 与 δ 的光滑分割精确合回去，
可单独将 FP3 原 Ramanujan 校正支付到 T^(1+ε)/q₀，且没有 E 下限。
关键是原核连续均值的非驻相衰减；这在保留单个 L 分割时不能直接使用。
本文不支付 PR529 的新模 a 主角色、其余除数项或全局中心化和，
也不证明 14/17、2/3 零点排除。它是一个局部解析检查点，不是 Lean 定理。

English summary: full h/delta reassembly bounds the original Ramanujan correction
of a fixed interior core FP3 AFE family by O(T^(1+epsilon)/q0), uniformly in E.
This does not bound an individual L packet, the new modulus-a principal, or the
remaining centered/global operator. Finite guards supplement the analytic proof.

## FD1. 定义源、全部掩码与对象

上游固定 49cfacd70c60372757280177c7b63fd4f7760817 的
`docs/research/2026-08-24-mobius-weighted-off-diagonal.md` (2.5)、(4.4)–(4.5)。
全 h 恒等式使用 PR519 的冻结 614624c83da5bfe41b20a5b1c6f4629d941da806
中 H1–H3；原 μ(q) 融合采用 H5。本文不修改 PR519 或 PR529。

固定 T≥2、N=T³、平方自由 q₀ 和尺度 R,S,E,Q,M,K，满足
\[
 EQ=S,\qquad KS\asymp MR,\qquad MK\le C T.             \tag{FD1}
\]
所有比较常数固定。整个 R/S 包满足 q₀n,q₀s≤N/2 的内部支持；
不另插入二变量硬角点。保留 p_N、F_R、F_S 及所有原 AFE 截断。
整数 n∼R、e∼E、q∼Q、s=eq，其中 e,q 平方自由，
\[
 (e,q_0q)=(q,q_0)=(n,q_0eq)=1,\qquad (uv,q)=1,
 \quad h=eu,\quad\delta=ev.                           \tag{FD2}
\]
这恰是 FP3 的双整除层，不是全部 canonical 分配。以下 q>1；
q=1 的原中心化核恒为零，应整体单列，不能只保留其非零校正。
没有新增 m 的互素或平方自由条件。

原 W∈C_c^∞(R) 支持在 [1,2]。原权满足
\[
 x^jT^k|\partial_x^j\partial_t^k V_t(x)|
 \le C_{A,j,k}(1+x/T)^{-A},\quad T\le t\le2T.          \tag{FD3}
\]
F_M(x)=F(x/M)、F_K(y)=F(y/K)，F 光滑支持在 [1/2,2]。
固定截断的缩放导数和原 mollifier taper 的模长均有界。

## FD2. 完整分割重组而非固定 L 包

从 FP1 插入的原重叠光滑分割
\[
 \sum_H F(|h|/H)=\sum_L F(|\delta|/L)=1
 \quad(h,\delta\ne0)
\]
精确恢复原和，不继承 literal 硬 H/L 壳。固定本层 AFE 参数时，
x∼M、y∼K 与 δ=sy−nx 给 |δ|≲SK+RM，因此只有有限个整数 δ，
即使在全 h Poisson 之前也是如此。对每个这样的 δ，x 核光滑紧支，
h Fourier 和绝对收敛。故本层可重组全部 H 与 L；
这不自动证明跨全部 AFE 尺度的换序或统一尾。

全 h 后 m 是正整数，m∈[M/2,2M]。定义连续 v 核
\[
 A_m(v)=\frac{F_M(m)F_K(y)}{\sqrt{my}}
  \int W(t/T)V_t(my)\left(\frac{sy}{nm}\right)^{it}dt,
 \qquad y=\frac{nm+ev}{s}.                             \tag{FD4}
\]
在 m,y>0 外光滑延零。y 是连续参数，不能补成整数。
这里已无 F(|ev|/L)；v=0 因 q>1 与 (v,q)=1 自动排除。

H2 的核为 C_q=c_q(nm+ev)−μ(q)c_q(m)/φ(q)。平方自由 q 给
\[
 \mu(q)C_q=
 \sum_{d\mid(q,nm+ev)}\mu(d)d-\frac{c_q(m)}{\varphi(q)}.\tag{FD5}
\]
所以本文估计的原校正项，含准确唯一外权，是
\[
 \mathscr R=-2\sum_{e,q,n,m}
 \frac{\mu(e)\mu(n)p_N(q_0n)p_N(q_0s)F_R(n)F_S(s)}
      {q_0\sqrt{ns}\,s}
 \frac{c_q(m)}{\varphi(q)}
 \sum_{(v,q)=1}A_m(v).                                \tag{FD6}
\]
所有 FD2 条件保留。该项不是另一字符分解的新主角色；
也不能不经映射就等同 PT 所处理的全部 D+J_Ram。

## FD3. 真正的缩放核与有限导数预算

置
\[
 A_* =\frac{T}{\sqrt{MK}},\qquad
 V_* =\frac{RM}{ET},\qquad
 \kappa=\frac{eRM}{Enm}.                               \tag{FD7}
\]
实际整数 e 与尺度 E 不同，κ 中的 e/E 不可漏掉。κ 在固定正紧区间。
令 z=v/V_*、w=t/T，则
\[
 y=\frac{nm}{s}(1+\kappa z/T),\qquad
 e^{it\log(sy/(nm))}=e^{iTw\log(1+\kappa z/T)}.
\]
在 F_K 的支集上，1+κz/T 由 KS∼MR 保证在固定正紧区间，且
\[
 |T\log(1+\kappa z/T)|\ge c|z|.
\]
归一化振幅的固定 z,w 混合导数由 FD3 控制；相位的一次 z 导数
wκ/(1+κz/T) 一致有界，更高导数多出 T^(-1)。
先作 a≤2 次 z 导数，再作四次 w 分部积分，得到
\[
 \left|\partial_z^a\{A_m(V_*z)/A_*\}\right|
 \ll \mathcal D_{12}(1+|z|)^{-4},\qquad 0\le a\le2.   \tag{FD8}
\]
|z|≤1 时用直接界。W 与 AFE 截断在边界平坦，无边界项；
y 支集外的延零仍光滑。相位导数落入振幅后，其 w 导数仍有界。

这里 D₁₂ 是 W、固定 F 的有限缩放半范数与 FD3 中 A=0、j+k≤12
常数的预算：固定 W/F 的半范数可乘入常数，对 V 的预算保持线性。
FD8 实际最多需六阶混合导数。后面的均值另用六次 y∂y，
同一最大导数预算足够，并非平方收费。本文不宣称任意 B₆ 点权均适用。

用 Fourier 约定 \(\widehat A(\xi)=\int A(v)e(-v\xi)dv\)，
FD8 的函数及二阶导数 L¹ 范数给
\[
 |\widehat A_m(\xi)|
 \ll \mathcal D_{12} A_*V_*(1+V_*|\xi|)^{-2}.         \tag{FD9}
\]

## FD4. 连续零频须另付，不能直接用 FD9

当 V_* 很大时，FD9 的零频上界过大。现在换元 dv=q dy，得
\[
 \widehat A_m(0)=\frac{qF_M(m)}{\sqrt m}
 \int W(t/T)(s/(nm))^{it}
 \int F_K(y)y^{-1/2+it}V_t(my)\,dy\,dt.              \tag{FD10}
\]
内层相位 t log y 无驻点。令 y=Kz，在固定紧支上用
\((z\partial_z)/(it)\) 分部积分六次，FD3 给
\[
 |\widehat A_m(0)|\ll\mathcal D_{12} A_*qK T^{-6}.     \tag{FD11}
\]
这是标准光滑非驻相分部积分，参见
[Tao 的振荡积分讲义 §2](https://www.math.ucla.edu/~tao/247b.1.07w/notes8.pdf)；
此处所有尺度一致性已由 FD1/FD3 显式核对，不由引用免费获得。
非空 m 支持给 M≥1/2，因而 K≲T；同时 q≤s≤N=T³，故
qK≲T⁴，FD11≲D₁₂A_*T^(-2)。只调用固定有限阶，不隐藏任意阶预算。

这一步依赖全部 L 重组。固定 L 时还存在 F(|sy−nm|/L)，
其 y 缩放导数可达 SK/L，不能套用上述统一六次分部积分。
一般 Schwartz 核也可能有大均值；必须保留 FD10–FD11。

## FD5. 任意整数网格与完整单位掩码

对每个整数 b≥1，普通 Poisson 给
\[
 \sum_{j\in\mathbb Z}A_m(bj)
 =\frac{\widehat A_m(0)}b
  +\frac1b\sum_{k\ne0}\widehat A_m(k/b).              \tag{FD12}
\]
令 x=V_*/b>0。由递减函数积分比较，
\[
 x\sum_{k\ne0}(1+x|k|)^{-2}\le2.
\]
因此 FD9 支付非零频，FD11 支付零频，统一得到
\[
 \left|\sum_j A_m(bj)\right|\ll\mathcal D_{12}A_*.
\]
该界同时包括 V_*<1 与 V_*≥1，不增加虚构的整数行数损失。
现在才作完整的 (v,q)=1 容斥：
\[
 \sum_{(v,q)=1}A_m(v)
 =\sum_{b\mid q}\mu(b)\sum_j A_m(bj)
 \ll\mathcal D_{12}A_*\tau(q).                        \tag{FD13}
\]
每个网格的 j=0 均保留；其项只在完整 Σ_{b|q}μ(b)=0 中取消。
若单独删去一个网格的 j=0，FD12 右边必须相应减 A_m(0)。
复合 q 和非单位 m 都未被删除；这里未使用新的 Möbius 有符号消去。

## FD6. 全部物理外层费用

用 |c_q(m)|≤φ(q)、τ(q)≪εT^ε。n,m,e,q 的行数分别为
O(R),O(M),O(E),O(Q)；非空整数壳的尺度至少是固定正数，
故不存在额外 +1 的幂损失。所有原掩码保留到此时，再取绝对上界。
EQ=S 给
\[
 |\mathscr R|
 \ll_\epsilon\mathcal D_{12}T^\epsilon
 \frac{RSM}{q_0\sqrt{RS}\,S}\frac{T}{\sqrt{MK}}
 =\frac{\mathcal D_{12}T^{1+\epsilon}}{q_0}
       \sqrt{\frac{MR}{KS}}
 \ll\frac{\mathcal D_{12}T^{1+\epsilon}}{q_0}.          \tag{FD14}
\]
这是完整 FD6 的费用，无 E 的幂阈值。结论仍只针对固定 q₀、R/S/E
及 core AFE 层的完整 h/δ 原校正；全除数项、新模 a 低导子/主角色、
其他 canonical 层、q₀ 外壳与跨 AFE 尾未因此支付。

## FD7. 辅助恒等式及不得扩张的含义

全 d|q 展开在 v 的普通零频上有精确 Euler 恒等式
\[
 \sum_{d\mid q,(m,d)=1}\mu(d)
   \sum_{b\mid q,(b,d)=1}\frac{\mu(b)}b
 =\frac{c_q(m)}q
 =\frac{c_q(m)}{\varphi(q)}\sum_{b\mid q}\frac{\mu(b)}b.
\]
逐素数 p∤m 给 −1/p，p|m 给 1−1/p。它仅重述原 v 均值中心化；
不能将另一个字符分解的主角色等同于此普通零频。

另有素数 q=p、(m,p)=1 的精确变换：
\[
 \frac1p\sum_{v\in U(p)}\mu(p)C_p e_p(kv)
 =\begin{cases}0&p\mid k,\\
 -e_p(-knm\bar e)-1/(p-1)&p\nmid k.\end{cases}
\]
FD4 的 v=p y−nm/e 换元产生 e(knm/(ep))，互反恒等式为
\[
 e_p(-knm\bar e)e(knm/(ep))=e_e(knm\bar p).
\]
这提供全 δ 后的一种模 e 表示，但本文未从中取得新上界。
固定 L 的联合截断仍依赖 n，不能提前称已得到共同 n 光滑列。

配套 `scripts/check_physical_full_delta_correction.py` 只核对有限恒等式、
精确归一化、反例及显式 Schwartz 玩具；不替代 FD3–FD6 的解析证明，
不认证全局零点目标或 Lean 基线。
