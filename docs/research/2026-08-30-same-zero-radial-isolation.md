# 无奇数限制的同零点响应与保持薄带的有限留数隔离

上一轮的共轭零点信号需要额外奇数限制。本轮改为同一个零点的二重位置，
以共同高度扭曲移到实轴，严格避开素数 2 的局部消去。进一步构造一个
径向多项式过滤器：在固定有限窗口内，它精确保留目标的完整双留数，
消去其他所有双留数，而且不额外支付薄带宽度倒数的幂次。

这是有限窗口的实际进展，不是完整零点排除。所需算术上界、窗口外频率、
水平边以及随窗口增长的过滤器代价仍未控制。尝试用固定高度 Gaussian
直接删除窗口外频率，会改变原问题的薄带宽度，本文把这个代价精确写出。
不写 Lean，不声称 eventual `14/17`、全局 `14/17` 或 `2/3` 已证明。

## 1. 复用对象与范围

沿用[互素 Euler 结构与零点响应](2026-08-30-primitive-euler-zero-response.md)
的原始全互素级数及真实过渡核：

\[
 D(u,v)=\sum_{(r,s)=1}\mu(r)\mu(s)r^{-u}s^{-v}
       =\frac{H(u,v)}{\zeta(u)\zeta(v)},\quad
 H_p=\frac{1-p^{-u}-p^{-v}}{(1-p^{-u})(1-p^{-v})}, \tag{1}
\]

\[
 B_\delta(x,y)=yU(x)V(y)k(z),\quad
 z=\frac{(x-y)y}{\delta},\quad \delta=X^{-1/3},\quad
 \mathcal B_\delta(u,v)=\iint B_\delta x^{u-1}y^{v-1}\,dx\,dy. \tag{2}
\]

这里 \(U,V\ge0\) 光滑紧支撑于 \((1,2)\)，\(UV\not\equiv0\)，
\(k=\chi\Re\mathcal I_{-z}[\Phi]\) 是前文构造的非负偶核，支撑于
\(32<|z|<64\)，\(\kappa_0=\int k>0\)。前文已证

\[
 \mathcal B_\delta(\beta,\beta)
 =\delta\kappa_0v_\beta+O(\delta^3)>0,\qquad
 v_\beta=\int U(y)V(y)y^{2\beta-2}\,dy>0. \tag{3}
\]

(1) 的级数只先在 \(\Re u,\Re v>1\) 使用；\(H\) 在
\(\Re u>0,\Re v>0,\Re(u+v)>1\) 正常收敛，给出亚纯延拓。
基础 [Euler 级数](https://dlmf.nist.gov/27.4) 和
[Mellin 反演](https://dlmf.nist.gov/2.5) 不包含本题缺失的相关上界。

也检查并复用了既有 worktree `vk-edge-annihilator-h-average`、commit
`ef9e04b6` 中 `docs/research/vk-edge-pi-over-two-localized-transfer.md`
的有限极点过滤思路。该文的固定多项式 Gaussian 稳定性针对单变量
\(\zeta'/\zeta\) 与宽对数窗口；它不自动给本题双变量 \(1/\zeta\)、
薄带及核半范数的一致结论。以下有限过滤和宽度计算单独推导。

## 2. 同零点位置使完整 Euler 因子不为零

设 \(\rho=\beta+i\gamma\) 是非平凡零点，\(2/3<\beta<1\)。在
\((u,v)=(\rho,\rho)\) 上，所有 \(p\ge3\) 满足

\[
 |2p^{-\rho}|=2p^{-\beta}<1.
\]

素数 2 则用反三角不等式，而不是共轭点的余弦符号：

\[
 \boxed{|1-2^{1-\rho}|\ge2^{1-\beta}-1>0.} \tag{4}
\]

因此 \(H(\rho,\rho)\ne0\)。对 \(2/3\le\beta\le1-\eta\)、固定
\(\eta>0\)，\(|H(\rho,\rho)|\) 还有不依赖 \(\gamma\) 的正常数上下界；
在 \(\beta\to1\) 时不能沿用同一个下界。这不是说 \(H\) 在整个双变量
半平面处处不为零，只是在同零点的对角位置排除了全部局部消去。

若重数为 \(m\)，写 \(a_\rho=\zeta^{(m)}(\rho)/m!\)。定义

\[
 C_\rho=H(\rho,\rho)/a_\rho^2\ne0,
 \qquad \omega_\rho=\overline{C_\rho}/|C_\rho|. \tag{5}
\]

\(C_\rho\) 通常不是正实数；不能像共轭位置一样把分母写成
\(|a_\rho|^2\)。单位相位 \(\omega_\rho\) 才使领先系数变成正实数。

对原整数系数作共同扭曲

\[
 \mathscr S_\gamma[B](X)
 =\sum_{(r,s)=1}\mu(r)\mu(s)(rs)^{-i\gamma}B(r/X,s/X). \tag{6}
\]

这不改变互素、平方自由或奇偶支撑。它的级数是
\(D_\gamma(u,v)=D(u+i\gamma,v+i\gamma)\)，目标极点位于
\((\beta,\beta)\)。对 \(c>1\)，严格反演给

\[
 \mathscr S_\gamma[B_\delta](X)
 =\frac1{(2\pi i)^2}\int_{(c)}\int_{(c)}
 D_\gamma(u,v)X^{u+v}\mathcal B_\delta(u,v)\,du\,dv. \tag{7}
\]

若改把相位放在归一化变量，必须保留
\((rs)^{-i\gamma}=X^{-2i\gamma}(xy)^{-i\gamma}\)，不能漏掉外面那一项。
对应变换的精确关系是
\(\mathcal M[(xy)^{-i\gamma}B](u,v)=\mathcal B(u-i\gamma,v-i\gamma)\)。
因此在原坐标 \((\rho,\rho)\) 的核值严格等于
\(\mathcal B(\beta,\beta)\)，没有前轮 \(|\gamma|\delta\ll1\) 的核响应条件。

固定 \(\rho\) 时，(7) 在 \((\beta,\beta)\) 的局部双留数满足

\[
 \boxed{\Re(\omega_\rho\mathcal R_\rho(X))\sim
 \frac{|C_\rho|\kappa_0v_\beta}{((m-1)!)^2}
 X^{2\beta-1/3}(\log X)^{2m-2}.} \tag{8}
\]

这还不是 (6) 的下界。扭曲相位也不免费：固定阶 Euler 导数的核半范数
可增长为 \((1+|\gamma|)^j\)。固定零点、\(X\to\infty\) 与
\(|\gamma|\asymp X^{1/3}\) 的统一估计是不同要求。原 MMKLS 并未因此
自动提供这些依赖零点的加权算术上界。

## 3. 同时伸缩两变量，保持真实薄带

始终在 **固定 \(\delta\)** 下令

\[
 \mathcal E=x\partial_x+y\partial_y.
\]

从 \(z=(x-y)y/\delta\) 精确算出

\[
 \boxed{\mathcal Ez=2z,}\qquad
 \mathcal E B_\delta
 =y[(xU'+U)V+yUV']k(z)+2yUV\,z k'(z). \tag{9}
\]

故任意固定次数 \(j\) 的 \(\mathcal E^j B_\delta\) 是有限个
\(y\,U_j(x)V_j(y)(z\partial_z)^{\ell}k(z)\) 的组合；其原型核及系数不依赖
\(\delta\)，仍支撑在同一个薄带。这里说的是没有因这次径向操作**额外**
出现 \(\delta^{-j}\)；普通横向偏导数本来就会包含薄带尺度。

保留真实 profile 也成立。对紧支撑 \(\Phi\)，积分分部给

\[
 \boxed{z\partial_z\mathcal I_{-z}[\Phi]
        =\mathcal I_{-z}[a\partial_a\Phi].} \tag{10}
\]

其证明中，profile 的 \(|z|^{-1}\) 导数与
\(\partial_a(a\Phi)\) 的零阶项正好匹配。对
\(k=\chi\Re\mathcal I_{-z}[\Phi]\)，Leibniz 法则保留全部
\(z\partial_z\chi\) 和 \(a\partial_a\Phi\) 项。于是 (9) 真正落在已声明
过渡 profile 的有限线性组合内，不是将核替换成任意 Schwartz 函数。

Mellin 积分分部无端点项，给出

\[
 \mathcal M[\mathcal EB](u,v)=-(u+v)\mathcal B(u,v),\qquad
 \mathcal M[P(-\mathcal E)B](u,v)=P(u+v)\mathcal B(u,v). \tag{11}
\]

不能把 \(\mathcal E\) 换成对 \(X\) 的微分：沿原族
\(\delta(X)=X^{-1/3}\) 求导时还有额外的 \(\delta\) 导数。

## 4. 固定有限窗口内的精确双留数隔离

选一个不穿过零点的有限矩形

\[
 \mathcal Q=\{a<\Re s<b,\ |\Im s|<L\},\qquad
 1/2<a<2/3,\quad b>1.
\]

假设它含有至少一个实部大于 \(2/3\) 的零点。令 \(\mathcal Z\) 为其中
的全部不同零点，\(m_\lambda\) 为重数。选择实部最大的零点，并在实部
并列时选虚部最大的一个，记为 \(\rho=\beta+i\gamma\)。这是对一个
有限集合的选择，不假定所有零点存在全局最右者。
若从一个假设零点出发，先取包含它的窗口；本节允许重新选择窗口的极端
零点，其实部不会更小。不是说任意预先指定的非极端零点都满足 (12)。

它有一个关键的有限集合性质：

\[
 \lambda,\nu\in\mathcal Z,\quad\lambda+\nu=2\rho
 \quad\Longrightarrow\quad\lambda=\nu=\rho. \tag{12}
\]

先比较实部，两者都只能取最大值；再比较虚部，同样只能同时取最大值。
令 \(w_0=2\beta\)，对其余有序对收集不同的和

\[
 w=\lambda+\nu-2i\gamma\ne w_0,\qquad
 K_w=\max_{\lambda+\nu-2i\gamma=w}(m_\lambda+m_\nu-1).
\]

构造

\[
 P_0(z)=\prod_w\left(\frac{z-w}{w_0-w}\right)^{K_w}. \tag{13}
\]

于是 \(P_0(w_0)=1\)。为完整保留重零点的留数，而非仅保留最高对数项，
再取 \(1/P_0\) 在 \(w_0\) 的 \(2m_\rho-2\) 次 Taylor 多项式 \(T_0\)，令

\[
 \boxed{P=P_0T_0,\qquad
 P(z)=1+O((z-w_0)^{2m_\rho-1}).} \tag{14}
\]

所有非目标根及其至少 \(K_w\) 的重数仍保留。

**双留数核查。** 在 \((u,v)=(\lambda-i\gamma,\nu-i\gamma)\) 的局部坐标
\((\xi,\eta)\)，亚纯部分至多为 \(\xi^{-m_\lambda}\eta^{-m_\nu}\) 乘
全纯函数。非目标处 \(P(u+v)\) 从总次数
\(m_\lambda+m_\nu-1\) 或更高开始，而双留数只读取总次数
\(m_\lambda+m_\nu-2\) 的系数，故严格为零。目标处 (14) 同理使
\(P-1\) 对完整双留数毫无贡献。

设 \(\Gamma=\partial(\mathcal Q-i\gamma)\) 正向，逐变量留数定理给

\[
 \boxed{\frac1{(2\pi i)^2}\int_\Gamma\int_\Gamma
 D_\gamma(u,v)X^{u+v}P(u+v)\mathcal B_\delta(u,v)\,du\,dv
 =\mathcal R_\rho(X).} \tag{15}
\]

这里 \(\mathcal R_\rho\) 是未乘 \(P\) 的同零点完整局部留数。由于
\(a>1/2\)，(1) 的修正因子在整个矩形乘积附近全纯；边界避开零点，
各积分都是有限且合法的。即使别处 \(H\) 有零，也不会产生额外极点。

(11) 又把 (15) 的测试核精确实现为 \(P(-\mathcal E)B_\delta\)，
全程没有加入奇数限制，没有冻结 \(r/X\)，也没有额外的
\(\delta^{-\deg P}\) 损失。**但闭矩形积分 (15) 不是右线无穷积分 (7)。**

## 5. 过滤器的具体代价与它尚未控制的项

记不同零点数为 \(n\)，总重数为 \(M\)。直接构造满足

\[
 \deg P_0\le\sum_{(\lambda,\nu)\ne(\rho,\rho)}
 (m_\lambda+m_\nu-1)\le2nM-n^2,\quad
 \deg P\le\deg P_0+2m_\rho-2. \tag{16}
\]

若 \(P_0=\sum c_jz^j\)，其系数范数有明确的有限界

\[
 \sum_j|c_j|\le
 \prod_w\left(\frac{1+|w|}{|w_0-w|}\right)^{K_w}. \tag{17}
\]

Taylor 修正 \(T_0\) 的系数还依赖这些间距。对固定有限配置，它们都是
有限常数；让窗口随 \(X\) 增长时，没有证明它们或所需高阶核半范数
只是对数幂或 \(X^{o(1)}\)。固定阶无额外薄带损失不等于增长阶数免费。
例如 \(P_0( w_0+t)=(1+t)^2\)、目标重数为 2 时，修正后是
\(P(w_0+t)=1+4t^3+3t^4\)；原乘积因子的逐项系数界不能不经重算就
套在修正后的 \(P\) 上。

具体地，若 \(d_0=\deg P_0\ge1\)、\(\eta=\min_w|w_0-w|>0\)、
\(q=2m_\rho-2\)，把 \(P\) 用 \(t=z-w_0\) 展开，则

\[
 |[t^\ell]P(w_0+t)|\le\eta^{-\ell}
 \sum_{j=\max(0,\ell-d_0)}^{\min(q,\ell)}
 {d_0\choose\ell-j}{d_0+j-1\choose j}. \tag{17a}
\]

因为 \(P_0\) 的系数被 \((1+t/\eta)^{d_0}\) 控制，而其逆幂级数的
绝对系数被 \((1-t/\eta)^{-d_0}\) 控制，截断后作卷积即得。
\(P_0\equiv1\) 时单独取 \(P=1\)，不定义空集最小间距。

径向过滤只识别 \(u+v\)。若窗口外某对零点有
\(\lambda+\nu=2\rho\)，它不能区别该对和目标；(12) 仅对固定集合成立。
这不是断言实际 zeta 零点存在这样的关系，而是过滤器的精确分辨边界。

实际尝试估计 (15) 的边界：固定矩形及固定 \(P,\rho\) 时，
\(\mathcal B_\delta=O(\delta)\) 一致，直接绝对值只给

\[
 O_{\Gamma,P,\rho}(\delta X^{2b}), \tag{18}
\]

远高于 \(X^{2\beta-1/3}\)，更不用说目标 \(X\)。这只是所用方法的
上界，不是边界积分的下界。改写为右线加其他边时，必须控制全部剩余
边和无穷尾；不能将有限留数的精确消去算作它们已经小了。

保留前文的 Mellin 衰减可得，对固定 \(P\)

\[
 |P(u+v)\mathcal B_\delta(u,v)|
 \ll_{P,N,J}\delta(1+|t+t'|)^{-N}(1+\delta|t|)^{-J}. \tag{19}
\]

多项式增长由更高阶的径向衰减支付，但 \(t\approx-t'\) 上仍允许
\(\delta^{-1}=X^{1/3}\) 的高度。这个过滤器没有删除长差频方向。

## 6. 固定差频 Gaussian 会改变薄带：精确计算

为了检查能否先无损地截到有限高度，取 \(A>0\) 并定义

\[
 (\mathcal G_A B)(x,y)=\frac A{\sqrt\pi}
 \int_{\mathbb R}e^{-A^2t^2}B(e^tx,e^{-t}y)\,dt. \tag{20}
\]

变量替换和 Gaussian 积分严格给

\[
 \boxed{\mathcal M[\mathcal G_A B](u,v)
   =e^{(u-v)^2/(4A^2)}\mathcal B(u,v).} \tag{21}
\]

在等实部竖线上，这正好抑制 \(|t-t'|\gg A\)。它不改变同零点位置
\(u=v=\beta\) 的核值，但确实改变物理和，不能当作原权不变。

令 \(p=\sqrt{xy}\)、\(d=\log(x/y)\)、\(b=t+d/2\)。在积分中的薄带上

\[
 z=\frac{p^2(1-e^{-2b})}{\delta},\quad
 b=-\frac12\log(1-\delta z/p^2),\quad
 db=\frac{\delta\,dz}{2p^2(1-\delta z/p^2)}. \tag{22}
\]

因此对 \(p\) 在固定正紧集、\(\delta\) 充分小时，(20) 精确变为

\[
 \frac{A\delta}{\sqrt\pi}\int
 e^{-A^2(b-d/2)^2}
 \frac{p e^{-b}U(pe^b)V(pe^{-b})k(z)}{2p^2(1-\delta z/p^2)}\,dz.
 \tag{23}
\]

取 \(p\) 位于 \(U,V\) 共同严格为正的固定内部区间。由 \(b=O(\delta)\)，
在 \(|d|\le1/A\)、\(A\ge A_0\)、\(A\delta\le c_0\) 时，固定
\(A_0,c_0>0\) 可选得

\[
 \boxed{c A\delta\le(\mathcal G_A B_\delta)(x,y)
                     \le C A\delta.} \tag{24}
\]

上下界常数不依赖 \(A,\delta\)。所以当 \(A\delta\to0\) 时，在
\(|d|=1/(2A)\gg\delta\) 处原核已经为零，新核却仍有 \(A\delta\) 大小。
固定高度截止将有效对数比值宽度扩至 \(A^{-1}\)，幅度相应变为
\(A\delta\)，不是免费获得了一个 \(\delta\) 节省。

要维持有效 \(\delta\) 宽度，至少需要 \(A\) 在
\(\delta^{-1}\) 量级，重新回到原长差频尺度。任意有限 \(A\) 的 Gaussian
都有非紧尾，故即便 \(A\gtrsim\delta^{-1}\) 也不是精确保留紧支撑。
硬裁回原薄带会破坏 (21) 的精确频率乘子，必须重新核算。

还可用两个精确恒等式检查这个代价。相对伸缩的生成元满足

\[
 (x\partial_x-y\partial_y)z=2y^2/\delta,
\]

与 (9) 的径向恒等式不同，直接触及横向薄带尺度。另一方面，反向伸缩
\((x,y)\mapsto(e^tx,e^{-t}y)\) 的二维 Jacobian 是 1，故对非负核

\[
 \iint\mathcal G_A B\,dx\,dy=\iint B\,dx\,dy. \tag{25}
\]

这也是 \(O(A\delta)\) 幅度与 \(O(A^{-1})\) 展宽不能分开算成净节省的
连续质量检查，不是整数 Möbius 加权和的质量守恒。

## 7. 本轮推进与真实下一步

已经闭合的是：全互素同零点因子的非消失、相位准确的共同扭曲、保持
薄带的径向微分实现、包括重数的有限双留数精确隔离，以及 Gaussian
差频截止的真实宽度代价。上述结果不需要额外奇数限制。

下一步真正要估计的是带 \(P(u+v)\) 的原耦合右线积分，特别是长差频
方向与剩余边的联合贡献；或者找能在保留该物理尺度的情况下控制窗口外
零点的探测器。本文没有把这项解析任务替换为“有限零点已经消去”。
也没有证明同强度的扭曲 Möbius 上界。所有目标零点界仍未证明。

后续[差频消失矩与原函数门槛](2026-08-30-difference-frequency-primitive-threshold.md)
证明实际核具有全部差频消失矩，但全局系数相容的 `B²` 原函数在
`σ≤3/4` 不存在。实际移位窗口排除了产生该门槛的相邻整数；剩余任务
仍是有限高度 Gram 非对角的真实符号控制，不能换用无限平均正交性。

有限检查见 `scripts/check_same_zero_radial_isolation.py`。其中谱节点是
明确标注的代数样本，不是发现了任何临界线外的实际零点；有限核算不
替代连续 Mellin、微分、留数及 Gaussian 论证。

### English scope summary

The same-zero position avoids the prime-2 cancellation without an odd-only
restriction. A common multiplicative twist produces a nonzero local pole
response, with its complex phase retained. A radial Hermite polynomial
filter exactly preserves the target mixed residue and removes all other
mixed residues in a fixed finite rectangle. Its differential realization
does not add inverse-thickness powers, but its configuration-dependent
constants are not uniform in growing windows. A difference-frequency
Gaussian broadens the physical strip; the infinite arithmetic integral,
boundary terms and zero-free conclusions remain uncontrolled.
