# 互素 Möbius 对的 Euler 结构与实际过渡核的零点响应

这次直接检查剩余相关和中的两种潜在消去：互素容斥是否会消去假设零点，
以及实际过渡核是否有相应的消失矩。答案不是简单的“都会消去”：去掉
素数 2 后，Euler 修正因子在目标区域不为零；一个合法的过渡核子区间
在共轭零点处也有正实部响应。这给出了可继续研究的零点信号，但**没有**
证明它在完整算术和中不可被其他项抵消，更没有证明零点界。

本文承接[实际 quotient 支撑与过渡区](2026-08-30-physical-quotient-support-transition.md)。
保留原互素条件、原变量权重、薄带 Jacobian 以及额外奇数限制的身份。
不改 Lean，不把解析延拓当作收敛级数，也不假定跨过零点的移线合法。

## 1. 双变量 Euler 因子与完整系数

先在 \(\Re u,\Re v>1\) 定义绝对收敛级数

\[
 D(u,v)=\sum_{(r,s)=1}\frac{\mu(r)\mu(s)}{r^u s^v}.
\]

每个素数只能出现在 \(r,s\) 中的一个，且次数最多为一，因此

\[
 D(u,v)=\prod_p(1-p^{-u}-p^{-v})
       =\frac{H(u,v)}{\zeta(u)\zeta(v)},\qquad
 H_p=1-\frac{p^{-u-v}}{(1-p^{-u})(1-p^{-v})}. \tag{1}
\]

使用的基础 Euler/倒数级数恒等式见
[DLMF 27.4](https://dlmf.nist.gov/27.4)；这里的双变量因子逐素数推导，
不引用任何 Möbius 相关猜想。

令

\[
 \Omega=\{(u,v):\Re u>0,\ \Re v>0,\ \Re(u+v)>1\}.
\]

在 \(\Omega\) 的每个紧集，\(H_p-1=O(p^{-\Re(u+v)})\) 一致，故
\(H=\prod H_p\) 正常收敛为全纯函数。它允许有限局部因子为零；不能由
乘积绝对收敛直接宣称不为零。(1) 给出 \(D\) 在 \(\Omega\) 的亚纯延拓，
并不宣称原双级数在此收敛。

这个修正的全部 Dirichlet 系数也可写明：

\[
 h(d,e)=
 \begin{cases}
 \mu(\operatorname{rad}d),&\operatorname{rad}d=\operatorname{rad}e,\\
 0,&\text{否则},
 \end{cases}
 \qquad h(1,1)=1. \tag{2}
\]

因为局部修正是 \(1-\sum_{a,b\ge1}p^{-au-bv}\)，对每个整数对有有限恒等式

\[
 \mu(r)\mu(s)\mathbf1_{(r,s)=1}
 =\sum_{d\mid r,e\mid s}h(d,e)\mu(r/d)\mu(s/e). \tag{3}
\]

这不是只保留 \(d=e\) 的卷积；例如 \(h(p,p^2)=-1\)。对 \(\sigma>1/2\)，

\[
 \sum_{d,e}\frac{|h(d,e)|}{(de)^\sigma}
 =\prod_p\left(1+\frac{p^{-2\sigma}}{(1-p^{-\sigma})^2}\right)<\infty.
 \tag{4}
\]

因而 \(0<\eta<1/2,Z\ge1\) 时
\(\sum_{de>Z}|h(d,e)|/(de)\ll_\eta Z^{-1/2+\eta}\)。这是系数尾界；
代回薄带时还须计数每个 \(d,e\) 的整数端点，不能直接把它当作物理和尾界。

## 2. 为什么单独去掉素数 2，以及不能免费去掉什么

定义奇数互素对级数

\[
 D_{\rm odd}(u,v)=\sum_{\substack{(r,s)=1\\r,s\text{ odd}}}
 \frac{\mu(r)\mu(s)}{r^u s^v}
 =\frac{G_{\rm odd}(u,v)}{\zeta(u)\zeta(v)},\quad
 G_{\rm odd}=\frac{\prod_{p\ge3}H_p(u,v)}{(1-2^{-u})(1-2^{-v})}.
 \tag{5}
\]

若 \(\Re u,\Re v\ge2/3\)，则对 \(p\ge3\)
\(|p^{-u}+p^{-v}|\le2p^{-2/3}<1\)：最后一步等价于 \(8<9\)。
每个分子 \(1-p^{-u}-p^{-v}\) 均不为零，结合正常乘积尾可得

\[
 0<c\le |G_{\rm odd}(u,v)|\le C<\infty
 \qquad(\Re u,\Re v\ge2/3), \tag{6}
\]

其中常数不依赖虚部。这里对有限小素数分别取上下界，对大素数使用
\(H_p=1+O(p^{-4/3})\)；不能把所有素数的一次项绝对相乘。
同一证明其实适用于任意固定 \(\Re u,\Re v\ge b>\log2/\log3\)，
常数可依赖 \(b\)。这里保留 \(2/3\) 是为了与原目标对应。

在共轭点 \((u,v)=(\sigma+it,\sigma-it)\)，还严格有

\[
 H_p=1-\frac{p^{-2\sigma}}{|1-p^{-\sigma-it}|^2}>0\quad(p\ge3),
 \qquad G_{\rm odd}(\sigma+it,\sigma-it)>0. \tag{7}
\]

若 \(\rho=\beta+i\gamma\) 是重数 \(m\) 的零点，\(\beta>2/3\)，令
\(a_\rho=\zeta^{(m)}(\rho)/m!\ne0\)。则 \(D_{\rm odd}\) 在
\((\rho,\bar\rho)\) 的最高混合 Laurent 系数是

\[
 \boxed{c_\rho=\frac{G_{\rm odd}(\rho,\bar\rho)}{|a_\rho|^2}>0,}
 \quad
 D_{\rm odd}=\frac{c_\rho+O(|u-\rho|+|v-\bar\rho|)}
 {(u-\rho)^m(v-\bar\rho)^m}. \tag{8}
\]

所以额外奇数限制下，互素 Euler 因子不会消去该混合极点。

**额外奇数限制不是原和的免费推论。** 对任意有限支撑权 \(B(r,s)\)，
记 \(Q[B]=\sum_{(r,s)=1}\mu(r)\mu(s)B(r,s)\)，\(Q_{\rm odd}\) 加奇数限制。
平方自由性和 \((r,s)=1\) 精确给出

\[
 \boxed{Q[B]=Q_{\rm odd}[B]
       -Q_{\rm odd}[B(2\,\cdot,\cdot)]
       -Q_{\rm odd}[B(\cdot,2\,\cdot)].} \tag{9}
\]

两变量不能同时为偶数。Mellin 端相应乘子是
\(1-2^{-u}-2^{-v}\)，在共轭零点处为
\(1-2^{1-\beta}\cos(\gamma\log2)\)，它可能为零或为负。上述局部代数
没有排除这一可能，也没有声称存在满足它的实际零点。三个奇数分量的
权重和支撑不同，不能从整个带符号和的上界推出每一个分量的同样上界。

## 3. 实际过渡 profile 有严格正实部的固定子区间

取非负非零实函数 \(\Phi\in C_c^\infty((1,2)^2)\)，沿用上一笔记的 profile

\[
 J(z):=\Re\mathcal I_{-z}[\Phi]
 =\frac1{|z|}\iint\Phi(a,b)\cos(2\pi ab/z)\,da\,db. \tag{10}
\]

当 \(32\le|z|\le64\) 时，\(|2\pi ab/z|<\pi/4\)，从而

\[
 J(z)\ge\frac{1}{\sqrt2|z|}\iint\Phi>0. \tag{11}
\]

取偶、非负、非零 \(\chi\in C_c^\infty(\{32<|z|<64\})\)，令
\(k(z)=\chi(z)J(z)\)。则 \(k\) 是非负偶函数且
\(\kappa_0:=\int k(z)\,dz>0\)。该子区间的 \(c=-z\) 仍在固定紧集，
因此上一笔记统一过渡公式确实适用；它没有使用任意指定的 quotient
Fourier 频率。核实部为正不使 Möbius 乘积为正，例如
\(\mu(15)\mu(17)=-1\)。这里也没有将完整物理和替换为其一个子和。

## 4. 带原权重的薄带 Mellin 变换

为避免与原 \(h\) 变量尺度混淆，记位移尺度为 \(Y\)。取

\[
 R=S=X,\quad Y=X^{2/3},\quad HL=XY,\quad
 \delta=Y/X=X^{-1/3}. \tag{12}
\]

在 \(p=q=1\) 的 packet 中，\(z=(r-s)s/(HL)\)。选非负
\(U,V\in C_c^\infty((1,2))\)，且 \(UV\not\equiv0\)，使用合法分离核
\(F_s(x,a,b)=U(x)V(s/X)\Phi(a,b)\)。上一笔记 (15) 主项的实部权重精确是

\[
 B_\delta(x,y)=yU(x)V(y)k\!\left(\frac{(x-y)y}{\delta}\right),
 \qquad x=r/X,\quad y=s/X. \tag{13}
\]

特别保留 \(U(r/X)\)，没有冻结成 \(U(s/X)\)。乘原归一化
\((HL/(Xs))(s^2/(HL))\) 得到的前因子确为 \(s/X=y\)。
定义整个双变量 Mellin 变换

\[
 \mathcal B_\delta(u,v)=\iint B_\delta(x,y)x^{u-1}y^{v-1}\,dx\,dy.
 \tag{14}
\]

固定 \(y\)，用 \(x=y+\delta z/y\) 得 \(dx=\delta\,dz/y\)。这正好抵消
\(B\) 中的 \(y\)，所以

\[
 \mathcal B_\delta(u,v)=\delta\iint
 U(y+\delta z/y)V(y)k(z)
 (y+\delta z/y)^{u-1}y^{v-1}\,dy\,dz. \tag{15}
\]

取 \(u=\rho,v=\bar\rho\)，对 \(f(x)=U(x)x^{\rho-1}\) 在 \(x=y\)
作一阶 Taylor。\(k\) 偶性使一次项精确为零，故

\[
 \boxed{\mathcal B_\delta(\rho,\bar\rho)
 =\delta\kappa_0 v_\beta+O_{U,V,k}(\delta^3(1+|\rho|)^2),\qquad
 v_\beta=\int U(y)V(y)y^{2\beta-2}\,dy>0.} \tag{16}
\]

该误差对 \(2/3\le\beta\le1\) 一致，\(0<\delta\le\delta_0\)，其中
固定 \(\delta_0\) 保证 Taylor 线段位于正常数紧集。对固定零点这是
\(O_\rho(\delta^3)\)。**偶性带来的改善仅用于这个连续测试变换**；原
整数和有 \(\mu(s+w)\)，不能在那里删除一次项并擅自冻结原权重。

也可直接获得带高度条件的正实部：在全部支撑上
\(|\log(x/y)|\le128\delta\)（取 \(\delta\le1/128\)）。若
\(|\gamma|\delta\le1/512\)，则
\(\cos(\gamma\log(x/y))\ge\cos(1/4)>0\)。结合 \(UV\) 的一个正内部区间，
缩小固定 \(\delta_0\) 后得到

\[
 \Re\mathcal B_\delta(\rho,\bar\rho)\ge c_{U,V,k}\delta>0.
 \tag{17}
\]

这是可选择 \(X^{1/3}\ge512|\gamma|\) 时的局部响应，不声称原 AFE/QCT
允许任意选择一个依赖零点的核或尺度。

## 5. 共轭留数的大小：已证明的是局部量，不是全和下界

为简洁先假设 \(\rho\) 是简单零点。对双变量亚纯微分形式
\(D_{\rm odd}(u,v)X^{u+v}\mathcal B_\delta(u,v)\,du\,dv\)，局部双留数精确为

\[
 \mathcal R_\rho(X)=c_\rho X^{2\beta}\mathcal B_\delta(\rho,\bar\rho).
 \tag{18}
\]

由 (16)，对固定 \(\rho\) 和 (12) 的尺度，

\[
 \boxed{\Re\mathcal R_\rho(X)
 =c_\rho\kappa_0v_\beta X^{2\beta-1/3}
  +O_\rho(X^{2\beta-1}).} \tag{19}
\]

所以这个单独信号在 \(\beta>2/3\) 时超过 \(X\) 的幂次；在
\(X=T^3\) 记号中是 \(T^{6\beta-1}\)，\(\beta=2/3\) 正好对应 \(T^3\)。
这只说明“若能无损隔离并控制其余项”，该实际核具有所需的检测尺度。

这里的未对称 \(\mathcal B_\delta(\rho,\bar\rho)\) 通常不是实数，即使
\(U=V\) 也不能默认其虚部为零。对有限算术和可精确把 \(B(x,y)\) 换成
\((B(x,y)+B(y,x))/2\)，因为其系数和奇数条件均对称；新 Mellin 值就是
原值的实部。这是算术双和的对称化，不另外宣称原 AFE 的每个核都对称。

任意固定重数 \(m\) 也可处理：把 (8) 的全纯分子及 (15) 在零点附近
展开。\(\mathcal B_\delta\) 的每个固定阶 \(u,v\) 导数都是
\(O_\rho(\delta)\)，其领先展开同样有 \(O_\rho(\delta^3)\) 余项。
最高次 \(\log X\) 来自对 \(X^{u+v}\) 各求 \(m-1\) 次导数。因此

\[
 \Re\mathcal R_\rho(X)\sim
 \frac{c_\rho\kappa_0v_\beta}{((m-1)!)^2}
 X^{2\beta-1/3}(\log X)^{2m-2}. \tag{19a}
\]

对于 \(m\ge2\)，其余 Laurent 项至多给
\(O_\rho(X^{2\beta-1/3}(\log X)^{2m-3})\)，加上
\(O_\rho(X^{2\beta-1}(\log X)^{2m-2})\) 的薄带展开误差。
\(m=1\) 直接使用 (19)。这仍然只计算一个孤立的局部双留数。

**不作如下推论：**
\(Q_{\rm odd}[B_\delta(\cdot/X,\cdot/X)]\gg X^{2\beta-1/3}\)。要作
这种推论，仍必须从原绝对收敛双 Mellin 积分作合法移线，控制所有其他
零点、混合零点对、水平边及剩余积分，并处理 (9) 中的真实奇偶分量。
单个正局部留数不证明它在完整有符号和中不可消去。

## 6. 不能遗漏的 Mellin 高度密度

[Mellin 反演](https://dlmf.nist.gov/2.5) 在 \(\sigma>1\) 给出严格恒等式

\[
 Q_{\rm odd}[B_\delta(\cdot/X,\cdot/X)]
 =\frac1{(2\pi i)^2}\int_{(\sigma)}\int_{(\sigma)}
 D_{\rm odd}(u,v)X^{u+v}\mathcal B_\delta(u,v)\,du\,dv. \tag{20}
\]

这里仅 (20) 的右线表示是对原有限权算术和的已证反演，没有跨过零点。
原支撑还允许一个精确的中心化。记
\(A_{\rm odd}(u)=1/(\zeta(u)(1-2^{-u}))\)。对 \(X\ge1\)，在 (20)
的右线积分中可将 \(D_{\rm odd}\) 替换为

\[
 D_{\rm odd}^{\circ}(u,v)
 :=D_{\rm odd}(u,v)-A_{\rm odd}(u)-A_{\rm odd}(v)+1. \tag{20a}
\]

因为后三项分别只含 \(s=1\)、\(r=1\) 和 \(r=s=1\) 的系数，而
\(B_\delta(r/X,s/X)\) 在这些轴上均为零。这保留了可用于下一步耦合
估计的精确消去，不是额外的幂次上界。减去单变量极点也不能消去 (8)
中两变量均有负幂的最高混合项。

取 \(x=y(1+\delta a)\)，(14) 变成

\[
 \delta\iint y^{u+v}(1+\delta a)^{u-1}
 U(y(1+\delta a))V(y)k(y^2a)\,da\,dy.
\]

支撑中的 \(a,y\) 在固定紧集。虚部相位分成
\((t+t')\log y+t\log(1+\delta a)\)，可分别分部积分。因此对实部所在
固定紧集、任意固定 \(N,M\)，

\[
 \boxed{|\mathcal B_\delta(\sigma+it,\sigma'+it')|
 \ll_{N,M}\delta(1+|t+t'|)^{-N}(1+\delta|t|)^{-M}.} \tag{21}
\]

这在 \(t\approx-t'\) 方向允许长达 \(\delta^{-1}=X^{1/3}\) 的高度；
不能把薄带的 \(\delta\) 因子直接算成净收益而忘记此密度。
准确地说，(21) 给出未加权 \(L^1\) 范数 \(\iint|\mathcal B_\delta|\ll1\)，
以及对任意固定 \(A\ge0\)，
\(\iint(1+|t|+|t'|)^A|\mathcal B_\delta|\ll_A\delta^{-A}\)。
未加权 \(L^1\) **没有**再额外损失一个 \(\delta^{-1}\)；高度密度恰好
抵消了点态幅度中的 \(\delta\)。

具体地，对任何固定 \(\sigma\ge2/3\)，若该竖直线上的下列负矩有限，则
(6)、(21)、\(2ab\le a^2+b^2\) 给出对应**竖线积分本身**的界

\[
 |\mathcal V_\sigma(X)|\ll X^{2\sigma}\delta
 \int_{\mathbb R}\frac{(1+\delta|t|)^{-M}}{|\zeta(\sigma+it)|^2}\,dt.
 \tag{22}
\]

证明中把 \(\tau=t+t'\) 积分掉，选 \(N>M+2\)，并用
\((1+\delta|\tau-t|)^{-M}\le(1+\delta|\tau|)^M(1+\delta|t|)^{-M}\)。
若竖线经过零点，不能假装这个负矩有限；而当 \(\sigma\le1\) 时，
\(\mathcal V_\sigma\) 不自动等于 (20) 的算术和。

即便额外假设该负矩只有正常长度 \(O(\delta^{-1}(\log X)^C)\)，
(22) 也仅给 \(X^{2\sigma}(\log X)^C\)。在 \(\sigma=2/3\) 是
\(X^{4/3}\)，不是目标 \(X\)。这是**绝对值方法所给的上界账本**，不是
对实际积分的下界或不可能性定理。若要借此路线前进，需要继续利用
\(t+t'\) 与径向权的有符号耦合，或建立真正的单零点隔离；不能以普通
一因子负矩及移线口号宣布闭合。

## 7. 结论边界与可继续攻击的对象

本轮得到的具体结论是 (1)–(9) 的完整 Euler/奇偶结构、(11) 的真实核
正实部、(16)–(19) 的局部共轭零点响应及 (21) 的精确 Mellin 高度尺度。
它们排除了“互素容斥或核的消失矩自动抹掉一切零点信号”这一捷径。

下一步有两个明确的数学问题：

- 能否在 (20) 的**原耦合积分**中估计高 Mellin 模式，不先丢掉径向振荡？
- 能否针对假设零点隔离 (18)，同时证明其余项无法抵消，且不暗中假设
  同强度的 Möbius 上界？奇数子和以及 (9) 的两个伸缩分量必须明示处理。

这没有证明上述任一缺失估计，也没有证明 eventual `14/17`、全局
`14/17` 或 `2/3`。有限检查脚本为
`scripts/check_primitive_euler_zero_response.py`；连续解析结论不由有限
样本代替，脚本不假装发现或计算了实部超过 `2/3` 的实际零点。

### English scope summary

The exact primitive-pair Euler product has a normally convergent correction.
After explicitly excluding 2, this correction is uniformly nonvanishing
in the two-thirds poly-half-plane and preserves a positive conjugate-zero
Laurent coefficient. A legitimate physical transition subpacket has a
nonzero Mellin response of size delta, with the original weight and
Jacobian retained. The corresponding local simple-zero residue has size
X^(2 beta - 1/3); no global Omega bound follows without contour, other-zero,
and parity control. Mellin localization also reveals a delta-inverse
height range, which cannot be counted as free cancellation. All zero-free
objectives and the required signed arithmetic estimate remain open.
