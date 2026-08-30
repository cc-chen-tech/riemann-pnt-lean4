# Conrey 完全和：用 Stepanov 方法补齐奇素数 Weil 核心

先说结论：本节在纸面上证明奇素数 p、p 不整除 ab 时
`|K_p(a,b)| <= 2 sqrt(p)`，补上前一篇留下的唯一素数核心。
与已经证明的素数幂、gcd 约化和 CRT 合起来，得到实际 Type I
使用的任意模数完全 Kloosterman 和界。这里不把曲线点数估计、
有限域 RH 或素数 Weil 定理另列为假设，而是给出所需点数界的构造证明。
DI 谱估计仍是外部输入；这不是完整 Conrey 的独立自证或新增 Lean 定理。

这是冻结源 `8cff6c6747e9402930209b42552390440077b3f2` 之后的
独立数学增量。没有修改冻结分支、Lean、Lake 或条件契约。
方法沿用经典 Stepanov 路线，不声称数学新颖性。
为便于逐项核验，本节自行选择有明确取整的辅助参数，保留较松的
`12m sqrt(Q)` 曲线误差，并用有限几何级数和 Cesaro 平均证明幂和引理。

## 1. 输入输出、符号与初等有限域事实

固定奇素数 p，a,b 为 F_p 的非零元素。定义

\[
 \psi(t)=\exp(2\pi i\widetilde t/p),\qquad
 K_n(a,b)=\sum_{x\in F_{p^n}^{\times}}
       \psi\bigl(\operatorname{Tr}_{F_{p^n}/F_p}(ax+b/x)\bigr).
 \tag{extension-sum}
\]

其中 `tilde t` 为任意整数代表；取逆始终在有限域中进行。
本节下标 n 表示扩域次数，不表示模数。仅 n=1 时
`K_1(a,b)` 等于[前篇](2026-08-31-conrey-kloosterman-prime-power-proof.md)
按模数记号写的 `K_p(a,b)`。没有把 F_(p^n) 与 Z/(p^n) 混用。

用到的有限域基础可以直接从多项式分解说明：在 F_p 的代数闭包中，
`X^(p^n)-X` 导数为 -1，因而有恰好 p^n 个互异根。
Frobenius 恒等式使根集合对加、减、乘、非零取逆封闭，故它就是
Q=p^n 元的域。对其中任意元素，Frobenius 轨道长度 d 整除 n；
轨道乘积 `product_(i<d)(X-x^(p^i))` 系数固定于 Frobenius，
所以在 F_p 中。它是该元素的最小多项式：任意 F_p 多项式若含 x
为根，就含整个轨道。由此，首一不可约多项式的根在扩域中的枚举
是精确且不重复的；次数 d 整除 n 的不可约多项式恰好贡献 d 个根。

迹在这里显式定义为

\[
 \operatorname{Tr}(z)=z+z^p+\cdots+z^{p^{n-1}}.
 \tag{trace}
\]

它取值于 F_p，是 F_p 线性的，而且满射。最后一点不依赖
`Tr(1)=n` 非零：迹多项式非零，次数 p^(n-1)<p^n，所以不能在整个
F_(p^n) 上恒为零；非零线性映射到一维 F_p 必满。
因此其核大小为 p^(n-1)。映射 `z -> z^p-z` 的核恰为 F_p，
像大小也为 p^(n-1)；由迹的望远镜消去，像包含于迹核，所以二者相等。
故对每个 t，有

\[
 \#\{z\in F_{p^n}:z^p-z=t\}
 =p\,1_{\operatorname{Tr}(t)=0}
 =\sum_{j\in F_p}\psi(j\operatorname{Tr}(t)).
 \tag{trace-fiber}
\]

最后的等式仅为 p 次单位根的有限几何级数正交性。

## 2. 二次生成多项式：先证明恒等式，不假设根的模

对常数项非零的首一多项式
`h=X^d+c_1 X^(d-1)+...+c_d`，d>=1，令

\[
 w(h)=\psi\left(-ac_1-b\frac{c_{d-1}}{c_d}\right).
 \tag{monic-weight}
\]

当 d=1 时 `c_(d-1)=c_0=1`。另外定义 w(1)=1，常数项为零的
首一多项式权重为零。非零常数项时，两个量分别是根之和及逆根之和
乘上 a、b；也可直接比较乘积的首项后系数和一次项系数。
这证明 `w(hh')=w(h)w(h')`，包括有零常数项的情况。

在 C[[T]] 中定义

\[
 L(T)=\sum_{h\text{ monic}} w(h)T^{\deg h}.
\]

这是形式幂级数，每个系数只有有限项。各次数系数可完全算出：

- 次数0：系数为1。
- 次数1：将 `c_1=-x` 换元，系数为 `K_1(a,b)`。
- 次数2：对 `c_2 != 0`，内层求和为
  `sum_(c_1 in F_p) psi(-(a+b/c_2)c_1)`。
  唯一非零情形 `c_2=-b/a`，此时内层为 p。因此系数为 p。
- 次数 d>=3：`c_1` 与 `c_(d-1)` 是独立系数；由于 a 非零，
  单独对 `c_1` 的求和已为零。

所以精确地有

\[
 L(T)=1+K_1(a,b)T+pT^2=(1-\alpha T)(1-\beta T),
 \quad \alpha+\beta=-K_1(a,b),\quad\alpha\beta=p.
 \tag{quadratic-L}
\]

此处仅使用复二次多项式分解，还没有使用任何根大小估计。
由 F_p[X] 唯一分解，形式 Euler 乘积及对数导数给出

\[
 \frac{TL'(T)}{L(T)}
 =\sum_{P\text{ monic irreducible}}\deg(P)
      \sum_{r\ge1} w(P)^r T^{r\deg P}.
 \tag{formal-euler}
\]

P=X 的权重为零，可直接排除。对 d=deg(P) 整除 n、P 的根 x，
由上节轨道枚举及迹公式，

\[
 w(P)^{n/d}
 =\psi\bigl(\operatorname{Tr}_{F_{p^n}/F_p}(ax+b/x)\bigr).
\]

这里迹在一个长度 d 的轨道上重复 n/d 次；即使 p 整除 n/d，
等式也仍成立。将不可约多项式的 d 个根展开，(formal-euler)
的 T^n 系数就是 `K_n(a,b)`。另一方面 (quadratic-L) 给出

\[
 K_n(a,b)=-(\alpha^n+\beta^n)\qquad(n\ge1).
 \tag{companion-powers}
\]

负号与实际正号定义的 Kloosterman 和相符。
这里既不需要无限级数解析收敛，也不需要先证明任何 Weil 界。

## 3. 所需的粗曲线点数界及其完整构造

**引理。** 设 F 为奇特征、Q 元有限域，f 属于 F[X]，次数 m>=1，
且 f 在代数闭包上不是平方。若 `Q>=64m^2`，则仿射点数

\[
 N_f=\#\{(x,y)\in F^2:y^2=f(x)\}
 \quad\text{满足}\quad |N_f-Q|\le12m\sqrt Q.
 \tag{rough-curve}
\]

以下证明不使用有限域曲线 RH、Hasse--Weil 或 character-sum 界。

### 3.1 Hasse 系数取代普通高阶求导

定义 `D_k h(X)` 为多项式 `h(X+U)` 的 U^k 系数。
因而 `D_k X^r=binom(r,k)X^(r-k)`，并有精确乘积公式
`D_k(hh')=sum_(i=0)^k D_i(h)D_(k-i)(h')`。
在 x 处前 ell 个 Hasse 系数全部为零，当且仅当
`(X-x)^ell` 整除 h；这直接来自 h(x+U) 的系数展开。
这些结论在 ell>=p 时也有效，不涉及除以 k!。

对 Q 为特征的幂，`(X+U)^Q=X^Q+U^Q`，故

\[
 D_k(h(X)X^{jQ})=(D_k h(X))X^{jQ}\quad(0\le k<Q).
 \tag{frobenius-hasse}
\]

这避免了在特征 p 下非法除以一个可能被 p 整除的整数 k。
另一个直接来自乘积公式的事实是：若 r>=k、deg(h)<=D，则

\[
 D_k(hf^r)=f^{r-k}h_k,\qquad
 \deg h_k\le D+k(m-1).
 \tag{factor-hasse}
\]

证明：在 k 阶系数展开的每项中，r 个 f 因子最多有 k 个被取正阶
Hasse 系数，所以至少保留 r-k 个 f。除去这些因子后，次数至多
`D+rm-k-(r-k)m=D+k(m-1)`。h 到 h_k 的对应是线性的。

### 3.2 整数参数、未知数和方程数

由于 Q>m，可平移变量使 f(0) 非零；点数、次数和非平方性均不变。
**在平移后**作如下构造，不需要声称任意给定的系数表示在平移下不变。
令

\[
 c=(Q-1)/2,\quad D=c-m,\quad
 \ell=\lfloor\sqrt Q\rfloor,\quad
 J=\lceil\ell/2\rceil+2m,\quad g=f^c.
 \tag{integer-parameters}
\]

这些是整数，D>=0、1<=ell<Q。对任意固定 `epsilon in {1,-1}`，考虑

\[
 R(X)=f(X)^\ell\sum_{j=0}^{J-1}
             \bigl(u_j(X)+v_j(X)g(X)\bigr)X^{jQ},
 \qquad \deg u_j,\deg v_j\le D.
 \tag{auxiliary-polynomial}
\]

共有 `A=2J(D+1)` 个系数未知数。
由 (frobenius-hasse) 和 (factor-hasse)，对 0<=k<ell，

\[
 D_kR=f^{\ell-k}\sum_{j<J}(u_{jk}+v_{jk}g)X^{jQ},
 \quad \deg u_{jk},\deg v_{jk}\le D+k(m-1).
\]

令下列多项式恒为零：

\[
 H_k(X)=\sum_{j<J}(u_{jk}(X)+\epsilon v_{jk}(X))X^j=0
 \qquad(0\le k<\ell).
 \tag{linear-conditions}
\]

每个 H_k 的次数至多 `D+k(m-1)+J-1`，故这至多是

\[
 B=\ell(D+J)+(m-1)\ell(\ell-1)/2
\]

个齐次线性方程。这里精确保留了次数加一的系数计数。
检查未知数严格多于方程：

\[
 \begin{aligned}
 A-B
 &=J(2D+2-\ell)-\ell D-(m-1)\ell(\ell-1)/2\\
 &\ge 2mQ-\frac m2\ell^2-\frac{3m-1}{2}\ell+2m-4m^2\\
 &\ge\frac32mQ-\frac32m\ell-4m^2>0.
 \end{aligned}
 \tag{dimension-surplus}
\]

首个不等式用 `J>=ell/2+2m` 及 `2D+2-ell=Q+1-2m-ell>0`；
第二个用 ell^2<=Q。最后，Q>=64m^2、m>=1 蕴含
`ell<=Q/8` 和 `4m^2<=mQ/16`，所以末行至少为 `(5/4)mQ>0`。
有限维线性代数于是给出一组不全为零的 u_j,v_j 满足所有方程。

### 3.3 非零性：不能把非零系数误当成非零辅助多项式

还须证明所得 R 本身不为零。否则除以非零 f^ell，取最小的
`j_0` 使 u_(j_0),v_(j_0) 不全为零，再除以 X^(j_0 Q)，得到
`U+Vf^c=0`，其中

\[
 U=\sum_{j\ge j_0}u_jX^{(j-j_0)Q},\qquad
 V=\sum_{j\ge j_0}v_jX^{(j-j_0)Q}.
\]

平方并乘以 f，得 `U^2 f=V^2 f^Q`。因为 F 有 Q 个元素，
`f(X)^Q=f(X^Q)`，所以模 X^Q 得到

\[
 u_{j_0}^2 f\equiv v_{j_0}^2 f(0)\pmod {X^Q}.
\]

两边次数均严格小于 Q：`2D+m=Q-1-m<Q`，且 `2D<Q`。
因此这是多项式相等。若任一 u_(j_0),v_(j_0) 为零，整域性质及
f(0) 非零迫使另一项也为零，与 j_0 的选择矛盾。
否则等式说 `f=f(0)(v_(j_0)/u_(j_0))^2`。
在代数闭包中按每个线性因子取重数，这迫使 f 的每个根重数为偶数；
常数也有平方根，所以 f 是多项式平方，仍矛盾。故 R!=0。

### 3.4 重数计数及上下两侧

令

\[
 S_\epsilon=\{x\in F:f(x)=0\ \text{或}\ f(x)^c=\epsilon\}.
\]

若 f(x)=0，R 的 f^ell 因子已给出至少 ell 重零点。
否则利用 x^Q=x、g(x)=epsilon 和 (linear-conditions)，得到
`D_k R(x)=f(x)^(ell-k)H_k(x)=0`，对所有 k<ell 成立。
因此每个 S_epsilon 点都是至少 ell 重零点。R 非零，故

\[
 \ell |S_\epsilon|\le\deg R
 \le m\ell+D+cm+(J-1)Q
 \le Q\ell/2+(5m/2)Q+m\ell.
 \tag{degree-count}
\]

最后一步用 `J<=ell/2+2m+1/2` 和 `D+cm=(m+1)c-m`。
所以 `|S_epsilon|<=Q/2+(5m/2)Q/ell+m`。

记 n_0 为 f 的 F 中互异根数，n_+、n_- 分别为 f(x)^c=1、-1
的 x 的个数。非零域元素 t 满足 t^(Q-1)=1，故 t^c 为 ±1。
而平方映射在 F^times 上每个像恰有两个原像，因此非零平方恰有 c 个；
它们都满足 t^c=1，后者次数为 c，不能有更多根。
所以平方判别不需要额外引用 character-sum 定理，且

\[
 n_0+n_++n_-=Q,\qquad N_f=n_0+2n_+,
 \qquad |S_\pm|=n_0+n_\pm.
\]

上界来自 `N_f<=2|S_+|`，下界来自
`N_f>=2n_+=2(Q-|S_-|)`。结合 (degree-count)，

\[
 |N_f-Q|\le5mQ/\ell+2m\le12m\sqrt Q,
\]

因为 `ell=floor(sqrt(Q))>=sqrt(Q)/2`、sqrt(Q)>=1。
这证明 (rough-curve)。注意这里估计的是仿射点，不添加或漏减无穷远点。

## 4. 实际 Kloosterman 幂和对应的显式曲线

在 F_(p^n) 上考虑

\[
 z^p-z=ax+b/x,\qquad x\ne0.
 \tag{artin-schreier}
\]

对 x 求和并使用 (trace-fiber)，它的解数 N_n 精确等于

\[
 N_n=p^n-1+\sum_{j\in F_p^\times}K_n(ja,jb).
 \tag{point-sum}
\]

乘以 x 后，(artin-schreier) 为
`ax^2-(z^p-z)x+b=0`。写 t=z^p-z，由明确的双射

\[
 (x,z)\longmapsto(z,v=2ax-t),\qquad
 (z,v)\longmapsto(x=(v+t)/(2a),z)
\]

其解数等于 `v^2=(z^p-z)^2-4ab` 的仿射点数。
逆映射中 x 不会为零：若 v=-t，则 v^2=t^2 与 ab!=0 矛盾。
所以没有忽略一个需额外补回的 x=0 分支。

多项式

\[
 f(Z)=(Z^p-Z)^2-4ab
 \tag{actual-curve}
\]

次数 m=2p；导数为 `-2(Z^p-Z)`。若 f 与其导数有公共根，
则同时有 Z^p-Z=0 及 4ab=0，不可能。因此 f 在代数闭包上
平方自由，特别不是平方。它在每个扩域中仍满足同一个非平方条件。
当 `p^n>=256p^2=64(2p)^2` 时，(rough-curve) 给出

\[
 |N_n-p^n|\le24p\,p^{n/2}.
 \tag{extension-point-bound}
\]

每个 j!=0 的系数 ja,jb 都非零，故第2节给出两个复数
alpha_j,beta_j，满足 alpha_j beta_j=p，及
`K_n(ja,jb)=-(alpha_j^n+beta_j^n)`。于是

\[
 \left|\sum_{j\in F_p^\times}(\alpha_j^n+\beta_j^n)\right|
 =|p^n-1-N_n|\le(24p+1)p^{n/2}
 \tag{joint-power-bound}
\]

对所有充分大的整数 n 成立。常数可以依赖固定 p，但不依赖 n。
特别保留了 (point-sum) 中的 -1；没有把仿射计数主项直接写成 p^n。

## 5. 幂和不能长期掩盖超出平方根的根

**引理。** 对有限个复数 omega_1,...,omega_r 和 A,B>0，若
`|sum_j omega_j^n|<=A B^n` 对所有充分大整数 n 成立，则每个
`|omega_j|<=B`。重复根必须按重数计入。

证明：反设最大模 M>B，把所有根除以 M。模严格小于1的有限部分
幂和趋于0；假设又给出整个归一化幂和趋于0，所以模恰为1的
非空子列 z_1,...,z_s 满足 `u_n=sum_i z_i^n -> 0`。
但

\[
 \frac1N\sum_{n=1}^N|u_n|^2
 =\sum_{i,k}\frac1N\sum_{n=1}^N(z_i\overline{z_k})^n
 \longrightarrow \#\{(i,k):z_i=z_k\}\ge s>0.
 \tag{cesaro-no-cancellation}
\]

内层在 z_i=z_k 时为1；否则由有限几何级数，其绝对值至多
`2/(N |1-z_i conjugate(z_k)|)`，趋于0。
另一方面 `u_n -> 0` 迫使其平方模的 Cesaro 平均趋于0，矛盾。
最后这一步由把有限初段除以 N、尾段用任意 epsilon 上界即可证明。
引理得证；不需要复解析延拓或同时逼近定理。

将引理用于 (joint-power-bound) 中的 `2(p-1)` 个根，取
`A=24p+1,B=sqrt(p)`，得到所有根模不超过 sqrt(p)。
又因每对根乘积恰为 p，每个根的模都必须恰为 sqrt(p)。特别 j=1 时，

\[
 \boxed{|K_1(a,b)|=|\alpha_1+\beta_1|\le2\sqrt p.}
 \tag{prime-weil-proved}
\]

由于第1节下标约定，框中就是实际整数模 p 完全和的素数 Weil 界。
它对每个奇素数 p、p 不整除 ab 成立；并没有要求基础域 p 很大。
第4节只要求扩域次数 n 足够大，第5节正好只使用这一条件。

## 6. 回接前篇和 Conrey 主线的准确边界

前篇已经证明：本原高次奇素数幂的驻相界、2的幂的退化处理、
一般参数的精确 gcd 约化，以及两个系数都带逆元扭曲的 CRT。
现在 (prime-weil-proved) 也覆盖 gcd 约化后落到奇素数模数的情形。
因此无需再假设 Weil 定理，合起来对全部 q>=1、整数 a,b 得到

\[
 \boxed{|K_q(a,b)|\le\tau(q)\sqrt q\sqrt{\gcd(a,b,q)}}.
 \tag{actual-all-moduli}
\]

此处重新回到前篇的**模数下标**，`K_1(a,b)=1`。
该式是[实际 Möbius Type I 估计](2026-08-31-conrey-actual-mobius-type-i.md)
使用的同一个完全和估计；至此其 Weil 输入已具备展开的纸面证明。

仍未完成的部分必须分开报告：

- Deshouillers--Iwaniec 谱估计没有在本节证明，仍是 Conrey 实际余项链的外部输入。
- 本篇有限域、Hasse 系数、辅助多项式和生成函数证明尚未新增为 Lean 原生定理。
- 既有的经典输入下严格超过2/5单零点纸面应用链，不等于不依赖经典输入的
  原生终点；也不等于本仓库已经通过最终源 SHA 的完整 Lean 集成验收。
- 本节与 zeta23 无关；不通过另一条定理桥关闭目标。

## 7. 来源核对及有意重写的细节

经典路线见 [Iwaniec--Kowalski, Sections 11.5--11.7,
pp.278--288](https://people.math.ethz.ch/~kowalski/ik-ant-exp-sums.pdf)。
已逐页查看本地 PDF 对应第12--22页；它的 S 定义在实际 K 前多一个负号。
本节全程固定实际正号 K，并由系数计算得到 `L=1+K_1 T+pT^2`。

为免将来源中的略写直接搬入证明，本节作以下可核验处理：

1. p.284 的 Hasse-Frobenius 论证包含整数比值式。
   当求导阶数被 p 整除时不能在 F 中按该分式直接运算；第3.1节
   改用 `(X+U)^Q=X^Q+U^Q` 的多项式恒等式。
2. p.285 的双变量中间表达出现 `Y^(jQ)`，而在 `Y=X^Q` 的替换下
   原辅助项需要 `Y^j`。本节直接证明 (frobenius-hasse)，不依赖这行。
3. p.286 显示的 J 公式未写取整。本节不用该参数值，另取
   `J=ceil(ell/2)+2m`，重新给出严格维数盈余和次数上界。
4. p.288 从 n>=1 的幂和生成函数写到 `sum_j 1/(1-omega_j z)`
   时少了常数项修正；正确形式应减去根数，或改用
   `sum_j omega_j z/(1-omega_j z)`。第5节完全用有限 Cesaro 论证。
5. p.288 的扩域阈值只写 `q^n>16q`，不直接满足前述
   `Q>4m^2,m=2q` 的条件。本节明确用自己的阈值 `p^n>=256p^2`；
   放宽固定阈值不影响只需充分大 n 的幂和论证。

这些核对不改变经典结论，也不构成新定理的优先权声明。
本节所需的估计均已在上文推导，不以“来源结论正确”代替局部证明。

## 8. 验收范围

本次增量只有本篇 Markdown。数学验收应逐项检查
`dimension-surplus`、辅助多项式非零性、迹的满射、实际仿射双射、
生成函数的负号及幂和的重复根处理；数值抽查不能代替这些证明。

提交后必须在最终 SHA 上重跑 Python 回归、目标分类、chain-gap
和 diff 检查，日志路径记录在 PR；这些仅是仓库回归证据。
在独占资源窗口明确放行前，不启动 Lean/Lake，也不把旧 Lean 日志
或本篇无 Lean 变更当作最终原生定理的验收证据。
