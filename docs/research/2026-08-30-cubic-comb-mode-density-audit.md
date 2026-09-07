# 三次倒数相位：保留 Jacobian 的全 Poisson 模式估计

通俗地说：小模数比例产生了很多 Fourier 模式，但每个模式也带着一个小的
变换因子。本笔记把两者一起估计，证明一个真实的局部 Möbius 求和界，避免
在“小于整数间距”的区间上直接使用连续密度。这推进了算术部分；它不是
完整长 mollifier 渐近式，更不是 `14/17` 或 `2/3` 零点界。

## 1. 复用的结果与本次范围

已读取 worktree `audit-mwkf-exact-20260824`、commit `7cc472d4` 的
`docs/research/2026-08-25-mwkf-alternative-routes-spike.md`，特别是
§§4.109zjace–4.109zjacec、4.109zjaced000f–h。旧稿在小
\(A<D(\log T)^{-K}\) 时采用原变量密度估计，在其余范围才用
\(c\)-Poisson 和三次倒数相位。这里证明：**对下述完整声明的光滑局部模型，
可以统一使用全模式估计，不需要这个小 \(A\) 分支。**

外部算术输入来自 Matomäki–Radziwiłł–Shao–Tao–Teräväinen，
[Higher uniformity II，Theorem 1.1(i)](https://arxiv.org/html/2411.05770v2#S1.Thmtheorem1.1)。
需要的是该定理对固定次数多项式相位的 supremum，以及式 (1.4) 对区间内
任意等差数列的 maximal 范数。不能只引用某个预先给定稀疏起点网格上的
“几乎处处”结论。

本笔记未修改该旧 worktree。原稿对完整物理系数回代、长余因子密度项以及
变换尾的论证仍需分别核查，不由本局部引理自动解决。

后续[互素与物理归一化审计](2026-08-30-coprime-comb-physical-normalization.md)
进一步处理固定互素模数、密度乘子和完整卷积尾，并定位旧稿短余因子
嵌入中 \(HL\) 与 \(HL/S\) 的差异。本文局部定理不提供这一个额外的
\(S^{-1}\) 幅度，不能以它宣布全局渐近式成立。

## 2. 一个全模式局部定理

固定

\[
 \epsilon_0=1/1000,\qquad \nu=17/50,\qquad
 1/2\le u\le3,\quad 0\le p\le2u,
\]

并令 \(T\to\infty\)、\(S=T^u\)。设 \(A,e,r\) 为正整数，

\[
 1\le A\le S,\quad e\le T^{\epsilon_0},\quad
 D=S/e,\quad r\le D^{\epsilon_0},\quad X=D/r.
 \tag{1}
\]

设整数 \(k,l\) 满足
\(|kl|\le T^p(\log T)^{C_P}\)，其中 \(C_P\) 固定。
取 \(W\in C_c^\infty((1,2))\)，以及光滑 \(\Phi_T(x,y)\)，其在相关
\(x\) 区间上的 \(y\)-支集包含于一个固定紧集。允许核依赖外部参数，
但每个固定阶数的 \(x,y\) 导数必须统一至多增长一个固定对数幂；这些幂
与 \(A,e,r,k,l\) 无关。\(W\) 也可属于具有这些界的固定支集族。

定义有限原变量求和

\[
 \mathcal C_{A,e,r,k,l}
 =\frac1{e^2}\sum_n\frac{\mu(n)}{rn}W(n/X)
       \sum_{c\in\mathbb Z}
          \Phi_T\!\left(n/X,\frac{rnc-Akl}{A}\right).
 \tag{2}
\]

**局部定理。** 对每个固定 \(B>0\)，统一于 (1) 的所有参数，

\[
 \boxed{
 |\mathcal C_{A,e,r,k,l}|
 \ll_B\left(\frac1{re^2}+\frac{A}{reS}\right)(\log T)^{-B}.}
 \tag{3}
\]

常数允许依赖固定支集、\(C_P\) 及已声明的核半范数界。
这里不要求 \(A/D\) 大于某个对数负幂，也不假设 \(k,l\) 非零。

### 2.1 精确 Poisson 与自然模式尺度

使用 \(\widehat\Phi_2(x,\xi)=\int\Phi_T(x,y)e(-y\xi)\,dy\)，
变量替换 \(y=(rnc-Akl)/A\) 给出

\[
 \mathcal C_{A,e,r,k,l}
 =\frac{A}{r^2e^2}\sum_{j\in\mathbb Z}\sum_n
       \frac{\mu(n)}{n^2}G_{\lambda_j}(n/X)e(-B_j/n),
 \tag{4}
\]

\[
 h=A/D,\quad\lambda_j=jh,\quad
 B_j=jAkl/r=\lambda_j Xkl,\quad
 G_\lambda(x)=W(x)\widehat\Phi_2(x,\lambda/x).
 \tag{5}
\]

Jacobian 是 \(A/(rn)\)，相位为负号。Poisson 右边是
**绝对收敛的无限级数**，不是未经取尾就成为“有限恒等式”。

链式法则使用 \(x\partial_x-\xi\partial_\xi\)。Fourier 分部积分给出
\((\xi\partial_\xi)^b\widehat\Phi_2
=(-1)^b\widehat{(\partial_y y)^b\Phi_T}_2\)。因此，对每个固定 \(J\)，

\[
 \|b_\lambda\|_\infty+\int_X^{2X}|b_\lambda'(t)|dt
 \ll_J X^{-2}(\log T)^{C_J}(1+|\lambda|)^{-J},
 \quad b_\lambda(t)=t^{-2}G_\lambda(t/X).
 \tag{6}
\]

所需核导数阶数有限；(6) 没有额外的 \(|j|\) 或 \(D/A\) 因子。

### 2.2 逐模式的算术消去，统一到幂次截断

取 \(\Lambda=T^{\epsilon_0}\)，先考虑 \(|\lambda|\le\Lambda\)。
由 (1)，

\[
 X\ge T^{x_0},\qquad x_0=(u-\epsilon_0)(1-\epsilon_0).
\]

在长度 \(Y=X^\nu\) 的每个滑动窗口上，将 \(-B/t\) 作三次 Taylor 展开。
余项统一满足

\[
 \frac{|B|Y^4}{X^5}
 \ll T^{\epsilon_0+p-4(1-\nu)x_0}(\log T)^{C_P}
 \ll T^{-c_0}(\log T)^{C_P},
 \tag{7}
\]

其中

\[
 c_0=\frac{3938033}{12500000}>0.
\]

确实 \(p\le2u\)，且 \(4(1-\nu)(1-\epsilon_0)-2>0\)，所以最差点
为 \(u=1/2,p=1\)。区间指数满足

\[
 \nu-(1/3+\epsilon_0)=17/3000>0,\qquad
 1-\epsilon_0-\nu=659/1000>0. \tag{8}
\]

外部定理因而适用。下面给出“几乎处处”到实际整段求和的步骤。
对任意整数区间 \(I\subset[X,2X]\)，令
\(I^\circ=I\cap[X+Y,2X-Y]\)。逐个整数计算它被窗口覆盖的测度，得到

\[
 \sum_{n\in I^\circ}v_n
 =\frac1Y\int_X^{2X-Y}
       \sum_{x<n\le x+Y}v_n\mathbf1_{I^\circ}(n)\,dx. \tag{9}
\]

被去掉的全局边缘最多含 \(2Y+O(1)\) 个整数。好起点上，内部截断是一个
等差数列（公差为一），并且 Taylor 多项式可以依赖起点；外部定理的双重
maximal/supremum 正好允许这些操作。异常集测度为
\(O_M(X\log^{-M}X)\)，其贡献用 \(O(Y)\) 平凡界，再除以 \(Y\)。
Taylor 误差贡献 \(O(XT^{-c_0}\log^{C_P}T)\)，边缘为 \(O(Y)\)。
两者均小于任意指定的 \(X\log^{-M}T\)。于是

\[
 \sup_{I\subset[X,2X]}
 \left|\sum_{n\in I}\mu(n)e(-B/n)\right|
 \ll_M X(\log T)^{-M}. \tag{10}
\]

固定三次多项式的 supremum 使异常集对所有需要的模式一致；不需要对多达
\(D/A\) 个模式作异常集并集。随后对每个模式使用 (6) 和 Abel 求和，得到

\[
 \left|\sum_n\mu(n)b_\lambda(n)e(-B/n)\right|
 \ll_B X^{-1}(\log T)^{-B}(1+|\lambda|)^{-J}.
 \tag{11}
\]

这里先把外部定理中的任意对数收益选得大于 (6) 的对数损失。
零相位 \(B=0\) 同样属于该定理，无需另加一个条件输入。

### 2.3 多模式密度与尾项

对每个 \(h>0\)、\(J>1\)，单调积分比较给出

\[
 \sum_{j\in\mathbb Z}(1+|j|h)^{-J}
 \le1+\frac2{h(J-1)}\ll_J1+h^{-1}. \tag{12}
\]

对 \(\Lambda\ge1\) 也有

\[
 \sum_{|j|h>\Lambda}(1+|j|h)^{-J}
 \ll_J(1+h^{-1})\Lambda^{1-J}. \tag{13}
\]

证明 (13) 时保留第一个格点，再用积分界；即使 \(h>\Lambda\) 也成立。
在这些尾模式上只使用 \(|\mu(n)|\le1\) 和 (6)，因此无需把 (10) 推广到
任意大的相位。固定取 \(J=2\) 已有尾因子 \(T^{-1/1000}\)，足以吸收任意
固定对数损失（起始高度可依赖所需的对数收益）。

将 (11)–(13) 代回 (4)，关键归一化是

\[
 \frac{A}{r^2e^2X}\left(1+\frac DA\right)
 =\frac{A}{reS}+\frac1{re^2}. \tag{14}
\]

这证明 (3)。模式数的 \(D/A\) 被保留并由 Jacobian 支付，没有把幂次模式数
称为“仅有对数损失”。

## 3. 哪一种外部聚合已经合法

若一个 \(A\asymp A_0\) 盒的外系数满足
\(|\alpha(A)|\le C\tau_j(A)\)（固定 \(j\)），则 (3) 给出

\[
 \sum_{A\asymp A_0}\frac{|\alpha(A)|}{A}
      |\mathcal C_{A,e,r,k,l}|
 \ll_B\frac1r\left(\frac1{e^2}+\frac{A_0}{eS}\right)
              (\log T)^{-B}. \tag{15}
\]

这里使用的是 (3) 对每个参数的一致界；不是假设旧稿实际外系数已经符合
这个条件。若允许的 \(r\) 只有素因子来自某个 \(Q\le T^C\)，可进一步用

\[
 \sum_{p\mid r\Rightarrow p\mid Q}\frac1r
 =\frac Q{\varphi(Q)}
 =\sum_{d\mid Q}\frac{\mu^2(d)}{\varphi(d)}
 \le\sum_{d\le Q}\frac{\tau(d)}d
 \le(1+\log Q)^2. \tag{16}
\]

因此这种 \(r\)-求和以及 \(e\)-求和只消耗对数幂。
如果允许的集合随 \(A\) 改变，先对每个 \(A\) 用 (16)，再用 (15) 的
系数平均；不能把相关集合不加说明地交换成一个固定集合。

对非零双频率 \(k,l\) 的实际数目 \(\mathcal N\)，还须保留
\((HL/S)\mathcal N\)。只有已经知道
\(\mathcal N\ll(S/H)(S/L)(\log T)^C\) 时，才能写成

\[
 \frac{HL}{S}\mathcal N\ll S(\log T)^C. \tag{17}
\]

坐标轴的数目是另一项，不能在某个双频率长度小于一时照用乘积体积。
局部定理 (3) 包含零相位，但这不等于其外部轴项聚合已经完成。

## 4. 长余因子主项的另一条精确审计义务

设 \(n\ne0\)，记

\[
 g(d)=\prod_{p\mid d}\frac p{p+1},\qquad
 b_A(n)=\prod_{\substack{p\mid |n|\\p\nmid A}}\frac1{p+1}.
\]

完整有限 Euler 恒等式确实是

\[
 \sum_{\substack{d\mid |n|\\(d,A)=1}}\mu(d)g(d)=b_A(n). \tag{18}
\]

但长余因子选择限制了 \(d\) 的范围。对任意截断 \(Y\ge1\)，正确公式是

\[
 \sum_{\substack{d\mid |n|,\ d\le Y\\(d,A)=1}}\mu(d)g(d)
 =b_A(n)-
   \underbrace{\sum_{\substack{d\mid |n|,\ d>Y\\(d,A)=1}}
         \mu(d)g(d)}_{\mathcal R_{A,Y}(n)}. \tag{19}
\]

例如 \(n=p>Y\) 为素数、\((p,A)=1\)，左侧等于一，完整乘积等于
\(1/(p+1)\)，而 \(\mathcal R_{A,Y}(p)=-p/(p+1)\)。截断和不能直接用
完整正乘积作为同一主项。平滑选择 \(v(d/Y)\) 时，对应修正是
\(\sum_{d\mid n,(d,A)=1}\mu(d)g(d)[1-v(d/Y)]\)，同样必须保留。

旧稿 §4.109zjaceb 的正主项估计引用完整 (18)，而后续又单列长/短余因子。
将它们用于全局重组时，必须在精确公式中展示 (19) 的修正放在哪里、如何
估计，或证明另一个完整重组已经包含它。**本节只证明这个必要的代数修正，
不声称其在实际完整和中很大，也不把它当作长 mollifier 渐近式的反例。**
本次新短余因子估计 (3) 不能自动估计或抵消这个人为延长主项产生的修正。

## 5. 当前数学边界与检查

已证明的是光滑局部模型的全模式界 (3) 及上述明确条件下的聚合 (15)–(17)。
尚未完成：

- 将原 QCT 的每个 entry、互素限制和 taper 回代到 (2)。若外系数仍依赖
  \(n\)，必须保留在核内并证明其正则性，或另行作精确算术分解；不能仅靠
  把它命名为 \(\Omega(A,e,r,k,l)\) 就宣称没有 \(n\) 依赖。
- 处理本定理以外的大 \(e\)、外部轴项和变换尾；保留其各自前因子。
  后续笔记已处理固定互素模数所产生的全部 \(r\)，但不涵盖任意未识别算术权重。
- 共同组装长余因子密度项及 (19) 的补偿，再连接完整固定线二阶矩。

核算脚本 `scripts/check_cubic_comb_mode_density.py` 最初的 11 个标准库测试检查
精确相位与前因子、Taylor 余量、模式密度与尾界、滑动窗口覆盖、有限 Euler
截断修正和轴项计数边界。调制高斯 Poisson 回归还会拒绝错误相位符号及
遗漏 Jacobian 的变体；它只检查规范，不替代 (2)–(14) 的数学证明。
测试中的高斯属于 Schwartz 类，而定理使用已声明的紧支光滑核。
没有修改或构建 Lean。
后续互素与归一化审计新增 8 项检查，当前共 19 项。

### English scope summary

Keeping the exact Poisson Jacobian yields an all-mode local Möbius bound,
uniform even when \(A/D\) is small. The proof combines the published MRSTT
maximal polynomial-phase estimate, a continuous sliding-window identity, and
Fourier decay on the natural mode scale. The original QCT coefficients and
the long-cofactor completion correction still require separate assembly;
this note does not establish a long-mollifier asymptotic or a zero-free line.
