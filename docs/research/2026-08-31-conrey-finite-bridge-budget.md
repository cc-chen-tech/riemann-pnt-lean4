# Conrey 原生化前的有限误差预算：半段均方到加权实际计数

先说结论：无需新证一个低高度均方，也无需先建立 liminf 框架。
现有实际 V1 转移定理可在分割点等于下端点时直接使用；本文把
此步、选高端点、全部轮廓余项、有限零点并集和 RVM 分母写成
一个有限高度的不等式，并给出严格余量所需的明确门槛组合。
这落实了后续原生组合应证明的代数步骤，不新增最终均方假设。

来源固定为 #550 的 `5ab32c1569a2e095f35a7bb51243c5599e864ac8`。
仅新增本篇纸面推导，不改冻结源、Lean、Lake 或契约。
[端到端纸面证明](2026-08-31-conrey-end-to-end-paper-proof.md)已给出
实际 Gaussian 误差趋零的数学来源；它们仍待原生化。
以下“有限”不表示已计算出一个数值可用的最终高度。

## 1. 固定参数、实际函数和 Gaussian 误差

沿用上述源的同一参数

\[
 L=\log T,\quad\theta=571/1000,\quad Y=\lfloor T^\theta\rfloor,
 \quad R=6/5,\quad k=51/50,\quad\sigma_0=1/2-R/L,
 \quad A=2\log L.
\]

`P=(84x+15x^3+x^5)/100`，`B_T=conreyMollifier Y sigma0 P`，
`V_T=conreyExplicitV L`，`V1_T=conreyDegreeOneV1 (49/100) 0 k L`。
所有函数在 `sigma0+it` 上取值，T 在积分中不变。记

\[
 f_T(t)=|V_TB_T|^2(\sigma_0+it),\quad
 z_T(t)=|\zeta B_T|^2(\sigma_0+it),\quad
 h_T(t)=|V_{1,T}B_T|^2(\sigma_0+it),
\]
\[
 m_V=\frac2T\int_{T/2}^T f_T,
 \qquad m_Z=\frac2T\int_{T/2}^T z_T,
 \qquad m_1=\frac2T\int_{T/2}^T h_T.
\]

令 C 为同一实际 `conreyExplicitMeanSquareIntegral`，C0 为
[局部 V1 文稿](2026-08-31-conrey-local-v1-mean.md)中的未微分
Gaussian 常数。两个积分的被积平方给 `C,C0>=1`。令

\[
 \kappa=1-\log C/R,\qquad 2/5<\kappa\le1,
 \quad\delta=3/256000,\quad\Delta=T^{1-\delta},
 \quad\phi_\Delta(x)=e^{-x^2/\Delta^2}/(\Delta\sqrt\pi).
\]

其中严格下界来自现有精确积分证书，上界来自 `C>=1`。
定义真实函数的两个误差，而不是抽象供应接口：

\[
 a_V(T)=\sup_{w\in[T/2,T]}|(f_T*\phi_\Delta)(w)-C|,
 \quad
 a_Z(T)=\sup_{w\in[T/2,T]}|(z_T*\phi_\Delta)(w)-C_0|.
 \tag{actual-Gaussian-errors}
\]

对所有足够大 T，这两个上确界非负且有限。全高度多项式增长
与 Gaussian 支配给连续性，紧中心区间给有界性。#550 引用的
实际主项、有限轮廓、算术和 DI 估计给 `a_V,a_Z->0`；此处
定义误差没有证明该事实，也没有把它当作已完成的 Lean 结果。

## 2. 同参数去平滑与直接复用现有 V1 转移

[已证纸面端点核不等式](2026-08-31-conrey-dyadic-desmoothing.md)
在长度 T/2 的区间上给

\[
 |m_V-C|\le b_V:=a_V+2\sqrt\pi\frac\Delta T(C+a_V),\qquad
 |m_Z-C_0|\le b_Z:=a_Z+2\sqrt\pi\frac\Delta T(C_0+a_Z).
 \tag{actual-half-errors}
\]

系数是 `2sqrt(pi)`，不是长度 T 的版本中的 `sqrt(pi)`。
证明是：平滑积分的归一化误差至多 a；两个端点贡献至多
`Delta sqrt(pi)(C+a)`，再乘 `2/T`。同理处理 C0。

令固定常数

\[
 K=\frac{51}{50}\left(10+\frac{\log2+|\log(2\pi)|}{2}\right).
\]

源码 `conreyMollifiedV1_meanSquare_le_V_and_zeta` 的参数允许
分割点等于任一端点。取

\[
 U=T/2,\qquad a=1-\log2/L,\qquad\varepsilon_Y=1/L.
\]

这里 `a<=1`、`exp(aL)=T/2=U`，`epsilon_Y>0`。当 `T>=6`、
`0<sigma0<=1/2` 时其余有限条件都成立。该定理的第一个积分
`int_U^exp(aL) z_T` **精确为零**，而
`conreyV1ComparisonCoefficient L a=K/L`。因此已存在的有限
定理直接给出

\[
 \boxed{m_1\le(1+1/L)m_V+(1+L)\frac{K^2}{L^2}m_Z.}
 \tag{native-transfer-specialization}
\]

没有另加低高度输入，也不需要调用带平方根的 L2 极限定理。
`epsilon_Y` 是 Young 不等式参数，与 DI 的固定小损失无关。
它随 T 变化合法，因为使用的是每个有限 T 的定理。

将 (actual-half-errors) 代入，定义非负的具体误差

\[
 E(T)=b_V+\frac{C+b_V}{L}
                  +(1+L)\frac{K^2}{L^2}(C_0+b_Z).
 \tag{actual-V1-upper-error}
\]

于是 `m_1<=C+E(T)`，且上述实际 Gaussian 估计给 `E(T)->0`。
最终计数只需这个上界，不必先原生化双向 V1 均方渐近。
这没有删掉深层 Gaussian 证明义务：它仍是 E 趋零的必要来源。

## 3. 不含大 O 的实际轮廓预算

以下 T 满足任意窗口选高与 V1 水平变幅定理的共同门槛，
`L>=40000`，`Creg,Cmass<=T`，以及 `A+1<=T/2`。
这些是源码中已构造的固定常数与最终门槛，不是新的均方条件。
同时有 `2<=Y<=T`。取两个窗口 `[T/2,T/2+1]` 和 `[T-1,T]`，
已有定理选择 u,v，令

\[
 u\in[T/2,T/2+1],\quad v\in[T-1,T],\quad
 \ell=v-u,\quad s=2\ell/T,\qquad1-4/T\le s\le1.
 \tag{selected-length}
\]

这些选择在同一个实际 F=V1_T B_T 上进行。三个非左边非零，
左边允许零点，实际 log 范数可积且 `I2=int_u^v h_T>0`。
完整非左边预算与 #550 一致：

\[
 B(T)=507T/L+2200000000000L^7+(A-\sigma_0)\pi\ge0.
\]

还可将 eta 三边变幅的误差全部显式化。源码
`conreyHorizontalJensenHeightBase L b=b+A+10` 且其
Archimedean 常数恰为10。因此两个水平 H 项的和不超过

\[
 H_*(T)=10(A-1/2)\bigl[2+
             \log(T/2+A+12)+\log(T+A+11)\bigr].
\]

两项中的 `+12` 和 `+11` 分别来自下窗口 `b=T/2`、上窗口
`b=T-1` 的 `HeightBase+2`，不使用不同高度重新定义 A。
右边 H 主项误差为 `8ell`，两条 V1 水平边合计至多
`2200000000000L^7`，V1 右边变幅至多 pi。又 `t>=T/2` 给
`log(t/(2pi))>=L-log(4pi)`。故定义

\[
 D(T)=\left(4+\frac{\log(4\pi)}4\right)T
                        +H_*(T)+2200000000000L^7+\pi
 \tag{eta-defect-budget}
\]

就有 `E_eta>=ell L/2-D(T)`。这里用
`(8+log(4pi)/2)ell <= (4+log(4pi)/4)T`，因为 `ell<=T/2`。
所有项都非负。

此结论使用 `ConreyEtaArgumentFactors` 的任意窗口 H 估计和
`ConreyV1HorizontalArgument` 的任意无零水平边定理；不能直接
把旧低底边窗口专用的 `exists_conreyEta_threeEdgeArgument_lower_bound`
当成已经陈述了本地版本。分解仅在非左边上，避开左边奇异积分。

## 4. 把选高长度损失明确压到 1/T

保留有限轮廓原始返回的真实简单零点集 `S subset (u,v)`。
完整重数、Littlewood 和 Jensen 已给

\[
 \#S\ge E_\eta/\pi
       -\frac{\ell\log(I_2/\ell)+2B(T)}{2\pi(R/L)}-1.
 \tag{finite-contour-input}
\]

这是对实际 F 的有限结论；其使用点和前提的构造详见
[局部计数证明](2026-08-31-conrey-local-simple-count.md)，并对应
`ConreyFiniteContourCount`、`ConreyMollifiedFullCount`、
`ConreyMollifiedLittlewood` 与 `ConreyMollifiedMeanSquare`。

非负积分限制给 `I2/ell <= (C+E)/s`。对 T>4，有 s>0。
使用 `log(1+x)<=x`（x>=0）及 `-log s<=1/s-1` 得

\[
 \log(I_2/\ell)\le\log C+E/C+(1-s)/s,
\]
\[
 \ell\log(I_2/\ell)
             \le\ell\log C+\ell E/C+2.
 \tag{finite-log-loss}
\]

最后一项的推导是 `ell(1-s)/s=T(1-s)/2<=2`。
它没有要求 `I2/ell>=1`；log 在正数上单调已经足够。
也没有对选高删去的单位段作点态或均方小量假设。

代入 (finite-contour-input) 并除以正数 `T L/(4pi)`，得到

\[
 \frac{\#S}{TL/(4\pi)}\ge s\kappa-s\frac{E}{RC}
       -\frac4{RT}-\frac{4D}{TL}-\frac{4B}{RT}-\frac{4\pi}{TL}.
\]

由 `0<kappa<=1`、`1-4/T<=s<=1` 和 E>=0，定义

\[
 q(T)=\frac4T+\frac{E(T)}{RC}+\frac4{RT}
                 +\frac{4D(T)}{TL}+\frac{4B(T)}{RT}+\frac{4\pi}{TL},
 \tag{local-defect}
\]

得到完全有限的结论

\[
 \boxed{\#S\ge\frac{T\log T}{4\pi}(\kappa-q(T)),
       \qquad S\subset(T/2,T).}
 \tag{finite-local-witness}
\]

q>=0。具体地 `H_*(T)=O(L log L)`，所以 `D/(TL)->0`，
`B/T->0`；由第2节 E->0 得 q->0。这里大 O 只用于证明已明写
误差的极限，不替代任何有限输入。q 很大时下界可能为负，
不影响不等式成立，亦不能省略后续门槛。

## 5. 有限并集的精确 log 修正

取整数 J>=1，X>1，`T_j=X/2^j`。要求每个 `j<J` 的 T_j
均满足前述有限门槛，故 `log T_j>0`。分别应用第4节得到 S_j。
不同块的函数可以不同，但它们返回的都是实际 zeta 简单零点。

若 j<k，`T_k<=T_j/2`，所以 `(T_k/2,T_k)` 与 `(T_j/2,T_j)`
不交。S_j 因而两两不交。映射 `t |-> 1/2+it` 是单射：取虚部
即恢复 t。每个像点满足实际零点、正高度、`Im<=X`、`Re=1/2`
和解析阶1，故属于 `positiveCriticalLineSimpleZerosFinset X`。
这证明同一个原生计数满足 `Ns(X)>=sum_(j<J) #S_j`，不是相减
两个全局下界。

记 `D_X=X log X/(2pi)>0`。精确归一化权重是

\[
 \frac{T_j\log T_j/(4\pi)}{D_X}
      =2^{-j-1}\left(1-\frac{j\log2}{\log X}\right).
\]

两项有限几何恒等式为

\[
 \sum_{j<J}2^{-j-1}=1-2^{-J},\qquad
 \sum_{j<J}j2^{-j-1}=1-(J+1)2^{-J}.
\]

对 J=1 成立；增加末项 `J/2^(J+1)` 即得到第二式的归纳步骤。
由于 `0<log T_j/log X<=1` 及 q(T_j)>=0，得到

\[
 \boxed{\frac{N_s(X)}{D_X}\ge
 \kappa(1-2^{-J})-
 \kappa\frac{\log2}{\log X}[1-(J+1)2^{-J}]
                         -\sum_{j<J}2^{-j-1}q(T_j).}
 \tag{finite-global-budget}
\]

没有要求 `kappa-q(T_j)>=0`：先精确分开 kappa 主项与 q 误差，
再仅对非负 q 放大扣除项。若错误地直接用较小权重乘整个
`kappa-q`，负下界情形会翻转所需比较。

令 `q_*=max_(j<J) q(T_j)`。由 `0<kappa<=1` 及上面两和均在
[0,1] 内，得到便于原生组合的保守式

\[
 \frac{N_s(X)}{D_X}\ge
                  \kappa-2^{-J}-\frac{\log2}{\log X}-q_*.
 \tag{four-margin-budget}
\]

这是有限 J、有限实 X 的估计，不是只在 dyadic 高度成立。

## 6. 明确分配严格余量并返回带重数的 N(X)

固定 `0<c<kappa`，设 `g=kappa-c`，则 `0<g<1`。取

\[
 J=\left\lceil\frac{\log(4/g)}{\log2}\right\rceil\ge1,
 \qquad 2^{-J}\le g/4.
\]

因 q(T)->0，可取 Tloc 使所有 `T>=Tloc` 同时满足第3节有限
条件、`T>=8` 和 `q(T)<=g/4`。这个 Tloc 来自已经证明的实际
误差及固定边界常数；它不是任意假设最终比例。

令 C_RVM>=0 是源码
`exists_abs_riemannZeroCount_sub_mainTerm_le_log` 构造的常数。
该定理对全部 X>=8 给

\[
 N(X)\le D_X-\frac{X}{2\pi}(\log(2\pi)+1)
                          +C_{\rm RVM}(1+\log(X+6)).
\]

此 N 计解析重数，与 Ns 的环境有限集相同。因 X>=8，
`X+6<=2X` 且 `1+log2<=log X`，故

\[
 \frac{N(X)}{D_X}\le1+\frac{4\pi C_{\rm RVM}}{X}.
 \tag{finite-RVM-upper}
\]

现在取任何实 X 满足

\[
 \boxed{X\ge\max\left\{8,\ 2^{J-1}T_{\rm loc},\
                 2^{4/g},\ \frac{16\pi c C_{\rm RVM}}g\right\}.}
 \tag{explicit-threshold-combination}
\]

第一、二项保证每块合规及 `q_*<=g/4`；第三项保证
`log2/logX<=g/4`；第四项保证 RVM 损失乘 c 后至多 g/4。
由 (four-margin-budget) 与 (finite-RVM-upper)，

\[
 \frac{N_s(X)}{D_X}\ge\kappa-3g/4=c+g/4
                  \ge c\frac{N(X)}{D_X}.
\]

乘 D_X>0 得 `c N(X)<=Ns(X)`。若 c<=0，只用两个计数非负。
这给当前 `conreyExplicitAnalyticLowerBound` 的逐量词数学证明：
先 c，再固定 J 和 Tloc，最后对全部 X>=X0；不交换未知的一致极限。

## 7. 后续原生步骤与本次交付边界

本篇没有新增 Lean 条件接口。有限代数路径已明确：

1. 特化现有 `conreyMollifiedV1_meanSquare_le_V_and_zeta`，
   消掉精确零长度积分，得到 (native-transfer-specialization)。
2. 用现有任意窗口原始定理证明局部三边预算，并保留
   `exists_conreyDegreeOneEta_simpleZero_finset_of_three_edges`
   返回的 S；不用丢弃定位信息的旧全局组合结论。
3. 以 `Finset` 并集、上述单射和两个有限几何恒等式，原生化
   (finite-global-budget)，再组合既有 RVM 和阈值。
4. 真正证明实际 a_V,a_Z 趋零的原生 Gaussian／算术／谱步骤
   仍不可省略。纸面已有的深输入不能由此自动变成 Lean 证明。

这些步骤不要求固定全局 mollifier 的低高度均方，也不要求
先补一个 liminf 基础库。目标并未缩小：仍是实际严格 `>2/5`
简单临界线零点、带解析重数分母的全部大实高度结论。

本篇只细化 #550 的原生化衔接，不宣称新文献定理或原生最终
目标完成。没有计算出可实际使用的数字 Tloc；其中的分析常数
仍来自上游证明。没有启动 Lean/Lake 或依赖加载，专属窗口
仍由唯一集成负责人协调；源验证与最终 main 验证继续分开。

### English summary

A specialization of the existing finite V1 transfer kills its low piece
exactly. Explicit half-interval desmoothing, selected-length and contour
defects then produce a finite bound for actual local simple-zero witnesses.
An injective finite union preserves multiplicities and endpoints correctly.
The exact dyadic log correction and a four-way margin allocation yield a
concrete combination of thresholds for the weighted RVM denominator.
The true Gaussian errors still require native proofs; this is paper-level
preparation, not a new conditional Lean interface or final certification.
