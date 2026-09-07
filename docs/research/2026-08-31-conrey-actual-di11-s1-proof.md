# Conrey 的最后一段 DI 谱输入：实际 S=1 五变量估计

先说结论：本篇在已有实际谱公式与大筛证明上，完整证明当前
Conrey 算术 completion 所需的 DI11 S=1 估计。一般光滑权重的
变量分离、三类普通谱、区间系数异常谱及所有尺度预算都保留。
异常权重使用 V=1+R/N，保证固定层数大筛的输入始终>=1，
并精确恢复 C^3 sqrt(R(R+N)) 项。

冻结基点 46b49ada33a37605565aa60f203827b96277d8ce。
本篇只新增纸面证明。它消解前序算术 completion 中明确保留的
DI11 S=1 输入，但不凭此宣布完整 Conrey 或 Lean 终点成立。

## 1. 实际和、光滑性与目标

设 C,M,N,R>=1，I 为 [M,2M] 中一个整数区间。
b(n,r) 为支撑在整数 n in [N,2N]、r in [R,2R] 的任意复系数，
允许随 r 变化；m 的系数始终是同一个区间指示函数。
记 ||b||_2^2=sum_(n,r)|b(n,r)|^2。

令 g(c,m,n,r) 为正半轴上的光滑复值函数，c 支撑在 [C,2C]，
在所用各尺度的固定倍数区间内具有一致的归一化导数界

\[
 |C^iM^jN^kR^l\partial_c^i\partial_m^j\partial_n^k\partial_r^l g|
                                    \le B_{i,j,k,l}.
 \tag{actual-smooth-weight-assumption}
\]

常数 B 固定，不随 C,M,N,R 改变。只需有限多个阶数，但允许
全部阶数受控以省去无关的阶数记账；当前 Fourier completion
的 Schwartz 权重满足这些条件。m,n,r 可乘固定倍数的光滑 cutoff，
在实际求和区间上为1；这不会改变实际和或导数预算。

研究

\[
 \mathcal S_\pm(g,b,I)=
 \sum_{r\in[R,2R]}\sum_{n\in[N,2N]}\sum_{m\in I}b(n,r)
       \sum_{(c,r)=1}g(c,m,n,r)\operatorname{Kl}_c(m\bar r,\pm n),
 \tag{actual-DI11-S1-object}
\]

其中 c,n,r,m 都取正整数，bar r 在模 c 下取逆，Kl 无1/c归一化。
本篇证明，对任意 epsilon>0，

\[
 \boxed{|\mathcal S_\pm(g,b,I)|
        \ll_{\epsilon,B}(CMNR)^\epsilon
                      F(C,M,N,R)\sqrt M\,\|b\|_2,}
 \tag{actual-DI11-S1-bound}
\]

\[
 \boxed{F^2=
 R\frac{(RC^2+MN+MC^2)(RC^2+MN+NC^2)}{RC^2+MN}
                      +C^3\sqrt{R(R+N)}.}
 \tag{actual-DI11-S1-budget}
\]

这是当前 S=1 的全部参数范围，不含 tempered 假设；也不声称
推广到任意 S 或把 m 改成任意复系数后仍有同样异常项。

## 2. 已证明的实际输入与端点

使用的不是 DI 定理的抽象接口，而是本链已写出证明的对象：

1. [实际跨尖点 Kuznetsov](2026-08-31-conrey-actual-signed-kuznetsov.md)：
   在 Gamma_0(r)，sigma_infinity=I、sigma_0=W_r 时，
   gamma=c sqrt(r)、(c,r)=1，且
   S_(infinity,0)(m,±n;gamma)=Kl_c(m bar r,±n)。
2. 实际普通 Maass、所有 Eisenstein 尖点连续谱、全纯谱大筛，
   以及 [固定层数异常谱估计](2026-08-31-conrey-fixed-level-exceptional-sieve.md)。
3. [区间系数层数平均异常谱](2026-08-31-conrey-interval-exceptional-sieve.md)，
   含 n=1 与任意区间前缀；Mellin 扭曲的 Hilbert Abel 预算亦已证明。
4. 本次 [光滑变化尺度核](2026-08-31-conrey-smooth-scale-spectral-kernel.md)，
   含全部普通谱衰减和异常参数趋0的一致对数。

普通平方大筛若原先写 (N,2N]，可把 [N,2N] 分成
(N/2,N] 与 (N,2N]，用两项 Cauchy；实尺度>=1/2 的普通大筛
已经证明。固定异常谱的原证明只用 N<=n<=2N 的几何界与
普通谱输入，按区间筛第1.1节相同方法重走即可得到闭端点版，
包括 N=1 的原子。本篇使用这个实际证明的扩展，常数一致，
不把固定异常谱定理未声明的 N<1 尺度直接传入其结论。

对负 Fourier 指标，反射 z -> -bar z 是 Gamma_0(r) 商上的
保测度等距映射，和 Laplace 算子及 W_r 对易。它将
rho_(j,0)(n) 换成 rho_(j,0)(-n)，并将正交谱基换成另一组
同特征值正交基。因此普通与异常平方大筛对负指标仍成立；
连续谱相应作全 Eisenstein 空间的酉变换。不能只引用正指标
估计而不解释异号情况。

## 3. 一般权重的精确对数 Fourier 分离

置物理核尺度及其倒数

\[
              a=\frac{4\pi\sqrt{MN}}{C\sqrt R},\qquad
              X=a^{-1},\qquad T=1+a.
 \tag{physical-and-exceptional-scales}
\]

取固定光滑 cutoff chi，在 [0,log2] 上为1，支撑在
(-log2,log4)。对实 u,v,w、x>0，令

\[
\begin{aligned}
 m&=Me^u,\quad n=Ne^v,\quad r=Re^w,\\
 c&=\frac{4\pi\sqrt{MN}\,e^{(u+v-w)/2}}{x\sqrt R},\\
 G(u,v,w;x)&=\chi(u)\chi(v)\chi(w)
                  \frac{a e^{(u+v)/2}}x\,g(c,Me^u,Ne^v,Re^w).
\end{aligned}
 \tag{actual-separated-profile}
\]

G 对 u,v,w 紧支撑在一个固定盒子；c in [C,2C] 及盒子限制
使 x/a 属于一个固定紧区间 [kappa,K]，远离0。
若需要，可选稍大的开区间固定所有轮廓支撑。
链式法则及 (actual-smooth-weight-assumption) 给 G 的任意
固定混合 log 坐标导数及 (x partial_x)^j 导数以常数 B 控制。
前因子 a exp((u+v)/2)/x 在支撑上也一致有界。

定义准确的三维 Fourier 系数

\[
 H_{\mathbf t}(x)=\int_{\mathbb R^3}G(u,v,w;x)
                       e^{-i(t_1u+t_2v+t_3w)}du\,dv\,dw.
\]

对每个所需核导数阶 J 和每个整数 L，可以对 u,v,w 分别
应用 (1-partial^2)^L 并分部积分，得到

\[
 \max_{j\le J}\sup_{x>0}a^j|\partial_x^j H_{\mathbf t}(x)|
          \le C_{J,L,B}\prod_{k=1}^3(1+t_k^2)^{-L}.
 \tag{uniform-separated-kernel-seminorms}
\]

因此 h_(t)(z)=H_(t)(az) 是配套核篇允许的固定支撑轮廓族，
其半范数具有显示的快速频率衰减。Fourier 反演精确给

\[
 g(c,m,n,r)=\frac{C\sqrt R}{c\sqrt r}\frac1{(2\pi)^3}
  \int_{\mathbb R^3}H_{\mathbf t}\!\left(\frac{4\pi\sqrt{mn}}{c\sqrt r}\right)
        (m/M)^{it_1}(n/N)^{it_2}(r/R)^{it_3}d\mathbf t
 \tag{exact-weight-separation}
\]

在实际 m,n,r 支撑上成立。前因子是 C sqrt(R)/(c sqrt(r))，
不能漏掉 sqrt(r) 或把它吸入依赖层数的常数。

将此式代入实际和，得到 C sqrt(R)/(2pi)^3 乘三重频率积分，
内层每个 r 的模数和精确为

\[
 \sum_{\gamma=c\sqrt r}\frac{S_{\infty0}(m,\pm n;\gamma)}\gamma
           H_{\mathbf t}(4\pi\sqrt{mn}/\gamma).
 \tag{actual-cross-cusp-geometric-block}
\]

这里没有一般尖点原刊可能出现的额外相位，因为当前 W_r
缩放与 Kl_c(m bar r,±n) 的关系已逐矩阵固定。

## 4. 普通谱的完整预算

先固定频率 t，并暂把其核半范数记为 B_t。
m 系数为 (m/M)^(it_1)1_I，范数平方 #I<=2M；n,r 的扭曲
可吸入 b_t(n,r)，其联合二次范数仍是 ||b||_2。

对实际跨尖点 Kuznetsov 的普通 Maass、全 Eisenstein 连续谱
及全纯项，配套核篇第6节给每个 r 的上界

\[
 C_\eta B_{\mathbf t}\frac{L_a}{T}
 (T^2+M^{1+\eta}/r)^{1/2}(T^2+N^{1+\eta}/r)^{1/2}
                        \sqrt M\,\|b(\cdot,r)\|_2.
\]

全纯项存在于同号公式，保留其 Gamma 因子和1/pi；异号公式
没有全纯项。其他固定谱归一化常数均已包含在上述绝对常数中。
由于 r in [R,2R]，再用 sum_r||b_r||<=sqrt(2R)||b||，并恢复
几何前因子 C sqrt(R)，普通谱总贡献不超过

\[
 C_\eta B_{\mathbf t}L_a(MN)^{\eta/2}
 \frac{CR}{T}(T^2+M/R)^{1/2}(T^2+N/R)^{1/2}
                                    \sqrt M\,\|b\|_2.
 \tag{actual-regular-spectrum-budget}
\]

以下核对它就是目标中的第一项，非“省略简单计算”。令

\[
 z=\frac{\sqrt{MN}}{C\sqrt R},\quad D=1+z^2,\quad
 u=M/R,\quad v=N/R.
\]

T=1+4pi z，所以 D<=T^2<=K_0D，有绝对 K_0。
又函数 (s+u)(s+v)/s=s+u+v+uv/s 给

\[
 \frac{(T^2+u)(T^2+v)}{T^2}
                 \le K_0\frac{(D+u)(D+v)}D.
\]

而

\[
 C^2R^2\frac{(D+u)(D+v)}D
 =R\frac{(RC^2+MN+MC^2)(RC^2+MN+NC^2)}{RC^2+MN}
 =F_{\rm reg}^2.
 \tag{exact-regular-budget-algebra}
\]

因此普通谱被目标 F_reg 控制，没有遗留谱截断或连续谱尾项。

## 5. 异常谱权重的合法分配

对 0<nu<=1/4，配套核篇给

\[
 |\widehat H_{\mathbf t}(i\nu)|+|\check H_{\mathbf t}(i\nu)|
              \le C B_{\mathbf t}\frac{L_a}{T}(1+X)^{2\nu}.
\]

实际公式中的 1/cos(pi nu)<=sqrt2，故只改变绝对常数。
现在固定

\[
                  V=1+R/N\ge1,\qquad U=1+X/\sqrt V\ge1.
 \tag{legal-exceptional-balancing-weights}
\]

逐个 nu 有

\[
 (1+X)^{2\nu}\le (U\sqrt V)^{2\nu}=U^{2\nu}V^\nu,
 \qquad U\sqrt V=\sqrt V+X\ge1+X.
 \tag{exact-spectral-weight-split}
\]

令 A_(j,r)(t_1)=sum_(m in I)(m/M)^(-it_1)rho_(j,infinity)(m)，
B_(j,r)=sum_n b_t(n,r)rho_(j,0)(±n)。同号实际乘积是
bar A B；异号只改变 B 的指标，已由第2节反射处理。
对所有 r,j 一起用 Cauchy，异常谱贡献至多

\[
 C B_{\mathbf t}\frac{C\sqrt R L_a}{T}
 \left(\sum_{r,j\ {\rm exc}}U^{4\nu_{j,r}}|A_{j,r}(t_1)|^2\right)^{1/2}
 \left(\sum_{r,j\ {\rm exc}}V^{2\nu_{j,r}}|B_{j,r}|^2\right)^{1/2}.
 \tag{actual-exceptional-Cauchy}
\]

此处的4nu与2nu不同，不能把两种大筛的权重混同。

### 5.1 区间一侧：层数平均与 Mellin 前缀

用已证区间筛于 q<=2R 的非负和，再对区间 Mellin 扭曲作
Hilbert Abel。所有前缀都由同一个区间估计控制，得到

\[
 \sum_{r,j\ {\rm exc}}U^{4\nu}|A_{j,r}(t_1)|^2
   \ll_\eta (1+|t_1|)^2(RM)^\eta(R+M+\sqrt M\,U)M.
\]

因为 M>=1，sqrt(M)<=M；并且由 a 的准确值，

\[
 \sqrt M\,\frac X{\sqrt V}
     =\frac C{4\pi}\sqrt{\frac R{R+N}}.
\]

故第一平方和至多

\[
 C_\eta(1+|t_1|)^2(RM)^\eta
                \left(R+M+C\sqrt{\frac R{R+N}}\right)M.
 \tag{actual-interval-side-exceptional}
\]

频率 t_1 对全部 r 相同，满足区间大筛的系数独立性。
不是把 (m/M)^(-it_1) 当成另一个指示函数。

### 5.2 任意系数一侧：固定层数，不取错误参数

V>=1，故实际固定层数异常谱定理可用。对每个 r in [R,2R]，

\[
 \sum_{j\ {\rm exc}}V^{2\nu}|B_{j,r}|^2
 \ll_\eta
  (1+\sqrt{NV/r})(1+\sqrt{N^{1+\eta}/r})\|b(\cdot,r)\|_2^2
 \ll_\eta N^{\eta/2}(1+N/R)\|b(\cdot,r)\|_2^2.
\]

这里 NV=N+R，r>=R；两个平方根因子的乘积可由
C N^(eta/2)(1+sqrt(N/R))^2<=C' N^(eta/2)(1+N/R) 控制。
对 r 求和没有再付一个 R，因为联合系数范数正是各 ||b_r||^2
之和。放宽 N^(eta/2) 为 (RN)^eta 后，

\[
 \sum_{r,j\ {\rm exc}}V^{2\nu}|B_{j,r}|^2
                \ll_\eta (RN)^\eta(1+N/R)\|b\|_2^2.
 \tag{actual-general-side-exceptional}
\]

若改选 R/N，在 N>R 时会小于1，不能调用当前固定层数定理。
保留 V=1+R/N 同时避免了这一范围错误与额外的 sqrt(N/R) 损失。

## 6. 异常项与目标 F 的逐项比较

将第5节两个平方和代入 Cauchy，略去已显示的频率因子和
epsilon 因子后，除以 sqrt(M)||b|| 的异常预算平方是

\[
 \frac{C^2R}{T^2}
        \left(R+M+C\sqrt{\frac R{R+N}}\right)(1+N/R)
 =\frac{C^2(R+M)(R+N)}{T^2}
             +\frac{C^3\sqrt{R(R+N)}}{T^2}.
 \tag{exact-exceptional-budget-algebra}
\]

第二项因 T>=1，不超过目标异常项 C^3 sqrt(R(R+N))。
第一项用第4节 D>=1、T^2>=D：

\[
 \frac{C^2(R+M)(R+N)}{T^2}
 =C^2R^2\frac{(1+u)(1+v)}{T^2}
 \le C^2R^2\frac{(D+u)(D+v)}D=F_{\rm reg}^2.
\]

因此异常谱整体受同一个 F 控制。这里覆盖 N>R 和 N<=R、
X>1 和 X<=1，均不删掉异常特征值，也不需要最小 nu 的下界。

## 7. 频率积分、epsilon 及绝对换序

前面给固定频率的完整谱界

\[
 C_\eta B_{\mathbf t}(1+|t_1|)
       L_a(CMNR)^\eta F\sqrt M\,\|b\|_2,
\]

必要时把 eta 放宽一个固定倍数；所有具体因子均已在第4、5节
列出。由 (uniform-separated-kernel-seminorms)，可取
B_t<=C_B product_(k=1)^3(1+t_k^2)^(-3)。乘 (1+|t_1|) 后仍
绝对可积，故三维频率积分给固定常数。

又 C,M,N,R>=1，X=C sqrt(R)/(4pi sqrt(MN))，所以
L_a=1+log_+X<=C_epsilon(CMNR)^(epsilon/2)。在所有大筛中先取
eta 为 epsilon 的充分小固定倍数，例如 epsilon/10，可把
全部剩余幂收入 (CMNR)^epsilon，得到第1节结论。

各次换序的依据是：原始 m,n,r,c 范围有限；分离后的 x 支撑
仍使 c 有限，并有快速频率衰减，所以初次有限和与 Fourier
积分交换绝对合法。换到实际谱后，第4节的可求和普通谱包络
以及第5节的两个实际异常平方和，提供同一个可积频率主化。
连续谱的全部尖点求和也包含在普通谱大筛中。因此没有用
形式上的 Mellin/Fubini 标签代替收敛证明。

至此 (actual-DI11-S1-bound) 与预算已作为实际估计得到证明。

## 8. 与算术 completion 的接合及剩余任务

[算术 completion 证明第5节](2026-08-31-conrey-di-arithmetic-completion.md)
保留的 (DI11-S1) 正是第1节的对象与预算。本篇的闭端点版本
覆盖原来的 dyadic 单点；负 m 可沿前篇的共轭恒等式处理。
前篇实际权重 (C/c)w_1(c/C)hat w_2(mD/c) 的所有归一化导数
带 (1+MD/C)^(-A) 衰减，满足本篇假设，且仍以区间示性函数
作为 m 系数。但模数 c=1 必须单独剥离：旧 w_1 支撑在
(1/2,3)，可以在该整数点非零，而光滑支撑 [C,2C]、C>=1
的函数在 c=1 必为0，不能声称有限光滑分割自动覆盖它。

由于 Kl_1=1，若当前权重的上界为 B，则

\[
 |\mathcal S_{c=1}|\le B\,\#I\sum_{n,r}|b(n,r)|
       \ll B M\sqrt{NR}\,\|b\|_2
       \le B F_{\rm reg}\sqrt M\,\|b\|_2,
 \tag{modulus-one-completion-endpoint}
\]

最后一步由 F_reg^2>=R(RC^2+MN)>=RMN。
旧权重的 B 仍带 (1+MD/C)^(-A)；剥离该点不损失 Schwartz
衰减。其余整数 c>=2 才使用前篇的有限光滑分割：在
[C/2,3C] 与 [2,infinity) 的交集上，用下端点 C_j>=1、
C_j 与 C 可比、相互重叠的 (C_j,2C_j) 覆盖。该集合的尺度
比有绝对上界，固定倍数光滑分割的项数与导数常数均一致。
结合 c=1 的独立估计，本篇提供了该处此前未自证的完整谱输入。

于是前篇已证明的 Poisson 零频、尾项、系数能量、dyadic 合并
及尺度代数可使用本篇结论，得到其中的 (incomplete-from-DI11)
和 (DI84-actual-derived)，不再需要把 DI11 S=1 当外部假设。
前篇是冻结历史交付，保留其当时的条件表述；本篇明确记录
这次依赖消解，而不改写旧 SHA 或将旧报告冒充新验证。

本篇不等同于所有最终目标均完成。下一步仍须逐项审计当前
Conrey 均方主项、参数极限、计数接合和误差链的其他实际输入，
确认没有剩余解析缺口；再在专属资源窗口完成相应 Lean 证明
及最终集成树验证。尤其不能用本次 Python、纸面审查或无公理
报告宣布原生严格 >2/5 已获机器验证。

原刊对照：DI Theorems 10--11，p.236，及 Section 9.1，
pp.278--280，[定理页](https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0070/LOG_0020.pdf)、
[证明页](https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0070/LOG_0028.pdf)。
本篇使用当前实际 W_r 缩放、标准 K 的变换常数及保留1+的
异常权重分配；公式逐项成立是验收依据，不靠原刊的简写授权。

### English summary

The actual S=1 DI11 estimate is proved for a smooth four-variable
weight, an interval in m, and arbitrary coefficients b(n,r). Exact
log-Fourier separation preserves the cross-cusp modulus c sqrt(r).
Ordinary spectral large sieves yield the rational regular budget.
Exceptional weights V=1+R/N and U=1+X/sqrt(V) stay in their proved
ranges; the interval average and the fixed-level sieve produce exactly
the C^3 sqrt(R(R+N)) contribution. This discharges the explicit DI11 S=1
input in the earlier arithmetic-completion note. A full Conrey endpoint
audit and Lean verification are still required.
