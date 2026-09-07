# 全局斜率完成与 B 平均：实际短 B 区域的新覆盖

白话结论：保留全部 e 重组后的公式，先对一条真正光滑的短
斜率求和，再使用整个 B 区间的平均，能改善平方自由均值的
误差。在 q=1、平衡顶层，K₁=K₂≈T^{1/2} 时，**整个
B≈Y≤T 的实际光滑 core** 达到 T^{3+ε}，不再只覆盖 Y≤T^{2/3}。
这包含非零 determinant 补集，不只是上一轮的精确共振子项。
**更长 B、一般 q、其他尺度、canonical zero Gram 和完整
signed operator 的目标界仍未证明；完整 twisted moment 未证明。**

本节只使用 [GE1–GE7](2026-08-30-mwkf-global-e-primitive-resonance.md)
的实际核，以及 [JT9–JT11](2026-08-30-mwkf-joint-type-ii-density.md)
的初等平方自由均值。不需要给 µ 加入新的相关性猜想。
下文完成的是 k,l 中较长的光滑变量；没有先对该变量取绝对值。

## 1. 全部 e 重组后，M 与 B 不再有互素限制

继续 q=1、R=S=T³、HL≈T⁵、K≈P≈Z≈T，X=R/K≈T²。
这里 K 是原 κ 的尺度，P=K₁K₂，别与两条短斜率混淆。
令 B∈[Y,2Y)、1≤Y≤2S。保留平方自由 M,B，但不添加 (M,B)=1：
它们的 gcd 正是已重组的原 e。若先前还有人工 e/A/b 分片，
必须先恢复到 GE4 的共同实际幅度。

可以交换两条斜率及其 H,L 标签，使 1≤K₁≤K₂；交换时同时
交换核的对应坐标，不假设核对称。所有 l 分片必须光滑且
支撑 |l|≈K₂；k,l 均非零。记
\[
 \mathcal P_{\rm crit}(Y)=\frac{HL}{R}
 \sum_{Y\le B<2Y}\frac{\mu(B)}B
 \sum_{k,l}\sum_{j\ne0}\frac1{|j|}
 \sum_{n\ne0} e(-nkl/(jB))
 \sum_{M\ge1}\frac{\mu^2(M)\kappa_M(n)}M
                 \Psi_{M,B,j,k,l}(n/B).             \tag{GS1}
\]
Ψ 是 GE5 的完整 JT symbol，M≈X。这里 j 属于固定有限集合，
critical 支撑给 **cY≤|n|≤CY**，c,C>0 固定。
这一正下界在下面的采样引理中不可删除。

对 M 使用 JT9 的 Q=1 情形，定义一个线性算术均值算子
\[
 \mathcal A_n[W]=\sum_M\frac{\mu^2(M)\kappa_M(n)}M W(M/X),
 \qquad
 \mathcal D_n[W]=\frac{\delta_1(n)}{\zeta(2)}
                          \int W(x)\frac{dx}{x},
 \quad D(n)=\sum_{d\mid|n|}\sqrt d .
\]
对固定倍数的紧支撑，有限分片后 JT9 给
\[
 |(\mathcal A_n-\mathcal D_n)[W]|
       \ll T^\varepsilon X^{-1/2}D(n)\|W\|_{C^1}.   \tag{GS2}
\]
Q=1 是 GE3 双射的结果，不是删掉一个原有单位掩码。
JT9 已计费大除数的连续主项延伸及整数 M=1 等过渡端点。

## 2. 精确完成光滑 l，且变换相位不依赖 M

固定 B,n,k,j，将 Ψ 看作光滑 l 函数，令
\[
 V_{M,B,j,k,n}(u)=\Psi_{M,B,j,k,K_2u}(n/B),\quad
 \widehat V(\xi)=\int V(u)e(-\xi u)\,du .
\]
精确 Poisson 恒等式是
\[
 \sum_l\Psi_{M,B,j,k,l}(n/B)e(-nkl/(jB))
   =K_2\sum_{\nu\in\mathbb Z}
           \widehat V_{M,B,j,k,n}\left(K_2(\nu+nk/(jB))\right).
                                                               \tag{GS3}
\]
没有新 leading-term 近似；负号 Fourier 约定与 GE8 一致。
固定 n，JT 参数的 M 与 l 归一化微分分别作用为
\[
 M\partial_M:\ \Lambda\partial_\Lambda-\eta\partial_\eta
                                 -2\sigma\partial_\sigma,
 \qquad
 l\partial_l:\ \Lambda\partial_\Lambda-\eta\partial_\eta
                                 -\sigma\partial_\sigma,
\]
另加 GE4 中实际 G 坐标与光滑分片的导数。JT4 的精确积分
symbol 对这些混合导数统一受控；χ(Sx/B) 不引入 l 或 M 的
快速变化。故任意固定 J 的积分分部给
\[
 \left\|M\mapsto K_2\widehat V_{M,B,j,k,n}
                 (K_2(\nu+nk/(jB)))\right\|_{C^1(M/X)}
 \ll_J T^\varepsilon K_2
                  (1+K_2|\nu+nk/(jB)|)^{-J}.        \tag{GS4}
\]
关键是载波 nk/(jB) **与 M 无关**；对 M 微分不产生新的大因子。
因此 GS2 可在 GS3 之后应用。原 µ(B) 和 κ_M(n) 的所有符号
在精确等式中保留；只在控制已经定义的误差时使用绝对值。

## 3. 全 B 采样引理：整数 +1 必须计费

设 cY≤|n|≤CY、|k|≈K₁、1≤|j|≤J₀，K₁,K₂≥1，J>1。
则
\[
 \sum_{Y\le B<2Y}\sum_{\nu\in\mathbb Z}
       (1+K_2|\nu+nk/(jB)|)^{-J}
       \ll_{c,C,J_0,J}\frac{Y}{K_2}+K_1 .          \tag{GS5}
\]
不要求 B,n,k 之间互素。证明如下。

1. B↦nk/(jB) 单调，导数的绝对值≈K₁/Y。对每个
   |ν|≤C₁K₁，函数 (1+K₂|ν+nk/(jB)|)^{-J} 至多一个峰。
   整数求和由积分加固定倍数的最大值控制，故每个 ν 的成本
   为 O(1+Y/(K₁K₂))。共有 O(K₁) 个这样的 ν。
2. 选 C₁ 充分大，|ν|>C₁K₁ 时距离至少 |ν|/2。完整远 ν 尾
   至多 O(Y K₂^{-J}K₁^{1-J})，由于 K₁,K₂≥1，被 Y/K₂ 吸收。

第一步中的 +1 正是 GS5 的 K₁ 项；不能删除。例如
n=Y=10、k=j=1、K₂=10000 时，B=10、ν=−1 仍有一个精确别名，
而 Y/K₂=1/1000。若丢失 |n|≳Y，ν=0 还可能有整段 B 的大贡献。
只允许在完成 GS5 后，为除数质量估计把 n 范围扩大为 |n|≤CY。

有限窗口也可精确写出。给定 F≥0，保留
|K₂(ν+nk/(jB))|≤F；每个 B 的 ν 端点是
ceil[−nk/(jB)−F/K₂] 与 floor[−nk/(jB)+F/K₂]，均包含等号。
固定 ν 反解 B 时，把 y=nk/j 取正（同时改变 ν 符号）；
若 u=F/K₂−ν≤0，则空；否则 B≥y/u，并在
v=−F/K₂−ν>0 时要求 B≤y/v。最后与 [Y,2Y) 的整数相交。
没有用连续区间长度替代实际整数计数。

## 4. 密度和误差是同一个分解，不是两个 saving 相乘

在 GS1 中用 \(\mathcal A_n=\mathcal D_n+(\mathcal A_n-\mathcal D_n)\)
定义 \(\mathcal P_{\rm crit}(Y)=\mathcal M(Y)+\mathcal E(Y)\)。
密度在原 l 表示中估计：Σ_{0<|n|≤CY}δ₁(n)≪T^ε，
Σ_{B≈Y}1/B≪1，#(k,l)≪P，所以
\[
                         |\mathcal M(Y)|\ll T^\varepsilon HL P/R.
                                                               \tag{GS6}
\]
该密度不是 canonical zero Gram，亦不假设它具有正性。

误差在线性等价的 GS3 表示中估计。利用 GS2、GS4，先保留
整个 B/ν 平均，再用 GS5。最后才用
\[
 \sum_{0<|n|\le CY}D(n)
 =2\sum_{d\le CY}\sqrt d\lfloor CY/d\rfloor\ll Y^{3/2}.
\]
支付 B^{-1}≤Y^{-1}、#k≪K₁ 及 Poisson 的 K₂ 因子，得到
\[
 |\mathcal E(Y)|
 \ll T^\varepsilon\frac{HL}{R\sqrt X}\,P
            \left(\frac{Y^{3/2}}{K_2}+K_1Y^{1/2}\right).
                                                               \tag{GS7}
\]
右侧第二项来自整数采样的 +1，不是可丢的低阶项。
没有使用平方自由误差在不同 B 之间的未知符号相关，也没有
对同一个余项先后相乘节省；密度与误差只是分别选择了合适表示。

## 5. 新覆盖、独立尾项及边界

当 K₁=K₂≈T^{1/2}，GS7 化为
\[
 |\mathcal E(Y)|\ll
            T^{3/2+\varepsilon}Y^{3/2}
             +T^{5/2+\varepsilon}Y^{1/2}.          \tag{GS8}
\]
因 GS6 是 T^{3+ε}，**整个 B≈Y≤T 的该实际 core 达标**。
此前不完成 l 的误差是 T^{2+ε}Y^{3/2}，仅在 Y≤T^{2/3}
达到预算。这里的 B=eb，新的覆盖包括全部 e 分配，特别包括
原 e=1、b≈T 的长 Type-II 项。这里仅指这些项包含于 **all-e
联合和**，不提供固定 e 子和的独立上界：单独限制 e=1 会
恢复 (M,B)=1，使本节 Q=1 的均值公式不再适用。

一般写 Kmin=T^a、Kmax=T^{1-a}、0≤a≤1/2、Y=T^β。
两项误差指数为
\[
 1+a+3\beta/2,\qquad 2+a+\beta/2;
 \quad \beta\le\min\{(4-2a)/3,\ 2-2a\}.          \tag{GS9}
\]
例如 a=0 覆盖 Y≤T^{4/3}；a=1/4 覆盖 Y≤T^{7/6}；a=1/2
覆盖 Y≤T。各常数尺度与固定对数成本由 ε 吸收。对这些范围的
全部 B dyadic 块求和只有对数成本。它不是原 q 外层的结论。

完整边界账本：

- 原 GE2 的 d=1 端点由 d≈S/e≳T 排除；U=1 无整数过渡边界。
  K>2 排除 κ=e=1 的独立纠正。不会因选择 B-shell 而重新引入它们。
- l 分片光滑、支撑远离0，零延拓后可用 GS3，没有硬 l 端点。
  B 的 [Y,2Y) 端点从未被积分替换；GS5 已包含整数 +1。
- M 均值的所有除数截断误差由 JT9/GS2 支付，不把 d>X 的
  连续项误当作不存在。对 n=0 不用均值定理；它已被 critical
  cutoff 排除，原 ℓ=0 另在 GE 中计费。
- 若需要字面有限 ν 和，取 F=T^δ、δ>0。GS4 和移位格求和
  给窗口外 O(T^ε K₂(1+1/K₂)F^{1-J})。用 |κ_M(n)|≤M、
  #M≪X、#n≪Y 等保守计费，单 B-shell 的完整物理尾至多
  O(T^{8+ε+δ(1-J)})（Y≲S）；选择 J 足够大后任意幂次小。
  窗口与 M 无关，因此不会破坏 GS2 的光滑性。
- GE10 的非critical 尾 O(T^{7-L+ε}) 和原 ℓ=0 尾
  O(T^{6-J+ε}) 独立保留。这里不需要 GE8 的新增 h-Fourier
  截断；若改用 GE9 比较 determinant 子项，再单独使用 GE10。

因此该范围内的完整指定光滑 core（critical 加上述补集）
为 O(T^{3+ε})。这并不包括此前独立列出的 AFE 物理尾。

## 6. 与 determinant 路线及完整目标的关系

本轮首先核验了 [Bettin–Chandee Corollary 1 及 §9](https://arxiv.org/pdf/1502.00769)：
其 determinant 误差由带乘积频率的模逆相位产生。逐个 Δ 使用
该结论需要另付 Δ 与冻结短斜率的数量，不能当成保留整个参数
平均的估计。这里没有声称完成该谱 adapter；GS3–GS7 给出
一个自包含、可以验证的新实际子域覆盖。

相较 GE12 仅估计精确 Δ=0，本节估计整个 GS1，故也包括新
覆盖范围内的非零 Δ：由 GE12 的同范围限制和三角不等式，该
补集也在预算内。不能把 GS6 与 GE12 两个未经识别的“密度”
从原式重复扣除。剩余更长 B 仍要保留 µ(M)µ(B) 的全局
determinant/dispersion 结构；不能用 GS9 在覆盖外宣布结论。

有限脚本只检验 GS5 窗口的精确整数端点、符号、无互素掩码和
GS8–GS9 的成本；解析导数、Poisson 和全目标界由数学证明承担。
