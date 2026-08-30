# 实际 quotient 的频率支撑与原变量上的有理过渡区

把 quotient 的实际 Fourier 形状代回后，频率不能再任意选择：它会恢复原
正区间支撑。因而前次通用核中靠近零相位的例子，不是这个物理核的障碍。
另一方面，原比值靠近非零有理数的过渡区仍然存在。本笔记给出该区的
统一核渐近式，连同真实 Möbius 系数、同余条件和互素条件完整保留。

这里完成的是解析核与有限系数的准确重组，不是所需的有符号相关估计。
不证明长 mollifier 渐近式、eventual `14/17` 或 `2/3`，不修改 Lean。
“实际”指使用 quotient 步骤强制产生的 Fourier 形状；完整 AFE/QCT 各项的
一致核半范数及硬端点仍须核查，本文不默认它们都满足渐近式的光滑假设。
承接[共同核有理点消去](2026-08-30-joint-kernel-rational-flatness.md)及
[平方自由完成](2026-08-30-joint-mode-squarefree-completion.md)。

## 1. 第二次 Fourier 变换恢复的是真实正区间

采用前次的 \(e(x)=\exp(2\pi i x)\) 及 Fourier 符号约定。令
\(F_s(x,z,v)\in C_c^\infty((1,2)^3)\)，其中 \(x\) 对应原整数变量
\(r/R\)，\(z,v\) 对应 \(h/H,\delta/L\)。允许三变量真正耦合。
取 \(R,H,L>0\) 及正整数 \(C,s\)，\(s\ge2,(C,s)=1\)。固定 quotient 组件是

\[
 M_C(s)=\frac1R\sum_{\substack{n\ge1\\(n,s)=1}}
 \sum_{h,\delta\in\mathbb Z}
 F_s(Cn/R,h/H,\delta/L)e(-h\delta\overline{Cn}/s).
 \tag{1}
\]

记 \(\widehat F_{s,1}\) 是只对第一坐标作 Fourier 变换。quotient Poisson
的精确形式为

\[
 M_C(s)=\frac1{Cs}\sum_{m,h,\delta}
 \widehat F_{s,1}\!\left(\frac{mR}{Cs},h/H,\delta/L\right)
 S(\bar C m,-h\delta;s). \tag{2}
\]

因此，前次以 \(y=m/C\) 写出的实际核不是任意 Schwartz 函数，而是

\[
 \Psi_s(y,z,v)=\widehat F_{s,1}((R/s)y,z,v).
\]

再次对 \(y\) 变换，Fourier 反演严格给出

\[
 \boxed{\Phi_{s;\lambda}(z,v)
 =\frac{s}{R}F_s(-\lambda s/R,z,v).} \tag{3}
\]

在 \(s=de\)、\(\lambda=jC/d\) 的共同完成中，支撑因而强制

\[
\boxed{j<0,\qquad R<-jCe<2R.} \tag{4}
\]

固定 \(C,d,e\) 后，实际 \(j\) 和因此有限；若 \(Ce\ge2R\)，整个该项为零。
这些是原支撑的精确复原，不另计一份幂次收益。

当 \(R/s\) 被上下正常数控制时，\(\lambda\) 与零保持正常数距离。
故前次通用核的 \(j=1,A\asymp T^2,d\asymp T^3\) 正频率见证，在本核类
中精确为零。前次通用核定理没有错误，但不能据此指定物理困难子区间。

## 2. 所有余因子一起恢复原互素条件

这一步甚至不要求 \(s\) 平方自由，也不需要除以 \(\mu(s)\)。对 (2)
先作双 Poisson，再使用通用恒等式

\[
 c_s(N)=\sum_{\substack{d\mid s\\d\mid N}}d\mu(s/d).
\]

在 \(m=dc-Ckl\) 上作 \(c\)-Poisson，其 \(C/d\) Jacobian 与以上 \(d\)
及外面的 \(1/C\) 正好抵消。再用 (3)，得到

\[
 \boxed{M_C(s)=\frac{HL}{Rs}
 \sum_{e\mid s}\mu(e)\sum_{j\in\mathbb Z}
 \mathcal K_{s/H,s/L;F_s(-jCe/R,\cdot,\cdot)}(jCe/s).} \tag{5}
\]

这里 \(e\mid s\) 是全部除数，没有额外加入 \((e,s/e)=1\)。若外面另乘
\(\mu(s)\)，非平方自由 \(s\) 本来就不贡献，才可与前次平方自由展开对应。

由 (4)，令 \(n=-je\ge1\)。每个 \(e\mid(n,s)\) 上的核和支撑相同，故

\[
 \sum_{e\mid(n,s)}\mu(e)=\mathbf1_{(n,s)=1}
\]

给出精确重组

\[
 \boxed{M_C(s)=\frac{HL}{Rs}
 \sum_{\substack{n\ge1\\(n,s)=1}}
 \mathcal K_{s/H,s/L;F_s(Cn/R,\cdot,\cdot)}(-Cn/s).} \tag{6}
\]

任何仅依赖 \((-Cn/s,s)\) 的共同有界权，都可原样带过这一步，包括前次
深有理邻域的指示函数。依赖单独 \(e\) 的任意权则不行。不能把所有
\(e>1\) 单独删去：它们通过带符号容斥恢复互素条件。

从 (1) 直接对 \(h,\delta\) 作双 Poisson，也得到 (6)。因此这个回路是
原变量的准确复原，不是又获得了一份算术节省。

## 3. 平方自由权和完整 Type 条件也必须一起复原

令 \(C=At^2b\)。固定原 quotient \(v=r/A\)，前次修正中的全部系数满足

\[
 \boxed{
 \sum_{\substack{t^2b\mid v\\(t,A)=1\\b\mid A}}\mu(t)\mu(b)
 =\mu^2(v)\mathbf1_{(v,A)=1}.} \tag{7}
\]

证明：固定 \(t\)，由于 \((t,A)=1\)，内层 \(b\) 和是
\(\sum_{b\mid(v,A)}\mu(b)\)。若 \((v,A)>1\) 则为零；否则所有
\(t^2\mid v\) 自动与 \(A\) 互素，余下为 \(\mu^2(v)\)。原有限平方除数
截断必须覆盖 \(v\) 的全部有效平方除数。

恢复 \(\mu(r)\) 时，还须完整保留 Type 恒等式。用 \(r=abv\) 的原符号，
对 \(r>U\)，

\[
 \mu(r)=-\sum_{\substack{abv=r\\a\le U,\ av>U}}\mu(a)\mu(b).
 \tag{8}
\]

若在每项保留 \(\mu^2(r)\)，还须保留
\(\mathbf1_{(a,b)=1}\mu^2(v)\mathbf1_{(v,ab)=1}\)。这里的 Type 因子
\(b\) 与 (7) 的 divisor-layer 记号用途不同，不可混淆。
共同的 \(r/s\) 权不破坏 (7)–(8)，但单个截断 Type 盒或分解依赖权重
不能擅自替换成完整卷积。所有光滑分区及原始端点也必须先合法重组。

## 4. 原变量的精确共同核表达式

对上述原光滑核，定义归一化算术和

\[
 \mathcal O[F]=\frac1R
 \sum_{\substack{r\ge1,\ S<s<2S\\(r,s)=1}}\mu(r)\mu(s)
 \sum_{h,\delta}F_s(r/R,h/H,\delta/L)e(-h\delta\bar r/s).
 \tag{9}
\]

直接双 Poisson 给

\[
 \boxed{\mathcal O[F]=\frac{HL}{R}
 \sum_{\substack{r,s\\(r,s)=1}}\frac{\mu(r)\mu(s)}s
 \mathcal K_{P_s,Q_s;F_s(r/R,\cdot,\cdot)}(-r/s),
 \quad P_s=s/H,\quad Q_s=s/L.} \tag{10}
\]

求和仍保留 (9) 的全部范围；乘共同的 ratio cutoff 同样成立。
这既可直接证明，也可通过 (2)–(8) 得到，是不同完成次序的交叉检查。

因为 \((r,s)=1\)，精确相位 \(-r/s\) 的约分分母就是 \(s\)。在平衡范围
\(s\asymp T^3,P_s,Q_s\asymp T^{1/2}\) 内，它不是小分母有理点。
不能把前次精确零、原互素条件和余因子容斥分别算作三份收益。
仍然有用的是小分母有理数**附近**的核估计。
\(\mathcal K\) 对相位具有周期性，但其 \(F_s(r/R,\cdot,\cdot)\) 权重
不能随相位一起模一约化；该权始终保留实际 \(r/R\)。

## 5. 有理过渡区的统一解析主项

对固定 \(\Phi\in C_c^\infty((1,2)^2)\)，定义

\[
 I_{c;\Phi}(\xi,\nu)=\iint\widehat\Phi(u,v)
 e(-cuv+\xi u+\nu v)\,du\,dv.
\]

取 \((a,q)=1,q\ge1\)。按模 \(q\) 分组后 Poisson，得到精确的变形有理公式

\[
 \boxed{\mathcal K_{P,Q;\Phi}\!\left(\frac aq+\frac c{PQ}\right)
 =\frac{PQ}{q}\sum_{h,v\in\mathbb Z}
 e(\bar a hv/q)I_{c;\Phi}(Ph/q,Qv/q).} \tag{11}
\]

\(q=1\) 的相位仍按一处理。函数
\(\widehat\Phi(u,v)e(-cuv)\) 在任何固定有界 \(c\) 集上是一致 Schwartz
族，包括 \(c=0\)。因此其逆 Fourier 变换 \(I_{c;\Phi}\) 也是。
当 \(1\le q\le\min(P,Q)\) 时，分出唯一的 \((h,v)=(0,0)\) 项可得

\[
 \boxed{\frac{\mathcal K(a/q+c/(PQ))}{PQ}
 =\frac1q\mathcal I_c[\Phi]
 +O_{N,\Phi,c}\!\left(\frac1q
       \left[(q/P)^N+(q/Q)^N\right]\right),} \tag{12}
\]

其中对 \(c\ne0\)，

\[
 \mathcal I_c[\Phi]=I_{c;\Phi}(0,0)
 =\frac1{|c|}\iint\Phi(x,y)e(xy/c)\,dxdy,
 \qquad \mathcal I_0[\Phi]=0. \tag{13}
\]

误差对约分分子 \(a\) 一致。需要小误差时要求 \(q\ll\min(P,Q)\)；
这与前次精确零使用的 \(q\le\max(P,Q)/2\) 是不同条件，不能互换。
对参数化核，只要所需半范数一致至多为对数幂，误差也只损失该对数幂。

## 6. 带真实系数和 gcd 的 packet 公式

固定约分 \(p/q>0\)，令

\[
 w=qr-ps,\qquad W_s=HL/s,\qquad z=\frac{w}{qW_s}.
 \tag{14}
\]

则 \(-r/s=-p/q-z/(P_sQ_s)\)。取固定光滑函数 \(\chi\)，其支集位于
远离零的固定紧集。在 (10) 中乘 \(\chi(z)\)，由 (12) 得到此 packet 的
主项

\[
 \boxed{\begin{aligned}
 \mathcal P_{p,q}={}&
 \sum_{S<s<2S}\sum_{\substack{w\equiv-ps\ (\mathrm{mod}\ q)\\
 r=(ps+w)/q\ge1\\(r,s)=1}}
 \mu(s)\mu(r)\frac{s}{Rq}\chi\!\left(\frac{w}{qW_s}\right)
 \mathcal I_{-w/(qW_s)}[F_s(r/R,\cdot,\cdot)].
 \end{aligned}} \tag{15}
\]

归一化可逐项核查：\((HL/(Rs))(P_sQ_s/q)=s/(Rq)\)。
绝不冻结 \(r/R\) 的权重。即使 \(q=1,p=1\)，把
\(U((s+w)/R)\) 换成 \(U(s/R)\) 通常也只产生 \(O(|w|/R)\) 误差，
不是快速衰减误差。

当 \(q>1\) 时，互素条件必须保持为
\(\gcd((ps+w)/q,s)=1\)。只有额外满足 \((q,s)=1\)，它才等价于
\((w,s)=1\)。例如 \(q=2,p=1,s=6,r=5\) 给 \(w=4\)：原互素条件成立，
但 \((w,s)=2\)。

每个 \(s\) 的同余条件使有效 \(w\) 数量为 \(O(W_s+1)\)，而不是
\(O(qW_s)\)。若 \(R/S\) 在固定正紧集，且

\[
 q\le \frac{S}{\max(H,L)}T^{-\varepsilon},\qquad\varepsilon>0,
\]

并保留 §5 的一致对数幂半范数假设，则单个 packet 的总误差满足

\[
 O_N\!\left(\frac{S}{q}(HL/S+1)
                T^{-N\varepsilon}(\log T)^{C_N}\right). \tag{16}
\]

这里通过原有 \(r\)-支撑可随时进一步缩小范围。若随后汇总多项 packet，
必须明确一个有限族及其实际分割权；不默认它们自动组成分割。对多项式
数量、至多多项式大的权，增大固定 \(N\) 可以支付全部 (16) 的误差。

## 7. 平衡近对角仍需哪条算术估计

取 \(R=S=T^3,H=L=T^{5/2}\)，并只看 \(s/R\) 位于第一坐标支集的内部
子区间，例如 \([1.4,1.6]\)。当 \(p=q=1\) 时，

\[
 r=s+w,\quad |w|\asymp W_s\asymp T^2,
 \quad (r,s)=1\Longleftrightarrow(w,s)=1. \tag{17}
\]

内部子区间是必要条件。不能同时固定 \(R=s\) 且取一个支撑严格位于
\((1,2)\) 内的 \(U(r/R)\)：那会使 \(r/R\to1\)，把所举的 packet
精确排除。这里始终保持固定 \(R\)、\(s/R\) 位于支集内部及精确 \(r/R\)。

在这个真实有权 packet 上，简单绝对计数只有 \(O(T^5)\)：
\(T^3\) 个 \(s\)，每个有 \(O(T^2)\) 个 \(w\)，主系数 \(s/R\) 有界。
所需归一化 MMKLS 目标仍为 \(T^3(\log T)^{-B}\)，所以还需 \(T^2\)
量级的整体有符号抵消。这是上界账本，不是实际和具有 \(T^5\) 下界。

重新核对 [MRSTT Theorem 1.1(i)](https://arxiv.org/html/2411.05770v2#S1.Thmtheorem1.1)：
该 Möbius 结论提供短区间长度乘任意对数节省，及对数小的异常集；不是
这里所缺的固定幂次。即便额外允许直接套用所有互素层和原权重，
\(T^5(\log T)^{-B}\) 仍不到 \(T^3\)。本文没有声称这套额外统一应用已证。

因此 (15) 把实际 Fourier 支撑、全部 gcd 层、振荡主核与端点同时落到了
原变量上，解析误差可支付；但真正的带符号 Möbius 相关尚未估计。
它也不能不经额外证明就替换成普通 Selberg 方差或 Good–Churchhouse。
下一步需要估计这个真实核，或者与其他原始 packet 联合抵消，而不是
再把同一段几何/Poisson 节省计算一次。

有限核算见 `scripts/check_physical_quotient_transition.py`；它检查频率
支撑、所有余因子与平方自由重组、有限二维完成及 packet 的同余/gcd/
归一化。连续 Poisson、uniform Schwartz 估计和算术目标仍由数学论证区分。

### English scope summary

The actual quotient Fourier transform restores positive original-variable
support, excluding the previous generic near-zero-frequency witness. Full
cofactor and squarefree reassembly recover the original coprimality and Type
coefficients. A uniform rational-transition profile then yields explicit
signed primitive-pair correlations with exact weights and gcd constraints.
Their analytic errors are controlled; the required arithmetic power saving
and all zero-free conclusions remain unproved.
