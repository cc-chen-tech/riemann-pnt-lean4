# 任务 A：Selberg Möbius mollifier 的 LCM 主项

> **证明状态。** 第 2--3 节是完全有限、初等且逐项可核验的证明，给出本任务所需的
> \(T^\varepsilon\) 上界；第 4 节的主常数求值是无条件的经典复分析论证，但尚未在
> Lean 中形式化。本文不声称控制 twisted moment 的 off-diagonal 余项，也不新增
> 仓库内已核验定理。

## 1. 结论

设 \(N\ge 2\)、\(T>1\)，并令

\[
 a_d=\mu(d)\frac{\log (N/d)}{\log N}\qquad(1\le d\le N).
\]

对任意固定实常数 \(C_W\)，定义

\[
 \mathcal Q_{N,T}
 =\sum_{d,e\le N}\frac{a_da_e}{[d,e]}
 \left(\log\frac{T(d,e)^2}{2\pi de}+C_W\right).
\]

本文证明以下无条件显式估计：

\[
 \boxed{
 |\mathcal Q_{N,T}|
 \le
 \bigl(|\log(T/(2\pi))+C_W|+6\log N\bigr)
 (1+\log N)^3.}
 \tag{1.1}
\]

特别地，当 \(T\ge2\) 且 \(N\le T^3\) 时，

\[
 |\mathcal Q_{N,T}|
 \le
 \bigl(|C_W|+\log(2\pi)+19\log T\bigr)
 (1+3\log T)^3
 \ll_{C_W}(1+\log T)^4.
 \tag{1.2}
\]

所以对每个 \(\varepsilon>0\)，

\[
 \boxed{\mathcal Q_{N,T}\ll_{\varepsilon,C_W}T^\varepsilon}
 \qquad(N\le T^3).
 \tag{1.3}
\]

这已经满足任务的强制成功判据：若 twisted moment 的主项为
\(T\mathcal Q_{N,T}\)（乘上一个固定光滑权重的质量也无妨），则

\[
 T\mathcal Q_{N,T}=O_{\varepsilon,C_W}(T^{1+\varepsilon})
\]

在 \(\theta=3\) 仍然成立。这里没有使用任何关于 off-diagonal 余项的估计。

此外，经典的 Selberg--Perron/Euler-product 求值给出：对固定
\(\theta>0\)，若 \(N=\lfloor T^\theta\rfloor\)，则

\[
 \boxed{\mathcal Q_{N,T}=1+\frac1\theta+o_{\theta,C_W}(1).}
 \tag{1.4}
\]

因此 \(\theta=3\) 时有限 LCM 主项的主常数为 \(4/3\)。式 (1.4) 是纯算术
LCM 和的求值；它不声称长度为 \(T^3\) 的完整 twisted moment 具有同一渐近，
因为后者还需要控制 off-diagonal 余项。

## 2. 完全有限的 gcd/LCM 对角化

以下各式对任意实系数 \(a_1,\ldots,a_N\) 都成立。定义

\[
 X_r:=\sum_{\substack{d\le N\\r\mid d}}\frac{a_d}{d}
     =\frac1r\sum_{m\le N/r}\frac{a_{rm}}m,
 \qquad
 Y_r:=\sum_{\substack{d\le N\\r\mid d}}\frac{a_d\log d}{d}.
 \tag{2.1}
\]

再定义 Jordan-totient 的对数导数权

\[
 \Psi(r):=\sum_{k\mid r}\mu(r/k)k\log k.
 \tag{2.2}
\]

### 2.1 无对数核

由

\[
 \frac1{[d,e]}=\frac{(d,e)}{de}
 =\frac1{de}\sum_{r\mid d,\ r\mid e}\varphi(r)
\]

以及有限和换序，严格地得到

\[
 \boxed{
 \sum_{d,e\le N}\frac{a_da_e}{[d,e]}
 =\sum_{r\le N}\varphi(r)X_r^2.}
 \tag{2.3}
\]

这是一个真正的平方和；没有延长求和范围，也没有截断误差。

### 2.2 \(\log d\) 和 \(\log e\)

在同一个有限换序中把 \(a_d/d\) 替换为 \(a_d\log d/d\)，得到

\[
 \sum_{d,e\le N}\frac{a_da_e}{[d,e]}\log d
 =\sum_{r\le N}\varphi(r)X_rY_r.
 \tag{2.4}
\]

交换 \(d,e\) 给出完全相同的 \(\log e\) 项，故

\[
 \sum_{d,e\le N}\frac{a_da_e}{[d,e]}(\log d+\log e)
 =2\sum_{r\le N}\varphi(r)X_rY_r.
 \tag{2.5}
\]

### 2.3 \(\log(d,e)\)

Möbius 反演应用于 \(n\log n\) 给出

\[
 n\log n=\sum_{r\mid n}\Psi(r).
 \tag{2.6}
\]

于是

\[
 \frac{(d,e)\log(d,e)}{de}
 =\frac1{de}\sum_{r\mid d,\ r\mid e}\Psi(r),
\]

从而

\[
 \boxed{
 \sum_{d,e\le N}\frac{a_da_e}{[d,e]}\log(d,e)
 =\sum_{r\le N}\Psi(r)X_r^2.}
 \tag{2.7}
\]

设

\[
 J_z(r):=\sum_{k\mid r}\mu(r/k)k^z.
\]

则 \(J_1(r)=\varphi(r)\)，而

\[
 \Psi(r)=\left.\frac{d}{dz}J_z(r)\right|_{z=1}.
\]

因此 (2.7) 正是题目要求的参数微分版本。

对 \(r\ge1\)，Euler 乘积还给出精确公式

\[
 \boxed{
 \Psi(r)=\varphi(r)
 \left(\log r+\sum_{p\mid r}\frac{\log p}{p-1}\right).}
 \tag{2.8}
\]

空和约定使 (2.8) 对 \(r=1\) 也成立。特别地，

\[
 0\le\Psi(r)\le2\varphi(r)\log r,
 \tag{2.9}
\]

因为 \((p-1)^{-1}\le1\) 且
\(\sum_{p\mid r}\log p=\log\operatorname{rad}(r)\le\log r\)。

### 2.4 总公式

记

\[
 c_T:=\log\frac{T}{2\pi}+C_W.
\]

将 (2.3)、(2.5)、(2.7) 合并，得到所求完整对角化：

\[
 \boxed{
 \mathcal Q_{N,T}
 =\sum_{r\le N}\bigl(c_T\varphi(r)+2\Psi(r)\bigr)X_r^2
  -2\sum_{r\le N}\varphi(r)X_rY_r.}
 \tag{2.10}
\]

等价地，令

\[
 \mathcal K_N(u,v,w)
 :=\sum_{d,e\le N}
 \frac{a_da_e(d,e)^{1+w}}{d^{1+u}e^{1+v}}.
\]

因为求和有限，可以逐项微分而没有一致收敛问题，并且

\[
 \mathcal Q_{N,T}
 =c_T\mathcal K_N(0,0,0)
 +2\partial_w\mathcal K_N(0,0,0)
 +\partial_u\mathcal K_N(0,0,0)
 +\partial_v\mathcal K_N(0,0,0).
 \tag{2.11}
\]

这里 \(u,v\) 导数自带负号，因为
\(\partial_u d^{-1-u}|_{u=0}=-(\log d)/d\)。

## 3. 初等上界及全部有限边界

对 Selberg 系数，当 \(1\le d\le N\) 时，

\[
 0\le\frac{\log(N/d)}{\log N}\le1,
 \qquad |a_d|\le1.
 \tag{3.1}
\]

对 \(1\le r\le N\)，置

\[
 U_r:=\frac1r H_{\lfloor N/r\rfloor},
 \qquad H_m:=\sum_{j=1}^m\frac1j.
\]

由 (2.1) 逐项取绝对值得

\[
 |X_r|\le U_r,
 \qquad |Y_r|\le(\log N)U_r.
 \tag{3.2}
\]

再用

\[
 H_m\le1+\log m,
 \quad \varphi(r)\le r,
 \quad \sum_{r\le N}\frac1r\le1+\log N,
\]

可得

\[
 \begin{aligned}
 \sum_{r\le N}\varphi(r)U_r^2
 &\le\sum_{r\le N}\frac{(1+\log(N/r))^2}{r}\\
 &\le(1+\log N)^3.
 \end{aligned}
 \tag{3.3}
\]

因此

\[
 \sum_{r\le N}\varphi(r)X_r^2\le(1+\log N)^3,
 \tag{3.4}
\]

\[
 \left|\sum_{r\le N}\varphi(r)X_rY_r\right|
 \le(\log N)(1+\log N)^3,
 \tag{3.5}
\]

以及由 (2.9)

\[
 0\le\sum_{r\le N}\Psi(r)X_r^2
 \le2(\log N)(1+\log N)^3.
 \tag{3.6}
\]

将 (3.4)--(3.6) 代入 (2.10)，即得 (1.1)。注意这里甚至没有使用
Möbius 函数的消去；Möbius 只通过 \(|a_d|\le1\) 出现。因此强制的
\(T^\varepsilon\) 上界比 Selberg sieve 的渐近求值弱得多。

### 3.1 边界和截断审计

1. **右端点 \(d=N\)**：\(a_N=0\) 精确成立。保留 \(d=N\) 不产生误差；也可把有效支撑写成 \(d\le N-1\)。
2. **除数变量 \(r\)**：若 \(r>N\)，则 \(r\mid d\le N\) 的纤维为空，所以 (2.3)--(2.10) 在 \(r=N\) 精确终止。
3. **商的取整**：\(m\le N/r\) 始终表示 \(m\le\lfloor N/r\rfloor\)；调和数中的 floor 没有被删除。
4. **有限换序**：所有和都在有限集合上；没有 Fubini、绝对收敛或极限交换误差。
5. **参数微分**：有限和逐项微分是恒等式，不产生解析截断误差。
6. **常数项**：\(C_W\) 和 \(-\log(2\pi)\) 完整地保留在 \(c_T\) 中，没有吸收到未说明的 \(O(1)\) 内。
7. **小 \(T\)**：主要陈述取 \(T\ge2\)。若只假设 \(T>1\) 且 \(N\le T^3\)，区间 \(1<T<2\) 只允许有限多个整数 \(N\le7\)，可直接扩大依赖 \(C_W,\varepsilon\) 的常数。
8. **非整数 \(T^\theta\)**：取 \(N=\lfloor T^\theta\rfloor\)。上界只用 \(N\le T^3\)，不产生额外项；渐近中
   \(\log N=\theta\log T+O(T^{-\theta})\)。

## 4. 主常数 \(1+1/\theta\)

本节只求有限 LCM 和，不处理 twisted moment 的 off-diagonal 余项。

令 \(L=\log N\)，并写

\[
 S_0(N):=\sum_{d,e\le N}\frac{a_da_e}{[d,e]},
\]

\[
 S_1(N):=\sum_{d,e\le N}\frac{a_da_e}{[d,e]}
 \log\frac{(d,e)^2}{de}.
\]

则

\[
 \mathcal Q_{N,T}=\bigl(\log(T/(2\pi))+C_W\bigr)S_0(N)+S_1(N).
 \tag{4.1}
\]

### 4.1 三变量 Euler 乘积

在绝对收敛区定义

\[
 F(s,t,w):=
 \sum_{d,e\ge1}\frac{\mu(d)\mu(e)}{[d,e]d^se^t}
 \left(\frac{(d,e)^2}{de}\right)^w.
\]

逐素数考察 \(p\nmid de,p\mid d,p\mid e,p\mid(d,e)\) 四种情形，得到

\[
 F(s,t,w)=\prod_p
 \left(1-p^{-1-s-w}-p^{-1-t-w}+p^{-1-s-t}\right).
 \tag{4.2}
\]

抽出三个 zeta 因子：

\[
 \boxed{
 F(s,t,w)=
 \frac{\zeta(1+s+t)}{\zeta(1+s+w)\zeta(1+t+w)}
 H(s,t,w),}
 \tag{4.3}
\]

其中

\[
 H_p(s,t,w)=
 \frac{(1-p^{-1-s-w}-p^{-1-t-w}+p^{-1-s-t})
       (1-p^{-1-s-t})}
      {(1-p^{-1-s-w})(1-p^{-1-t-w})}.
\]

因为 \(H_p=1+O(p^{-2+\delta})\) 在原点的一个固定小多圆盘上一致成立，
\(H=\prod_pH_p\) 在那里绝对收敛且全纯，并且

\[
 H(0,0,0)=1.
 \tag{4.4}
\]

由 ζ 在 1 的 Laurent 展开，原点附近

\[
 F(s,t,0)=\frac{st}{s+t}
 +O\left(\frac{|st|(|s|+|t|)}{|s+t|}+|st|\right),
 \tag{4.5}
\]

而对 \(w\) 微分后

\[
 \left.\partial_wF(s,t,w)\right|_{w=0}
 =1+O(|s|+|t|)+O\left(\frac{|st|}{|s+t|}\right).
 \tag{4.6}
\]

式 (4.6) 中的常数 1 来自

\[
 \left.\partial_w\frac{(s+w)(t+w)}{s+t}\right|_{w=0}=1.
\]

这正是最终主常数中的额外“1”。

### 4.2 双 Perron 求值

精确 Mellin--Perron 公式

\[
 \log(N/d)_+
 =\frac1{2\pi i}\int_{(c)}(N/d)^s\frac{ds}{s^2}
 \qquad(c>0)
\]

给出

\[
 S_0(N)=\frac1{L^2}\frac1{(2\pi i)^2}
 \int_{(c)}\int_{(c)}
 N^{s+t}F(s,t,0)\frac{ds\,dt}{s^2t^2},
 \tag{4.7}
\]

\[
 S_1(N)=\frac1{L^2}\frac1{(2\pi i)^2}
 \int_{(c)}\int_{(c)}N^{s+t}
 \left.\partial_wF(s,t,w)\right|_{w=0}
 \frac{ds\,dt}{s^2t^2}.
 \tag{4.8}
\]

用经典 de la Vallée Poussin 零点自由区把两个截断积分移到绕开 zeta 零点的
PNT 轮廓。在移线前取高度 \(V\to\infty\)，Perron 截断误差先按固定 \(N\)
趋于零；随后令 \(N\to\infty\)。零点自由区、zeta 的竖直增长界以及
\(H\) 的局部一致有界性表明：(4.5) 的非主部分在除以 \(L^2\) 后是
\(o(L^{-1})\)，(4.6) 的非主部分在除以 \(L^2\) 后是 \(o(1)\)。这就是
通常的二变量 Selberg--Perron 引理；它只需 PNT 级别的零点自由区。
主模型积分可以直接计算：

\[
 \frac1{(2\pi i)^2}\int\!\!\int
 \frac{N^{s+t}}{st(s+t)}\,ds\,dt=L,
 \tag{4.9}
\]

因为 \(1/(s+t)=\int_0^\infty e^{-(s+t)u}du\)，两个 Perron 阶跃函数
同时为 1 的范围恰为 \(0<u<L\)。同样，

\[
 \frac1{(2\pi i)^2}\int\!\!\int
 \frac{N^{s+t}}{s^2t^2}\,ds\,dt=L^2.
 \tag{4.10}
\]

故

\[
 \boxed{S_0(N)=\frac{1+o(1)}{\log N},}
 \tag{4.11}
\]

\[
 \boxed{S_1(N)=1+o(1).}
 \tag{4.12}
\]

这里的轮廓余项只使用通常的 PNT 零点自由区；若希望完全“初等化”，可用
Selberg 的初等 PNT 和相应的 Selberg sieve 基本引理替换双 Perron 移线。

当 \(N=\lfloor T^\theta\rfloor\)、固定 \(\theta>0\) 时，把
(4.11)--(4.12) 代入 (4.1)：

\[
 \begin{aligned}
 \mathcal Q_{N,T}
 &=\frac{\log T}{\log N}+1+o_{\theta,C_W}(1)\\
 &=1+\frac1\theta+o_{\theta,C_W}(1).
 \end{aligned}
\]

固定的 \(C_W\) 和 \(-\log(2\pi)\) 只乘 \(S_0(N)=O(1/\log N)\)，所以不改变主常数。

这一常数也与 Kühn--Robles--Zeindler 对线性 mollifier \(P(u)=u\) 的公式
\(1+\theta^{-1}\int_0^1(P'(u))^2du=1+1/\theta\) 一致。Bettin--Chandee--Radziwiłł
给出的 twisted-second-moment 算术主项正是本文的 LCM 核；他们论文中的
mollifier 长度限制属于 off-diagonal 估计，而不是有限和 (4.1) 的限制。

### 4.3 不依赖长 mollifier 余项的独立反推

还有一个方便的严格交叉验证，它只在两个辅助的短 mollifier 尺度上调用已发表的
twisted-moment 定理。任选

\[
 0<\alpha<\beta<\frac12
\]

并对同一个整数 \(N\) 置

\[
 T_\alpha=N^{1/\alpha},\qquad T_\beta=N^{1/\beta}.
\]

在这两个尺度上，经典的短-mollifier 定理适用；Bettin--Chandee--Radziwiłł
识别出的 LCM 主项与 Kühn--Robles--Zeindler 的 \(P(u)=u,Q=1,R=0\)
求值合起来给出

\[
 \mathcal Q_{N,T_\alpha}=1+\frac1\alpha+o(1),\qquad
 \mathcal Q_{N,T_\beta}=1+\frac1\beta+o(1).
 \tag{4.13}
\]

另一方面，(4.1) 对 \(\log T\) 是精确的仿射函数，所以

\[
 \mathcal Q_{N,T_\alpha}-\mathcal Q_{N,T_\beta}
 =\left(\frac1\alpha-\frac1\beta\right)(\log N)S_0(N).
 \tag{4.14}
\]

比较 (4.13)--(4.14)，由于 \(\alpha\ne\beta\)，得到

\[
 (\log N)S_0(N)=1+o(1).
\]

再代回 (4.13) 中任一式，固定的 \(C_W-\log(2\pi)\) 只贡献
\(O(S_0(N))=o(1)\)，故 \(S_1(N)=1+o(1)\)。最后再次使用 (4.1)，便对
任意固定 \(\theta>0\) 得到

\[
 \mathcal Q_{N,N^{1/\theta}}=1+\frac1\theta+o(1).
\]

这个反推没有假设长度 \(N=T^3\) 的 off-diagonal 可控：off-diagonal 定理只在
两个辅助尺度 \(\alpha,\beta<1/2\) 上使用；从短尺度到 \(\theta=3\) 的步骤完全是
有限 LCM 和对 \(\log T\) 的代数恒等式。

## 5. 仅用初等方法能得到什么

| 目标 | 所需输入 | 结论 |
|---|---|---|
| \(\mathcal Q_{N,T}\ll_\varepsilon T^\varepsilon\), \(N\le T^3\) | gcd/totient 恒等式、调和和上界 | **完全足够**；甚至不需 Möbius 消去或 Euler 乘积 |
| \(\mathcal Q_{N,T}=O(1)\) | Selberg sieve 基本引理或 Euler product/PNT | 可以 |
| 主常数 \(1+1/\theta\) | 二变量 Selberg--Perron 求值，或等价的 Selberg sieve 渐近 | 可以；固定 \(\theta>0\) 无长度障碍 |
| 完整 twisted moment 在 \(\theta=3\) 的渐近 | off-diagonal Kloosterman/移位卷积估计 | 本文不提供；这正是剩余困难 |

## 6. 可直接形式化的有限和命题

以下命题均不涉及渐近、无限级数或复分析，适合作为 Lean 的第一批接口。

### 命题 F1：一般 reciprocal-LCM 平方和

对 \(N\in\mathbb N\) 和 \(a:\mathbb N\to\mathbb R\)，

\[
 \sum_{d\in[1,N]}\sum_{e\in[1,N]}
 a_d a_e([d,e]:\mathbb R)^{-1}
 =\sum_{r\in[1,N]}(\varphi(r):\mathbb R)
 \left(\sum_{d\in[1,N],\ r\mid d}\frac{a_d}{d}\right)^2.
\]

仓库中的 `MathlibAux.sum_reciprocal_lcm_quadratic_eq_totient_squares`
已经给出此命题。

### 命题 F2：有限 gcd-log Möbius反演

定义

\[
 \operatorname{gcdLogWeight}(r)
 :=\sum_{k\in r.\mathrm{divisors}}
 (\mu(r/k):\mathbb R)(k:\mathbb R)\log k.
\]

则对 \(n>0\)，

\[
 (n:\mathbb R)\log n
 =\sum_{r\in n.\mathrm{divisors}}\operatorname{gcdLogWeight}(r).
\]

### 命题 F3：gcd-log 平方和

\[
 \sum_{d,e\in[1,N]}a_da_e([d,e]:\mathbb R)^{-1}
 \log(\gcd(d,e))
 =\sum_{r\in[1,N]}\operatorname{gcdLogWeight}(r)
 \left(\sum_{d\in[1,N],\ r\mid d}\frac{a_d}{d}\right)^2.
\]

### 命题 F4：单边 log-index 双线性式

\[
 \sum_{d,e\in[1,N]}a_da_e([d,e]:\mathbb R)^{-1}\log d
 =\sum_{r\in[1,N]}(\varphi(r):\mathbb R)
 \left(\sum_{d\in[1,N],\ r\mid d}\frac{a_d}{d}\right)
 \left(\sum_{d\in[1,N],\ r\mid d}\frac{a_d\log d}{d}\right).
\]

### 命题 F5：完整 LCM-log 对角化

把 F1、F3、F4 线性组合，得到 (2.10) 的 `Finset.Icc 1 N` 版本。
此命题应对任意实系数成立；Selberg Möbius 系数只在后续 bound 中实例化。

### 命题 F6：有限显式 bound

若 \(2\le N\) 且对所有 \(d\in[1,N]\) 有 \(|a_d|\le1\)，则

\[
 |\mathcal Q_{N,T}|
 \le(|c_T|+6\log N)(1+\log N)^3.
\]

形式化时可先保留精确调和数版本

\[
 |\mathcal Q_{N,T}|
 \le(|c_T|+6\log N)
 \sum_{r=1}^N\frac{H_{\lfloor N/r\rfloor}^2}{r},
\]

再调用 `harmonic_le_one_add_log` 得到闭式 bound。

## 7. 与现有仓库结构的接口

- `HardyTheorem/SelbergMollifier.lean` 已定义 `selbergMoebiusCoeff` 并证明
  区间内绝对值不超过 1。
- `MathlibAux/GcdLcmQuadratic.lean` 已证明 F1。
- 建议未来新增独立的 `MathlibAux/GcdLcmLogQuadratic.lean` 实现 F2--F5，
  再由 Hardy 层实例化 F6；不要把一般有限算术恒等式塞进 mollifier 的分析模块。
- 本文没有修改上述仓库文件。

## 8. 参考核对

1. S. Bettin, V. Chandee, M. Radziwiłł,
   [*The mean square of the product of the Riemann zeta-function with Dirichlet polynomials*](https://arxiv.org/abs/1411.7764).
   其式 (1.2) 给出同一个 gcd/LCM 算术主项，并明确把长度障碍放在 off-diagonal 分析中。
2. P. Kühn, N. Robles, D. Zeindler,
   [*On a mollifier of the perturbed Riemann zeta-function*](https://arxiv.org/abs/1605.02604).
   Theorem 1.5 在 \(P(u)=u,Q=1,R=0\) 时给出 \(1+1/\theta\)。
