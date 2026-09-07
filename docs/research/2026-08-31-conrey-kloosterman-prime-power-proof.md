# Conrey 完全 Kloosterman 和：素数幂、退化 gcd 与 CRT 的初等证明

先说结论：本节不再把任意模数的 Weil 界整条作为黑箱。
我们证明实际完全和的两条精确驻相恒等式，处理本原参数的全部
高次素数幂（包括2的幂），并证明一般参数的 gcd 约化和 CRT。
这里本原指 `gcd(a,b,p)=1`。剩余的深输入准确缩小为：
奇素数 p、`p∤ab` 时的 `|K_p(a,b)|<=2 sqrt(p)`。
该素数 Weil 核心及 DI 谱估计仍未在这里自证，也没有新增 Lean 公理。

本节是源 `176a7f63ee568a2ffeae589e15b58fe5e9b850c7` 之后的
独立纸面增量。下文的有限恒等式、素数幂估计和约化均有证明；
没有把另一个任意模数界改名成一个条件接口。

## 1. 与实际 Type I 输入保持同一个完全和

对整数 a,b 和正整数 q，记

\[
 e_q(t)=\exp(2\pi i t/q),\qquad
 K_q(a,b)=\sum_{x\in(\mathbb Z/q\mathbb Z)^\times}e_q(ax+b\bar x),
 \qquad K_1(a,b)=1.
 \tag{K-actual}
\]

`bar x` 是同一模数下的乘法逆元。所有有限式的相位只取整数模q，
不把模逆替换成实数倒数。[实际 Type I 证明](2026-08-31-conrey-actual-mobius-type-i.md)
使用的完全和正是 `K_v(h,l)`，所需界为

\[
 |K_q(a,b)|\le\tau(q)\sqrt q\sqrt{\gcd(a,b,q)}.
 \tag{full-modulus-bound}
\]

来源核对：[Iwaniec--Kowalski, Corollary 11.12, (11.16), p.280](https://people.math.ethz.ch/~kowalski/ik-ant-exp-sums.pdf)。
该页将高次素数幂的初等处理指向后续练习；本节给出在本任务
归一化下的完整推导，而不是引用那个练习作为证明。

先记录单位根正交：对任意 n>=1、整数 d，有限几何级数给出

\[
 \sum_{t=0}^{n-1}e_n(dt)=
 \begin{cases}n,&n\mid d,\\0,&n\nmid d.\end{cases}
 \tag{orthogonality}
\]

第二种情况由 `z=e_n(d)!=1`、`z^n=1` 及
`(1-z) sum_(t=0)^(n-1) z^t=1-z^n=0` 得到。

## 2. 偶数次素数幂的精确驻相

令 p 为任意素数（允许2）、m>=1、`h=p^m,q=h^2`。
每个模q单位唯一写成 `x=r+ht`，其中
`0<=r<h,p∤r,0<=t<h`。对每个 r 选定一个模q逆元整数 u_r。
直接相乘验证

\[
 (r+ht)^{-1}\equiv u_r-ht u_r^2\pmod q.
\]

因而 `ax+b xbar ≡ ar+b u_r+ht(a-b u_r^2) (mod q)`。
对 t 使用 (orthogonality)，仅当 `h|(a-b u_r^2)` 时保留 h 倍。
乘以模h单位 `r^2`，这个条件等价于 `ar^2≡b (mod h)`。
于是对任意 a,b（不要求互素）都有精确恒等式

\[
 \boxed{K_{p^{2m}}(a,b)=p^m
 \sum_{\substack{0\le r<p^m\\p\nmid r\\ar^2\equiv b\ (p^m)}}
 e_{p^{2m}}(ar+b u_r).}
 \tag{even-stationary}
\]

所选模q逆元代表元改变一个 q 的倍数不改变相位。
恒等式保留有限根集合和每个根的相位，不仅是一个范数界。

## 3. 奇数次素数幂必须保留的二次和

令 `q=p^(2m+1),h=p^m,m>=1`。
先将模q单位唯一写成 `x=r'+p^(m+1)t`，其中
`r' mod p^(m+1)` 是单位、`0<=t<p^m`。
因为 `2m+2>=2m+1`，同样的一阶逆元展开和正交给出

\[
 K_q(a,b)=p^m
 \sum_{\substack{r'\bmod p^{m+1}\ \mathrm{unit}\\a(r')^2\equiv b\ (p^m)}}
 e_q(ar'+b\overline{r'}).
 \tag{odd-first-split}
\]

将剩余的 r' 唯一写成 `r+hz`，其中 `0<=r<h,p∤r,0<=z<p`。
固定 u_r 为 r 的模q逆元；由于 `3m>=2m+1`，精确二次展开是

\[
 (r+hz)^{-1}\equiv u_r-hzu_r^2+h^2z^2u_r^3\pmod q.
 \tag{inverse-quadratic}
\]

在根条件 `ar^2≡b (mod h)` 下，整数 `a-bu_r^2` 被 h 整除。
定义模p参数

\[
 A_r=(a-bu_r^2)/h\pmod p,\qquad B_r=bu_r^3\pmod p,
 \qquad G_p(A,B)=\sum_{z=0}^{p-1}e_p(Az+Bz^2).
\]

于是得到第二条精确有限恒等式

\[
 \boxed{K_{p^{2m+1}}(a,b)=p^m
 \sum_{\substack{0\le r<p^m\\p\nmid r\\ar^2\equiv b\ (p^m)}}
 e_q(ar+bu_r)G_p(A_r,B_r).}
 \tag{odd-stationary}
\]

`A_r` 中的除法是先作精确整数除法、再模p；不是在模p里除以h。
两个驻相恒等式均对所有 a,b 成立。只有在接下来估计 Gauss 和时
才要求相应的二次系数非零，不能对退化 b 直接使用 sqrt(p) 界。

## 4. 奇素数的二次和与根数：全部初等

设 p 奇且 `p∤B`。令 `z=w+d`，直接展开模平方得

\[
 |G_p(A,B)|^2
 =\sum_{d\bmod p}e_p(Ad+Bd^2)\sum_{w\bmod p}e_p(2Bdw)=p.
 \tag{Gauss-norm}
\]

这里 `2B` 是模p单位，故内和只有 d=0 时非零。
因此 `|G_p(A,B)|=sqrt(p)`，不需要选择 Gauss 和的具体相位。

若 `p∤ab`，驻相根等价于 `r^2≡b/a (mod p^m)`。
模p至多有两个根：任意两个根 r,s 满足 `(r-s)(r+s)=0`，域中
无零因子使 `r=±s`。每个模 `p^j` 的单位根至多唯一提升为模
`p^(j+1)` 的根，因为候选 `r+p^j t` 的平方为
`r^2+2r p^j t (mod p^(j+1))`，而 `2r` 是模p单位。
归纳得到每个 m>=1 的根数至多2。

若恰有一个 a,b 被 p 整除，则根条件模p已无解。
因此对 primitive 参数 `gcd(a,b,p)=1`、任意 k>=2：

\[
 K_{p^k}(a,b)=0\quad\text{if }p\mid ab,
 \qquad
 |K_{p^k}(a,b)|\le2p^{k/2}\quad\text{if }p\nmid ab.
 \tag{odd-prime-power-bound}
\]

偶 k 用 (even-stationary)，奇 k 用 (odd-stationary) 和
(Gauss-norm)。这部分没有调用素数 Weil 定理。

## 5. 模 2 的例外不能照抄奇素数计算

对 k>=2 的 primitive 参数，若 a,b 中恰有一个偶数，根条件
模2无解，两条驻相式仍给出 `K_(2^k)(a,b)=0`。
下面只需考虑 a,b 都奇数。

记 `R_m(c)` 为模 `2^m` 的奇数平方根数，c 是奇数。有

\[
 R_1(c)\le1,\qquad R_2(c)\le2,\qquad R_m(c)\le4\quad(m\ge3).
 \tag{two-adic-roots}
\]

前两项由模2、模4的单位个数给出。对 m>=3，若无根结论平凡；
否则固定奇根 s。任一另一奇根 r 满足 `2^m|(r-s)(r+s)`。
两个偶数 `r-s,r+s` 中恰有一个被2整除但不被4整除，因为两者
差为 `2s≡2 (mod4)`。故另一因子必被 `2^(m-1)` 整除，
即 `r≡s` 或 `r≡-s (mod 2^(m-1))`。
每个同余类在模 `2^m` 下有两个提升，故至多4根。
该论证也包括 r=±s 的情况，不需要给0定义有限的2-adic估值。

模2的二次和只有两项：

\[
 G_2(A,B)=1+(-1)^{A+B},\qquad |G_2(A,B)|\le2.
 \tag{binary-Gauss}
\]

这里一般不是 sqrt(2)，所以不可使用 (Gauss-norm)。代入两条驻相式：

\[
 |K_{2^{2m}}(a,b)|\le2^m R_m(b/a),\qquad
 |K_{2^{2m+1}}(a,b)|\le2^{m+1}R_m(b/a).
\]

这些初等界已足够匹配所需的除数因子。具体地，偶数次时
`R_m<=2m+1`；奇数次时 `2R_m<=(2m+2)sqrt(2)`。
两者在 m=1、2 直接用 (two-adic-roots) 检查，m>=3 则用 `R_m<=4`。
所以对全部 k>=2、全部 primitive a,b，有

\[
 \boxed{|K_{2^k}(a,b)|\le(k+1)2^{k/2}.}
 \tag{binary-prime-power-bound}
\]

没有丢弃小模数、额外假设 a=b，或把模2的退化当成深输入。

## 6. 一次素数模数与唯一剩余 Weil 核心

若 q=p 是素数，a,b 中恰有一个为模p零，则通过单位的乘法或
取逆置换以及 (orthogonality)，精确得到 `K_p(a,b)=-1`。
若二者都是模p零，则 `K_p(a,b)=p-1`。

p=2 的单位集合仅有1，故对所有 a,b 有 `|K_2(a,b)|=1`。
真正未由上述计算证明的情形，只剩

\[
 p\text{ odd prime},\quad p\nmid ab:
 \qquad |K_p(a,b)|\le2\sqrt p.
 \tag{remaining-prime-Weil}
\]

它是上述来源 Theorem 11.11 在素域、两个非平凡加法特征下的
特例。它不能由本节的 m>=1 驻相恒等式套 m=0 得到：那样的
分层根条件及非退化二次和并不存在。

在明确调用 (remaining-prime-Weil) 的情况下，第4--6节一起给出
每个素数 p、k>=1、primitive a,b 的实际界
`|K_(p^k)(a,b)|<=(k+1)p^(k/2)`。
唯一的深调用发生在奇 p、k=1、`p∤ab`；其余情况上面均已证明。

## 7. 公共 gcd：先精确降模，再支付平方根权重

对任意 p,k>=1，令 `d=gcd(a,b,p^k)=p^j`，其中 `0<=j<=k`。
若 j=k，则全部相位为1，有 `K_(p^k)(a,b)=phi(p^k)`，因此
其绝对值不超过 `p^k=sqrt(p^k) sqrt(d)`。

若 j<k，写 `a=d a0,b=d b0,q0=p^(k-j)`。单位约化映射
`(Z/p^k Z)^× -> (Z/q0 Z)^×` 的每个纤维恰有 d 个元素：
它们是 `r+q0 t,0<=t<d`，均保持模p非零。
逆元约化也相容；相位仅取决于模q0的单位。因此有精确等式

\[
 \boxed{K_{p^k}(a,b)=d K_{q_0}(a_0,b_0).}
 \tag{gcd-reduction}
\]

`gcd(a0,b0,p)=1`，所以已证 primitive 处理（及第6节明确的
素数深输入，在需要它时）给出

\[
 \begin{split}
 |K_{p^k}(a,b)|
 &\le p^j(k-j+1)p^{(k-j)/2}\\
 &=(k-j+1)\sqrt{p^k}\sqrt{p^j}
 \le(k+1)\sqrt{p^k}\sqrt{\gcd(a,b,p^k)}.
 \end{split}
 \tag{local-gcd-bound}
\]

此处 d 的纤维因子不能误写成 sqrt(d)，也不能在降模后再次把
原 gcd 算进 primitive 和。若降模后只剩一次奇素数，仍须第6节
的深输入；“原模数是高次幂”本身并不使这个退化情形初等化。

## 8. CRT 的两个系数扭转与最终乘积

设 r,s>=2 互素，取 `sbar*s≡1 (mod r)`、
`rbar*r≡1 (mod s)`。加法特征的分解为

\[
 e_{rs}(z)=e_r(\bar s z)e_s(\bar r z).
\]

因为整数 `s sbar+r rbar` 模rs等于1，该等式逐项成立。
CRT 将模rs单位双射到模r、模s单位对，并保持逆元的两个分量，故

\[
 \boxed{K_{rs}(a,b)=K_r(a\bar s,b\bar s)K_s(a\bar r,b\bar r).}
 \tag{CRT-exact}
\]

这里每个局部和的两个系数都要扭转。不能写成未经扭转的
`K_r(a,b)K_s(a,b)`。扭转因子在对应局部环为单位，所以不改变
`gcd(a,b,p^k)`。重复 (CRT-exact) 并用 (local-gcd-bound)，得到

\[
 \begin{split}
 |K_q(a,b)|
 &\le\prod_{p^k\Vert q}(k+1)\sqrt{p^k}\sqrt{\gcd(a,b,p^k)}\\
 &=\tau(q)\sqrt q\sqrt{\gcd(a,b,q)}.
 \end{split}
\]

最后一行来自素数分解中的除数计数和 gcd 的互素分解。
q=1 时定义给出1，右边也为1；a=0、b=0、负系数及非互素参数
都已由相同有限式覆盖。

## 9. 真实依赖收缩，不变更最终结论层级

至此，Type I 实际使用的任意模数完全和界已经有完整的
初等模数提升证明。上游的 Fourier 补全、g过滤与 Abel 求和可以
原样接用：仍然保留 `sqrt(gcd(h,l,v))`，进而用
`gcd(h,l,v)<=gcd(l,v)`，不存在新增长度损失。

新完成的无深输入内容是两条驻相恒等式、二次 Gauss 范数、
根数、2-adic例外、gcd纤维和CRT。任意模数最终界仍明确依赖
(remaining-prime-Weil)，DI84 的谱输入则完全未由这些计算替代。
本节不声称这两项深核心或整个 Conrey 原生 Lean 目标已完成。

补充诊断在 p=2,3,5,7 的若干幂上检查了3731组驻相恒等式，
用分圆多项式的整数系数约化比较，而非浮点容差；另检查3731组
gcd精确纤维等式和600组CRT相位多重集合等式。它们仅排查公式
错误，不代替对任意模数的上述证明。Lean 原生化仍待资源窗口放行。
