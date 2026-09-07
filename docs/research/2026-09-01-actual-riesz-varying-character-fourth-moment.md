# 实际 Riesz 素数权的变模角色四阶矩

## 结论边界

本文证明一个无条件的局部解析估计。固定 ζ 零点候选
\(\rho=\beta+i\gamma\)、\(1/2<\beta<1\)，先构造实际 Riesz 素数权
\(Y_p\)，再令 \(P\to\infty\)。对 \(q\asymp P\) 的素数模数作带
\(|Y_q|^2\) 的平均时，prime polynomial 与长度
\(A=P^{11/12}\) 的平滑区间 polynomial 的乘积二阶矩只有
\(A(\sum|Y_p|^2)^2P^\varepsilon\) 大小。相对于逐模数
Pólya--Parseval 费用，这准确节省 \(A/P=P^{-1/12}\)。

这不是完整 QCT/MWKF 上界。本文没有把 opposite quotient、
zero-alias selector、两侧 valuation-one shell、projection correction、
principal/axis/endpoints 或其余 boxes 迁入同一个角色矩；也不证明
高高度 \(14/17\) 零点区域。

## RV1. 实际素数权及其平坦性

固定非负 \(C^1\) 函数 \(w\)，支撑于 \([1,2]\)，并假设它在一个
非退化子区间上为正。所有下列素数均在 \((P,2P]\)。定义
\[
 a_p={w(p/P)\over p-1},\qquad v_p=p^{1-\rho},qquad
 D=\sum_pa_p,\qquad E=\sum_pa_pv_p,
\]
\[
 Y_p=a_p\{D\overline {v_p}-\overline E\},qquad
 S_Y=\sum_p|Y_p|^2,qquad M_Y=\max_p|Y_p|^2.            \tag{RV1.1}
\]
若 \(w(p/P)=0\)，相应 \(Y_p=0\)。

置
\[
 d=\int_1^2{w(u)\over u}\,du,qquad
 e_\rho=\int_1^2w(u)u^{-\rho}\,du,
\]
\[
 y_\rho(u)={w(u)\over u}
       \{d u^{1-\overline\rho}-\overline {e_\rho}\}.    \tag{RV1.2}
\]
普通素数定理经分部求和，在固定 \(C^1\) 权上一致给
\[
 D={d+o(1)\over\log P},\qquad
 E={P^{1-\rho}\over\log P}\{e_\rho+o(1)\}.             \tag{RV1.3}
\]
又因 \((p-1)^{-1}=P^{-1}(p/P)^{-1}\{1+O(P^{-1})\}\)，
RV1.1--RV1.3 逐素数一致给
\[
 Y_p={P^{-\overline\rho}\over\log P}
          \{y_\rho(p/P)+o(1)\}.                         \tag{RV1.4}
\]
函数 \(y_\rho\) 不恒为零：在 \(w>0\) 的区间上，若它恒为零，则
\(u^{1-\overline\rho}\) 为常数，与 \(\Re(1-\overline\rho)>0\)
矛盾。因此再用一次带权 PNT，
\[
 S_Y={P^{1-2\beta}\over(\log P)^3}
       \left\{\int_1^2|y_\rho(u)|^2du+o(1)\right\}.    \tag{RV1.5}
\]
RV1.4 的一致上界与 RV1.5 的正主项证明：存在只依赖固定
\(\rho,w\) 的 \(C,P_0\)，使 \(P\ge P_0\) 时
\[
             \boxed{\quad
             0<M_Y\le C{\log P\over P}S_Y .\quad}       \tag{RV1.6}
\]
这里固定 \(\rho\) 后才取 \(P_0\)；没有声称对全部零点统一。

## RV2. 定理

固定 \(C^\infty\) 函数 \(W\)，支撑于 \([1,2]\)，并写
\(e(x)=e^{2\pi ix}\)。令
\(1\le A\le P/3\)、整数 \(1\le a\le A\)、\(0\le\alpha\le1\)，并定义
\[
 \mathcal P_q(\chi)=\sum_pY_p\chi(p),\qquad
 \mathcal T_{A,a,\alpha,q}(\chi)
 =\sum_{t\in\mathbb Z}W(t/A)\chi(t)e(\alpha at/q).      \tag{RV2.1}
\]
对素数 \(q\in(P,2P]\)，角色按通常方式在非单位处取零；故
RV2.1 的 \(p=q\) 项自动为零，同一个系数列可用于所有 \(q\)。

**定理 RV.** 对每个 \(\varepsilon>0\)，存在
\(C_{\rho,w,W,\varepsilon}\)，使全部充分大 \(P\) 与
\(1\le A\le P/3\)、整数 \(1\le a\le A\)、\(0\le\alpha\le1\) 满足
\[
 \boxed{\quad
 \sum_{\substack{P<q\le2P\\q\ {\rm prime}}}|Y_q|^2
 {1\over q-1}
 \sum_{\substack{\chi\ ({\rm mod}\ q)\\\chi\ne\chi_0}}
 |\mathcal P_q(\chi)\mathcal T_{A,a,\alpha,q}(\chi)|^2
 \ll_{\rho,w,W,\varepsilon} A P^\varepsilon S_Y^2.
 \quad}                                                  \tag{RV2.2}
\]

## RV3. 素数乘积列的精确能量

令
\[
                 c_n=\sum_{p_1p_2=n}Y_{p_1}Y_{p_2}.     \tag{RV3.1}
\]
有序对定义使 \(c_{p^2}=Y_p^2\)，而不同素数时
\(c_{p_1p_2}=2Y_{p_1}Y_{p_2}\)。素数唯一分解遂给精确式
\[
 \sum_n|c_n|^2
 =\sum_p|Y_p|^4+4\sum_{p_1<p_2}|Y_{p_1}Y_{p_2}|^2
 =2S_Y^2-\sum_p|Y_p|^4\le2S_Y^2.                       \tag{RV3.2}
\]
而且
\[
                   \mathcal P_q(\chi)^2
                        =\sum_nc_n\chi(n).              \tag{RV3.3}
\]
这些是有限恒等式，不含素数分布估计。

## RV4. 在模数平均上使用一次乘法大筛

采用 primitive Dirichlet 大筛的标准精确范围：对支撑在长度
\(N\) 区间内的任意有限列 \(z_n\)，
\[
 \sum_{r\le Q}{r\over\varphi(r)}
   \sum_{\chi\ ({\rm mod}\ r)}^{*}
      \left|\sum_nz_n\chi(n)\right|^2
 \le (Q^2+N-1)\sum_n|z_n|^2.                            \tag{RV4.1}
\]
对 RV3.1 有 \(n\in(P^2,4P^2]\)，故可取 \(Q=2P\)、
\(N\le3P^2+1\)。素数模数的非主角色全为 primitive，且
\[
 {1\over q-1}={1\over q}{q\over\varphi(q)}\le
 {1\over P}{q\over\varphi(q)}.
\]
由 RV3.2--RV4.1，
\[
 \sum_{P<q\le2P}{1\over q-1}
  \sum_{\chi\ne\chi_0}|\mathcal P_q(\chi)|^4
 \ll P S_Y^2.                                           \tag{RV4.2}
\]
注意 \(P\) 来自 \((Q^2+N)/P\)，没有另乘素数模数的个数。

## RV5. Gauss--Poisson 后的短对偶角色四阶矩

Cochrane--Shi 的一般模数定理明确对任意整数起点 \(c\) 与正整数长度
\(B\) 给出；在素数模数 \(q\) 上，它化为
\[
 {1\over q-1}\sum_{\chi\ne\chi_0}
       \left|\sum_{x=c+1}^{c+B}\chi(x)\right|^4
 \ll B^2(\log q)^3\{\log\log(3q)\}^7.                  \tag{RV5.1}
\]
参见 [Cochrane--Shi, Journal of Number Theory 130 (2010), Theorem 1,
767--785](https://www.math.ksu.edu/~cochrane/research/xyequvmodm.pdf)。
该定理原常数中的 \(8^{\nu(q)}\tau(q)\) 在素数 \(q\) 上为绝对常数。

这里不能直接对 RV2.1 作 Abel 分部求和：相位的总变差可达
\(aA/q\asymp A^2/P=P^{5/6}\)。正确做法是先完成。取 Fourier
约定
\[
                   \widehat W(\xi)=\int_{\mathbb R}W(x)e(-x\xi)\,dx.
\]
对每个非主角色 \(\chi\pmod q\)，它是 primitive，Poisson 求和与
Gauss 恒等式逐项给
\[
 \mathcal T_{A,a,\alpha,q}(\chi)
 ={A\tau(\chi)\over q}
  \sum_{h\in\mathbb Z}\overline{\chi(h)}
       \widehat W\!\left({A(h-a\alpha)\over q}\right),   \tag{RV5.2}
\]
其中 \(|\tau(\chi)|=\sqrt q\)。没有把 \(a\alpha\) 取整；它只是
对偶区间的实中心。

置 \(H=q/A\)，并取整数 \(B=\lfloor H/2\rfloor\)。由
\(A\le P/3<q/3\) 得 \(H>3\)，所以
\[
                         1\le B<q.                       \tag{RV5.3}
\]
置 \(m_0=\lfloor a\alpha\rfloor\)，并令
\(I_k=[m_0+kB,m_0+(k+1)B)\cap\mathbb Z\)。这些长度为 \(B\) 的
连续整数块分割整个 \(h\)-轴。Schwartz 衰减逐块给：
对每个固定 \(J>2\)，
\[
 \sup_{h\in I_k}|\widehat W((h-a\alpha)/H)|
 +\operatorname {Var}_{I_k}\{\widehat W((h-a\alpha)/H)\}
 \ll_{J,W}(1+|k|)^{-J}.                                 \tag{RV5.4}
\]
这里的变差可取分段线性插值的总变差；常数对实中心 \(a\alpha\)
一致。对每块作 Abel 分部求和，并在 Abel 积分内对角色 \(L^4\)
使用 Minkowski。块内每个前缀都是长度至多 \(B<q\) 的任意位置区间；
由角色的 \(q\)-周期性，跨越一个剩余系边界时把它拆成至多两个这种
区间。因此 RV5.1 与 RV5.4 给
\[
 \left\{{1\over q-1}\sum_{\chi\ne\chi_0}
  \left|\sum_{h\in I_k}\overline{\chi(h)}
       \widehat W((h-a\alpha)/H)\right|^4\right\}^{1/4}
 \ll_W(1+|k|)^{-J}H^{1/2}(\log P)^3.
\]
最后在 \(k\in\mathbb Z\) 上再用一次 Minkowski；因
\(\sum_k(1+|k|)^{-J}<\infty\)，整个对偶和满足
\[
 \left\{{1\over q-1}\sum_{\chi\ne\chi_0}
  \left|\sum_{h\in\mathbb Z}\overline{\chi(h)}
       \widehat W((h-a\alpha)/H)\right|^4\right\}^{1/4}
 \ll_W H^{1/2}(\log P)^3.                              \tag{RV5.5}
\]
因此 RV5.2 与 RV5.5 一致于全部 \(a,\alpha,q\) 给
\[
 {1\over q-1}\sum_{\chi\ne\chi_0}
        |\mathcal T_{A,a,\alpha,q}(\chi)|^4
 \ll_W {A^4\over q^2}H^2(\log P)^{12}
 =A^2(\log P)^{12}.                                    \tag{RV5.6}
\]

对每个 \(q\) 在角色平均中用 Cauchy，由 RV5.6，RV2.2 左端至多
\[
 A(\log P)^6\sum_q|Y_q|^2
 \left\{{1\over q-1}\sum_{\chi\ne\chi_0}
                     |\mathcal P_q(\chi)|^4\right\}^{1/2}. \tag{RV5.7}
\]
再以 \(|Y_q|^2\) 为测度对 \(q\) 用 Cauchy，RV5.7 至多
\[
 A(\log P)^6S_Y^{1/2}
 \left\{M_Y\sum_q{1\over q-1}
             \sum_{\chi\ne\chi_0}|\mathcal P_q(\chi)|^4
 \right\}^{1/2}.                                       \tag{RV5.8}
\]
代入 RV1.6 与 RV4.2 得
\[
 \text{RV5.8}\ll_{\rho,w,W}
 A(\log P)^{13/2}S_Y^2,
\]
把固定对数幂吸收到 \(P^\varepsilon\) 即证 RV2.2。

## RV6. 对 (14/17) 路线的准确作用

取 \(A=P^{11/12}\) 时，充分大 \(P\) 自动满足 \(A\le P/3\)。
RV2.2 把旧 prime--interval Pólya 容量中的 \(P\) 换成 \(A\)，故
相对节省恰为
\[
                         {A\over P}=P^{-1/12}.            \tag{RV6.1}
\]
这正是 balanced squarefree scalar row 的剩余指数。

RV5 的完成还表明该估计对 CF11 的共享相位
\(e(\alpha at/q)\) 一致；固定一个 divisor/shell 输出 \(a\) 不产生
\(P^{5/6}\) 的相位变差损失。

但 RV2.2 只在同一个 \(q\)-平均内控制
\(|\mathcal P_q\mathcal T_{A,a,\alpha,q}|^2\)。完整物理输出还必须证明一个共同
有限系数映射，使两侧 shell incidence、精确等式而非仅模 \(pq\) 的
shift detector、principal/equal-prime/axis 四行、nonflat/gcd/endpoints、
AFE 与 transform tails 在使用 RV2.2 前已经位于这些相同的
\(q,\chi\) 坐标。本文没有证明这个映射，也没有处理低高度完整投影
方差。因此 RV2.2 是一个真实局部 supplier，不是 forcing lower bound、
高高度定理或 Lean 接口。
