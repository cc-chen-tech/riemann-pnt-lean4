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

固定 \(C^1\) 函数 \(W\)，支撑于 \([1,2]\)。令
\(1\le A\le P/3\)，并定义
\[
 \mathcal P_q(\chi)=\sum_pY_p\chi(p),\qquad
 \mathcal T_A(\chi)=\sum_{t\in\mathbb Z}W(t/A)\chi(t). \tag{RV2.1}
\]
对素数 \(q\in(P,2P]\)，角色按通常方式在非单位处取零；故
RV2.1 的 \(p=q\) 项自动为零，同一个系数列可用于所有 \(q\)。

**定理 RV.** 对每个 \(\varepsilon>0\)，存在
\(C_{\rho,w,W,\varepsilon}\)，使全部充分大 \(P\) 与
\(1\le A\le P/3\) 满足
\[
 \boxed{\quad
 \sum_{\substack{P<q\le2P\\q\ {\rm prime}}}|Y_q|^2
 {1\over q-1}
 \sum_{\substack{\chi\ ({\rm mod}\ q)\\\chi\ne\chi_0}}
 |\mathcal P_q(\chi)\mathcal T_A(\chi)|^2
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

## RV5. 区间角色四阶矩与最终 Cauchy

Ayyad--Cochrane--Zheng 对任意位置、长度 \(B<q\) 的整数区间证明
\[
 {1\over q-1}\sum_{\chi\ne\chi_0}
       \left|\sum_{x=a+1}^{a+B}\chi(x)\right|^4
 \ll B^2(\log q)^2;                                     \tag{RV5.1}
\]
参见 [Journal of Number Theory 59 (1996), 398--413,
DOI 10.1006/jnth.1996.0105](https://doi.org/10.1006/jnth.1996.0105)。
对 RV2.1 作 Abel 分部求和；\(W\) 的总变差固定，且
\([A,2A]\) 长度为 \(A<q\)，所以
\[
 {1\over q-1}\sum_{\chi\ne\chi_0}
                  |\mathcal T_A(\chi)|^4
 \ll_W A^2(\log P)^2.                                  \tag{RV5.2}
\]

对每个 \(q\) 在角色平均中用 Cauchy，由 RV5.2，RV2.2 左端至多
\[
 A\log P\sum_q|Y_q|^2
 \left\{{1\over q-1}\sum_{\chi\ne\chi_0}
                     |\mathcal P_q(\chi)|^4\right\}^{1/2}. \tag{RV5.3}
\]
再以 \(|Y_q|^2\) 为测度对 \(q\) 用 Cauchy，RV5.3 至多
\[
 A\log P\,S_Y^{1/2}
 \left\{M_Y\sum_q{1\over q-1}
             \sum_{\chi\ne\chi_0}|\mathcal P_q(\chi)|^4
 \right\}^{1/2}.                                       \tag{RV5.4}
\]
代入 RV1.6 与 RV4.2 得
\[
 \text{RV5.4}\ll_{\rho,w,W}
 A(\log P)^{3/2}S_Y^2,
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

但 RV2.2 只在同一个 \(q\)-平均内控制
\(|\mathcal P_q\mathcal T_A|^2\)。完整物理输出还必须证明一个共同
有限系数映射，使两侧 shell incidence、精确等式而非仅模 \(pq\) 的
shift detector、principal/equal-prime/axis 四行、nonflat/gcd/endpoints、
AFE 与 transform tails 在使用 RV2.2 前已经位于这些相同的
\(q,\chi\) 坐标。本文没有证明这个映射，也没有处理低高度完整投影
方差。因此 RV2.2 是一个真实局部 supplier，不是 forcing lower bound、
高高度定理或 Lean 接口。
