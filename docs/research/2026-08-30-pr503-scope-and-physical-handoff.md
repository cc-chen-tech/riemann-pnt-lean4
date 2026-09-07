# PR503 交付范围与物理原子交接

白话结论：本 PR 交付有限恒等式、带明确前提的局部解析估计和
归一化纠错，不交付完整长 mollifier 渐近式，也没有证明
eventual/global \(14/17\)、\(2/3\) 或 RH。共同频率与 gcd 的新估计
可以保留，但必须逐个核对原式的系数和外权后才能用于物理总和。
模型中的上界账本超过目标，仅说明该估计尚不足够；不是原式的下界。

本清单是 `d6bd004d9ccc4c34ca04c3760ec36491ea8cfa25` 已有成果的
范围修订，不增加解析定理，不将尚未完成物理适配的平方自由
交叠变量 e 平均加入此次交付。以下范围说明优先于概述中可能
将“真实共同频率结构”误读为“全部物理权均已适配”的说法。

## 1. 本次可独立交付什么

各行的完整量词、常数依赖与支撑以链接的命题为准，不能跨行
拼成一个未声明的无条件结论。Python 有限检查辅助核算，不替代
无限和、余项或一致常数的解析证明。

| 成果及入口 | 已有输出及必要前提 | 不包含的结论 |
| --- | --- | --- |
| [归一化与完整模式](2026-08-30-coprime-comb-physical-normalization.md)、[平方自由完成](2026-08-30-joint-mode-squarefree-completion.md) | 对写明的有限核、单位掩码与平方自由完成保留完整零模式、尾项以及 HL 因子；不得改写为 HL/S | 不提供物理核额外 S 的逆因子，也不是实际和达到某下界的反例 |
| [有理邻域](2026-08-30-joint-kernel-rational-flatness.md)、[实际 quotient 过渡](2026-08-30-physical-quotient-support-transition.md) | 指定统一光滑核下的有理邻域界；quotient 支撑与过渡 profile 的精确恢复 | 自然过渡尺度上的有符号算术抵消、所有外层权聚合 |
| [互素 Euler 响应](2026-08-30-primitive-euler-zero-response.md)、[同零点局部隔离](2026-08-30-same-zero-radial-isolation.md) | 保留互素、奇偶及核条件的局部 Mellin/Laurent 响应；固定零点避让轮廓上的有限隔离 | 无限算术积分的全局下界、其余零点与轮廓尾的一致控制 |
| [差频与有限高度](2026-08-30-difference-frequency-primitive-threshold.md)、[Gaussian–Cauchy](2026-08-30-gaussian-cauchy-finite-height-ledger.md) | 指定谱系数的 B² 原函数阈值；有限 mollifier 的条件性检测不等式及核范数 | 实际所需算术上界、全高度桥；单个高度的示意数值比较不是零点排除 |
| [pre-Cauchy 行列式](2026-08-30-pre-cauchy-common-determinant-residual.md)、[共同相位](2026-08-30-common-phase-prime-average-large-sieve.md) | 保留共同相位、CRT、密度扣除的有限恒等式；在实际支撑满足明确不等式时排除指定整数零层 | 不能把整数行列式零层与共同 Fourier 零频混同；不证明长素数有符号色散 |
| [完整共同频率](2026-08-30-all-common-frequencies-prime-average.md)、[Parseval C1–C2](2026-08-30-common-frequency-parseval-conductor-average.md)、[全 g 大筛 G1–G2](2026-08-30-global-common-modulus-conductor-average.md) | 声明的共同内部系数、统一实光滑权、固定相位函数下的行能量上界；G2 还要求跨 g 共同系数 | 任意依赖 g、c、ν 的算术系数；主角色；完整反射及外权；不能重复相乘各轮 saving |
| [gcd 交叠 O1–O13](2026-08-30-genuine-gcd-overlap-smooth-mode-removal.md) | 精确 signed overlap 容斥；C1 模型下的两方向平滑衰减及剩余参数域 | 交叠项不是已求值的 residual main term；模型删区不等于物理包对应项已经删除 |

[原始 cubic 模式审计](2026-08-30-cubic-comb-mode-density-audit.md)
和[共同零频 Poisson 估计](2026-08-30-common-zero-product-poisson-mobius-bound.md)
仍按各自声明的核、共同系数、尾项和归一化使用；后续修订不能
追溯性地取消它们明确保留的未证物理输入。

## 2. 唯一上游与本任务的责任

“完成 LCM 主项求值”负责原始表达式、canonical principal/reflection
分账、真实参数域、权重半范数和完整外归一化。本任务负责其中
**已逐项映射的共同频率 gcd 交叠子区**的算术上界，不再独立
重推另一套完整 master。双方交接须引用同一 source commit、公式
编号和参数表；另一工作树的最新提交不会自动更新这份证书。

本次只读对照的来源是 `docs-mobius-weighted-offdiagonal-20260824`
的 `49cfacd70c60372757280177c7b63fd4f7760817`：

- `docs/research/2026-08-24-mobius-weighted-off-diagonal.md`：
  (9.908)–(9.916) 真正 gcd，(9.955)–(9.958) 共同系数与原子成本，
  (9.1013)–(9.1014) 全部 Type 周期相位，(9.1114)–(9.1115) 全共频 master；
- `docs/research/2026-08-30-mwkf-common-phase-adapter.md`：
  CG1–CG4 的相位恢复，以及 CG11–CG14 的实际字符导子与完整 Type 系数。

这两个文件由上游维护；本 PR 不改它们。上游若再次修正物理识别，
本任务必须重新核查适配，不能以本地有限测试通过替代。

## 3. 已核实的窄连接：ratio 相位，而非整个物理包

来源 CG3 在 \(m=h\delta\)、\((mn,gp)=1\) 时准确为
\[
 V_p^{(\nu)}(x)=\sum_{h,\delta,n}f(h)\ell(\delta)b(n)
 e_g(-C\bar p\,n\bar m+\nu\bar p\,m\bar n)
 {\bf1}_{m+xn\equiv0\ (p)}.
\]
固定该原子并令 \(t=m\bar n\)、\(x'=-x\)，则其相位和 incidence
分别等于
\[
 f_{g,p}(t)e_g(\nu u_{g,p}t),\qquad
 f_{g,p}(t)=e_g(-C\bar p\,t^{-1}),\quad u_{g,p}=\bar p,
 \qquad m\equiv x'n\pmod p.
\]
因此 **该 ratio 相位及符号重标记**确实属于 C1 的形式，未把
共同零频的非平凡相位删除。字符投影也须按 \(x'=-x\) 一致转换。
此恒等式本身不证明以下任何一项：跨 g 的内部系数共同性、全部
物理权的统一分离成本、真正 gcd 的跨层聚合、主角色或完整外权。

尤其，Type 下降中
\(C_1=-K_1\overline{d^{\rm tf}_1}_{Q_1}\)、
\(C_2=K_2\overline{d^{\rm tf}_2}_{Q_2}\) 虽没有显式写 genuine gcd，
还不能据此断言跨交叠 e 的全部相位与系数独立于 e。
必须同时固定其标签、原支持与两项 inactive Type 相位。
\(d^{\rm tf}=1\) 只删除相应 inactive trace，不证明其余适配。
genuine d 改变时约化 Q、共同 g、cofactor 也可能改变；
不能把固定它们时的代数观察当作跨 e 求和的共同性证书。

## 4. 下一次物理交接的验收表

在下列项目全部对同一个原子核实前，不公布“原问题净节省”：

1. 明确原式到该原子的有限恒等式，保留原始 Möbius 系数及有符号反射；
2. 明确 \(d=a_0b_0e\)、Type gcd、共同 g、active c、inactive k 的不同角色，
   保留 \((e,n)=1\)、\((n,a_0b_0k)=1\) 和所有原单位掩码；
3. 明确允许变化的标签；只有被证明共同的内部系数才进入同一次大筛；
4. 对 e、u、v、n 的统一光滑分离给真实半范数预算；周期算术依赖不算实光滑；
5. 给出真实非空参数域、物理目标范数、完整外权与剩余标签计数；
6. 主角色、canonical zero/reflection、其余共频及交叉项保留在明确补集中；
7. 报告该区域实际受控的总成本，只使用一次抵消，不以模型上界失败推出原式反例。

现有 G15–G16 中 \(12.9\to12.4\) 是指定模型的**上界账本改进**。
当前尚未提供包含上述全部项目的物理交叠子区证书，故不能说该模型
见证就是原式的真实剩余障碍，也不能说原式某区域已经按此净节省。

## 5. PR 验证与合并的边界

本次源分支只修订范围，不加入新的 e 平均定理或 Lean 外壳。
源分支负责冻结 SHA 上的 15 个现有检查脚本及 10 项既有 coverage
检查、文档链接与 diff 检查；这些有限测试不认证整条数学证明。
“合并PR”负责冻结版本与最新 main 的集成验证，并核对适用的仓库
基线和 CI。不重复启动对方的重型构建，也不竞态修改或合并。

交付完成须有当前 SHA 的必要 review、适用验证、准确 merge commit
进入 `origin/main` 的证据。缺少 CI 记录不是通过；PR Ready 或
无冲突也不是最终验收。合并这个研究检查点不等于解决仍开放的
全局算术上界或零点问题。普通 review 修复推送同一 PR。

## English scope

This checkpoint delivers exact finite identities, normalization corrections,
and local estimates under their stated hypotheses. The common ratio phase
has an exact adapter; the full physical gcd-overlap packet does not yet have
a certified adapter including all coefficients, periodic factors, outer
weights and complementary sectors. Model exponent budgets are upper-bound
diagnostics, not counterexamples to the original arithmetic sum. The new
squarefree-overlap average is excluded from this delivery. No zero-free
half-plane or long-mollifier asymptotic is claimed.
