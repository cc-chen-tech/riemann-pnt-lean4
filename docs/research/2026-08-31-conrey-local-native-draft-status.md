# Conrey 两项局部 Lean 结论与验收边界

## 2026-09-08：局部验收与集中交付

两项结论分别给出同参数半段上的实际均方转移，以及开区间内的真实有限单零点见证。
它们不提供实际长均方误差趋零，也不证明完整 Conrey 严格 `>2/5`。

首轮验收从基础 `144bfae7112aa46f2553e7f83c8a9bc1b0076b28` 加四份草稿的
准确字节状态出发，顺序重编全部 130 个本地依赖模块；130 项均真实退出 0，
全部源码前后一致，两份完整字面契约均通过。两项实际 `#print axioms` 输出各自
仅含 `propext`、`Classical.choice`、`Quot.sound`。这份首轮源码另保存于提交
`32d639f5`，不把基础提交误称为包含当时未跟踪的草稿。

首轮警告为三处冗余 tactic：半段模块一处不必要的 `<;>`、一处不可达 `ring`，
局部见证模块一处不可达 `ring`；两个契约没有警告。后续整理只清理这些冗余、
更新状态注释，并将两生产模块和两契约登记为四个默认构建目标；没有改变任何
数学命题或增加分析假设。最终源树验收以整理后同一提交对应的四目标原始日志、
两个公理报告及交接记录为准，首轮日志不能替代整理后的复验。

这是本地源树验收：外部包缓存只读，vendored Mathlib 没有独立 Git 仓库，
没有声称它等同于 CI 固定依赖版本；默认 Lake 全基线、远端 CI、合并树和
`origin/main` 的最终验收仍须分别兑现。

按用户的新发布要求，本组成果交给现有 #566 统筹，不另拆小 PR。后续顺序仍为
实际同参数均方误差趋零，再到完整计数组合；不得用新的宽泛条件接口替代实际估计。

## 2026-08-31：原始草稿准备记录（历史）

下文保留当时的准备状态与数学核对，其中“未编译”“未授权”等措辞仅描述
2026-08-31 的状态，不覆盖上方最新验收记录。

本次仅准备源码，不交付已验证证明，不新增 Ready PR，不增加通过目标。
没有运行 Lean、Lake、编辑器 LSP、依赖加载、Python 回归或基线脚本。
字面契约先于实现草稿编写，但未运行红灯或绿灯，不能称为已完成测试驱动验证。

## 隔离和授权边界

- 分支：`codex/conrey-local-native-draft-20260831`。
- worktree：`.worktrees/conrey-local-native-draft-20260831`。
- 基础提交：`144bfae7112aa46f2553e7f83c8a9bc1b0076b28`（#552）。
- 本记录对应未提交草稿；基础提交 SHA **不包含**这些新文件。
- 不修改任何冻结 PR/source，包括 #500、#508 及后继纸面 PR。
- 不改 `lakefile.lean`、默认 roots、目标清单或已有契约。
- 本次授权仅为已审查数学的源码准备，不代表集成负责人已批准纸面数学或 main 集成。
- 构建仍须专属通知；顺位保持 #490 → #504 → #496 → Conrey。

## 1. 同参数半段 V1 特化

源码：`HardyTheorem/ConreyV1HalfMeanSquare.lean`。
字面契约：`Test/ConreyV1HalfMeanSquareContract.lean`。

输入仅为 `T >= 6`、`0 < sigma <= 1/2`，保留任意原始 `Y,P`。
设置 `L=log T`、`U=T/2`、`a=1-log 2/L`、`epsilon=1/L`。
草稿拟从已有实际均方转移定理推出

\[
 \int_{T/2}^{T}|V_1B|^2
 \le (1+1/L)\int_{T/2}^{T}|VB|^2
 +(1+L)(K/L)^2\int_{T/2}^{T}|\zeta B|^2,
\]
\[
 K=\frac{51}{50}\left(10+\frac{\log2+|\log(2\pi)|}{2}\right).
\]

每项都使用同一个 T、L、sigma、Y、P；没有重设 mollifier。
`exp(aL)=T/2` 后，低积分由 `intervalIntegral.integral_same` 精确化为零，
不是用新的低高度估计压小。这里仅写出未归一化积分版本；乘以正数 `2/T`
即可得到纸面半段均方形式，但本次不另行扩展模块。

## 2. 局部有限单零点见证

源码：`HardyTheorem/ConreyLocalSimpleZeroWitness.lean`。
字面契约：`Test/ConreyLocalSimpleZeroWitnessContract.lean`。

沿用实际 `F=V1 B`、`g != 0`、`Y >= 2`、`P(1)=1`、
`0 < sigma0 < 1/2 < A`、`0 < U < T`，以及实际乘积在三条非左边上非零。
草稿保留并拟返回 `S : Finset R`，每个成员均在开区间 `(U,T)`，
满足真实 zeta 零点方程和 `analyticOrderNatAt = 1`。

令 `M` 为同一乘积在左边的实际平方积分，`B` 为完整非左边余项，
`E_eta` 为已有实际 eta 三边变幅。拟返回 `M > 0` 及

\[
 \frac{E_\eta}{\pi}
 -\frac{(T-U)\log(M/(T-U))+2B}{2\pi(1/2-\sigma_0)}-1
 \le |S|.
\]

组合保留 eta 全重数的二倍损失、完整余项的二倍系数和端点损失 1。
左边允许零点；不输入现成零点数下界、实际均方上界或最终渐近式。
三边非零仍为明确输入，本草稿没有完成端点选择或定量边界估计的组合。

## 待专属窗口确认

当前仅对照现有源码的签名、归一化和不等号方向阅读检查。
以下问题未经过 elaborator/kernel 验证：

1. `exp(aL)=T/2`、比较系数 `K/L` 的分式化简与隐式实数类型。
2. 等端点积分、`1/(1/L)`、乘法结合律及 `let` 绑定的最终化简。
3. 有限 eta 零点质量的自然数到实数转换，以及局部见证的原样保留。
4. Jensen 与 Littlewood 的 `let` 展开、正分母变换及最终线性组合。
5. 两个完整字面契约和其 `#print axioms`；命令目前仅存在于源码，未执行。

获得专属通知后，先由唯一 owner 复核资源、依赖状态和允许的验收范围。
只在本后继分支把上述四模块加入 roots，处理实际编译反馈，再锁定包含源码、
契约及 roots 的最终准确 SHA。以下为**尚未执行**的验收命令计划：

```sh
git rev-parse HEAD
git status --short
lake build HardyTheorem.ConreyV1HalfMeanSquare HardyTheorem.ConreyLocalSimpleZeroWitness Test.ConreyV1HalfMeanSquareContract Test.ConreyLocalSimpleZeroWitnessContract
bash scripts/verify-baseline.sh
```

先后执行，不并发启动另一份验证。任何源码修改后均须更新 SHA 并补齐对应验收；
失败时记录真实退出码，不沿用旧日志。完整适用契约覆盖、精确公理审计及最终集成树
验证由 owner 按届时最终树确定；以上命令列表不保证默认 roots 已覆盖所有契约。
源树验收与 main 集成验收分开，不能用前者替代后者。

两项局部草稿均不等同于原生 Conrey 严格 `>2/5`：实际长 mollifier 均方主项、
误差趋零及后续计数组合仍须各自兑现，不能用宽泛条件接口替代。

## 后续只读核对：实际均方的参数一致性

继续以基础 SHA `144bfae7112aa46f2553e7f83c8a9bc1b0076b28` 中的源码与
纸面文件为准。此节只是阅读审计记录，不是新的数学定理、独立审查批准，
更不是编译或 main 验收记录；两项 Lean 草稿的未验证状态不变。

- `conrey-gaussian-differentiation` 第3节的共同支配只用于固定 T 下的
  存在性和求导，其常数允许依赖 Y、Delta、中心区间；该节明确没有用它
  直接交换 `T -> infinity` 与积分。
- `conrey-gaussian-profile-main-term` 第1--4节使用 `H_Y=log Y`，而不是
  静默把整数 cutoff 的对数改成 `theta log T`。正负双圆盘半径均为
  `21/40`，所需 `theta(R+21/40)=39399/40000<1`；最终替换有显式误差。
- `conrey-actual-mobius-type-i` 第1节对无上界 N 单独保留
  `|d_gamma(n)| <= tau(n) n^max(Re gamma,0)`，先固定小损失 rho 再增大
  T 门槛。不能把只对 `n <= Y` 有效的移位常数界套到该无限尾。
- `conrey-dual-dyadic-contour` 第4--7节只移动有限算术块，选线集合不依赖
  复移位或四相位标签；被跨留数的 N 范围有限。无限右线尾有自己的绝对
  收敛依据，不因有限块可积就自动得到渐近消去。
- `conrey-actual-di-remainder` 的实际余项预算使用 `epsilon < eta` 支付
  N 的几何尾；`conrey-end-to-end-paper-proof` 第3节固定全部小参数后，
  才用半径 `1/2` 的 Cauchy 圆将一致误差传到混合微分。
- `conrey-local-v1-mean` 第2节保留原 T、L、Y、Delta 和射线角，仅将中心
  w 的范围改为 `[T/2,T]`。这正是当前半段草稿可使用的参数匹配，不能换成
  在高度 T/2 重新定义的 mollifier。

上述针对参数与换序的核对未发现需修改当前两份草稿的问题，但没有重新逐项
认证所有 Weil、谱完备性、测试核反演或 DI 深输入，不能据此升级整条纸面链
的审查状态。部分谱依赖的阅读也不构成整份谱证明的批准。

机器端的确切未闭合处仍是 `HardyTheorem/ConreyTwoFifthsBridge.lean` 中
`conreyTwoFifthsSimpleZerosTarget_of_explicit_analytic_lower_bound` 的参数
`h : conreyExplicitAnalyticLowerBound`。该 Prop 要求对每个严格小于真实
积分比例的 c，最终都有 `c * riemannZeroCount T <= positiveCriticalLineSimpleZeroCount T`。
本轮没有构造这个 h，也没有发现可以绕过真实均方证明的现成 Conrey Gaussian
原生模块。下一步仍按获准范围先验收两项局部草稿；不得把它们或本节审计替代 h。
