# Carlson 联合检查点：密度无条件，零点排除仍依赖实际种子 forcing

本检查点冻结 `delta=1/400, B=6`。成果是实际 ζ 零点的无条件零密度定理，
不是 `Re rho<=14/17`、`Re rho<=2/3` 或 RH 的证明。没有继续优化指数，
没有以 Ingham 的零密度定理替换 Carlson 证明。

## 可以直接复用的结论

令 `N_ge(sigma,T)` 统计 `0<Im rho<=T, sigma<=Re rho` 的实际非平凡 ζ 零点，
按 `analyticOrderNatAt riemannZeta rho` 计重数。则

\[
N_{\ge}(2/3,T)\ll T^{8/9-1/400}(\log T)^6\quad(T\to\infty).
\]

旧计数 `N_>(sigma,T)` 使用严格的 `sigma<Re rho`。由 `N_> <= N_ge` 得到
同样的上界，但不能把闭阈值的**下界**用这个包含关系转换成严格阈值的下界。

| 环节 | 公开入口（前缀 `PrimeNumberTheorem.`） | 证明边界 |
| --- | --- | --- |
| 闭阈值计数 | `ZeroDensity.zeroDensityClosedCount` | 实际 ζ 重数，不是模型计数 |
| 不交增量 | `ZeroDensity.zeroDensityClosedCount_step_eq` | 增量为 `(U,T]`，避免壳端点重计 |
| 壳递推 | `ZeroDensity.exists_eventually_closedCount_twoThirds_step_le` | 无解析前提，比例 `9/8` |
| 几何求和 | `exists_eventually_powerLog_bound_of_geometric_step` | 通用初等引理；正指数、单调性及递推由此路线实际提供 |
| 闭阈值全局密度 | `carlson_halfRange_closed_zeroDensity_isBigO` | 无前提 |
| 严格阈值全局密度 | `carlson_halfRange_zeroDensity_isBigO` | 无前提 |
| 旧接口证书 | `exists_carlson_halfRange_densityCertificate` | 无前提地构造证书，不是假设证书存在 |

最小 Lean 用法：

```lean
import PrimeNumberTheorem.CarlsonHalfRangeDensity

open Filter Asymptotics PrimeNumberTheorem

example : (fun T => (ZeroDensity.zeroDensityClosedCount (2 / 3) T : ℝ)) =O[atTop]
    (fun T => T ^ (8 / 9 - 1 / 400 : ℝ) * (Real.log T) ^ 6) :=
  carlson_halfRange_closed_zeroDensity_isBigO
```

这段类型在 `Test/CarlsonHalfRangeDensityContract.lean` 中实际编译。
完整分析路线、两个原始端点的 minimax 障碍及候选路线账本见
[当前结果说明](2026-08-30-carlson-half-range-density-result.md)。

## 真正仍缺失的输入：从实际种子零点推出计数下界

对每个实际非平凡零点 `rho`，令 `beta=Re rho`。需要从 `rho` 的存在证明：

\[
\exists c>0\;\exists k\ge0\;\exists X_0\;\forall X\ge X_0,\qquad
cX^{2(\beta-2/3)-(1-\beta)8/9}(\log X)^{-k}
\le N_>(2/3,X^{1-\beta}).
\]

`c,k,X0` 可以依赖种子 `rho`，但不能随 `X` 改变；`X0` 可增大到大于 1。
只需 `lambda=1`，不要求对所有尺度同时给出一个统一供应者。
种子本身不另加虚部正性或高度门槛；若某条分析路线只覆盖部分种子，必须先补足
对应归约，不能直接代入此全称接口。这里的下界使用严格阈值的实际计数 `N_>`。

具体保留两种条件结论，均从
`PrimeNumberTheorem.SingleLayerForcingHalfRangeDensity` 导入：

- `no_nontrivial_zero_re_gt_14_over_17_of_forcing_halfRange`：
  只对 `14/17 < Re rho` 的实际种子要求上述下界；结论为所有非平凡零点
  `Re rho <= 14/17`。这次有意修改旧接口，删除无种子依赖的 `∀ beta lambda` 前提。
- `no_nontrivial_zero_re_ge_14_over_17_of_seed_forcing_halfRange`：
  对 `14/17 <= Re rho` 的实际种子要求同一下界；结论为所有非平凡零点
  `Re rho < 14/17`，包括排除等号。

二者都只有一个 `hforcing` 输入，没有密度证书或额外解析门。
**本检查点没有构造 `hforcing`。** 原先那个对任意实数 `beta` 提供下界的接口
甚至不需要存在零点就能产生矛盾，不能把它称为实际种子的 forcing 定理。
历史 `SingleLayerForcingBeta14Over17`/DI 模块的旧接口未全局重构；对外使用上述
两条 half-range 入口，而不要把旧接口自动视为种子供应者。

在 `beta=14/17`，令 `T=X^(3/17)`，所需下界为
`N_>(2/3,T) >> T^(8/9)/(log T)^k`，与密度上界的 `X` 幂次差为 `3/6800`。
若 forcing 内部损失增至 `8/9+eta`，一般尺度的差为
`3lambda(1/400-eta)/17`；仅当 `eta<1/400` 才保留正余量。
这个预算不能修复 MWKF/QCT 的共同权、带符号抵消或全分块重组缺口。

## 可重复验证与范围

在本分支仓库根目录运行：

```bash
python3 scripts/check_carlson_checkpoint.py
uv run --no-project --with pytest --with numpy --with python-flint --with mpmath --with scipy python -m pytest -q -rs
python3 scripts/check-targets-consistent.py
python3 scripts/check-chain-gaps.py
git diff --check
```

第一条先联合构建冻结清单中的全部 152 个 Test 模块及依赖，再逐一检查真实
`.trace` 输出与源码的 `#print axioms` 请求。它拒绝缺失报告、任何未允许公理，
清单的删项/重复/替换，以及验证期间源码或清单变动；保存完整构建日志、源码指纹、
HEAD、冻结目标摘要和 JSON 验收记录到
新建临时目录。固定清单来自原成果的 verification JSON；其中旧测试结果是历史记录，
不是本次命令的成功依据。精确无前提类型和两个实际种子接口由 Lean 契约检查。

允许的基础公理仅 `propext`、`Classical.choice`、`Quot.sound`。联合构建不等于
整仓默认 `lake build`、与最新 main 合并后的回归或远程 CI 通过；这些必须分别报告。
独立只读审查覆盖本次四个最终模块、四个契约和必要计数/壳定义，不宣称重审了
整个解析依赖链。没有新增数学公理，也没有证明最佳零密度指数或历史首创性。

### 本次验收与发布状态

实际种子接口及验证器的已验证源码提交为
`1f3003001c55c057d04e2e5363998e3179fa3c67`。
该提交后仅补充文档和验收 JSON，不改变上述源码指纹。
[本次机器可读验收记录](2026-08-30-carlson-checkpoint-validation.json) 包含：

- 联合 Lean 构建：152 个 Test 模块及依赖，9055 jobs，退出码 `0`。
- 公理审计：465 条报告、447 个不同声明，仅允许的三项基础公理，退出码 `0`。
- 完整 Python：558 项通过，无失败或跳过，退出码 `0`。
- 数学命题清单、chain-gap、项目占位符扫描和 `git diff --check`：均退出 `0`。
- 实际种子契约先在旧接口失败（退出码 `1`），修正后通过；清单删改的四项负例
  先失败，再随验证器修正通过。独立限定范围复审没有剩余 Critical/Important/Minor。

**本次发布为草稿检查点 PR，不是 main 集成或全仓发布验收。** 原成果上的
`scripts/verify-baseline.sh` 运行在改接口前被主动中断，退出码 `130`；
它没有通过，也没有被分支范围的检查替代。合并前仍需完成最终树上的全仓门禁，
并单独核对远程 CI。未合并、未证明实际 forcing 供应者。

原成果记录保留在[历史验收 JSON](2026-08-30-carlson-half-range-verification.json)，
对应提交 `64417646`。复用时必须同时引用本检查点的源码版本与证明边界，
不要仅凭旧验收条目、证书类型或公理列表宣称零点排除已完成。
