# Riemann--von Mangoldt 零点计数公式

## 这一定理在说什么

令 `N(T)` 表示虚部位于 `0` 到 `T` 之间的 Riemann zeta 非平凡零点总数，
每个零点按照解析重数计算。Riemann--von Mangoldt 公式说明：

```text
N(T) = T/(2*pi) * log(T/(2*pi)) - T/(2*pi) + O(log T).
```

因此高度不超过 `T` 的零点总数主要按照 `T log T` 增长。这里的公式统计所有
非平凡零点，而不是只统计临界线 `Re(s) = 1/2` 上的零点，所以它本身不蕴含
Riemann 假设。

## Lean 中的最终定理

主定理是：

```lean
PrimeNumberTheorem.RiemannVonMangoldt.exists_abs_riemannZeroCount_sub_mainTerm_le_log
```

源码位于
[AllHeightAsymptotic.lean](../PrimeNumberTheorem/RiemannVonMangoldt/AllHeightAsymptotic.lean)。
它证明存在 `C >= 0`，使所有 `T >= 8` 满足：

```lean
|(riemannZeroCount T : ℝ) - riemannVonMangoldtMainTerm T| ≤
  C * (1 + Real.log (T + 6)).
```

其中：

- `riemannZeroCount` 在
  [ZeroCount.lean](../PrimeNumberTheorem/RiemannVonMangoldt/ZeroCount.lean)
  中定义；
- `riemannVonMangoldtMainTerm` 在
  [GammaMainTerm.lean](../PrimeNumberTheorem/RiemannVonMangoldt/GammaMainTerm.lean)
  中定义。

## 证明分层

形式化证明分成四层：

1. 构造适合辩值原理的 completed-zeta 轮廓，并用零点解析重数解释轮廓计数；
2. 从 Gamma 因子的辩角变化提取 `T log T` 主项；
3. 在与零点纵坐标定量分离的 good heights 上控制 zeta 边界项；
4. 使用零点计数单调性和单位区间内的 good-height 选择，将结论推广到所有充分大实数高度。

更细的模块索引见
[正式定理清单](formal-theorem-inventory.md)和
[数学贡献说明](mathematical-contributions.md)。

## 声明边界

该定理：

- 是全高度、乘重数的零点计数渐近公式；
- 不假设也不证明 RH；
- 不说明这些零点中有多少位于临界线上；
- 最终常数以存在量词给出，不是数值显式的零点计数界。
