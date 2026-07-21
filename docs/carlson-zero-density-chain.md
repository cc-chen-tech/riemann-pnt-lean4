# Carlson 零密度估计

## 从“数全部零点”到“数靠右零点”

对固定的 `sigma`，令 `N(sigma,T)` 统计满足以下条件的非平凡 zeta 零点：

```text
Re(rho) >= sigma,    0 < Im(rho) <= T,
```

并按照解析重数计数。Riemann--von Mangoldt 公式给出所有零点约有 `T log T`
个，而零密度估计研究临界带右侧区域中的零点是否显著更少。

## Lean 中的最终定理

主定理是：

```lean
PrimeNumberTheorem.CarlsonZeroDensity.carlson_zeroDensity_isBigO
```

源码位于
[CarlsonAsymptotic.lean](../PrimeNumberTheorem/CarlsonAsymptotic.lean)。它对每个固定的
`1/2 < sigma < 1` 证明：

```text
N(sigma,T) = O(T^(4*sigma*(1-sigma)) * (log T)^4).
```

形式化陈述中的计数函数 `ZeroDensity.zeroDensityCount` 定义在
[ZeroDensityCount.lean](../PrimeNumberTheorem/ZeroDensityCount.lean)。

## 证明分层

证明路线包含：

1. 定义乘重数的右半平面零点计数，并证明区域包含与单调性接口；
2. 建立有限 Dirichlet 多项式均方估计和 Mobius mollifier；
3. 构造在目标零点附近变大的 Carlson detector；
4. 用 Littlewood 矩形计数和 Jensen 型局部零点控制，把 detector 的平均增长转化为零点数上界；
5. 选择并优化多项式长度，得到指数 `4*sigma*(1-sigma)` 和四次对数因子。

相关的零点计数基础也用于
[Riemann--von Mangoldt 公式](riemann-von-mangoldt-chain.md)。完整声明索引见
[正式定理清单](formal-theorem-inventory.md)。

## 声明边界

该定理是无条件、固定 `sigma`、非数值显式常数的经典 Carlson 型估计。它：

- 不证明 RH；
- 不证明 Selberg 的临界线正比例定理；
- 不证明 Vinogradov--Korobov 零自由区域；
- 不宣称改进经典零密度指数或创造新的数值记录。
