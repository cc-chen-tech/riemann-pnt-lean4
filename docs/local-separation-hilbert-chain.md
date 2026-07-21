# 局部分离 Hilbert 不等式与指数和均方估计

## 为什么需要“局部分离”

有限指数和把许多不同频率的振荡叠加在一起。估计它的均方时，对角项容易处理，
难点是不同频率之间的交叉项。传统全局间隔估计只使用所有频率之间最小的一个间距；
局部分离估计则让每个频率使用自己的最近邻间距，因此在频率分布不均匀时更精细。

## Lean 中的最终定理

源码位于
[CarneiroLittmannProfile.lean](../PrimeNumberTheorem/CarneiroLittmannProfile.lean)。
两个主要无条件结论是：

```lean
PrimeNumberTheorem.DirichletPolynomial.hilbertForm_norm_le_two_pi_localSeparation_carneiroLittmann

PrimeNumberTheorem.DirichletPolynomial.finiteExponentialSum_meanSquare_le_localSeparation
```

第一条给出加权 Hilbert--Montgomery--Vaughan 型界：

```text
||Hilbert form|| <= 2*pi * sum_n |c_n|^2 / delta_n,
```

其中 `delta_n` 是第 `n` 个频率的局部间距。第二条把它转化为区间上的指数和均方估计：

```text
integral |sum_n c_n exp(i*omega_n*t)|^2 dt
  <= interval_length * sum_n |c_n|^2
     + 4*pi * sum_n |c_n|^2 / delta_n.
```

局部间距和抽象核接口定义在
[LocalSeparationKernel.lean](../PrimeNumberTheorem/LocalSeparationKernel.lean)。

## 证明分层

形式化路线来自 Carneiro--Littmann 的单调极值函数方法：

1. 构造具体的密度和 signed radial tail profile；
2. 证明可积性、非负性、精确总质量和缩放单调性；
3. 计算 sinc-square 及平移版本的 Fourier 变换；
4. 证明 Fourier 变换在尾部等于所需的 reciprocal kernel；
5. 将具体 certificate 代入抽象局部分离 Hilbert 界，再推出指数和均方估计。

原始数学背景见 Carneiro--Littmann，
[Monotone extremal functions and the weighted Hilbert's inequality](https://doi.org/10.4171/PM/2109)。

## 声明边界

这是可复用的无条件解析工具层。它比仓库中 Carlson 证明所需的全局分离 API 更一般，
但 Carlson 定理本身并不依赖这条新路线。因此该模块：

- 不自动产生更强的 Carlson 指数；
- 不证明零密度假设或 RH；
- 不声称原始 Hilbert 不等式是新的数学定理；
- 贡献重点是具体极值核闭合和 Lean 中可组合的局部分离接口。
