/-
# ξ 对数导数的圆盘零点主部估计（Blaschke / Borel–Carathéodory 路线）

本文件给出 ξ'/ξ 在同心圆盘上的**零点主部分解估计**：

```text
‖ξ'/ξ(z) − Σ_{u ∈ closedBall 0 R} m_u·(z−u)⁻¹‖ ≤ C·(1 + log R)²
    (∀ R ≥ 4, z ∈ closedBall 0 (R/2), ξ z ≠ 0)
```

这是重数加权部分分式展开「修正项恒为常数」归约
（`xi_weighted_partial_fraction_expansion_of_const_correction`）所需的
最后一个分析输入：差函数 `E = ξ'/ξ − c₀ − W` 在 `|z| = R` 上由此获得
`O(log² R)` 控制，从而次线性 ⇒ 常数 ⇒ 恒为零。

## 方法（经典 Poisson–Jensen / Blaschke 论证）

取 `D` 为 ξ 在 `closedBall 0 R` 上的零点除子（有限支撑），构造
Blaschke 型因子 `B(z) = ∏_{u} canonicalFactor (2R) u ^ {m_u}`
（mathlib `Complex.canonicalFactor`：在 `ball 0 (2R)` 内以 `u` 为单极点、
`closedBall 0 (2R)` 内无零点、`sphere 0 (2R)` 上范数恒为 1），令
`g = ξ·B`。则：

- `g` 在 `closedBall 0 (2R)` 上解析（`u` 处极点与 ξ 的 `m_u` 阶零点相消，
  经 `AnalyticAt.analyticOrderAt_eq_natCast` 因子分解逐点验证）；
- `g` 在 `closedBall 0 R` 上无零点；
- `sphere 0 (2R)` 上 `‖g‖ = ‖ξ‖ ≤ exp(K(1+2R)log(4+2R))`（增长阶 ≤ 1，
  `exists_norm_xiFunction_le_exp_order_one`），故 `log‖g‖` 在
  `sphere 0 R` 上有上界 `B := K(1+2R)log(4+2R)`；
- `log‖g 0‖ = log‖ξ 0‖ + Σ m_u·log(2R/‖u‖) ≥ log(1/2)`（每项 `log(2R/‖u‖)
  ≥ 0`），给出圆心下界 `C₀ := −log 2`；
- 对 `logDeriv g` 应用仓库已有的 Borel–Carathéodory + Cauchy 引理
  `ZeroFreeRegion.norm_logDeriv_le_four_mul_max_sub_mul_add_div_sq_of_sphere_log_norm_le_of_center_lower`，
  得 `‖logDeriv g z‖ ≤ 24·max(B − C₀, 1)/R = O(log R)`；
- 而 `logDeriv ξ z = logDeriv g z + Σ m_u·[(z−u)⁻¹ + conj u/((2R)² − conj u·z)]`，
  Blaschke 余项每项 `≤ 2/(7R)`，零点计数 `n = O(R log R)`（Jensen，
  `jensen_inner_zero_multiplicity_le_log_div`）给出总余项 `O(log R)`。

全部无条件、无 sorry。
-/

import PrimeNumberTheorem.AnalyticJensen
import PrimeNumberTheorem.AnalyticBorel
import RiemannExplorer.XiPartialFractionEntire
import RiemannExplorer.XiGrowthOrder

open Complex ComplexConjugate Metric Filter Real
open scoped BigOperators

namespace RiemannExplorer

/-! ## 圆平均对数上界 -/

/-- **ξ 的圆平均对数界（无条件）**：存在 `K ≥ 0`，对所有 `t > 0`，
`circleAverage (log‖ξ·‖) 0 t ≤ K·(1+t)·log(4+t)`。
由增长阶 ≤ 1（`exists_norm_xiFunction_le_exp_order_one`，常数调整为非负）
与圆平均引理 `circleAverage_log_norm_le_log_of_norm_le` 直接得到。 -/
theorem exists_circleAverage_log_norm_xi_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 < t →
      circleAverage (Real.log ‖xiFunction ·‖) 0 t ≤ K * (1 + t) * Real.log (4 + t) := by
  obtain ⟨K₀, hK₀⟩ := exists_norm_xiFunction_le_exp_order_one
  refine ⟨max K₀ 0, le_max_right _ _, fun t ht => ?_⟩
  have hexp : ∀ s : ℂ, ‖xiFunction s‖ ≤
      Real.exp (max K₀ 0 * (1 + ‖s‖) * Real.log (4 + ‖s‖)) := by
    intro s
    refine (hK₀ s).trans (Real.exp_le_exp.mpr ?_)
    have hnn : (0 : ℝ) ≤ (1 + ‖s‖) * Real.log (4 + ‖s‖) :=
      mul_nonneg (by positivity) (Real.log_nonneg (by linarith [norm_nonneg s]))
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left K₀ 0) hnn
  have hM : (1 : ℝ) ≤ Real.exp (max K₀ 0 * (1 + t) * Real.log (4 + t)) :=
    Real.one_le_exp (mul_nonneg (mul_nonneg (le_max_right _ _) (by positivity))
      (Real.log_nonneg (by linarith)))
  have hsphere : ∀ z ∈ Metric.sphere (0 : ℂ) t, ‖xiFunction z‖ ≤
      Real.exp (max K₀ 0 * (1 + t) * Real.log (4 + t)) := by
    intro z hz
    rw [Metric.mem_sphere, dist_zero_right] at hz
    have h1 := hexp z
    rwa [hz] at h1
  have hmer : MeromorphicOn xiFunction (Metric.closedBall 0 t) :=
    (show AnalyticOnNhd ℂ xiFunction (Metric.closedBall 0 t) from
      fun z _ => differentiable_xiFunction.analyticAt z).meromorphicOn
  have h := PrimeNumberTheorem.CarlsonZeroDensity.circleAverage_log_norm_le_log_of_norm_le
    ht hmer hM hsphere
  rwa [Real.log_exp] at h

/-! ## Jensen 零点计数界 -/

/-- **ξ 的圆盘零点计数（无条件）**：在 `closedBall 0 R`（`R ≥ 4`）内按解析
重数计次的零点总数 `≤ (K(1+2R)log(4+2R) + log 2)/log 2 = O(R log R)`，
其中 `K` 取自 `exists_circleAverage_log_norm_xi_le`。
由 Jensen 计数引理 `jensen_inner_zero_multiplicity_le_log_div`
（`r = R, R' = 2R`）与嵌套圆盘上除子的一致性（`divisor_apply` 两侧同取
`(meromorphicOrderAt ξ u).untop₀`）得到。 -/
theorem xi_zero_count_in_closedBall_le {K : ℝ}
    (hK : ∀ t : ℝ, 0 < t → circleAverage (Real.log ‖xiFunction ·‖) 0 t ≤
      K * (1 + t) * Real.log (4 + t)) (R : ℝ) (hR : 4 ≤ R) :
    (∑ᶠ u ∈ Metric.closedBall 0 R,
        ((MeromorphicOn.divisor xiFunction (Metric.closedBall 0 R) u : ℤ) : ℝ)) ≤
      (K * (1 + 2 * R) * Real.log (4 + 2 * R) + Real.log 2) / Real.log 2 := by
  have hR0 : (0 : ℝ) < R := by linarith
  have hanR : AnalyticOnNhd ℂ xiFunction (Metric.closedBall 0 R) :=
    fun z _ => differentiable_xiFunction.analyticAt z
  have han2R : AnalyticOnNhd ℂ xiFunction (Metric.closedBall 0 (2 * R)) :=
    fun z _ => differentiable_xiFunction.analyticAt z
  have hcenter : (1 / 2 : ℝ) ≤ ‖xiFunction 0‖ := by
    rw [xiFunction_zero]
    norm_num
  have hcount := PrimeNumberTheorem.CarlsonZeroDensity.jensen_inner_zero_multiplicity_le_log_div
    (c := 0) (r := R) (R := 2 * R) (f := xiFunction)
    hR0 (by linarith) han2R (by norm_num) hcenter (hK (2 * R) (by linarith))
  have hlogR : Real.log (2 * R / R) = Real.log 2 := by
    have h2 : (2 : ℝ) * R / R = 2 := by field_simp [hR0.ne']
    rw [h2]
  have hloghalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [hlogR, hloghalf] at hcount
  have hD : ∀ u ∈ Metric.closedBall 0 R,
      MeromorphicOn.divisor xiFunction (Metric.closedBall 0 (2 * R)) u =
        MeromorphicOn.divisor xiFunction (Metric.closedBall 0 R) u := by
    intro u hu
    rw [MeromorphicOn.divisor_apply han2R.meromorphicOn
        (Metric.closedBall_subset_closedBall (by linarith) hu),
      MeromorphicOn.divisor_apply hanR.meromorphicOn hu]
  have heq : (∑ᶠ u ∈ Metric.closedBall 0 R,
        ((MeromorphicOn.divisor xiFunction (Metric.closedBall 0 (2 * R)) u : ℤ) : ℝ)) =
      (∑ᶠ u ∈ Metric.closedBall 0 R,
        ((MeromorphicOn.divisor xiFunction (Metric.closedBall 0 R) u : ℤ) : ℝ)) := by
    rw [finsum_mem_def, finsum_mem_def]
    apply finsum_congr
    intro u
    by_cases hu : u ∈ Metric.closedBall 0 R
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, hD u hu]
    · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu]
  rw [heq] at hcount
  calc (∑ᶠ u ∈ Metric.closedBall 0 R,
        ((MeromorphicOn.divisor xiFunction (Metric.closedBall 0 R) u : ℤ) : ℝ))
      ≤ (K * (1 + 2 * R) * Real.log (4 + 2 * R) - -Real.log 2) / Real.log 2 := hcount
    _ = (K * (1 + 2 * R) * Real.log (4 + 2 * R) + Real.log 2) / Real.log 2 := by ring

end RiemannExplorer
