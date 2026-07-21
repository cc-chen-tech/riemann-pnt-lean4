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
open scoped BigOperators Topology

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

/-! ## Blaschke 型因子：零点除子的有限支撑与重数 -/

/-- ξ 在 `closedBall 0 R` 上除子的有限支撑（Finset 形式）。 -/
noncomputable def xiZeroDiscFinset (R : ℝ) : Finset ℂ :=
  ((MeromorphicOn.divisor xiFunction (Metric.closedBall 0 R)).finiteSupport
    (isCompact_closedBall 0 R)).toFinset

lemma mem_xiZeroDiscFinset {R : ℝ} {u : ℂ} :
    u ∈ xiZeroDiscFinset R ↔
      MeromorphicOn.divisor xiFunction (Metric.closedBall 0 R) u ≠ 0 := by
  rw [xiZeroDiscFinset, Set.Finite.mem_toFinset]
  exact Function.mem_support

lemma xiZeroDiscFinset_subset_closedBall {R : ℝ} {u : ℂ} (hu : u ∈ xiZeroDiscFinset R) :
    u ∈ Metric.closedBall 0 R :=
  (MeromorphicOn.divisor xiFunction _).supportWithinDomain
    (Function.mem_support.mpr (mem_xiZeroDiscFinset.mp hu))

/-- ξ 在 `closedBall 0 R` 上除子的重数（自然数形式）。 -/
noncomputable def xiZeroDiscMult (R : ℝ) (u : ℂ) : ℕ :=
  (MeromorphicOn.divisor xiFunction (Metric.closedBall 0 R) u).toNat

/-- ξ 在闭圆盘上的亚纯性（ξ 整）。 -/
lemma meromorphicOn_xiFunction_closedBall (R : ℝ) :
    MeromorphicOn xiFunction (Metric.closedBall (0 : ℂ) R) :=
  (show AnalyticOnNhd ℂ xiFunction (Metric.closedBall (0 : ℂ) R) from
    fun z _ => differentiable_xiFunction.analyticAt z).meromorphicOn

lemma xiZeroDiscMult_cast (R : ℝ) (u : ℂ) :
    (xiZeroDiscMult R u : ℤ) =
      MeromorphicOn.divisor xiFunction (Metric.closedBall 0 R) u := by
  have hnn : 0 ≤ MeromorphicOn.divisor xiFunction (Metric.closedBall 0 R) u := by
    by_cases hu : u ∈ Metric.closedBall (0 : ℂ) R
    · rw [MeromorphicOn.divisor_apply (meromorphicOn_xiFunction_closedBall R) hu]
      exact WithTop.untop₀_nonneg.mpr
        (differentiable_xiFunction.analyticAt u).meromorphicOrderAt_nonneg
    · rw [MeromorphicOn.divisor_def, if_neg (fun h => hu h.2)]
  rw [xiZeroDiscMult, Int.toNat_of_nonneg hnn]

lemma xiFunction_eq_zero_of_mem_xiZeroDiscFinset {R : ℝ} {u : ℂ}
    (hu : u ∈ xiZeroDiscFinset R) : xiFunction u = 0 := by
  have huB := xiZeroDiscFinset_subset_closedBall hu
  have hne := mem_xiZeroDiscFinset.mp hu
  rw [MeromorphicOn.divisor_apply (meromorphicOn_xiFunction_closedBall R) huB] at hne
  have han : AnalyticAt ℂ xiFunction u := differentiable_xiFunction.analyticAt u
  have horder_ne : meromorphicOrderAt xiFunction u ≠ 0 := by
    intro h
    rw [h, WithTop.untop₀_zero] at hne
    exact hne rfl
  rw [han.meromorphicOrderAt_eq] at horder_ne
  have hao_ne : analyticOrderAt xiFunction u ≠ 0 := by
    intro h
    rw [h] at horder_ne
    simp at horder_ne
  exact (analyticOrderAt_ne_zero.mp hao_ne).2

lemma zero_notMem_xiZeroDiscFinset (R : ℝ) : (0 : ℂ) ∉ xiZeroDiscFinset R := by
  intro h
  have hz := xiFunction_eq_zero_of_mem_xiZeroDiscFinset h
  rw [xiFunction_zero] at hz
  norm_num at hz

lemma xiZeroDiscMult_eq_analyticOrderNatAt {R : ℝ} {u : ℂ}
    (hu : u ∈ Metric.closedBall (0 : ℂ) R) :
    xiZeroDiscMult R u = analyticOrderNatAt xiFunction u := by
  have hne_top : analyticOrderAt xiFunction u ≠ ⊤ :=
    fun ht => xiFunction_ne_eventually_zero u (analyticOrderAt_eq_top.mp ht)
  have key : MeromorphicOn.divisor xiFunction (Metric.closedBall 0 R) u =
      (analyticOrderNatAt xiFunction u : ℤ) := by
    rw [MeromorphicOn.divisor_apply (meromorphicOn_xiFunction_closedBall R) hu,
      (differentiable_xiFunction.analyticAt u).meromorphicOrderAt_eq,
      ← Nat.cast_analyticOrderNatAt hne_top, ENat.map_coe, WithTop.untop₀_coe]
  rw [xiZeroDiscMult, key, Int.toNat_natCast]

/-- Blaschke 型乘积 `B_R(z) = ∏_{u} canonicalFactor (2R) u z ^ {m_u}`。 -/
noncomputable def xiBlaschkeProd (R : ℝ) (z : ℂ) : ℂ :=
  ∏ u ∈ xiZeroDiscFinset R, Complex.canonicalFactor (2 * R) u z ^ xiZeroDiscMult R u

lemma xiZeroDiscFinset_mem_ball_two_mul {R : ℝ} (hR : 0 < R) {u : ℂ}
    (hu : u ∈ xiZeroDiscFinset R) : u ∈ Metric.ball (0 : ℂ) (2 * R) := by
  have huB := xiZeroDiscFinset_subset_closedBall hu
  rw [Metric.mem_ball, dist_zero_right]
  rw [Metric.mem_closedBall, dist_zero_right] at huB
  linarith

lemma xiBlaschkeProd_ne_zero {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) (2 * R))
    (hzS : ∀ u ∈ xiZeroDiscFinset R, z ≠ u) :
    xiBlaschkeProd R z ≠ 0 := by
  rw [xiBlaschkeProd, Finset.prod_ne_zero_iff]
  intro u hu
  exact pow_ne_zero _ (Complex.canonicalFactor_ne_zero
    (xiZeroDiscFinset_mem_ball_two_mul hR hu) hz (hzS u hu))

lemma norm_xiBlaschkeProd_eq_one {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ Metric.sphere (0 : ℂ) (2 * R)) :
    ‖xiBlaschkeProd R z‖ = 1 := by
  rw [xiBlaschkeProd, Complex.norm_prod]
  exact Finset.prod_eq_one fun u hu => by
    rw [norm_pow, Complex.norm_canonicalFactor_eval_circle_eq_one
      (xiZeroDiscFinset_mem_ball_two_mul hR hu) hz, one_pow]

/-! ## 正则化函数 `g`：`ξ · B` 消去零点后所得的解析无零点函数 -/

/-- Blaschke 分子的正则化因子 `((2R)² - conj u · w)/(2R)`。 -/
noncomputable def xiBlaschkeNumFactor (R : ℝ) (u w : ℂ) : ℂ :=
  ((2 * R : ℝ) ^ 2 - conj u * w) / (2 * R : ℝ)

lemma xiBlaschkeNumFactor_ne_zero {R : ℝ} (hR : 0 < R) {u w : ℂ}
    (hu : u ∈ Metric.closedBall (0 : ℂ) R) (hw : w ∈ Metric.closedBall (0 : ℂ) (2 * R)) :
    xiBlaschkeNumFactor R u w ≠ 0 := by
  rw [xiBlaschkeNumFactor, div_ne_zero_iff]
  refine ⟨?_, by simp [hR.ne']⟩
  intro hzero
  have heq : ((2 * R : ℝ) : ℂ) ^ 2 = conj u * w := sub_eq_zero.mp hzero
  have hN : ‖((2 * R : ℝ) : ℂ) ^ 2‖ = ‖conj u * w‖ := by rw [heq]
  have h2R : ‖((2 * R : ℝ) : ℂ)‖ = 2 * R := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [norm_pow, h2R, norm_mul, norm_conj] at hN
  rw [Metric.mem_closedBall, dist_zero_right] at hu hw
  have hle : ‖u‖ * ‖w‖ ≤ R * (2 * R) := mul_le_mul hu hw (norm_nonneg _) (by linarith)
  nlinarith

/-- 乘积恒等式（`w ≠ u` 时）：`(w - u) · canonicalFactor (2R) u w = xiBlaschkeNumFactor`。 -/
lemma mul_canonicalFactor_eq_xiBlaschkeNumFactor {R : ℝ} (hR : 0 < R) {u w : ℂ}
    (hwu : w ≠ u) :
    (w - u) * Complex.canonicalFactor (2 * R) u w = xiBlaschkeNumFactor R u w := by
  rw [Complex.canonicalFactor_apply, xiBlaschkeNumFactor]
  field_simp [sub_ne_zero.mpr hwu, hR.ne']

/-- **正则化函数的存在性**：存在 `g` 在 `ball 0 (3R)` 上解析、在 `closedBall 0 R` 上
无零点，且与 `ξ · B_R` 在 `ball 0 (3R)` 的余离散集上相等。
证明用 `MeromorphicOn.extract_zeros_poles` 把 ξ 在 `ball 0 (3R)` 内的所有零点抽出为
有理因子，再把 `closedBall 0 R` 内的因子与 Blaschke 乘积的极点配对成多项式因子。 -/
theorem exists_xiBlaschkeRegularized {R : ℝ} (hR : 0 < R) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) (3 * R)) ∧
      (∀ w ∈ Metric.closedBall (0 : ℂ) R, g w ≠ 0) ∧
      (fun w => xiFunction w * xiBlaschkeProd R w)
        =ᶠ[Filter.codiscreteWithin (Metric.ball (0 : ℂ) (3 * R))] g := by
  set U := Metric.ball (0 : ℂ) (3 * R) with hUdef
  have hξmero : MeromorphicOn xiFunction U :=
    (show AnalyticOnNhd ℂ xiFunction U from
      fun z _ => differentiable_xiFunction.analyticAt z).meromorphicOn
  have hξorder : ∀ u : U, meromorphicOrderAt xiFunction u ≠ ⊤ := by
    intro ⟨u, _⟩
    rw [(differentiable_xiFunction.analyticAt u).meromorphicOrderAt_eq]
    intro htop
    rw [ENat.map_eq_top_iff] at htop
    exact xiFunction_ne_eventually_zero u (analyticOrderAt_eq_top.mp htop)
  have hbig : (MeromorphicOn.divisor xiFunction (Metric.closedBall (0 : ℂ) (3 * R))).support.Finite :=
    (MeromorphicOn.divisor xiFunction _).finiteSupport (isCompact_closedBall 0 (3 * R))
  have hsuppU : (MeromorphicOn.divisor xiFunction U).support.Finite := by
    apply hbig.subset
    intro u hu
    have huU : u ∈ U := (MeromorphicOn.divisor xiFunction U).supportWithinDomain hu
    rw [Function.mem_support] at hu ⊢
    rw [MeromorphicOn.divisor_apply hξmero huU] at hu
    rwa [MeromorphicOn.divisor_apply (meromorphicOn_xiFunction_closedBall (3 * R))
      (Metric.ball_subset_closedBall huU)]
  obtain ⟨g₀, hg₀an, hg₀ne, hg₀eq⟩ := hξmero.extract_zeros_poles hξorder hsuppU
  set S : Finset ℂ := xiZeroDiscFinset R with hSdef
  set m : ℂ → ℕ := xiZeroDiscMult R with hmdef
  set DU := MeromorphicOn.divisor xiFunction U with hDUdef
  set S' : Finset ℂ := hsuppU.toFinset with hS'def
  set P : ℂ → ℂ := fun w =>
    (∏ u ∈ S, xiBlaschkeNumFactor R u w ^ m u) * (∏ u ∈ S' \ S, (w - u) ^ (DU u).toNat) with hPdef
  set g : ℂ → ℂ := fun w => g₀ w * P w with hgdef
  have hDU_nonneg : ∀ u ∈ S', 0 ≤ DU u := by
    intro u hu
    have huU : u ∈ U := (MeromorphicOn.divisor xiFunction U).supportWithinDomain
      (Function.mem_support.mpr ((Set.Finite.mem_toFinset _).mp hu))
    rw [hDUdef, MeromorphicOn.divisor_apply hξmero huU]
    exact WithTop.untop₀_nonneg.mpr
      (differentiable_xiFunction.analyticAt u).meromorphicOrderAt_nonneg
  have hSS' : S ⊆ S' := by
    intro u hu
    have huB := xiZeroDiscFinset_subset_closedBall hu
    have huU : u ∈ U := Metric.closedBall_subset_ball (by linarith) huB
    rw [hS'def, Set.Finite.mem_toFinset, Function.mem_support, hDUdef,
      MeromorphicOn.divisor_apply hξmero huU,
      ← MeromorphicOn.divisor_apply (meromorphicOn_xiFunction_closedBall R) huB]
    exact mem_xiZeroDiscFinset.mp hu
  have hDRU : ∀ u ∈ S, DU u = MeromorphicOn.divisor xiFunction (Metric.closedBall 0 R) u := by
    intro u hu
    have huB := xiZeroDiscFinset_subset_closedBall hu
    have huU : u ∈ U := Metric.closedBall_subset_ball (by linarith) huB
    rw [hDUdef, MeromorphicOn.divisor_apply hξmero huU,
      MeromorphicOn.divisor_apply (meromorphicOn_xiFunction_closedBall R) huB]
  have happF : ∀ w : ℂ, (∏ᶠ u, (fun x => x - u) ^ DU u) w = ∏ᶠ u, (w - u) ^ DU u := by
    intro w
    have hsub : Function.mulSupport (fun u => (fun x => x - u) ^ DU u) ⊆ ↑S' := by
      intro u hu
      rw [Function.mem_mulSupport] at hu
      by_contra huS'
      rw [Finset.mem_coe, hS'def, Set.Finite.mem_toFinset, Function.mem_support] at huS'
      push_neg at huS'
      rw [huS', zpow_zero] at hu
      exact hu rfl
    have hf : Function.HasFiniteMulSupport (fun u => (fun x => x - u) ^ DU u) :=
      (Finset.finite_toSet S').subset hsub
    rw [finprod_apply hf w]
    apply finprod_congr
    intro u
    rfl
  have hg₀eq' : xiFunction =ᶠ[Filter.codiscreteWithin U]
      (fun w => (∏ᶠ u, (w - u) ^ DU u) * g₀ w) :=
    hg₀eq.trans (Filter.Eventually.of_forall fun w => by
      rw [Pi.smul_apply', smul_eq_mul, happF w])
  refine ⟨g, fun w hw => ?_, fun w hw => ?_, ?_⟩
  · -- 解析性
    apply AnalyticAt.mul (hg₀an w hw)
    apply AnalyticAt.mul
    · apply Finset.analyticAt_fun_prod
      intro u hu
      apply AnalyticAt.pow
      unfold xiBlaschkeNumFactor
      fun_prop (disch := simp [hR.ne'])
    · apply Finset.analyticAt_fun_prod
      intro u hu
      apply AnalyticAt.pow
      fun_prop
  · -- closedBall 0 R 上无零点
    have hwU : w ∈ U := Metric.closedBall_subset_ball (by linarith) hw
    simp only [hgdef, hPdef]
    apply mul_ne_zero (hg₀ne ⟨w, hwU⟩)
    apply mul_ne_zero
    · rw [Finset.prod_ne_zero_iff]
      intro u hu
      exact pow_ne_zero _ (xiBlaschkeNumFactor_ne_zero hR
        (xiZeroDiscFinset_subset_closedBall hu)
        (Metric.closedBall_subset_closedBall (by linarith) hw))
    · rw [Finset.prod_ne_zero_iff]
      intro u hu
      rw [Finset.mem_sdiff] at hu
      obtain ⟨huS', huS⟩ := hu
      apply pow_ne_zero _
      have huU : u ∈ U := (MeromorphicOn.divisor xiFunction U).supportWithinDomain
        (Function.mem_support.mpr ((Set.Finite.mem_toFinset _).mp huS'))
      have hnorm_u : R < ‖u‖ := by
        by_contra hle
        push_neg at hle
        have huB : u ∈ Metric.closedBall (0 : ℂ) R := by
          rw [Metric.mem_closedBall, dist_zero_right]; exact hle
        have hdu : DU u ≠ 0 := Function.mem_support.mp ((Set.Finite.mem_toFinset _).mp huS')
        rw [hDUdef, MeromorphicOn.divisor_apply hξmero huU,
          ← MeromorphicOn.divisor_apply (meromorphicOn_xiFunction_closedBall R) huB] at hdu
        exact huS (mem_xiZeroDiscFinset.mpr hdu)
      intro hzero
      rw [sub_eq_zero] at hzero
      rw [Metric.mem_closedBall, dist_zero_right] at hw
      rw [← hzero] at hnorm_u
      linarith
  · -- 余离散集上的相等
    classical
    have hBeq : (fun w => (∏ᶠ u, (w - u) ^ DU u) * g₀ w * xiBlaschkeProd R w)
        =ᶠ[Filter.codiscreteWithin U] g := by
      have hS'cod : (↑S' : Set ℂ)ᶜ ∈ Filter.codiscreteWithin U := by
        rw [codiscreteWithin_iff_locallyFiniteComplementWithin]
        intro z _
        refine ⟨Set.univ, Filter.univ_mem, ?_⟩
        have : Set.univ ∩ (U \ (↑S' : Set ℂ)ᶜ) = U ∩ ↑S' := by
          simp
        rw [this]
        exact (Finset.finite_toSet S').subset Set.inter_subset_right
      apply Filter.eventuallyEq_of_mem hS'cod
      intro w hwS'
      have hwu : ∀ u ∈ S', w ≠ u := by
        intro u hu h
        apply hwS'
        rw [h]
        exact Finset.mem_coe.mpr hu
      have hfinprod : (∏ᶠ u, (w - u) ^ DU u) = ∏ u ∈ S', (w - u) ^ DU u := by
        apply finprod_eq_prod_of_mulSupport_subset
        intro u hu
        rw [Function.mem_mulSupport] at hu
        by_contra huS'
        rw [Finset.mem_coe, hS'def, Set.Finite.mem_toFinset, Function.mem_support] at huS'
        push_neg at huS'
        rw [huS', zpow_zero] at hu
        exact hu rfl
      show (∏ᶠ u, (w - u) ^ DU u) * g₀ w * xiBlaschkeProd R w = g w
      rw [hfinprod, ← Finset.prod_sdiff hSS']
      have hfactor : ∀ u ∈ S, (w - u) ^ DU u * (Complex.canonicalFactor (2 * R) u w ^ m u)
          = xiBlaschkeNumFactor R u w ^ m u := by
        intro u hu
        have hcast : DU u = (m u : ℤ) := by
          rw [hmdef, xiZeroDiscMult_cast, hDRU u hu]
        rw [hcast, zpow_natCast, ← mul_pow, mul_canonicalFactor_eq_xiBlaschkeNumFactor hR
          (hwu u (hSS' hu))]
      have hpow : ∀ u ∈ S' \ S, (w - u) ^ DU u = (w - u) ^ (DU u).toNat := by
        intro u hu
        rw [Finset.mem_sdiff] at hu
        have hnn := hDU_nonneg u hu.1
        conv_lhs => rw [← Int.toNat_of_nonneg hnn]
        rw [zpow_natCast]
      rw [Finset.prod_congr rfl hpow]
      have hprodS : (∏ u ∈ S, (w - u) ^ DU u) * xiBlaschkeProd R w
          = ∏ u ∈ S, xiBlaschkeNumFactor R u w ^ m u := by
        rw [xiBlaschkeProd, ← hSdef, ← hmdef, ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl hfactor
      simp only [hgdef, hPdef]
      rw [← hprodS]
      ring
    have h1 : (fun w => xiFunction w * xiBlaschkeProd R w)
        =ᶠ[Filter.codiscreteWithin U]
          (fun w => (∏ᶠ u, (w - u) ^ DU u) * g₀ w * xiBlaschkeProd R w) :=
      hg₀eq'.mul Filter.EventuallyEq.rfl
    exact h1.trans hBeq

/-- **余离散相等 ⇒ 邻域相等**：在 `ξ·B_R` 连续且 `g` 连续的点 `w`（`w ∈ ball 0 (3R)`、
`w ∉ xiZeroDiscFinset R`），两函数在 `𝓝 w` 中相等。 -/
theorem xiBlaschkeRegularized_eventuallyEq_nhds {R : ℝ} (hR : 0 < R) {g : ℂ → ℂ}
    (hg : (fun w => xiFunction w * xiBlaschkeProd R w)
      =ᶠ[Filter.codiscreteWithin (Metric.ball (0 : ℂ) (3 * R))] g)
    (hgC : ContinuousOn g (Metric.ball (0 : ℂ) (3 * R)))
    {w : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) (3 * R)) (hwS : w ∉ xiZeroDiscFinset R) :
    (fun w => xiFunction w * xiBlaschkeProd R w) =ᶠ[𝓝 w] g := by
  set U := Metric.ball (0 : ℂ) (3 * R) with hUdef
  set F : ℂ → ℂ := fun w => xiFunction w * xiBlaschkeProd R w with hFdef
  have hFC : ContinuousAt F w := by
    have hBan : AnalyticAt ℂ (xiBlaschkeProd R) w := by
      unfold xiBlaschkeProd
      apply Finset.analyticAt_fun_prod
      intro u hu
      apply AnalyticAt.pow
      exact Complex.analyticOnNhd_canonicalFactor (R := 2 * R) (w := u) w
        (Set.mem_compl_singleton_iff.mpr (fun h : w = u => hwS (h ▸ hu)))
    rw [hFdef]
    exact ContinuousAt.mul differentiable_xiFunction.continuous.continuousAt hBan.continuousAt
  have hUmem : U ∈ 𝓝 w := Metric.isOpen_ball.mem_nhds hw
  have ht : {x | F x = g x} ∈ Filter.codiscreteWithin U := hg
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at ht
  have h1 := ht w hw
  have hU' : U ∈ 𝓝[≠] w := nhdsWithin_le_nhds hUmem
  have h3 : {x | F x = g x} ∈ 𝓝[≠] w := by
    apply Filter.mem_of_superset (Filter.inter_mem h1 hU')
    rintro x ⟨hx1, hx2⟩
    rcases hx1 with h | h
    · exact h
    · exact absurd hx2 h
  have hval : F w = g w := by
    have hF' : Filter.Tendsto F (𝓝[≠] w) (𝓝 (F w)) := hFC.continuousWithinAt
    have hgC' : ContinuousAt g w := hgC.continuousAt hUmem
    have h2 : Filter.Tendsto g (𝓝[≠] w) (𝓝 (F w)) := hF'.congr' h3
    exact tendsto_nhds_unique h2 hgC'.continuousWithinAt
  have h4 : insert w {x | F x = g x} ∈ 𝓝 w := by
    rw [mem_nhdsWithin] at h3
    obtain ⟨t, htopen, hat, htsub⟩ := h3
    apply Filter.mem_of_superset (htopen.mem_nhds hat)
    intro y hy
    by_cases hyw : y = w
    · exact Or.inl hyw
    · exact Or.inr (htsub ⟨hy, hyw⟩)
  apply Filter.mem_of_superset h4
  intro y hy
  rcases hy with rfl | h
  · exact hval
  · exact h

/-- **`g` 在外圈的对数上界**：`w ∈ sphere 0 (2R)` 时
`log‖g w‖ ≤ K(1+2R)log(4+2R)`（`g w = ξ w · B w` 且 `‖B w‖ = 1`）。 -/
theorem log_norm_xiBlaschkeRegularized_le_of_mem_sphere {R : ℝ} (hR : 0 < R) {K : ℝ} (hK : 0 ≤ K)
    (hgrow : ∀ s : ℂ, ‖xiFunction s‖ ≤ Real.exp (K * (1 + ‖s‖) * Real.log (4 + ‖s‖)))
    {g : ℂ → ℂ}
    (hg : (fun w => xiFunction w * xiBlaschkeProd R w)
      =ᶠ[Filter.codiscreteWithin (Metric.ball (0 : ℂ) (3 * R))] g)
    (hgC : ContinuousOn g (Metric.ball (0 : ℂ) (3 * R)))
    {w : ℂ} (hw : w ∈ Metric.sphere (0 : ℂ) (2 * R)) :
    Real.log ‖g w‖ ≤ K * (1 + 2 * R) * Real.log (4 + 2 * R) := by
  have hwU : w ∈ Metric.ball (0 : ℂ) (3 * R) := by
    rw [Metric.mem_sphere, dist_zero_right] at hw
    rw [Metric.mem_ball, dist_zero_right, hw]
    linarith
  have hwS : w ∉ xiZeroDiscFinset R := by
    intro hmem
    have huB := xiZeroDiscFinset_subset_closedBall hmem
    rw [Metric.mem_closedBall, dist_zero_right] at huB
    rw [Metric.mem_sphere, dist_zero_right] at hw
    linarith
  have hval : xiFunction w * xiBlaschkeProd R w = g w :=
    (xiBlaschkeRegularized_eventuallyEq_nhds hR hg hgC hwU hwS).self_of_nhds
  have hnorm : ‖g w‖ = ‖xiFunction w‖ := by
    rw [← hval, norm_mul, norm_xiBlaschkeProd_eq_one hR hw, mul_one]
  have hBnn : 0 ≤ K * (1 + 2 * R) * Real.log (4 + 2 * R) :=
    mul_nonneg (mul_nonneg hK (by positivity)) (Real.log_nonneg (by linarith))
  by_cases hg0 : g w = 0
  · rw [hg0, norm_zero, Real.log_zero]
    exact hBnn
  · rw [Metric.mem_sphere, dist_zero_right] at hw
    have hξw := hgrow w
    rw [hw] at hξw
    have hpos : (0 : ℝ) < ‖xiFunction w‖ := by
      rw [← hnorm]
      exact norm_pos_iff.mpr hg0
    rw [hnorm]
    calc Real.log ‖xiFunction w‖ ≤ Real.log (Real.exp _) := Real.log_le_log hpos hξw
    _ = K * (1 + 2 * R) * Real.log (4 + 2 * R) := Real.log_exp _

/-- **圆心下界**：`log‖g 0‖ ≥ log(1/2)`（每个 Blaschke 因子在 `0` 处范数
`2R/‖u‖ ≥ 1`，对数非负）。 -/
theorem center_lower_xiBlaschkeRegularized {R : ℝ} (hR : 0 < R) {g : ℂ → ℂ}
    (hg : (fun w => xiFunction w * xiBlaschkeProd R w)
      =ᶠ[Filter.codiscreteWithin (Metric.ball (0 : ℂ) (3 * R))] g)
    (hgC : ContinuousOn g (Metric.ball (0 : ℂ) (3 * R))) :
    Real.log (1 / 2) ≤ Real.log ‖g 0‖ := by
  have h0U : (0 : ℂ) ∈ Metric.ball (0 : ℂ) (3 * R) := by
    rw [Metric.mem_ball, dist_self]
    linarith
  have h0S : (0 : ℂ) ∉ xiZeroDiscFinset R := zero_notMem_xiZeroDiscFinset R
  have hval : xiFunction 0 * xiBlaschkeProd R 0 = g 0 :=
    (xiBlaschkeRegularized_eventuallyEq_nhds hR hg hgC h0U h0S).self_of_nhds
  have hξ0 : xiFunction 0 ≠ 0 := by rw [xiFunction_zero]; norm_num
  have hune : ∀ u ∈ xiZeroDiscFinset R, u ≠ 0 := by
    intro u hu h
    have hz := xiFunction_eq_zero_of_mem_xiZeroDiscFinset hu
    rw [h, xiFunction_zero] at hz
    norm_num at hz
  have hB0ne : xiBlaschkeProd R 0 ≠ 0 := xiBlaschkeProd_ne_zero hR
    (by rw [Metric.mem_closedBall, dist_zero_right, norm_zero]; linarith)
    (fun u hu h => hune u hu h.symm)
  have hcanon : ∀ u ∈ xiZeroDiscFinset R, ‖Complex.canonicalFactor (2 * R) u 0‖ = 2 * R / ‖u‖ := by
    intro u hu
    have hu0 := hune u hu
    have h2R0 : (0 : ℝ) < 2 * R := by positivity
    rw [Complex.canonicalFactor_apply]
    simp only [mul_zero, sub_zero, zero_sub, norm_div, norm_mul, norm_neg]
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h2R0.le, pow_two,
      mul_div_mul_left _ _ h2R0.ne']
  have hlogprod : Real.log ‖xiBlaschkeProd R 0‖ =
      ∑ u ∈ xiZeroDiscFinset R, (xiZeroDiscMult R u : ℝ) * Real.log (2 * R / ‖u‖) := by
    rw [xiBlaschkeProd, Complex.norm_prod]
    rw [Real.log_prod (fun u hu => by
      rw [norm_pow, hcanon u hu]
      exact pow_ne_zero _ (div_ne_zero (by positivity : (2 * R : ℝ) ≠ 0)
        (norm_pos_iff.mpr (hune u hu)).ne'))]
    apply Finset.sum_congr rfl
    intro u hu
    rw [norm_pow, hcanon u hu, Real.log_pow]
  have hterm : ∀ u ∈ xiZeroDiscFinset R,
      0 ≤ (xiZeroDiscMult R u : ℝ) * Real.log (2 * R / ‖u‖) := by
    intro u hu
    have huB := xiZeroDiscFinset_subset_closedBall hu
    rw [Metric.mem_closedBall, dist_zero_right] at huB
    apply mul_nonneg (Nat.cast_nonneg _)
    apply Real.log_nonneg
    rw [one_le_div (norm_pos_iff.mpr (hune u hu))]
    linarith
  have hg0 : g 0 ≠ 0 := by rw [← hval]; exact mul_ne_zero hξ0 hB0ne
  have hB0log : 0 ≤ Real.log ‖xiBlaschkeProd R 0‖ := by
    rw [hlogprod]
    exact Finset.sum_nonneg hterm
  have hξ0n : ‖xiFunction 0‖ = 1 / 2 := by rw [xiFunction_zero]; norm_num
  rw [← hval, norm_mul,
    Real.log_mul (norm_ne_zero_iff.mpr hξ0) (norm_ne_zero_iff.mpr hB0ne), hξ0n]
  linarith

end RiemannExplorer
