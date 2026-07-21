/-
# Li 系数的加权零点求和表示（B1 切片）

本文件无条件证明 **Li 系数的重数加权零点求和表示**：

```text
li_weighted_zero_sum_representation :
  ∀ n ≥ 1, liCoefficient n =
    ∑' ρ : UpperHalfPlaneNontrivialZero, m_ξ(ρ) · liPairedTerm n ρ
```

与 `LiWeightedPositivity.lean` 的 B2 切片（
`rh_implies_li_criterion_of_weighted_representation`）拼接即得
**正向方向闭合** `rh_implies_li_criterion_target`（本文件末尾）。

## 数学路线

记 `L(s) = log ξ(s)`（在 `s = 1` 的邻域内取正则分支：`ξ(1) = 1/2` 实部
为正，连续性给出 `Re ξ > 0` 的小球，落在 slit plane 内）。

1. **加权部分分式展开**（`xi_weighted_partial_fraction_expansion`，
   `XiCorrectionConst.lean` 无条件已证）：在 `ξ s ≠ 0` 处
   `ξ'/ξ(s) = B + W(s)`，其中 `B = ξ'/ξ(0)`，
   `W(s) = Σ_ρ m_ξ(ρ)·([1/(s-ρ)+1/ρ] + [1/(s-conjρ)+1/conjρ])`。
2. **W 的高阶导数**（逐项微分，`hasSum_deriv_of_summable_norm` 的
   Weierstrass–Cauchy 机器）：对 `k ≥ 1`，在 `s = 1` 的小球上
   `W^{(k)}(s) = (-1)^k k! · D_{k+1}(s)`，其中
   `D_j(s) = Σ_ρ m_ξ(ρ)·((s-ρ)⁻¹^j + (s-conjρ)⁻¹^j)`。
3. **对合 `τ(ρ) = 1 - conjρ`**：保持上半平面非平凡零点集与解析重数
   （`analyticOrderNatAt_xiFunction_one_sub_conj`），把
   `D_m(1) =: S_m` 改写为 `R_m := Σ_ρ m_ξ(ρ)·(ρ⁻¹^m + conjρ⁻¹^m)`
   （`m ≥ 2` 时绝对收敛，换序合法）。
4. **一阶项**：`L'(1) = -B`（函数方程 `ξ(s) = ξ(1-s)` 求导）与
   `L'(1) = B + W(1)`、`W(1) = 2R_1`（`τ` 换序）联立得 `L'(1) = R_1`。
5. **Leibniz 组装**：`λ_n = (1/(n-1)!)·dⁿ/dsⁿ[s^{n-1}·L(s)]|_{s=1}`
   展开为 `Σ_{j=1}^n (C(n,j)/(j-1)!)·L^{(j)}(1)`，代入 2–4 的取值，
   与 `1-(1-1/ρ)^n = Σ_{j≥1} (-1)^{j-1}C(n,j)ρ^{-j}` 的二项式展开
   逐项比对，得到 `λ_n = Σ_ρ m_ξ(ρ)·liPairedTerm n ρ`。

## 证明纪律

无 `sorry`/`admit`/新公理；公理审计见 `Test/XiFunctionAxiomAudit.lean`。
-/

import RiemannExplorer.XiCorrectionConst
import RiemannExplorer.LiWeightedPositivity
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

open Complex ComplexConjugate Filter
open scoped BigOperators Topology

namespace RiemannExplorer

/-! ## Part 1：`s = 1` 邻域的对数分支 -/

/-- `Re ξ` 在 `s = 1` 的邻域内恒正（`ξ(1) = 1/2` + 连续性）。 -/
theorem xi_re_pos_nhds_one : ∀ᶠ s in 𝓝 (1 : ℂ), 0 < (xiFunction s).re := by
  have hc : ContinuousAt (fun s : ℂ => (xiFunction s).re) 1 :=
    (Complex.continuous_re.comp differentiable_xiFunction.continuous).continuousAt
  have h0 : (0 : ℝ) < (xiFunction 1).re := by
    rw [xiFunction_one]
    norm_num
  exact Tendsto.eventually hc (Ioi_mem_nhds h0)

/-- 球半径版本：存在 `r > 0` 使 `ball 1 r` 上 `Re ξ > 0`。 -/
theorem exists_ball_xi_re_pos :
    ∃ r : ℝ, 0 < r ∧ ∀ s ∈ Metric.ball (1 : ℂ) r, 0 < (xiFunction s).re :=
  Metric.eventually_nhds_iff_ball.mp xi_re_pos_nhds_one

section LogBranch

variable {r : ℝ} (hr0 : 0 < r)
  (hball : ∀ s ∈ Metric.ball (1 : ℂ) r, 0 < (xiFunction s).re)

include hr0 hball in
/-- `Re ξ > 0` 蕴含 `ξ s ≠ 0`。 -/
theorem xi_ne_zero_of_mem_ball {s : ℂ} (hs : s ∈ Metric.ball (1 : ℂ) r) :
    xiFunction s ≠ 0 := by
  have h := hball s hs
  intro h0
  rw [h0, Complex.zero_re] at h
  exact lt_irrefl 0 h

include hball in
/-- `Re ξ > 0` 蕴含 `ξ s ∈ slitPlane`。 -/
theorem xi_mem_slitPlane_of_mem_ball {s : ℂ} (hs : s ∈ Metric.ball (1 : ℂ) r) :
    xiFunction s ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (hball s hs))

include hr0 hball in
/-- `log ∘ ξ` 在球上复可微。 -/
theorem differentiableOn_log_xi :
    DifferentiableOn ℂ (fun s => Complex.log (xiFunction s)) (Metric.ball 1 r) :=
  fun s hs =>
    ((Complex.differentiableAt_log (xi_mem_slitPlane_of_mem_ball hball hs)).comp s
      (differentiable_xiFunction s)).differentiableWithinAt

include hr0 hball in
/-- 球上 `deriv (log ∘ ξ) = ξ'/ξ`（`Complex.deriv_log_comp_eq_logDeriv`）。 -/
theorem deriv_log_xi_eqOn :
    Set.EqOn (deriv fun s => Complex.log (xiFunction s))
      (fun s => deriv xiFunction s / xiFunction s) (Metric.ball 1 r) := by
  intro s hs
  have h := Complex.deriv_log_comp_eq_logDeriv (differentiable_xiFunction s)
    (xi_mem_slitPlane_of_mem_ball hball hs)
  show deriv (Complex.log ∘ xiFunction) s = deriv xiFunction s / xiFunction s
  rw [h]
  rfl

include hr0 hball in
/-- `log ∘ ξ` 在 `s = 1` 任意阶 `ContDiffAt`（复可微 ⇒ 光滑）。 -/
theorem contDiffAt_log_xi_one (n : ℕ) :
    ContDiffAt ℂ n (fun s => Complex.log (xiFunction s)) 1 :=
  ((differentiableOn_log_xi hr0 hball).contDiffOn Metric.isOpen_ball).contDiffAt
    (Metric.ball_mem_nhds 1 hr0)

end LogBranch

/-! ## Part 2：重数的 `s ↦ 1 - s` 与 `s ↦ 1 - conj s` 对称性 -/

/-- **`s ↦ 1 - s` 保序**：ξ 在 `1 - s₀` 的解析重数等于在 `s₀` 的解析重数。
由 `ξ(1 - s) = ξ(s)`（`xiFunction_one_sub`）把 `s₀` 处的局部因子分解
`ξ z = (z−s₀)ⁿ·g z` 经 `w = 1 - z` 转移到 `1 - s₀` 处：
`ξ w = (w−(1−s₀))ⁿ·((-1)ⁿ·g(1−w))`，两侧用
`AnalyticAt.analyticOrderAt_eq_natCast` 读出阶数相同。 -/
theorem analyticOrderNatAt_xiFunction_one_sub (s₀ : ℂ) :
    analyticOrderNatAt xiFunction (1 - s₀) = analyticOrderNatAt xiFunction s₀ := by
  have hne_top : ∀ z : ℂ, analyticOrderAt xiFunction z ≠ ⊤ :=
    fun z ht => xiFunction_ne_eventually_zero z (analyticOrderAt_eq_top.mp ht)
  set n := analyticOrderNatAt xiFunction s₀ with hn
  have hn_eq : analyticOrderAt xiFunction s₀ = (n : ℕ∞) :=
    (Nat.cast_analyticOrderNatAt (hne_top s₀)).symm
  obtain ⟨g, hg_an, hg_ne, hg_eq⟩ :=
    ((differentiable_xiFunction.analyticAt s₀).analyticOrderAt_eq_natCast).mp hn_eq
  have hsub_an : AnalyticAt ℂ (fun w : ℂ => 1 - w) (1 - s₀) :=
    analyticAt_const.sub analyticAt_id
  have hg1 : AnalyticAt ℂ g ((fun w : ℂ => 1 - w) (1 - s₀)) := by
    show AnalyticAt ℂ g (1 - (1 - s₀))
    rw [sub_sub_self]
    exact hg_an
  have hgT_an : AnalyticAt ℂ (fun w => (-1 : ℂ) ^ n * g (1 - w)) (1 - s₀) :=
    analyticAt_const.mul (hg1.comp hsub_an)
  have hgT_ne : (fun w => (-1 : ℂ) ^ n * g (1 - w)) (1 - s₀) ≠ 0 := by
    show (-1 : ℂ) ^ n * g (1 - (1 - s₀)) ≠ 0
    rw [sub_sub_self]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hg_ne
  have hmap : Filter.Tendsto (fun w : ℂ => 1 - w) (𝓝 (1 - s₀)) (𝓝 s₀) := by
    have hc : Continuous fun w : ℂ => 1 - w := continuous_const.sub continuous_id
    have h := hc.tendsto (1 - s₀)
    have he : (1 : ℂ) - (1 - s₀) = s₀ := sub_sub_self _ _
    rwa [he] at h
  have hev : ∀ᶠ w in 𝓝 (1 - s₀),
      xiFunction w = (w - (1 - s₀)) ^ n • (fun w => (-1 : ℂ) ^ n * g (1 - w)) w := by
    filter_upwards [hmap.eventually hg_eq] with w hw
    show xiFunction w = (w - (1 - s₀)) ^ n • ((-1 : ℂ) ^ n * g (1 - w))
    have hid : xiFunction w = xiFunction (1 - w) := xiFunction_one_sub w
    rw [hid, hw, smul_eq_mul, smul_eq_mul]
    have hsub : (1 : ℂ) - w - s₀ = -(w - (1 - s₀)) := by ring
    rw [hsub, neg_pow]
    ring
  have hn_eq2 : analyticOrderAt xiFunction (1 - s₀) = (n : ℕ∞) :=
    ((differentiable_xiFunction.analyticAt (1 - s₀)).analyticOrderAt_eq_natCast).mpr
      ⟨_, hgT_an, hgT_ne, hev⟩
  calc analyticOrderNatAt xiFunction (1 - s₀)
      = (analyticOrderAt xiFunction (1 - s₀)).toNat := rfl
    _ = n := by rw [hn_eq2]; rfl
    _ = analyticOrderNatAt xiFunction s₀ := hn.symm

/-- **`s ↦ 1 - conj s` 保序**：`1 - conj s₀ = conj (1 - s₀)`，故由共轭保序
（`analyticOrderNatAt_xiFunction_conj`）与 `1 - s` 保序
（`analyticOrderNatAt_xiFunction_one_sub`）复合即得。 -/
theorem analyticOrderNatAt_xiFunction_one_sub_conj (s₀ : ℂ) :
    analyticOrderNatAt xiFunction (1 - conj s₀) = analyticOrderNatAt xiFunction s₀ := by
  have h1 : (1 : ℂ) - conj s₀ = conj (1 - s₀) := by
    refine Complex.ext ?_ ?_
    · simp [Complex.sub_re, Complex.conj_re]
    · simp [Complex.sub_im, Complex.conj_im]
  rw [h1, analyticOrderNatAt_xiFunction_conj, analyticOrderNatAt_xiFunction_one_sub]

end RiemannExplorer
