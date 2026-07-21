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

/-! ## Part 3：重数加权逆幂级数 `D_j` 的逐项微分 -/

/-- 重数加权逆幂配对项：`m_ξ(ρ)·((s-ρ)⁻¹^j + (s-conjρ)⁻¹^j)`。 -/
noncomputable def xiWeightedInvPowTerm (j : ℕ) (s ρ : ℂ) : ℂ :=
  (analyticOrderNatAt xiFunction ρ : ℂ) * ((s - ρ)⁻¹ ^ j + (s - conj ρ)⁻¹ ^ j)

/-- 重数加权逆幂配对级数 `D_j(s)`。 -/
noncomputable def xiWeightedInvPowSum (j : ℕ) (s : ℂ) : ℂ :=
  ∑' ρ : UpperHalfPlaneNontrivialZero, xiWeightedInvPowTerm j s (ρ : ℂ)

/-- M-判别界函数：`‖ρ‖ < 4`（有限支撑）用 `(2/r₁)^j` 常数界，
`‖ρ‖ ≥ 4` 用 `20·‖ρ‖⁻²` 界（对一切 `j ≥ 1` 统一：高段逐片
`≤ 2^{4-j}‖ρ‖⁻² ≤ 4‖ρ‖⁻²`，`j = 1` 配对恒等式给出 `20‖ρ‖⁻²`）。 -/
noncomputable def xiWeightedInvPowBound (r₁ : ℝ) (j : ℕ)
    (ρ : UpperHalfPlaneNontrivialZero) : ℝ :=
  if ‖(ρ : ℂ)‖ < 4 then
    (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * (2 * (2 / r₁) ^ j)
  else
    (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * (20 * ‖(ρ : ℂ)‖⁻¹ ^ 2)

/-- 界函数可和：低段有限支撑（`nontrivialZerosFinset 4` 原像之外恒零），
高段是 `summable_xiOrder_mul_norm_inv_sq_upperZeros` 的常数倍。 -/
theorem summable_xiWeightedInvPowBound {r₁ : ℝ} (hr₁ : 0 < r₁) (j : ℕ) :
    Summable (xiWeightedInvPowBound r₁ j) := by
  show Summable fun ρ => xiWeightedInvPowBound r₁ j ρ
  classical
  have hsplit : (fun ρ : UpperHalfPlaneNontrivialZero ↦ xiWeightedInvPowBound r₁ j ρ) =
      (fun ρ : UpperHalfPlaneNontrivialZero ↦
          if ‖(ρ : ℂ)‖ < 4 then
            (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * (2 * (2 / r₁) ^ j)
          else 0) +
        (fun ρ : UpperHalfPlaneNontrivialZero ↦
          if ‖(ρ : ℂ)‖ < 4 then 0
          else (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * (20 * ‖(ρ : ℂ)‖⁻¹ ^ 2)) := by
    funext ρ
    simp only [Pi.add_apply, xiWeightedInvPowBound]
    by_cases h : ‖(ρ : ℂ)‖ < 4
    · rw [if_pos h, if_pos h, if_pos h, add_zero]
    · rw [if_neg h, if_neg h, if_neg h, zero_add]
  rw [hsplit]
  refine Summable.add ?_ ?_
  · apply summable_of_ne_finset_zero
      (s := (PrimeNumberTheorem.nontrivialZerosFinset 4).preimage
        (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn)
    intro ρ hρ
    rw [Finset.mem_preimage] at hρ
    by_cases hlt : ‖(ρ : ℂ)‖ < 4
    · exfalso
      apply hρ
      rw [PrimeNumberTheorem.mem_nontrivialZerosFinset]
      exact ⟨ρ.2.1, (Complex.abs_im_le_norm _).trans hlt.le⟩
    · exact if_neg hlt
  · refine Summable.of_norm_bounded
      (g := fun ρ : UpperHalfPlaneNontrivialZero ↦
        20 * ((analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹ ^ 2))
      (summable_xiOrder_mul_norm_inv_sq_upperZeros.mul_left _) fun ρ => ?_
    by_cases h : ‖(ρ : ℂ)‖ < 4
    · rw [if_pos h, norm_zero]
      positivity
    · rw [if_neg h, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤
          (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * (20 * ‖(ρ : ℂ)‖⁻¹ ^ 2))]
      exact le_of_eq (by ring)

/-- W 的 M-判别界函数：低段（有限支撑）逐片 `2/r₁` 与 `‖ρ‖⁻¹`，
高段 `22·‖ρ‖⁻²`（首对配恒等式 `≤ 20‖ρ‖⁻²`，常数对 `2|re ρ|/‖ρ‖² ≤ 2‖ρ‖⁻²`）。
注：`xiWeightedMittagLefflerTerm`/`xiWeightedMittagLefflerSum` 已在
`XiPartialFractionWeighted.lean` 定义（经 `XiCorrectionConst` 导入），本文件
只补充球上 M-判别与逐项微分机器。 -/
noncomputable def xiWeightedMittagLefflerBound (r₁ : ℝ)
    (ρ : UpperHalfPlaneNontrivialZero) : ℝ :=
  if ‖(ρ : ℂ)‖ < 4 then
    (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * (4 / r₁ + 2 * ‖(ρ : ℂ)‖⁻¹)
  else
    (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * (22 * ‖(ρ : ℂ)‖⁻¹ ^ 2)

/-- W 界函数可和：低段有限支撑（`nontrivialZerosFinset 4` 原像之外恒零），
高段是 `summable_xiOrder_mul_norm_inv_sq_upperZeros` 的常数倍。 -/
theorem summable_xiWeightedMittagLefflerBound {r₁ : ℝ} (hr₁ : 0 < r₁) :
    Summable (xiWeightedMittagLefflerBound r₁) := by
  show Summable fun ρ => xiWeightedMittagLefflerBound r₁ ρ
  classical
  have hsplit : (fun ρ : UpperHalfPlaneNontrivialZero ↦ xiWeightedMittagLefflerBound r₁ ρ) =
      (fun ρ : UpperHalfPlaneNontrivialZero ↦
          if ‖(ρ : ℂ)‖ < 4 then
            (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * (4 / r₁ + 2 * ‖(ρ : ℂ)‖⁻¹)
          else 0) +
        (fun ρ : UpperHalfPlaneNontrivialZero ↦
          if ‖(ρ : ℂ)‖ < 4 then 0
          else (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * (22 * ‖(ρ : ℂ)‖⁻¹ ^ 2)) := by
    funext ρ
    simp only [Pi.add_apply, xiWeightedMittagLefflerBound]
    by_cases h : ‖(ρ : ℂ)‖ < 4
    · rw [if_pos h, if_pos h, if_pos h, add_zero]
    · rw [if_neg h, if_neg h, if_neg h, zero_add]
  rw [hsplit]
  refine Summable.add ?_ ?_
  · apply summable_of_ne_finset_zero
      (s := (PrimeNumberTheorem.nontrivialZerosFinset 4).preimage
        (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn)
    intro ρ hρ
    rw [Finset.mem_preimage] at hρ
    by_cases hlt : ‖(ρ : ℂ)‖ < 4
    · exfalso
      apply hρ
      rw [PrimeNumberTheorem.mem_nontrivialZerosFinset]
      exact ⟨ρ.2.1, (Complex.abs_im_le_norm _).trans hlt.le⟩
    · exact if_neg hlt
  · refine Summable.of_norm_bounded
      (g := fun ρ : UpperHalfPlaneNontrivialZero ↦
        22 * ((analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹ ^ 2))
      (summable_xiOrder_mul_norm_inv_sq_upperZeros.mul_left _) fun ρ => ?_
    by_cases h : ‖(ρ : ℂ)‖ < 4
    · rw [if_pos h, norm_zero]
      positivity
    · rw [if_neg h, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤
          (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * (22 * ‖(ρ : ℂ)‖⁻¹ ^ 2))]
      exact le_of_eq (by ring)

section DSeries

variable {r₁ : ℝ} (hr₁ : 0 < r₁) (hr₁1 : r₁ ≤ 1)
  (hρfar : ∀ ρ : UpperHalfPlaneNontrivialZero,
    r₁ ≤ ‖1 - (ρ : ℂ)‖ ∧ r₁ ≤ ‖1 - conj (ρ : ℂ)‖)

include hr₁ hr₁1 hρfar in
/-- 球内点到任一上半零点（及其共轭）的距离下界 `r₁/2`，且 `‖s‖ ≤ 3/2`。 -/
theorem dist_bound_of_mem_ball {s : ℂ} (hs : s ∈ Metric.ball (1 : ℂ) (r₁ / 2))
    (ρ : UpperHalfPlaneNontrivialZero) :
    r₁ / 2 ≤ ‖s - (ρ : ℂ)‖ ∧ r₁ / 2 ≤ ‖s - conj (ρ : ℂ)‖ ∧ ‖s‖ ≤ 3 / 2 := by
  have hsn1 : ‖s - 1‖ < r₁ / 2 := by
    have := Metric.mem_ball.mp hs
    rwa [dist_eq_norm] at this
  have hfar := hρfar ρ
  have hsub : ‖1 - s‖ = ‖s - 1‖ := norm_sub_rev _ _
  refine ⟨?_, ?_, ?_⟩
  · have htr : ‖1 - (ρ : ℂ)‖ ≤ ‖1 - s‖ + ‖s - (ρ : ℂ)‖ := by
      calc ‖1 - (ρ : ℂ)‖ = ‖(1 - s) + (s - (ρ : ℂ))‖ := by
            congr 1
            ring
        _ ≤ ‖1 - s‖ + ‖s - (ρ : ℂ)‖ := norm_add_le _ _
    rw [hsub] at htr
    linarith
  · have htr : ‖1 - conj (ρ : ℂ)‖ ≤ ‖1 - s‖ + ‖s - conj (ρ : ℂ)‖ := by
      calc ‖1 - conj (ρ : ℂ)‖ = ‖(1 - s) + (s - conj (ρ : ℂ))‖ := by
            congr 1
            ring
        _ ≤ ‖1 - s‖ + ‖s - conj (ρ : ℂ)‖ := norm_add_le _ _
    rw [hsub] at htr
    linarith
  · have hs1 : ‖s‖ = ‖(s - 1) + 1‖ := by
      congr 1
      ring
    have hs2 := norm_add_le (s - 1) (1 : ℂ)
    rw [norm_one] at hs2
    rw [hs1]
    linarith

include hr₁ hr₁1 hρfar in
/-- **M-判别主界**：`j ≥ 1`、`s ∈ ball 1 (r₁/2)` 时
`‖xiWeightedInvPowTerm j s ρ‖ ≤ xiWeightedInvPowBound r₁ j ρ`。 -/
theorem norm_xiWeightedInvPowTerm_le {j : ℕ} (hj : 1 ≤ j) {s : ℂ}
    (hs : s ∈ Metric.ball (1 : ℂ) (r₁ / 2)) (ρ : UpperHalfPlaneNontrivialZero) :
    ‖xiWeightedInvPowTerm j s (ρ : ℂ)‖ ≤ xiWeightedInvPowBound r₁ j ρ := by
  obtain ⟨hd1, hd2, hsn⟩ := dist_bound_of_mem_ball hr₁ hr₁1 hρfar hs ρ
  rw [xiWeightedInvPowTerm, norm_mul, RCLike.norm_natCast]
  by_cases hρ4 : ‖(ρ : ℂ)‖ < 4
  · -- 低段：两片各 ≤ (2/r₁)^j
    rw [xiWeightedInvPowBound, if_pos hρ4]
    have hb1 : ‖(s - (ρ : ℂ))⁻¹ ^ j‖ ≤ (2 / r₁) ^ j := by
      rw [norm_pow, norm_inv]
      have h1 : ‖s - (ρ : ℂ)‖⁻¹ ≤ 2 / r₁ := by
        have h2 : ‖s - (ρ : ℂ)‖⁻¹ ≤ (r₁ / 2)⁻¹ :=
          inv_anti₀ (by positivity) hd1
        rwa [inv_div] at h2
      exact pow_le_pow_left₀ (by positivity) h1 j
    have hb2 : ‖(s - conj (ρ : ℂ))⁻¹ ^ j‖ ≤ (2 / r₁) ^ j := by
      rw [norm_pow, norm_inv]
      have h1 : ‖s - conj (ρ : ℂ)‖⁻¹ ≤ 2 / r₁ := by
        have h2 : ‖s - conj (ρ : ℂ)‖⁻¹ ≤ (r₁ / 2)⁻¹ :=
          inv_anti₀ (by positivity) hd2
        rwa [inv_div] at h2
      exact pow_le_pow_left₀ (by positivity) h1 j
    calc (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) *
            ‖(s - (ρ : ℂ))⁻¹ ^ j + (s - conj (ρ : ℂ))⁻¹ ^ j‖
        ≤ (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) *
            (‖(s - (ρ : ℂ))⁻¹ ^ j‖ + ‖(s - conj (ρ : ℂ))⁻¹ ^ j‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (Nat.cast_nonneg _)
      _ ≤ (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) *
            ((2 / r₁) ^ j + (2 / r₁) ^ j) :=
          mul_le_mul_of_nonneg_left (add_le_add hb1 hb2) (Nat.cast_nonneg _)
      _ = (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * (2 * (2 / r₁) ^ j) := by ring
  · -- 高段
    rw [xiWeightedInvPowBound, if_neg hρ4]
    have hρ4' : 4 ≤ ‖(ρ : ℂ)‖ := le_of_not_gt hρ4
    have hρpos : 0 < ‖(ρ : ℂ)‖ := by linarith
    have hge1 : ‖(ρ : ℂ)‖ / 2 ≤ ‖s - (ρ : ℂ)‖ := by
      have h := norm_sub_norm_le (ρ : ℂ) s
      have hsr : ‖(ρ : ℂ) - s‖ = ‖s - (ρ : ℂ)‖ := norm_sub_rev _ _
      rw [hsr] at h
      have h1 : ‖(ρ : ℂ)‖ - ‖s‖ ≤ ‖s - (ρ : ℂ)‖ := h
      linarith
    have hge2 : ‖(ρ : ℂ)‖ / 2 ≤ ‖s - conj (ρ : ℂ)‖ := by
      have h := norm_sub_norm_le (conj (ρ : ℂ)) s
      have hsr : ‖conj (ρ : ℂ) - s‖ = ‖s - conj (ρ : ℂ)‖ := norm_sub_rev _ _
      rw [hsr, Complex.norm_conj] at h
      have h1 : ‖(ρ : ℂ)‖ - ‖s‖ ≤ ‖s - conj (ρ : ℂ)‖ := h
      linarith
    rcases Nat.lt_or_ge j 2 with hj1 | hj2
    · -- j = 1：配对恒等式
      have hj_eq : j = 1 := by omega
      subst hj_eq
      have h1 : s - (ρ : ℂ) ≠ 0 := sub_ne_zero.mpr fun h => by
        rw [h] at hd1
        simp at hd1
        linarith
      have h2 : s - conj (ρ : ℂ) ≠ 0 := sub_ne_zero.mpr fun h => by
        rw [h] at hd2
        simp at hd2
        linarith
      have hid : (s - (ρ : ℂ))⁻¹ ^ 1 + (s - conj (ρ : ℂ))⁻¹ ^ 1 =
          (2 * s - (2 * (ρ : ℂ).re : ℂ)) / ((s - (ρ : ℂ)) * (s - conj (ρ : ℂ))) := by
        rw [pow_one, pow_one]
        field_simp
        have hc : (ρ : ℂ) + conj (ρ : ℂ) = (2 * (ρ : ℂ).re : ℂ) := by
          rw [Complex.add_conj]
          push_cast
          ring
        linear_combination -hc
      have hnum : ‖2 * s - (2 * (ρ : ℂ).re : ℂ)‖ ≤ 5 := by
        have hre : |(ρ : ℂ).re| ≤ 1 := by
          have h3 := ρ.2.1.2.1
          have h4 := ρ.2.1.2.2
          rw [abs_le]
          constructor <;> linarith
        calc ‖2 * s - (2 * (ρ : ℂ).re : ℂ)‖
            ≤ ‖2 * s‖ + ‖(2 * (ρ : ℂ).re : ℂ)‖ := norm_sub_le _ _
          _ = 2 * ‖s‖ + 2 * |(ρ : ℂ).re| := by
            rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
            norm_num
          _ ≤ 2 * (3 / 2) + 2 * 1 := by linarith
          _ = 5 := by norm_num
      have hden : (‖(ρ : ℂ)‖ / 2) ^ 2 ≤ ‖s - (ρ : ℂ)‖ * ‖s - conj (ρ : ℂ)‖ := by
        rw [sq]
        exact mul_le_mul hge1 hge2 (by positivity) (by linarith)
      have hdenpos : 0 < ‖s - (ρ : ℂ)‖ * ‖s - conj (ρ : ℂ)‖ :=
        mul_pos (by linarith) (by linarith)
      have hmain : ‖(2 * s - (2 * (ρ : ℂ).re : ℂ)) /
            ((s - (ρ : ℂ)) * (s - conj (ρ : ℂ)))‖ ≤ 20 * ‖(ρ : ℂ)‖⁻¹ ^ 2 := by
        rw [norm_div, norm_mul]
        have hle1 : ‖2 * s - (2 * (ρ : ℂ).re : ℂ)‖ / (‖s - (ρ : ℂ)‖ * ‖s - conj (ρ : ℂ)‖)
            ≤ 5 / (‖s - (ρ : ℂ)‖ * ‖s - conj (ρ : ℂ)‖) :=
          div_le_div_of_nonneg_right hnum hdenpos.le
        have hle2 : (5 : ℝ) / (‖s - (ρ : ℂ)‖ * ‖s - conj (ρ : ℂ)‖) ≤
            5 / (‖(ρ : ℂ)‖ / 2) ^ 2 :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
        have heq : (5 : ℝ) / (‖(ρ : ℂ)‖ / 2) ^ 2 = 20 * ‖(ρ : ℂ)‖⁻¹ ^ 2 := by
          rw [div_pow, inv_pow]
          field_simp
          ring
        exact hle1.trans (hle2.trans_eq heq)
      have hmain' : ‖(s - (ρ : ℂ))⁻¹ ^ 1 + (s - conj (ρ : ℂ))⁻¹ ^ 1‖ ≤
          20 * ‖(ρ : ℂ)‖⁻¹ ^ 2 := by
        rw [hid]
        exact hmain
      exact mul_le_mul_of_nonneg_left hmain' (Nat.cast_nonneg _)
    · -- j ≥ 2：逐片估计
      have hb1 : ‖(s - (ρ : ℂ))⁻¹ ^ j‖ ≤ 4 * ‖(ρ : ℂ)‖⁻¹ ^ 2 := by
        rw [norm_pow, norm_inv]
        have h1 : ‖s - (ρ : ℂ)‖⁻¹ ≤ 2 / ‖(ρ : ℂ)‖ := by
          have h2 : ‖s - (ρ : ℂ)‖⁻¹ ≤ (‖(ρ : ℂ)‖ / 2)⁻¹ :=
            inv_anti₀ (by positivity) hge1
          rwa [inv_div] at h2
        have h3 : (‖s - (ρ : ℂ)‖⁻¹) ^ j ≤ (2 / ‖(ρ : ℂ)‖) ^ j :=
          pow_le_pow_left₀ (by positivity) h1 j
        have h4 : (2 / ‖(ρ : ℂ)‖) ^ j ≤ (2 / ‖(ρ : ℂ)‖) ^ 2 :=
          pow_le_pow_of_le_one (by positivity)
            ((div_le_one hρpos).mpr (by linarith)) hj2
        have h5 : (2 / ‖(ρ : ℂ)‖) ^ 2 = 4 * ‖(ρ : ℂ)‖⁻¹ ^ 2 := by
          rw [div_pow, inv_pow]
          field_simp
          ring
        exact h3.trans (h4.trans_eq h5)
      have hb2 : ‖(s - conj (ρ : ℂ))⁻¹ ^ j‖ ≤ 4 * ‖(ρ : ℂ)‖⁻¹ ^ 2 := by
        rw [norm_pow, norm_inv]
        have h1 : ‖s - conj (ρ : ℂ)‖⁻¹ ≤ 2 / ‖(ρ : ℂ)‖ := by
          have h2 : ‖s - conj (ρ : ℂ)‖⁻¹ ≤ (‖(ρ : ℂ)‖ / 2)⁻¹ :=
            inv_anti₀ (by positivity) hge2
          rwa [inv_div] at h2
        have h3 : (‖s - conj (ρ : ℂ)‖⁻¹) ^ j ≤ (2 / ‖(ρ : ℂ)‖) ^ j :=
          pow_le_pow_left₀ (by positivity) h1 j
        have h4 : (2 / ‖(ρ : ℂ)‖) ^ j ≤ (2 / ‖(ρ : ℂ)‖) ^ 2 :=
          pow_le_pow_of_le_one (by positivity)
            ((div_le_one hρpos).mpr (by linarith)) hj2
        have h5 : (2 / ‖(ρ : ℂ)‖) ^ 2 = 4 * ‖(ρ : ℂ)‖⁻¹ ^ 2 := by
          rw [div_pow, inv_pow]
          field_simp
          ring
        exact h3.trans (h4.trans_eq h5)
      have hle1 : (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) *
            ‖(s - (ρ : ℂ))⁻¹ ^ j + (s - conj (ρ : ℂ))⁻¹ ^ j‖ ≤
          (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) *
            (‖(s - (ρ : ℂ))⁻¹ ^ j‖ + ‖(s - conj (ρ : ℂ))⁻¹ ^ j‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (Nat.cast_nonneg _)
      have hle2 : (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) *
            (‖(s - (ρ : ℂ))⁻¹ ^ j‖ + ‖(s - conj (ρ : ℂ))⁻¹ ^ j‖) ≤
          (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) *
            (4 * ‖(ρ : ℂ)‖⁻¹ ^ 2 + 4 * ‖(ρ : ℂ)‖⁻¹ ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hb1 hb2) (Nat.cast_nonneg _)
      have hle3 : (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) *
            (4 * ‖(ρ : ℂ)‖⁻¹ ^ 2 + 4 * ‖(ρ : ℂ)‖⁻¹ ^ 2) ≤
          (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * (20 * ‖(ρ : ℂ)‖⁻¹ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        have hnn : 0 ≤ ‖(ρ : ℂ)‖⁻¹ ^ 2 := by positivity
        linarith
      exact hle1.trans (hle2.trans hle3)

include hr₁ hr₁1 hρfar in
/-- 每个逆幂配对项在球上复可微（分母在球内非零）。 -/
theorem differentiableOn_xiWeightedInvPowTerm (j : ℕ)
    (ρ : UpperHalfPlaneNontrivialZero) :
    DifferentiableOn ℂ (fun s => xiWeightedInvPowTerm j s (ρ : ℂ))
      (Metric.ball 1 (r₁ / 2)) := by
  intro s hs
  obtain ⟨hd1, hd2, _⟩ := dist_bound_of_mem_ball hr₁ hr₁1 hρfar hs ρ
  have h1 : s - (ρ : ℂ) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hd1
    linarith
  have h2 : s - conj (ρ : ℂ) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hd2
    linarith
  have hp1 : DifferentiableAt ℂ (fun w => (w - (ρ : ℂ))⁻¹ ^ j) s :=
    ((differentiableAt_id.sub_const _).inv h1).pow j
  have hp2 : DifferentiableAt ℂ (fun w => (w - conj (ρ : ℂ))⁻¹ ^ j) s :=
    ((differentiableAt_id.sub_const _).inv h2).pow j
  exact ((hp1.add hp2).const_mul _).differentiableWithinAt

include hr₁ hr₁1 hρfar in
/-- **`D_j` 在球上复可微**（Weierstrass M-判别逐项微分）。 -/
theorem differentiableOn_xiWeightedInvPowSum {j : ℕ} (hj : 1 ≤ j) :
    DifferentiableOn ℂ (fun s => xiWeightedInvPowSum j s) (Metric.ball 1 (r₁ / 2)) := by
  classical
  exact differentiableOn_tsum_of_summable_norm (u := xiWeightedInvPowBound r₁ j)
    (summable_xiWeightedInvPowBound hr₁ j)
    (fun ρ => differentiableOn_xiWeightedInvPowTerm hr₁ hr₁1 hρfar j ρ)
    Metric.isOpen_ball
    (fun ρ s hs => norm_xiWeightedInvPowTerm_le hr₁ hr₁1 hρfar hj hs ρ)

/-- 逆幂片的逐项导数：`d/ds [(s-c)⁻¹^j] = j·(s-c)⁻¹^(j-1)·(-(s-c)²)⁻¹`。 -/
theorem hasDerivAt_invPow_piece {s c : ℂ} (h : s - c ≠ 0) (j : ℕ) :
    HasDerivAt (fun w => (w - c)⁻¹ ^ j)
      ((j : ℂ) * ((s - c)⁻¹ ^ (j - 1)) * (-((s - c) ^ 2)⁻¹)) s := by
  have h1 : HasDerivAt (fun w : ℂ => w - c) 1 s := (hasDerivAt_id' s).sub_const c
  have h2 : HasDerivAt (fun w : ℂ => (w - c)⁻¹) (-((s - c) ^ 2)⁻¹) s := by
    have h2' := (hasDerivAt_inv h).comp s h1
    simpa using h2'
  exact h2.pow j

/-- 逆幂片导数的规范形：`= -j·(s-c)⁻¹^(j+1)`（`j ≥ 1`）。 -/
theorem invPow_piece_deriv_eq {s c : ℂ} (h : s - c ≠ 0) {j : ℕ} (hj : 1 ≤ j) :
    (j : ℂ) * ((s - c)⁻¹ ^ (j - 1)) * (-((s - c) ^ 2)⁻¹) =
      -((j : ℂ) * ((s - c)⁻¹ ^ (j + 1))) := by
  have hp : ((s - c)⁻¹) ^ (j - 1) * ((s - c)⁻¹) ^ 2 = ((s - c)⁻¹) ^ (j + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [← inv_pow (s - c) 2]
  calc (j : ℂ) * ((s - c)⁻¹ ^ (j - 1)) * (-(((s - c)⁻¹) ^ 2))
      = -((j : ℂ) * (((s - c)⁻¹) ^ (j - 1) * ((s - c)⁻¹) ^ 2)) := by ring
    _ = -((j : ℂ) * ((s - c)⁻¹) ^ (j + 1)) := by rw [hp]

include hr₁ hr₁1 hρfar in
/-- 逆幂配对项的逐项导数：`deriv (xiWeightedInvPowTerm j · ρ) s =
-j · xiWeightedInvPowTerm (j+1) s ρ`（`j ≥ 1`）。 -/
theorem hasDerivAt_xiWeightedInvPowTerm {j : ℕ} (hj : 1 ≤ j) {s : ℂ}
    (hs : s ∈ Metric.ball (1 : ℂ) (r₁ / 2)) (ρ : UpperHalfPlaneNontrivialZero) :
    HasDerivAt (fun w => xiWeightedInvPowTerm j w (ρ : ℂ))
      (-(j : ℂ) * xiWeightedInvPowTerm (j + 1) s (ρ : ℂ)) s := by
  obtain ⟨hd1, hd2, _⟩ := dist_bound_of_mem_ball hr₁ hr₁1 hρfar hs ρ
  have h1 : s - (ρ : ℂ) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hd1
    linarith
  have h2 : s - conj (ρ : ℂ) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hd2
    linarith
  have hp1 := hasDerivAt_invPow_piece h1 j
  have hp2 := hasDerivAt_invPow_piece h2 j
  have hsum := hp1.add hp2
  have hval := hsum.const_mul (analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ)
  have hv1 := invPow_piece_deriv_eq h1 hj
  have hv2 := invPow_piece_deriv_eq h2 hj
  rw [hv1, hv2] at hval
  refine hval.congr_deriv ?_
  show (analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) *
      (-((j : ℂ) * ((s - (ρ : ℂ))⁻¹) ^ (j + 1)) +
        -((j : ℂ) * ((s - conj (ρ : ℂ))⁻¹) ^ (j + 1))) =
    -(j : ℂ) * ((analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) *
      ((s - (ρ : ℂ))⁻¹ ^ (j + 1) + (s - conj (ρ : ℂ))⁻¹ ^ (j + 1)))
  ring

include hr₁ hr₁1 hρfar in
/-- **`D_j` 的导数恒等式**：球上 `deriv D_j = -j · D_{j+1}`（`j ≥ 1`）。
由 `hasSum_deriv_of_summable_norm`（Weierstrass–Cauchy）逐项微分。 -/
theorem deriv_xiWeightedInvPowSum_eqOn {j : ℕ} (hj : 1 ≤ j) :
    Set.EqOn (deriv fun s => xiWeightedInvPowSum j s)
      (fun s => -(j : ℂ) * xiWeightedInvPowSum (j + 1) s)
      (Metric.ball 1 (r₁ / 2)) := by
  classical
  intro s hs
  have hsu := hasSum_deriv_of_summable_norm (u := xiWeightedInvPowBound r₁ j)
    (summable_xiWeightedInvPowBound hr₁ j)
    (fun ρ => differentiableOn_xiWeightedInvPowTerm hr₁ hr₁1 hρfar j ρ)
    Metric.isOpen_ball
    (fun ρ w hw => norm_xiWeightedInvPowTerm_le hr₁ hr₁1 hρfar hj hw ρ) hs
  have hd : ∀ ρ : UpperHalfPlaneNontrivialZero,
      deriv (fun w => xiWeightedInvPowTerm j w (ρ : ℂ)) s =
        -(j : ℂ) * xiWeightedInvPowTerm (j + 1) s (ρ : ℂ) := fun ρ =>
    (hasDerivAt_xiWeightedInvPowTerm hr₁ hr₁1 hρfar hj hs ρ).deriv
  have hsu' : HasSum (fun ρ : UpperHalfPlaneNontrivialZero =>
        -(j : ℂ) * xiWeightedInvPowTerm (j + 1) s (ρ : ℂ))
      (deriv (fun s => xiWeightedInvPowSum j s) s) := hsu.congr_fun fun ρ => (hd ρ).symm
  have htsum := hsu'.tsum_eq
  rw [tsum_mul_left] at htsum
  exact htsum.symm

include hr₁ hr₁1 hρfar in
/-- **M-判别主界（W）**：`s ∈ ball 1 (r₁/2)` 时
`‖xiWeightedMittagLefflerTerm s ρ‖ ≤ xiWeightedMittagLefflerBound r₁ ρ`。 -/
theorem norm_xiWeightedMittagLefflerTerm_le {s : ℂ}
    (hs : s ∈ Metric.ball (1 : ℂ) (r₁ / 2)) (ρ : UpperHalfPlaneNontrivialZero) :
    ‖xiWeightedMittagLefflerTerm s (ρ : ℂ)‖ ≤ xiWeightedMittagLefflerBound r₁ ρ := by
  obtain ⟨hd1, hd2, _⟩ := dist_bound_of_mem_ball hr₁ hr₁1 hρfar hs ρ
  simp only [xiWeightedMittagLefflerTerm, xiPairedMittagLefflerTerm, one_div]
  rw [norm_mul, RCLike.norm_natCast]
  by_cases hρ4 : ‖(ρ : ℂ)‖ < 4
  · -- 低段：四片逐片估计
    rw [xiWeightedMittagLefflerBound, if_pos hρ4]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have hb1 : ‖(s - (ρ : ℂ))⁻¹‖ ≤ 2 / r₁ := by
      rw [norm_inv]
      have h2 : ‖s - (ρ : ℂ)‖⁻¹ ≤ (r₁ / 2)⁻¹ := inv_anti₀ (by positivity) hd1
      rwa [inv_div] at h2
    have hb2 : ‖(s - conj (ρ : ℂ))⁻¹‖ ≤ 2 / r₁ := by
      rw [norm_inv]
      have h2 : ‖s - conj (ρ : ℂ)‖⁻¹ ≤ (r₁ / 2)⁻¹ := inv_anti₀ (by positivity) hd2
      rwa [inv_div] at h2
    have hb3 : ‖(ρ : ℂ)⁻¹‖ = ‖(ρ : ℂ)‖⁻¹ := norm_inv (ρ : ℂ)
    have hb4 : ‖(conj (ρ : ℂ))⁻¹‖ = ‖(ρ : ℂ)‖⁻¹ := by rw [norm_inv, Complex.norm_conj]
    calc ‖((s - (ρ : ℂ))⁻¹ + (ρ : ℂ)⁻¹) + ((s - conj (ρ : ℂ))⁻¹ + (conj (ρ : ℂ))⁻¹)‖
        ≤ (‖(s - (ρ : ℂ))⁻¹‖ + ‖(ρ : ℂ)⁻¹‖) +
            (‖(s - conj (ρ : ℂ))⁻¹‖ + ‖(conj (ρ : ℂ))⁻¹‖) :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
      _ ≤ (2 / r₁ + ‖(ρ : ℂ)‖⁻¹) + (2 / r₁ + ‖(ρ : ℂ)‖⁻¹) := by
          rw [hb3, hb4]
          exact add_le_add (add_le_add hb1 le_rfl) (add_le_add hb2 le_rfl)
      _ = 4 / r₁ + 2 * ‖(ρ : ℂ)‖⁻¹ := by ring
  · -- 高段：重新配对 [(s-ρ)⁻¹ + (s-conjρ)⁻¹] + [ρ⁻¹ + conjρ⁻¹]
    rw [xiWeightedMittagLefflerBound, if_neg hρ4]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have hρ4' : 4 ≤ ‖(ρ : ℂ)‖ := le_of_not_gt hρ4
    have hρpos : 0 < ‖(ρ : ℂ)‖ := by linarith
    have hρne : (ρ : ℂ) ≠ 0 := norm_pos_iff.mp hρpos
    have hconjne : conj (ρ : ℂ) ≠ 0 := by
      intro h
      apply hρne
      rw [← norm_eq_zero, ← Complex.norm_conj, h, norm_zero]
    have hre : |(ρ : ℂ).re| ≤ 1 := by
      have h3 := ρ.2.1.2.1
      have h4 := ρ.2.1.2.2
      rw [abs_le]
      constructor <;> linarith
    -- 首对：复用 `j = 1` 的逆幂配对界
    have hpair1 : ‖(s - (ρ : ℂ))⁻¹ + (s - conj (ρ : ℂ))⁻¹‖ ≤
        20 * ‖(ρ : ℂ)‖⁻¹ ^ 2 := by
      have hW := norm_xiWeightedInvPowTerm_le hr₁ hr₁1 hρfar (j := 1) le_rfl hs ρ
      rw [xiWeightedInvPowBound, if_neg hρ4, xiWeightedInvPowTerm, norm_mul,
        RCLike.norm_natCast, pow_one, pow_one] at hW
      have hm : (0 : ℝ) < (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) := by
        have h1 := one_le_analyticOrderNatAt_xiFunction_of_isNontrivialZero ρ.2.1
        have h1' : (1 : ℝ) ≤ (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) := by
          exact_mod_cast h1
        linarith
      exact le_of_mul_le_mul_left hW hm
    -- 常数对：`ρ⁻¹ + conjρ⁻¹ = 2·re ρ/(ρ·conjρ)`，`|re ρ| ≤ 1`
    have hid2 : (ρ : ℂ)⁻¹ + (conj (ρ : ℂ))⁻¹ =
        (2 * (ρ : ℂ).re : ℂ) / ((ρ : ℂ) * conj (ρ : ℂ)) := by
      field_simp
      have hc : (ρ : ℂ) + conj (ρ : ℂ) = (2 * (ρ : ℂ).re : ℂ) := by
        rw [Complex.add_conj]
        push_cast
        ring
      linear_combination hc
    have hpair2 : ‖(ρ : ℂ)⁻¹ + (conj (ρ : ℂ))⁻¹‖ ≤ 2 * ‖(ρ : ℂ)‖⁻¹ ^ 2 := by
      rw [hid2, norm_div]
      have hnum : ‖(2 * (ρ : ℂ).re : ℂ)‖ = 2 * |(ρ : ℂ).re| := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        norm_num
      rw [hnum, norm_mul, Complex.norm_conj]
      have hle2 : 2 * |(ρ : ℂ).re| / (‖(ρ : ℂ)‖ * ‖(ρ : ℂ)‖) ≤
          2 / (‖(ρ : ℂ)‖ * ‖(ρ : ℂ)‖) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      refine hle2.trans_eq ?_
      rw [show ‖(ρ : ℂ)‖ * ‖(ρ : ℂ)‖ = ‖(ρ : ℂ)‖ ^ 2 from (sq _).symm, inv_pow,
        div_eq_mul_inv]
    have hreg : ((s - (ρ : ℂ))⁻¹ + (ρ : ℂ)⁻¹) + ((s - conj (ρ : ℂ))⁻¹ + (conj (ρ : ℂ))⁻¹) =
        ((s - (ρ : ℂ))⁻¹ + (s - conj (ρ : ℂ))⁻¹) + ((ρ : ℂ)⁻¹ + (conj (ρ : ℂ))⁻¹) := by
      ring
    rw [hreg]
    calc ‖((s - (ρ : ℂ))⁻¹ + (s - conj (ρ : ℂ))⁻¹) + ((ρ : ℂ)⁻¹ + (conj (ρ : ℂ))⁻¹)‖
        ≤ ‖(s - (ρ : ℂ))⁻¹ + (s - conj (ρ : ℂ))⁻¹‖ +
            ‖(ρ : ℂ)⁻¹ + (conj (ρ : ℂ))⁻¹‖ := norm_add_le _ _
      _ ≤ 20 * ‖(ρ : ℂ)‖⁻¹ ^ 2 + 2 * ‖(ρ : ℂ)‖⁻¹ ^ 2 := add_le_add hpair1 hpair2
      _ = 22 * ‖(ρ : ℂ)‖⁻¹ ^ 2 := by ring

include hr₁ hr₁1 hρfar in
/-- 每个 Mittag-Leffler 配对项在球上复可微（分母在球内非零）。 -/
theorem differentiableOn_xiWeightedMittagLefflerTerm (ρ : UpperHalfPlaneNontrivialZero) :
    DifferentiableOn ℂ (fun s => xiWeightedMittagLefflerTerm s (ρ : ℂ))
      (Metric.ball 1 (r₁ / 2)) := by
  intro s hs
  simp only [xiWeightedMittagLefflerTerm, xiPairedMittagLefflerTerm, one_div]
  obtain ⟨hd1, hd2, _⟩ := dist_bound_of_mem_ball hr₁ hr₁1 hρfar hs ρ
  have h1 : s - (ρ : ℂ) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hd1
    linarith
  have h2 : s - conj (ρ : ℂ) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hd2
    linarith
  have hp1 : DifferentiableAt ℂ (fun w => (w - (ρ : ℂ))⁻¹) s :=
    (differentiableAt_id.sub_const _).inv h1
  have hp2 : DifferentiableAt ℂ (fun w => (w - conj (ρ : ℂ))⁻¹) s :=
    (differentiableAt_id.sub_const _).inv h2
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.const_mul
  apply DifferentiableAt.add
  · apply DifferentiableAt.add
    · exact hp1
    · exact differentiableAt_const _
  · apply DifferentiableAt.add
    · exact hp2
    · exact differentiableAt_const _

include hr₁ hr₁1 hρfar in
/-- **`W` 在球上复可微**（Weierstrass M-判别逐项微分）。 -/
theorem differentiableOn_xiWeightedMittagLefflerSum :
    DifferentiableOn ℂ (fun s => xiWeightedMittagLefflerSum s)
      (Metric.ball 1 (r₁ / 2)) := by
  classical
  exact differentiableOn_tsum_of_summable_norm (u := xiWeightedMittagLefflerBound r₁)
    (summable_xiWeightedMittagLefflerBound hr₁)
    (fun ρ => differentiableOn_xiWeightedMittagLefflerTerm hr₁ hr₁1 hρfar ρ)
    Metric.isOpen_ball
    (fun ρ s hs => norm_xiWeightedMittagLefflerTerm_le hr₁ hr₁1 hρfar hs ρ)

include hr₁ hr₁1 hρfar in
/-- Mittag-Leffler 配对项的逐项导数：`deriv (xiWeightedMittagLefflerTerm · ρ) s =
-xiWeightedInvPowTerm 2 s ρ`（常数片导数为零）。 -/
theorem hasDerivAt_xiWeightedMittagLefflerTerm {s : ℂ}
    (hs : s ∈ Metric.ball (1 : ℂ) (r₁ / 2)) (ρ : UpperHalfPlaneNontrivialZero) :
    HasDerivAt (fun w => xiWeightedMittagLefflerTerm w (ρ : ℂ))
      (-xiWeightedInvPowTerm 2 s (ρ : ℂ)) s := by
  simp only [xiWeightedMittagLefflerTerm, xiPairedMittagLefflerTerm, one_div]
  obtain ⟨hd1, hd2, _⟩ := dist_bound_of_mem_ball hr₁ hr₁1 hρfar hs ρ
  have h1 : s - (ρ : ℂ) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hd1
    linarith
  have h2 : s - conj (ρ : ℂ) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hd2
    linarith
  have hp1 : HasDerivAt (fun w : ℂ => (w - (ρ : ℂ))⁻¹) (-((s - (ρ : ℂ)) ^ 2)⁻¹) s := by
    simpa using hasDerivAt_invPow_piece h1 1
  have hp2 : HasDerivAt (fun w : ℂ => (w - conj (ρ : ℂ))⁻¹)
      (-((s - conj (ρ : ℂ)) ^ 2)⁻¹) s := by
    simpa using hasDerivAt_invPow_piece h2 1
  have hsum : HasDerivAt
      (fun w => (analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) *
        ((w - (ρ : ℂ))⁻¹ + (ρ : ℂ)⁻¹ + ((w - conj (ρ : ℂ))⁻¹ + (conj (ρ : ℂ))⁻¹)))
      ((analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) *
        ((-((s - (ρ : ℂ)) ^ 2)⁻¹ + 0) + (-((s - conj (ρ : ℂ)) ^ 2)⁻¹ + 0))) s := by
    apply HasDerivAt.const_mul
    apply HasDerivAt.add
    · apply HasDerivAt.add
      · exact hp1
      · exact hasDerivAt_const s _
    · apply HasDerivAt.add
      · exact hp2
      · exact hasDerivAt_const s _
  refine hsum.congr_deriv ?_
  show (analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) *
      ((-((s - (ρ : ℂ)) ^ 2)⁻¹ + 0) + (-((s - conj (ρ : ℂ)) ^ 2)⁻¹ + 0)) =
    -((analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) *
      ((s - (ρ : ℂ))⁻¹ ^ 2 + (s - conj (ρ : ℂ))⁻¹ ^ 2))
  rw [← inv_pow (s - (ρ : ℂ)) 2, ← inv_pow (s - conj (ρ : ℂ)) 2]
  ring

include hr₁ hr₁1 hρfar in
/-- **`W` 的导数恒等式**：球上 `deriv W = -D_2`
（Weierstrass–Cauchy 逐项微分）。 -/
theorem deriv_xiWeightedMittagLefflerSum_eqOn :
    Set.EqOn (deriv fun s => xiWeightedMittagLefflerSum s)
      (fun s => -xiWeightedInvPowSum 2 s) (Metric.ball 1 (r₁ / 2)) := by
  classical
  intro s hs
  have hsu := hasSum_deriv_of_summable_norm (u := xiWeightedMittagLefflerBound r₁)
    (summable_xiWeightedMittagLefflerBound hr₁)
    (fun ρ => differentiableOn_xiWeightedMittagLefflerTerm hr₁ hr₁1 hρfar ρ)
    Metric.isOpen_ball
    (fun ρ w hw => norm_xiWeightedMittagLefflerTerm_le hr₁ hr₁1 hρfar hw ρ) hs
  have hd : ∀ ρ : UpperHalfPlaneNontrivialZero,
      deriv (fun w => xiWeightedMittagLefflerTerm w (ρ : ℂ)) s =
        -xiWeightedInvPowTerm 2 s (ρ : ℂ) := fun ρ =>
    (hasDerivAt_xiWeightedMittagLefflerTerm hr₁ hr₁1 hρfar hs ρ).deriv
  have hsu' : HasSum (fun ρ : UpperHalfPlaneNontrivialZero =>
        -xiWeightedInvPowTerm 2 s (ρ : ℂ))
      (deriv (fun s => xiWeightedMittagLefflerSum s) s) :=
    hsu.congr_fun fun ρ => (hd ρ).symm
  have htsum := hsu'.tsum_eq
  rw [tsum_neg] at htsum
  exact htsum.symm

include hr₁ hr₁1 hρfar in
/-- **D-族高阶导数（带常数因子）**：球上
`iteratedDeriv k (c·D_j) = c·(-1)^k·(j+k-1)↓_k·D_{j+k}`（`j ≥ 1`），
其中 `(j+k-1)↓_k = Nat.descFactorial (j+k-1) k = j(j+1)⋯(j+k-1)`。
归纳步：`iteratedDeriv_succ'`（此版为 `iteratedDeriv (n+1) f =
iteratedDeriv n (deriv f)`）+ `deriv_const_mul` + D-求导规则。 -/
theorem iteratedDeriv_const_mul_xiWeightedInvPowSum_eqOn (k : ℕ) (c : ℂ) {j : ℕ}
    (hj : 1 ≤ j) :
    Set.EqOn (iteratedDeriv k fun s => c * xiWeightedInvPowSum j s)
      (fun s => c * ((-1 : ℂ) ^ k * (Nat.descFactorial (j + k - 1) k : ℂ) *
        xiWeightedInvPowSum (j + k) s))
      (Metric.ball 1 (r₁ / 2)) := by
  induction k generalizing c j with
  | zero =>
      intro s hs
      simp [iteratedDeriv_zero, Nat.descFactorial_zero]
  | succ k ih =>
      intro s hs
      rw [iteratedDeriv_succ']
      have hdon : DifferentiableOn ℂ (fun s => xiWeightedInvPowSum j s)
          (Metric.ball 1 (r₁ / 2)) :=
        differentiableOn_xiWeightedInvPowSum hr₁ hr₁1 hρfar hj
      have hEv : (deriv fun s => c * xiWeightedInvPowSum j s) =ᶠ[𝓝 s]
          (fun s => (c * -(j : ℂ)) * xiWeightedInvPowSum (j + 1) s) := by
        apply Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hs)
        intro w hw
        rw [deriv_const_mul _ (hdon.differentiableAt (Metric.isOpen_ball.mem_nhds hw)),
          deriv_xiWeightedInvPowSum_eqOn hr₁ hr₁1 hρfar hj hw]
        ring
      have hj1 : 1 ≤ j + 1 := by omega
      rw [hEv.iteratedDeriv_eq k]
      have hIH := ih (c * -(j : ℂ)) (j := j + 1) hj1 hs
      rw [hIH]
      have h1 : j + 1 + k - 1 = j + k := by omega
      have h2 : j + (k + 1) - 1 = j + k := by omega
      have h3 : j + 1 + k = j + (k + 1) := by omega
      rw [h1, h2, h3]
      have h4 : Nat.descFactorial (j + k) (k + 1) = j * Nat.descFactorial (j + k) k := by
        rw [Nat.descFactorial_succ, show j + k - k = j from by omega]
      rw [h4, pow_succ' (-1 : ℂ) k]
      push_cast
      ring

include hr₁ hr₁1 hρfar in
/-- **`W` 的高阶导数公式**：球上
`iteratedDeriv (k+1) W = (-1)^(k+1)·(k+1)!·D_{k+2}`。
由 `iteratedDeriv_succ'`、`deriv W = -D_2` 与 D-族公式
（`descFactorial (k+1) k = (k+1)!`）合并。 -/
theorem iteratedDeriv_xiWeightedMittagLefflerSum_eqOn (k : ℕ) :
    Set.EqOn (iteratedDeriv (k + 1) fun s => xiWeightedMittagLefflerSum s)
      (fun s => (-1 : ℂ) ^ (k + 1) * (Nat.factorial (k + 1) : ℂ) *
        xiWeightedInvPowSum (k + 2) s)
      (Metric.ball 1 (r₁ / 2)) := by
  intro s hs
  rw [iteratedDeriv_succ']
  have hEq : Set.EqOn (deriv fun s => xiWeightedMittagLefflerSum s)
      (fun s => (-1 : ℂ) * xiWeightedInvPowSum 2 s) (Metric.ball 1 (r₁ / 2)) := by
    intro w hw
    rw [deriv_xiWeightedMittagLefflerSum_eqOn hr₁ hr₁1 hρfar hw]
    ring
  have hEv := Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hs) hEq
  rw [hEv.iteratedDeriv_eq k]
  have h2le : (1 : ℕ) ≤ 2 := by norm_num
  have hD := iteratedDeriv_const_mul_xiWeightedInvPowSum_eqOn hr₁ hr₁1 hρfar k
    (-1 : ℂ) (j := 2) h2le hs
  rw [hD]
  have hfact : Nat.descFactorial (k + 1) k = Nat.factorial (k + 1) := by
    rw [Nat.descFactorial_eq_div (by omega), show k + 1 - k = 1 from by omega,
      Nat.factorial_one, Nat.div_one]
  have h5 : 2 + k - 1 = k + 1 := by omega
  have h6 : 2 + k = k + 2 := by omega
  rw [h5, h6, hfact, pow_succ' (-1 : ℂ) k]
  push_cast
  ring

end DSeries

/-! ## Part 5a：`ρ ↦ 1 - conj ρ` 对合、留数级数 `R_m`、`ξ'(1) = -ξ'(0)` -/

/-- **`1 - conj` 保非平凡零点**（经 ξ 的函数方程与共轭对称，绕开 ζ 的
函数方程）：`ξ(1 - conj u) = conj (ξ (1 - u)) = conj (ξ u) = 0`，
实部 `re(1 - conj u) = 1 - re u ∈ (0,1)`。 -/
theorem isNontrivialZero_one_sub_conj {u : ℂ} (h : RiemannHypothesis.IsNontrivialZero u) :
    RiemannHypothesis.IsNontrivialZero (1 - conj u) := by
  have hξ : xiFunction u = 0 := (xiFunction_eq_zero_iff h.2.1 h.2.2).mpr h.1
  have hre0 : 0 < (1 - conj u).re := by
    rw [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith [h.2.2]
  have hre1 : (1 - conj u).re < 1 := by
    rw [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith [h.2.1]
  refine (xiFunction_eq_zero_iff_isNontrivialZero hre0 hre1).mp ?_
  have hid : (1 : ℂ) - conj u = conj (1 - u) := by
    rw [map_sub, map_one]
  have hξ1 : xiFunction (1 - u) = 0 := by
    rw [← xiFunction_one_sub u]
    exact hξ
  rw [hid, xiFunction_conj, hξ1]
  exact map_zero _

/-- **对合等价**：`ρ ↦ 1 - conj ρ` 是上半平面非平凡零点的对合
（函数方程 `ξ(s) = ξ(1-s)` 与共轭对称的复合；`im(1 - conj ρ) = im ρ > 0`）。 -/
def uhzOneSubConjEquiv :
    UpperHalfPlaneNontrivialZero ≃ UpperHalfPlaneNontrivialZero where
  toFun ρ := ⟨1 - conj (ρ : ℂ), isNontrivialZero_one_sub_conj ρ.2.1, by
    rw [Complex.sub_im, Complex.one_im, Complex.conj_im]
    linarith [ρ.2.2]⟩
  invFun ρ := ⟨1 - conj (ρ : ℂ), isNontrivialZero_one_sub_conj ρ.2.1, by
    rw [Complex.sub_im, Complex.one_im, Complex.conj_im]
    linarith [ρ.2.2]⟩
  left_inv ρ := by
    apply Subtype.ext
    show (1 : ℂ) - conj (1 - conj (ρ : ℂ)) = ρ
    rw [map_sub, map_one, Complex.conj_conj, sub_sub_self]
  right_inv ρ := by
    apply Subtype.ext
    show (1 : ℂ) - conj (1 - conj (ρ : ℂ)) = ρ
    rw [map_sub, map_one, Complex.conj_conj, sub_sub_self]

/-- **留数配对项**：`m_ξ(ρ)·(ρ⁻¹^m + conjρ⁻¹^m)`。 -/
noncomputable def xiWeightedInvResidTerm (m : ℕ) (ρ : ℂ) : ℂ :=
  (analyticOrderNatAt xiFunction ρ : ℂ) * (ρ⁻¹ ^ m + (conj ρ)⁻¹ ^ m)

/-- **留数级数** `R_m = Σ_ρ m_ξ(ρ)·(ρ⁻¹^m + conjρ⁻¹^m)`。 -/
noncomputable def xiWeightedInvResidSum (m : ℕ) : ℂ :=
  ∑' ρ : UpperHalfPlaneNontrivialZero, xiWeightedInvResidTerm m (ρ : ℂ)

/-- **`R_m` 绝对收敛**（`m ≥ 1`）：`‖ρ‖ < 2` 段有限支撑
（`nontrivialZerosFinset 4` 原像之外恒零）；`‖ρ‖ ≥ 2` 段，当 `m = 1` 时用
配对恒等式 `ρ⁻¹ + conjρ⁻¹ = 2·re ρ/(ρ·conjρ)` 与 `|re ρ| ≤ 1` 得
`≤ 2‖ρ‖⁻²`，当 `m ≥ 2` 时逐片 `‖ρ‖⁻ᵐ ≤ ‖ρ‖⁻²`；统一界
`2·m_ξ(ρ)·‖ρ‖⁻²` 可和（`summable_xiOrder_mul_norm_inv_sq_upperZeros`）。 -/
theorem summable_xiWeightedInvResidTerm {m : ℕ} (hm : 1 ≤ m) :
    Summable fun ρ : UpperHalfPlaneNontrivialZero => xiWeightedInvResidTerm m (ρ : ℂ) := by
  classical
  have hsplit : (fun ρ : UpperHalfPlaneNontrivialZero ↦ xiWeightedInvResidTerm m (ρ : ℂ)) =
      (fun ρ : UpperHalfPlaneNontrivialZero ↦
          if ‖(ρ : ℂ)‖ < 2 then xiWeightedInvResidTerm m (ρ : ℂ) else 0) +
        (fun ρ : UpperHalfPlaneNontrivialZero ↦
          if 2 ≤ ‖(ρ : ℂ)‖ then xiWeightedInvResidTerm m (ρ : ℂ) else 0) := by
    funext ρ
    simp only [Pi.add_apply]
    by_cases h : ‖(ρ : ℂ)‖ < 2
    · rw [if_pos h, if_neg (by linarith), add_zero]
    · rw [if_neg h, if_pos (le_of_not_gt h), zero_add]
  rw [hsplit]
  refine Summable.add ?_ ?_
  · apply summable_of_ne_finset_zero
      (s := (PrimeNumberTheorem.nontrivialZerosFinset 4).preimage
        (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn)
    intro ρ hρ
    rw [Finset.mem_preimage] at hρ
    by_cases hlt : ‖(ρ : ℂ)‖ < 2
    · exfalso
      apply hρ
      rw [PrimeNumberTheorem.mem_nontrivialZerosFinset]
      exact ⟨ρ.2.1, ((Complex.abs_im_le_norm _).trans hlt.le).trans (by norm_num)⟩
    · exact if_neg hlt
  · refine Summable.of_norm_bounded
      (g := fun ρ : UpperHalfPlaneNontrivialZero ↦
        2 * ((analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹ ^ 2))
      (summable_xiOrder_mul_norm_inv_sq_upperZeros.mul_left _) fun ρ => ?_
    by_cases h : 2 ≤ ‖(ρ : ℂ)‖
    · rw [if_pos h]
      have hρpos : 0 < ‖(ρ : ℂ)‖ := by linarith
      have hρne : (ρ : ℂ) ≠ 0 := norm_pos_iff.mp hρpos
      have hconjne : conj (ρ : ℂ) ≠ 0 := by
        intro hc
        apply hρne
        rw [← norm_eq_zero, ← Complex.norm_conj, hc, norm_zero]
      have hre : |(ρ : ℂ).re| ≤ 1 := by
        have h1 := ρ.2.1.2.1
        have h2 := ρ.2.1.2.2
        rw [abs_le]
        constructor <;> linarith
      rw [xiWeightedInvResidTerm, norm_mul, RCLike.norm_natCast]
      rcases Nat.lt_or_ge m 2 with hm2 | hm2
      · -- m = 1：配对恒等式
        have hm1 : m = 1 := by omega
        subst hm1
        have hid : (ρ : ℂ)⁻¹ ^ 1 + (conj (ρ : ℂ))⁻¹ ^ 1 =
            (2 * (ρ : ℂ).re : ℂ) / ((ρ : ℂ) * conj (ρ : ℂ)) := by
          rw [pow_one, pow_one]
          field_simp
          have hc : (ρ : ℂ) + conj (ρ : ℂ) = (2 * (ρ : ℂ).re : ℂ) := by
            rw [Complex.add_conj]
            push_cast
            ring
          linear_combination hc
        have hpair : ‖(ρ : ℂ)⁻¹ ^ 1 + (conj (ρ : ℂ))⁻¹ ^ 1‖ ≤
            2 * ‖(ρ : ℂ)‖⁻¹ ^ 2 := by
          rw [hid, norm_div]
          have hnum : ‖(2 * (ρ : ℂ).re : ℂ)‖ = 2 * |(ρ : ℂ).re| := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            norm_num
          rw [hnum, norm_mul, Complex.norm_conj]
          have hle2 : 2 * |(ρ : ℂ).re| / (‖(ρ : ℂ)‖ * ‖(ρ : ℂ)‖) ≤
              2 / (‖(ρ : ℂ)‖ * ‖(ρ : ℂ)‖) :=
            div_le_div_of_nonneg_right (by linarith) (by positivity)
          refine hle2.trans_eq ?_
          rw [show ‖(ρ : ℂ)‖ * ‖(ρ : ℂ)‖ = ‖(ρ : ℂ)‖ ^ 2 from (sq _).symm, inv_pow,
            div_eq_mul_inv]
        calc (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) *
              ‖(ρ : ℂ)⁻¹ ^ 1 + (conj (ρ : ℂ))⁻¹ ^ 1‖
            ≤ (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * (2 * ‖(ρ : ℂ)‖⁻¹ ^ 2) :=
              mul_le_mul_of_nonneg_left hpair (Nat.cast_nonneg _)
          _ = 2 * ((analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹ ^ 2) := by
              ring
      · -- m ≥ 2：逐片估计
        have hb1 : ‖(ρ : ℂ)⁻¹ ^ m‖ ≤ ‖(ρ : ℂ)‖⁻¹ ^ 2 := by
          rw [norm_pow, norm_inv]
          exact pow_le_pow_of_le_one (by positivity)
            (inv_le_one_of_one_le₀ (by linarith)) hm2
        have hb2 : ‖(conj (ρ : ℂ))⁻¹ ^ m‖ ≤ ‖(ρ : ℂ)‖⁻¹ ^ 2 := by
          rw [norm_pow, norm_inv, Complex.norm_conj]
          exact pow_le_pow_of_le_one (by positivity)
            (inv_le_one_of_one_le₀ (by linarith)) hm2
        calc (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) *
              ‖(ρ : ℂ)⁻¹ ^ m + (conj (ρ : ℂ))⁻¹ ^ m‖
            ≤ (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) *
                (‖(ρ : ℂ)⁻¹ ^ m‖ + ‖(conj (ρ : ℂ))⁻¹ ^ m‖) :=
              mul_le_mul_of_nonneg_left (norm_add_le _ _) (Nat.cast_nonneg _)
          _ ≤ (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) *
                (‖(ρ : ℂ)‖⁻¹ ^ 2 + ‖(ρ : ℂ)‖⁻¹ ^ 2) :=
              mul_le_mul_of_nonneg_left (add_le_add hb1 hb2) (Nat.cast_nonneg _)
          _ = 2 * ((analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹ ^ 2) := by
              ring
    · rw [if_neg h, norm_zero]
      positivity

/-- **`ξ'(1) = -ξ'(0)`**：函数方程 `ξ(s) = ξ(1-s)` 在 `s = 1` 处求导
（链式法则，内函数 `s ↦ 1 - s` 的导数为 `-1`）。 -/
theorem deriv_xiFunction_one_eq_neg : deriv xiFunction 1 = -deriv xiFunction 0 := by
  have hfun : xiFunction = fun s : ℂ => xiFunction (1 - s) := funext xiFunction_one_sub
  have h1 : HasDerivAt (fun s : ℂ => 1 - s) (-1) 1 := by
    have h := (hasDerivAt_const 1 (1 : ℂ)).sub (hasDerivAt_id' 1)
    simpa using h
  have hξ : HasDerivAt xiFunction (deriv xiFunction 0) (1 - 1) := by
    rw [sub_self]
    exact (differentiable_xiFunction 0).hasDerivAt
  have h2 := hξ.comp 1 h1
  have h4 : deriv xiFunction 1 = deriv (xiFunction ∘ (fun s : ℂ => 1 - s)) 1 := by
    congr 1
  have h5 : deriv (xiFunction ∘ (fun s : ℂ => 1 - s)) 1 = -deriv xiFunction 0 := by
    have hd := h2.deriv
    rw [mul_neg_one] at hd
    exact hd
  exact h4.trans h5

/-! ## Part 5b：`D_m(1) = R_m`（`m ≥ 2`，对合换序） -/

/-- **统一高段界引理**：`m ≥ 2`、高段 `‖c ρ‖ ≥ ‖ρ‖/2` 时
`Σ_ρ m_ξ(ρ)·(c ρ)⁻¹^m` 收敛（低段有限支撑；高段逐片
`‖(c ρ)⁻¹^m‖ ≤ (2/‖ρ‖)^m ≤ (2/‖ρ‖)² = 4‖ρ‖⁻²`）。 -/
private theorem summable_weighted_inv_pow_of_norm_ge {m : ℕ} (hm : 2 ≤ m)
    (c : UpperHalfPlaneNontrivialZero → ℂ)
    (hc : ∀ ρ : UpperHalfPlaneNontrivialZero,
      2 ≤ ‖(ρ : ℂ)‖ → ‖(ρ : ℂ)‖ / 2 ≤ ‖c ρ‖) :
    Summable fun ρ : UpperHalfPlaneNontrivialZero =>
      (analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) * (c ρ)⁻¹ ^ m := by
  classical
  have hsplit : (fun ρ : UpperHalfPlaneNontrivialZero ↦
        (analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) * (c ρ)⁻¹ ^ m) =
      (fun ρ : UpperHalfPlaneNontrivialZero ↦
          if ‖(ρ : ℂ)‖ < 2 then
            (analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) * (c ρ)⁻¹ ^ m
          else 0) +
        (fun ρ : UpperHalfPlaneNontrivialZero ↦
          if 2 ≤ ‖(ρ : ℂ)‖ then
            (analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) * (c ρ)⁻¹ ^ m
          else 0) := by
    funext ρ
    simp only [Pi.add_apply]
    by_cases h : ‖(ρ : ℂ)‖ < 2
    · rw [if_pos h, if_neg (by linarith), add_zero]
    · rw [if_neg h, if_pos (le_of_not_gt h), zero_add]
  rw [hsplit]
  refine Summable.add ?_ ?_
  · apply summable_of_ne_finset_zero
      (s := (PrimeNumberTheorem.nontrivialZerosFinset 4).preimage
        (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn)
    intro ρ hρ
    rw [Finset.mem_preimage] at hρ
    by_cases hlt : ‖(ρ : ℂ)‖ < 2
    · exfalso
      apply hρ
      rw [PrimeNumberTheorem.mem_nontrivialZerosFinset]
      exact ⟨ρ.2.1, ((Complex.abs_im_le_norm _).trans hlt.le).trans (by norm_num)⟩
    · exact if_neg hlt
  · refine Summable.of_norm_bounded
      (g := fun ρ : UpperHalfPlaneNontrivialZero ↦
        4 * ((analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹ ^ 2))
      (summable_xiOrder_mul_norm_inv_sq_upperZeros.mul_left _) fun ρ => ?_
    by_cases h : 2 ≤ ‖(ρ : ℂ)‖
    · rw [if_pos h, norm_mul, RCLike.norm_natCast]
      have hρpos : 0 < ‖(ρ : ℂ)‖ := by linarith
      have hge := hc ρ h
      have hbound : ‖(c ρ)⁻¹ ^ m‖ ≤ 4 * ‖(ρ : ℂ)‖⁻¹ ^ 2 := by
        rw [norm_pow, norm_inv]
        have h1 : ‖c ρ‖⁻¹ ≤ 2 / ‖(ρ : ℂ)‖ := by
          have h2 : ‖c ρ‖⁻¹ ≤ (‖(ρ : ℂ)‖ / 2)⁻¹ :=
            inv_anti₀ (show (0 : ℝ) < ‖(ρ : ℂ)‖ / 2 by linarith) hge
          rwa [inv_div] at h2
        have h3 : ‖c ρ‖⁻¹ ^ m ≤ (2 / ‖(ρ : ℂ)‖) ^ m :=
          pow_le_pow_left₀ (by positivity) h1 m
        have h4 : (2 / ‖(ρ : ℂ)‖) ^ m ≤ (2 / ‖(ρ : ℂ)‖) ^ 2 :=
          pow_le_pow_of_le_one (by positivity) ((div_le_one hρpos).mpr h) hm
        have h5 : (2 / ‖(ρ : ℂ)‖) ^ 2 = 4 * ‖(ρ : ℂ)‖⁻¹ ^ 2 := by
          rw [div_pow, inv_pow]
          field_simp
          ring
        exact h3.trans (h4.trans_eq h5)
      calc (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * ‖(c ρ)⁻¹ ^ m‖
          ≤ (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * (4 * ‖(ρ : ℂ)‖⁻¹ ^ 2) :=
            mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _)
        _ = 4 * ((analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹ ^ 2) := by
            ring
    · rw [if_neg h, norm_zero]
      positivity

/-- **`D_m(1) = R_m`**（`m ≥ 2`）：`D_m(1)` 的两片
`(1-ρ)⁻¹ᵐ`、`(1-conjρ)⁻¹ᵐ` 经对合 `τ(ρ) = 1 - conj ρ` 分别换序为
`conjρ⁻¹ᵐ`、`ρ⁻¹ᵐ`（`τ` 保解析重数，
`analyticOrderNatAt_xiFunction_one_sub_conj`），合并即 `R_m`。 -/
theorem xiWeightedInvPowSum_one_eq_invResidSum {m : ℕ} (hm : 2 ≤ m) :
    xiWeightedInvPowSum m 1 = xiWeightedInvResidSum m := by
  classical
  have hA : Summable fun ρ : UpperHalfPlaneNontrivialZero =>
      (analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) * (1 - (ρ : ℂ))⁻¹ ^ m :=
    summable_weighted_inv_pow_of_norm_ge hm (fun ρ => 1 - (ρ : ℂ)) fun ρ h => by
      show ‖(ρ : ℂ)‖ / 2 ≤ ‖1 - (ρ : ℂ)‖
      have h1 := norm_sub_norm_le (ρ : ℂ) (1 : ℂ)
      rw [norm_one] at h1
      have h2 : ‖(ρ : ℂ) - 1‖ = ‖1 - (ρ : ℂ)‖ := norm_sub_rev _ _
      rw [h2] at h1
      linarith
  have hB : Summable fun ρ : UpperHalfPlaneNontrivialZero =>
      (analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) * (1 - conj (ρ : ℂ))⁻¹ ^ m :=
    summable_weighted_inv_pow_of_norm_ge hm (fun ρ => 1 - conj (ρ : ℂ)) fun ρ h => by
      show ‖(ρ : ℂ)‖ / 2 ≤ ‖1 - conj (ρ : ℂ)‖
      have h1 := norm_sub_norm_le (conj (ρ : ℂ)) (1 : ℂ)
      rw [norm_one, Complex.norm_conj] at h1
      have h2 : ‖conj (ρ : ℂ) - 1‖ = ‖1 - conj (ρ : ℂ)‖ := norm_sub_rev _ _
      rw [h2] at h1
      linarith
  have hmτ : ∀ ρ : UpperHalfPlaneNontrivialZero,
      analyticOrderNatAt xiFunction ↑(uhzOneSubConjEquiv ρ) =
        analyticOrderNatAt xiFunction (ρ : ℂ) := fun ρ =>
    analyticOrderNatAt_xiFunction_one_sub_conj (ρ : ℂ)
  have hstepB : ∀ ρ : UpperHalfPlaneNontrivialZero,
      (analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) * (1 - conj (ρ : ℂ))⁻¹ ^ m =
        (analyticOrderNatAt xiFunction ↑(uhzOneSubConjEquiv ρ) : ℂ) *
          (↑(uhzOneSubConjEquiv ρ))⁻¹ ^ m := by
    intro ρ
    have hcoe : (↑(uhzOneSubConjEquiv ρ) : ℂ) = 1 - conj (ρ : ℂ) := rfl
    rw [hmτ ρ, hcoe]
  have hstepA : ∀ ρ : UpperHalfPlaneNontrivialZero,
      (analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) * (1 - (ρ : ℂ))⁻¹ ^ m =
        (analyticOrderNatAt xiFunction ↑(uhzOneSubConjEquiv ρ) : ℂ) *
          (conj ↑(uhzOneSubConjEquiv ρ))⁻¹ ^ m := by
    intro ρ
    have hcoe : conj ↑(uhzOneSubConjEquiv ρ) = 1 - (ρ : ℂ) := by
      show conj (1 - conj (ρ : ℂ)) = 1 - (ρ : ℂ)
      rw [map_sub, map_one, Complex.conj_conj]
    rw [hmτ ρ, hcoe]
  have hf : Summable fun σ : UpperHalfPlaneNontrivialZero =>
      (analyticOrderNatAt xiFunction (σ : ℂ) : ℂ) * (σ : ℂ)⁻¹ ^ m :=
    (Equiv.summable_iff uhzOneSubConjEquiv (f := fun σ : UpperHalfPlaneNontrivialZero =>
      (analyticOrderNatAt xiFunction (σ : ℂ) : ℂ) * (σ : ℂ)⁻¹ ^ m)).mp
      (hB.congr fun ρ => hstepB ρ)
  have hg : Summable fun σ : UpperHalfPlaneNontrivialZero =>
      (analyticOrderNatAt xiFunction (σ : ℂ) : ℂ) * (conj (σ : ℂ))⁻¹ ^ m :=
    (Equiv.summable_iff uhzOneSubConjEquiv (f := fun σ : UpperHalfPlaneNontrivialZero =>
      (analyticOrderNatAt xiFunction (σ : ℂ) : ℂ) * (conj (σ : ℂ))⁻¹ ^ m)).mp
      (hA.congr fun ρ => hstepA ρ)
  have hAB : ∀ ρ : UpperHalfPlaneNontrivialZero,
      xiWeightedInvPowTerm m 1 (ρ : ℂ) =
        (analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) * (1 - (ρ : ℂ))⁻¹ ^ m +
          (analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) * (1 - conj (ρ : ℂ))⁻¹ ^ m :=
    fun ρ => by rw [xiWeightedInvPowTerm, mul_add]
  show (∑' ρ : UpperHalfPlaneNontrivialZero, xiWeightedInvPowTerm m 1 (ρ : ℂ)) = _
  rw [tsum_congr hAB, Summable.tsum_add hA hB]
  have hBval : (∑' ρ : UpperHalfPlaneNontrivialZero,
        (analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) * (1 - conj (ρ : ℂ))⁻¹ ^ m) =
      ∑' σ : UpperHalfPlaneNontrivialZero,
        (analyticOrderNatAt xiFunction (σ : ℂ) : ℂ) * (σ : ℂ)⁻¹ ^ m := by
    rw [tsum_congr hstepB]
    exact Equiv.tsum_eq uhzOneSubConjEquiv (fun σ : UpperHalfPlaneNontrivialZero =>
      (analyticOrderNatAt xiFunction (σ : ℂ) : ℂ) * (σ : ℂ)⁻¹ ^ m)
  have hAval : (∑' ρ : UpperHalfPlaneNontrivialZero,
        (analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) * (1 - (ρ : ℂ))⁻¹ ^ m) =
      ∑' σ : UpperHalfPlaneNontrivialZero,
        (analyticOrderNatAt xiFunction (σ : ℂ) : ℂ) * (conj (σ : ℂ))⁻¹ ^ m := by
    rw [tsum_congr hstepA]
    exact Equiv.tsum_eq uhzOneSubConjEquiv (fun σ : UpperHalfPlaneNontrivialZero =>
      (analyticOrderNatAt xiFunction (σ : ℂ) : ℂ) * (conj (σ : ℂ))⁻¹ ^ m)
  rw [hAval, hBval, add_comm]
  have hfg : ∀ σ : UpperHalfPlaneNontrivialZero,
      (analyticOrderNatAt xiFunction (σ : ℂ) : ℂ) * (σ : ℂ)⁻¹ ^ m +
        (analyticOrderNatAt xiFunction (σ : ℂ) : ℂ) * (conj (σ : ℂ))⁻¹ ^ m =
        xiWeightedInvResidTerm m (σ : ℂ) :=
    fun σ => by rw [xiWeightedInvResidTerm, mul_add]
  show _ = ∑' σ : UpperHalfPlaneNontrivialZero, xiWeightedInvResidTerm m (σ : ℂ)
  rw [← tsum_congr hfg]
  exact (Summable.tsum_add hf hg).symm

end RiemannExplorer
