/-
# ξ'/ξ 部分分式展开：配对 Mittag-Leffler 级数的留数（Hadamard 切片四）

本文件是「ξ'/ξ - B - Σ 配对项 = 整函数」论证的**可去奇点一半的级数侧**：
配对 Mittag-Leffler 级数和函数 `xiPairedMittagLefflerSum` 在每个上半平面
非平凡零点 `ρ₀` 处有**留数 1**（按不同零点计，不含解析重数）：

  `Tendsto (fun s => (s - ρ₀) * xiPairedMittagLefflerSum s) (𝓝[≠] ρ₀) (𝓝 1)`

## 证明路线

设 `F(s) = Σ_ρ term(s, ρ)`。取 `B := max 2 (2(‖ρ₀‖+1))` 作高/低拆分：

- **低部**是 `nontrivialZerosFinset B` 原像上的有限和
  （`tsum_xiPairedMittagLefflerTerm_low_eq_sum`）。其中 `ρ₀` 项乘以
  `(s - ρ₀)` 后恒等于连续函数
  `1 + (s-ρ₀)/ρ₀ + (s-ρ₀)/(s-conjρ₀) + (s-ρ₀)/conjρ₀`（去心邻域上，
  `field_simp`），在 `ρ₀` 处取值为 1；其余有限项在 `ρ₀` 连续
  （`s ≠ ρ, conjρ`：共轭虚部为负而 `ρ₀` 虚部为正），乘 `(s - ρ₀)` 后
  极限为 0。
- **高部**在球 `ball ρ₀ 1` 上 `DifferentiableOn`（切片三），故在 `ρ₀`
  连续，乘 `(s - ρ₀)` 后极限为 0。
- 三部由 `Tendsto.add` 合并得极限 `1 + (0 + 0) = 1`。

## 与整函数目标的关系

`ξ'/ξ` 在零点 `ρ₀` 处的留数等于 `ξ` 在该点的**解析重数**
（`analyticOrderNatAt`）。本文件给出级数侧留数恒为 1；两侧之差
`(s - ρ₀)·(ξ'/ξ - B - F)` 的极限为重数减 1，因此对**单零点**（重数 1）
差函数可去，对重零点需按重数加权的级数（配对/重数约定拼接，见
`XiPartialFraction.lean` 文件头）。

## 证明纪律

无 `sorry`/`admit`/新公理；公理审计见 `Test/XiFunctionAxiomAudit.lean`。
-/

import RiemannExplorer.XiPartialFractionAnalytic
import Mathlib.Analysis.Analytic.Order

open Complex ComplexConjugate
open scoped BigOperators Topology

namespace RiemannExplorer

/-- 上半平面非平凡零点非零（实部为正）。 -/
theorem upperZero_ne_zero (ρ : UpperHalfPlaneNontrivialZero) : (ρ : ℂ) ≠ 0 := by
  have hre := ρ.2.1.2.1
  intro h
  rw [h, Complex.zero_re] at hre
  exact (lt_irrefl 0) hre

/-- 上半平面零点的共轭非零。 -/
theorem upperZero_conj_ne_zero (ρ : UpperHalfPlaneNontrivialZero) : conj (ρ : ℂ) ≠ 0 := by
  intro h
  exact upperZero_ne_zero ρ ((map_eq_zero (starRingEnd ℂ)).mp h)

/-- 上半平面零点不等于任何上半平面零点的共轭（虚部符号相反）。 -/
theorem upperZero_ne_conj (ρ₀ ρ : UpperHalfPlaneNontrivialZero) :
    (ρ₀ : ℂ) ≠ conj (ρ : ℂ) := by
  intro h
  have him : (ρ₀ : ℂ).im = (conj (ρ : ℂ)).im := by rw [h]
  rw [Complex.conj_im] at him
  have h1 := ρ₀.2.2
  have h2 := ρ.2.2
  linarith

/-- 配对项在自身零点处的留数：`s → ρ₀`（去心）时 `(s - ρ₀)·term(s, ρ₀) → 1`。 -/
theorem tendsto_sub_mul_xiPairedMittagLefflerTerm_self
    (ρ₀ : UpperHalfPlaneNontrivialZero) :
    Filter.Tendsto (fun s => (s - (ρ₀ : ℂ)) * xiPairedMittagLefflerTerm s (ρ₀ : ℂ))
      (𝓝[≠] (ρ₀ : ℂ)) (𝓝 1) := by
  classical
  have hρ₀ : (ρ₀ : ℂ) ≠ 0 := upperZero_ne_zero ρ₀
  have hρ₀c : conj (ρ₀ : ℂ) ≠ 0 := upperZero_conj_ne_zero ρ₀
  have hρ₀ρc : (ρ₀ : ℂ) ≠ conj (ρ₀ : ℂ) := upperZero_ne_conj ρ₀ ρ₀
  have hsub : Filter.Tendsto (fun s : ℂ => s - (ρ₀ : ℂ)) (𝓝 (ρ₀ : ℂ)) (𝓝 0) := by
    have h := (continuousAt_id.sub continuousAt_const :
      ContinuousAt (fun s : ℂ => s - (ρ₀ : ℂ)) (ρ₀ : ℂ)).tendsto
    simpa using h
  -- 连续模型 q：在 ρ₀ 处取值为 1
  have hq : Filter.Tendsto
      (fun s => 1 + (s - (ρ₀ : ℂ)) / (ρ₀ : ℂ) +
        (s - (ρ₀ : ℂ)) / (s - conj (ρ₀ : ℂ)) + (s - (ρ₀ : ℂ)) / conj (ρ₀ : ℂ))
      (𝓝 (ρ₀ : ℂ)) (𝓝 1) := by
    have hsubc : Filter.Tendsto (fun s : ℂ => s - conj (ρ₀ : ℂ)) (𝓝 (ρ₀ : ℂ))
        (𝓝 ((ρ₀ : ℂ) - conj (ρ₀ : ℂ))) :=
      (continuousAt_id.sub continuousAt_const).tendsto
    have h1 := hsub.div_const (ρ₀ : ℂ)
    have h2 := hsub.div hsubc (sub_ne_zero.mpr hρ₀ρc)
    have h3 := hsub.div_const (conj (ρ₀ : ℂ))
    have h4 : Filter.Tendsto
        (fun s => 1 + (s - (ρ₀ : ℂ)) / (ρ₀ : ℂ) +
          (s - (ρ₀ : ℂ)) / (s - conj (ρ₀ : ℂ)) + (s - (ρ₀ : ℂ)) / conj (ρ₀ : ℂ))
        (𝓝 (ρ₀ : ℂ)) (𝓝 (1 + 0 / (ρ₀ : ℂ) + 0 / ((ρ₀ : ℂ) - conj (ρ₀ : ℂ)) +
          0 / conj (ρ₀ : ℂ))) :=
      ((tendsto_const_nhds.add h1).add h2).add h3
    simpa using h4
  -- 与真实函数在去心邻域上逐点相等
  have heq : (fun s => (s - (ρ₀ : ℂ)) * xiPairedMittagLefflerTerm s (ρ₀ : ℂ))
      =ᶠ[𝓝[≠] (ρ₀ : ℂ)]
      (fun s => 1 + (s - (ρ₀ : ℂ)) / (ρ₀ : ℂ) +
        (s - (ρ₀ : ℂ)) / (s - conj (ρ₀ : ℂ)) + (s - (ρ₀ : ℂ)) / conj (ρ₀ : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_ne_nhds hρ₀ρc).filter_mono nhdsWithin_le_nhds] with s hs hsρc
    show (s - (ρ₀ : ℂ)) * xiPairedMittagLefflerTerm s (ρ₀ : ℂ) =
      1 + (s - (ρ₀ : ℂ)) / (ρ₀ : ℂ) +
        (s - (ρ₀ : ℂ)) / (s - conj (ρ₀ : ℂ)) + (s - (ρ₀ : ℂ)) / conj (ρ₀ : ℂ)
    unfold xiPairedMittagLefflerTerm
    field_simp [sub_ne_zero.mpr hs, sub_ne_zero.mpr hsρc, hρ₀, hρ₀c]
    ring
  exact Filter.Tendsto.congr' heq.symm (hq.mono_left nhdsWithin_le_nhds)

/-- 其他零点项：`ρ ≠ ρ₀` 时项在 `ρ₀` 连续，乘 `(s - ρ₀)` 后极限为 0。 -/
theorem tendsto_sub_mul_xiPairedMittagLefflerTerm_of_ne
    (ρ₀ ρ : UpperHalfPlaneNontrivialZero) (hρ : ρ ≠ ρ₀) :
    Filter.Tendsto (fun s => (s - (ρ₀ : ℂ)) * xiPairedMittagLefflerTerm s (ρ : ℂ))
      (𝓝 (ρ₀ : ℂ)) (𝓝 0) := by
  have h1 : (ρ₀ : ℂ) ≠ (ρ : ℂ) := fun h => hρ (Subtype.coe_injective h).symm
  have h2 : (ρ₀ : ℂ) ≠ conj (ρ : ℂ) := upperZero_ne_conj ρ₀ ρ
  have hsub : Filter.Tendsto (fun s : ℂ => s - (ρ₀ : ℂ)) (𝓝 (ρ₀ : ℂ)) (𝓝 0) := by
    have h := (continuousAt_id.sub continuousAt_const :
      ContinuousAt (fun s : ℂ => s - (ρ₀ : ℂ)) (ρ₀ : ℂ)).tendsto
    simpa using h
  have hterm : Filter.Tendsto (fun s => xiPairedMittagLefflerTerm s (ρ : ℂ))
      (𝓝 (ρ₀ : ℂ)) (𝓝 (xiPairedMittagLefflerTerm (ρ₀ : ℂ) (ρ : ℂ))) :=
    (differentiableAt_xiPairedMittagLefflerTerm h1 h2).continuousAt.tendsto
  have h := hsub.mul hterm
  simpa using h

/-- **留数定理（级数侧）**：配对 Mittag-Leffler 级数和函数在每个上半平面零点
`ρ₀` 处留数为 1（按不同零点计）：去心极限 `(s - ρ₀)·F(s) → 1`。 -/
theorem tendsto_sub_mul_xiPairedMittagLefflerSum (ρ₀ : UpperHalfPlaneNontrivialZero) :
    Filter.Tendsto (fun s => (s - (ρ₀ : ℂ)) * xiPairedMittagLefflerSum s)
      (𝓝[≠] (ρ₀ : ℂ)) (𝓝 1) := by
  classical
  set B := max 2 (2 * (‖(ρ₀ : ℂ)‖ + 1)) with hB
  have hltB : ‖(ρ₀ : ℂ)‖ < B := by
    have h1 : 2 * (‖(ρ₀ : ℂ)‖ + 1) ≤ B := le_max_right _ _
    have h2 := norm_nonneg (ρ₀ : ℂ)
    linarith
  have hmem : ρ₀ ∈ (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
      (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn := by
    rw [Finset.mem_preimage, PrimeNumberTheorem.mem_nontrivialZerosFinset]
    exact ⟨ρ₀.2.1, (Complex.abs_im_le_norm _).trans hltB.le⟩
  -- 高部在 ρ₀ 连续（来自高部的球上 DifferentiableOn）
  have hcontHigh : ContinuousAt (fun s => ∑' ρ : UpperHalfPlaneNontrivialZero,
        (if B ≤ ‖(ρ : ℂ)‖ then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0)) (ρ₀ : ℂ) := by
    have hd := differentiableOn_tsum_xiPairedMittagLefflerTerm_high (ρ₀ : ℂ)
    exact hd.continuousOn.continuousAt (Metric.ball_mem_nhds _ one_pos)
  -- 分解恒等式
  have hdecomp : (fun s => (s - (ρ₀ : ℂ)) * xiPairedMittagLefflerSum s) =
      fun s => (s - (ρ₀ : ℂ)) * xiPairedMittagLefflerTerm s (ρ₀ : ℂ) +
        ((s - (ρ₀ : ℂ)) * ∑ ρ ∈ (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
              (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn
              |>.erase ρ₀,
            (if ‖(ρ : ℂ)‖ < B then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0) +
          (s - (ρ₀ : ℂ)) * ∑' ρ : UpperHalfPlaneNontrivialZero,
            (if B ≤ ‖(ρ : ℂ)‖ then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0)) := by
    funext s
    rw [xiPairedMittagLefflerSum_eq_low_add_high B s,
      tsum_xiPairedMittagLefflerTerm_low_eq_sum B s,
      ← Finset.add_sum_erase _ _ hmem, if_pos hltB]
    ring
  rw [hdecomp]
  have hA := tendsto_sub_mul_xiPairedMittagLefflerTerm_self ρ₀
  have hB' : Filter.Tendsto (fun s => (s - (ρ₀ : ℂ)) *
        ∑ ρ ∈ (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
            (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn
            |>.erase ρ₀,
          (if ‖(ρ : ℂ)‖ < B then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0))
      (𝓝 (ρ₀ : ℂ)) (𝓝 0) := by
    rw [show (fun s => (s - (ρ₀ : ℂ)) *
          ∑ ρ ∈ (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
              (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn
              |>.erase ρ₀,
            (if ‖(ρ : ℂ)‖ < B then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0)) =
        fun s => ∑ ρ ∈ (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
              (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn
              |>.erase ρ₀,
          (s - (ρ₀ : ℂ)) * (if ‖(ρ : ℂ)‖ < B then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0)
      from funext fun s => Finset.mul_sum _ _ _]
    have hsum : Filter.Tendsto
        (fun s => ∑ ρ ∈ (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
              (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn
              |>.erase ρ₀,
          (s - (ρ₀ : ℂ)) * (if ‖(ρ : ℂ)‖ < B then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0))
        (𝓝 (ρ₀ : ℂ))
        (𝓝 (∑ _ρ ∈ (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
              (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn
              |>.erase ρ₀, (0 : ℂ))) := by
      refine tendsto_finset_sum _ fun ρ hρmem => ?_
      have hρne : ρ ≠ ρ₀ := (Finset.mem_erase.mp hρmem).1
      by_cases hlt : ‖(ρ : ℂ)‖ < B
      · rw [show (fun s => (s - (ρ₀ : ℂ)) *
            (if ‖(ρ : ℂ)‖ < B then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0)) =
          fun s => (s - (ρ₀ : ℂ)) * xiPairedMittagLefflerTerm s (ρ : ℂ)
          from funext fun s => by rw [if_pos hlt]]
        exact tendsto_sub_mul_xiPairedMittagLefflerTerm_of_ne ρ₀ ρ hρne
      · rw [show (fun s => (s - (ρ₀ : ℂ)) *
            (if ‖(ρ : ℂ)‖ < B then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0)) =
          fun _ => 0 from funext fun s => by rw [if_neg hlt, mul_zero]]
        exact tendsto_const_nhds
    simpa using hsum
  have hC : Filter.Tendsto (fun s => (s - (ρ₀ : ℂ)) * ∑' ρ : UpperHalfPlaneNontrivialZero,
        (if B ≤ ‖(ρ : ℂ)‖ then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0))
      (𝓝 (ρ₀ : ℂ)) (𝓝 0) := by
    have hsub : Filter.Tendsto (fun s : ℂ => s - (ρ₀ : ℂ)) (𝓝 (ρ₀ : ℂ)) (𝓝 0) := by
      have h := (continuousAt_id.sub continuousAt_const :
        ContinuousAt (fun s : ℂ => s - (ρ₀ : ℂ)) (ρ₀ : ℂ)).tendsto
      simpa using h
    have h := hsub.mul hcontHigh.tendsto
    simpa using h
  have hBC := (hB'.mono_left (nhdsWithin_le_nhds (s := {(ρ₀ : ℂ)}ᶜ))).add
    (hC.mono_left (nhdsWithin_le_nhds (s := {(ρ₀ : ℂ)}ᶜ)))
  have hABC := hA.add hBC
  simpa using hABC

/-- 差函数 `D(s) = ξ'(s)/ξ(s) - c - F(s)` 在 `ξ` 非零点开集上复可微：
`ξ'` 在开集上仍可微（复可微函数的导数定理 `DifferentiableOn.deriv`），
商式在 `ξ ≠ 0` 处可微，级数侧可微性由切片三给出。 -/
theorem differentiableOn_logDeriv_xiFunction_sub_xiPairedMittagLefflerSum (c : ℂ) :
    DifferentiableOn ℂ
      (fun s => deriv xiFunction s / xiFunction s - c - xiPairedMittagLefflerSum s)
      {s : ℂ | xiFunction s ≠ 0} := by
  have hderiv : DifferentiableOn ℂ (deriv xiFunction) {s : ℂ | xiFunction s ≠ 0} :=
    ((differentiable_xiFunction.differentiableOn (s := Set.univ)).deriv
      isOpen_univ).mono (Set.subset_univ _)
  exact (((hderiv.div differentiable_xiFunction.differentiableOn
    fun s hs => hs).sub (differentiableOn_const c)).sub
    differentiableOn_tsum_xiPairedMittagLefflerTerm)

/-! ## ξ'/ξ 侧的留数：等于解析重数 -/

/-- **留数定理（ξ'/ξ 侧）**：在每个上半平面零点 `ρ₀` 处，
`(s - ρ₀)·ξ'(s)/ξ(s)` 的去心极限等于 `ξ` 在 `ρ₀` 的解析重数
（`analyticOrderNatAt`，≥ 1）。

证明：由恒等定理（`ξ 0 = 1/2 ≠ 0`），`ξ` 在 `ρ₀` 不局部恒零，
故解析阶为某个自然数 `n`；`ξ ρ₀ = 0` 给出 `n ≥ 1`。局部因子分解
`ξ z = (z - ρ₀)ⁿ · g z`（`g` 解析、`g ρ₀ ≠ 0`，
`AnalyticAt.analyticOrderAt_eq_natCast`）逐项求导后在去心邻域上
`(s - ρ₀)·ξ'/ξ = (n·g + (s - ρ₀)·g')/g`，极限为 `n·g ρ₀/g ρ₀ = n`。 -/
theorem tendsto_sub_mul_logDeriv_xiFunction (ρ₀ : UpperHalfPlaneNontrivialZero) :
    Filter.Tendsto (fun s => (s - (ρ₀ : ℂ)) * (deriv xiFunction s / xiFunction s))
      (𝓝[≠] (ρ₀ : ℂ)) (𝓝 ((analyticOrderNatAt xiFunction (ρ₀ : ℂ) : ℂ))) := by
  classical
  have hξa : AnalyticAt ℂ xiFunction (ρ₀ : ℂ) := differentiable_xiFunction.analyticAt _
  have hξ0 : xiFunction (ρ₀ : ℂ) = 0 :=
    (xiFunction_eq_zero_iff_isNontrivialZero ρ₀.2.1.2.1 ρ₀.2.1.2.2).mpr ρ₀.2.1
  -- 恒等定理：ξ 不在 ρ₀ 附近恒为零（否则 ξ ≡ 0，与 ξ 0 = 1/2 矛盾）
  have hne : ¬ ∀ᶠ z in 𝓝 (ρ₀ : ℂ), xiFunction z = 0 := by
    intro h
    have han : AnalyticOnNhd ℂ xiFunction Set.univ :=
      (differentiable_xiFunction.differentiableOn (s := Set.univ)).analyticOnNhd isOpen_univ
    have hfreq : ∃ᶠ z in 𝓝[≠] (ρ₀ : ℂ), xiFunction z = 0 :=
      (h.filter_mono nhdsWithin_le_nhds).frequently
    have hEq := han.eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_univ (Set.mem_univ _) hfreq
    have h00 := hEq (Set.mem_univ (0 : ℂ))
    simp only [Pi.zero_apply] at h00
    rw [xiFunction_zero] at h00
    norm_num at h00
  have horder_top : analyticOrderAt xiFunction (ρ₀ : ℂ) ≠ ⊤ :=
    fun h => hne (analyticOrderAt_eq_top.mp h)
  set n := analyticOrderNatAt xiFunction (ρ₀ : ℂ) with hn
  have hn_eq : analyticOrderAt xiFunction (ρ₀ : ℂ) = (n : ℕ∞) := by
    rw [hn]
    exact (Nat.cast_analyticOrderNatAt horder_top).symm
  obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := (hξa.analyticOrderAt_eq_natCast).mp hn_eq
  -- n ≥ 1：若 n = 0 则 g ρ₀ = ξ ρ₀ = 0，矛盾
  have hn_pos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exfalso
      have hh := Filter.EventuallyEq.eq_of_nhds hg_eq
      rw [h0, pow_zero, one_smul] at hh
      exact hg_ne (hh.symm.trans hξ0)
    · exact hpos
  have hg_eq' : ∀ᶠ z in 𝓝 (ρ₀ : ℂ), xiFunction z = (z - (ρ₀ : ℂ)) ^ n * g z := by
    filter_upwards [hg_eq] with z hz
    rwa [smul_eq_mul] at hz
  have hg_cont : ContinuousAt g (ρ₀ : ℂ) := hg_an.continuousAt
  -- deriv g 在 ρ₀ 连续（deriv 在解析邻域上仍解析）
  have hgder_cont : ContinuousAt (deriv g) (ρ₀ : ℂ) := by
    obtain ⟨U, hU_nhds, hU⟩ := hg_an.eventually_analyticAt.exists_mem
    exact (AnalyticOnNhd.deriv (fun z hz => hU z hz)) (ρ₀ : ℂ)
      (mem_of_mem_nhds hU_nhds) |>.continuousAt
  have hsub : Filter.Tendsto (fun s : ℂ => s - (ρ₀ : ℂ)) (𝓝 (ρ₀ : ℂ)) (𝓝 0) := by
    have h := (continuousAt_id.sub continuousAt_const :
      ContinuousAt (fun s : ℂ => s - (ρ₀ : ℂ)) (ρ₀ : ℂ)).tendsto
    simpa using h
  -- 连续模型 q(s) = (n·g s + (s - ρ₀)·g' s)/g s 的极限为 n
  have hnum : Filter.Tendsto (fun s => (↑n : ℂ) * g s + (s - (ρ₀ : ℂ)) * deriv g s)
      (𝓝 (ρ₀ : ℂ)) (𝓝 ((↑n : ℂ) * g (ρ₀ : ℂ) + 0 * deriv g (ρ₀ : ℂ))) :=
    (tendsto_const_nhds.mul hg_cont.tendsto).add (hsub.mul hgder_cont.tendsto)
  have hT : Filter.Tendsto
      (fun s => ((↑n : ℂ) * g s + (s - (ρ₀ : ℂ)) * deriv g s) / g s)
      (𝓝 (ρ₀ : ℂ)) (𝓝 (((↑n : ℂ) * g (ρ₀ : ℂ) + 0 * deriv g (ρ₀ : ℂ)) / g (ρ₀ : ℂ))) :=
    hnum.div hg_cont.tendsto hg_ne
  have hlim : ((↑n : ℂ) * g (ρ₀ : ℂ) + 0 * deriv g (ρ₀ : ℂ)) / g (ρ₀ : ℂ) = (↑n : ℂ) := by
    rw [zero_mul, add_zero]
    field_simp [hg_ne]
  have hmodel : Filter.Tendsto
      (fun s => ((↑n : ℂ) * g s + (s - (ρ₀ : ℂ)) * deriv g s) / g s)
      (𝓝[≠] (ρ₀ : ℂ)) (𝓝 (↑n : ℂ)) := by
    rw [congrArg 𝓝 hlim.symm]
    exact hT.mono_left (nhdsWithin_le_nhds (s := {(ρ₀ : ℂ)}ᶜ))
  -- 去心邻域上的逐点恒等式
  have heq : (fun s => (s - (ρ₀ : ℂ)) * (deriv xiFunction s / xiFunction s))
      =ᶠ[𝓝[≠] (ρ₀ : ℂ)]
      (fun s => ((↑n : ℂ) * g s + (s - (ρ₀ : ℂ)) * deriv g s) / g s) := by
    filter_upwards [self_mem_nhdsWithin, hg_eq'.filter_mono nhdsWithin_le_nhds,
      (Filter.EventuallyEq.deriv hg_eq').filter_mono nhdsWithin_le_nhds,
      hg_an.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      (hg_cont.tendsto.eventually (eventually_ne_nhds hg_ne)).filter_mono
        nhdsWithin_le_nhds] with s hs_ne hξz hder_z hg_an_s hg_ne_s
    show (s - (ρ₀ : ℂ)) * (deriv xiFunction s / xiFunction s) =
      ((↑n : ℂ) * g s + (s - (ρ₀ : ℂ)) * deriv g s) / g s
    have hder_pow : deriv (fun z : ℂ => (z - (ρ₀ : ℂ)) ^ n) s =
        ↑n * (s - (ρ₀ : ℂ)) ^ (n - 1) := by
      have h1 : deriv (fun z : ℂ => (z - (ρ₀ : ℂ)) ^ n) s =
          ↑n * (s - (ρ₀ : ℂ)) ^ (n - 1) * deriv (fun z : ℂ => z - (ρ₀ : ℂ)) s :=
        deriv_pow (differentiableAt_id.sub (differentiableAt_const (ρ₀ : ℂ))) n
      have h2 : deriv (fun z : ℂ => z - (ρ₀ : ℂ)) s = 1 := by
        rw [deriv_sub_const]
        exact (hasDerivAt_id' s).deriv
      rw [h1, h2, mul_one]
    have hder_prod : deriv (fun z : ℂ => (z - (ρ₀ : ℂ)) ^ n * g z) s =
        ↑n * (s - (ρ₀ : ℂ)) ^ (n - 1) * g s + (s - (ρ₀ : ℂ)) ^ n * deriv g s := by
      have hm : deriv (fun z : ℂ => (z - (ρ₀ : ℂ)) ^ n * g z) s =
          deriv (fun z : ℂ => (z - (ρ₀ : ℂ)) ^ n) s * g s +
            (s - (ρ₀ : ℂ)) ^ n * deriv g s :=
        deriv_mul ((differentiableAt_id.sub (differentiableAt_const (ρ₀ : ℂ))).pow n)
          hg_an_s.differentiableAt
      rw [hm, hder_pow]
    have hpow : (s - (ρ₀ : ℂ)) ^ n = (s - (ρ₀ : ℂ)) ^ (n - 1) * (s - (ρ₀ : ℂ)) := by
      conv_lhs => rw [← Nat.sub_one_add_one_eq_of_pos hn_pos, pow_succ]
    rw [hξz, hder_z, hder_prod, hpow]
    field_simp [pow_ne_zero _ (sub_ne_zero.mpr hs_ne), sub_ne_zero.mpr hs_ne, hg_ne_s]
    try ring
  exact Filter.Tendsto.congr' heq.symm hmodel

/-- **差函数留数**：`(s - ρ₀)·(ξ'(s)/ξ(s) - F(s)) → 重数 - 1`。
因此差函数在**单零点**（重数 1）处留数为 0（可去奇点的一半）；
重零点处按不同零点计的级数与 `ξ'/ξ` 留数差为重数减 1，
这正是「重数约定拼接」缺口的精确形态。 -/
theorem tendsto_sub_mul_logDeriv_xiFunction_sub_xiPairedMittagLefflerSum
    (ρ₀ : UpperHalfPlaneNontrivialZero) :
    Filter.Tendsto
      (fun s => (s - (ρ₀ : ℂ)) *
        (deriv xiFunction s / xiFunction s - xiPairedMittagLefflerSum s))
      (𝓝[≠] (ρ₀ : ℂ))
      (𝓝 ((analyticOrderNatAt xiFunction (ρ₀ : ℂ) : ℂ) - 1)) := by
  rw [show (fun s => (s - (ρ₀ : ℂ)) *
        (deriv xiFunction s / xiFunction s - xiPairedMittagLefflerSum s)) =
      fun s => (s - (ρ₀ : ℂ)) * (deriv xiFunction s / xiFunction s) -
        (s - (ρ₀ : ℂ)) * xiPairedMittagLefflerSum s
    from funext fun s => mul_sub _ _ _]
  exact (tendsto_sub_mul_logDeriv_xiFunction ρ₀).sub
    (tendsto_sub_mul_xiPairedMittagLefflerSum ρ₀)

end RiemannExplorer
