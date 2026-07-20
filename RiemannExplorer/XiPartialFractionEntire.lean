/-
# ξ'/ξ 部分分式展开：任意零点留数与整函数延拓（Hadamard 切片五）

本文件把 `XiPartialFractionResidue.lean` 中「上半平面非平凡零点」处的留数
结果推广到 ξ 的**任意零点**（含下半平面，经施瓦茨对称 `ξ(conj s) = conj(ξ s)`
共轭得到），给出**单零点**处对数导数与配对 Mittag-Leffler 级数之差的
留数消失定理：

  `Tendsto (fun s => (s - s₀) * (ξ'/ξ s - c - F s)) (𝓝[≠] s₀) (𝓝 0)`

并在此之上完成**可去奇点粘合（gluing）**：定义修正函数
`xiPartialFractionEntireCorrection c`（非零点等于差函数 `ξ'/ξ − c − F`，
零点处取去心极限），证明在「ξ 的零点都是临界带内虚部非零的单零点」
两个显式假设下该修正函数是**整函数**
（`differentiable_xiPartialFractionEntireCorrection`）。

## 证明纪律

无 `sorry`/`admit`/新公理；公理审计见 `Test/XiFunctionAxiomAudit.lean`。
-/

import RiemannExplorer.XiPartialFractionResidue
import Mathlib.Analysis.Complex.RemovableSingularity

open Complex ComplexConjugate
open scoped BigOperators Topology

namespace RiemannExplorer

/-- 配对 Mittag-Leffler 项关于 `s ↦ conj s` 的共轭对称性。 -/
theorem xiPairedMittagLefflerTerm_conj (s ρ : ℂ) :
    xiPairedMittagLefflerTerm (conj s) ρ = conj (xiPairedMittagLefflerTerm s ρ) := by
  unfold xiPairedMittagLefflerTerm
  simp only [map_add, map_div₀, map_one, map_sub, Complex.conj_conj]
  ring

/-- 配对 Mittag-Leffler 级数和函数的共轭对称性：`F(conj s) = conj (F s)`。 -/
theorem xiPairedMittagLefflerSum_conj (s : ℂ) :
    xiPairedMittagLefflerSum (conj s) = conj (xiPairedMittagLefflerSum s) := by
  unfold xiPairedMittagLefflerSum
  rw [Complex.conj_tsum]
  exact tsum_congr fun ρ => xiPairedMittagLefflerTerm_conj s (ρ : ℂ)

/-- 级数在上半平面零点的共轭点处留数亦为 1（经共轭映射复合）。 -/
theorem tendsto_sub_mul_xiPairedMittagLefflerSum_conj
    (ρ₀ : UpperHalfPlaneNontrivialZero) :
    Filter.Tendsto (fun s => (s - conj (ρ₀ : ℂ)) * xiPairedMittagLefflerSum s)
      (𝓝[≠] (conj (ρ₀ : ℂ))) (𝓝 1) := by
  have hmap : Filter.Tendsto (conj : ℂ → ℂ) (𝓝[≠] (conj (ρ₀ : ℂ)))
      (𝓝[≠] (ρ₀ : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    have hc : Filter.Tendsto (conj : ℂ → ℂ) (𝓝 (conj (ρ₀ : ℂ))) (𝓝 (ρ₀ : ℂ)) := by
      have h := Complex.continuous_conj.tendsto (conj (ρ₀ : ℂ))
      rwa [Complex.conj_conj] at h
    have hne : ∀ᶠ s in 𝓝[≠] (conj (ρ₀ : ℂ)), conj s ≠ (ρ₀ : ℂ) := by
      rw [eventually_nhdsWithin_iff]
      exact Filter.Eventually.of_forall fun s hs heq =>
        hs (by have h := congrArg conj heq; rwa [Complex.conj_conj] at h)
    exact ⟨hc.mono_left nhdsWithin_le_nhds, hne⟩
  have h1 := (tendsto_sub_mul_xiPairedMittagLefflerSum ρ₀).comp hmap
  have h2 := (Complex.continuous_conj.tendsto (1 : ℂ)).comp h1
  rw [map_one] at h2
  refine h2.congr' (Filter.Eventually.of_forall fun s => ?_)
  show conj ((conj s - (ρ₀ : ℂ)) * xiPairedMittagLefflerSum (conj s)) =
    (s - conj (ρ₀ : ℂ)) * xiPairedMittagLefflerSum s
  rw [map_mul, map_sub, Complex.conj_conj, xiPairedMittagLefflerSum_conj,
    Complex.conj_conj]

/-- 级数在 ζ 的**任意**非平凡零点（虚部非零）处留数为 1。 -/
theorem tendsto_sub_mul_xiPairedMittagLefflerSum_of_zero {s₀ : ℂ}
    (hz : RiemannHypothesis.IsNontrivialZero s₀) (him : s₀.im ≠ 0) :
    Filter.Tendsto (fun s => (s - s₀) * xiPairedMittagLefflerSum s)
      (𝓝[≠] s₀) (𝓝 1) := by
  rcases lt_or_gt_of_ne him with hlt | hgt
  · -- s₀.im < 0：conj s₀ 是上半平面非平凡零点
    have h0' : 0 < (conj s₀).re := by rw [Complex.conj_re]; exact hz.2.1
    have h1' : (conj s₀).re < 1 := by rw [Complex.conj_re]; exact hz.2.2
    have hξs₀ : xiFunction s₀ = 0 :=
      (xiFunction_eq_zero_iff hz.2.1 hz.2.2).mpr hz.1
    have hξc : xiFunction (conj s₀) = 0 := by
      rw [xiFunction_conj, hξs₀, map_zero]
    have hζc : riemannZeta (conj s₀) = 0 := (xiFunction_eq_zero_iff h0' h1').mp hξc
    have himc : 0 < (conj s₀).im := by rw [Complex.conj_im]; linarith
    have h3 := tendsto_sub_mul_xiPairedMittagLefflerSum_conj
      ⟨conj s₀, ⟨⟨hζc, h0', h1'⟩, himc⟩⟩
    have h3' : Filter.Tendsto
        (fun s => (s - conj (conj s₀)) * xiPairedMittagLefflerSum s)
        (𝓝[≠] (conj (conj s₀))) (𝓝 1) := h3
    rwa [Complex.conj_conj] at h3'
  · exact tendsto_sub_mul_xiPairedMittagLefflerSum ⟨s₀, hz, hgt⟩

/-- 任意非平凡零点处，`(s − s₀)·(ξ'/ξ − F)` 的极限为「解析重数 − 1」。 -/
theorem tendsto_sub_mul_logDeriv_sub_xiPairedMittagLefflerSum_of_zero {s₀ : ℂ}
    (hz : RiemannHypothesis.IsNontrivialZero s₀) (him : s₀.im ≠ 0) :
    Filter.Tendsto
      (fun s => (s - s₀) * (deriv xiFunction s / xiFunction s -
        xiPairedMittagLefflerSum s))
      (𝓝[≠] s₀) (𝓝 ((analyticOrderNatAt xiFunction s₀ : ℂ) - 1)) := by
  have h1 := tendsto_sub_mul_logDeriv_xiFunction_of_zero
    ((xiFunction_eq_zero_iff hz.2.1 hz.2.2).mpr hz.1)
  have h2 := tendsto_sub_mul_xiPairedMittagLefflerSum_of_zero hz him
  have h3 := h1.sub h2
  refine h3.congr' (Filter.Eventually.of_forall fun s => ?_)
  show (s - s₀) * (deriv xiFunction s / xiFunction s) -
      (s - s₀) * xiPairedMittagLefflerSum s =
    (s - s₀) * (deriv xiFunction s / xiFunction s - xiPairedMittagLefflerSum s)
  rw [mul_sub]

/-- **单零点**处差函数的留数消失：`(s − s₀)·(ξ'/ξ − c − F) → 0`。
这是差函数在 `s₀` 处奇点可去的 `isLittleO` 输入。 -/
theorem tendsto_sub_mul_logDeriv_sub_const_sub_xiPairedMittagLefflerSum_of_zero
    (c : ℂ) {s₀ : ℂ}
    (hz : RiemannHypothesis.IsNontrivialZero s₀) (him : s₀.im ≠ 0)
    (hs : analyticOrderNatAt xiFunction s₀ = 1) :
    Filter.Tendsto
      (fun s => (s - s₀) * (deriv xiFunction s / xiFunction s - c -
        xiPairedMittagLefflerSum s))
      (𝓝[≠] s₀) (𝓝 0) := by
  have h1 := tendsto_sub_mul_logDeriv_sub_xiPairedMittagLefflerSum_of_zero hz him
  rw [hs] at h1
  simp only [Nat.cast_one, sub_self] at h1
  have hsub0 : Filter.Tendsto (fun s : ℂ => s - s₀) (𝓝[≠] s₀) (𝓝 0) := by
    have h : Filter.Tendsto (fun s : ℂ => s - s₀) (𝓝 s₀) (𝓝 0) := by
      have h := (continuous_sub_right s₀).tendsto s₀
      simpa using h
    exact h.mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto (fun s => (s - s₀) * c) (𝓝[≠] s₀) (𝓝 0) := by
    have hc0 : Filter.Tendsto (fun _ : ℂ => c) (𝓝[≠] s₀) (𝓝 c) := tendsto_const_nhds
    have h := hsub0.mul hc0
    rwa [zero_mul] at h
  have h3 := h1.sub h2
  rw [sub_zero] at h3
  refine h3.congr' (Filter.Eventually.of_forall fun s => ?_)
  ring

/-- 差函数 `ξ'/ξ − c − F` 的**整函数延拓修正**：在非零点等于差函数本身，
在零点处取去心极限（可去奇点粘合后的值）。 -/
noncomputable def xiPartialFractionEntireCorrection (c : ℂ) (s : ℂ) : ℂ :=
  Filter.limUnder (𝓝[≠] s)
    (fun z => deriv xiFunction z / xiFunction z - c - xiPairedMittagLefflerSum z)

/-- 在非零点处，修正函数等于差函数本身（无条件：去心极限等于函数值）。 -/
theorem xiPartialFractionEntireCorrection_apply_of_ne_zero (c : ℂ) {s : ℂ}
    (hs : xiFunction s ≠ 0) :
    xiPartialFractionEntireCorrection c s =
      deriv xiFunction s / xiFunction s - c - xiPairedMittagLefflerSum s := by
  have hopen : IsOpen {z : ℂ | xiFunction z ≠ 0} :=
    isOpen_compl_singleton.preimage differentiable_xiFunction.continuous
  have hdiff := (differentiableOn_logDeriv_xiFunction_sub_xiPairedMittagLefflerSum
    c).differentiableAt (hopen.mem_nhds hs)
  exact (hdiff.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq

/-- **Gluing（整函数延拓）**：在「ξ 的零点都是临界带内虚部非零的单零点」
两个显式假设下，差函数 `ξ'/ξ − c − F` 的修正延拓是**整函数**。

证明：非零点处修正与差函数局部相等（差函数在该处可微）；零点 `s` 处，
单零点假设给出 `(z − s)·D z → 0`（本文件切片五），即
`D z − D s = o((z − s)⁻¹)`（去心），孤立零点性质给出可微的去心球，
由可去奇点定理 `differentiableOn_update_limUnder_of_isLittleO` 粘合后
`update D s (lim D)` 在球上可微，而修正函数在球上与它逐点相等。 -/
theorem differentiable_xiPartialFractionEntireCorrection (c : ℂ)
    (hclass : ∀ s : ℂ, xiFunction s = 0 →
      RiemannHypothesis.IsNontrivialZero s ∧ s.im ≠ 0)
    (hsimple : ∀ s : ℂ, xiFunction s = 0 → analyticOrderNatAt xiFunction s = 1) :
    Differentiable ℂ (xiPartialFractionEntireCorrection c) := by
  intro s
  by_cases hs : xiFunction s = 0
  · -- 零点分支：可去奇点粘合
    obtain ⟨hz, him⟩ := hclass s hs
    have hs' := hsimple s hs
    -- 孤立零点：解析阶 ≠ ⊤（否则阶的 Nat 部分为 0，与单零点矛盾）
    have hne_top : analyticOrderAt xiFunction s ≠ ⊤ := by
      intro ht
      have hrfl : analyticOrderNatAt xiFunction s =
        (analyticOrderAt xiFunction s).toNat := rfl
      have h0 : analyticOrderNatAt xiFunction s = 0 := by rw [hrfl, ht]; rfl
      rw [h0] at hs'
      exact zero_ne_one hs'
    have hne : ¬ ∀ᶠ z in 𝓝 s, xiFunction z = 0 :=
      fun h => hne_top (analyticOrderAt_eq_top.mpr h)
    have hpunct : ¬ ∃ᶠ z in 𝓝[≠] s, xiFunction z = 0 :=
      fun hfreq => hne ((differentiable_xiFunction.analyticAt
        s).frequently_zero_iff_eventually_zero.mp hfreq)
    rw [Filter.not_frequently, eventually_nhdsWithin_iff,
      Metric.eventually_nhds_iff_ball] at hpunct
    obtain ⟨R, hR0, hR⟩ := hpunct
    -- 差函数在去心球上可微
    have hDball : DifferentiableOn ℂ
        (fun z => deriv xiFunction z / xiFunction z - c -
          xiPairedMittagLefflerSum z)
        (Metric.ball s R \ {s}) :=
      (differentiableOn_logDeriv_xiFunction_sub_xiPairedMittagLefflerSum c).mono
        (fun z hz => hR z hz.1 hz.2)
    -- isLittleO 输入：(z − s)·D z → 0 与 (z − s)·D s → 0
    have hres :=
      tendsto_sub_mul_logDeriv_sub_const_sub_xiPairedMittagLefflerSum_of_zero
        c hz him hs'
    have hsub0 : Filter.Tendsto (fun z : ℂ => z - s) (𝓝[≠] s) (𝓝 0) := by
      have h : Filter.Tendsto (fun z : ℂ => z - s) (𝓝 s) (𝓝 0) := by
        have h := (continuous_sub_right s).tendsto s
        simpa using h
      exact h.mono_left nhdsWithin_le_nhds
    have hconst : Filter.Tendsto
        (fun z => (z - s) * (deriv xiFunction s / xiFunction s - c -
          xiPairedMittagLefflerSum s)) (𝓝[≠] s) (𝓝 0) := by
      have hc0 : Filter.Tendsto
          (fun _ : ℂ => deriv xiFunction s / xiFunction s - c -
            xiPairedMittagLefflerSum s) (𝓝[≠] s)
          (𝓝 (deriv xiFunction s / xiFunction s - c -
            xiPairedMittagLefflerSum s)) :=
        tendsto_const_nhds
      have h := hsub0.mul hc0
      rwa [zero_mul] at h
    have hDs := hres.sub hconst
    rw [sub_zero] at hDs
    have hquot : Filter.Tendsto
        (fun z => ((deriv xiFunction z / xiFunction z - c -
          xiPairedMittagLefflerSum z) -
            (deriv xiFunction s / xiFunction s - c -
              xiPairedMittagLefflerSum s)) / (z - s)⁻¹)
        (𝓝[≠] s) (𝓝 0) :=
      hDs.congr' (Filter.Eventually.of_forall fun z => by
        show (z - s) * (deriv xiFunction z / xiFunction z - c -
            xiPairedMittagLefflerSum z) -
            (z - s) * (deriv xiFunction s / xiFunction s - c -
              xiPairedMittagLefflerSum s) =
          ((deriv xiFunction z / xiFunction z - c -
            xiPairedMittagLefflerSum z) -
              (deriv xiFunction s / xiFunction s - c -
                xiPairedMittagLefflerSum s)) / (z - s)⁻¹
        rw [div_inv_eq_mul]; ring)
    have ho : (fun z => (deriv xiFunction z / xiFunction z - c -
        xiPairedMittagLefflerSum z) -
          (deriv xiFunction s / xiFunction s - c - xiPairedMittagLefflerSum s))
        =o[𝓝[≠] s] fun z => (z - s)⁻¹ :=
      (Asymptotics.isLittleO_iff_tendsto fun z hz0 => by
        have hzs : z = s := sub_eq_zero.mp (inv_eq_zero.mp hz0)
        rw [hzs, sub_self]).mpr hquot
    have hUpd := differentiableOn_update_limUnder_of_isLittleO
      (Metric.ball_mem_nhds s hR0) hDball ho
    -- 修正函数在球上与 update 版逐点相等
    have hEq : ∀ z ∈ Metric.ball s R,
        xiPartialFractionEntireCorrection c z =
          Function.update
            (fun w => deriv xiFunction w / xiFunction w - c -
              xiPairedMittagLefflerSum w) s
            (Filter.limUnder (𝓝[≠] s)
              (fun w => deriv xiFunction w / xiFunction w - c -
                xiPairedMittagLefflerSum w)) z := by
      intro z hzb
      by_cases hzs : z = s
      · rw [hzs, Function.update_self]
        rfl
      · rw [Function.update_of_ne hzs]
        exact xiPartialFractionEntireCorrection_apply_of_ne_zero c
          (hR z hzb hzs)
    have hev : xiPartialFractionEntireCorrection c =ᶠ[𝓝 s]
        Function.update
          (fun w => deriv xiFunction w / xiFunction w - c -
            xiPairedMittagLefflerSum w) s
          (Filter.limUnder (𝓝[≠] s)
            (fun w => deriv xiFunction w / xiFunction w - c -
              xiPairedMittagLefflerSum w)) :=
      Filter.eventually_of_mem (Metric.ball_mem_nhds s hR0) hEq
    exact (hUpd.differentiableAt (Metric.ball_mem_nhds s hR0)).congr_of_eventuallyEq hev
  · -- 非零点分支：修正函数与差函数局部相等
    have hopen : IsOpen {z : ℂ | xiFunction z ≠ 0} :=
      isOpen_compl_singleton.preimage differentiable_xiFunction.continuous
    have hev : xiPartialFractionEntireCorrection c =ᶠ[𝓝 s]
        (fun z => deriv xiFunction z / xiFunction z - c -
          xiPairedMittagLefflerSum z) :=
      Filter.eventually_of_mem (hopen.mem_nhds hs) fun z hz =>
        xiPartialFractionEntireCorrection_apply_of_ne_zero c hz
    exact ((differentiableOn_logDeriv_xiFunction_sub_xiPairedMittagLefflerSum
      c).differentiableAt (hopen.mem_nhds hs)).congr_of_eventuallyEq hev

/-- ξ 在任意点附近不恒为零（恒等定理 + `ξ 0 = 1/2`）。 -/
theorem xiFunction_ne_eventually_zero (s₀ : ℂ) :
    ¬ ∀ᶠ z in 𝓝 s₀, xiFunction z = 0 := by
  intro h
  have han : AnalyticOnNhd ℂ xiFunction Set.univ :=
    (differentiable_xiFunction.differentiableOn (s := Set.univ)).analyticOnNhd
      isOpen_univ
  have hfreq : ∃ᶠ z in 𝓝[≠] s₀, xiFunction z = 0 :=
    (h.filter_mono nhdsWithin_le_nhds).frequently
  have hEq := han.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_univ (Set.mem_univ _) hfreq
  have h00 := hEq (Set.mem_univ (0 : ℂ))
  simp only [Pi.zero_apply] at h00
  rw [xiFunction_zero] at h00
  norm_num at h00

/-- ξ 的零点孤立：任意点的去心邻域上 ξ 最终非零。 -/
theorem xiFunction_eventually_ne_zero_punctured (s₀ : ℂ) :
    ∀ᶠ z in 𝓝[≠] s₀, xiFunction z ≠ 0 := by
  rw [← Filter.not_frequently]
  intro hfreq
  exact xiFunction_ne_eventually_zero s₀
    ((differentiable_xiFunction.analyticAt
      s₀).frequently_zero_iff_eventually_zero.mp hfreq)

/-- **不可约缺口的精确刻画（必要条件）**：若
`xi_partial_fraction_expansion_target` 成立（存在常数 `B` 使**按不同零点
计、留数 1** 的配对展开在非零点处成立），则 ξ 的每个零点都是**单零点**
（解析重数 1）。

证明：在零点 `s₀` 处，留数定理给出
`(s − s₀)·(ξ'/ξ − B − F) → 重数 − 1`（去心）；而展开式使该函数在
`{ξ ≠ 0}`（去心邻域的最终集，`xiFunction_eventually_ne_zero_punctured`）
上恒为零，极限唯一性给出「重数 − 1 = 0」。

因此该 target 逻辑上**蕴含**「ζ 的非平凡零点全为单零点」——这是著名
**公开问题**（与 RH 互不蕴含）。故 target 的无条件证明必须先解决零点
单性；无条件的 Hadamard 展开必须按解析重数对级数计次。 -/
theorem xi_partial_fraction_expansion_target_imp_simple_zeros
    (h : xi_partial_fraction_expansion_target)
    (hclass : ∀ s : ℂ, xiFunction s = 0 →
      RiemannHypothesis.IsNontrivialZero s ∧ s.im ≠ 0)
    {s₀ : ℂ} (hs₀ : xiFunction s₀ = 0) :
    analyticOrderNatAt xiFunction s₀ = 1 := by
  obtain ⟨B, hB⟩ := h
  obtain ⟨hz, him⟩ := hclass s₀ hs₀
  have hpunct := xiFunction_eventually_ne_zero_punctured s₀
  -- 留数侧：极限 = 重数 − 1
  have h1 := tendsto_sub_mul_logDeriv_xiFunction_of_zero hs₀
  have hF := tendsto_sub_mul_xiPairedMittagLefflerSum_of_zero hz him
  have hB0 : Filter.Tendsto (fun s => (s - s₀) * B) (𝓝[≠] s₀) (𝓝 0) := by
    have hsub0 : Filter.Tendsto (fun s : ℂ => s - s₀) (𝓝[≠] s₀) (𝓝 0) := by
      have h : Filter.Tendsto (fun s : ℂ => s - s₀) (𝓝 s₀) (𝓝 0) := by
        have h := (continuous_sub_right s₀).tendsto s₀
        simpa using h
      exact h.mono_left nhdsWithin_le_nhds
    have hc0 : Filter.Tendsto (fun _ : ℂ => B) (𝓝[≠] s₀) (𝓝 B) :=
      tendsto_const_nhds
    have h := hsub0.mul hc0
    rwa [zero_mul] at h
  have hD : Filter.Tendsto
      (fun s => (s - s₀) * (deriv xiFunction s / xiFunction s - B -
        xiPairedMittagLefflerSum s))
      (𝓝[≠] s₀) (𝓝 ((analyticOrderNatAt xiFunction s₀ : ℂ) - 1)) := by
    have h := (h1.sub hB0).sub hF
    rw [sub_zero] at h
    refine h.congr' (Filter.Eventually.of_forall fun s => ?_)
    show (s - s₀) * (deriv xiFunction s / xiFunction s) - (s - s₀) * B -
        (s - s₀) * xiPairedMittagLefflerSum s =
      (s - s₀) * (deriv xiFunction s / xiFunction s - B -
        xiPairedMittagLefflerSum s)
    ring
  -- 展开式侧：该函数在去心邻域的最终集上恒为零
  have hzero : (fun s => (s - s₀) * (deriv xiFunction s / xiFunction s - B -
      xiPairedMittagLefflerSum s)) =ᶠ[𝓝[≠] s₀] fun _ => 0 := by
    refine hpunct.mono fun z hz => ?_
    have heq := hB z hz
    show (z - s₀) * (deriv xiFunction z / xiFunction z - B -
        ∑' ρ : UpperHalfPlaneNontrivialZero, xiPairedMittagLefflerTerm z (ρ : ℂ)) =
      0
    rw [heq]
    ring
  have hlim0 : Filter.Tendsto (fun _ : ℂ => (0 : ℂ)) (𝓝[≠] s₀)
      (𝓝 ((analyticOrderNatAt xiFunction s₀ : ℂ) - 1)) :=
    hD.congr' hzero
  have huniq := tendsto_nhds_unique hlim0 tendsto_const_nhds
  have hm : (analyticOrderNatAt xiFunction s₀ : ℂ) = 1 := sub_eq_zero.mp huniq
  exact_mod_cast hm

end RiemannExplorer
