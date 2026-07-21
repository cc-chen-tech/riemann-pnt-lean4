/-
# ξ'/ξ 部分分式展开：重数加权配对 Mittag-Leffler 级数与无条件整修正（Hadamard 切片六）

本文件是「ξ'/ξ − B − Σ = 常数」论证的**重数修正版**。
`XiPartialFractionEntire.lean` 的差函数修正只在「零点全单」（公开问题）下整；
本文件把配对级数按解析重数加权：

```text
W(s) = Σ_ρ m_ξ(ρ) · ([1/(s-ρ) + 1/ρ] + [1/(s-conjρ) + 1/conjρ])
```

使 `ξ'/ξ` 与 `W` 在**每个**零点处留数都等于该点的解析重数
（`m − m = 0`，无需单零点假设），从而差函数的修正延拓
`xiWeightedEntireCorrection c` 是**无条件整函数**
（`differentiable_xiWeightedEntireCorrection`）。

## 关键新输入

1. **加权可和性**：`‖m_ρ·term‖ = m_ρ·‖term‖ ≤ (8(‖s‖+1)+2)·(m_ρ‖ρ‖⁻²)`，
   后者由 `summable_xiOrder_mul_norm_inv_sq_upperZeros` 可和。
2. **实轴排除**（切片七 `ZetaRealSegment.lean`）：ξ 的零点都在临界带
   （`xiFunction_zero_imp_isNontrivialZero`），而实轴段 `(0,1)` 上
   `ζ ≠ 0`（`riemannZeta_ofReal_ne_zero_of_Ioo`），故
   **ξ 没有实零点**（`xiFunction_zero_im_ne_zero`）——每个零点都是
   某个上半零点或其共轭。
3. **共轭保序**（`analyticOrderNatAt_xiFunction_conj`）：
   `ξ(conj z) = conj(ξ z)` 给出解析重数在共轭下不变，从而下半零点
   `conjρ` 处两侧留数同为 `m_ξ(ρ)`。

## 证明纪律

无 `sorry`/`admit`/新公理；公理审计见 `Test/XiFunctionAxiomAudit.lean`。
-/

import RiemannExplorer.XiPartialFractionEntire
import RiemannExplorer.LiZeroSumConvergence
import RiemannExplorer.ZetaRealSegment
import Mathlib.Analysis.Calculus.Deriv.Star

open Complex ComplexConjugate
open scoped BigOperators Topology

namespace RiemannExplorer

/-! ## ξ 没有实零点 -/

/-- **ξ 没有实零点**：ξ 的零点都是临界带内 ζ 的非平凡零点
（`xiFunction_zero_imp_isNontrivialZero`）；若虚部为零，则零点为
`(0,1)` 内的实数，与 `riemannZeta_ofReal_ne_zero_of_Ioo` 矛盾。 -/
theorem xiFunction_zero_im_ne_zero {s₀ : ℂ} (hξ : xiFunction s₀ = 0) : s₀.im ≠ 0 := by
  intro him
  have hz := xiFunction_zero_imp_isNontrivialZero hξ
  have hs : s₀ = (s₀.re : ℂ) := by
    rw [Complex.ext_iff, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨rfl, him⟩
  have h1 : riemannZeta (s₀.re : ℂ) = 0 := by rw [← hs]; exact hz.1
  exact riemannZeta_ofReal_ne_zero_of_Ioo hz.2.1 hz.2.2 h1

/-! ## 共轭保序：解析重数在 `s ↦ conj s` 下不变 -/

/-- `conj ∘ g ∘ conj` 在 `g` 的解析点的共轭处解析（`DifferentiableAt.conj_conj`
加上球邻域上的 `DifferentiableOn.analyticAt`）。 -/
theorem analyticAt_conj_conj {g : ℂ → ℂ} {z₀ : ℂ} (hg : AnalyticAt ℂ g z₀) :
    AnalyticAt ℂ (fun z => conj (g (conj z))) (conj z₀) := by
  have h2 : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ g z := hg.eventually_analyticAt
  rw [Metric.eventually_nhds_iff_ball] at h2
  obtain ⟨r, hr0, hr⟩ := h2
  have hd : DifferentiableOn ℂ (fun z => conj (g (conj z))) (Metric.ball (conj z₀) r) := by
    intro z hz
    have hz' : conj z ∈ Metric.ball z₀ r := by
      rw [Metric.mem_ball] at hz ⊢
      have hdist : dist (conj z) z₀ = dist z (conj z₀) := by
        have h := dist_conj_conj z (conj z₀)
        rwa [Complex.conj_conj] at h
      rwa [hdist]
    have hz2 : z = conj (conj z) := (Complex.conj_conj z).symm
    rw [hz2]
    exact (DifferentiableAt.conj_conj (hr (conj z) hz').differentiableAt).differentiableWithinAt
  exact hd.analyticAt (Metric.ball_mem_nhds _ hr0)

/-- **共轭保序**：ξ 在 `conj s₀` 的解析重数等于在 `s₀` 的解析重数。
由 `ξ(conj z) = conj(ξ z)` 把 `s₀` 处的局部因子分解 `ξ z = (z−s₀)ⁿ·g z`
共轭成 `conj s₀` 处的因子分解，两侧用 `AnalyticAt.analyticOrderAt_eq_natCast`
读出阶数相同。 -/
theorem analyticOrderNatAt_xiFunction_conj (s₀ : ℂ) :
    analyticOrderNatAt xiFunction (conj s₀) = analyticOrderNatAt xiFunction s₀ := by
  have hne_top : ∀ z : ℂ, analyticOrderAt xiFunction z ≠ ⊤ :=
    fun z ht => xiFunction_ne_eventually_zero z (analyticOrderAt_eq_top.mp ht)
  set n := analyticOrderNatAt xiFunction s₀ with hn
  have hn_eq : analyticOrderAt xiFunction s₀ = (n : ℕ∞) :=
    (Nat.cast_analyticOrderNatAt (hne_top s₀)).symm
  obtain ⟨g, hg_an, hg_ne, hg_eq⟩ :=
    ((differentiable_xiFunction.analyticAt s₀).analyticOrderAt_eq_natCast).mp hn_eq
  have hgT_an : AnalyticAt ℂ (fun z => conj (g (conj z))) (conj s₀) :=
    analyticAt_conj_conj hg_an
  have hgT_ne : (fun w => conj (g (conj w))) (conj s₀) ≠ 0 := by
    show conj (g (conj (conj s₀))) ≠ 0
    rw [Complex.conj_conj]
    exact fun h => hg_ne ((map_eq_zero (starRingEnd ℂ)).mp h)
  have hmap : Filter.Tendsto (conj : ℂ → ℂ) (𝓝 (conj s₀)) (𝓝 s₀) := by
    have h := Complex.continuous_conj.tendsto (conj s₀)
    rwa [Complex.conj_conj] at h
  have hev : ∀ᶠ z in 𝓝 (conj s₀),
      xiFunction z = (z - conj s₀) ^ n • (fun w => conj (g (conj w))) z := by
    filter_upwards [hmap.eventually hg_eq] with z hz
    show xiFunction z = (z - conj s₀) ^ n • conj (g (conj z))
    have hid : xiFunction z = conj (xiFunction (conj z)) := by
      have h := xiFunction_conj (conj z)
      rwa [Complex.conj_conj] at h
    rw [hid, hz, smul_eq_mul, map_mul, map_pow, map_sub, Complex.conj_conj, smul_eq_mul]
  have hn_eq2 : analyticOrderAt xiFunction (conj s₀) = (n : ℕ∞) :=
    ((differentiable_xiFunction.analyticAt (conj s₀)).analyticOrderAt_eq_natCast).mpr
      ⟨_, hgT_an, hgT_ne, hev⟩
  calc analyticOrderNatAt xiFunction (conj s₀)
      = (analyticOrderAt xiFunction (conj s₀)).toNat := rfl
    _ = n := by rw [hn_eq2]; rfl
    _ = analyticOrderNatAt xiFunction s₀ := hn.symm

/-! ## 重数加权配对级数：定义与可和性 -/

/-- 重数加权配对 Mittag-Leffler 项：`m_ξ(ρ)·([1/(s-ρ)+1/ρ]+[1/(s-conjρ)+1/conjρ])`。 -/
noncomputable def xiWeightedMittagLefflerTerm (s ρ : ℂ) : ℂ :=
  (↑(analyticOrderNatAt xiFunction ρ)) * xiPairedMittagLefflerTerm s ρ

/-- 重数加权配对 Mittag-Leffler 级数的和函数。 -/
noncomputable def xiWeightedMittagLefflerSum (s : ℂ) : ℂ :=
  ∑' ρ : UpperHalfPlaneNontrivialZero, xiWeightedMittagLefflerTerm s (ρ : ℂ)

/-- 加权配对项按阈值 `B` 的高/低拆分（逐点恒等式）。 -/
theorem xiWeightedMittagLefflerTerm_eq_low_add_high (B : ℝ)
    (ρ : UpperHalfPlaneNontrivialZero) (s : ℂ) :
    xiWeightedMittagLefflerTerm s (ρ : ℂ) =
      (if ‖(ρ : ℂ)‖ < B then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0) +
        (if B ≤ ‖(ρ : ℂ)‖ then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0) := by
  by_cases h : ‖(ρ : ℂ)‖ < B
  · rw [if_pos h, if_neg (not_le_of_gt h), add_zero]
  · rw [if_neg h, if_pos (le_of_not_gt h), zero_add]

/-- 低部支撑事实：原像之外低部为零（条件只含 `‖ρ‖`，与权无关）。 -/
theorem xiWeightedMittagLefflerTerm_low_eq_zero_of_not_mem (B : ℝ) (s : ℂ)
    (ρ : UpperHalfPlaneNontrivialZero)
    (hρ : ρ ∉ (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
      (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn) :
    (if ‖(ρ : ℂ)‖ < B then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0) = 0 := by
  by_cases hlt : ‖(ρ : ℂ)‖ < B
  · exfalso
    apply hρ
    rw [Finset.mem_preimage, PrimeNumberTheorem.mem_nontrivialZerosFinset]
    exact ⟨ρ.2.1, (Complex.abs_im_le_norm _).trans hlt.le⟩
  · exact if_neg hlt

/-- 低部可和（有限支撑）。 -/
theorem summable_xiWeightedMittagLefflerTerm_low (B : ℝ) (s : ℂ) :
    Summable fun ρ : UpperHalfPlaneNontrivialZero ↦
      if ‖(ρ : ℂ)‖ < B then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0 := by
  classical
  apply summable_of_ne_finset_zero
    (s := (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
      (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn)
  intro ρ hρ
  exact xiWeightedMittagLefflerTerm_low_eq_zero_of_not_mem B s ρ hρ

/-- **加权主定理（可和性）**：对每个固定的 `s : ℂ`，重数加权配对
Mittag-Leffler 项级数（无条件）收敛。
高部（`B := max 2 (2‖s‖)`）由 `norm_xiPairedMittagLefflerTerm_le` 给出
`‖m_ρ·term‖ ≤ (8(‖s‖+1)+2)·(m_ρ‖ρ‖⁻²)`，后者由
`summable_xiOrder_mul_norm_inv_sq_upperZeros` 可和。 -/
theorem summable_xiWeightedMittagLefflerTerm (s : ℂ) :
    Summable fun ρ : UpperHalfPlaneNontrivialZero ↦
      xiWeightedMittagLefflerTerm s (ρ : ℂ) := by
  classical
  set B := max 2 (2 * ‖s‖) with hB
  have hlow : Summable fun ρ : UpperHalfPlaneNontrivialZero ↦
      if ‖(ρ : ℂ)‖ < B then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0 :=
    summable_xiWeightedMittagLefflerTerm_low B s
  have hhigh : Summable fun ρ : UpperHalfPlaneNontrivialZero ↦
      if B ≤ ‖(ρ : ℂ)‖ then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0 := by
    refine Summable.of_norm_bounded
      (summable_xiOrder_mul_norm_inv_sq_upperZeros.mul_left (8 * (‖s‖ + 1) + 2))
      fun ρ => ?_
    by_cases hρB : B ≤ ‖(ρ : ℂ)‖
    · rw [if_pos hρB]
      have hρ2 : 2 ≤ ‖(ρ : ℂ)‖ := le_trans (le_max_left _ _) hρB
      have hρs : 2 * ‖s‖ ≤ ‖(ρ : ℂ)‖ := le_trans (le_max_right _ _) hρB
      have hre : |(ρ : ℂ).re| ≤ 1 := by
        have h3 := ρ.2.1.2.1
        have h4 := ρ.2.1.2.2
        rw [abs_le]
        constructor <;> linarith
      calc ‖xiWeightedMittagLefflerTerm s (ρ : ℂ)‖
          = (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) *
              ‖xiPairedMittagLefflerTerm s (ρ : ℂ)‖ := by
            rw [xiWeightedMittagLefflerTerm, norm_mul, RCLike.norm_natCast]
        _ ≤ (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) *
              ((8 * (‖s‖ + 1) + 2) * ‖(ρ : ℂ)‖⁻¹ ^ 2) :=
            mul_le_mul_of_nonneg_left (norm_xiPairedMittagLefflerTerm_le hρ2 hρs hre)
              (Nat.cast_nonneg _)
        _ = (8 * (‖s‖ + 1) + 2) *
              ((analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹ ^ 2) := by ring
    · rw [if_neg hρB, norm_zero]
      positivity
  refine (hlow.add hhigh).congr fun ρ => ?_
  exact (xiWeightedMittagLefflerTerm_eq_low_add_high B ρ s).symm

/-- 高部可和（由整体可和减低部可和）。 -/
theorem summable_xiWeightedMittagLefflerTerm_high (B : ℝ) (s : ℂ) :
    Summable fun ρ : UpperHalfPlaneNontrivialZero ↦
      if B ≤ ‖(ρ : ℂ)‖ then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0 := by
  classical
  have h : (fun ρ : UpperHalfPlaneNontrivialZero ↦
        if B ≤ ‖(ρ : ℂ)‖ then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0) =
      (fun ρ : UpperHalfPlaneNontrivialZero ↦ xiWeightedMittagLefflerTerm s (ρ : ℂ)) -
        (fun ρ : UpperHalfPlaneNontrivialZero ↦
          if ‖(ρ : ℂ)‖ < B then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0) := by
    funext ρ
    rw [Pi.sub_apply]
    by_cases hlt : ‖(ρ : ℂ)‖ < B
    · rw [if_pos hlt, if_neg (not_le_of_gt hlt), sub_self]
    · rw [if_neg hlt, if_pos (le_of_not_gt hlt), sub_zero]
  rw [h]
  exact (summable_xiWeightedMittagLefflerTerm s).sub
    (summable_xiWeightedMittagLefflerTerm_low B s)

/-- 加权级数的高/低拆分：`W = W_low + W_high`（逐点）。 -/
theorem xiWeightedMittagLefflerSum_eq_low_add_high (B : ℝ) (s : ℂ) :
    xiWeightedMittagLefflerSum s =
      (∑' ρ : UpperHalfPlaneNontrivialZero,
        if ‖(ρ : ℂ)‖ < B then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0) +
        (∑' ρ : UpperHalfPlaneNontrivialZero,
          if B ≤ ‖(ρ : ℂ)‖ then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0) := by
  rw [← Summable.tsum_add (summable_xiWeightedMittagLefflerTerm_low B s)
    (summable_xiWeightedMittagLefflerTerm_high B s)]
  exact tsum_congr fun ρ => xiWeightedMittagLefflerTerm_eq_low_add_high B ρ s

/-- 加权低部和等于有限集上的有限和（`tsum_eq_sum`）。 -/
theorem tsum_xiWeightedMittagLefflerTerm_low_eq_sum (B : ℝ) (s : ℂ) :
    (∑' ρ : UpperHalfPlaneNontrivialZero,
      if ‖(ρ : ℂ)‖ < B then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0) =
      ∑ ρ ∈ (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
          (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn,
        (if ‖(ρ : ℂ)‖ < B then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0) := by
  classical
  exact tsum_eq_sum fun ρ hρ =>
    xiWeightedMittagLefflerTerm_low_eq_zero_of_not_mem B s ρ hρ

/-! ## 逐项可微性与和函数在非零点的可微性 -/

/-- 加权配对项的逐项可微性（权不依赖 `s`，`DifferentiableAt.const_mul`）。 -/
theorem differentiableAt_xiWeightedMittagLefflerTerm {s₀ ρ : ℂ} (hρ : s₀ ≠ ρ)
    (hρc : s₀ ≠ conj ρ) :
    DifferentiableAt ℂ (fun s => xiWeightedMittagLefflerTerm s ρ) s₀ :=
  (differentiableAt_xiPairedMittagLefflerTerm hρ hρc).const_mul _

/-- 加权高部和在开球 `ball s₀ 1` 上复可微（Weierstrass 逐项微分，
主项 `(8(‖s₀‖+2)+2)·(m_ρ‖ρ‖⁻²)` 对零点可和）。 -/
theorem differentiableOn_tsum_xiWeightedMittagLefflerTerm_high (s₀ : ℂ) :
    DifferentiableOn ℂ
      (fun s => ∑' ρ : UpperHalfPlaneNontrivialZero,
        if max 2 (2 * (‖s₀‖ + 1)) ≤ ‖(ρ : ℂ)‖ then
          xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0)
      (Metric.ball s₀ 1) := by
  classical
  set B := max 2 (2 * (‖s₀‖ + 1)) with hB
  have hball : ∀ s ∈ Metric.ball s₀ 1, ‖s‖ < ‖s₀‖ + 1 := by
    intro s hs
    rw [Metric.mem_ball, dist_eq_norm] at hs
    have h := norm_sub_norm_le s s₀
    have hs0 := norm_nonneg s
    linarith
  refine differentiableOn_tsum_of_summable_norm
    (u := fun ρ : UpperHalfPlaneNontrivialZero =>
      (8 * (‖s₀‖ + 2) + 2) *
        ((analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹ ^ 2))
    (summable_xiOrder_mul_norm_inv_sq_upperZeros.mul_left _) ?_ Metric.isOpen_ball ?_
  · intro ρ
    by_cases hρB : B ≤ ‖(ρ : ℂ)‖
    · have hFρ : (fun s => if B ≤ ‖(ρ : ℂ)‖ then
          xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0) =
          fun s => xiWeightedMittagLefflerTerm s (ρ : ℂ) := funext fun s => if_pos hρB
      rw [hFρ]
      intro s hs
      have hsn : ‖s‖ < ‖(ρ : ℂ)‖ := by
        have h1 := hball s hs
        have h2 : 2 * (‖s₀‖ + 1) ≤ B := le_max_right _ _
        have hs0 := norm_nonneg s
        linarith
      have hsρ : s ≠ (ρ : ℂ) := fun h => by rw [h] at hsn; exact lt_irrefl _ hsn
      have hsρc : s ≠ conj (ρ : ℂ) := fun h => by
        have h3 : ‖s‖ = ‖(ρ : ℂ)‖ := by rw [h, Complex.norm_conj]
        linarith
      exact (differentiableAt_xiWeightedMittagLefflerTerm hsρ hsρc).differentiableWithinAt
    · have hFρ : (fun s => if B ≤ ‖(ρ : ℂ)‖ then
          xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0) =
          fun _ => 0 := funext fun s => if_neg hρB
      rw [hFρ]
      exact differentiableOn_const _
  · intro ρ s hs
    by_cases hρB : B ≤ ‖(ρ : ℂ)‖
    · rw [if_pos hρB]
      have h1 := hball s hs
      have hρ2 : 2 ≤ ‖(ρ : ℂ)‖ := le_trans (le_max_left _ _) hρB
      have hρs : 2 * ‖s‖ ≤ ‖(ρ : ℂ)‖ := by
        have h2 : 2 * (‖s₀‖ + 1) ≤ B := le_max_right _ _
        linarith
      have hre : |(ρ : ℂ).re| ≤ 1 := by
        have h3 := ρ.2.1.2.1
        have h4 := ρ.2.1.2.2
        rw [abs_le]
        constructor <;> linarith
      calc ‖xiWeightedMittagLefflerTerm s (ρ : ℂ)‖
          = (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) *
              ‖xiPairedMittagLefflerTerm s (ρ : ℂ)‖ := by
            rw [xiWeightedMittagLefflerTerm, norm_mul, RCLike.norm_natCast]
        _ ≤ (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) *
              ((8 * (‖s‖ + 1) + 2) * ‖(ρ : ℂ)‖⁻¹ ^ 2) :=
            mul_le_mul_of_nonneg_left (norm_xiPairedMittagLefflerTerm_le hρ2 hρs hre)
              (Nat.cast_nonneg _)
        _ = (8 * (‖s‖ + 1) + 2) *
              ((analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹ ^ 2) := by ring
        _ ≤ (8 * (‖s₀‖ + 2) + 2) *
              ((analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹ ^ 2) :=
            mul_le_mul_of_nonneg_right (by linarith)
              (mul_nonneg (Nat.cast_nonneg _) (by positivity))
    · rw [if_neg hρB, norm_zero]
      positivity

/-- **加权主定理（可微性）**：加权和函数在每个满足 `ξ(s₀) ≠ 0` 的点
`s₀` 处复可微（论证与未加权版相同：低部有限和逐项可微，
高部球上 `DifferentiableOn`）。 -/
theorem differentiableAt_tsum_xiWeightedMittagLefflerTerm {s₀ : ℂ}
    (hξ : xiFunction s₀ ≠ 0) :
    DifferentiableAt ℂ (fun s => xiWeightedMittagLefflerSum s) s₀ := by
  classical
  set B := max 2 (2 * (‖s₀‖ + 1)) with hB
  set F₀ := (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
      (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn
  have hsρ : ∀ ρ : UpperHalfPlaneNontrivialZero, s₀ ≠ (ρ : ℂ) := by
    intro ρ h
    apply hξ
    rw [h]
    exact (xiFunction_eq_zero_iff_isNontrivialZero ρ.2.1.2.1 ρ.2.1.2.2).mpr ρ.2.1
  have hsρc : ∀ ρ : UpperHalfPlaneNontrivialZero, s₀ ≠ conj (ρ : ℂ) := by
    intro ρ h
    apply hξ
    rw [h, xiFunction_conj,
      (xiFunction_eq_zero_iff_isNontrivialZero ρ.2.1.2.1 ρ.2.1.2.2).mpr ρ.2.1]
    exact map_zero _
  have hdecomp : (fun s => xiWeightedMittagLefflerSum s) =
      (fun s => ∑' ρ : UpperHalfPlaneNontrivialZero,
        if ‖(ρ : ℂ)‖ < B then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0) +
        (fun s => ∑' ρ : UpperHalfPlaneNontrivialZero,
          if B ≤ ‖(ρ : ℂ)‖ then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0) := by
    funext s
    simp only [Pi.add_apply]
    exact xiWeightedMittagLefflerSum_eq_low_add_high B s
  rw [hdecomp]
  refine DifferentiableAt.add ?_ ?_
  · rw [show (fun s => ∑' ρ : UpperHalfPlaneNontrivialZero,
          if ‖(ρ : ℂ)‖ < B then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0) =
        fun s => ∑ ρ ∈ F₀,
          (if ‖(ρ : ℂ)‖ < B then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0)
      from funext fun s => tsum_xiWeightedMittagLefflerTerm_low_eq_sum B s]
    rw [show (fun s => ∑ ρ ∈ F₀,
          (if ‖(ρ : ℂ)‖ < B then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0)) =
        (∑ ρ ∈ F₀, fun s =>
          if ‖(ρ : ℂ)‖ < B then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0)
      from funext fun s => by rw [Finset.sum_apply]]
    refine DifferentiableAt.sum fun ρ _ => ?_
    by_cases hlt : ‖(ρ : ℂ)‖ < B
    · rw [show (fun s => if ‖(ρ : ℂ)‖ < B then
            xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0) =
          fun s => xiWeightedMittagLefflerTerm s (ρ : ℂ) from funext fun s => if_pos hlt]
      exact differentiableAt_xiWeightedMittagLefflerTerm (hsρ ρ) (hsρc ρ)
    · rw [show (fun s => if ‖(ρ : ℂ)‖ < B then
            xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0) =
          fun _ => 0 from funext fun s => if_neg hlt]
      exact differentiableAt_const _
  · exact (differentiableOn_tsum_xiWeightedMittagLefflerTerm_high s₀).differentiableAt
      (Metric.ball_mem_nhds s₀ one_pos)

/-- 与 `differentiableAt_tsum_xiWeightedMittagLefflerTerm` 同一论证，
但把「避开所有上半零点及其共轭」作为显式假设。 -/
theorem differentiableAt_tsum_xiWeightedMittagLefflerTerm_of_ne {s₀ : ℂ}
    (hsρ : ∀ ρ : UpperHalfPlaneNontrivialZero, s₀ ≠ (ρ : ℂ))
    (hsρc : ∀ ρ : UpperHalfPlaneNontrivialZero, s₀ ≠ conj (ρ : ℂ)) :
    DifferentiableAt ℂ (fun s => xiWeightedMittagLefflerSum s) s₀ := by
  classical
  set B := max 2 (2 * (‖s₀‖ + 1)) with hB
  set F₀ := (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
      (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn
  have hdecomp : (fun s => xiWeightedMittagLefflerSum s) =
      (fun s => ∑' ρ : UpperHalfPlaneNontrivialZero,
        if ‖(ρ : ℂ)‖ < B then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0) +
        (fun s => ∑' ρ : UpperHalfPlaneNontrivialZero,
          if B ≤ ‖(ρ : ℂ)‖ then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0) := by
    funext s
    simp only [Pi.add_apply]
    exact xiWeightedMittagLefflerSum_eq_low_add_high B s
  rw [hdecomp]
  refine DifferentiableAt.add ?_ ?_
  · rw [show (fun s => ∑' ρ : UpperHalfPlaneNontrivialZero,
          if ‖(ρ : ℂ)‖ < B then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0) =
        fun s => ∑ ρ ∈ F₀,
          (if ‖(ρ : ℂ)‖ < B then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0)
      from funext fun s => tsum_xiWeightedMittagLefflerTerm_low_eq_sum B s]
    rw [show (fun s => ∑ ρ ∈ F₀,
          (if ‖(ρ : ℂ)‖ < B then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0)) =
        (∑ ρ ∈ F₀, fun s =>
          if ‖(ρ : ℂ)‖ < B then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0)
      from funext fun s => by rw [Finset.sum_apply]]
    refine DifferentiableAt.sum fun ρ _ => ?_
    by_cases hlt : ‖(ρ : ℂ)‖ < B
    · rw [show (fun s => if ‖(ρ : ℂ)‖ < B then
            xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0) =
          fun s => xiWeightedMittagLefflerTerm s (ρ : ℂ) from funext fun s => if_pos hlt]
      exact differentiableAt_xiWeightedMittagLefflerTerm (hsρ ρ) (hsρc ρ)
    · rw [show (fun s => if ‖(ρ : ℂ)‖ < B then
            xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0) =
          fun _ => 0 from funext fun s => if_neg hlt]
      exact differentiableAt_const _
  · exact (differentiableOn_tsum_xiWeightedMittagLefflerTerm_high s₀).differentiableAt
      (Metric.ball_mem_nhds s₀ one_pos)

/-- 加权和函数在开集 `{s | ξ s ≠ 0}` 上 `DifferentiableOn`。 -/
theorem differentiableOn_tsum_xiWeightedMittagLefflerTerm :
    DifferentiableOn ℂ xiWeightedMittagLefflerSum {s : ℂ | xiFunction s ≠ 0} :=
  fun _s hs => (differentiableAt_tsum_xiWeightedMittagLefflerTerm hs).differentiableWithinAt

/-- 加权差函数 `D(s) = ξ'(s)/ξ(s) - c - W(s)` 在 `ξ` 非零点开集上复可微。 -/
theorem differentiableOn_logDeriv_xiFunction_sub_xiWeightedMittagLefflerSum (c : ℂ) :
    DifferentiableOn ℂ
      (fun s => deriv xiFunction s / xiFunction s - c - xiWeightedMittagLefflerSum s)
      {s : ℂ | xiFunction s ≠ 0} := by
  have hderiv : DifferentiableOn ℂ (deriv xiFunction) {s : ℂ | xiFunction s ≠ 0} :=
    ((differentiable_xiFunction.differentiableOn (s := Set.univ)).deriv
      isOpen_univ).mono (Set.subset_univ _)
  exact (((hderiv.div differentiable_xiFunction.differentiableOn
    fun s hs => hs).sub (differentiableOn_const c)).sub
    differentiableOn_tsum_xiWeightedMittagLefflerTerm)

/-! ## 加权级数的共轭对称与留数 -/

/-- 加权配对项关于 `s ↦ conj s` 的共轭对称性（权为自然数，共轭不变）。 -/
theorem xiWeightedMittagLefflerTerm_conj (s ρ : ℂ) :
    xiWeightedMittagLefflerTerm (conj s) ρ = conj (xiWeightedMittagLefflerTerm s ρ) := by
  rw [xiWeightedMittagLefflerTerm, xiWeightedMittagLefflerTerm, map_mul, map_natCast,
    xiPairedMittagLefflerTerm_conj]

/-- 加权和函数的共轭对称性：`W(conj s) = conj (W s)`。 -/
theorem xiWeightedMittagLefflerSum_conj (s : ℂ) :
    xiWeightedMittagLefflerSum (conj s) = conj (xiWeightedMittagLefflerSum s) := by
  unfold xiWeightedMittagLefflerSum
  rw [Complex.conj_tsum]
  exact tsum_congr fun ρ => xiWeightedMittagLefflerTerm_conj s (ρ : ℂ)

/-- 加权配对项在自身零点处的留数：`(s - ρ₀)·(m₀·term) → m₀`（未加权
留数 1 的 `Tendsto.const_mul`）。 -/
theorem tendsto_sub_mul_xiWeightedMittagLefflerTerm_self
    (ρ₀ : UpperHalfPlaneNontrivialZero) :
    Filter.Tendsto (fun s => (s - (ρ₀ : ℂ)) * xiWeightedMittagLefflerTerm s (ρ₀ : ℂ))
      (𝓝[≠] (ρ₀ : ℂ)) (𝓝 ↑(analyticOrderNatAt xiFunction (ρ₀ : ℂ))) := by
  have h := (tendsto_sub_mul_xiPairedMittagLefflerTerm_self ρ₀).const_mul
    (↑(analyticOrderNatAt xiFunction (ρ₀ : ℂ)))
  rw [mul_one] at h
  refine h.congr' (Filter.Eventually.of_forall fun s => ?_)
  show (↑(analyticOrderNatAt xiFunction (ρ₀ : ℂ))) *
      ((s - (ρ₀ : ℂ)) * xiPairedMittagLefflerTerm s (ρ₀ : ℂ)) =
    (s - (ρ₀ : ℂ)) * xiWeightedMittagLefflerTerm s (ρ₀ : ℂ)
  rw [xiWeightedMittagLefflerTerm]
  ring

/-- 其他零点项：加权后乘 `(s - ρ₀)` 极限仍为 0。 -/
theorem tendsto_sub_mul_xiWeightedMittagLefflerTerm_of_ne
    (ρ₀ ρ : UpperHalfPlaneNontrivialZero) (hρ : ρ ≠ ρ₀) :
    Filter.Tendsto (fun s => (s - (ρ₀ : ℂ)) * xiWeightedMittagLefflerTerm s (ρ : ℂ))
      (𝓝 (ρ₀ : ℂ)) (𝓝 0) := by
  have h := (tendsto_sub_mul_xiPairedMittagLefflerTerm_of_ne ρ₀ ρ hρ).const_mul
    (↑(analyticOrderNatAt xiFunction (ρ : ℂ)))
  rw [mul_zero] at h
  refine h.congr' (Filter.Eventually.of_forall fun s => ?_)
  show (↑(analyticOrderNatAt xiFunction (ρ : ℂ))) *
      ((s - (ρ₀ : ℂ)) * xiPairedMittagLefflerTerm s (ρ : ℂ)) =
    (s - (ρ₀ : ℂ)) * xiWeightedMittagLefflerTerm s (ρ : ℂ)
  rw [xiWeightedMittagLefflerTerm]
  ring

/-- **留数定理（加权级数侧，上半零点）**：加权和函数在每个上半平面零点
`ρ₀` 处留数等于 `ξ` 在该点的解析重数 `m₀`：去心极限
`(s - ρ₀)·W(s) → m₀`。 -/
theorem tendsto_sub_mul_xiWeightedMittagLefflerSum (ρ₀ : UpperHalfPlaneNontrivialZero) :
    Filter.Tendsto (fun s => (s - (ρ₀ : ℂ)) * xiWeightedMittagLefflerSum s)
      (𝓝[≠] (ρ₀ : ℂ)) (𝓝 ↑(analyticOrderNatAt xiFunction (ρ₀ : ℂ))) := by
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
  have hcontHigh : ContinuousAt (fun s => ∑' ρ : UpperHalfPlaneNontrivialZero,
        (if B ≤ ‖(ρ : ℂ)‖ then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0)) (ρ₀ : ℂ) := by
    have hd := differentiableOn_tsum_xiWeightedMittagLefflerTerm_high (ρ₀ : ℂ)
    exact hd.continuousOn.continuousAt (Metric.ball_mem_nhds _ one_pos)
  have hdecomp : (fun s => (s - (ρ₀ : ℂ)) * xiWeightedMittagLefflerSum s) =
      fun s => (s - (ρ₀ : ℂ)) * xiWeightedMittagLefflerTerm s (ρ₀ : ℂ) +
        ((s - (ρ₀ : ℂ)) * ∑ ρ ∈ (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
              (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn
              |>.erase ρ₀,
            (if ‖(ρ : ℂ)‖ < B then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0) +
          (s - (ρ₀ : ℂ)) * ∑' ρ : UpperHalfPlaneNontrivialZero,
            (if B ≤ ‖(ρ : ℂ)‖ then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0)) := by
    funext s
    rw [xiWeightedMittagLefflerSum_eq_low_add_high B s,
      tsum_xiWeightedMittagLefflerTerm_low_eq_sum B s,
      ← Finset.add_sum_erase _ _ hmem, if_pos hltB]
    ring
  rw [hdecomp]
  have hA := tendsto_sub_mul_xiWeightedMittagLefflerTerm_self ρ₀
  have hB' : Filter.Tendsto (fun s => (s - (ρ₀ : ℂ)) *
        ∑ ρ ∈ (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
            (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn
            |>.erase ρ₀,
          (if ‖(ρ : ℂ)‖ < B then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0))
      (𝓝 (ρ₀ : ℂ)) (𝓝 0) := by
    rw [show (fun s => (s - (ρ₀ : ℂ)) *
          ∑ ρ ∈ (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
              (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn
              |>.erase ρ₀,
            (if ‖(ρ : ℂ)‖ < B then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0)) =
        fun s => ∑ ρ ∈ (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
              (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn
              |>.erase ρ₀,
          (s - (ρ₀ : ℂ)) * (if ‖(ρ : ℂ)‖ < B then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0)
      from funext fun s => Finset.mul_sum _ _ _]
    have hsum : Filter.Tendsto
        (fun s => ∑ ρ ∈ (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
              (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn
              |>.erase ρ₀,
          (s - (ρ₀ : ℂ)) * (if ‖(ρ : ℂ)‖ < B then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0))
        (𝓝 (ρ₀ : ℂ))
        (𝓝 (∑ _ρ ∈ (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
              (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn
              |>.erase ρ₀, (0 : ℂ))) := by
      refine tendsto_finset_sum _ fun ρ hρmem => ?_
      have hρne : ρ ≠ ρ₀ := (Finset.mem_erase.mp hρmem).1
      by_cases hlt : ‖(ρ : ℂ)‖ < B
      · rw [show (fun s => (s - (ρ₀ : ℂ)) *
            (if ‖(ρ : ℂ)‖ < B then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0)) =
          fun s => (s - (ρ₀ : ℂ)) * xiWeightedMittagLefflerTerm s (ρ : ℂ)
          from funext fun s => by rw [if_pos hlt]]
        exact tendsto_sub_mul_xiWeightedMittagLefflerTerm_of_ne ρ₀ ρ hρne
      · rw [show (fun s => (s - (ρ₀ : ℂ)) *
            (if ‖(ρ : ℂ)‖ < B then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0)) =
          fun _ => 0 from funext fun s => by rw [if_neg hlt, mul_zero]]
        exact tendsto_const_nhds
    simpa using hsum
  have hC : Filter.Tendsto (fun s => (s - (ρ₀ : ℂ)) * ∑' ρ : UpperHalfPlaneNontrivialZero,
        (if B ≤ ‖(ρ : ℂ)‖ then xiWeightedMittagLefflerTerm s (ρ : ℂ) else 0))
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

/-- 加权级数在上半零点的共轭点处留数亦为该点的解析重数（经共轭映射复合）。 -/
theorem tendsto_sub_mul_xiWeightedMittagLefflerSum_conj
    (ρ₀ : UpperHalfPlaneNontrivialZero) :
    Filter.Tendsto (fun s => (s - conj (ρ₀ : ℂ)) * xiWeightedMittagLefflerSum s)
      (𝓝[≠] (conj (ρ₀ : ℂ))) (𝓝 ↑(analyticOrderNatAt xiFunction (ρ₀ : ℂ))) := by
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
  have h1 := (tendsto_sub_mul_xiWeightedMittagLefflerSum ρ₀).comp hmap
  have h2 := (Complex.continuous_conj.tendsto
    (↑(analyticOrderNatAt xiFunction (ρ₀ : ℂ)))).comp h1
  rw [map_natCast] at h2
  refine h2.congr' (Filter.Eventually.of_forall fun s => ?_)
  show conj ((conj s - (ρ₀ : ℂ)) * xiWeightedMittagLefflerSum (conj s)) =
    (s - conj (ρ₀ : ℂ)) * xiWeightedMittagLefflerSum s
  rw [map_mul, map_sub, Complex.conj_conj, xiWeightedMittagLefflerSum_conj,
    Complex.conj_conj]

/-- **留数定理（加权级数侧，任意零点）**：加权和函数在 ζ 的**任意**非平凡
零点（虚部非零）`s₀` 处留数等于 `ξ` 在 `s₀` 的解析重数。
下半平面零点经共轭化到上半平面，重数由
`analyticOrderNatAt_xiFunction_conj` 保持。 -/
theorem tendsto_sub_mul_xiWeightedMittagLefflerSum_of_zero {s₀ : ℂ}
    (hz : RiemannHypothesis.IsNontrivialZero s₀) (him : s₀.im ≠ 0) :
    Filter.Tendsto (fun s => (s - s₀) * xiWeightedMittagLefflerSum s)
      (𝓝[≠] s₀) (𝓝 ↑(analyticOrderNatAt xiFunction s₀)) := by
  rcases lt_or_gt_of_ne him with hlt | hgt
  · have h0' : 0 < (conj s₀).re := by rw [Complex.conj_re]; exact hz.2.1
    have h1' : (conj s₀).re < 1 := by rw [Complex.conj_re]; exact hz.2.2
    have hξs₀ : xiFunction s₀ = 0 :=
      (xiFunction_eq_zero_iff hz.2.1 hz.2.2).mpr hz.1
    have hξc : xiFunction (conj s₀) = 0 := by
      rw [xiFunction_conj, hξs₀, map_zero]
    have hζc : riemannZeta (conj s₀) = 0 := (xiFunction_eq_zero_iff h0' h1').mp hξc
    have himc : 0 < (conj s₀).im := by rw [Complex.conj_im]; linarith
    have h3 := tendsto_sub_mul_xiWeightedMittagLefflerSum_conj
      ⟨conj s₀, ⟨⟨hζc, h0', h1'⟩, himc⟩⟩
    rwa [Complex.conj_conj, analyticOrderNatAt_xiFunction_conj] at h3
  · exact tendsto_sub_mul_xiWeightedMittagLefflerSum ⟨s₀, hz, hgt⟩

/-- **加权差函数留数消失（无条件）**：任意非平凡零点（虚部非零）处，
`(s − s₀)·(ξ'/ξ − c − W) → m − m = 0`。无需单零点假设——这正是
重数加权的关键作用。 -/
theorem tendsto_sub_mul_logDeriv_sub_const_sub_xiWeightedMittagLefflerSum_of_zero
    (c : ℂ) {s₀ : ℂ}
    (hz : RiemannHypothesis.IsNontrivialZero s₀) (him : s₀.im ≠ 0) :
    Filter.Tendsto
      (fun s => (s - s₀) * (deriv xiFunction s / xiFunction s - c -
        xiWeightedMittagLefflerSum s))
      (𝓝[≠] s₀) (𝓝 0) := by
  have h1 := tendsto_sub_mul_logDeriv_xiFunction_of_zero
    ((xiFunction_eq_zero_iff hz.2.1 hz.2.2).mpr hz.1)
  have h2 := tendsto_sub_mul_xiWeightedMittagLefflerSum_of_zero hz him
  have h12 := h1.sub h2
  rw [sub_self] at h12
  have hsub0 : Filter.Tendsto (fun s : ℂ => s - s₀) (𝓝[≠] s₀) (𝓝 0) := by
    have h : Filter.Tendsto (fun s : ℂ => s - s₀) (𝓝 s₀) (𝓝 0) := by
      have h := (continuous_sub_right s₀).tendsto s₀
      simpa using h
    exact h.mono_left nhdsWithin_le_nhds
  have hc : Filter.Tendsto (fun s => (s - s₀) * c) (𝓝[≠] s₀) (𝓝 0) := by
    have hc0 : Filter.Tendsto (fun _ : ℂ => c) (𝓝[≠] s₀) (𝓝 c) := tendsto_const_nhds
    have h := hsub0.mul hc0
    rwa [zero_mul] at h
  have h3 := h12.sub hc
  rw [sub_zero] at h3
  refine h3.congr' (Filter.Eventually.of_forall fun s => ?_)
  show (s - s₀) * (deriv xiFunction s / xiFunction s) -
      (s - s₀) * xiWeightedMittagLefflerSum s - (s - s₀) * c =
    (s - s₀) * (deriv xiFunction s / xiFunction s - c - xiWeightedMittagLefflerSum s)
  ring

/-! ## 无条件整修正 -/

/-- 加权差函数 `ξ'/ξ − c − W` 的**整函数延拓修正**：在非零点等于差函数
本身，在零点处取去心极限。 -/
noncomputable def xiWeightedEntireCorrection (c : ℂ) (s : ℂ) : ℂ :=
  Filter.limUnder (𝓝[≠] s)
    (fun z => deriv xiFunction z / xiFunction z - c - xiWeightedMittagLefflerSum z)

/-- 在非零点处，加权修正函数等于差函数本身。 -/
theorem xiWeightedEntireCorrection_apply_of_ne_zero (c : ℂ) {s : ℂ}
    (hs : xiFunction s ≠ 0) :
    xiWeightedEntireCorrection c s =
      deriv xiFunction s / xiFunction s - c - xiWeightedMittagLefflerSum s := by
  have hopen : IsOpen {z : ℂ | xiFunction z ≠ 0} :=
    isOpen_compl_singleton.preimage differentiable_xiFunction.continuous
  have hdiff := (differentiableOn_logDeriv_xiFunction_sub_xiWeightedMittagLefflerSum
    c).differentiableAt (hopen.mem_nhds hs)
  exact (hdiff.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq

/-- **Gluing（无条件整函数延拓）**：加权差函数 `ξ'/ξ − c − W` 的修正延拓
是整函数。非零点处修正与差函数局部相等；零点 `s` 处，重数匹配
（`m − m`，经 `xiFunction_zero_imp_isNontrivialZero` 与
`xiFunction_zero_im_ne_zero` 覆盖全部零点）给出 `(z − s)·D z → 0`，
孤立零点性质给出可微的去心球，由可去奇点定理
`differentiableOn_update_limUnder_of_isLittleO` 粘合。 -/
theorem differentiable_xiWeightedEntireCorrection (c : ℂ) :
    Differentiable ℂ (xiWeightedEntireCorrection c) := by
  intro s
  by_cases hs : xiFunction s = 0
  · have hz := xiFunction_zero_imp_isNontrivialZero hs
    have him := xiFunction_zero_im_ne_zero hs
    have hne_top : analyticOrderAt xiFunction s ≠ ⊤ :=
      fun ht => xiFunction_ne_eventually_zero s (analyticOrderAt_eq_top.mp ht)
    have hne : ¬ ∀ᶠ z in 𝓝 s, xiFunction z = 0 :=
      fun h => hne_top (analyticOrderAt_eq_top.mpr h)
    have hpunct : ¬ ∃ᶠ z in 𝓝[≠] s, xiFunction z = 0 :=
      fun hfreq => hne ((differentiable_xiFunction.analyticAt
        s).frequently_zero_iff_eventually_zero.mp hfreq)
    rw [Filter.not_frequently, eventually_nhdsWithin_iff,
      Metric.eventually_nhds_iff_ball] at hpunct
    obtain ⟨R, hR0, hR⟩ := hpunct
    have hDball : DifferentiableOn ℂ
        (fun z => deriv xiFunction z / xiFunction z - c -
          xiWeightedMittagLefflerSum z)
        (Metric.ball s R \ {s}) :=
      (differentiableOn_logDeriv_xiFunction_sub_xiWeightedMittagLefflerSum c).mono
        (fun z hz => hR z hz.1 hz.2)
    have hres :=
      tendsto_sub_mul_logDeriv_sub_const_sub_xiWeightedMittagLefflerSum_of_zero c hz him
    have hsub0 : Filter.Tendsto (fun z : ℂ => z - s) (𝓝[≠] s) (𝓝 0) := by
      have h : Filter.Tendsto (fun z : ℂ => z - s) (𝓝 s) (𝓝 0) := by
        have h := (continuous_sub_right s).tendsto s
        simpa using h
      exact h.mono_left nhdsWithin_le_nhds
    have hconst : Filter.Tendsto
        (fun z => (z - s) * (deriv xiFunction s / xiFunction s - c -
          xiWeightedMittagLefflerSum s)) (𝓝[≠] s) (𝓝 0) := by
      have hc0 : Filter.Tendsto
          (fun _ : ℂ => deriv xiFunction s / xiFunction s - c -
            xiWeightedMittagLefflerSum s) (𝓝[≠] s)
          (𝓝 (deriv xiFunction s / xiFunction s - c -
            xiWeightedMittagLefflerSum s)) :=
        tendsto_const_nhds
      have h := hsub0.mul hc0
      rwa [zero_mul] at h
    have hDs := hres.sub hconst
    rw [sub_zero] at hDs
    have hquot : Filter.Tendsto
        (fun z => ((deriv xiFunction z / xiFunction z - c -
          xiWeightedMittagLefflerSum z) -
            (deriv xiFunction s / xiFunction s - c -
              xiWeightedMittagLefflerSum s)) / (z - s)⁻¹)
        (𝓝[≠] s) (𝓝 0) :=
      hDs.congr' (Filter.Eventually.of_forall fun z => by
        show (z - s) * (deriv xiFunction z / xiFunction z - c -
            xiWeightedMittagLefflerSum z) -
            (z - s) * (deriv xiFunction s / xiFunction s - c -
              xiWeightedMittagLefflerSum s) =
          ((deriv xiFunction z / xiFunction z - c -
            xiWeightedMittagLefflerSum z) -
              (deriv xiFunction s / xiFunction s - c -
                xiWeightedMittagLefflerSum s)) / (z - s)⁻¹
        rw [div_inv_eq_mul]; ring)
    have ho : (fun z => (deriv xiFunction z / xiFunction z - c -
        xiWeightedMittagLefflerSum z) -
          (deriv xiFunction s / xiFunction s - c - xiWeightedMittagLefflerSum s))
        =o[𝓝[≠] s] fun z => (z - s)⁻¹ :=
      (Asymptotics.isLittleO_iff_tendsto fun z hz0 => by
        have hzs : z = s := sub_eq_zero.mp (inv_eq_zero.mp hz0)
        rw [hzs, sub_self]).mpr hquot
    have hUpd := differentiableOn_update_limUnder_of_isLittleO
      (Metric.ball_mem_nhds s hR0) hDball ho
    have hEq : ∀ z ∈ Metric.ball s R,
        xiWeightedEntireCorrection c z =
          Function.update
            (fun w => deriv xiFunction w / xiFunction w - c -
              xiWeightedMittagLefflerSum w) s
            (Filter.limUnder (𝓝[≠] s)
              (fun w => deriv xiFunction w / xiFunction w - c -
                xiWeightedMittagLefflerSum w)) z := by
      intro z hzb
      by_cases hzs : z = s
      · rw [hzs, Function.update_self]
        rfl
      · rw [Function.update_of_ne hzs]
        exact xiWeightedEntireCorrection_apply_of_ne_zero c
          (hR z hzb hzs)
    have hev : xiWeightedEntireCorrection c =ᶠ[𝓝 s]
        Function.update
          (fun w => deriv xiFunction w / xiFunction w - c -
            xiWeightedMittagLefflerSum w) s
          (Filter.limUnder (𝓝[≠] s)
            (fun w => deriv xiFunction w / xiFunction w - c -
              xiWeightedMittagLefflerSum w)) :=
      Filter.eventually_of_mem (Metric.ball_mem_nhds s hR0) hEq
    exact (hUpd.differentiableAt (Metric.ball_mem_nhds s hR0)).congr_of_eventuallyEq hev
  · have hopen : IsOpen {z : ℂ | xiFunction z ≠ 0} :=
      isOpen_compl_singleton.preimage differentiable_xiFunction.continuous
    have hev : xiWeightedEntireCorrection c =ᶠ[𝓝 s]
        (fun z => deriv xiFunction z / xiFunction z - c -
          xiWeightedMittagLefflerSum z) :=
      Filter.eventually_of_mem (hopen.mem_nhds hs) fun z hz =>
        xiWeightedEntireCorrection_apply_of_ne_zero c hz
    exact ((differentiableOn_logDeriv_xiFunction_sub_xiWeightedMittagLefflerSum
      c).differentiableAt (hopen.mem_nhds hs)).congr_of_eventuallyEq hev

end RiemannExplorer
