/-
# 加权整修正函数的常数性（Stage A：E ≡ 0 ⇒ 重数加权部分分式展开）

本文件完成 `xi_weighted_partial_fraction_expansion_of_const_correction`
（XiPartialFractionWeighted.lean）所归约到的唯一硬核心：证明整函数

```text
E(s) := xiWeightedEntireCorrection (ξ'(0)/ξ(0)) s
```

恒为零，从而闭合**重数加权部分分式展开**：

```text
∀ s, ξ s ≠ 0 → ξ'(s)/ξ(s) = ξ'(0)/ξ(0) + Σ_ρ m_ξ(ρ)·pairedTerm(s, ρ)
```

## 方法

1. **E 的 O(log² R) 界**（`norm_xiWeightedEntireCorrection_le`）：
   在 `ball 0 (R/2)` 上分解
   `E = [ξ'/ξ − finsum_R] + [finsum_R − W_low] + [−W_high] − c₀`。
   第一括号是 C1 主定理 `xi_logDeriv_sub_finsum_divisor_le`；
   `finsum_R − W_low` 经**配对转换**（上半平面零点集
   `xiUpperZerosFinset R` 与其共轭像之并 = `nontrivialZerosFinset R`）
   化为边界圆弧项（`‖u‖ = R`，Jensen 计数 `xiZeroDiscMult_sum_le` 吸收）
   与常数项 `u⁻¹ + (conj u)⁻¹ = 2·Re(u⁻¹)`（头部计数界
   `exists_upperZeros_weighted_norm_inv_le_log_sq`）；
   `W_high` 由逐项界 `norm_xiPairedMittagLefflerTerm_le` 与尾部计数界
   `exists_upperZeros_tail_weighted_norm_inv_sq_le` 给出 `O(log R)`。
   零点处由 `xiFunction_ne_eventually_zero` 稠密逼近延拓。
2. **次线性 ⇒ 导数恒零**（`deriv_xiWeightedEntireCorrection_eq_zero`）：
   Cauchy 估计 `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`
   在半径 `r` 的圆上取 `R_w = 2(‖z‖+r)+8`，得
   `‖E' z‖ ≤ C_E(1+log(2(‖z‖+r)+8))²/r → 0`（`r → ∞`）。
3. **常数性**：`is_const_of_deriv_eq_zero` + `xiWeightedEntireCorrection_zero`
   给出 `E ≡ 0`，代入归约定理即得展开式
   `xi_weighted_partial_fraction_expansion`。

全部无条件、无 sorry。
-/

import RiemannExplorer.XiPartialFractionWeighted
import RiemannExplorer.XiLogDerivDisc
import RiemannExplorer.XiZeroCountingBounds

open Complex ComplexConjugate Metric Filter Real
open scoped BigOperators Topology

namespace RiemannExplorer

/-! ## 上半平面零点有限集与共轭配对分解 -/

/-- 高度 `≤ B` 且虚部为正的 ζ 非平凡零点有限集。 -/
noncomputable def xiUpperZerosFinset (B : ℝ) : Finset ℂ :=
  (PrimeNumberTheorem.nontrivialZerosFinset B).filter fun u => 0 < u.im

lemma mem_xiUpperZerosFinset {B : ℝ} {u : ℂ} :
    u ∈ xiUpperZerosFinset B ↔
      RiemannHypothesis.IsNontrivialZero u ∧ |u.im| ≤ B ∧ 0 < u.im := by
  rw [xiUpperZerosFinset, Finset.mem_filter, PrimeNumberTheorem.mem_nontrivialZerosFinset]
  tauto

/-- ζ 非平凡零点的共轭仍为非平凡零点（经 ξ 的共轭对称 `xiFunction_conj`）。 -/
theorem isNontrivialZero_conj {u : ℂ} (h : RiemannHypothesis.IsNontrivialZero u) :
    RiemannHypothesis.IsNontrivialZero (conj u) := by
  have hξ : xiFunction u = 0 := (xiFunction_eq_zero_iff h.2.1 h.2.2).mpr h.1
  have hre0 : 0 < (conj u).re := by
    rw [Complex.conj_re]
    exact h.2.1
  have hre1 : (conj u).re < 1 := by
    rw [Complex.conj_re]
    exact h.2.2
  refine (xiFunction_eq_zero_iff_isNontrivialZero hre0 hre1).mp ?_
  rw [xiFunction_conj, hξ]
  exact map_zero _

/-- `nontrivialZerosFinset` 成员的虚部非零（经 ξ 零点虚部非零）。 -/
theorem im_ne_zero_of_mem_nontrivialZerosFinset {B : ℝ} {u : ℂ}
    (hu : u ∈ PrimeNumberTheorem.nontrivialZerosFinset B) : u.im ≠ 0 := by
  have h := (PrimeNumberTheorem.mem_nontrivialZerosFinset.mp hu).1
  exact xiFunction_zero_im_ne_zero ((xiFunction_eq_zero_iff h.2.1 h.2.2).mpr h.1)

/-- **高度截断零点集的上下半平面分解**：`NZF B = upper ∪ conj '' upper`。 -/
theorem nontrivialZerosFinset_eq_upper_union_conj (B : ℝ) :
    PrimeNumberTheorem.nontrivialZerosFinset B =
      xiUpperZerosFinset B ∪ (xiUpperZerosFinset B).image conj := by
  ext u
  rw [Finset.mem_union, Finset.mem_image]
  constructor
  · intro hu
    have hNTZ := (PrimeNumberTheorem.mem_nontrivialZerosFinset.mp hu).1
    have himB := (PrimeNumberTheorem.mem_nontrivialZerosFinset.mp hu).2
    have him := im_ne_zero_of_mem_nontrivialZerosFinset hu
    rcases lt_or_gt_of_ne him with himlt | himgt
    · right
      refine ⟨conj u, ?_, Complex.conj_conj u⟩
      rw [mem_xiUpperZerosFinset]
      refine ⟨isNontrivialZero_conj hNTZ, ?_, ?_⟩
      · rw [Complex.conj_im, abs_neg]
        exact himB
      · rw [Complex.conj_im]
        linarith
    · left
      rw [mem_xiUpperZerosFinset]
      exact ⟨hNTZ, himB, himgt⟩
  · intro h
    rcases h with hu | ⟨v, hv, rfl⟩
    · exact (Finset.mem_filter.mp hu).1
    · have hv' := mem_xiUpperZerosFinset.mp hv
      rw [PrimeNumberTheorem.mem_nontrivialZerosFinset]
      refine ⟨isNontrivialZero_conj hv'.1, ?_⟩
      rw [Complex.conj_im, abs_neg]
      exact hv'.2.1

/-- 上半平面零点集与其共轭像不交（虚部一正一负）。 -/
theorem xiUpperZerosFinset_disjoint_conj_image (B : ℝ) :
    Disjoint (xiUpperZerosFinset B) ((xiUpperZerosFinset B).image conj) := by
  rw [Finset.disjoint_left]
  intro u hu hunion
  rw [Finset.mem_image] at hunion
  obtain ⟨v, hv, hconjv⟩ := hunion
  have huim := (mem_xiUpperZerosFinset.mp hu).2.2
  have hvim := (mem_xiUpperZerosFinset.mp hv).2.2
  rw [← hconjv, Complex.conj_im] at huim
  linarith

/-- 圆盘零点集含于同高度截断零点集：`S_R ⊆ NZF R`。 -/
theorem xiZeroDiscFinset_subset_nontrivialZerosFinset (R : ℝ) :
    xiZeroDiscFinset R ⊆ PrimeNumberTheorem.nontrivialZerosFinset R := by
  intro u hu
  have hξ := xiFunction_eq_zero_of_mem_xiZeroDiscFinset hu
  have hNTZ := xiFunction_zero_imp_isNontrivialZero hξ
  have huB := xiZeroDiscFinset_subset_closedBall hu
  rw [Metric.mem_closedBall, dist_zero_right] at huB
  rw [PrimeNumberTheorem.mem_nontrivialZerosFinset]
  exact ⟨hNTZ, (Complex.abs_im_le_norm u).trans huB⟩

/-- 上半平面零点子型的原像在 `coe` 下的像正是 `xiUpperZerosFinset`。 -/
theorem preimage_coe_nontrivialZerosFinset_image (B : ℝ) :
    ((PrimeNumberTheorem.nontrivialZerosFinset B).preimage
        (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn).image
      (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) = xiUpperZerosFinset B := by
  ext u
  rw [Finset.mem_image]
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    rw [mem_xiUpperZerosFinset]
    have hmem := Finset.mem_preimage.mp hρ
    rw [PrimeNumberTheorem.mem_nontrivialZerosFinset] at hmem
    exact ⟨hmem.1, hmem.2, ρ.2.2⟩
  · intro hu
    have hu' := mem_xiUpperZerosFinset.mp hu
    refine ⟨⟨u, hu'.1, hu'.2.2⟩, ?_, rfl⟩
    rw [Finset.mem_preimage, PrimeNumberTheorem.mem_nontrivialZerosFinset]
    exact ⟨hu'.1, hu'.2.1⟩

/-- NZF 成员中范数严格小于 `R` 者必在圆盘零点集 `S_R` 内
（ζ 零点 ⇒ ξ 零点 ⇒ 除子非零）。 -/
theorem mem_xiZeroDiscFinset_of_mem_nontrivialZerosFinset_of_norm_lt {R : ℝ} {u : ℂ}
    (hu : u ∈ PrimeNumberTheorem.nontrivialZerosFinset R) (huR : ‖u‖ < R) :
    u ∈ xiZeroDiscFinset R := by
  have hNTZ := (PrimeNumberTheorem.mem_nontrivialZerosFinset.mp hu).1
  have hξ : xiFunction u = 0 := (xiFunction_eq_zero_iff hNTZ.2.1 hNTZ.2.2).mpr hNTZ.1
  have huB : u ∈ Metric.closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_lt huR
  rw [mem_xiZeroDiscFinset]
  have hne_top : analyticOrderAt xiFunction u ≠ ⊤ :=
    fun ht => xiFunction_ne_eventually_zero u (analyticOrderAt_eq_top.mp ht)
  have hkey : MeromorphicOn.divisor xiFunction (Metric.closedBall 0 R) u =
      (analyticOrderNatAt xiFunction u : ℤ) := by
    rw [MeromorphicOn.divisor_apply (meromorphicOn_xiFunction_closedBall R) huB,
      (differentiable_xiFunction.analyticAt u).meromorphicOrderAt_eq,
      ← Nat.cast_analyticOrderNatAt hne_top, ENat.map_coe, WithTop.untop₀_coe]
  rw [hkey]
  norm_cast
  have hne0 : analyticOrderAt xiFunction u ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨differentiable_xiFunction.analyticAt u, hξ⟩
  intro hnat0
  rw [analyticOrderNatAt, ENat.toNat_eq_zero] at hnat0
  rcases hnat0 with h | h
  · exact hne0 h
  · exact hne_top h

/-- **配对转换恒等式**：除子形式和与加权低部级数之差
= 边界圆弧项（`‖u‖ = R` 的零点）− 常数部项（`u⁻¹ + (conj u)⁻¹`）。

证明路径：低部 tsum 经 `tsum_xiWeightedMittagLefflerTerm_low_eq_sum` 与
`preimage_coe_nontrivialZerosFinset_image` 落到 `xiUpperZerosFinset R` 上；
每项 `m·pairedTerm` 拆为主部 `m·[(z−u)⁻¹+(z−conj u)⁻¹]` 与常数部
`m·(u⁻¹+(conj u)⁻¹)`；主部经上下半平面分解
`nontrivialZerosFinset_eq_upper_union_conj` 与
`analyticOrderNatAt_xiFunction_conj` 收成 `NZF R` 上的 `m·(z−u)⁻¹` 和，
再由 `S_R ⊆ NZF R` 外项为零（`mem_xiZeroDiscFinset_of_..._norm_lt` 的逆否）
收进 `S_R`，与 finsum 的有限和（`xi_finsum_divisor_mul_inv_eq_sum`，
重数经 `xiZeroDiscMult_eq_analyticOrderNatAt` 统一）相消，余下
`S_R` 中 `‖u‖ = R` 的边界项。 -/
theorem xi_finsum_divisor_sub_low_tsum_eq (R : ℝ) (z : ℂ) :
    (∑ᶠ u, ((MeromorphicOn.divisor xiFunction
          (Metric.closedBall 0 R) u : ℤ) : ℂ) * (z - u)⁻¹) -
      (∑' ρ : UpperHalfPlaneNontrivialZero,
        if ‖(ρ : ℂ)‖ < R then xiWeightedMittagLefflerTerm z (ρ : ℂ) else 0) =
    (∑ u ∈ (xiZeroDiscFinset R).filter fun u => ¬ ‖u‖ < R,
        (analyticOrderNatAt xiFunction u : ℂ) * (z - u)⁻¹) -
      ∑ u ∈ xiUpperZerosFinset R,
        if ‖u‖ < R then
          (analyticOrderNatAt xiFunction u : ℂ) * (u⁻¹ + (conj u)⁻¹) else 0 := by
  classical
  -- A. finsum → S 上的有限和（统一为 analyticOrderNatAt）
  have hfin : (∑ᶠ u, ((MeromorphicOn.divisor xiFunction
          (Metric.closedBall 0 R) u : ℤ) : ℂ) * (z - u)⁻¹)
      = ∑ u ∈ xiZeroDiscFinset R,
          (analyticOrderNatAt xiFunction u : ℂ) * (z - u)⁻¹ := by
    rw [xi_finsum_divisor_mul_inv_eq_sum R z]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [xiZeroDiscMult_eq_analyticOrderNatAt
      (xiZeroDiscFinset_subset_closedBall hu)]
  -- B. 低部 tsum → 上半平面零点集上的和
  have hlow : (∑' ρ : UpperHalfPlaneNontrivialZero,
        if ‖(ρ : ℂ)‖ < R then xiWeightedMittagLefflerTerm z (ρ : ℂ) else 0)
      = ∑ u ∈ xiUpperZerosFinset R,
          if ‖u‖ < R then xiWeightedMittagLefflerTerm z u else 0 := by
    have hsumimg : (∑ u ∈ ((PrimeNumberTheorem.nontrivialZerosFinset R).preimage
            (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ))
            Subtype.coe_injective.injOn).image
          (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)),
          if ‖u‖ < R then xiWeightedMittagLefflerTerm z u else 0)
        = ∑ ρ ∈ (PrimeNumberTheorem.nontrivialZerosFinset R).preimage
            (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ))
            Subtype.coe_injective.injOn,
          if ‖(ρ : ℂ)‖ < R then xiWeightedMittagLefflerTerm z (ρ : ℂ) else 0 :=
      Finset.sum_image (fun x _ y _ h => Subtype.coe_injective h)
    rw [tsum_xiWeightedMittagLefflerTerm_low_eq_sum R z, ← hsumimg,
      preimage_coe_nontrivialZerosFinset_image R]
  -- C. 每项拆为主部 + 常数部
  have hlowsplit : (∑ u ∈ xiUpperZerosFinset R,
        if ‖u‖ < R then xiWeightedMittagLefflerTerm z u else 0)
      = (∑ u ∈ xiUpperZerosFinset R,
          if ‖u‖ < R then (analyticOrderNatAt xiFunction u : ℂ) *
            ((z - u)⁻¹ + (z - conj u)⁻¹) else 0) +
        (∑ u ∈ xiUpperZerosFinset R,
          if ‖u‖ < R then (analyticOrderNatAt xiFunction u : ℂ) *
            (u⁻¹ + (conj u)⁻¹) else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : ‖u‖ < R
    · rw [if_pos hu, if_pos hu, if_pos hu, xiWeightedMittagLefflerTerm,
        xiPairedMittagLefflerTerm]
      ring
    · rw [if_neg hu, if_neg hu, if_neg hu, add_zero]
  -- D. 主部配对：上半平面的 [(z−u)⁻¹+(z−conj u)⁻¹] 和 = NZF 上的 (z−u)⁻¹ 和
  have hpair : (∑ u ∈ xiUpperZerosFinset R,
        if ‖u‖ < R then (analyticOrderNatAt xiFunction u : ℂ) *
          ((z - u)⁻¹ + (z - conj u)⁻¹) else 0)
      = ∑ u ∈ PrimeNumberTheorem.nontrivialZerosFinset R,
          if ‖u‖ < R then (analyticOrderNatAt xiFunction u : ℂ) * (z - u)⁻¹ else 0 := by
    have hif : ∀ u : ℂ,
        (if ‖u‖ < R then (analyticOrderNatAt xiFunction u : ℂ) *
            ((z - u)⁻¹ + (z - conj u)⁻¹) else 0)
        = (if ‖u‖ < R then (analyticOrderNatAt xiFunction u : ℂ) * (z - u)⁻¹ else 0) +
          (if ‖u‖ < R then (analyticOrderNatAt xiFunction u : ℂ) *
            (z - conj u)⁻¹ else 0) := by
      intro u
      by_cases hu : ‖u‖ < R
      · rw [if_pos hu, if_pos hu, if_pos hu]
        ring
      · rw [if_neg hu, if_neg hu, if_neg hu, add_zero]
    have himg2 : (∑ u ∈ (xiUpperZerosFinset R).image conj,
          if ‖u‖ < R then (analyticOrderNatAt xiFunction u : ℂ) * (z - u)⁻¹ else 0)
        = ∑ u ∈ xiUpperZerosFinset R,
            if ‖u‖ < R then (analyticOrderNatAt xiFunction u : ℂ) *
              (z - conj u)⁻¹ else 0 := by
      rw [Finset.sum_image (fun x _ y _ h => by
        have h2 := congrArg conj h
        simp only [Complex.conj_conj] at h2
        exact h2)]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [norm_conj, analyticOrderNatAt_xiFunction_conj]
    rw [Finset.sum_congr rfl (fun u _ => hif u), Finset.sum_add_distrib,
      nontrivialZerosFinset_eq_upper_union_conj R,
      Finset.sum_union (xiUpperZerosFinset_disjoint_conj_image R), himg2]
  -- E. NZF 和收进 S（S 外 if 项为零）
  have hNZF : (∑ u ∈ PrimeNumberTheorem.nontrivialZerosFinset R,
        if ‖u‖ < R then (analyticOrderNatAt xiFunction u : ℂ) * (z - u)⁻¹ else 0)
      = ∑ u ∈ xiZeroDiscFinset R,
          if ‖u‖ < R then (analyticOrderNatAt xiFunction u : ℂ) * (z - u)⁻¹ else 0 := by
    symm
    refine Finset.sum_subset (xiZeroDiscFinset_subset_nontrivialZerosFinset R)
      fun u huNZF huS => ?_
    by_cases hu : ‖u‖ < R
    · exact absurd (mem_xiZeroDiscFinset_of_mem_nontrivialZerosFinset_of_norm_lt
        huNZF hu) huS
    · rw [if_neg hu]
  -- F. S 上的和按 filter 拆分并与主部相消
  have hSsplit : (∑ u ∈ xiZeroDiscFinset R,
        (analyticOrderNatAt xiFunction u : ℂ) * (z - u)⁻¹)
      = (∑ u ∈ (xiZeroDiscFinset R).filter fun u => ‖u‖ < R,
          (analyticOrderNatAt xiFunction u : ℂ) * (z - u)⁻¹) +
        (∑ u ∈ (xiZeroDiscFinset R).filter fun u => ¬ ‖u‖ < R,
          (analyticOrderNatAt xiFunction u : ℂ) * (z - u)⁻¹) := by
    rw [← Finset.sum_filter_add_sum_filter_not (xiZeroDiscFinset R) (fun u => ‖u‖ < R)
      fun u => (analyticOrderNatAt xiFunction u : ℂ) * (z - u)⁻¹]
  have hSfilt : (∑ u ∈ (xiZeroDiscFinset R).filter fun u => ‖u‖ < R,
        (analyticOrderNatAt xiFunction u : ℂ) * (z - u)⁻¹)
      = ∑ u ∈ xiZeroDiscFinset R,
          if ‖u‖ < R then (analyticOrderNatAt xiFunction u : ℂ) * (z - u)⁻¹ else 0 :=
    Finset.sum_filter _ _
  rw [hfin, hlow, hlowsplit, hpair, hNZF, hSsplit, hSfilt]
  ring

/-! ## 三块误差项的界 -/

/-- **边界圆弧项界**：`S_R` 中 `‖u‖ = R` 的零点贡献
`≤ (9K/log 2 + 1)·(1 + log R)`。每项 `‖(z−u)⁻¹‖ ≤ 2/R`（`‖z‖ ≤ R/2`），
重数和由 Jensen 计数 `xiZeroDiscMult_sum_le` 控制，再经
`(1+2R) ≤ (9/4)R`、`log(4+2R) ≤ 2(1+log R)` 吸收。 -/
theorem norm_boundary_sum_le (K : ℝ) (hK0 : 0 ≤ K)
    (hcircK : ∀ t : ℝ, 0 < t → circleAverage (Real.log ‖xiFunction ·‖) 0 t ≤
      K * (1 + t) * Real.log (4 + t)) {R : ℝ} (hR : 4 ≤ R) {z : ℂ}
    (hz : ‖z‖ ≤ R / 2) :
    ‖∑ u ∈ (xiZeroDiscFinset R).filter fun u => ¬ ‖u‖ < R,
        (analyticOrderNatAt xiFunction u : ℂ) * (z - u)⁻¹‖
      ≤ (9 * K / Real.log 2 + 1) * (1 + Real.log R) := by
  have hR0 : (0 : ℝ) < R := by linarith
  have hlogR0 : (0 : ℝ) ≤ Real.log R := Real.log_nonneg (by linarith)
  have hL2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog6 : Real.log 6 < 2 := by
    have h6e : (6 : ℝ) < Real.exp 2 := by
      have h1 := Real.exp_one_gt_d9
      have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]
        norm_num
      nlinarith [Real.exp_pos 1]
    calc Real.log 6 < Real.log (Real.exp 2) := Real.log_lt_log (by norm_num) h6e
      _ = 2 := Real.log_exp 2
  have hlog42 : Real.log (4 + 2 * R) ≤ 2 * (1 + Real.log R) := by
    have h1 : (4 : ℝ) + 2 * R ≤ 6 * R := by linarith
    have h2 := Real.log_le_log (show (0 : ℝ) < 4 + 2 * R by positivity) h1
    rw [Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) hR0.ne'] at h2
    linarith
  -- 重数统一为 xiZeroDiscMult
  have hmult_eq : ∑ u ∈ (xiZeroDiscFinset R).filter fun u => ¬ ‖u‖ < R,
        (analyticOrderNatAt xiFunction u : ℝ)
      = ∑ u ∈ (xiZeroDiscFinset R).filter fun u => ¬ ‖u‖ < R,
          (xiZeroDiscMult R u : ℝ) := by
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [xiZeroDiscMult_eq_analyticOrderNatAt
      (xiZeroDiscFinset_subset_closedBall (Finset.mem_filter.mp hu).1)]
  have hle_sum : ∑ u ∈ (xiZeroDiscFinset R).filter fun u => ¬ ‖u‖ < R,
        (xiZeroDiscMult R u : ℝ)
      ≤ ∑ u ∈ xiZeroDiscFinset R, (xiZeroDiscMult R u : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun u _ _ => Nat.cast_nonneg _
  have hcount := xiZeroDiscMult_sum_le hcircK R hR
  -- 逐项上界
  have hterm : ∀ u ∈ (xiZeroDiscFinset R).filter fun u => ¬ ‖u‖ < R,
      (analyticOrderNatAt xiFunction u : ℝ) * ‖z - u‖⁻¹ ≤
        (analyticOrderNatAt xiFunction u : ℝ) * (2 / R) := by
    intro u hu
    have huS := (Finset.mem_filter.mp hu).1
    have hunot := (Finset.mem_filter.mp hu).2
    have huB := xiZeroDiscFinset_subset_closedBall huS
    rw [Metric.mem_closedBall, dist_zero_right] at huB
    have huR : ‖u‖ = R := le_antisymm huB (le_of_not_gt hunot)
    have hge : R / 2 ≤ ‖z - u‖ := by
      have h := norm_sub_norm_le u z
      rw [norm_sub_rev] at h
      rw [huR] at h
      linarith
    have hinv : ‖z - u‖⁻¹ ≤ (R / 2)⁻¹ :=
      (inv_le_inv₀ (lt_of_lt_of_le (by linarith : (0 : ℝ) < R / 2) hge)
        (by linarith : (0 : ℝ) < R / 2)).mpr hge
    rw [inv_div] at hinv
    exact mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg _)
  -- 常数吸收
  have hA0 : (0 : ℝ) ≤ K * (1 + 2 * R) * Real.log (4 + 2 * R) :=
    mul_nonneg (mul_nonneg hK0 (by linarith)) (Real.log_nonneg (by linarith))
  have hA_le : K * (1 + 2 * R) * Real.log (4 + 2 * R) ≤
      (9 / 2) * K * R * (1 + Real.log R) := by
    have h12 : (1 : ℝ) + 2 * R ≤ (9 / 4) * R := by linarith
    have h3 := mul_le_mul (mul_le_mul_of_nonneg_left h12 hK0) hlog42
      (Real.log_nonneg (by linarith : (1 : ℝ) ≤ 4 + 2 * R))
      (mul_nonneg hK0 (by linarith : (0 : ℝ) ≤ (9 / 4) * R))
    have heq : K * ((9 / 4) * R) * (2 * (1 + Real.log R)) =
        (9 / 2) * K * R * (1 + Real.log R) := by ring
    rwa [heq] at h3
  calc ‖∑ u ∈ (xiZeroDiscFinset R).filter fun u => ¬ ‖u‖ < R,
          (analyticOrderNatAt xiFunction u : ℂ) * (z - u)⁻¹‖
      ≤ ∑ u ∈ (xiZeroDiscFinset R).filter fun u => ¬ ‖u‖ < R,
          ‖(analyticOrderNatAt xiFunction u : ℂ) * (z - u)⁻¹‖ := norm_sum_le _ _
    _ = ∑ u ∈ (xiZeroDiscFinset R).filter fun u => ¬ ‖u‖ < R,
          (analyticOrderNatAt xiFunction u : ℝ) * ‖z - u‖⁻¹ := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [norm_mul, RCLike.norm_natCast, norm_inv]
    _ ≤ ∑ u ∈ (xiZeroDiscFinset R).filter fun u => ¬ ‖u‖ < R,
          (analyticOrderNatAt xiFunction u : ℝ) * (2 / R) :=
        Finset.sum_le_sum hterm
    _ = (2 / R) * ∑ u ∈ (xiZeroDiscFinset R).filter fun u => ¬ ‖u‖ < R,
          (analyticOrderNatAt xiFunction u : ℝ) := by
        rw [← Finset.sum_mul, mul_comm]
    _ ≤ (2 / R) * ((K * (1 + 2 * R) * Real.log (4 + 2 * R) + Real.log 2)
          / Real.log 2) :=
        mul_le_mul_of_nonneg_left
          (hmult_eq ▸ hle_sum.trans hcount) (by positivity)
    _ ≤ (9 * K / Real.log 2 + 1) * (1 + Real.log R) := by
        have h1 : (0 : ℝ) ≤ 1 + Real.log R := by linarith
        have h2 : (2 / R) * ((K * (1 + 2 * R) * Real.log (4 + 2 * R) + Real.log 2)
              / Real.log 2)
            ≤ (2 / R) * (((9 / 2) * K * R * (1 + Real.log R) + Real.log 2)
              / Real.log 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact div_le_div_of_nonneg_right (add_le_add hA_le le_rfl) hL2.le
        refine h2.trans ?_
        have h3 : (2 / R) * (((9 / 2) * K * R * (1 + Real.log R) + Real.log 2)
              / Real.log 2)
            = (9 * K * (1 + Real.log R) + (2 / R) * Real.log 2) / Real.log 2 := by
          field_simp [hR0.ne', hL2.ne']
        rw [h3, div_le_iff₀ hL2]
        have h6 : (9 * K / Real.log 2 + 1) * (1 + Real.log R) * Real.log 2
            = 9 * K * (1 + Real.log R) + Real.log 2 * (1 + Real.log R) := by
          field_simp [hL2.ne']
        rw [h6]
        have h4 : (2 / R) * Real.log 2 ≤ Real.log 2 * (1 + Real.log R) := by
          have h21 : (2 : ℝ) / R ≤ 1 := by
            rw [div_le_one hR0]
            linarith
          calc (2 / R) * Real.log 2 ≤ 1 * Real.log 2 :=
              mul_le_mul_of_nonneg_right h21 hL2.le
            _ = Real.log 2 := one_mul _
            _ ≤ Real.log 2 * (1 + Real.log R) :=
              (le_mul_iff_one_le_right hL2).mpr (by linarith : (1 : ℝ) ≤ 1 + Real.log R)
        exact add_le_add le_rfl h4

/-- **常数部项界**：`u⁻¹ + (conj u)⁻¹ = 2·Re(u⁻¹)`，范数 `≤ 2‖u‖⁻¹`，
和式经 `preimage_coe_nontrivialZerosFinset_image` 转为头部计数界
`exists_upperZeros_weighted_norm_inv_le_log_sq` 的子型和。 -/
theorem norm_const_sum_le (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ B : ℝ, 4 ≤ B →
      ∑ ρ ∈ (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
          (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn,
        (if ‖(ρ : ℂ)‖ < B then
          (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹
        else 0) ≤ C * (1 + Real.log B) ^ 2) {R : ℝ} (hR : 4 ≤ R) :
    ‖∑ u ∈ xiUpperZerosFinset R,
        if ‖u‖ < R then
          (analyticOrderNatAt xiFunction u : ℂ) * (u⁻¹ + (conj u)⁻¹) else 0‖
      ≤ 2 * C * (1 + Real.log R) ^ 2 := by
  classical
  have hterm : ∀ u ∈ xiUpperZerosFinset R,
      ‖if ‖u‖ < R then (analyticOrderNatAt xiFunction u : ℂ) *
          (u⁻¹ + (conj u)⁻¹) else 0‖
        ≤ if ‖u‖ < R then
            (analyticOrderNatAt xiFunction u : ℝ) * (2 * ‖u‖⁻¹) else 0 := by
    intro u _
    by_cases hu : ‖u‖ < R
    · rw [if_pos hu, if_pos hu]
      have hconj : u⁻¹ + (conj u)⁻¹ = ((2 * (u⁻¹).re : ℝ) : ℂ) := by
        rw [← Complex.conj_inv]
        exact Complex.add_conj _
      rw [norm_mul, RCLike.norm_natCast, hconj, Complex.norm_real]
      have hle : |(2 : ℝ) * (u⁻¹).re| ≤ 2 * ‖u‖⁻¹ := by
        have h1 : |(2 : ℝ) * (u⁻¹).re| = 2 * |(u⁻¹).re| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        rw [h1]
        have h2 : |(u⁻¹).re| ≤ ‖u‖⁻¹ := by
          rw [← norm_inv]
          exact Complex.abs_re_le_norm _
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
      exact mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _)
    · rw [if_neg hu, if_neg hu, norm_zero]
  -- 上半平面和 = 子型原像和
  have hsumimg : (∑ u ∈ xiUpperZerosFinset R,
        if ‖u‖ < R then
          (analyticOrderNatAt xiFunction u : ℝ) * ‖u‖⁻¹ else 0)
      = ∑ ρ ∈ (PrimeNumberTheorem.nontrivialZerosFinset R).preimage
          (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn,
        (if ‖(ρ : ℂ)‖ < R then
          (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹ else 0) := by
    rw [← preimage_coe_nontrivialZerosFinset_image R]
    exact Finset.sum_image (fun x _ y _ h => Subtype.coe_injective h)
  calc ‖∑ u ∈ xiUpperZerosFinset R,
          if ‖u‖ < R then (analyticOrderNatAt xiFunction u : ℂ) *
            (u⁻¹ + (conj u)⁻¹) else 0‖
      ≤ ∑ u ∈ xiUpperZerosFinset R,
          ‖if ‖u‖ < R then (analyticOrderNatAt xiFunction u : ℂ) *
            (u⁻¹ + (conj u)⁻¹) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ u ∈ xiUpperZerosFinset R,
          if ‖u‖ < R then
            (analyticOrderNatAt xiFunction u : ℝ) * (2 * ‖u‖⁻¹) else 0 :=
        Finset.sum_le_sum hterm
    _ = 2 * ∑ u ∈ xiUpperZerosFinset R,
          if ‖u‖ < R then
            (analyticOrderNatAt xiFunction u : ℝ) * ‖u‖⁻¹ else 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        by_cases hu : ‖u‖ < R
        · rw [if_pos hu, if_pos hu]
          ring
        · rw [if_neg hu, if_neg hu, mul_zero]
    _ ≤ 2 * (C * (1 + Real.log R) ^ 2) :=
        mul_le_mul_of_nonneg_left (hsumimg ▸ hC R hR) (by norm_num)
    _ = 2 * C * (1 + Real.log R) ^ 2 := by ring

/-- **高部尾项界**：逐项 `norm_xiPairedMittagLefflerTerm_le`（`‖ρ‖ ≥ R ≥ 4`
给出 `2 ≤ ‖ρ‖` 与 `2‖z‖ ≤ ‖ρ‖`）后由尾部计数界吸收。 -/
theorem norm_high_tsum_le (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ T : ℝ, 4 ≤ T →
      (∑' ρ : UpperHalfPlaneNontrivialZero,
        if T ≤ ‖(ρ : ℂ)‖ then
          (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹ ^ 2
        else 0) ≤ C * (1 + Real.log T) / T) {R : ℝ} (hR : 4 ≤ R) {z : ℂ}
    (hz : ‖z‖ ≤ R / 2) :
    ‖∑' ρ : UpperHalfPlaneNontrivialZero,
        if R ≤ ‖(ρ : ℂ)‖ then xiWeightedMittagLefflerTerm z (ρ : ℂ) else 0‖
      ≤ (8 * (R / 2 + 1) + 2) * C * (1 + Real.log R) / R := by
  classical
  have hR0 : (0 : ℝ) < R := by linarith
  have hlogR0 : (0 : ℝ) ≤ Real.log R := Real.log_nonneg (by linarith)
  set Kz : ℝ := 8 * (‖z‖ + 1) + 2 with hKzdef
  have hKz0 : (0 : ℝ) ≤ Kz := by positivity
  have hKzKR : Kz ≤ 8 * (R / 2 + 1) + 2 := by linarith [hz]
  -- 逐项范数上界
  have hptw : ∀ ρ : UpperHalfPlaneNontrivialZero,
      ‖if R ≤ ‖(ρ : ℂ)‖ then xiWeightedMittagLefflerTerm z (ρ : ℂ) else 0‖
        ≤ Kz * (if R ≤ ‖(ρ : ℂ)‖ then
            (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹ ^ 2
          else 0) := by
    intro ρ
    by_cases hρ : R ≤ ‖(ρ : ℂ)‖
    · rw [if_pos hρ, if_pos hρ]
      have hρ2 : 2 ≤ ‖(ρ : ℂ)‖ := le_trans (by linarith : (2 : ℝ) ≤ R) hρ
      have hρs : 2 * ‖z‖ ≤ ‖(ρ : ℂ)‖ := le_trans (by linarith [hz] : 2 * ‖z‖ ≤ R) hρ
      have hre : |(ρ : ℂ).re| ≤ 1 := by
        have h3 := ρ.2.1.2.1
        have h4 := ρ.2.1.2.2
        rw [abs_le]
        constructor <;> linarith
      calc ‖xiWeightedMittagLefflerTerm z (ρ : ℂ)‖
          = (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) *
              ‖xiPairedMittagLefflerTerm z (ρ : ℂ)‖ := by
            rw [xiWeightedMittagLefflerTerm, norm_mul, RCLike.norm_natCast]
        _ ≤ (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) *
              (Kz * ‖(ρ : ℂ)‖⁻¹ ^ 2) :=
            mul_le_mul_of_nonneg_left (norm_xiPairedMittagLefflerTerm_le hρ2 hρs hre)
              (Nat.cast_nonneg _)
        _ = Kz * ((analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) *
              ‖(ρ : ℂ)‖⁻¹ ^ 2) := by ring
    · rw [if_neg hρ, if_neg hρ, norm_zero, mul_zero]
  -- 截断实和的可和性
  have hg : Summable fun ρ : UpperHalfPlaneNontrivialZero ↦
      if R ≤ ‖(ρ : ℂ)‖ then
        (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹ ^ 2
      else 0 := by
    refine Summable.of_nonneg_of_le (fun ρ => ?_) (fun ρ => ?_)
      summable_xiOrder_mul_norm_inv_sq_upperZeros
    · by_cases hρ : R ≤ ‖(ρ : ℂ)‖
      · rw [if_pos hρ]
        positivity
      · rw [if_neg hρ]
    · by_cases hρ : R ≤ ‖(ρ : ℂ)‖
      · rw [if_pos hρ]
      · rw [if_neg hρ]
        positivity
  have hnorm : Summable fun ρ : UpperHalfPlaneNontrivialZero ↦
      ‖if R ≤ ‖(ρ : ℂ)‖ then xiWeightedMittagLefflerTerm z (ρ : ℂ) else 0‖ :=
    Summable.of_nonneg_of_le (fun ρ => norm_nonneg _) hptw (hg.mul_left Kz)
  calc ‖∑' ρ : UpperHalfPlaneNontrivialZero,
          if R ≤ ‖(ρ : ℂ)‖ then xiWeightedMittagLefflerTerm z (ρ : ℂ) else 0‖
      ≤ ∑' ρ : UpperHalfPlaneNontrivialZero,
          ‖if R ≤ ‖(ρ : ℂ)‖ then xiWeightedMittagLefflerTerm z (ρ : ℂ) else 0‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' ρ : UpperHalfPlaneNontrivialZero,
          Kz * (if R ≤ ‖(ρ : ℂ)‖ then
            (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹ ^ 2
          else 0) := hnorm.tsum_le_tsum hptw (hg.mul_left Kz)
    _ = Kz * (∑' ρ : UpperHalfPlaneNontrivialZero,
          if R ≤ ‖(ρ : ℂ)‖ then
            (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹ ^ 2
          else 0) := tsum_mul_left
    _ ≤ Kz * (C * (1 + Real.log R) / R) :=
        mul_le_mul_of_nonneg_left (hC R hR) hKz0
    _ ≤ (8 * (R / 2 + 1) + 2) * (C * (1 + Real.log R) / R) :=
        mul_le_mul hKzKR (le_refl _)
          (div_nonneg (mul_nonneg hC0 (by linarith)) hR0.le)
          (by positivity)
    _ = (8 * (R / 2 + 1) + 2) * C * (1 + Real.log R) / R := by ring

/-! ## 修正函数在 `ball 0 (R/2)` 上的 `O(log² R)` 界 -/

/-- **E 的 O(log² R) 界（非零点版）**：存在 `C_E ≥ 0`，对所有 `R ≥ 4` 与
`z ∈ ball 0 (R/2)` 且 `ξ z ≠ 0`，`‖E z‖ ≤ C_E·(1 + log R)²`。
分解 `E = [ξ'/ξ − finsum_R] + [finsum_R − W_low] + [−W_high] − c₀`，
四块分别由 C1、`xi_finsum_divisor_sub_low_tsum_eq` + 边界/常数项界、
高部尾项界、`‖c₀‖ ≤ ‖c₀‖(1+log R)²` 控制。 -/
theorem norm_xiWeightedEntireCorrection_le_of_ne_zero :
    ∃ C_E : ℝ, 0 ≤ C_E ∧ ∀ R : ℝ, 4 ≤ R → ∀ z ∈ Metric.ball 0 (R / 2),
      xiFunction z ≠ 0 →
        ‖xiWeightedEntireCorrection (deriv xiFunction 0 / xiFunction 0) z‖ ≤
          C_E * (1 + Real.log R) ^ 2 := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := xi_logDeriv_sub_finsum_divisor_le
  obtain ⟨K₁, hK₁0, hcirc⟩ := exists_circleAverage_log_norm_xi_le
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_upperZeros_weighted_norm_inv_le_log_sq
  obtain ⟨C₃, hC₃0, hC₃⟩ := exists_upperZeros_tail_weighted_norm_inv_sq_le
  have hL2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hXnn : (0 : ℝ) ≤ 9 * K₁ / Real.log 2 + 1 := by
    have h : (0 : ℝ) ≤ 9 * K₁ / Real.log 2 :=
      div_nonneg (mul_nonneg (by norm_num) hK₁0) hL2.le
    linarith
  refine ⟨C₁ + (9 * K₁ / Real.log 2 + 1) + 2 * C₂ + (13 / 2) * C₃ +
      ‖deriv xiFunction 0 / xiFunction 0‖,
    add_nonneg (add_nonneg (add_nonneg (add_nonneg hC₁0 hXnn)
      (mul_nonneg (by norm_num) hC₂0)) (mul_nonneg (by norm_num) hC₃0))
      (norm_nonneg _),
    fun R hR z hz hξz => ?_⟩
  have hR0 : (0 : ℝ) < R := by linarith
  have hlogR0 : (0 : ℝ) ≤ Real.log R := Real.log_nonneg (by linarith)
  have hW1 : (1 : ℝ) ≤ 1 + Real.log R := by linarith
  have hW2 : 1 + Real.log R ≤ (1 + Real.log R) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hW1 (by linarith : (0 : ℝ) ≤ 1 + Real.log R)
    rwa [one_mul, ← pow_two] at h
  have hW1sq : (1 : ℝ) ≤ (1 + Real.log R) ^ 2 := le_trans hW1 hW2
  have hzcl : z ∈ Metric.closedBall (0 : ℂ) (R / 2) := Metric.ball_subset_closedBall hz
  have hznorm : ‖z‖ ≤ R / 2 := by
    have hz' := hz
    rw [Metric.mem_ball, dist_zero_right] at hz'
    exact hz'.le
  -- E 展开与 W 拆分
  have hE : xiWeightedEntireCorrection (deriv xiFunction 0 / xiFunction 0) z
      = logDeriv xiFunction z - deriv xiFunction 0 / xiFunction 0 -
        xiWeightedMittagLefflerSum z := by
    rw [xiWeightedEntireCorrection_apply_of_ne_zero _ hξz, ← logDeriv_apply]
  have hW : xiWeightedMittagLefflerSum z
      = (∑' ρ : UpperHalfPlaneNontrivialZero,
          if ‖(ρ : ℂ)‖ < R then xiWeightedMittagLefflerTerm z (ρ : ℂ) else 0) +
        (∑' ρ : UpperHalfPlaneNontrivialZero,
          if R ≤ ‖(ρ : ℂ)‖ then xiWeightedMittagLefflerTerm z (ρ : ℂ) else 0) :=
    xiWeightedMittagLefflerSum_eq_low_add_high R z
  have hdecomp : xiWeightedEntireCorrection (deriv xiFunction 0 / xiFunction 0) z
      = (logDeriv xiFunction z - (∑ᶠ u, ((MeromorphicOn.divisor xiFunction
              (Metric.closedBall 0 R) u : ℤ) : ℂ) * (z - u)⁻¹))
        + (((∑ᶠ u, ((MeromorphicOn.divisor xiFunction
              (Metric.closedBall 0 R) u : ℤ) : ℂ) * (z - u)⁻¹)
          - (∑' ρ : UpperHalfPlaneNontrivialZero,
              if ‖(ρ : ℂ)‖ < R then xiWeightedMittagLefflerTerm z (ρ : ℂ) else 0))
        + (-(∑' ρ : UpperHalfPlaneNontrivialZero,
              if R ≤ ‖(ρ : ℂ)‖ then xiWeightedMittagLefflerTerm z (ρ : ℂ) else 0)
          + -(deriv xiFunction 0 / xiFunction 0))) := by
    rw [hE, hW]
    ring
  -- 四块各自的界
  have hA : ‖logDeriv xiFunction z - (∑ᶠ u, ((MeromorphicOn.divisor xiFunction
          (Metric.closedBall 0 R) u : ℤ) : ℂ) * (z - u)⁻¹)‖
      ≤ C₁ * (1 + Real.log R) ^ 2 := hC₁ R hR z hzcl hξz
  have hmiddle : ‖(∑ᶠ u, ((MeromorphicOn.divisor xiFunction
          (Metric.closedBall 0 R) u : ℤ) : ℂ) * (z - u)⁻¹)
        - (∑' ρ : UpperHalfPlaneNontrivialZero,
            if ‖(ρ : ℂ)‖ < R then xiWeightedMittagLefflerTerm z (ρ : ℂ) else 0)‖
      ≤ (9 * K₁ / Real.log 2 + 1) * (1 + Real.log R)
        + 2 * C₂ * (1 + Real.log R) ^ 2 := by
    rw [xi_finsum_divisor_sub_low_tsum_eq R z]
    exact (norm_sub_le _ _).trans
      (add_le_add (norm_boundary_sum_le K₁ hK₁0 hcirc hR hznorm)
        (norm_const_sum_le C₂ hC₂0 hC₂ hR))
  have hB : ‖(∑ᶠ u, ((MeromorphicOn.divisor xiFunction
          (Metric.closedBall 0 R) u : ℤ) : ℂ) * (z - u)⁻¹)
        - (∑' ρ : UpperHalfPlaneNontrivialZero,
            if ‖(ρ : ℂ)‖ < R then xiWeightedMittagLefflerTerm z (ρ : ℂ) else 0)‖
      ≤ (9 * K₁ / Real.log 2 + 1 + 2 * C₂) * (1 + Real.log R) ^ 2 := by
    refine hmiddle.trans ?_
    have h1 := mul_le_mul_of_nonneg_left hW2 hXnn
    have h2 : (9 * K₁ / Real.log 2 + 1) * (1 + Real.log R)
          + 2 * C₂ * (1 + Real.log R) ^ 2
        ≤ (9 * K₁ / Real.log 2 + 1) * (1 + Real.log R) ^ 2
          + 2 * C₂ * (1 + Real.log R) ^ 2 := add_le_add h1 (le_refl _)
    refine h2.trans (le_of_eq ?_)
    ring
  have hhigh := norm_high_tsum_le C₃ hC₃0 hC₃ hR hznorm
  have hC : ‖-(∑' ρ : UpperHalfPlaneNontrivialZero,
        if R ≤ ‖(ρ : ℂ)‖ then xiWeightedMittagLefflerTerm z (ρ : ℂ) else 0)‖
      ≤ (13 / 2) * C₃ * (1 + Real.log R) ^ 2 := by
    rw [norm_neg]
    refine hhigh.trans ?_
    have hfac : (8 * (R / 2 + 1) + 2) / R ≤ 13 / 2 := by
      rw [div_le_iff₀ hR0]
      have heq : 8 * (R / 2 + 1) + 2 = 4 * R + 10 := by ring
      rw [heq]
      linarith
    have hnn : (0 : ℝ) ≤ C₃ * (1 + Real.log R) := mul_nonneg hC₃0 (by linarith)
    calc (8 * (R / 2 + 1) + 2) * C₃ * (1 + Real.log R) / R
        = ((8 * (R / 2 + 1) + 2) / R) * (C₃ * (1 + Real.log R)) := by ring
      _ ≤ (13 / 2) * (C₃ * (1 + Real.log R)) :=
          mul_le_mul_of_nonneg_right hfac hnn
      _ ≤ (13 / 2) * (C₃ * (1 + Real.log R) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW2 hC₃0)
            (by norm_num)
      _ = (13 / 2) * C₃ * (1 + Real.log R) ^ 2 := by ring
  have hD : ‖-(deriv xiFunction 0 / xiFunction 0)‖
      ≤ ‖deriv xiFunction 0 / xiFunction 0‖ * (1 + Real.log R) ^ 2 := by
    rw [norm_neg]
    calc ‖deriv xiFunction 0 / xiFunction 0‖
        = ‖deriv xiFunction 0 / xiFunction 0‖ * 1 := (mul_one _).symm
      _ ≤ ‖deriv xiFunction 0 / xiFunction 0‖ * (1 + Real.log R) ^ 2 :=
          mul_le_mul_of_nonneg_left hW1sq (norm_nonneg _)
  -- 合并
  have hsum : ‖(logDeriv xiFunction z - (∑ᶠ u, ((MeromorphicOn.divisor xiFunction
            (Metric.closedBall 0 R) u : ℤ) : ℂ) * (z - u)⁻¹))
        + (((∑ᶠ u, ((MeromorphicOn.divisor xiFunction
              (Metric.closedBall 0 R) u : ℤ) : ℂ) * (z - u)⁻¹)
          - (∑' ρ : UpperHalfPlaneNontrivialZero,
              if ‖(ρ : ℂ)‖ < R then xiWeightedMittagLefflerTerm z (ρ : ℂ) else 0))
        + (-(∑' ρ : UpperHalfPlaneNontrivialZero,
              if R ≤ ‖(ρ : ℂ)‖ then xiWeightedMittagLefflerTerm z (ρ : ℂ) else 0)
          + -(deriv xiFunction 0 / xiFunction 0)))‖
      ≤ ‖logDeriv xiFunction z - (∑ᶠ u, ((MeromorphicOn.divisor xiFunction
            (Metric.closedBall 0 R) u : ℤ) : ℂ) * (z - u)⁻¹)‖
        + (‖(∑ᶠ u, ((MeromorphicOn.divisor xiFunction
              (Metric.closedBall 0 R) u : ℤ) : ℂ) * (z - u)⁻¹)
          - (∑' ρ : UpperHalfPlaneNontrivialZero,
              if ‖(ρ : ℂ)‖ < R then xiWeightedMittagLefflerTerm z (ρ : ℂ) else 0)‖
        + (‖-(∑' ρ : UpperHalfPlaneNontrivialZero,
              if R ≤ ‖(ρ : ℂ)‖ then xiWeightedMittagLefflerTerm z (ρ : ℂ) else 0)‖
          + ‖-(deriv xiFunction 0 / xiFunction 0)‖)) := by
    have h1 := norm_add_le (logDeriv xiFunction z - (∑ᶠ u, ((MeromorphicOn.divisor
        xiFunction (Metric.closedBall 0 R) u : ℤ) : ℂ) * (z - u)⁻¹))
      (((∑ᶠ u, ((MeromorphicOn.divisor xiFunction (Metric.closedBall 0 R) u : ℤ) : ℂ)
          * (z - u)⁻¹)
        - (∑' ρ : UpperHalfPlaneNontrivialZero,
            if ‖(ρ : ℂ)‖ < R then xiWeightedMittagLefflerTerm z (ρ : ℂ) else 0))
        + (-(∑' ρ : UpperHalfPlaneNontrivialZero,
            if R ≤ ‖(ρ : ℂ)‖ then xiWeightedMittagLefflerTerm z (ρ : ℂ) else 0)
          + -(deriv xiFunction 0 / xiFunction 0)))
    have h2 := norm_add_le ((∑ᶠ u, ((MeromorphicOn.divisor xiFunction
          (Metric.closedBall 0 R) u : ℤ) : ℂ) * (z - u)⁻¹)
        - (∑' ρ : UpperHalfPlaneNontrivialZero,
            if ‖(ρ : ℂ)‖ < R then xiWeightedMittagLefflerTerm z (ρ : ℂ) else 0))
      (-(∑' ρ : UpperHalfPlaneNontrivialZero,
            if R ≤ ‖(ρ : ℂ)‖ then xiWeightedMittagLefflerTerm z (ρ : ℂ) else 0)
        + -(deriv xiFunction 0 / xiFunction 0))
    have h3 := norm_add_le (-(∑' ρ : UpperHalfPlaneNontrivialZero,
            if R ≤ ‖(ρ : ℂ)‖ then xiWeightedMittagLefflerTerm z (ρ : ℂ) else 0))
      (-(deriv xiFunction 0 / xiFunction 0))
    exact h1.trans (add_le_add le_rfl (h2.trans (add_le_add le_rfl h3)))
  calc ‖xiWeightedEntireCorrection (deriv xiFunction 0 / xiFunction 0) z‖
      ≤ ‖logDeriv xiFunction z - (∑ᶠ u, ((MeromorphicOn.divisor xiFunction
            (Metric.closedBall 0 R) u : ℤ) : ℂ) * (z - u)⁻¹)‖
        + (‖(∑ᶠ u, ((MeromorphicOn.divisor xiFunction
              (Metric.closedBall 0 R) u : ℤ) : ℂ) * (z - u)⁻¹)
          - (∑' ρ : UpperHalfPlaneNontrivialZero,
              if ‖(ρ : ℂ)‖ < R then xiWeightedMittagLefflerTerm z (ρ : ℂ) else 0)‖
        + (‖-(∑' ρ : UpperHalfPlaneNontrivialZero,
              if R ≤ ‖(ρ : ℂ)‖ then xiWeightedMittagLefflerTerm z (ρ : ℂ) else 0)‖
          + ‖-(deriv xiFunction 0 / xiFunction 0)‖)) := hdecomp ▸ hsum
    _ ≤ C₁ * (1 + Real.log R) ^ 2
        + ((9 * K₁ / Real.log 2 + 1 + 2 * C₂) * (1 + Real.log R) ^ 2
        + ((13 / 2) * C₃ * (1 + Real.log R) ^ 2
          + ‖deriv xiFunction 0 / xiFunction 0‖ * (1 + Real.log R) ^ 2)) :=
        add_le_add hA (add_le_add hB (add_le_add hC hD))
    _ = (C₁ + (9 * K₁ / Real.log 2 + 1) + 2 * C₂ + (13 / 2) * C₃ +
          ‖deriv xiFunction 0 / xiFunction 0‖) * (1 + Real.log R) ^ 2 := by ring

/-- **E 的 O(log² R) 界（稠密延拓，去掉 `ξ z ≠ 0`）**：零点处由
`xiFunction_ne_eventually_zero` 取逼近序列 `zₙ → z`（`ξ zₙ ≠ 0`），
E 的连续性（整函数）与 `le_of_tendsto'` 闭合。 -/
theorem norm_xiWeightedEntireCorrection_le :
    ∃ C_E : ℝ, 0 ≤ C_E ∧ ∀ R : ℝ, 4 ≤ R → ∀ z ∈ Metric.ball 0 (R / 2),
      ‖xiWeightedEntireCorrection (deriv xiFunction 0 / xiFunction 0) z‖ ≤
        C_E * (1 + Real.log R) ^ 2 := by
  obtain ⟨C_E, hC_E0, hbound⟩ := norm_xiWeightedEntireCorrection_le_of_ne_zero
  refine ⟨C_E, hC_E0, fun R hR z hz => ?_⟩
  by_cases hξz : xiFunction z = 0
  swap
  · exact hbound R hR z hz hξz
  · have hfreq : ∃ᶠ w in 𝓝 z, xiFunction w ≠ 0 :=
      not_eventually.mp (xiFunction_ne_eventually_zero z)
    have hfreqn : ∀ n : ℕ, ∃ w : ℂ, xiFunction w ≠ 0 ∧
        w ∈ Metric.ball z (1 / ((n : ℝ) + 1)) ∧ w ∈ Metric.ball 0 (R / 2) := by
      intro n
      have hev1 : ∀ᶠ w in 𝓝 z, w ∈ Metric.ball z (1 / ((n : ℝ) + 1)) :=
        Metric.ball_mem_nhds z (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))
      have hev2 : ∀ᶠ w in 𝓝 z, w ∈ Metric.ball 0 (R / 2) := isOpen_ball.mem_nhds hz
      exact (hfreq.and_eventually (hev1.and hev2)).exists
    choose seq hseqξ hseqball hseqR using hfreqn
    have hT : Filter.Tendsto seq Filter.atTop (𝓝 z) := by
      have hdist : Filter.Tendsto (fun n => dist (seq n) z) Filter.atTop (𝓝 0) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
          tendsto_one_div_add_atTop_nhds_zero_nat (fun n => dist_nonneg)
          fun n => (hseqball n).le
      exact tendsto_iff_dist_tendsto_zero.mpr hdist
    have hcont : Filter.Tendsto
        (fun n => ‖xiWeightedEntireCorrection
          (deriv xiFunction 0 / xiFunction 0) (seq n)‖)
        Filter.atTop
        (𝓝 ‖xiWeightedEntireCorrection (deriv xiFunction 0 / xiFunction 0) z‖) :=
      ((differentiable_xiWeightedEntireCorrection _).continuous.norm.tendsto z).comp hT
    exact le_of_tendsto' hcont fun n => hbound R hR (seq n) (hseqR n) (hseqξ n)

end RiemannExplorer
