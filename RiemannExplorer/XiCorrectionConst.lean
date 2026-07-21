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

end RiemannExplorer
