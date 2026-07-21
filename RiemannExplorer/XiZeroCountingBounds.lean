/-
# 上半平面零点的重数加权计数界：头部 `O(log² T)` 与尾部 `O(log T / T)`

本文件给出 ξ 函数零点（上半平面、按解析重数计次）的两个无条件计数界，
是「ξ'/ξ 的重数加权部分分式展开」归约链上增长估计的算术输入：

- `exists_upperZeros_weighted_norm_inv_le_log_sq`：
  圆盘 `‖ρ‖ < B` 内 `Σ m_ξ(ρ)·‖ρ‖⁻¹ ≤ C·(1 + log B)²`。
  这是展开式差函数中「零点常数项部分」 `Σ_{‖ρ‖<B} m_ρ(1/ρ + 1/conj ρ)`
  的范数控制。
- `exists_upperZeros_tail_weighted_norm_inv_sq_le`：
  尾部 `Σ_{‖ρ‖ ≥ T} m_ξ(ρ)·‖ρ‖⁻² ≤ C·(1 + log T)/T`。
  这是加权 Mittag-Leffler 级数高部在 `‖s‖ ≤ T/2` 上一致 `O(log T)`
  的来源（`|s/(ρ(s−ρ))| ≤ 2|s|/‖ρ‖²`）。

## 方法

头部界直接归约到仓库已有的倒数加权全局计数
`PrimeNumberTheorem.ExplicitFormulaAux.exists_globalReciprocalZeroMultiplicity_le_log_sq`
（`|Im ρ| ≤ T` 窗口内 `Σ m_ζ(ρ)/‖ρ‖ = O(log² T)`）：上半平面零点是
`nontrivialZerosFinset` 的原像子集，ξ 与 ζ 的解析重数在临界带内相同
（`analyticOrderNatAt_xiFunction_eq_riemannZeta_of_isNontrivialZero`）。

尾部界按二进壳 `2ᵏ⁺¹ ≤ ‖ρ‖ < 2ᵏ⁺²` 分组：壳内重数和由
`exists_globalZeroMultiplicity_le_mul_log`（`N(T) = O(T log T)`）控制为
`C·2ᵏ⁺²·(k+4)`，壳贡献 `≤ C·(k+4)·2⁻ᵏ`；`‖ρ‖ ≥ T` 只涉及
`2ᵏ⁺² > T` 的壳（`k ≥ ⌈log₂ T⌉ − 2`），几何尾 `Σ_{k≥K₀}(k+4)2⁻ᵏ`
`= 2⁻ᴷ⁰·(2(K₀+4)+2)` 给出 `O((1+log T)/T)`。

两条均无条件、无 sorry。
-/

import RiemannExplorer.LiZeroSumConvergence

open Complex ComplexConjugate
open scoped BigOperators

namespace RiemannExplorer

/-! ## 头部界：`Σ_{‖ρ‖ < B} m_ξ(ρ)·‖ρ‖⁻¹ = O(log² B)` -/

/-- **头部计数界（无条件）**：存在 `C ≥ 0`，对所有 `B ≥ 4`，上半平面零点
在圆盘 `‖ρ‖ < B` 内的 ξ-重数加权倒数范数和不超过 `C·(1 + log B)²`。

证明要点：截断和 ≤ 全和（逐项非负）；ξ 重数 = ζ 重数（临界带内相等）；
原像和 = 像和（`Subtype.coe` 单射）≤ 全体零点倒数加权和
`globalReciprocalZeroMultiplicity B ≤ C₀·(1 + log(B+6))²`（仓库已有）；
最后 `1 + log(B+6) ≤ (5/2)·(1 + log B)` 吸收常数。 -/
theorem exists_upperZeros_weighted_norm_inv_le_log_sq :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, 4 ≤ B →
      ∑ ρ ∈ (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
          (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn,
        (if ‖(ρ : ℂ)‖ < B then
          (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹
        else 0) ≤
        C * (1 + Real.log B) ^ 2 := by
  classical
  obtain ⟨C₀, hC₀, hbound⟩ :=
    PrimeNumberTheorem.ExplicitFormulaAux.exists_globalReciprocalZeroMultiplicity_le_log_sq
  refine ⟨25 / 4 * C₀, mul_nonneg (by norm_num) hC₀, fun B hB => ?_⟩
  -- 第一步：截断和 ≤ 全和（逐项非负）
  have hstep1 : ∑ ρ ∈ (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
          (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn,
        (if ‖(ρ : ℂ)‖ < B then
          (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹
        else 0) ≤
      ∑ ρ ∈ (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
          (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn,
        (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹ :=
    Finset.sum_le_sum fun ρ _ => by
      split_ifs
      · exact le_refl _
      · exact mul_nonneg (Nat.cast_nonneg _) (by positivity)
  -- 第二步：ξ 重数换成 ζ 重数（临界带内逐点相等）
  have hstep2 : ∑ ρ ∈ (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
          (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn,
        (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹ =
      ∑ ρ ∈ (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
          (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn,
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹ := by
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    have hzero := (PrimeNumberTheorem.mem_nontrivialZerosFinset.mp
      (Finset.mem_preimage.mp hρ)).1
    rw [analyticOrderNatAt_xiFunction_eq_riemannZeta_of_isNontrivialZero
      hzero.2.1 hzero.2.2]
  -- 第三步：原像和 = 像和 ≤ 全体零点倒数加权和
  have hstep3 : ∑ ρ ∈ (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
          (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn,
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹ ≤
      PrimeNumberTheorem.ExplicitFormulaAux.globalReciprocalZeroMultiplicity B := by
    have himg : ((PrimeNumberTheorem.nontrivialZerosFinset B).preimage
            (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn).image
          (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) ⊆
        PrimeNumberTheorem.nontrivialZerosFinset B := by
      intro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨ρ, hρ, rfl⟩ := hz
      exact Finset.mem_preimage.mp hρ
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f := fun z : ℂ =>
        (analyticOrderNatAt riemannZeta z : ℝ) / ‖z‖) himg
      (fun x _ _ => div_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
    rw [Finset.sum_image (fun x _ y _ h => Subtype.coe_injective h)] at hsum
    refine le_trans ?_ hsum
    refine Finset.sum_le_sum fun ρ _ => ?_
    rw [div_eq_mul_inv]
  -- 第四步：常数吸收 `1 + log(B+6) ≤ (5/2)(1 + log B)`
  have hlog : Real.log (B + 6) ≤ Real.log B + 1 := by
    have h1 : B + 6 ≤ (5 / 2) * B := by linarith
    have h2 := Real.log_le_log (by linarith : (0 : ℝ) < B + 6) h1
    rw [Real.log_mul (by norm_num) (by linarith)] at h2
    have hlog25 : Real.log (5 / 2 : ℝ) ≤ 1 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      exact le_of_lt ((by norm_num : (5 / 2 : ℝ) < 2.7182818283).trans Real.exp_one_gt_d9)
    linarith
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
  have hfactor : (1 + Real.log (B + 6)) ^ 2 ≤ (25 / 4) * (1 + Real.log B) ^ 2 := by
    have hnn : (0 : ℝ) ≤ 1 + Real.log (B + 6) :=
      add_nonneg zero_le_one (Real.log_nonneg (by linarith))
    have h3 : 1 + Real.log (B + 6) ≤ 5 / 2 * (1 + Real.log B) := by linarith
    calc (1 + Real.log (B + 6)) ^ 2 ≤ (5 / 2 * (1 + Real.log B)) ^ 2 :=
        pow_le_pow_left₀ hnn h3 2
      _ = 25 / 4 * (1 + Real.log B) ^ 2 := by ring
  calc ∑ ρ ∈ (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
          (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn,
        (if ‖(ρ : ℂ)‖ < B then
          (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹
        else 0)
      ≤ ∑ ρ ∈ (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
          (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn,
        (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹ := hstep1
    _ = ∑ ρ ∈ (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
          (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn,
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹ := hstep2
    _ ≤ PrimeNumberTheorem.ExplicitFormulaAux.globalReciprocalZeroMultiplicity B := hstep3
    _ ≤ C₀ * (1 + Real.log (B + 6)) ^ 2 := hbound B hB
    _ ≤ C₀ * (25 / 4 * (1 + Real.log B) ^ 2) :=
        mul_le_mul_of_nonneg_left hfactor hC₀
    _ = 25 / 4 * C₀ * (1 + Real.log B) ^ 2 := by ring

/-! ## 尾部界：`Σ_{‖ρ‖ ≥ T} m_ξ(ρ)·‖ρ‖⁻² = O((1 + log T)/T)` -/

/-- **尾部计数界（无条件）**：存在 `C ≥ 0`，对所有 `T ≥ 4`，上半平面零点
在圆盘外 `‖ρ‖ ≥ T` 的 ξ-重数加权平方倒数和不超过 `C·(1 + log T)/T`。

证明要点：ξ 重数换 ζ 重数后，对任意有限子集用 `tsum_le_of_sum_le`。
截断部分逐点放缩 `‖ρ‖⁻¹ ≤ (2^(shellIdx+1))⁻¹` 并按壳分组；壳 `k` 的
重数和 `≤ globalZeroMultiplicity(2ᵏ⁺²) ≤ C₀·2ᵏ⁺²·(k+4)`，壳贡献
`≤ C₀·(k+4)·2⁻ᵏ`。`‖ρ‖ ≥ T` 的零点只出现在 `2ᵏ⁺² > T` 的壳中，即
`k ≥ K₀ := ⌈log₂ T⌉ − 2`；几何尾 `Σ_{j} g(j+K₀) = C₀·2⁻ᴷ⁰·(2 + 2(K₀+4))`
中 `2⁻ᴷ⁰ ≤ 4/T`、`K₀ + 4 ≤ 2·log T + 5`，合得 `48·C₀·(1+log T)/T`。 -/
theorem exists_upperZeros_tail_weighted_norm_inv_sq_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 4 ≤ T →
      (∑' ρ : UpperHalfPlaneNontrivialZero,
        if T ≤ ‖(ρ : ℂ)‖ then
          (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹ ^ 2
        else 0) ≤
        C * (1 + Real.log T) / T := by
  classical
  obtain ⟨C₀, hC₀, hcount⟩ :=
    PrimeNumberTheorem.ExplicitFormulaAux.exists_globalZeroMultiplicity_le_mul_log
  refine ⟨48 * C₀, mul_nonneg (by norm_num) hC₀, fun T hT => ?_⟩
  have hTpos : (0 : ℝ) < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlog2pos : (0 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  -- ξ 重数逐点换成 ζ 重数
  have hcongr : (fun ρ : UpperHalfPlaneNontrivialZero ↦
        if T ≤ ‖(ρ : ℂ)‖ then
          (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹ ^ 2
        else 0) =
      fun ρ : UpperHalfPlaneNontrivialZero ↦
        if T ≤ ‖(ρ : ℂ)‖ then
          (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹ ^ 2
        else 0 := by
    funext ρ
    split_ifs with hρ
    · rw [analyticOrderNatAt_xiFunction_eq_riemannZeta_of_isNontrivialZero
        ρ.2.1.2.1 ρ.2.1.2.2]
    · rfl
  rw [hcongr]
  -- 截断函数可和
  have hsumm : Summable fun ρ : UpperHalfPlaneNontrivialZero ↦
      if T ≤ ‖(ρ : ℂ)‖ then
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹ ^ 2
      else 0 :=
    Summable.of_nonneg_of_le
      (fun ρ => by
        split_ifs with hρ
        · exact mul_nonneg (Nat.cast_nonneg _) (by positivity)
        · exact le_refl 0)
      (fun ρ => by
        split_ifs with hρ
        · exact le_refl _
        · exact mul_nonneg (Nat.cast_nonneg _) (by positivity))
      summable_mul_norm_inv_sq_upperZeros
  -- 壳计数：每层二进上界（照 `summable_mul_norm_inv_sq_upperZeros` 证明的 hcount'）
  have hcount' : ∀ k : ℕ,
      PrimeNumberTheorem.ExplicitFormulaAux.globalZeroMultiplicity ((2 : ℝ) ^ (k + 2)) ≤
        C₀ * (2 : ℝ) ^ (k + 2) * ((k : ℝ) + 4) := by
    intro k
    have hTk : (4 : ℝ) ≤ (2 : ℝ) ^ (k + 2) := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h1 := hcount ((2 : ℝ) ^ (k + 2)) hTk
    have h2 : 1 + Real.log ((2 : ℝ) ^ (k + 2) + 6) ≤ (k : ℝ) + 4 := by
      have h3 := log_two_pow_add_six_le k
      linarith
    calc PrimeNumberTheorem.ExplicitFormulaAux.globalZeroMultiplicity ((2 : ℝ) ^ (k + 2))
        ≤ C₀ * (2 : ℝ) ^ (k + 2) * (1 + Real.log ((2 : ℝ) ^ (k + 2) + 6)) := h1
      _ ≤ C₀ * (2 : ℝ) ^ (k + 2) * ((k : ℝ) + 4) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hC₀ (by positivity))
  -- 壳级数 `g k = C₀·(k+4)·2⁻ᵏ` 可和
  have hgsumm : Summable fun k : ℕ ↦ C₀ * ((k : ℝ) + 4) * (1 / 2 : ℝ) ^ k := by
    have h1 : Summable fun k : ℕ ↦ C₀ * ((k : ℝ) ^ 1 * (1 / 2) ^ k) :=
      (summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1 / 2 : ℝ))
        (by norm_num)).mul_left C₀
    have h2 : Summable fun k : ℕ ↦ (4 * C₀) * (1 / 2 : ℝ) ^ k :=
      summable_geometric_two.mul_left (4 * C₀)
    refine (h1.add h2).congr fun k => ?_
    simp only [pow_one]
    ring
  -- 起始壳 `K₀ = ⌈log₂ T⌉ − 2`
  set K₀ : ℕ := ⌈Real.log T / Real.log 2⌉₊ - 2 with hK₀
  refine hsumm.tsum_le_of_sum_le fun s => ?_
  rw [← Finset.sum_filter]
  -- 逐点放缩到壳界
  have hpt : ∀ ρ ∈ s.filter (fun ρ : UpperHalfPlaneNontrivialZero ↦ T ≤ ‖(ρ : ℂ)‖),
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹ ^ 2 ≤
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) *
          (((2 : ℝ) ^ (shellIdx ‖(ρ : ℂ)‖ + 1))⁻¹) ^ 2 := by
    intro ρ hρ
    rw [Finset.mem_filter] at hρ
    have h2 : (2 : ℝ) ≤ ‖(ρ : ℂ)‖ := le_trans (by linarith) hρ.2
    have hpos : (0 : ℝ) < ‖(ρ : ℂ)‖ := lt_of_lt_of_le (by norm_num) h2
    have hle := (two_pow_shellIdx_add_one_le h2).1
    have hinv : ‖(ρ : ℂ)‖⁻¹ ≤ ((2 : ℝ) ^ (shellIdx ‖(ρ : ℂ)‖ + 1))⁻¹ :=
      (inv_le_inv₀ hpos (by positivity)).mpr hle
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hinv 2)
      (Nat.cast_nonneg _)
  have hMaps : ∀ ρ ∈ s.filter (fun ρ : UpperHalfPlaneNontrivialZero ↦ T ≤ ‖(ρ : ℂ)‖),
      shellIdx ‖(ρ : ℂ)‖ ∈ (s.filter
          (fun ρ : UpperHalfPlaneNontrivialZero ↦ T ≤ ‖(ρ : ℂ)‖)).image
        (fun σ : UpperHalfPlaneNontrivialZero ↦ shellIdx ‖(σ : ℂ)‖) :=
    fun ρ hρ => Finset.mem_image_of_mem _ hρ
  calc ∑ ρ ∈ s.filter (fun ρ : UpperHalfPlaneNontrivialZero ↦ T ≤ ‖(ρ : ℂ)‖),
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹ ^ 2
      ≤ ∑ ρ ∈ s.filter (fun ρ : UpperHalfPlaneNontrivialZero ↦ T ≤ ‖(ρ : ℂ)‖),
          (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) *
            (((2 : ℝ) ^ (shellIdx ‖(ρ : ℂ)‖ + 1))⁻¹) ^ 2 :=
        Finset.sum_le_sum hpt
    _ = ∑ k ∈ (s.filter (fun ρ : UpperHalfPlaneNontrivialZero ↦ T ≤ ‖(ρ : ℂ)‖)).image
            (fun σ : UpperHalfPlaneNontrivialZero ↦ shellIdx ‖(σ : ℂ)‖),
          ∑ ρ ∈ (s.filter (fun ρ : UpperHalfPlaneNontrivialZero ↦ T ≤ ‖(ρ : ℂ)‖)).filter
              (fun σ : UpperHalfPlaneNontrivialZero ↦ shellIdx ‖(σ : ℂ)‖ = k),
            (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) *
              (((2 : ℝ) ^ (shellIdx ‖(ρ : ℂ)‖ + 1))⁻¹) ^ 2 :=
        (Finset.sum_fiberwise_of_maps_to hMaps _).symm
    _ = ∑ k ∈ (s.filter (fun ρ : UpperHalfPlaneNontrivialZero ↦ T ≤ ‖(ρ : ℂ)‖)).image
            (fun σ : UpperHalfPlaneNontrivialZero ↦ shellIdx ‖(σ : ℂ)‖),
          (∑ ρ ∈ (s.filter (fun ρ : UpperHalfPlaneNontrivialZero ↦ T ≤ ‖(ρ : ℂ)‖)).filter
              (fun σ : UpperHalfPlaneNontrivialZero ↦ shellIdx ‖(σ : ℂ)‖ = k),
            (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ)) *
              (((2 : ℝ) ^ (k + 1))⁻¹) ^ 2 := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun ρ hρ => ?_
          rw [Finset.mem_filter] at hρ
          rw [hρ.2]
    _ ≤ ∑ k ∈ (s.filter (fun ρ : UpperHalfPlaneNontrivialZero ↦ T ≤ ‖(ρ : ℂ)‖)).image
            (fun σ : UpperHalfPlaneNontrivialZero ↦ shellIdx ‖(σ : ℂ)‖),
          (C₀ * (2 : ℝ) ^ (k + 2) * ((k : ℝ) + 4)) *
            (((2 : ℝ) ^ (k + 1))⁻¹) ^ 2 := by
          refine Finset.sum_le_sum fun k _ => ?_
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have himg : (((s.filter (fun ρ : UpperHalfPlaneNontrivialZero ↦
                    T ≤ ‖(ρ : ℂ)‖)).filter
                  (fun σ : UpperHalfPlaneNontrivialZero ↦ shellIdx ‖(σ : ℂ)‖ = k)).image
                  fun σ : UpperHalfPlaneNontrivialZero ↦ (σ : ℂ)) ⊆
              PrimeNumberTheorem.nontrivialZerosFinset ((2 : ℝ) ^ (k + 2)) := by
            intro z hz
            rw [Finset.mem_image] at hz
            obtain ⟨σ, hσ, rfl⟩ := hz
            rw [Finset.mem_filter, Finset.mem_filter] at hσ
            rw [PrimeNumberTheorem.mem_nontrivialZerosFinset]
            refine ⟨σ.2.1, ?_⟩
            have h2 : (2 : ℝ) ≤ ‖(σ : ℂ)‖ := le_trans (by linarith) hσ.1.2
            have hub := (two_pow_shellIdx_add_one_le (t := ‖(σ : ℂ)‖) h2).2
            rw [hσ.2] at hub
            exact (Complex.abs_im_le_norm _).trans hub.le
          have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f := fun z : ℂ =>
              (analyticOrderNatAt riemannZeta z : ℝ)) himg
            (fun x _ _ => Nat.cast_nonneg _)
          rw [Finset.sum_image (fun x _ y _ h => Subtype.coe_injective h)] at hsum
          exact hsum.trans (hcount' k)
    _ = ∑ k ∈ (s.filter (fun ρ : UpperHalfPlaneNontrivialZero ↦ T ≤ ‖(ρ : ℂ)‖)).image
            (fun σ : UpperHalfPlaneNontrivialZero ↦ shellIdx ‖(σ : ℂ)‖),
          C₀ * ((k : ℝ) + 4) * (1 / 2 : ℝ) ^ k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          have e1 : (((2 : ℝ) ^ (k + 1))⁻¹) ^ 2 = (1 / 2 : ℝ) ^ k * (1 / 2) ^ (k + 2) := by
            have h1 : (((2 : ℝ) ^ (k + 1))⁻¹) ^ 2 = (1 / 2 : ℝ) ^ (2 * (k + 1)) := by
              rw [inv_pow, ← pow_mul, mul_comm (k + 1) 2, ← inv_pow, inv_eq_one_div]
            rw [h1, show 2 * (k + 1) = k + (k + 2) by ring, pow_add]
          have e2 : (2 : ℝ) ^ (k + 2) * (1 / 2 : ℝ) ^ (k + 2) = 1 := by
            rw [← mul_pow, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_pow]
          calc (C₀ * (2 : ℝ) ^ (k + 2) * ((k : ℝ) + 4)) * (((2 : ℝ) ^ (k + 1))⁻¹) ^ 2
              = C₀ * ((k : ℝ) + 4) * (1 / 2 : ℝ) ^ k *
                  ((2 : ℝ) ^ (k + 2) * (1 / 2 : ℝ) ^ (k + 2)) := by
                rw [e1]
                ring
            _ = C₀ * ((k : ℝ) + 4) * (1 / 2 : ℝ) ^ k := by
                rw [e2]
                ring
    _ ≤ ∑' j : ℕ, C₀ * (((j + K₀ : ℕ) : ℝ) + 4) * (1 / 2 : ℝ) ^ (j + K₀) := by
          by_cases hne : ((s.filter (fun ρ : UpperHalfPlaneNontrivialZero ↦
              T ≤ ‖(ρ : ℂ)‖)).image
            (fun σ : UpperHalfPlaneNontrivialZero ↦ shellIdx ‖(σ : ℂ)‖)).Nonempty
          · set M := ((s.filter (fun ρ : UpperHalfPlaneNontrivialZero ↦
                T ≤ ‖(ρ : ℂ)‖)).image
              (fun σ : UpperHalfPlaneNontrivialZero ↦ shellIdx ‖(σ : ℂ)‖)).max' hne with hM
            have hsub : (s.filter (fun ρ : UpperHalfPlaneNontrivialZero ↦
                    T ≤ ‖(ρ : ℂ)‖)).image
                  (fun σ : UpperHalfPlaneNontrivialZero ↦ shellIdx ‖(σ : ℂ)‖) ⊆
                Finset.Ico K₀ (M + 1) := by
              intro k hk
              rw [Finset.mem_Ico]
              have hkM : k ≤ M := Finset.le_max' _ _ hk
              refine ⟨?_, by omega⟩
              rw [Finset.mem_image] at hk
              obtain ⟨σ, hσ, rfl⟩ := hk
              rw [Finset.mem_filter] at hσ
              have h2 : (2 : ℝ) ≤ ‖(σ : ℂ)‖ := le_trans (by linarith) hσ.2
              have hub := (two_pow_shellIdx_add_one_le h2).2
              have hTlt : T < (2 : ℝ) ^ (shellIdx ‖(σ : ℂ)‖ + 2) :=
                lt_of_le_of_lt hσ.2 hub
              have hlog := Real.log_lt_log hTpos hTlt
              rw [Real.log_pow] at hlog
              have hgt : Real.log T / Real.log 2 <
                  (shellIdx ‖(σ : ℂ)‖ : ℝ) + 2 := by
                rw [div_lt_iff₀ hlog2pos]
                push_cast at hlog
                exact hlog
              have hceil : ⌈Real.log T / Real.log 2⌉₊ ≤ shellIdx ‖(σ : ℂ)‖ + 2 := by
                refine Nat.ceil_le.mpr ?_
                have hgt' : Real.log T / Real.log 2 ≤
                    ((shellIdx ‖(σ : ℂ)‖ + 2 : ℕ) : ℝ) := by
                  push_cast
                  exact le_of_lt hgt
                exact hgt'
              rw [hK₀]
              omega
            calc ∑ k ∈ (s.filter (fun ρ : UpperHalfPlaneNontrivialZero ↦
                    T ≤ ‖(ρ : ℂ)‖)).image
                  (fun σ : UpperHalfPlaneNontrivialZero ↦ shellIdx ‖(σ : ℂ)‖),
                C₀ * ((k : ℝ) + 4) * (1 / 2 : ℝ) ^ k
              ≤ ∑ k ∈ Finset.Ico K₀ (M + 1),
                  C₀ * ((k : ℝ) + 4) * (1 / 2 : ℝ) ^ k :=
                Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ =>
                  mul_nonneg (mul_nonneg hC₀ (by positivity)) (by positivity)
            _ = ∑ j ∈ Finset.range (M + 1 - K₀),
                  C₀ * (((j + K₀ : ℕ) : ℝ) + 4) * (1 / 2 : ℝ) ^ (j + K₀) := by
                rw [Finset.sum_Ico_eq_sum_range]
                refine Finset.sum_congr rfl fun j _ => ?_
                rw [add_comm K₀ j]
            _ ≤ ∑' j : ℕ, C₀ * (((j + K₀ : ℕ) : ℝ) + 4) * (1 / 2 : ℝ) ^ (j + K₀) :=
                ((summable_nat_add_iff K₀).mpr hgsumm).sum_le_tsum _ fun j _ =>
                  mul_nonneg (mul_nonneg hC₀ (by positivity)) (by positivity)
          · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
            simp only [Finset.sum_empty]
            exact tsum_nonneg fun j =>
              mul_nonneg (mul_nonneg hC₀ (by positivity)) (by positivity)
    _ = C₀ * (1 / 2 : ℝ) ^ K₀ * (2 + 2 * ((K₀ : ℝ) + 4)) := by
          have hdecomp : ∀ j : ℕ,
              C₀ * (((j + K₀ : ℕ) : ℝ) + 4) * (1 / 2 : ℝ) ^ (j + K₀) =
                C₀ * (1 / 2 : ℝ) ^ K₀ * (((j : ℝ) + ((K₀ : ℝ) + 4)) * (1 / 2) ^ j) := by
            intro j
            rw [pow_add]
            push_cast
            ring
          rw [tsum_congr hdecomp, tsum_mul_left]
          congr 1
          have hsplit : (fun j : ℕ ↦ ((j : ℝ) + ((K₀ : ℝ) + 4)) * (1 / 2 : ℝ) ^ j) =
              fun j : ℕ ↦
                (j : ℝ) * (1 / 2 : ℝ) ^ j + ((K₀ : ℝ) + 4) * (1 / 2) ^ j := by
            funext j
            ring
          have hsum1 : Summable fun j : ℕ ↦ (j : ℝ) * (1 / 2 : ℝ) ^ j :=
            (summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1 / 2 : ℝ))
              (by norm_num)).congr fun k => by rw [pow_one]
          have hsum2 : Summable fun j : ℕ ↦ ((K₀ : ℝ) + 4) * (1 / 2 : ℝ) ^ j :=
            summable_geometric_two.mul_left _
          rw [hsplit, Summable.tsum_add hsum1 hsum2,
            tsum_coe_mul_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1),
            tsum_mul_left, tsum_geometric_two]
          have hval : (1 / 2 : ℝ) / (1 - 1 / 2) ^ 2 = 2 := by norm_num
          rw [hval]
          ring
    _ ≤ 48 * C₀ * (1 + Real.log T) / T := by
          -- `2⁻ᴷ⁰ ≤ 4/T`：`K₀ + 2 = ⌈log₂ T⌉` 给出 `2^(K₀+2) ≥ T`
          have hpow : (1 / 2 : ℝ) ^ K₀ ≤ 4 / T := by
            have hge : T ≤ (2 : ℝ) ^ (K₀ + 2) := by
              by_contra hcon
              push_neg at hcon
              have hlog := Real.log_lt_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ (K₀ + 2))
                hcon
              rw [Real.log_pow] at hlog
              have hK2 : K₀ + 2 = ⌈Real.log T / Real.log 2⌉₊ := by
                have hceilge : 2 ≤ ⌈Real.log T / Real.log 2⌉₊ := by
                  have hx : (2 : ℝ) ≤ Real.log T / Real.log 2 := by
                    rw [le_div_iff₀ hlog2pos]
                    have h2log : Real.log 4 = 2 * Real.log 2 := by
                      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
                      push_cast
                      ring
                    have h4 : Real.log 4 ≤ Real.log T := Real.log_le_log (by norm_num) hT
                    linarith
                  calc 2 = ⌈(2 : ℝ)⌉₊ := (Nat.ceil_natCast 2).symm
                    _ ≤ ⌈Real.log T / Real.log 2⌉₊ := Nat.ceil_mono hx
                omega
              have hleceil : Real.log T / Real.log 2 ≤
                  (⌈Real.log T / Real.log 2⌉₊ : ℝ) := Nat.le_ceil _
              have hle : Real.log T ≤ ((K₀ + 2 : ℕ) : ℝ) * Real.log 2 := by
                rw [← hK2] at hleceil
                exact (div_le_iff₀ hlog2pos).mp hleceil
              linarith
            have h4 : (2 : ℝ) ^ (K₀ + 2) = 4 * (2 : ℝ) ^ K₀ := by
              rw [pow_add, show (2 : ℝ) ^ (2 : ℕ) = 4 by norm_num]
              ring
            have h2K : T / 4 ≤ (2 : ℝ) ^ K₀ := by linarith
            have hpos2 : (0 : ℝ) < (2 : ℝ) ^ K₀ := by positivity
            have hposT : (0 : ℝ) < T / 4 := by linarith
            calc (1 / 2 : ℝ) ^ K₀ = ((2 : ℝ) ^ K₀)⁻¹ := by
                  rw [one_div, inv_pow]
              _ ≤ (T / 4)⁻¹ := (inv_le_inv₀ hpos2 hposT).mpr h2K
              _ = 4 / T := inv_div _ _
          -- `2 + 2(K₀+4) ≤ 12·(1 + log T)`：`K₀ ≤ 2·log T + 1`
          have hK₀le : (K₀ : ℝ) ≤ 2 * Real.log T + 1 := by
            have h1 : (K₀ : ℝ) ≤ (⌈Real.log T / Real.log 2⌉₊ : ℝ) := by
              rw [hK₀]
              exact_mod_cast Nat.sub_le _ _
            have h2 : (⌈Real.log T / Real.log 2⌉₊ : ℝ) ≤
                Real.log T / Real.log 2 + 1 :=
              (Nat.ceil_lt_add_one (div_nonneg hlogT hlog2pos.le)).le
            have h3 : Real.log T / Real.log 2 ≤ 2 * Real.log T := by
              rw [div_le_iff₀ hlog2pos]
              calc Real.log T = Real.log T * 1 := by ring
                _ ≤ Real.log T * (2 * Real.log 2) :=
                    mul_le_mul_of_nonneg_left
                      (by linarith [Real.log_two_gt_d9]) hlogT
                _ = 2 * Real.log T * Real.log 2 := by ring
            linarith
          have hvalue : 2 + 2 * ((K₀ : ℝ) + 4) ≤ 12 * (1 + Real.log T) := by linarith
          calc C₀ * (1 / 2 : ℝ) ^ K₀ * (2 + 2 * ((K₀ : ℝ) + 4))
              ≤ C₀ * (4 / T) * (12 * (1 + Real.log T)) :=
                mul_le_mul (mul_le_mul_of_nonneg_left hpow hC₀) hvalue
                  (by positivity)
                  (mul_nonneg hC₀ (div_nonneg (by norm_num) hTpos.le))
            _ = 48 * C₀ * (1 + Real.log T) / T := by ring

end RiemannExplorer
