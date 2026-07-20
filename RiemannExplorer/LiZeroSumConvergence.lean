/-
# Li 零点配对级数的无条件收敛性

本文件证明 Li 准则路线中零点级数的**无条件收敛性**：

```text
对每个 n : ℕ，级数
  Σ_{ρ : 上半平面非平凡零点} [1 - (1 - 1/ρ)ⁿ] + [1 - (1 - 1/conj ρ)ⁿ]
收敛（`Summable`）。
```

这正是 `RiemannExplorer.li_zero_sum_representation_target`
（`LiCriterion.lean`）右端 `∑'` 良定义的直接前置：
该目标从「形式书写一个未必收敛的级数」升级为「真收敛级数上的恒等式」。

## 证明路线（全部无条件，无 sorry）

- **Part A（二项式余项估计）**：`norm_one_sub_one_sub_pow_sub_le`——
  对 `‖w‖ ≤ 1/2`，

  ```text
  ‖1 - (1-w)ⁿ - n·w‖ ≤ 4·(3/2)ⁿ·‖w‖²
  ```

  由 `add_pow` 展开并剥去前两项，尾部用 `‖w‖ᵏ ≤ (1/2)ᵏ⁻²·‖w‖²`
  与二项式恒等式 `Σ C(n,j)(1/2)ʲ = (3/2)ⁿ` 控制。

- **Part B（范数平方倒数级数）**：`summable_norm_inv_sq_upperZeros`——
  `Σ ‖ρ‖⁻²` 在上半平面零点上收敛。方法：任意有限子集按 `‖ρ‖ < 2`
  与 `‖ρ‖ ≥ 2` 拆分；低点落入固定有限集 `nontrivialZerosFinset 4`；
  高点按二进壳 `2ᵏ⁺¹ ≤ ‖ρ‖ < 2ᵏ⁺²` 分组，壳计数由仓库已有的零点计数
  `PrimeNumberTheorem.exists_card_nontrivialZerosFinset_le_mul_log`
  （`N(T) ≤ C·T·(1+log(T+6))`）控制，壳贡献求和为收敛几何级数
  `C·(k+4)·2⁻ᵏ`，最后由 `summable_of_sum_le` 收尾。

- **Part C（配对项估计与主定理）**：配对使线性项相消——
  `1/ρ + 1/conj ρ = 2·Re(1/ρ) = 2·ρ.re/‖ρ‖²`，而 `|ρ.re| ≤ 1`，
  故配对项范数 `≤ (2n + 8·(3/2)ⁿ)·‖ρ‖⁻²`；高低拆分后由
  `summable_of_ne_finset_zero` 与 `Summable.of_norm_bounded` 得
  `summable_liPairedTerm`，即 `summable_li_zero_sum_terms`。

## 与硬卡点的关系

`li_zero_sum_representation_target` 本身还需要 ξ'/ξ 的部分分式展开
（Hadamard 因子分解级），这是 Mathlib 缺失的分析工具，不属于本文件。
本文件消除的是该目标路线上的**收敛性工作量卡点**。
-/

import RiemannExplorer.LiCriterion
import PrimeNumberTheorem.GlobalZeroCount

open Complex ComplexConjugate
open scoped BigOperators

namespace RiemannExplorer

/-! ## Part A：二项式余项估计 -/

/-- 二项式尾部恒等式（`n = m + 2` 情形）：
`1 - (1-w)ⁿ - n·w = -∑_{k < m+1} (-w)^{k+2}·C(n, k+2)`。 -/
theorem one_sub_one_sub_pow_sub_eq (m : ℕ) (w : ℂ) :
    1 - (1 - w) ^ (m + 2) - ((m + 2 : ℕ) : ℂ) * w =
      -∑ k ∈ Finset.range (m + 1), (-w) ^ (k + 2) * (((m + 2).choose (k + 2) : ℕ) : ℂ) := by
  have hexp : (1 - w) ^ (m + 2) =
      ∑ k ∈ Finset.range (m + 2 + 1), (-w) ^ k * (((m + 2).choose k : ℕ) : ℂ) := by
    have h := add_pow (-w) (1 : ℂ) (m + 2)
    rw [show (1 : ℂ) - w = -w + 1 by ring, h]
    exact Finset.sum_congr rfl fun k _ => by rw [one_pow, mul_one]
  rw [hexp]
  show 1 - (∑ k ∈ Finset.range (m + 1 + 1 + 1), (-w) ^ k * (((m + 2).choose k : ℕ) : ℂ))
      - ((m + 2 : ℕ) : ℂ) * w =
    -∑ k ∈ Finset.range (m + 1), (-w) ^ (k + 2) * (((m + 2).choose (k + 2) : ℕ) : ℂ)
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [show ∀ k : ℕ, k + 1 + 1 = k + 2 from fun k => rfl]
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, pow_one,
    Nat.choose_one_right, zero_add]
  ring

/-- 二项式余项的范数界：对 `‖w‖ ≤ 1/2`，
`‖1 - (1-w)ⁿ - n·w‖ ≤ 4·(3/2)ⁿ·‖w‖²`。
这是配对零点级数 `O(1/‖ρ‖²)` 控制的局部来源。 -/
theorem norm_one_sub_one_sub_pow_sub_le (n : ℕ) {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖1 - (1 - w) ^ n - (n : ℂ) * w‖ ≤ 4 * (3 / 2) ^ n * ‖w‖ ^ 2 := by
  rcases n with _ | _ | m
  · rw [show (1 : ℂ) - (1 - w) ^ 0 - ((0 : ℕ) : ℂ) * w = 0 by push_cast; ring, norm_zero]
    positivity
  · rw [show (1 : ℂ) - (1 - w) ^ 1 - ((1 : ℕ) : ℂ) * w = 0 by push_cast; ring, norm_zero]
    positivity
  · rw [one_sub_one_sub_pow_sub_eq m w, norm_neg]
    have h2nn : (0 : ℝ) ≤ ‖w‖ ^ 2 := sq_nonneg _
    have htail : ∑ k ∈ Finset.range (m + 1), (((m + 2).choose (k + 2) : ℕ) : ℝ) * (1 / 2) ^ k
        ≤ 4 * (3 / 2) ^ (m + 2) := by
      have h1 : ∀ k : ℕ, (((m + 2).choose (k + 2) : ℕ) : ℝ) * (1 / 2) ^ k =
          4 * ((((m + 2).choose (k + 2) : ℕ) : ℝ) * (1 / 2) ^ (k + 2)) := by
        intro k
        rw [pow_add]
        ring
      rw [Finset.sum_congr rfl (fun k _ => h1 k), ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      have hshift : ∑ k ∈ Finset.range (m + 1), (((m + 2).choose (k + 2) : ℕ) : ℝ) * (1 / 2) ^ (k + 2)
          = ∑ j ∈ Finset.Ico 2 (m + 3), (((m + 2).choose j : ℕ) : ℝ) * (1 / 2) ^ j := by
        conv_rhs => rw [Finset.sum_Ico_eq_sum_range]
        exact Finset.sum_congr (rfl : Finset.range (m + 3 - 2) = Finset.range (m + 1))
          fun k _ => by rw [Nat.add_comm 2 k]
      rw [hshift]
      have hsum : ∑ j ∈ Finset.range (m + 3), (((m + 2).choose j : ℕ) : ℝ) * (1 / 2) ^ j
          = (3 / 2 : ℝ) ^ (m + 2) := by
        have h := add_pow (1 / 2 : ℝ) 1 (m + 2)
        rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, h]
        exact Finset.sum_congr rfl fun j _ => by rw [one_pow, mul_one, mul_comm]
      rw [← hsum]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => by positivity)
      intro x hx
      simp only [Finset.mem_Ico] at hx
      simp only [Finset.mem_range]
      omega
    calc ‖∑ k ∈ Finset.range (m + 1), (-w) ^ (k + 2) * (((m + 2).choose (k + 2) : ℕ) : ℂ)‖
        ≤ ∑ k ∈ Finset.range (m + 1),
            ‖(-w) ^ (k + 2) * (((m + 2).choose (k + 2) : ℕ) : ℂ)‖ := norm_sum_le _ _
      _ = ∑ k ∈ Finset.range (m + 1),
            ‖w‖ ^ (k + 2) * (((m + 2).choose (k + 2) : ℕ) : ℝ) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [norm_mul, norm_pow, norm_neg, Complex.norm_natCast]
      _ ≤ ∑ k ∈ Finset.range (m + 1),
            (1 / 2) ^ k * ‖w‖ ^ 2 * (((m + 2).choose (k + 2) : ℕ) : ℝ) := by
          refine Finset.sum_le_sum fun k _ => ?_
          have hk : ‖w‖ ^ (k + 2) ≤ (1 / 2) ^ k * ‖w‖ ^ 2 := by
            rw [pow_add]
            exact mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ (norm_nonneg w) hw k) h2nn
          exact mul_le_mul_of_nonneg_right hk (Nat.cast_nonneg _)
      _ = ‖w‖ ^ 2 * ∑ k ∈ Finset.range (m + 1),
            (((m + 2).choose (k + 2) : ℕ) : ℝ) * (1 / 2) ^ k := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ ≤ ‖w‖ ^ 2 * (4 * (3 / 2) ^ (m + 2)) := mul_le_mul_of_nonneg_left htail h2nn
      _ = 4 * (3 / 2) ^ (m + 2) * ‖w‖ ^ 2 := by ring

/-! ## Part B：上半平面零点的 `‖ρ‖⁻²` 可和性 -/

/-- 对数辅助界：`log(2ᵏ⁺² + 6) ≤ k + 3`。
证明：`2ᵏ⁺² + 6 ≤ (5/2)·2ᵏ⁺²`，而 `log(5/2) ≤ 1`（因 `5/2 < e`）、
`log 2 ≤ 1`（因 `log x ≤ x - 1`）。 -/
theorem log_two_pow_add_six_le (k : ℕ) : Real.log ((2 : ℝ) ^ (k + 2) + 6) ≤ k + 3 := by
  have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ (k + 2) := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (k + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h1 : (2 : ℝ) ^ (k + 2) + 6 ≤ (5 / 2) * 2 ^ (k + 2) := by linarith
  have h2 := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ (k + 2) + 6) h1
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h2
  have hlog25 : Real.log (5 / 2 : ℝ) ≤ 1 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    exact le_of_lt ((by norm_num : (5 / 2 : ℝ) < 2.7182818283).trans Real.exp_one_gt_d9)
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  calc Real.log ((2 : ℝ) ^ (k + 2) + 6) ≤ Real.log (5 / 2) + ↑(k + 2) * Real.log 2 := h2
  _ ≤ 1 + ↑(k + 2) * 1 :=
      add_le_add hlog25 (mul_le_mul_of_nonneg_left hlog2 (by positivity))
  _ = k + 3 := by push_cast; ring

/-- 二进壳指标：对 `2 ≤ t` 满足 `2^(shellIdx t + 1) ≤ t < 2^(shellIdx t + 2)`。
取 `Nat.log 2 ⌊t⌋₊ - 1`；存在性由 `Nat.pow_log_le_self` 与
`Nat.lt_pow_succ_log_self` 给出。 -/
noncomputable def shellIdx (t : ℝ) : ℕ := Nat.log 2 ⌊t⌋₊ - 1

/-- 壳指标的基本性质：`t ≥ 2` 落在第 `shellIdx t` 个二进壳内。 -/
theorem two_pow_shellIdx_add_one_le {t : ℝ} (ht : 2 ≤ t) :
    (2 : ℝ) ^ (shellIdx t + 1) ≤ t ∧ t < (2 : ℝ) ^ (shellIdx t + 2) := by
  have hfloor : 2 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast ht)
  have hne : ⌊t⌋₊ ≠ 0 := by omega
  have h1 : 2 ^ Nat.log 2 ⌊t⌋₊ ≤ ⌊t⌋₊ := Nat.pow_log_le_self 2 hne
  have h2 : ⌊t⌋₊ < 2 ^ (Nat.log 2 ⌊t⌋₊).succ := Nat.lt_pow_succ_log_self (by norm_num) _
  have hlog : 1 ≤ Nat.log 2 ⌊t⌋₊ :=
    Nat.le_log_of_pow_le (by norm_num) (by rwa [pow_one])
  have hsh1 : shellIdx t + 1 = Nat.log 2 ⌊t⌋₊ := by unfold shellIdx; omega
  have hsh2 : shellIdx t + 2 = (Nat.log 2 ⌊t⌋₊).succ := by unfold shellIdx; omega
  rw [hsh1, hsh2]
  refine ⟨?_, ?_⟩
  · calc (2 : ℝ) ^ Nat.log 2 ⌊t⌋₊ ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast h1
    _ ≤ t := Nat.floor_le (le_trans (by norm_num) ht)
  · calc t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
    _ ≤ (2 : ℝ) ^ (Nat.log 2 ⌊t⌋₊).succ := by exact_mod_cast Nat.add_one_le_of_lt h2

/-- **Part B 主定理**：`Σ ‖ρ‖⁻²` 在上半平面非平凡零点上（无条件）收敛。

证明：任意有限子集按 `‖ρ‖ < 2` 与 `‖ρ‖ ≥ 2` 拆分。低点落入固定有限集
`nontrivialZerosFinset 4`；高点按二进壳 `2ᵏ⁺¹ ≤ ‖ρ‖ < 2ᵏ⁺²` 分组，
壳内零点数由全局零点计数
`PrimeNumberTheorem.exists_card_nontrivialZerosFinset_le_mul_log`
（`N(T) ≤ C·T·(1 + log(T+6))`，取 `T = 2ᵏ⁺² ≥ 4`）控制为
`C·2ᵏ⁺²·(k+4)`，壳贡献 `≤ C·(k+4)·2⁻ᵏ`，对 `k` 求和收敛
（几何级数与 `k·2⁻ᵏ`），最后由 `summable_of_sum_le` 收尾。 -/
theorem summable_norm_inv_sq_upperZeros :
    Summable fun ρ : UpperHalfPlaneNontrivialZero ↦ ‖(ρ : ℂ)‖⁻¹ ^ 2 := by
  classical
  obtain ⟨C, hC, hcount⟩ :=
    PrimeNumberTheorem.ExplicitFormulaAux.exists_card_nontrivialZerosFinset_le_mul_log
  -- 每个二进壳中的零点数上界
  have hcard : ∀ k : ℕ,
      ((PrimeNumberTheorem.nontrivialZerosFinset ((2 : ℝ) ^ (k + 2))).card : ℝ) ≤
        C * (2 : ℝ) ^ (k + 2) * ((k : ℝ) + 4) := by
    intro k
    have hT : (4 : ℝ) ≤ (2 : ℝ) ^ (k + 2) := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h1 := hcount ((2 : ℝ) ^ (k + 2)) hT
    have h2 : 1 + Real.log ((2 : ℝ) ^ (k + 2) + 6) ≤ (k : ℝ) + 4 := by
      have h3 := log_two_pow_add_six_le k
      linarith
    calc ((PrimeNumberTheorem.nontrivialZerosFinset ((2 : ℝ) ^ (k + 2))).card : ℝ)
        ≤ C * (2 : ℝ) ^ (k + 2) * (1 + Real.log ((2 : ℝ) ^ (k + 2) + 6)) := h1
      _ ≤ C * (2 : ℝ) ^ (k + 2) * ((k : ℝ) + 4) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hC (by positivity))
  -- 收敛的几何参考级数 C·(k+4)·2⁻ᵏ
  have hgeom : Summable fun k : ℕ ↦ C * ((k : ℝ) + 4) * (1 / 2 : ℝ) ^ k := by
    have h1 : Summable fun k : ℕ ↦ C * ((k : ℝ) ^ 1 * (1 / 2) ^ k) :=
      (summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1 / 2 : ℝ))
        (by norm_num)).mul_left C
    have h2 : Summable fun k : ℕ ↦ (4 * C) * (1 / 2 : ℝ) ^ k :=
      summable_geometric_two.mul_left (4 * C)
    refine (h1.add h2).congr fun k => ?_
    simp only [pow_one]
    ring
  refine summable_of_sum_le
    (c := ∑ ρ ∈ (PrimeNumberTheorem.nontrivialZerosFinset 4).preimage
          (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn,
        ‖(ρ : ℂ)‖⁻¹ ^ 2 +
      ∑' k : ℕ, C * ((k : ℝ) + 4) * (1 / 2 : ℝ) ^ k) (fun ρ => by positivity) ?_
  intro u
  rw [← Finset.sum_filter_add_sum_filter_not u
    (fun ρ : UpperHalfPlaneNontrivialZero ↦ ‖(ρ : ℂ)‖ < 2)]
  -- 低点部分：落入固定有限集 nontrivialZerosFinset 4 的原像
  have hlow : ∑ ρ ∈ u.filter (fun ρ : UpperHalfPlaneNontrivialZero ↦ ‖(ρ : ℂ)‖ < 2), ‖(ρ : ℂ)‖⁻¹ ^ 2 ≤
      ∑ ρ ∈ (PrimeNumberTheorem.nontrivialZerosFinset 4).preimage
          (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn,
        ‖(ρ : ℂ)‖⁻¹ ^ 2 := by
    have hpre : u.filter (fun ρ : UpperHalfPlaneNontrivialZero ↦ ‖(ρ : ℂ)‖ < 2) ⊆
        (PrimeNumberTheorem.nontrivialZerosFinset 4).preimage
          (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      rw [Finset.mem_preimage, PrimeNumberTheorem.mem_nontrivialZerosFinset]
      exact ⟨ρ.2.1, ((Complex.abs_im_le_norm _).trans hρ.2.le).trans (by norm_num)⟩
    exact Finset.sum_le_sum_of_subset_of_nonneg hpre (fun x _ _ => by positivity)
  -- 高点部分：二进壳分组
  have hhigh : ∑ ρ ∈ u.filter (fun ρ : UpperHalfPlaneNontrivialZero ↦ ¬ ‖(ρ : ℂ)‖ < 2), ‖(ρ : ℂ)‖⁻¹ ^ 2 ≤
      ∑' k : ℕ, C * ((k : ℝ) + 4) * (1 / 2 : ℝ) ^ k := by
    have hpt : ∀ ρ ∈ u.filter (fun ρ : UpperHalfPlaneNontrivialZero ↦ ¬ ‖(ρ : ℂ)‖ < 2),
        ‖(ρ : ℂ)‖⁻¹ ^ 2 ≤ (((2 : ℝ) ^ (shellIdx ‖(ρ : ℂ)‖ + 1))⁻¹) ^ 2 := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      have h2 : (2 : ℝ) ≤ ‖(ρ : ℂ)‖ := le_of_not_gt hρ.2
      have hpos : (0 : ℝ) < ‖(ρ : ℂ)‖ := lt_of_lt_of_le (by norm_num) h2
      have hle := (two_pow_shellIdx_add_one_le h2).1
      have hinv : ‖(ρ : ℂ)‖⁻¹ ≤ ((2 : ℝ) ^ (shellIdx ‖(ρ : ℂ)‖ + 1))⁻¹ :=
        (inv_le_inv₀ hpos (by positivity)).mpr hle
      exact pow_le_pow_left₀ (by positivity) hinv 2
    have hMaps : ∀ ρ ∈ u.filter (fun ρ : UpperHalfPlaneNontrivialZero ↦ ¬ ‖(ρ : ℂ)‖ < 2),
        shellIdx ‖(ρ : ℂ)‖ ∈ (u.filter (fun ρ : UpperHalfPlaneNontrivialZero ↦ ¬ ‖(ρ : ℂ)‖ < 2)).image
          (fun σ : UpperHalfPlaneNontrivialZero ↦ shellIdx ‖(σ : ℂ)‖) :=
      fun ρ hρ => Finset.mem_image_of_mem _ hρ
    calc ∑ ρ ∈ u.filter (fun ρ : UpperHalfPlaneNontrivialZero ↦ ¬ ‖(ρ : ℂ)‖ < 2), ‖(ρ : ℂ)‖⁻¹ ^ 2
        ≤ ∑ ρ ∈ u.filter (fun ρ : UpperHalfPlaneNontrivialZero ↦ ¬ ‖(ρ : ℂ)‖ < 2),
            (((2 : ℝ) ^ (shellIdx ‖(ρ : ℂ)‖ + 1))⁻¹) ^ 2 := Finset.sum_le_sum hpt
      _ = ∑ k ∈ (u.filter (fun ρ : UpperHalfPlaneNontrivialZero ↦ ¬ ‖(ρ : ℂ)‖ < 2)).image
              (fun σ : UpperHalfPlaneNontrivialZero ↦ shellIdx ‖(σ : ℂ)‖),
            ∑ ρ ∈ (u.filter (fun ρ : UpperHalfPlaneNontrivialZero ↦ ¬ ‖(ρ : ℂ)‖ < 2)).filter
              (fun σ : UpperHalfPlaneNontrivialZero ↦ shellIdx ‖(σ : ℂ)‖ = k),
            (((2 : ℝ) ^ (shellIdx ‖(ρ : ℂ)‖ + 1))⁻¹) ^ 2 :=
          (Finset.sum_fiberwise_of_maps_to hMaps _).symm
      _ = ∑ k ∈ (u.filter (fun ρ : UpperHalfPlaneNontrivialZero ↦ ¬ ‖(ρ : ℂ)‖ < 2)).image
              (fun σ : UpperHalfPlaneNontrivialZero ↦ shellIdx ‖(σ : ℂ)‖),
            (((u.filter (fun ρ : UpperHalfPlaneNontrivialZero ↦ ¬ ‖(ρ : ℂ)‖ < 2)).filter
                (fun σ : UpperHalfPlaneNontrivialZero ↦ shellIdx ‖(σ : ℂ)‖ = k)).card : ℝ) *
              (((2 : ℝ) ^ (k + 1))⁻¹) ^ 2 := by
          refine Finset.sum_congr rfl fun k _ => ?_
          trans ∑ _ρ ∈ (u.filter (fun ρ : UpperHalfPlaneNontrivialZero ↦ ¬ ‖(ρ : ℂ)‖ < 2)).filter
              (fun σ : UpperHalfPlaneNontrivialZero ↦ shellIdx ‖(σ : ℂ)‖ = k), (((2 : ℝ) ^ (k + 1))⁻¹) ^ 2
          · exact Finset.sum_congr rfl fun ρ hρ => by
              rw [Finset.mem_filter] at hρ
              rw [hρ.2]
          · rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ k ∈ (u.filter (fun ρ : UpperHalfPlaneNontrivialZero ↦ ¬ ‖(ρ : ℂ)‖ < 2)).image
              (fun σ : UpperHalfPlaneNontrivialZero ↦ shellIdx ‖(σ : ℂ)‖),
            C * ((k : ℝ) + 4) * (1 / 2 : ℝ) ^ k := by
          refine Finset.sum_le_sum fun k _ => ?_
          have hcardk : (((u.filter (fun ρ : UpperHalfPlaneNontrivialZero ↦ ¬ ‖(ρ : ℂ)‖ < 2)).filter
                  (fun σ : UpperHalfPlaneNontrivialZero ↦ shellIdx ‖(σ : ℂ)‖ = k)).card : ℝ) ≤
              C * (2 : ℝ) ^ (k + 2) * ((k : ℝ) + 4) := by
            have himg : (((u.filter (fun ρ : UpperHalfPlaneNontrivialZero ↦ ¬ ‖(ρ : ℂ)‖ < 2)).filter
                    (fun σ : UpperHalfPlaneNontrivialZero ↦ shellIdx ‖(σ : ℂ)‖ = k)).image
                  fun σ : UpperHalfPlaneNontrivialZero ↦ (σ : ℂ)) ⊆
                PrimeNumberTheorem.nontrivialZerosFinset ((2 : ℝ) ^ (k + 2)) := by
              intro z hz
              rw [Finset.mem_image] at hz
              obtain ⟨σ, hσ, rfl⟩ := hz
              rw [Finset.mem_filter, Finset.mem_filter] at hσ
              rw [PrimeNumberTheorem.mem_nontrivialZerosFinset]
              refine ⟨σ.2.1, ?_⟩
              have h2 : (2 : ℝ) ≤ ‖(σ : ℂ)‖ := le_of_not_gt hσ.1.2
              have hub := (two_pow_shellIdx_add_one_le (t := ‖(σ : ℂ)‖) h2).2
              rw [hσ.2] at hub
              exact (Complex.abs_im_le_norm _).trans hub.le
            have hcardimg := Finset.card_le_card himg
            rw [Finset.card_image_of_injective _ Subtype.coe_injective] at hcardimg
            have hcardimg' : (((u.filter (fun ρ : UpperHalfPlaneNontrivialZero ↦
                    ¬ ‖(ρ : ℂ)‖ < 2)).filter
                  (fun σ : UpperHalfPlaneNontrivialZero ↦ shellIdx ‖(σ : ℂ)‖ = k)).card : ℝ) ≤
                ((PrimeNumberTheorem.nontrivialZerosFinset ((2 : ℝ) ^ (k + 2))).card : ℝ) := by
              exact_mod_cast hcardimg
            exact hcardimg'.trans (hcard k)
          have heq : (C * (2 : ℝ) ^ (k + 2) * ((k : ℝ) + 4)) *
                (((2 : ℝ) ^ (k + 1))⁻¹) ^ 2 = C * ((k : ℝ) + 4) * (1 / 2 : ℝ) ^ k := by
            have e1 : (((2 : ℝ) ^ (k + 1))⁻¹) ^ 2 = (1 / 2 : ℝ) ^ k * (1 / 2) ^ (k + 2) := by
              have h1 : (((2 : ℝ) ^ (k + 1))⁻¹) ^ 2 = (1 / 2 : ℝ) ^ (2 * (k + 1)) := by
                rw [inv_pow, ← pow_mul, mul_comm (k + 1) 2, ← inv_pow, inv_eq_one_div]
              rw [h1, show 2 * (k + 1) = k + (k + 2) by ring, pow_add]
            rw [e1]
            have e2 : (2 : ℝ) ^ (k + 2) * (1 / 2 : ℝ) ^ (k + 2) = 1 := by
              rw [← mul_pow, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_pow]
            calc C * 2 ^ (k + 2) * (k + 4) * ((1 / 2 : ℝ) ^ k * (1 / 2) ^ (k + 2))
                = C * (k + 4) * (1 / 2) ^ k * (2 ^ (k + 2) * (1 / 2) ^ (k + 2)) := by
                  ring
              _ = C * (k + 4) * (1 / 2 : ℝ) ^ k * 1 := by rw [e2]
              _ = C * (k + 4) * (1 / 2 : ℝ) ^ k := by ring
          calc (((u.filter (fun ρ : UpperHalfPlaneNontrivialZero ↦ ¬ ‖(ρ : ℂ)‖ < 2)).filter
                  (fun σ : UpperHalfPlaneNontrivialZero ↦ shellIdx ‖(σ : ℂ)‖ = k)).card : ℝ) *
                (((2 : ℝ) ^ (k + 1))⁻¹) ^ 2
              ≤ (C * (2 : ℝ) ^ (k + 2) * ((k : ℝ) + 4)) *
                  (((2 : ℝ) ^ (k + 1))⁻¹) ^ 2 :=
                mul_le_mul_of_nonneg_right hcardk (by positivity)
            _ = C * ((k : ℝ) + 4) * (1 / 2 : ℝ) ^ k := heq
      _ ≤ ∑' k : ℕ, C * ((k : ℝ) + 4) * (1 / 2 : ℝ) ^ k :=
          hgeom.sum_le_tsum _ (fun k _ =>
            mul_nonneg (mul_nonneg hC (by positivity)) (by positivity))
  exact add_le_add hlow hhigh

/-! ## Part C：配对项的 `O(1/‖ρ‖²)` 控制与主定理 -/

/-- Li 零点级数的共轭配对项：与 `li_zero_sum_representation_target`
（`LiCriterion.lean`）的被加项逐字一致。 -/
noncomputable def liPairedTerm (n : ℕ) (ρ : ℂ) : ℂ :=
  ((1 : ℂ) - (1 - 1 / ρ) ^ n) + ((1 : ℂ) - (1 - 1 / conj ρ) ^ n)

/-- 配对项拆成「线性主项 + 两个二项式余项」（纯代数恒等式）。
收敛性的关键在于：配对后线性项 `n·(1/ρ + 1/conj ρ)` 仍受 `O(1/‖ρ‖²)`
控制（见 `norm_liPairedTerm_le`），未配对时 `n/ρ` 不绝对可和。 -/
theorem liPairedTerm_eq (n : ℕ) (ρ : ℂ) :
    liPairedTerm n ρ = (n : ℂ) * (1 / ρ + 1 / conj ρ) +
      ((1 - (1 - 1 / ρ) ^ n - (n : ℂ) * (1 / ρ)) +
        (1 - (1 - 1 / conj ρ) ^ n - (n : ℂ) * (1 / conj ρ))) := by
  unfold liPairedTerm
  ring

/-- 配对项的范数界：对 `‖ρ‖ ≥ 2` 且 `|ρ.re| ≤ 1`（非平凡零点自动满足后者，
因为 `0 < ρ.re < 1`），

```text
‖liPairedTerm n ρ‖ ≤ (2n + 8·(3/2)ⁿ)·‖ρ‖⁻²。
```

证明：`1/ρ + 1/conj ρ = 2·Re(ρ⁻¹) = 2·ρ.re/normSq ρ`（`Complex.add_conj` +
`Complex.inv_re`），其范数 `≤ 2·‖ρ‖⁻²`；两个余项各由 Part A 的
`norm_one_sub_one_sub_pow_sub_le`（取 `w = 1/ρ`、`w = 1/conj ρ`，
范数 `≤ 1/2`）控制为 `4·(3/2)ⁿ·‖ρ‖⁻²`。 -/
theorem norm_liPairedTerm_le (n : ℕ) {ρ : ℂ} (hρ2 : 2 ≤ ‖ρ‖) (hre : |ρ.re| ≤ 1) :
    ‖liPairedTerm n ρ‖ ≤ (2 * (n : ℝ) + 8 * (3 / 2) ^ n) * ‖ρ‖⁻¹ ^ 2 := by
  have hρ0 : ρ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hρ2
    norm_num at hρ2
  have hnormSq : (0 : ℝ) < Complex.normSq ρ := Complex.normSq_pos.mpr hρ0
  have hmain : (1 : ℂ) / ρ + 1 / conj ρ = ((2 * ρ.re / Complex.normSq ρ : ℝ) : ℂ) := by
    rw [one_div, one_div, ← Complex.conj_inv, Complex.add_conj, Complex.inv_re]
    congr 1
    ring
  have hmain_norm : ‖(n : ℂ) * (1 / ρ + 1 / conj ρ)‖ ≤ 2 * (n : ℝ) * ‖ρ‖⁻¹ ^ 2 := by
    rw [hmain, norm_mul, Complex.norm_natCast, norm_real, Real.norm_eq_abs]
    have habs : |2 * ρ.re / Complex.normSq ρ| = 2 * |ρ.re| / Complex.normSq ρ := by
      rw [abs_div, abs_of_pos hnormSq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hle : 2 * |ρ.re| / Complex.normSq ρ ≤ 2 * ‖ρ‖⁻¹ ^ 2 := by
      have h1 : 2 * |ρ.re| ≤ 2 * 1 := mul_le_mul_of_nonneg_left hre (by norm_num)
      have h2 : 2 * |ρ.re| / Complex.normSq ρ ≤ 2 * 1 / Complex.normSq ρ :=
        div_le_div_of_nonneg_right h1 hnormSq.le
      have h3 : 2 * 1 / Complex.normSq ρ = 2 * ‖ρ‖⁻¹ ^ 2 := by
        rw [Complex.normSq_eq_norm_sq, inv_pow]
        ring
      exact h2.trans_eq h3
    calc (n : ℝ) * |2 * ρ.re / Complex.normSq ρ|
        = (n : ℝ) * (2 * |ρ.re| / Complex.normSq ρ) := by rw [habs]
      _ ≤ (n : ℝ) * (2 * ‖ρ‖⁻¹ ^ 2) := mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _)
      _ = 2 * (n : ℝ) * ‖ρ‖⁻¹ ^ 2 := by ring
  have hz1 : ‖(1 : ℂ) / ρ‖ ≤ 1 / 2 := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le (by norm_num) hρ2
  have hz2 : ‖(1 : ℂ) / conj ρ‖ ≤ 1 / 2 := by
    rw [norm_div, norm_one, Complex.norm_conj]
    exact one_div_le_one_div_of_le (by norm_num) hρ2
  calc ‖liPairedTerm n ρ‖
      = ‖(n : ℂ) * (1 / ρ + 1 / conj ρ) +
          ((1 - (1 - 1 / ρ) ^ n - (n : ℂ) * (1 / ρ)) +
            (1 - (1 - 1 / conj ρ) ^ n - (n : ℂ) * (1 / conj ρ)))‖ := by
        rw [liPairedTerm_eq]
    _ ≤ ‖(n : ℂ) * (1 / ρ + 1 / conj ρ)‖ +
          (‖1 - (1 - 1 / ρ) ^ n - (n : ℂ) * (1 / ρ)‖ +
            ‖1 - (1 - 1 / conj ρ) ^ n - (n : ℂ) * (1 / conj ρ)‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ (2 * (n : ℝ) * ‖ρ‖⁻¹ ^ 2) +
          (4 * (3 / 2) ^ n * ‖(1 : ℂ) / ρ‖ ^ 2 +
            4 * (3 / 2) ^ n * ‖(1 : ℂ) / conj ρ‖ ^ 2) :=
        add_le_add hmain_norm
          (add_le_add (norm_one_sub_one_sub_pow_sub_le n hz1)
            (norm_one_sub_one_sub_pow_sub_le n hz2))
    _ = (2 * (n : ℝ) + 8 * (3 / 2) ^ n) * ‖ρ‖⁻¹ ^ 2 := by
        have e1 : ‖(1 : ℂ) / ρ‖ = ‖ρ‖⁻¹ := by rw [norm_div, norm_one, one_div]
        have e2 : ‖(1 : ℂ) / conj ρ‖ = ‖ρ‖⁻¹ := by
          rw [norm_div, norm_one, Complex.norm_conj, one_div]
        rw [e1, e2]
        ring

/-- **Part C 主定理**：Li 零点配对级数对每个 `n`（无条件）收敛。

证明：按 `‖ρ‖ < 2` 与 `‖ρ‖ ≥ 2` 把被加项拆成两个函数。低点函数在
`nontrivialZerosFinset 4` 的原像之外恒为零（有限支撑，
`summable_of_ne_finset_zero`）；高点函数由
`norm_liPairedTerm_le`（`|ρ.re| ≤ 1` 来自 `0 < ρ.re < 1`）被
`(2n + 8·(3/2)ⁿ)·‖ρ‖⁻²` 控制，后者可和由 Part B 的
`summable_norm_inv_sq_upperZeros` 给出（`Summable.of_norm_bounded`）。 -/
theorem summable_liPairedTerm (n : ℕ) :
    Summable fun ρ : UpperHalfPlaneNontrivialZero ↦ liPairedTerm n (ρ : ℂ) := by
  classical
  have hsplit : (fun ρ : UpperHalfPlaneNontrivialZero ↦ liPairedTerm n (ρ : ℂ)) =
      (fun ρ : UpperHalfPlaneNontrivialZero ↦
          if ‖(ρ : ℂ)‖ < 2 then liPairedTerm n (ρ : ℂ) else 0) +
        (fun ρ : UpperHalfPlaneNontrivialZero ↦
          if 2 ≤ ‖(ρ : ℂ)‖ then liPairedTerm n (ρ : ℂ) else 0) := by
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
        (2 * (n : ℝ) + 8 * (3 / 2) ^ n) * ‖(ρ : ℂ)‖⁻¹ ^ 2)
      (summable_norm_inv_sq_upperZeros.mul_left _) fun ρ => ?_
    by_cases h : 2 ≤ ‖(ρ : ℂ)‖
    · rw [if_pos h]
      have hre : |(ρ : ℂ).re| ≤ 1 := by
        have h1 := ρ.2.1.2.1
        have h2 := ρ.2.1.2.2
        rw [abs_le]
        constructor <;> linarith
      exact norm_liPairedTerm_le n h hre
    · rw [if_neg h, norm_zero]
      positivity

/-- `li_zero_sum_representation_target` 右端级数对每个 `n`（无条件）收敛：
该目标从「形式书写一个未必收敛的级数」升级为「真收敛级数上的恒等式」。
这就是 `li_zero_sum_representation_target` 在「ξ'/ξ 部分分式展开」
（Hardamard 因子分解级，Mathlib 缺失）之外的全部收敛性前置。 -/
theorem summable_li_zero_sum_terms (n : ℕ) :
    Summable fun ρ : UpperHalfPlaneNontrivialZero ↦
      (((1 : ℂ) - (1 - 1 / (ρ : ℂ)) ^ n) + ((1 : ℂ) - (1 - 1 / conj (ρ : ℂ)) ^ n)) :=
  summable_liPairedTerm n

end RiemannExplorer
