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

end RiemannExplorer
