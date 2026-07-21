/-
# 加权 Li 零点求和的严格正性（B2 切片）

本文件是「RH ⇒ Li 准则」正向闭合的第二步（B2）：把 `LiStrictPositivity.lean`
中针对**无权重**配对级数的严格正性机器，平行提升为**重数加权**版本。
加权表示 `liCoefficient n = ∑' ρ, m_ξ(ρ)·liPairedTerm n ρ`（B1 切片，
`LiWeightedRepresentation.lean` 中无条件证明）是本文件的条件输入。

## 数学内容

与无权版完全平行：设 RH 成立且
`T_n := ∑' ρ, m_ξ(ρ)·liPairedTerm n ρ` 的实部为零。RH 下每项实部
`m_ξ(ρ)·(liPairedTerm n ρ).re ≥ 0`（`liPairedTerm_re_nonneg_of_rh` 乘
非负重数），非负实部级数和为零迫使每项实部为零；而零点处
`m_ξ(ρ) ≥ 1`（`one_le_analyticOrderNatAt_xiFunction_of_isNontrivialZero`），
故 `(liPairedTerm n ρ).re = 0`，即 `(1-1/ρ)ⁿ = 1` 对所有上半平面
非平凡零点成立。左端 `ρ ↦ 1-1/ρ` 单射且 `wⁿ = 1` 根集有限
（`finite_upperZeros_pow_eq_one`），与 Hardy 定理给出的零点无穷性
（`infinite_upperZeros`）矛盾。

## 主要定理

- `one_le_analyticOrderNatAt_xiFunction_of_isNontrivialZero`：非平凡零点
  处 ξ 的解析重数至少为 1（无条件）；
- `summable_weightedLiPairedTerm`：加权 Li 配对级数对每个 `n`（无条件）
  收敛——比较判别 `‖m·liPairedTerm‖ ≤ m·(2n+8·(3/2)ⁿ)·‖ρ‖⁻²`，
  后者由 `summable_xiOrder_mul_norm_inv_sq_upperZeros` 可和；
- `weightedLiPairedTerm_im` / `weightedLiPairedTerm_re_nonneg_of_rh` /
  `tsum_weightedLiPairedTerm_re_nonneg_of_rh`：加权项的实性、RH 下逐项
  实部非负、级数实部非负；
- `liCoefficient_re_pos_of_weighted_representation_of_rh`：**加权严格正性
  的条件归约**——加权表示 + RH ⇒ `0 < (liCoefficient n).re`；
- `rh_implies_li_criterion_of_weighted_representation`：**正向方向的条件
  证明（加权版）**——加权表示 ⇒ `rh_implies_li_criterion_target`。

## 证明纪律

无 `sorry`/`admit`/新公理；公理审计见 `Test/XiFunctionAxiomAudit.lean`。
-/

import RiemannExplorer.LiStrictPositivity
import RiemannExplorer.XiPartialFractionWeighted

open Complex ComplexConjugate
open scoped BigOperators

namespace RiemannExplorer

/-- **零点处重数至少为 1**（无条件）：`ρ` 是 `ζ` 的非平凡零点时
`ξ(ρ) = 0`（`xiFunction_eq_zero_iff_isNontrivialZero`），而 ξ 在 `ρ`
解析（整函数），故 `analyticOrderAt ξ ρ ≠ 0`；ξ 不恒为零
（`xiFunction_ne_eventually_zero`）给出 `analyticOrderAt ξ ρ ≠ ⊤`，
于是 `analyticOrderNatAt ξ ρ = (analyticOrderAt ξ ρ).toNat ≥ 1`。 -/
theorem one_le_analyticOrderNatAt_xiFunction_of_isNontrivialZero {s : ℂ}
    (hs : RiemannHypothesis.IsNontrivialZero s) :
    1 ≤ analyticOrderNatAt xiFunction s := by
  have hξ0 : xiFunction s = 0 :=
    (xiFunction_eq_zero_iff_isNontrivialZero hs.2.1 hs.2.2).mpr hs
  have h0 : analyticOrderAt xiFunction s ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨differentiable_xiFunction.analyticAt s, hξ0⟩
  have htop : analyticOrderAt xiFunction s ≠ ⊤ :=
    fun ht => xiFunction_ne_eventually_zero s (analyticOrderAt_eq_top.mp ht)
  have hto : analyticOrderNatAt xiFunction s ≠ 0 := by
    show (analyticOrderAt xiFunction s).toNat ≠ 0
    rw [Ne, ENat.toNat_eq_zero]
    exact fun h => h.elim h0 htop
  exact Nat.one_le_iff_ne_zero.mpr hto

/-- **加权 Li 配对级数可和**（无条件）：`Σ_ρ m_ξ(ρ)·liPairedTerm n ρ`
对每个 `n` 收敛。证明与 `summable_liPairedTerm` 平行：`‖ρ‖ < 2` 部分
有限支撑（`nontrivialZerosFinset 4` 的原像之外恒为零）；`‖ρ‖ ≥ 2` 部分
由 `norm_liPairedTerm_le` 给出 `‖m·liPairedTerm‖ ≤ m·(2n+8·(3/2)ⁿ)·‖ρ‖⁻²`，
后者可和由 `summable_xiOrder_mul_norm_inv_sq_upperZeros` 给出。 -/
theorem summable_weightedLiPairedTerm (n : ℕ) :
    Summable fun ρ : UpperHalfPlaneNontrivialZero ↦
      (analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) * liPairedTerm n (ρ : ℂ) := by
  classical
  have hsplit : (fun ρ : UpperHalfPlaneNontrivialZero ↦
        (analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) * liPairedTerm n (ρ : ℂ)) =
      (fun ρ : UpperHalfPlaneNontrivialZero ↦
          if ‖(ρ : ℂ)‖ < 2 then
            (analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) * liPairedTerm n (ρ : ℂ)
          else 0) +
        (fun ρ : UpperHalfPlaneNontrivialZero ↦
          if 2 ≤ ‖(ρ : ℂ)‖ then
            (analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) * liPairedTerm n (ρ : ℂ)
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
        (2 * (n : ℝ) + 8 * (3 / 2) ^ n) *
          ((analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹ ^ 2))
      (summable_xiOrder_mul_norm_inv_sq_upperZeros.mul_left _) fun ρ => ?_
    by_cases h : 2 ≤ ‖(ρ : ℂ)‖
    · rw [if_pos h]
      have hre : |(ρ : ℂ).re| ≤ 1 := by
        have h1 := ρ.2.1.2.1
        have h2 := ρ.2.1.2.2
        rw [abs_le]
        constructor <;> linarith
      calc ‖(analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) * liPairedTerm n (ρ : ℂ)‖
          = (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) *
              ‖liPairedTerm n (ρ : ℂ)‖ := by
            rw [norm_mul, RCLike.norm_natCast]
        _ ≤ (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) *
              ((2 * (n : ℝ) + 8 * (3 / 2) ^ n) * ‖(ρ : ℂ)‖⁻¹ ^ 2) :=
            mul_le_mul_of_nonneg_left (norm_liPairedTerm_le n h hre)
              (Nat.cast_nonneg _)
        _ = (2 * (n : ℝ) + 8 * (3 / 2) ^ n) *
              ((analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * ‖(ρ : ℂ)‖⁻¹ ^ 2) := by
            ring
    · rw [if_neg h, norm_zero]
      positivity

/-- 加权配对项的虚部为零（重数为自然数，配对项实值由
`liPairedTerm_im` 给出）。 -/
theorem weightedLiPairedTerm_im (n : ℕ) (ρ : UpperHalfPlaneNontrivialZero) :
    ((analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) * liPairedTerm n (ρ : ℂ)).im = 0 := by
  rw [Complex.mul_im, liPairedTerm_im]
  simp

/-- RH 下加权配对项实部非负：实部 `= m_ξ(ρ)·(liPairedTerm n ρ).re`，
非负重数乘非负项（`liPairedTerm_re_nonneg_of_rh`）。 -/
theorem weightedLiPairedTerm_re_nonneg_of_rh (hRH : RiemannHypothesis.Statement)
    (n : ℕ) (ρ : UpperHalfPlaneNontrivialZero) :
    0 ≤ ((analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) * liPairedTerm n (ρ : ℂ)).re := by
  have hre : ((analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) * liPairedTerm n (ρ : ℂ)).re =
      (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * (liPairedTerm n (ρ : ℂ)).re := by
    rw [Complex.mul_re]
    simp
  rw [hre]
  exact mul_nonneg (Nat.cast_nonneg _) (liPairedTerm_re_nonneg_of_rh hRH n ρ)

/-- RH 下加权配对级数的实部非负（逐项实性转移 + `tsum_nonneg`）。 -/
theorem tsum_weightedLiPairedTerm_re_nonneg_of_rh (hRH : RiemannHypothesis.Statement)
    (n : ℕ) :
    0 ≤ (∑' ρ : UpperHalfPlaneNontrivialZero,
      (analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) * liPairedTerm n (ρ : ℂ)).re := by
  have hnn : ∀ ρ : UpperHalfPlaneNontrivialZero,
      0 ≤ ((analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) * liPairedTerm n (ρ : ℂ)).re :=
    weightedLiPairedTerm_re_nonneg_of_rh hRH n
  have heq : (fun ρ : UpperHalfPlaneNontrivialZero ↦
        (analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) * liPairedTerm n (ρ : ℂ)) =
      fun ρ : UpperHalfPlaneNontrivialZero ↦
        ((((analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) *
          liPairedTerm n (ρ : ℂ)).re : ℝ) : ℂ) := by
    funext ρ
    refine Complex.ext ?_ ?_
    · rw [Complex.ofReal_re]
    · rw [Complex.ofReal_im]
      exact weightedLiPairedTerm_im n ρ
  rw [heq, ← Complex.ofReal_tsum, Complex.ofReal_re]
  exact tsum_nonneg hnn

/-- **加权严格正性的条件归约**：加权零点求和表示 + RH ⇒
`0 < (liCoefficient n).re`（对一切 `n ≥ 1`）。

证明结构与 `liCoefficient_re_pos_of_representation_of_rh` 相同：
表示定理给出 `(liCoefficient n).re = T_n.re ≥ 0`；若 `T_n.re = 0`，
非负实部级数（可和由 `summable_weightedLiPairedTerm` 经各项实性转移）
和为零，每项实部为零（`Summable.le_tsum` + 逐项非负），由
`m_ξ(ρ) ≥ 1` 剥掉重数得 `(liPairedTerm n ρ).re = 0`，于是每个零点满足
`(1-1/ρ)ⁿ = 1`（`liPairedTerm_eq_one_of_re_eq_zero_of_rh`），与
`finite_upperZeros_pow_eq_one`（有限）和 `infinite_upperZeros`
（无穷）矛盾。 -/
theorem liCoefficient_re_pos_of_weighted_representation_of_rh
    (hrep : ∀ n : ℕ, 1 ≤ n → liCoefficient n =
      ∑' ρ : UpperHalfPlaneNontrivialZero,
        (analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) * liPairedTerm n (ρ : ℂ))
    (hRH : RiemannHypothesis.Statement) (n : ℕ) (hn : 1 ≤ n) :
    0 < (liCoefficient n).re := by
  have hSnn := tsum_weightedLiPairedTerm_re_nonneg_of_rh hRH n
  have hS : (liCoefficient n).re =
      (∑' ρ : UpperHalfPlaneNontrivialZero,
        (analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) * liPairedTerm n (ρ : ℂ)).re := by
    rw [hrep n hn]
  rw [hS]
  refine lt_of_le_of_ne' hSnn fun hS0 => ?_
  have heq : (fun ρ : UpperHalfPlaneNontrivialZero ↦
        (analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) * liPairedTerm n (ρ : ℂ)) =
      fun ρ : UpperHalfPlaneNontrivialZero ↦
        ((((analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) *
          liPairedTerm n (ρ : ℂ)).re : ℝ) : ℂ) := by
    funext ρ
    refine Complex.ext ?_ ?_
    · rw [Complex.ofReal_re]
    · rw [Complex.ofReal_im]
      exact weightedLiPairedTerm_im n ρ
  have hfsum : Summable fun ρ : UpperHalfPlaneNontrivialZero ↦
      ((analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) * liPairedTerm n (ρ : ℂ)).re := by
    have hC := summable_weightedLiPairedTerm n
    rw [heq] at hC
    exact Complex.summable_ofReal.mp hC
  have hSre : (∑' ρ : UpperHalfPlaneNontrivialZero,
        (analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) * liPairedTerm n (ρ : ℂ)).re =
      ∑' ρ : UpperHalfPlaneNontrivialZero,
        ((analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) * liPairedTerm n (ρ : ℂ)).re := by
    rw [heq, ← Complex.ofReal_tsum, Complex.ofReal_re]
  have hterm0 : ∀ ρ : UpperHalfPlaneNontrivialZero,
      ((analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) * liPairedTerm n (ρ : ℂ)).re = 0 := by
    intro ρ
    have hle := Summable.le_tsum hfsum ρ
      (fun σ _ => weightedLiPairedTerm_re_nonneg_of_rh hRH n σ)
    rw [← hSre, hS0] at hle
    exact le_antisymm hle (weightedLiPairedTerm_re_nonneg_of_rh hRH n ρ)
  have hterm0' : ∀ ρ : UpperHalfPlaneNontrivialZero,
      (liPairedTerm n (ρ : ℂ)).re = 0 := by
    intro ρ
    have hm1 := one_le_analyticOrderNatAt_xiFunction_of_isNontrivialZero ρ.2.1
    have hm1r : (1 : ℝ) ≤ (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) := by
      exact_mod_cast hm1
    have h := hterm0 ρ
    have hre : ((analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) * liPairedTerm n (ρ : ℂ)).re =
        (analyticOrderNatAt xiFunction (ρ : ℂ) : ℝ) * (liPairedTerm n (ρ : ℂ)).re := by
      rw [Complex.mul_re]
      simp
    rw [hre] at h
    rcases mul_eq_zero.mp h with hm | ht
    · linarith
    · exact ht
  have hall : ∀ ρ : UpperHalfPlaneNontrivialZero, (1 - 1 / (ρ : ℂ)) ^ n = 1 :=
    fun ρ => liPairedTerm_eq_one_of_re_eq_zero_of_rh hRH n ρ (hterm0' ρ)
  have hfin := finite_upperZeros_pow_eq_one n hn
  rw [Set.eq_univ_of_forall hall] at hfin
  haveI := infinite_upperZeros
  exact Set.infinite_univ hfin

/-- **正向方向的条件证明（加权版）**：加权零点求和表示蕴含
`rh_implies_li_criterion_target`（RH ⇒ Li 准则）。虚部由
`liCoefficient_im`（无条件）给出，严格正性由
`liCoefficient_re_pos_of_weighted_representation_of_rh` 给出。 -/
theorem rh_implies_li_criterion_of_weighted_representation
    (hrep : ∀ n : ℕ, 1 ≤ n → liCoefficient n =
      ∑' ρ : UpperHalfPlaneNontrivialZero,
        (analyticOrderNatAt xiFunction (ρ : ℂ) : ℂ) * liPairedTerm n (ρ : ℂ)) :
    rh_implies_li_criterion_target :=
  fun hRH n hn =>
    ⟨liCoefficient_im n, liCoefficient_re_pos_of_weighted_representation_of_rh hrep hRH n hn⟩

end RiemannExplorer
