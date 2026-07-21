/-
# 反向方向（Li 准则 ⇒ RH）：归约层与 Bombieri–Lagarias 机器的先行砖

本文件是 `li_criterion_implies_rh_target`（Li 准则蕴含 RH）的第一刀：
**不证明**反向主定理，而是把剩余缺口精确压缩为一个数学命题，并备齐
Bombieri–Lagarias（1999）论证的两块通用砖。

## 数学内容

记 `w(ρ) := 1 - 1/ρ`（`liPairedTerm n ρ = (1 - wⁿ) + (1 - w̄ⁿ)` 的底）。

1. **w-范数代数**（`half_le_re_of_norm_one_sub_inv_le_one`）：
   `‖1 - 1/s‖ ≤ 1 ↔ ‖s - 1‖ ≤ ‖s‖ ↔ re s ≥ 1/2`（`normSq` 展开后
   `(re-1)² ≤ re²`）。故「所有零点 `|w| ≤ 1`」等价于「所有零点
   `re ≥ 1/2`」；函数方程 `ρ ↦ 1 - ρ` 再给出 `re ≤ 1/2`，合为
   `re = 1/2`。
2. **归约主定理**（`rh_of_forall_upperZero_norm_one_sub_inv_le`）：
   `(∀ ρ 上半非平凡零点, ‖1 - 1/ρ‖ ≤ 1) → RiemannHypothesis.Statement`。
   虚部为负的零点取共轭（`isNontrivialZero_conj`）化到上半平面；
   实部上界由 `1 - s`（`isNontrivialZero_one_sub_conj` 复合）给出。
3. **缺口压缩**（`li_criterion_implies_rh_of_bl_bound`）：
   反向目标 `li_criterion_implies_rh_target` 归约为单一命题
   `LiCriterionHolds → ∀ ρ, ‖1 - 1/ρ‖ ≤ 1`（BL 核心）。
4. **有限性砖**（`finite_upperZeros_norm_one_sub_inv_ge`）：
   `r > 1` 时 `{ρ : r ≤ ‖1 - 1/ρ‖}` 有限——由
   `r‖ρ‖ ≤ ‖ρ - 1‖ ≤ ‖ρ‖ + 1` 得 `‖ρ‖ ≤ 1/(r-1)`，落入
   `nontrivialZerosFinset (1/(r-1))`。
5. **最大值存在砖**（`exists_max_norm_one_sub_inv`）：若存在
   `|w| > 1` 的零点（即 RH 不成立），则 `|w|` 在零点集上取到最大值
   `M > 1`（有限非空集上的最大值）——BL 主导项分析的起点。

## 证明纪律

无 `sorry`/`admit`/新公理；公理审计见 `Test/XiFunctionAxiomAudit.lean`。
-/

import RiemannExplorer.LiWeightedRepresentation

open Complex ComplexConjugate

namespace RiemannExplorer

/-- **w-范数代数**：`s ≠ 0` 且 `‖1 - 1/s‖ ≤ 1` 时 `re s ≥ 1/2`。
`‖1 - 1/s‖ = ‖s-1‖/‖s‖`，故条件等价于 `‖s-1‖ ≤ ‖s‖`；`normSq`
展开 `(re-1)² + im² ≤ re² + im²` 即 `-2re + 1 ≤ 0`。 -/
theorem half_le_re_of_norm_one_sub_inv_le_one {s : ℂ} (hs : s ≠ 0)
    (h : ‖1 - 1 / s‖ ≤ 1) : 1 / 2 ≤ s.re := by
  have hspos : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have hw : ‖1 - 1 / s‖ = ‖s - 1‖ / ‖s‖ := by
    have he : (1 : ℂ) - 1 / s = (s - 1) / s := by
      field_simp
    rw [he, norm_div]
  rw [hw, div_le_one hspos] at h
  have h2 : Complex.normSq (s - 1) ≤ Complex.normSq s := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [Complex.normSq_apply, Complex.normSq_apply] at h2
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
    sub_zero] at h2
  nlinarith [h2]

/-- **有限性砖**：`r > 1` 时 `{ρ : r ≤ ‖1 - 1/ρ‖}` 有限。
`r‖ρ‖ ≤ ‖ρ-1‖ ≤ ‖ρ‖ + 1` 给出 `‖ρ‖ ≤ 1/(r-1)`，故该集落入
`nontrivialZerosFinset (1/(r-1))`（有限）的原像。 -/
theorem finite_upperZeros_norm_one_sub_inv_ge {r : ℝ} (hr : 1 < r) :
    Set.Finite {ρ : UpperHalfPlaneNontrivialZero | r ≤ ‖1 - 1 / (ρ : ℂ)‖} := by
  have hr1 : (0 : ℝ) < r - 1 := by linarith
  refine Set.Finite.subset
    ((PrimeNumberTheorem.nontrivialZerosFinset (1 / (r - 1))).preimage
      (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn).finite_toSet
    fun ρ hρ => ?_
  have hρre := ρ.2.1.2.1
  have hρne : (ρ : ℂ) ≠ 0 := by
    intro hz
    rw [hz, Complex.zero_re] at hρre
    exact lt_irrefl 0 hρre
  have hρpos : 0 < ‖(ρ : ℂ)‖ := norm_pos_iff.mpr hρne
  have hw : ‖1 - 1 / (ρ : ℂ)‖ = ‖(ρ : ℂ) - 1‖ / ‖(ρ : ℂ)‖ := by
    have he : (1 : ℂ) - 1 / (ρ : ℂ) = ((ρ : ℂ) - 1) / (ρ : ℂ) := by
      field_simp
    rw [he, norm_div]
  have hρ' : r ≤ ‖1 - 1 / (ρ : ℂ)‖ := hρ
  rw [hw] at hρ'
  have hle1 : r * ‖(ρ : ℂ)‖ ≤ ‖(ρ : ℂ) - 1‖ := (le_div_iff₀ hρpos).mp hρ'
  have hle2 : ‖(ρ : ℂ) - 1‖ ≤ ‖(ρ : ℂ)‖ + 1 := by
    have h2 := norm_add_le (ρ : ℂ) (-1 : ℂ)
    rw [norm_neg, norm_one] at h2
    exact h2
  have hle3 : ‖(ρ : ℂ)‖ ≤ 1 / (r - 1) := by
    rw [le_div_iff₀ hr1]
    nlinarith [hle1, hle2]
  rw [Finset.mem_coe, Finset.mem_preimage, PrimeNumberTheorem.mem_nontrivialZerosFinset]
  exact ⟨ρ.2.1, (Complex.abs_im_le_norm _).trans hle3⟩

/-- **最大值存在砖**：若存在 `|w| > 1` 的上半非平凡零点（即 RH 不成立，
由 `ρ ↔ 1 - ρ` 对称），则 `|w|` 在全体上半零点上取到最大值 `M > 1`。
以任一 `|w₁| > 1` 的零点为门槛，候选集 `{|w| ≥ |w₁|}` 有限非空，
其最大值即全局最大值（集外 `< |w₁| ≤ M`）。 -/
theorem exists_max_norm_one_sub_inv
    (hne : ∃ ρ : UpperHalfPlaneNontrivialZero, 1 < ‖1 - 1 / (ρ : ℂ)‖) :
    ∃ ρ₀ : UpperHalfPlaneNontrivialZero, 1 < ‖1 - 1 / (ρ₀ : ℂ)‖ ∧
      ∀ ρ : UpperHalfPlaneNontrivialZero, ‖1 - 1 / (ρ : ℂ)‖ ≤ ‖1 - 1 / (ρ₀ : ℂ)‖ := by
  classical
  obtain ⟨ρ₁, hρ₁⟩ := hne
  have hfin := finite_upperZeros_norm_one_sub_inv_ge (r := ‖1 - 1 / (ρ₁ : ℂ)‖) hρ₁
  have hS : ρ₁ ∈ hfin.toFinset :=
    (Set.Finite.mem_toFinset _).mpr
      (show ‖1 - 1 / (ρ₁ : ℂ)‖ ≤ ‖1 - 1 / (ρ₁ : ℂ)‖ from le_rfl)
  obtain ⟨ρ₀, hρ₀S, hmax⟩ :=
    Finset.exists_max_image hfin.toFinset (fun ρ => ‖1 - 1 / (ρ : ℂ)‖) ⟨ρ₁, hS⟩
  have h1 := hmax ρ₁ hS
  refine ⟨ρ₀, by linarith [hρ₁], fun ρ => ?_⟩
  by_cases hρ : ‖1 - 1 / (ρ₁ : ℂ)‖ ≤ ‖1 - 1 / (ρ : ℂ)‖
  · exact hmax ρ ((Set.Finite.mem_toFinset _).mpr
      (show ‖1 - 1 / (ρ₁ : ℂ)‖ ≤ ‖1 - 1 / (ρ : ℂ)‖ from hρ))
  · have h2 := not_le.mp hρ
    linarith

/-- **归约主定理**：所有上半非平凡零点满足 `‖1 - 1/ρ‖ ≤ 1`（即
`re ρ ≥ 1/2`）蕴含 RH。虚部符号由共轭归一；实部上界由函数方程
`1 - s`（仍为非平凡零点，`re(1-s) = 1 - re s`）给出。 -/
theorem rh_of_forall_upperZero_norm_one_sub_inv_le
    (h : ∀ ρ : UpperHalfPlaneNontrivialZero, ‖1 - 1 / (ρ : ℂ)‖ ≤ 1) :
    RiemannHypothesis.Statement := by
  rw [riemannHypothesis_iff_xi_zeros_on_critical_line]
  intro s hξ h0 h1
  have hNTZ : RiemannHypothesis.IsNontrivialZero s :=
    (xiFunction_eq_zero_iff_isNontrivialZero h0 h1).mp hξ
  -- 任一非平凡零点的实部下界 `1/2 ≤ re t`
  have hge_of : ∀ t : ℂ, RiemannHypothesis.IsNontrivialZero t → 1 / 2 ≤ t.re := by
    intro t ht
    have htne : t ≠ 0 := by
      intro hz
      have h1' := ht.2.1
      rw [hz, Complex.zero_re] at h1'
      exact lt_irrefl 0 h1'
    have hξt : xiFunction t = 0 := (xiFunction_eq_zero_iff ht.2.1 ht.2.2).mpr ht.1
    rcases lt_or_gt_of_ne (xiFunction_zero_im_ne_zero hξt) with hlt | hgt
    · -- im t < 0：取共轭化到上半平面
      have hct : RiemannHypothesis.IsNontrivialZero (conj t) := isNontrivialZero_conj ht
      have himc : 0 < (conj t).im := by
        rw [Complex.conj_im]
        linarith
      have hρ := h ⟨conj t, hct, himc⟩
      have hccne : conj t ≠ 0 := by
        intro hz
        apply htne
        rw [← Complex.conj_conj t, hz]
        exact map_zero _
      have hcre := half_le_re_of_norm_one_sub_inv_le_one hccne hρ
      rwa [Complex.conj_re] at hcre
    · exact half_le_re_of_norm_one_sub_inv_le_one htne (h ⟨t, ht, hgt⟩)
  -- 实部上界：对 `1 - s` 应用下界
  have ht : RiemannHypothesis.IsNontrivialZero (1 - s) := by
    have ht0 := isNontrivialZero_one_sub_conj (isNontrivialZero_conj hNTZ)
    have he : (1 : ℂ) - conj (conj s) = 1 - s := by rw [Complex.conj_conj]
    rwa [he] at ht0
  have hle : s.re ≤ 1 / 2 := by
    have h2 := hge_of (1 - s) ht
    rw [Complex.sub_re, Complex.one_re] at h2
    linarith
  linarith [hge_of s hNTZ]

/-- **反向缺口的精确压缩**：若 Bombieri–Lagarias 核心命题
「Li 准则（`λ_n` 正实）⟹ 所有上半零点 `|w| ≤ 1`」成立，则
`li_criterion_implies_rh_target` 闭合。剩余工作即该命题本身
（生成函数 `log ξ(1/(1-z))` 的非负 Taylor 系数 + Vivanti–Pringsheim
奇点论证）。 -/
theorem li_criterion_implies_rh_of_bl_bound
    (hBL : LiCriterionHolds →
      ∀ ρ : UpperHalfPlaneNontrivialZero, ‖1 - 1 / (ρ : ℂ)‖ ≤ 1) :
    li_criterion_implies_rh_target :=
  fun hLi => rh_of_forall_upperZero_norm_one_sub_inv_le (hBL hLi)

end RiemannExplorer
