/-
# 反向方向切片 A：生成函数 `F(z) = log ξ(1/(1-z))` 的局部机器

本文件是 Bombieri–Lagarias 反向路线缺口 2（Taylor 系数桥）的第一切片：

```text
F(z) := log ξ(1/(1-z))，收敛幂级数  Σ_{k≥1} (λ_k/k)·z^k + λ_0
```

## 数学路线（已定案）

`L(s) = log ξ(s)` 在 `s = 1` 解析（Part 1 的对数分支，复可微 ⇒ 解析），
Taylor 展开 `L(1+y) = Σ_n (L⁽ⁿ⁾(1)/n!)·yⁿ`（`hasSum_iteratedFDeriv`）。
代入 `y = φ(z) - 1 = z/(1-z)`：`(s-1)^j = z^j·(1-z)^{-j}`，而
`(1-z)^{-j} = Σ_m C(m+j-1, j-1)·z^m`（Newton 级数，
`hasSum_choose_mul_geometric_of_norm_lt_one`）。双重级数重组后

```text
[z^k] F = Σ_{j=1}^k (-1)^{j-1}·R_j/j·C(k-1, j-1) = λ_k / k
```

末一等号由 `(j+1)·C(k, j+1) = k·C(k-1, j)`（`Nat.add_one_mul_choose_eq`）
与 Part 6 的 `liCoefficient_eq_sum_choose_invResid` 给出。

## 本切片内容

- `analyticAt_log_xi_one_sub_inv`：`F` 在 `z = 0` 解析
  （对数分支解析 ∘ `z ↦ 1/(1-z)`）；
- `hasSum_taylor_log_xi_one`：`L` 在 `s = 1` 的 Taylor hasSum
  （`hasSum_iteratedFDeriv` 的一维标量化：`p n (y^…)` = `L⁽ⁿ⁾(1)·yⁿ`）；
- `sum_choose_invResid_div_eq_liCoefficient_div`：有限系数恒等式
  `Σ_{j<k} (-1)^j·C(k-1,j)/(j+1)·R_{j+1} = λ_k/k`（纯代数，BL 桥的
  组合心脏）。

下一切片（缺口 2 收尾）：双重级数重组（`z/(1-z)` 代入 + antidiagonal
分组）得 `HasSum (fun k => (λ_k/k)·z^k) (F z - λ_0)`。

## 证明纪律

无 `sorry`/`admit`/新公理；公理审计见 `Test/XiFunctionAxiomAudit.lean`。
-/

import RiemannExplorer.LiConverse

open Complex ComplexConjugate Filter
open scoped BigOperators Topology

namespace RiemannExplorer

/-- **生成函数在 0 解析**：`F(z) = log ξ(1/(1-z))` 是解析函数的复合
（`z ↦ 1/(1-z)` 在 0 解析且取值 `1`；`log ∘ ξ` 在 `s = 1` 解析，
Part 1 的对数分支复可微性经 `DifferentiableOn.analyticAt` 升级）。 -/
theorem analyticAt_log_xi_one_sub_inv :
    AnalyticAt ℂ (fun z => Complex.log (xiFunction (1 / (1 - z)))) 0 := by
  obtain ⟨r₀, hr₀, hball⟩ := exists_ball_xi_re_pos
  have hL : AnalyticAt ℂ (fun s => Complex.log (xiFunction s)) 1 :=
    (differentiableOn_log_xi hr₀ hball).analyticAt (Metric.ball_mem_nhds 1 hr₀)
  have hφ : AnalyticAt ℂ (fun z : ℂ => 1 / (1 - z)) 0 := by
    have h1 : AnalyticAt ℂ (fun z : ℂ => (1 : ℂ) - z) 0 :=
      analyticAt_const.sub analyticAt_id
    have hne : (1 : ℂ) - 0 ≠ 0 := by norm_num
    have h2 := h1.inv hne
    simpa only [one_div] using h2
  exact AnalyticAt.comp (g := fun s => Complex.log (xiFunction s))
    (f := fun z : ℂ => 1 / (1 - z)) (x := 0) hL hφ

/-- **`L` 在 `s = 1` 的 Taylor hasSum**：存在 `r > 0`，`‖y‖ < r` 时

```text
L(1 + y) = Σ_{n≥0} (L⁽ⁿ⁾(1)/n!)·yⁿ。
```

由 `AnalyticAt` 取 `HasFPowerSeriesOnBall`，`hasSum_iteratedFDeriv`
给出多重线性形式，再经 `map_smul_univ`（对角输入 `y^…`）标量化。 -/
theorem hasSum_taylor_log_xi_one :
    ∃ r : ℝ, 0 < r ∧ ∀ {y : ℂ}, ‖y‖ < r →
      HasSum (fun n => (iteratedDeriv n (fun s => Complex.log (xiFunction s)) 1 /
          (Nat.factorial n : ℂ)) * y ^ n)
        (Complex.log (xiFunction (1 + y))) := by
  obtain ⟨r₀, hr₀, hball⟩ := exists_ball_xi_re_pos
  have hL : AnalyticAt ℂ (fun s => Complex.log (xiFunction s)) 1 :=
    (differentiableOn_log_xi hr₀ hball).analyticAt (Metric.ball_mem_nhds 1 hr₀)
  obtain ⟨p, r, hballp⟩ := hL
  -- ℝ 半径：`min r 1` 非 ⊤ 且正，取其 `toReal`
  have hr1 : (0 : ℝ≥0∞) < min r 1 := lt_min hballp.r_pos (by norm_num)
  have hr1top : min r (1 : ℝ≥0∞) ≠ ⊤ :=
    ne_top_of_le_ne_top (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) (min_le_right _ _)
  refine ⟨(min r 1).toReal, ENNReal.toReal_pos (ne_of_gt hr1) hr1top, fun {y} hy => ?_⟩
  -- `y ∈ eball 0 r`（`ofReal_toReal` + `eball_ofReal` + 半径单调）
  have hy' : y ∈ Metric.eball (0 : ℂ) r := by
    have h1 : y ∈ Metric.ball (0 : ℂ) (min r 1).toReal := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      exact hy
    have h2 : y ∈ Metric.eball (0 : ℂ) (min r 1) := by
      rw [show min r (1 : ℝ≥0∞) = ENNReal.ofReal (min r 1).toReal from
        (ENNReal.ofReal_toReal hr1top).symm, Metric.eball_ofReal]
      exact h1
    exact EMetric.ball_subset_ball (min_le_left _ _) h2
  have hs := hballp.hasSum_iteratedFDeriv hy'
  -- 一维标量化：`iteratedFDeriv n L 1 (y^…) = (L⁽ⁿ⁾ 1) * yⁿ`
  refine hs.congr_fun fun n => ?_
  have hdiag : iteratedFDeriv ℂ n (fun s => Complex.log (xiFunction s)) 1 (fun _ => y) =
      (iteratedDeriv n (fun s => Complex.log (xiFunction s)) 1) * y ^ n := by
    have hsm := ContinuousMultilinearMap.map_smul_univ
      (iteratedFDeriv ℂ n (fun s => Complex.log (xiFunction s)) 1) (fun _ : Fin n => y)
      (fun _ : Fin n => (1 : ℂ))
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hsm
    have h1 : (fun _ : Fin n => y) = (fun i : Fin n => y • (1 : ℂ)) := by
      funext i
      rw [Pi.smul_apply, smul_eq_mul, mul_one]
    rw [h1, hsm, smul_eq_mul]
    show y ^ n * iteratedDeriv n (fun s => Complex.log (xiFunction s)) 1 = _
    rw [mul_comm]
  rw [hdiag]
  show (Nat.factorial n : ℂ)⁻¹ •
      (iteratedDeriv n (fun s => Complex.log (xiFunction s)) 1 * y ^ n) =
    (iteratedDeriv n (fun s => Complex.log (xiFunction s)) 1 / (Nat.factorial n : ℂ)) * y ^ n
  rw [smul_eq_mul, div_eq_mul_inv]
  ring

/-- **BL 系数恒等式（有限代数心脏）**：`k ≥ 1` 时

```text
Σ_{j=0}^{k-1} (-1)^j·C(k-1,j)/(j+1)·R_{j+1} = λ_k / k。
```

由 Part 6 的 `liCoefficient_eq_sum_choose_invResid`（`λ_k =
Σ (-1)^j·C(k,j+1)·R_{j+1}`）逐项用 `(j+1)·C(k,j+1) = k·C(k-1,j)`
（`Nat.add_one_mul_choose_eq`）除以 `k`。 -/
theorem sum_choose_invResid_div_eq_liCoefficient_div (k : ℕ) (hk : 1 ≤ k)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hball : ∀ s ∈ Metric.ball (1 : ℂ) r, 0 < (xiFunction s).re)
    (hρfar : ∀ ρ : UpperHalfPlaneNontrivialZero,
      r ≤ ‖1 - (ρ : ℂ)‖ ∧ r ≤ ‖1 - conj (ρ : ℂ)‖) :
    (∑ j ∈ Finset.range k,
        (-1 : ℂ) ^ j * ((k - 1).choose j : ℂ) / ((j : ℂ) + 1) *
          xiWeightedInvResidSum (j + 1)) =
      liCoefficient k / (k : ℂ) := by
  rw [liCoefficient_eq_sum_choose_invResid hr0 hr1 hball hρfar k hk, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  -- Nat 恒等式：`(j+1)·C(k,j+1) = k·C(k-1,j)`
  have hNat : (j + 1) * k.choose (j + 1) = k * (k - 1).choose j := by
    rw [show k = k - 1 + 1 from by omega, mul_comm ((j + 1)) _]
    exact (Nat.add_one_mul_choose_eq (k - 1) j).symm
  have hid : ((j : ℂ) + 1) * (k.choose (j + 1) : ℂ) = (k : ℂ) * ((k - 1).choose j : ℂ) := by
    exact_mod_cast hNat
  have hkc : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hj1 : (j : ℂ) + 1 ≠ 0 := by
    have h : ((j : ℂ) + 1) = ((j + 1 : ℕ) : ℂ) := by
      rw [Nat.cast_add, Nat.cast_one]
    rw [h]
    exact Nat.cast_ne_zero.mpr (by omega)
  have hdiv : ((k - 1).choose j : ℂ) / ((j : ℂ) + 1) = (k.choose (j + 1) : ℂ) / (k : ℂ) := by
    rw [div_eq_div_iff hj1 hkc]
    linear_combination hid
  rw [hdiv]
  field_simp
  ring

end RiemannExplorer
