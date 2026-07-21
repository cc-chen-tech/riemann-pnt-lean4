/-
# de Bruijn–Newman 常数 Λ 方向 · 第一阶段骨架 (Phase-0 skeleton)

本文件是 de Bruijn–Newman 常数方向的**第一阶段开拓骨架**，配套调研笔记见
`docs/research/de-bruijn-newman-note.md`（含文献锚点、Mathlib 差距分析、
分阶段工作量与风险表）。全仓此前对该方向零提及。

## 数学对象

```
Φ(u) := Σ_{n ≥ 1} (2π²n⁴ e^{9u} − 3πn² e^{5u}) · exp(−πn² e^{4u}),
H_t(z) := ∫_0^∞ e^{t u²} Φ(u) cos(z u) du,
Λ := inf { t ∈ ℝ : H_t 只有实零点 }.
```

经典事实链（文献锚点见调研笔记）：
- de Bruijn (1950)：单调性（`H_t` 实零点 ⇒ `t' ≥ t` 时 `H_{t'}` 实零点）与
  `Λ ≤ 1/2`；
- Newman (1976)：`Λ > −∞`，并猜想 `Λ ≥ 0`；
- Rodgers–Tao (arXiv:1801.05914, 2018；Forum Math. Pi 8, 2020, e6)：`Λ ≥ 0`；
- RH 的逻辑位置：`RH ⇔ Λ ≤ 0`（经 `H_0(z) = (1/8)·Ξ(z/2)` 与阈值性质）。

## 本文件的证明面（sorry-free）

- `phiTerm_zero`：`n = 0` 项为 `0`，故 `ℕ` 上级数与经典 `n ≥ 1` 级数一致；
- `abs_phiTerm_le`：项级几何界 `|phiTerm n u| ≤ C(u) · n⁴ rⁿ`，`r = e^{−π e^{4u}}`；
- `summable_phiTerm_all` / `summable_phiTerm`：`Φ` 定义级数对每个 `u : ℝ`
  （绝对）收敛——这是本阶段对适定性（well-definedness）的实质推进；
- `norm_cos_le_exp_abs_im` / `norm_cos_mul_ofReal_le_exp`：`H_t` 被积函数
  增长控制所需的余弦界 `‖cos(z·u)‖ ≤ e^{|Im(z)·u|}`（积分收敛性证明的
  两个组成部分之一）。

## Prop 目标（按 `docs/implementation-standards.md` 纪律，全部 `def : Prop`）

`heat_integrand_integrable_target`（适定性）、`phi_even_target`（Φ 偶性，
等价于 ζ 函数方程）、`h_even_entire_target`（H_t 偶整函数）、
`backward_heat_equation_target`（反向热方程 `∂_t H_t = −∂_z² H_t`）、
`de_bruijn_monotone_target`、`lambda_le_half_target`（Λ ≤ 1/2）、
`newman_lower_bound_target`（Λ > −∞）、`lambda_nonneg_target`（Λ ≥ 0，
Rodgers–Tao）、`rh_iff_lambda_le_zero_target`（RH ⇔ Λ ≤ 0）。

上述目标**均未证明**，亦不得以任何形式引用为已证定理。
-/

import RiemannExplorer

namespace RiemannExplorer
namespace DeBruijnNewman

/-! ## Φ：项级定义与级数收敛性 -/

/-- The `n`-th summand of the de Bruijn–Newman kernel series
`Φ(u) = Σ_{n ≥ 1} (2π²n⁴ e^{9u} − 3πn² e^{5u}) exp(−πn² e^{4u})`.
The `n = 0` value is `0`, so indexing over all of `ℕ` gives the same series. -/
noncomputable def phiTerm (n : ℕ) (u : ℝ) : ℝ :=
  (2 * Real.pi ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u)
      - 3 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u))
    * Real.exp (-(Real.pi * (n : ℝ) ^ 2 * Real.exp (4 * u)))

/-- The `n = 0` summand vanishes: the `ℕ`-indexed series is the classical
`n ≥ 1` series. -/
theorem phiTerm_zero (u : ℝ) : phiTerm 0 u = 0 := by
  simp [phiTerm]

/-- Pointwise geometric bound for the kernel summands: with
`r = exp (−π e^{4u}) ∈ (0, 1)` one has
`|phiTerm n u| ≤ (2π² e^{9u} + 3π e^{5u}) · n⁴ rⁿ`.
This is the comparison input for absolute convergence of the `Φ` series. -/
theorem abs_phiTerm_le (u : ℝ) (n : ℕ) :
    |phiTerm n u| ≤
      (2 * Real.pi ^ 2 * Real.exp (9 * u) + 3 * Real.pi * Real.exp (5 * u))
        * ((n : ℝ) ^ 4 * Real.exp (-(Real.pi * Real.exp (4 * u))) ^ n) := by
  have h0 : phiTerm n u =
      (2 * Real.pi ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u)
          - 3 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u))
        * Real.exp (-(Real.pi * (n : ℝ) ^ 2 * Real.exp (4 * u))) := rfl
  have hA : 0 ≤ 2 * Real.pi ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u) := by positivity
  have hB : 0 ≤ 3 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u) := by positivity
  have hAB : |2 * Real.pi ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u)
        - 3 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u)|
      ≤ 2 * Real.pi ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u)
        + 3 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u) := by
    rw [abs_le]; constructor <;> linarith
  have hEr : Real.exp (-(Real.pi * (n : ℝ) ^ 2 * Real.exp (4 * u)))
      ≤ Real.exp (-(Real.pi * Real.exp (4 * u))) ^ n := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hnn : (n : ℝ) ≤ (n : ℝ) ^ 2 := le_self_pow₀ h1 (by norm_num)
      have hpe : 0 ≤ Real.pi * Real.exp (4 * u) := by positivity
      have h2 : Real.pi * (n : ℝ) * Real.exp (4 * u)
          ≤ Real.pi * (n : ℝ) ^ 2 * Real.exp (4 * u) := by
        calc Real.pi * (n : ℝ) * Real.exp (4 * u)
            = (n : ℝ) * (Real.pi * Real.exp (4 * u)) := by ring
          _ ≤ (n : ℝ) ^ 2 * (Real.pi * Real.exp (4 * u)) :=
              mul_le_mul_of_nonneg_right hnn hpe
          _ = Real.pi * (n : ℝ) ^ 2 * Real.exp (4 * u) := by ring
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      calc -(Real.pi * (n : ℝ) ^ 2 * Real.exp (4 * u))
          ≤ -(Real.pi * (n : ℝ) * Real.exp (4 * u)) := neg_le_neg h2
        _ = (n : ℝ) * (-(Real.pi * Real.exp (4 * u))) := by ring
  have hn4 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have h2 := le_self_pow₀ h1 (by norm_num : (2 : ℕ) ≠ 0)
      calc (n : ℝ) ^ 2 = (n : ℝ) ^ 2 * 1 := (mul_one _).symm
        _ ≤ (n : ℝ) ^ 2 * (n : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ (n : ℝ) ^ 2) (by positivity)
        _ = (n : ℝ) ^ 4 := by ring
  rw [h0, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  calc |2 * Real.pi ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u)
        - 3 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u)|
        * Real.exp (-(Real.pi * (n : ℝ) ^ 2 * Real.exp (4 * u)))
      ≤ (2 * Real.pi ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u)
          + 3 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u))
        * Real.exp (-(Real.pi * (n : ℝ) ^ 2 * Real.exp (4 * u))) :=
        mul_le_mul_of_nonneg_right hAB (Real.exp_nonneg _)
    _ = 2 * Real.pi ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u)
          * Real.exp (-(Real.pi * (n : ℝ) ^ 2 * Real.exp (4 * u)))
        + 3 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u)
          * Real.exp (-(Real.pi * (n : ℝ) ^ 2 * Real.exp (4 * u))) := by ring
    _ ≤ 2 * Real.pi ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u)
          * Real.exp (-(Real.pi * Real.exp (4 * u))) ^ n
        + 3 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u)
          * Real.exp (-(Real.pi * Real.exp (4 * u))) ^ n :=
        add_le_add (mul_le_mul_of_nonneg_left hEr hA) (mul_le_mul_of_nonneg_left hEr hB)
    _ = (2 * Real.pi ^ 2 * Real.exp (9 * u)) * ((n : ℝ) ^ 4
          * Real.exp (-(Real.pi * Real.exp (4 * u))) ^ n)
        + (3 * Real.pi * Real.exp (5 * u)) * ((n : ℝ) ^ 2
          * Real.exp (-(Real.pi * Real.exp (4 * u))) ^ n) := by ring
    _ ≤ (2 * Real.pi ^ 2 * Real.exp (9 * u)) * ((n : ℝ) ^ 4
          * Real.exp (-(Real.pi * Real.exp (4 * u))) ^ n)
        + (3 * Real.pi * Real.exp (5 * u)) * ((n : ℝ) ^ 4
          * Real.exp (-(Real.pi * Real.exp (4 * u))) ^ n) := by
        apply add_le_add_right
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hn4 (pow_nonneg (Real.exp_nonneg _) n)
    _ = (2 * Real.pi ^ 2 * Real.exp (9 * u) + 3 * Real.pi * Real.exp (5 * u))
          * ((n : ℝ) ^ 4 * Real.exp (-(Real.pi * Real.exp (4 * u))) ^ n) := by ring

/-- The kernel series with all `n : ℕ` is (absolutely) summable for every
real `u`, by comparison with the geometric series `n⁴ rⁿ`, `r = e^{−π e^{4u}}`. -/
theorem summable_phiTerm_all (u : ℝ) : Summable fun n : ℕ => phiTerm n u := by
  have hr1 : Real.exp (-(Real.pi * Real.exp (4 * u))) < 1 := by
    rw [Real.exp_lt_one_iff]
    have hpe : 0 < Real.pi * Real.exp (4 * u) := by positivity
    linarith
  have hs : Summable fun n : ℕ =>
      (n : ℝ) ^ 4 * Real.exp (-(Real.pi * Real.exp (4 * u))) ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one 4 (by
      rwa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)])
  refine Summable.of_norm_bounded
    (hs.mul_left (2 * Real.pi ^ 2 * Real.exp (9 * u) + 3 * Real.pi * Real.exp (5 * u)))
    fun n => ?_
  rw [Real.norm_eq_abs]
  exact abs_phiTerm_le u n

/-- The defining series of `Φ` converges for every real `u`. -/
theorem summable_phiTerm (u : ℝ) : Summable fun n : ℕ => phiTerm (n + 1) u :=
  (summable_nat_add_iff 1).mpr (summable_phiTerm_all u)

/-- The de Bruijn–Newman kernel
`Φ(u) = Σ_{n ≥ 1} (2π²n⁴ e^{9u} − 3πn² e^{5u}) exp(−πn² e^{4u})`.
Convergence for every real `u` is `summable_phiTerm`. -/
noncomputable def phi (u : ℝ) : ℝ := ∑' n : ℕ, phiTerm (n + 1) u

/-! ## 余弦增长界（H_t 被积函数控制的组成部分） -/

/-- `cosh y + |sinh y| = exp |y|` for real `y`. -/
theorem cosh_add_abs_sinh_eq (y : ℝ) :
    Real.cosh y + |Real.sinh y| = Real.exp |y| := by
  rw [Real.cosh_eq, Real.sinh_eq]
  rcases le_total 0 y with hy | hy
  · have h1 : Real.exp (-y) ≤ Real.exp y := Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (Real.exp y - Real.exp (-y)) / 2),
      abs_of_nonneg hy]
    linarith
  · have h1 : Real.exp y ≤ Real.exp (-y) := Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonpos (by linarith : (Real.exp y - Real.exp (-y)) / 2 ≤ 0),
      abs_of_nonpos hy]
    linarith

/-- Auxiliary cosine growth bound: `‖cos w‖ ≤ exp |Im w|` for `w : ℂ`.
Proved from `Complex.cos_eq` and `cosh y + |sinh y| = exp |y|`. -/
theorem norm_cos_le_exp_abs_im (w : ℂ) :
    ‖Complex.cos w‖ ≤ Real.exp |w.im| := by
  have hcs : Real.cosh w.im + |Real.sinh w.im| = Real.exp |w.im| :=
    cosh_add_abs_sinh_eq w.im
  have hc : 0 ≤ Real.cosh w.im := by rw [Real.cosh_eq]; positivity
  have nc : ‖Complex.cos (w.re : ℂ)‖ = |Real.cos w.re| := by
    simp [← Complex.ofReal_cos]
  have nch : ‖Complex.cosh (w.im : ℂ)‖ = Real.cosh w.im := by
    simp [← Complex.ofReal_cosh, abs_of_nonneg hc]
  have ns : ‖Complex.sin (w.re : ℂ)‖ = |Real.sin w.re| := by
    simp [← Complex.ofReal_sin]
  have nsh : ‖Complex.sinh (w.im : ℂ)‖ = |Real.sinh w.im| := by
    simp [← Complex.ofReal_sinh]
  rw [Complex.cos_eq]
  apply le_trans (norm_sub_le _ _)
  simp only [norm_mul]
  rw [nc, nch, ns, nsh, Complex.norm_I, mul_one]
  have h1 : |Real.cos w.re| * Real.cosh w.im ≤ Real.cosh w.im := by
    have h := mul_le_mul_of_nonneg_right (Real.abs_cos_le_one w.re) hc
    rwa [one_mul] at h
  have h2 : |Real.sin w.re| * |Real.sinh w.im| ≤ |Real.sinh w.im| := by
    have h := mul_le_mul_of_nonneg_right (Real.abs_sin_le_one w.re) (abs_nonneg (Real.sinh w.im))
    rwa [one_mul] at h
  linarith [hcs]

/-- Auxiliary sine growth bound: `‖sin w‖ ≤ exp |Im w|` for `w : ℂ`,
from the same `cosh_add_abs_sinh_eq` template. -/
theorem norm_sin_le_exp_abs_im (w : ℂ) :
    ‖Complex.sin w‖ ≤ Real.exp |w.im| := by
  have hcs : Real.cosh w.im + |Real.sinh w.im| = Real.exp |w.im| :=
    cosh_add_abs_sinh_eq w.im
  have hc : 0 ≤ Real.cosh w.im := by rw [Real.cosh_eq]; positivity
  have nc : ‖Complex.cos (w.re : ℂ)‖ = |Real.cos w.re| := by
    simp [← Complex.ofReal_cos]
  have nch : ‖Complex.cosh (w.im : ℂ)‖ = Real.cosh w.im := by
    simp [← Complex.ofReal_cosh, abs_of_nonneg hc]
  have ns : ‖Complex.sin (w.re : ℂ)‖ = |Real.sin w.re| := by
    simp [← Complex.ofReal_sin]
  have nsh : ‖Complex.sinh (w.im : ℂ)‖ = |Real.sinh w.im| := by
    simp [← Complex.ofReal_sinh]
  rw [Complex.sin_eq]
  apply le_trans (norm_add_le _ _)
  simp only [norm_mul]
  rw [ns, nch, nc, nsh, Complex.norm_I, mul_one]
  have h1 : |Real.sin w.re| * Real.cosh w.im ≤ Real.cosh w.im := by
    have h := mul_le_mul_of_nonneg_right (Real.abs_sin_le_one w.re) hc
    rwa [one_mul] at h
  have h2 : |Real.cos w.re| * |Real.sinh w.im| ≤ |Real.sinh w.im| := by
    have h := mul_le_mul_of_nonneg_right (Real.abs_cos_le_one w.re) (abs_nonneg (Real.sinh w.im))
    rwa [one_mul] at h
  linarith [hcs]

/-- Growth control for the oscillatory factor of the `H_t` integrand:
`‖cos (z · u)‖ ≤ exp |Im z · u|` for real `u`. -/
theorem norm_cos_mul_ofReal_le_exp (z : ℂ) (u : ℝ) :
    ‖Complex.cos (z * (u : ℂ))‖ ≤ Real.exp |z.im * u| := by
  have him : (z * (u : ℂ)).im = z.im * u := by simp [Complex.mul_im]
  rw [← him]
  exact norm_cos_le_exp_abs_im _

/-- Growth control for the sine factor of the differentiated integrand:
`‖sin (z · u)‖ ≤ exp |Im z · u|` for real `u`. -/
theorem norm_sin_mul_ofReal_le_exp (z : ℂ) (u : ℝ) :
    ‖Complex.sin (z * (u : ℂ))‖ ≤ Real.exp |z.im * u| := by
  have him : (z * (u : ℂ)).im = z.im * u := by simp [Complex.mul_im]
  rw [← him]
  exact norm_sin_le_exp_abs_im _

/-! ## Phase 1a 第一块：Φ 的连续性与 `[0,∞)` 上的双指数衰减界 -/

/-- Pointwise continuity of each kernel term. -/
@[fun_prop]
theorem continuous_phiTerm (n : ℕ) : Continuous fun u : ℝ => phiTerm n u := by
  unfold phiTerm
  fun_prop

/-- `Φ` is continuous on `ℝ`: on every compact neighborhood the defining
series admits a uniform geometric bound, so `continuousOn_tsum` applies
locally. -/
@[fun_prop]
theorem continuous_phi : Continuous phi := by
  rw [continuous_iff_continuousAt]
  intro u₀
  set C₀ : ℝ := 2 * Real.pi ^ 2 * Real.exp (9 * (u₀ + 1))
    + 3 * Real.pi * Real.exp (5 * (u₀ + 1)) with hC₀
  set r₀ : ℝ := Real.exp (-(Real.pi * Real.exp (4 * (u₀ - 1)))) with hr₀
  have hr₀1 : r₀ < 1 := by
    rw [hr₀, Real.exp_lt_one_iff]
    have hpe : 0 < Real.pi * Real.exp (4 * (u₀ - 1)) := by positivity
    linarith
  have hs : Summable fun n : ℕ => C₀ * (((n + 1 : ℕ) : ℝ) ^ 4 * r₀ ^ (n + 1)) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one 4 (show ‖r₀‖ < 1 from by
      rwa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)])
    exact ((summable_nat_add_iff 1).mpr h).mul_left C₀
  have hcont : ContinuousOn (fun u : ℝ => ∑' n : ℕ, phiTerm (n + 1) u)
      (Set.Icc (u₀ - 1) (u₀ + 1)) := by
    refine continuousOn_tsum (fun n => (continuous_phiTerm (n + 1)).continuousOn) hs
      (fun n u hu => ?_)
    rw [Real.norm_eq_abs]
    calc |phiTerm (n + 1) u|
        ≤ (2 * Real.pi ^ 2 * Real.exp (9 * u) + 3 * Real.pi * Real.exp (5 * u))
            * (((n + 1 : ℕ) : ℝ) ^ 4
              * Real.exp (-(Real.pi * Real.exp (4 * u))) ^ (n + 1)) :=
          abs_phiTerm_le u (n + 1)
      _ ≤ C₀ * (((n + 1 : ℕ) : ℝ) ^ 4 * r₀ ^ (n + 1)) := by
          apply mul_le_mul _ _ (by positivity) (by rw [hC₀]; positivity)
          · have hu1 : u ≤ u₀ + 1 := hu.2
            rw [hC₀]
            apply add_le_add
            · apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact Real.exp_le_exp.mpr (by linarith)
            · apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact Real.exp_le_exp.mpr (by linarith)
          · have hu0 : u₀ - 1 ≤ u := hu.1
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg _) _)
            apply pow_le_pow_left₀ (Real.exp_nonneg _)
            apply Real.exp_le_exp.mpr
            have hle : Real.pi * Real.exp (4 * (u₀ - 1)) ≤ Real.pi * Real.exp (4 * u) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact Real.exp_le_exp.mpr (by linarith)
            linarith [hle]
  exact hcont.continuousAt (Icc_mem_nhds (by linarith) (by linarith))

/-- Summability helper: `Σ_{n ≥ 0} (n+1)⁴ e^{x n}` converges for `x < 0`.
Used both for the tail constant (`x = -π`) and for the pointwise geometric
comparison (`x = -π e^{4u}`). -/
theorem summable_shift_pow_mul_exp {x : ℝ} (hx : x < 0) :
    Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp x ^ n := by
  have hr : ‖Real.exp x‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), Real.exp_lt_one_iff]
    exact hx
  have h1 := (summable_nat_add_iff
      (f := fun m : ℕ => (m : ℝ) ^ 4 * Real.exp x ^ m) 1).mpr
    (summable_pow_mul_geometric_of_norm_lt_one 4 hr)
  have h2 := h1.mul_left (Real.exp x)⁻¹
  refine h2.congr fun n => ?_
  have hxne : Real.exp x ≠ 0 := (Real.exp_pos _).ne'
  show (Real.exp x)⁻¹ * (((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp x ^ (n + 1))
      = ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp x ^ n
  rw [pow_succ]
  field_simp
  ring

/-- The tail constant `K₁ = Σ_{n ≥ 1} n⁴ e^{-π (n-1)}` used to dominate the
kernel series on `[0, ∞)`. -/
noncomputable def phiTailConst : ℝ :=
  ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-Real.pi) ^ n

theorem summable_phiTailConst :
    Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-Real.pi) ^ n :=
  summable_shift_pow_mul_exp (neg_lt_zero.mpr Real.pi_pos)

theorem phiTailConst_nonneg : 0 ≤ phiTailConst :=
  tsum_nonneg fun n => by positivity

theorem phiTailConst_pos : 0 < phiTailConst := by
  apply Summable.tsum_pos summable_phiTailConst (fun n => by positivity) 0
  simp

/-- Global decay bound for `Φ` on `[0, ∞)`:
`|Φ(u)| ≤ (2π² + 3π) · K₁ · e^{9u} · e^{−π e^{4u}}`. -/
theorem abs_phi_le (u : ℝ) (hu : 0 ≤ u) :
    |phi u| ≤ (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst * Real.exp (9 * u)
      * Real.exp (-(Real.pi * Real.exp (4 * u))) := by
  have hs_bound : Summable fun n : ℕ =>
      (2 * Real.pi ^ 2 * Real.exp (9 * u) + 3 * Real.pi * Real.exp (5 * u))
        * (((n + 1 : ℕ) : ℝ) ^ 4
          * Real.exp (-(Real.pi * Real.exp (4 * u))) ^ (n + 1)) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one 4 (show
        ‖Real.exp (-(Real.pi * Real.exp (4 * u)))‖ < 1 from by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), Real.exp_lt_one_iff]
      have hpe : 0 < Real.pi * Real.exp (4 * u) := by positivity
      linarith)
    exact ((summable_nat_add_iff 1).mpr h).mul_left _
  have hs_norm : Summable fun n : ℕ => ‖phiTerm (n + 1) u‖ :=
    Summable.of_norm_bounded hs_bound (fun n => by
      simp only [Real.norm_eq_abs, abs_abs]
      exact abs_phiTerm_le u (n + 1))
  have hC0 : 0 ≤ (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst :=
    mul_nonneg (by positivity) phiTailConst_nonneg
  have hr_le : Real.exp (-(Real.pi * Real.exp (4 * u))) ≤ Real.exp (-Real.pi) := by
    apply Real.exp_le_exp.mpr
    have hpe : Real.pi ≤ Real.pi * Real.exp (4 * u) := by
      nth_rewrite 1 [← mul_one Real.pi]
      exact mul_le_mul_of_nonneg_left (Real.one_le_exp (by linarith)) (le_of_lt Real.pi_pos)
    linarith
  calc |phi u| = ‖∑' n : ℕ, phiTerm (n + 1) u‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n : ℕ, ‖phiTerm (n + 1) u‖ := norm_tsum_le_tsum_norm hs_norm
    _ ≤ ∑' n : ℕ,
        (2 * Real.pi ^ 2 * Real.exp (9 * u) + 3 * Real.pi * Real.exp (5 * u))
          * (((n + 1 : ℕ) : ℝ) ^ 4
            * Real.exp (-(Real.pi * Real.exp (4 * u))) ^ (n + 1)) :=
        Summable.tsum_le_tsum (fun n => by
          rw [Real.norm_eq_abs]; exact abs_phiTerm_le u (n + 1)) hs_norm hs_bound
    _ = (2 * Real.pi ^ 2 * Real.exp (9 * u) + 3 * Real.pi * Real.exp (5 * u))
          * (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ 4
            * Real.exp (-(Real.pi * Real.exp (4 * u))) ^ (n + 1)) := by
        rw [tsum_mul_left]
    _ ≤ (2 * Real.pi ^ 2 * Real.exp (9 * u) + 3 * Real.pi * Real.exp (5 * u))
          * (phiTailConst * Real.exp (-(Real.pi * Real.exp (4 * u)))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ 4
                * Real.exp (-(Real.pi * Real.exp (4 * u))) ^ (n + 1)
            = Real.exp (-(Real.pi * Real.exp (4 * u)))
                * (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ 4
                    * Real.exp (-(Real.pi * Real.exp (4 * u))) ^ n) := by
              rw [← tsum_mul_left]
              apply tsum_congr
              intro n
              rw [pow_succ]
              ring
          _ ≤ Real.exp (-(Real.pi * Real.exp (4 * u))) * phiTailConst := by
              apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
              apply Summable.tsum_le_tsum _ _ summable_phiTailConst
              · intro n
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact pow_le_pow_left₀ (Real.exp_nonneg _) hr_le n
              · exact summable_shift_pow_mul_exp
                  (neg_lt_zero.mpr (show (0:ℝ) < Real.pi * Real.exp (4 * u) by positivity))
          _ = phiTailConst * Real.exp (-(Real.pi * Real.exp (4 * u))) := by ring
    _ ≤ ((2 * Real.pi ^ 2 + 3 * Real.pi) * Real.exp (9 * u))
          * (phiTailConst * Real.exp (-(Real.pi * Real.exp (4 * u)))) := by
        apply mul_le_mul_of_nonneg_right _
          (mul_nonneg phiTailConst_nonneg (Real.exp_nonneg _))
        have h59 : Real.exp (5 * u) ≤ Real.exp (9 * u) := Real.exp_le_exp.mpr (by linarith)
        calc 2 * Real.pi ^ 2 * Real.exp (9 * u) + 3 * Real.pi * Real.exp (5 * u)
            ≤ 2 * Real.pi ^ 2 * Real.exp (9 * u) + 3 * Real.pi * Real.exp (9 * u) :=
              add_le_add_right
                (mul_le_mul_of_nonneg_left h59 (show (0:ℝ) ≤ 3 * Real.pi by positivity)) _
          _ = (2 * Real.pi ^ 2 + 3 * Real.pi) * Real.exp (9 * u) := by ring
    _ = (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst * Real.exp (9 * u)
          * Real.exp (-(Real.pi * Real.exp (4 * u))) := by ring

/-! ## H_t：积分定义与适定性目标 -/

/-- The integrand of the de Bruijn–Newman family,
`u ↦ e^{t u²} Φ(u) cos(z u)` for real `u`. -/
noncomputable def heatIntegrand (t : ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  ((Real.exp (t * u ^ 2) * phi u : ℝ) : ℂ) * Complex.cos (z * (u : ℂ))

/-- The de Bruijn–Newman family
`H_t(z) := ∫_0^∞ e^{t u²} Φ(u) cos(z u) du`.
The integral value is a placeholder until `heat_integrand_integrable_target`
is discharged; all deep statements about `H_t` are `def : Prop` targets below. -/
noncomputable def deBruijnNewmanH (t : ℝ) (z : ℂ) : ℂ :=
  ∫ u in Set.Ioi 0, heatIntegrand t z u

/-! ## Phase 1a 第二块：主衰减估计与 `H_t` 被积函数的可积性 -/

/-- **Master decay estimate**: polynomial-exponential factors are eventually
crushed by the double-exponential kernel: for `C > 0`, `a ≥ 0`,
`C · e^{t u² + a u} · e^{−π e^{4u}} ≤ e^{−u}` for all sufficiently large `u`. -/
theorem heat_decay_eventually_le (t a C : ℝ) (hC : 0 < C) (ha : 0 ≤ a) :
    ∀ᶠ u in Filter.atTop,
      C * Real.exp (t * u ^ 2 + a * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))
        ≤ Real.exp (-u) := by
  have hcube : ∀ u : ℝ, 0 ≤ u → (4 * u) ^ 3 / 27 ≤ Real.exp (4 * u) := by
    intro u hu
    have h1 : 4 * u / 3 + 1 ≤ Real.exp (4 * u / 3) := Real.add_one_le_exp _
    have h2 : (4 * u / 3) ^ 3 ≤ Real.exp (4 * u / 3) ^ 3 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 3
    have h3 : Real.exp (4 * u / 3) ^ 3 = Real.exp (4 * u) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have h4 : (4 * u / 3) ^ 3 = (4 * u) ^ 3 / 27 := by ring
    rwa [h3, h4] at h2
  have hsq : ∀ u : ℝ, 0 ≤ u → 4 * u ^ 2 ≤ Real.exp (4 * u) := by
    intro u hu
    have h1 : 2 * u ≤ Real.exp (2 * u) := by
      have h := Real.add_one_le_exp (2 * u)
      linarith
    have h2 : (2 * u) ^ 2 ≤ Real.exp (2 * u) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
    have h3 : Real.exp (2 * u) ^ 2 = Real.exp (4 * u) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have h4 : (2 * u) ^ 2 = 4 * u ^ 2 := by ring
    rwa [h3, h4] at h2
  set B : ℝ := 1 + 27 * max t 0 / (32 * Real.pi) + (a + 1) / Real.pi
      + max (Real.log C) 0 / Real.pi with hB
  have hx0 : 0 ≤ 27 * max t 0 / (32 * Real.pi) :=
    div_nonneg (by positivity) (by positivity)
  have hy0 : 0 ≤ (a + 1) / Real.pi := div_nonneg (by linarith) (le_of_lt Real.pi_pos)
  have hz0 : 0 ≤ max (Real.log C) 0 / Real.pi :=
    div_nonneg (le_max_right _ _) (le_of_lt Real.pi_pos)
  have hB1 : 1 ≤ B := by rw [hB]; linarith
  filter_upwards [Filter.eventually_ge_atTop B] with u huB
  have hu1 : 1 ≤ u := le_trans hB1 huB
  have hu0 : 0 ≤ u := zero_le_one.trans hu1
  have hpi3 : 0 ≤ (32 * Real.pi / 27) * u ^ 3 := by positivity
  have hi : t * u ^ 2 ≤ (32 * Real.pi / 27) * u ^ 3 := by
    rcases le_total t 0 with ht | ht
    · exact (mul_nonpos_of_nonpos_of_nonneg ht (pow_nonneg hu0 _)).trans hpi3
    · have h1 : 27 * t / (32 * Real.pi) ≤ B := by
        have hmax : 27 * t / (32 * Real.pi) ≤ 27 * max t 0 / (32 * Real.pi) := by
          rw [div_le_iff₀ (by positivity : (0:ℝ) < 32 * Real.pi),
            div_mul_cancel₀ _ (ne_of_gt (by positivity : (0:ℝ) < 32 * Real.pi))]
          exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
        rw [hB]
        linarith [hmax]
      have h3 : t ≤ (32 * Real.pi / 27) * B := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < 32 * Real.pi)] at h1
        have h4 : (32 * Real.pi / 27) * B = B * (32 * Real.pi) / 27 := by ring
        rw [h4, le_div_iff₀ (by norm_num : (0:ℝ) < 27)]
        calc t * 27 = 27 * t := by ring
          _ ≤ B * (32 * Real.pi) := h1
      calc t * u ^ 2 ≤ (32 * Real.pi / 27) * B * u ^ 2 :=
            mul_le_mul_of_nonneg_right h3 (pow_nonneg hu0 _)
        _ ≤ (32 * Real.pi / 27) * u * u ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left huB (by positivity)) (pow_nonneg hu0 _)
        _ = (32 * Real.pi / 27) * u ^ 3 := by ring
  have hii : (a + 1) * u ≤ Real.pi * u ^ 2 := by
    have h1 : (a + 1) / Real.pi ≤ B := by rw [hB]; linarith
    rw [div_le_iff₀ Real.pi_pos] at h1
    calc (a + 1) * u ≤ B * Real.pi * u :=
          mul_le_mul_of_nonneg_right h1 hu0
      _ ≤ Real.pi * u * u :=
          mul_le_mul_of_nonneg_right
            (calc B * Real.pi = Real.pi * B := by ring
              _ ≤ Real.pi * u := mul_le_mul_of_nonneg_left huB (le_of_lt Real.pi_pos)) hu0
      _ = Real.pi * u ^ 2 := by ring
  have hiii : Real.log C ≤ Real.pi * u ^ 2 := by
    have h1 : max (Real.log C) 0 / Real.pi ≤ B := by rw [hB]; linarith
    rw [div_le_iff₀ Real.pi_pos] at h1
    calc Real.log C ≤ max (Real.log C) 0 := le_max_left _ _
      _ ≤ B * Real.pi := h1
      _ ≤ u * Real.pi := mul_le_mul_of_nonneg_right huB (le_of_lt Real.pi_pos)
      _ = Real.pi * u := by ring
      _ ≤ Real.pi * u ^ 2 :=
          mul_le_mul_of_nonneg_left (le_self_pow₀ hu1 (by norm_num)) (le_of_lt Real.pi_pos)
  have hmain : t * u ^ 2 + (a + 1) * u + Real.log C ≤ Real.pi * Real.exp (4 * u) := by
    have hsplit : (32 * Real.pi / 27) * u ^ 3 + 2 * Real.pi * u ^ 2
        ≤ Real.pi * Real.exp (4 * u) := by
      have hc := hcube u hu0
      have hs := hsq u hu0
      have h64 : (4 * u) ^ 3 / 27 = (64 / 27) * u ^ 3 := by ring
      rw [h64] at hc
      have h2 : (32 * Real.pi / 27) * u ^ 3 ≤ (Real.pi / 2) * Real.exp (4 * u) := by
        have he : (32 * Real.pi / 27) * u ^ 3
            = (Real.pi / 2) * ((64 / 27) * u ^ 3) := by ring
        rw [he]
        exact mul_le_mul_of_nonneg_left hc (by positivity)
      have h3 : 2 * Real.pi * u ^ 2 ≤ (Real.pi / 2) * Real.exp (4 * u) := by
        have he : 2 * Real.pi * u ^ 2 = (Real.pi / 2) * (4 * u ^ 2) := by ring
        rw [he]
        exact mul_le_mul_of_nonneg_left hs (by positivity)
      calc (32 * Real.pi / 27) * u ^ 3 + 2 * Real.pi * u ^ 2
          ≤ (Real.pi / 2) * Real.exp (4 * u) + (Real.pi / 2) * Real.exp (4 * u) :=
            add_le_add h2 h3
        _ = Real.pi * Real.exp (4 * u) := by ring
    calc t * u ^ 2 + (a + 1) * u + Real.log C
        ≤ (32 * Real.pi / 27) * u ^ 3 + Real.pi * u ^ 2 + Real.pi * u ^ 2 :=
          add_le_add (add_le_add hi hii) hiii
      _ = (32 * Real.pi / 27) * u ^ 3 + 2 * Real.pi * u ^ 2 := by ring
      _ ≤ Real.pi * Real.exp (4 * u) := hsplit
  have hau : (a + 1) * u = a * u + u := by ring
  rw [(Real.exp_log hC).symm, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith [hmain]

/-- Variant of `heat_decay_eventually_le` carrying an extra factor `u`
(absorbed via `u ≤ e^u`). Used for the differentiated integrand. -/
theorem heat_decay_eventually_le_mul (t a C : ℝ) (hC : 0 < C) (ha : 0 ≤ a) :
    ∀ᶠ u in Filter.atTop,
      C * u * Real.exp (t * u ^ 2 + a * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))
        ≤ Real.exp (-u) := by
  have hmain := heat_decay_eventually_le t (a + 1) C hC (by linarith)
  filter_upwards [hmain] with u hu
  have hule : u ≤ Real.exp u := by
    have h := Real.add_one_le_exp u
    linarith
  calc C * u * Real.exp (t * u ^ 2 + a * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))
      ≤ C * Real.exp u * Real.exp (t * u ^ 2 + a * u)
          * Real.exp (-(Real.pi * Real.exp (4 * u))) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        exact mul_le_mul_of_nonneg_left hule (le_of_lt hC)
    _ = C * Real.exp (t * u ^ 2 + (a + 1) * u)
          * Real.exp (-(Real.pi * Real.exp (4 * u))) := by
        have he : Real.exp u * Real.exp (t * u ^ 2 + a * u)
            = Real.exp (t * u ^ 2 + (a + 1) * u) := by
          rw [← Real.exp_add]
          congr 1
          ring
        have e1 : C * Real.exp u * Real.exp (t * u ^ 2 + a * u)
            * Real.exp (-(Real.pi * Real.exp (4 * u)))
          = C * (Real.exp u * Real.exp (t * u ^ 2 + a * u))
            * Real.exp (-(Real.pi * Real.exp (4 * u))) := by ring
        rw [e1, he]
    _ ≤ Real.exp (-u) := hu

/-- Dominating function for the `H_t` integrand with `c = |Im z|`:
`u ↦ (2π² + 3π) · K₁ · e^{t u² + (9 + c) u} · e^{−π e^{4u}}`. -/
noncomputable def heatDominatingFun (t c : ℝ) (u : ℝ) : ℝ :=
  (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
    * Real.exp (t * u ^ 2 + (9 + c) * u)
    * Real.exp (-(Real.pi * Real.exp (4 * u)))

theorem continuous_heatDominatingFun (t c : ℝ) : Continuous (heatDominatingFun t c) := by
  unfold heatDominatingFun
  fun_prop

theorem heatDominatingFun_isBigO (t c : ℝ) (hc : 0 ≤ c) :
    Asymptotics.IsBigO Filter.atTop (heatDominatingFun t c)
      fun u : ℝ => Real.exp (-(1:ℝ) * u) := by
  apply Asymptotics.IsBigO.of_bound'
  have hC0 : (0:ℝ) ≤ (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst :=
    mul_nonneg (by positivity) phiTailConst_nonneg
  have h := heat_decay_eventually_le t (9 + c)
    ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst)
    (mul_pos (by positivity) phiTailConst_pos) (by linarith)
  filter_upwards [h] with u hu
  have hdom0 : 0 ≤ heatDominatingFun t c u :=
    mul_nonneg (mul_nonneg hC0 (Real.exp_nonneg _)) (Real.exp_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hdom0, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_nonneg _), neg_mul, one_mul]
  exact hu

theorem integrableOn_heatDominatingFun (t c : ℝ) (hc : 0 ≤ c) :
    MeasureTheory.IntegrableOn (heatDominatingFun t c) (Set.Ioi 0)
      MeasureTheory.volume :=
  integrable_of_isBigO_exp_neg (show (0:ℝ) < 1 by norm_num)
    (continuous_heatDominatingFun t c).continuousOn
    (heatDominatingFun_isBigO t c hc)

/-- **Phase 1a main theorem**: the `H_t` integrand
`u ↦ e^{t u²} Φ(u) cos(z u)` is integrable on `(0, ∞)` for every `t : ℝ`
and `z : ℂ`. -/
theorem heat_integrand_integrable (t : ℝ) (z : ℂ) :
    MeasureTheory.IntegrableOn (heatIntegrand t z) (Set.Ioi 0)
      MeasureTheory.volume := by
  have hcont : Continuous (heatIntegrand t z) := by
    unfold heatIntegrand
    fun_prop
  have hC0 : (0:ℝ) ≤ (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst :=
    mul_nonneg (by positivity) phiTailConst_nonneg
  apply MeasureTheory.Integrable.mono'
    (integrableOn_heatDominatingFun t |z.im| (abs_nonneg _))
  · exact hcont.continuousOn.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := le_of_lt hu
    have h1 : ‖heatIntegrand t z u‖
        = |Real.exp (t * u ^ 2) * phi u| * ‖Complex.cos (z * (u : ℂ))‖ := by
      unfold heatIntegrand
      rw [norm_mul, show ‖((Real.exp (t * u ^ 2) * phi u : ℝ) : ℂ)‖
          = |Real.exp (t * u ^ 2) * phi u| from RCLike.norm_ofReal _]
    rw [h1]
    have hcos : ‖Complex.cos (z * (u : ℂ))‖ ≤ Real.exp (|z.im| * u) := by
      calc ‖Complex.cos (z * (u : ℂ))‖ ≤ Real.exp |z.im * u| :=
            norm_cos_mul_ofReal_le_exp z u
        _ = Real.exp (|z.im| * u) := by rw [abs_mul, abs_of_nonneg hu0]
    have hphi : |Real.exp (t * u ^ 2) * phi u|
        ≤ Real.exp (t * u ^ 2) * ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
            * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))) := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (abs_phi_le u hu0) (Real.exp_nonneg _)
    have hb0 : 0 ≤ Real.exp (t * u ^ 2)
        * ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
          * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))) :=
      mul_nonneg (Real.exp_nonneg _)
        (mul_nonneg (mul_nonneg hC0 (Real.exp_nonneg _)) (Real.exp_nonneg _))
    calc |Real.exp (t * u ^ 2) * phi u| * ‖Complex.cos (z * (u : ℂ))‖
        ≤ (Real.exp (t * u ^ 2) * ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
            * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))))
          * Real.exp (|z.im| * u) := mul_le_mul hphi hcos (norm_nonneg _) hb0
      _ = (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
          * Real.exp (t * u ^ 2 + (9 + |z.im|) * u)
          * Real.exp (-(Real.pi * Real.exp (4 * u))) := by
          have e1 : Real.exp (t * u ^ 2)
              * ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
                * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u))))
              * Real.exp (|z.im| * u)
            = (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
              * (Real.exp (t * u ^ 2) * Real.exp (9 * u) * Real.exp (|z.im| * u))
              * Real.exp (-(Real.pi * Real.exp (4 * u))) := by ring
          rw [e1, ← Real.exp_add, ← Real.exp_add]
          have e2 : t * u ^ 2 + 9 * u + |z.im| * u
              = t * u ^ 2 + (9 + |z.im|) * u := by ring
          rw [e2]
      _ = heatDominatingFun t |z.im| u := rfl

/-! ## Phase 1b：被积函数的 `z` 导数与 `H_t` 的整性、偶性 -/

/-- The `z`-derivative of the `H_t` integrand:
`u ↦ e^{t u²} Φ(u) · (− sin(z u)) · u`. -/
noncomputable def heatIntegrandDeriv (t : ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  ((Real.exp (t * u ^ 2) * phi u : ℝ) : ℂ) * (-Complex.sin (z * (u : ℂ)) * (u : ℂ))

theorem heat_integrand_hasDerivAt (t : ℝ) (u : ℝ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => heatIntegrand t w u) (heatIntegrandDeriv t z u) z := by
  have h := (((hasDerivAt_id z).mul_const (u : ℂ)).ccos).const_mul
    ((Real.exp (t * u ^ 2) * phi u : ℝ) : ℂ)
  simpa [heatIntegrand, heatIntegrandDeriv] using h

/-- Dominating function for the differentiated `H_t` integrand:
`u ↦ (2π² + 3π) · K₁ · u · e^{t u² + (9 + c) u} · e^{−π e^{4u}}`. -/
noncomputable def heatDerivDominatingFun (t c : ℝ) (u : ℝ) : ℝ :=
  (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst * u
    * Real.exp (t * u ^ 2 + (9 + c) * u)
    * Real.exp (-(Real.pi * Real.exp (4 * u)))

theorem continuous_heatDerivDominatingFun (t c : ℝ) :
    Continuous (heatDerivDominatingFun t c) := by
  unfold heatDerivDominatingFun
  fun_prop

theorem heatDerivDominatingFun_isBigO (t c : ℝ) (hc : 0 ≤ c) :
    Asymptotics.IsBigO Filter.atTop (heatDerivDominatingFun t c)
      fun u : ℝ => Real.exp (-(1:ℝ) * u) := by
  apply Asymptotics.IsBigO.of_bound'
  have hC0 : (0:ℝ) ≤ (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst :=
    mul_nonneg (by positivity) phiTailConst_nonneg
  have h := heat_decay_eventually_le_mul t (9 + c)
    ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst)
    (mul_pos (by positivity) phiTailConst_pos) (by linarith)
  filter_upwards [h, Filter.eventually_ge_atTop 0] with u hu hu0
  have hdom0 : 0 ≤ heatDerivDominatingFun t c u :=
    mul_nonneg (mul_nonneg (mul_nonneg hC0 hu0) (Real.exp_nonneg _)) (Real.exp_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hdom0, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_nonneg _), neg_mul, one_mul]
  exact hu

theorem integrableOn_heatDerivDominatingFun (t c : ℝ) (hc : 0 ≤ c) :
    MeasureTheory.IntegrableOn (heatDerivDominatingFun t c) (Set.Ioi 0)
      MeasureTheory.volume :=
  integrable_of_isBigO_exp_neg (show (0:ℝ) < 1 by norm_num)
    (continuous_heatDerivDominatingFun t c).continuousOn
    (heatDerivDominatingFun_isBigO t c hc)

theorem continuous_heatIntegrandDeriv (t : ℝ) (z : ℂ) :
    Continuous fun u : ℝ => heatIntegrandDeriv t z u := by
  unfold heatIntegrandDeriv
  fun_prop

/-- Variant of `heat_decay_eventually_le` carrying an extra factor `u²`
(absorbed via `u² ≤ e^{2u}`). Used for the second `z`-derivative and the
`t`-derivative of the `H_t` integrand. -/
theorem heat_decay_eventually_le_mul2 (t a C : ℝ) (hC : 0 < C) (ha : 0 ≤ a) :
    ∀ᶠ u in Filter.atTop,
      C * u ^ 2 * Real.exp (t * u ^ 2 + a * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))
        ≤ Real.exp (-u) := by
  have hmain := heat_decay_eventually_le t (a + 2) C hC (by linarith)
  filter_upwards [hmain, Filter.eventually_ge_atTop 0] with u hu hu0
  have hule : u ≤ Real.exp u := by
    have h := Real.add_one_le_exp u
    linarith
  have hu2 : u ^ 2 ≤ Real.exp (2 * u) := by
    have h1 : u * u ≤ Real.exp u * Real.exp u := mul_self_le_mul_self hu0 hule
    have h2 : Real.exp u * Real.exp u = Real.exp (2 * u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc u ^ 2 = u * u := pow_two u
      _ ≤ Real.exp u * Real.exp u := h1
      _ = Real.exp (2 * u) := h2
  calc C * u ^ 2 * Real.exp (t * u ^ 2 + a * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))
      ≤ C * Real.exp (2 * u) * Real.exp (t * u ^ 2 + a * u)
          * Real.exp (-(Real.pi * Real.exp (4 * u))) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        exact mul_le_mul_of_nonneg_left hu2 (le_of_lt hC)
    _ = C * Real.exp (t * u ^ 2 + (a + 2) * u)
          * Real.exp (-(Real.pi * Real.exp (4 * u))) := by
        have he : Real.exp (2 * u) * Real.exp (t * u ^ 2 + a * u)
            = Real.exp (t * u ^ 2 + (a + 2) * u) := by
          rw [← Real.exp_add]
          congr 1
          ring
        have e1 : C * Real.exp (2 * u) * Real.exp (t * u ^ 2 + a * u)
            * Real.exp (-(Real.pi * Real.exp (4 * u)))
          = C * (Real.exp (2 * u) * Real.exp (t * u ^ 2 + a * u))
            * Real.exp (-(Real.pi * Real.exp (4 * u))) := by ring
        rw [e1, he]
    _ ≤ Real.exp (-u) := hu

/-- Dominating function for the second `z`-derivative (and the `t`-derivative)
of the `H_t` integrand:
`u ↦ (2π² + 3π) · K₁ · u² · e^{t u² + (9 + c) u} · e^{−π e^{4u}}`. -/
noncomputable def heatSqDominatingFun (t c : ℝ) (u : ℝ) : ℝ :=
  (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst * u ^ 2
    * Real.exp (t * u ^ 2 + (9 + c) * u)
    * Real.exp (-(Real.pi * Real.exp (4 * u)))

theorem continuous_heatSqDominatingFun (t c : ℝ) :
    Continuous (heatSqDominatingFun t c) := by
  unfold heatSqDominatingFun
  fun_prop

theorem heatSqDominatingFun_isBigO (t c : ℝ) (hc : 0 ≤ c) :
    Asymptotics.IsBigO Filter.atTop (heatSqDominatingFun t c)
      fun u : ℝ => Real.exp (-(1:ℝ) * u) := by
  apply Asymptotics.IsBigO.of_bound'
  have hC0 : (0:ℝ) ≤ (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst :=
    mul_nonneg (by positivity) phiTailConst_nonneg
  have h := heat_decay_eventually_le_mul2 t (9 + c)
    ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst)
    (mul_pos (by positivity) phiTailConst_pos) (by linarith)
  filter_upwards [h, Filter.eventually_ge_atTop 0] with u hu hu0
  have hdom0 : 0 ≤ heatSqDominatingFun t c u :=
    mul_nonneg (mul_nonneg (mul_nonneg hC0 (sq_nonneg u)) (Real.exp_nonneg _))
      (Real.exp_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hdom0, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_nonneg _), neg_mul, one_mul]
  exact hu

theorem integrableOn_heatSqDominatingFun (t c : ℝ) (hc : 0 ≤ c) :
    MeasureTheory.IntegrableOn (heatSqDominatingFun t c) (Set.Ioi 0)
      MeasureTheory.volume :=
  integrable_of_isBigO_exp_neg (show (0:ℝ) < 1 by norm_num)
    (continuous_heatSqDominatingFun t c).continuousOn
    (heatSqDominatingFun_isBigO t c hc)

/-- Pointwise continuity of the `H_t` integrand (global version). -/
theorem continuous_heatIntegrand (t : ℝ) (z : ℂ) :
    Continuous (heatIntegrand t z) := by
  unfold heatIntegrand
  fun_prop

/-- The `t`-derivative of the `H_t` integrand:
`∂_t [e^{t u²} Φ(u) cos(z u)] = u² · e^{t u²} Φ(u) cos(z u)`. -/
theorem heat_integrand_hasDerivAt_t (u : ℝ) (z : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => heatIntegrand s z u)
      ((u : ℂ) ^ 2 * heatIntegrand t z u) t := by
  have h1 : HasDerivAt (fun s : ℝ => Real.exp (s * u ^ 2))
      (Real.exp (t * u ^ 2) * u ^ 2) t := by
    simpa using ((hasDerivAt_id t).mul_const (u ^ 2 : ℝ)).exp
  have h2 : HasDerivAt (fun s : ℝ => Real.exp (s * u ^ 2) * phi u)
      (Real.exp (t * u ^ 2) * u ^ 2 * phi u) t := h1.mul_const (phi u)
  have h3 : HasDerivAt (fun s : ℝ => ((Real.exp (s * u ^ 2) * phi u : ℝ) : ℂ))
      (((Real.exp (t * u ^ 2) * u ^ 2 * phi u : ℝ) : ℂ)) t := h2.ofReal_comp
  have h4 : HasDerivAt (fun s : ℝ => ((Real.exp (s * u ^ 2) * phi u : ℝ) : ℂ)
        * Complex.cos (z * (u : ℂ)))
      ((((Real.exp (t * u ^ 2) * u ^ 2 * phi u : ℝ) : ℂ))
        * Complex.cos (z * (u : ℂ))) t :=
    h3.mul_const (Complex.cos (z * (u : ℂ)))
  refine h4.congr_deriv ?_
  unfold heatIntegrand
  push_cast
  ring

/-- The `z`-derivative of `heatIntegrandDeriv`:
`∂_z [−e^{t u²} Φ(u) sin(z u) · u] = −u² · e^{t u²} Φ(u) cos(z u)`. -/
theorem heat_integrandDeriv_hasDerivAt (t : ℝ) (u : ℝ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => heatIntegrandDeriv t w u)
      (-((u : ℂ) ^ 2) * heatIntegrand t z u) z := by
  have h := ((((hasDerivAt_id z).mul_const (u : ℂ)).csin).neg.mul_const
    (u : ℂ)).const_mul ((Real.exp (t * u ^ 2) * phi u : ℝ) : ℂ)
  refine h.congr_deriv ?_
  show ((Real.exp (t * u ^ 2) * phi u : ℝ) : ℂ)
      * (-(Complex.cos (z * (u : ℂ)) * (1 * (u : ℂ))) * (u : ℂ))
      = -((u : ℂ) ^ 2) * heatIntegrand t z u
  unfold heatIntegrand
  ring

/-- The once-`z`-differentiated `H_t` integrand is integrable on `(0, ∞)`. -/
theorem heat_integrandDeriv_integrable (t : ℝ) (z : ℂ) :
    MeasureTheory.IntegrableOn (heatIntegrandDeriv t z) (Set.Ioi 0)
      MeasureTheory.volume := by
  have hC0 : (0:ℝ) ≤ (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst :=
    mul_nonneg (by positivity) phiTailConst_nonneg
  apply MeasureTheory.Integrable.mono'
    (integrableOn_heatDerivDominatingFun t |z.im| (abs_nonneg _))
  · exact (continuous_heatIntegrandDeriv t z).continuousOn.aestronglyMeasurable
      measurableSet_Ioi
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := le_of_lt hu
    have hsin : ‖Complex.sin (z * (u : ℂ))‖ ≤ Real.exp (|z.im| * u) := by
      calc ‖Complex.sin (z * (u : ℂ))‖ ≤ Real.exp |z.im * u| :=
            norm_sin_mul_ofReal_le_exp z u
        _ = Real.exp (|z.im| * u) := by rw [abs_mul, abs_of_nonneg hu0]
    have hn : ‖heatIntegrandDeriv t z u‖
        = |Real.exp (t * u ^ 2) * phi u| * (‖Complex.sin (z * (u : ℂ))‖ * u) := by
      unfold heatIntegrandDeriv
      rw [norm_mul, norm_mul, norm_neg,
        show ‖((Real.exp (t * u ^ 2) * phi u : ℝ) : ℂ)‖
          = |Real.exp (t * u ^ 2) * phi u| from RCLike.norm_ofReal _,
        show ‖(u : ℂ)‖ = u from by
          rw [show ‖(u : ℂ)‖ = |u| from RCLike.norm_ofReal u, abs_of_nonneg hu0]]
    rw [hn]
    have hphi : |Real.exp (t * u ^ 2) * phi u|
        ≤ Real.exp (t * u ^ 2) * ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
            * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))) := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (abs_phi_le u hu0) (Real.exp_nonneg _)
    have hb0 : 0 ≤ Real.exp (t * u ^ 2)
        * ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
          * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))) :=
      mul_nonneg (Real.exp_nonneg _)
        (mul_nonneg (mul_nonneg hC0 (Real.exp_nonneg _)) (Real.exp_nonneg _))
    calc |Real.exp (t * u ^ 2) * phi u| * (‖Complex.sin (z * (u : ℂ))‖ * u)
        ≤ (Real.exp (t * u ^ 2) * ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
            * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))))
          * (Real.exp (|z.im| * u) * u) :=
          mul_le_mul hphi
            (mul_le_mul hsin le_rfl hu0 (Real.exp_nonneg _))
            (mul_nonneg (norm_nonneg _) hu0) hb0
      _ = heatDerivDominatingFun t |z.im| u := by
          unfold heatDerivDominatingFun
          have e1 : Real.exp (t * u ^ 2)
              * ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
                * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u))))
              * (Real.exp (|z.im| * u) * u)
            = (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst * u
              * (Real.exp (t * u ^ 2) * Real.exp (9 * u)
                * Real.exp (|z.im| * u))
              * Real.exp (-(Real.pi * Real.exp (4 * u))) := by ring
          rw [e1, ← Real.exp_add, ← Real.exp_add]
          have e2 : t * u ^ 2 + 9 * u + |z.im| * u
              = t * u ^ 2 + (9 + |z.im|) * u := by ring
          rw [e2]

/-- The `z`-derivative of `H_t` as an integral:
`H_t'(z₀) = ∫_0^∞ e^{t u²} Φ(u) (−sin(z₀ u)) · u du`. -/
theorem hasDerivAt_deBruijnNewmanH (t : ℝ) (z₀ : ℂ) :
    HasDerivAt (deBruijnNewmanH t)
      (∫ u in Set.Ioi 0, heatIntegrandDeriv t z₀ u) z₀ := by
  set μ := MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)) with hμ
  have hcont : ∀ w : ℂ, Continuous (heatIntegrand t w) := fun w => by
    unfold heatIntegrand
    fun_prop
  have hmeas : ∀ w : ℂ, MeasureTheory.AEStronglyMeasurable (heatIntegrand t w) μ :=
    fun w => (hcont w).continuousOn.aestronglyMeasurable measurableSet_Ioi
  have hderv_meas : MeasureTheory.AEStronglyMeasurable (heatIntegrandDeriv t z₀) μ :=
    (continuous_heatIntegrandDeriv t z₀).continuousOn.aestronglyMeasurable
      measurableSet_Ioi
  have hC0 : (0:ℝ) ≤ (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst :=
    mul_nonneg (by positivity) phiTailConst_nonneg
  have hbound : ∀ᵐ u ∂μ, ∀ w ∈ Metric.ball z₀ 1,
      ‖heatIntegrandDeriv t w u‖ ≤ heatDerivDominatingFun t (|z₀.im| + 1) u := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu w hw
    have hu0 : 0 ≤ u := le_of_lt hu
    have hwim : |w.im| ≤ |z₀.im| + 1 := by
      have h2 : |(w - z₀).im| ≤ ‖w - z₀‖ := Complex.abs_im_le_norm _
      have h3 : ‖w - z₀‖ < 1 := by
        rw [← dist_eq_norm]
        exact Metric.mem_ball.mp hw
      have him : w.im - z₀.im = (w - z₀).im := by simp [Complex.sub_im]
      calc |w.im| = |w.im - z₀.im + z₀.im| :=
            (congrArg abs (sub_add_cancel w.im z₀.im)).symm
        _ ≤ |w.im - z₀.im| + |z₀.im| := abs_add_le _ _
        _ ≤ ‖w - z₀‖ + |z₀.im| := by rw [him]; exact add_le_add_left h2 _
        _ ≤ 1 + |z₀.im| := by linarith [h3.le]
        _ = |z₀.im| + 1 := by ring
    have hsin : ‖Complex.sin (w * (u : ℂ))‖ ≤ Real.exp ((|z₀.im| + 1) * u) := by
      calc ‖Complex.sin (w * (u : ℂ))‖ ≤ Real.exp |w.im * u| :=
            norm_sin_mul_ofReal_le_exp w u
        _ = Real.exp (|w.im| * u) := by rw [abs_mul, abs_of_nonneg hu0]
        _ ≤ Real.exp ((|z₀.im| + 1) * u) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hwim hu0)
    have hn : ‖heatIntegrandDeriv t w u‖
        = |Real.exp (t * u ^ 2) * phi u| * (‖Complex.sin (w * (u : ℂ))‖ * u) := by
      unfold heatIntegrandDeriv
      rw [norm_mul, norm_mul, norm_neg,
        show ‖((Real.exp (t * u ^ 2) * phi u : ℝ) : ℂ)‖
          = |Real.exp (t * u ^ 2) * phi u| from RCLike.norm_ofReal _,
        show ‖(u : ℂ)‖ = u from by
          rw [show ‖(u : ℂ)‖ = |u| from RCLike.norm_ofReal u, abs_of_nonneg hu0]]
    rw [hn]
    have hphi : |Real.exp (t * u ^ 2) * phi u|
        ≤ Real.exp (t * u ^ 2) * ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
            * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))) := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (abs_phi_le u hu0) (Real.exp_nonneg _)
    have hb0 : 0 ≤ Real.exp (t * u ^ 2)
        * ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
          * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))) :=
      mul_nonneg (Real.exp_nonneg _)
        (mul_nonneg (mul_nonneg hC0 (Real.exp_nonneg _)) (Real.exp_nonneg _))
    calc |Real.exp (t * u ^ 2) * phi u| * (‖Complex.sin (w * (u : ℂ))‖ * u)
        ≤ (Real.exp (t * u ^ 2) * ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
            * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))))
          * (Real.exp ((|z₀.im| + 1) * u) * u) :=
          mul_le_mul hphi
            (mul_le_mul hsin le_rfl hu0 (Real.exp_nonneg _))
            (mul_nonneg (norm_nonneg _) hu0) hb0
      _ = heatDerivDominatingFun t (|z₀.im| + 1) u := by
          unfold heatDerivDominatingFun
          have e1 : Real.exp (t * u ^ 2)
              * ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
                * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u))))
              * (Real.exp ((|z₀.im| + 1) * u) * u)
            = (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst * u
              * (Real.exp (t * u ^ 2) * Real.exp (9 * u)
                * Real.exp ((|z₀.im| + 1) * u))
              * Real.exp (-(Real.pi * Real.exp (4 * u))) := by ring
          rw [e1, ← Real.exp_add, ← Real.exp_add]
          have e2 : t * u ^ 2 + 9 * u + (|z₀.im| + 1) * u
              = t * u ^ 2 + (9 + (|z₀.im| + 1)) * u := by ring
          rw [e2]
  have hint : MeasureTheory.Integrable (heatDerivDominatingFun t (|z₀.im| + 1)) μ :=
    integrableOn_heatDerivDominatingFun t (|z₀.im| + 1) (by positivity)
  have hdiff : ∀ᵐ u ∂μ, ∀ w ∈ Metric.ball z₀ 1,
      HasDerivAt (fun x => heatIntegrand t x u) (heatIntegrandDeriv t w u) w :=
    Filter.Eventually.of_forall fun u w _ => heat_integrand_hasDerivAt t u w
  have hFint : MeasureTheory.Integrable (heatIntegrand t z₀) μ :=
    heat_integrand_integrable t z₀
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z₀ (by norm_num : (0:ℝ) < 1))
    (Filter.Eventually.of_forall hmeas) hFint hderv_meas hbound hint hdiff
  exact h.2

/-- Derivative formula: `deriv (H_t) z₀ = ∫_0^∞ e^{t u²} Φ(u) (−sin(z₀ u)) u du`. -/
theorem deriv_deBruijnNewmanH (t : ℝ) (z₀ : ℂ) :
    deriv (deBruijnNewmanH t) z₀ = ∫ u in Set.Ioi 0, heatIntegrandDeriv t z₀ u :=
  (hasDerivAt_deBruijnNewmanH t z₀).deriv

/-- The second `z`-derivative of the integrand integral:
`(∫ heatIntegrandDeriv)' = ∫ −u² · heatIntegrand`. -/
theorem hasDerivAt_integral_heatIntegrandDeriv (t : ℝ) (z₀ : ℂ) :
    HasDerivAt (fun w : ℂ => ∫ u in Set.Ioi 0, heatIntegrandDeriv t w u)
      (∫ u : ℝ in Set.Ioi 0, -((u : ℂ) ^ 2) * heatIntegrand t z₀ u) z₀ := by
  set μ := MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)) with hμ
  have hmeas : ∀ w : ℂ, MeasureTheory.AEStronglyMeasurable (heatIntegrandDeriv t w) μ :=
    fun w => (continuous_heatIntegrandDeriv t w).continuousOn.aestronglyMeasurable
      measurableSet_Ioi
  have hderv_meas : MeasureTheory.AEStronglyMeasurable
      (fun u : ℝ => -((u : ℂ) ^ 2) * heatIntegrand t z₀ u) μ :=
    ((Complex.continuous_ofReal.pow 2).neg.mul
      (continuous_heatIntegrand t z₀)).continuousOn.aestronglyMeasurable
      measurableSet_Ioi
  have hC0 : (0:ℝ) ≤ (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst :=
    mul_nonneg (by positivity) phiTailConst_nonneg
  have hbound : ∀ᵐ u ∂μ, ∀ w ∈ Metric.ball z₀ 1,
      ‖-(((u : ℝ) : ℂ) ^ 2) * heatIntegrand t w u‖
        ≤ heatSqDominatingFun t (|z₀.im| + 1) u := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu w hw
    have hu0 : 0 ≤ u := le_of_lt hu
    have hwim : |w.im| ≤ |z₀.im| + 1 := by
      have h2 : |(w - z₀).im| ≤ ‖w - z₀‖ := Complex.abs_im_le_norm _
      have h3 : ‖w - z₀‖ < 1 := by
        rw [← dist_eq_norm]
        exact Metric.mem_ball.mp hw
      have him : w.im - z₀.im = (w - z₀).im := by simp [Complex.sub_im]
      calc |w.im| = |w.im - z₀.im + z₀.im| :=
            (congrArg abs (sub_add_cancel w.im z₀.im)).symm
        _ ≤ |w.im - z₀.im| + |z₀.im| := abs_add_le _ _
        _ ≤ ‖w - z₀‖ + |z₀.im| := by rw [him]; exact add_le_add_left h2 _
        _ ≤ 1 + |z₀.im| := by linarith [h3.le]
        _ = |z₀.im| + 1 := by ring
    have hcos : ‖Complex.cos (w * (u : ℂ))‖ ≤ Real.exp ((|z₀.im| + 1) * u) := by
      calc ‖Complex.cos (w * (u : ℂ))‖ ≤ Real.exp |w.im * u| :=
            norm_cos_mul_ofReal_le_exp w u
        _ = Real.exp (|w.im| * u) := by rw [abs_mul, abs_of_nonneg hu0]
        _ ≤ Real.exp ((|z₀.im| + 1) * u) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hwim hu0)
    have hn : ‖-((u : ℂ) ^ 2) * heatIntegrand t w u‖
        = u ^ 2 * (|Real.exp (t * u ^ 2) * phi u|
            * ‖Complex.cos (w * (u : ℂ))‖) := by
      rw [norm_mul, norm_neg, norm_pow,
        show ‖(u : ℂ)‖ = u from by
          rw [show ‖(u : ℂ)‖ = |u| from RCLike.norm_ofReal u, abs_of_nonneg hu0]]
      unfold heatIntegrand
      rw [norm_mul, show ‖((Real.exp (t * u ^ 2) * phi u : ℝ) : ℂ)‖
          = |Real.exp (t * u ^ 2) * phi u| from RCLike.norm_ofReal _]
    rw [hn]
    have hphi : |Real.exp (t * u ^ 2) * phi u|
        ≤ Real.exp (t * u ^ 2) * ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
            * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))) := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (abs_phi_le u hu0) (Real.exp_nonneg _)
    have hb0 : 0 ≤ Real.exp (t * u ^ 2)
        * ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
          * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))) :=
      mul_nonneg (Real.exp_nonneg _)
        (mul_nonneg (mul_nonneg hC0 (Real.exp_nonneg _)) (Real.exp_nonneg _))
    calc u ^ 2 * (|Real.exp (t * u ^ 2) * phi u| * ‖Complex.cos (w * (u : ℂ))‖)
        ≤ u ^ 2 * ((Real.exp (t * u ^ 2)
            * ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
              * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))))
          * Real.exp ((|z₀.im| + 1) * u)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hphi hcos (norm_nonneg _) hb0) (sq_nonneg u)
      _ = heatSqDominatingFun t (|z₀.im| + 1) u := by
          unfold heatSqDominatingFun
          have e1 : u ^ 2 * ((Real.exp (t * u ^ 2)
                * ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
                  * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))))
              * Real.exp ((|z₀.im| + 1) * u))
            = (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst * u ^ 2
              * (Real.exp (t * u ^ 2) * Real.exp (9 * u)
                * Real.exp ((|z₀.im| + 1) * u))
              * Real.exp (-(Real.pi * Real.exp (4 * u))) := by ring
          rw [e1, ← Real.exp_add, ← Real.exp_add]
          have e2 : t * u ^ 2 + 9 * u + (|z₀.im| + 1) * u
              = t * u ^ 2 + (9 + (|z₀.im| + 1)) * u := by ring
          rw [e2]
  have hint : MeasureTheory.Integrable (heatSqDominatingFun t (|z₀.im| + 1)) μ :=
    integrableOn_heatSqDominatingFun t (|z₀.im| + 1) (by positivity)
  have hdiff : ∀ᵐ u ∂μ, ∀ w ∈ Metric.ball z₀ 1,
      HasDerivAt (fun x => heatIntegrandDeriv t x u)
        (-(((u : ℝ) : ℂ) ^ 2) * heatIntegrand t w u) w :=
    Filter.Eventually.of_forall fun u w _ => heat_integrandDeriv_hasDerivAt t u w
  have hFint : MeasureTheory.Integrable (heatIntegrandDeriv t z₀) μ :=
    heat_integrandDeriv_integrable t z₀
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z₀ (by norm_num : (0:ℝ) < 1))
    (Filter.Eventually.of_forall hmeas) hFint hderv_meas hbound hint hdiff).2

/-- The second `z`-derivative of `H_t` as an integral:
`H_t''(z₀) = ∫_0^∞ −u² · e^{t u²} Φ(u) cos(z₀ u) du`. -/
theorem hasDerivAt_deriv_deBruijnNewmanH (t : ℝ) (z₀ : ℂ) :
    HasDerivAt (deriv (fun w : ℂ => deBruijnNewmanH t w))
      (∫ u : ℝ in Set.Ioi 0, -((u : ℂ) ^ 2) * heatIntegrand t z₀ u) z₀ := by
  have hEq : (fun w : ℂ => ∫ u in Set.Ioi 0, heatIntegrandDeriv t w u)
      = deriv (fun w : ℂ => deBruijnNewmanH t w) :=
    funext fun w => (deriv_deBruijnNewmanH t w).symm
  rw [← hEq]
  exact hasDerivAt_integral_heatIntegrandDeriv t z₀

/-- The `t`-derivative of `H_t` as an integral:
`∂_t H_t(z) = ∫_0^∞ u² · e^{t u²} Φ(u) cos(z u) du`. -/
theorem hasDerivAt_deBruijnNewmanH_t (z : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => deBruijnNewmanH s z)
      (∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand t z u) t := by
  set μ := MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)) with hμ
  have hmeas : ∀ s : ℝ, MeasureTheory.AEStronglyMeasurable
      (fun u : ℝ => heatIntegrand s z u) μ :=
    fun s => (continuous_heatIntegrand s z).continuousOn.aestronglyMeasurable
      measurableSet_Ioi
  have hderv_meas : MeasureTheory.AEStronglyMeasurable
      (fun u : ℝ => ((u : ℂ) ^ 2) * heatIntegrand t z u) μ :=
    ((Complex.continuous_ofReal.pow 2).mul
      (continuous_heatIntegrand t z)).continuousOn.aestronglyMeasurable
      measurableSet_Ioi
  have hC0 : (0:ℝ) ≤ (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst :=
    mul_nonneg (by positivity) phiTailConst_nonneg
  have hbound : ∀ᵐ u ∂μ, ∀ s ∈ Metric.ball t 1,
      ‖(((u : ℝ) : ℂ) ^ 2) * heatIntegrand s z u‖
        ≤ heatSqDominatingFun (t + 1) |z.im| u := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu s hs
    have hu0 : 0 ≤ u := le_of_lt hu
    have hs1 : s ≤ t + 1 := by
      have h1 : |s - t| < 1 := by
        rw [← Real.dist_eq]
        exact Metric.mem_ball.mp hs
      have h2 : s - t ≤ |s - t| := le_abs_self _
      linarith
    have hexp : Real.exp (s * u ^ 2) ≤ Real.exp ((t + 1) * u ^ 2) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hs1 (sq_nonneg u))
    have hn : ‖((u : ℂ) ^ 2) * heatIntegrand s z u‖
        = u ^ 2 * (|Real.exp (s * u ^ 2) * phi u|
            * ‖Complex.cos (z * (u : ℂ))‖) := by
      rw [norm_mul, norm_pow,
        show ‖(u : ℂ)‖ = u from by
          rw [show ‖(u : ℂ)‖ = |u| from RCLike.norm_ofReal u, abs_of_nonneg hu0]]
      unfold heatIntegrand
      rw [norm_mul, show ‖((Real.exp (s * u ^ 2) * phi u : ℝ) : ℂ)‖
          = |Real.exp (s * u ^ 2) * phi u| from RCLike.norm_ofReal _]
    rw [hn]
    have hcos : ‖Complex.cos (z * (u : ℂ))‖ ≤ Real.exp (|z.im| * u) := by
      calc ‖Complex.cos (z * (u : ℂ))‖ ≤ Real.exp |z.im * u| :=
            norm_cos_mul_ofReal_le_exp z u
        _ = Real.exp (|z.im| * u) := by rw [abs_mul, abs_of_nonneg hu0]
    have hphi : |Real.exp (s * u ^ 2) * phi u|
        ≤ Real.exp ((t + 1) * u ^ 2) * ((2 * Real.pi ^ 2 + 3 * Real.pi)
            * phiTailConst * Real.exp (9 * u)
            * Real.exp (-(Real.pi * Real.exp (4 * u)))) := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul hexp (abs_phi_le u hu0) (abs_nonneg _) (Real.exp_nonneg _)
    have hb0 : 0 ≤ Real.exp ((t + 1) * u ^ 2)
        * ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
          * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))) :=
      mul_nonneg (Real.exp_nonneg _)
        (mul_nonneg (mul_nonneg hC0 (Real.exp_nonneg _)) (Real.exp_nonneg _))
    calc u ^ 2 * (|Real.exp (s * u ^ 2) * phi u| * ‖Complex.cos (z * (u : ℂ))‖)
        ≤ u ^ 2 * ((Real.exp ((t + 1) * u ^ 2)
            * ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
              * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))))
          * Real.exp (|z.im| * u)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hphi hcos (norm_nonneg _) hb0) (sq_nonneg u)
      _ = heatSqDominatingFun (t + 1) |z.im| u := by
          unfold heatSqDominatingFun
          have e1 : u ^ 2 * ((Real.exp ((t + 1) * u ^ 2)
                * ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
                  * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))))
              * Real.exp (|z.im| * u))
            = (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst * u ^ 2
              * (Real.exp ((t + 1) * u ^ 2) * Real.exp (9 * u)
                * Real.exp (|z.im| * u))
              * Real.exp (-(Real.pi * Real.exp (4 * u))) := by ring
          rw [e1, ← Real.exp_add, ← Real.exp_add]
          have e2 : (t + 1) * u ^ 2 + 9 * u + |z.im| * u
              = (t + 1) * u ^ 2 + (9 + |z.im|) * u := by ring
          rw [e2]
  have hint : MeasureTheory.Integrable (heatSqDominatingFun (t + 1) |z.im|) μ :=
    integrableOn_heatSqDominatingFun (t + 1) |z.im| (abs_nonneg _)
  have hdiff : ∀ᵐ u ∂μ, ∀ s ∈ Metric.ball t 1,
      HasDerivAt (fun s' => heatIntegrand s' z u)
        ((((u : ℝ) : ℂ) ^ 2) * heatIntegrand s z u) s :=
    Filter.Eventually.of_forall fun u s _ => heat_integrand_hasDerivAt_t u z s
  have hFint : MeasureTheory.Integrable (fun u : ℝ => heatIntegrand t z u) μ :=
    heat_integrand_integrable t z
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds t (by norm_num : (0:ℝ) < 1))
    (Filter.Eventually.of_forall hmeas) hFint hderv_meas hbound hint hdiff).2

/-- **Phase 1b main theorem, part 1**: every `H_t` is entire
(ℂ-differentiable everywhere), by dominated differentiation under the
integral sign on `(0, ∞)`. -/
theorem differentiable_deBruijnNewmanH (t : ℝ) :
    Differentiable ℂ (deBruijnNewmanH t) := by
  intro z₀
  set μ := MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)) with hμ
  have hcont : ∀ w : ℂ, Continuous (heatIntegrand t w) := fun w => by
    unfold heatIntegrand
    fun_prop
  have hmeas : ∀ w : ℂ, MeasureTheory.AEStronglyMeasurable (heatIntegrand t w) μ :=
    fun w => (hcont w).continuousOn.aestronglyMeasurable measurableSet_Ioi
  have hderv_meas : MeasureTheory.AEStronglyMeasurable (heatIntegrandDeriv t z₀) μ :=
    (continuous_heatIntegrandDeriv t z₀).continuousOn.aestronglyMeasurable
      measurableSet_Ioi
  have hC0 : (0:ℝ) ≤ (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst :=
    mul_nonneg (by positivity) phiTailConst_nonneg
  have hbound : ∀ᵐ u ∂μ, ∀ w ∈ Metric.ball z₀ 1,
      ‖heatIntegrandDeriv t w u‖ ≤ heatDerivDominatingFun t (|z₀.im| + 1) u := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu w hw
    have hu0 : 0 ≤ u := le_of_lt hu
    have hwim : |w.im| ≤ |z₀.im| + 1 := by
      have h2 : |(w - z₀).im| ≤ ‖w - z₀‖ := Complex.abs_im_le_norm _
      have h3 : ‖w - z₀‖ < 1 := by
        rw [← dist_eq_norm]
        exact Metric.mem_ball.mp hw
      have him : w.im - z₀.im = (w - z₀).im := by simp [Complex.sub_im]
      calc |w.im| = |w.im - z₀.im + z₀.im| :=
            (congrArg abs (sub_add_cancel w.im z₀.im)).symm
        _ ≤ |w.im - z₀.im| + |z₀.im| := abs_add_le _ _
        _ ≤ ‖w - z₀‖ + |z₀.im| := by rw [him]; exact add_le_add_left h2 _
        _ ≤ 1 + |z₀.im| := by linarith [h3.le]
        _ = |z₀.im| + 1 := by ring
    have hsin : ‖Complex.sin (w * (u : ℂ))‖ ≤ Real.exp ((|z₀.im| + 1) * u) := by
      calc ‖Complex.sin (w * (u : ℂ))‖ ≤ Real.exp |w.im * u| :=
            norm_sin_mul_ofReal_le_exp w u
        _ = Real.exp (|w.im| * u) := by rw [abs_mul, abs_of_nonneg hu0]
        _ ≤ Real.exp ((|z₀.im| + 1) * u) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hwim hu0)
    have hn : ‖heatIntegrandDeriv t w u‖
        = |Real.exp (t * u ^ 2) * phi u| * (‖Complex.sin (w * (u : ℂ))‖ * u) := by
      unfold heatIntegrandDeriv
      rw [norm_mul, norm_mul, norm_neg,
        show ‖((Real.exp (t * u ^ 2) * phi u : ℝ) : ℂ)‖
          = |Real.exp (t * u ^ 2) * phi u| from RCLike.norm_ofReal _,
        show ‖(u : ℂ)‖ = u from by
          rw [show ‖(u : ℂ)‖ = |u| from RCLike.norm_ofReal u, abs_of_nonneg hu0]]
    rw [hn]
    have hphi : |Real.exp (t * u ^ 2) * phi u|
        ≤ Real.exp (t * u ^ 2) * ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
            * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))) := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (abs_phi_le u hu0) (Real.exp_nonneg _)
    have hb0 : 0 ≤ Real.exp (t * u ^ 2)
        * ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
          * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))) :=
      mul_nonneg (Real.exp_nonneg _)
        (mul_nonneg (mul_nonneg hC0 (Real.exp_nonneg _)) (Real.exp_nonneg _))
    calc |Real.exp (t * u ^ 2) * phi u| * (‖Complex.sin (w * (u : ℂ))‖ * u)
        ≤ (Real.exp (t * u ^ 2) * ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
            * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))))
          * (Real.exp ((|z₀.im| + 1) * u) * u) :=
          mul_le_mul hphi
            (mul_le_mul hsin le_rfl hu0 (Real.exp_nonneg _))
            (mul_nonneg (norm_nonneg _) hu0) hb0
      _ = heatDerivDominatingFun t (|z₀.im| + 1) u := by
          unfold heatDerivDominatingFun
          have e1 : Real.exp (t * u ^ 2)
              * ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
                * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u))))
              * (Real.exp ((|z₀.im| + 1) * u) * u)
            = (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst * u
              * (Real.exp (t * u ^ 2) * Real.exp (9 * u)
                * Real.exp ((|z₀.im| + 1) * u))
              * Real.exp (-(Real.pi * Real.exp (4 * u))) := by ring
          rw [e1, ← Real.exp_add, ← Real.exp_add]
          have e2 : t * u ^ 2 + 9 * u + (|z₀.im| + 1) * u
              = t * u ^ 2 + (9 + (|z₀.im| + 1)) * u := by ring
          rw [e2]
  have hint : MeasureTheory.Integrable (heatDerivDominatingFun t (|z₀.im| + 1)) μ :=
    integrableOn_heatDerivDominatingFun t (|z₀.im| + 1) (by positivity)
  have hdiff : ∀ᵐ u ∂μ, ∀ w ∈ Metric.ball z₀ 1,
      HasDerivAt (fun x => heatIntegrand t x u) (heatIntegrandDeriv t w u) w :=
    Filter.Eventually.of_forall fun u w _ => heat_integrand_hasDerivAt t u w
  have hFint : MeasureTheory.Integrable (heatIntegrand t z₀) μ :=
    heat_integrand_integrable t z₀
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z₀ (by norm_num : (0:ℝ) < 1))
    (Filter.Eventually.of_forall hmeas) hFint hderv_meas hbound hint hdiff
  exact h.2.differentiableAt

/-- **Phase 1b main theorem, part 2**: every `H_t` is even. -/
theorem deBruijnNewmanH_even (t : ℝ) (z : ℂ) :
    deBruijnNewmanH t (-z) = deBruijnNewmanH t z := by
  unfold deBruijnNewmanH
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro u _
  unfold heatIntegrand
  rw [neg_mul, Complex.cos_neg]

/-- Bundled Phase 1b result: `H_t` is an even entire function. -/
theorem h_even_entire (t : ℝ) :
    Differentiable ℂ (deBruijnNewmanH t) ∧
      ∀ z : ℂ, deBruijnNewmanH t (-z) = deBruijnNewmanH t z :=
  ⟨differentiable_deBruijnNewmanH t, deBruijnNewmanH_even t⟩

/-! ## Phase 1c 第一块：theta 级数、逐项求导与 `G = x·T'' + (3/2)·T'` -/

/-- General summability helper: `Σ_{n ≥ 0} (n+1)^k e^{x (n+1)}` converges
for `x < 0` (any power `k`). -/
theorem summable_shift_pow_mul_exp' {k : ℕ} {x : ℝ} (hx : x < 0) :
    Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ k * Real.exp x ^ (n + 1) := by
  have hr : ‖Real.exp x‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), Real.exp_lt_one_iff]
    exact hx
  exact (summable_nat_add_iff
      (f := fun m : ℕ => (m : ℝ) ^ k * Real.exp x ^ m) 1).mpr
    (summable_pow_mul_geometric_of_norm_lt_one k hr)

/-- The `n ≥ 1` Jacobi theta series (real, `x > 0`):
`S(x) = Σ_{n ≥ 1} e^{−π n² x}`, indexed as `n + 1` over `ℕ`. -/
noncomputable def thetaSTerm (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * x)

/-- First termwise derivative of `thetaSTerm`:
`d/dx e^{−π n² x} = e^{−π n² x} · (−π n²)`. -/
noncomputable def thetaSDerivTerm (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * x) * (-Real.pi * ((n : ℝ) + 1) ^ 2)

/-- Second termwise derivative: `d²/dx² e^{−π n² x} = e^{−π n² x} · (−π n²)²`. -/
noncomputable def thetaSDeriv2Term (n : ℕ) (x : ℝ) : ℝ :=
  (Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * x) * (-Real.pi * ((n : ℝ) + 1) ^ 2))
    * (-Real.pi * ((n : ℝ) + 1) ^ 2)

/-- The `n ≥ 1` theta series `S(x) = Σ_{n ≥ 1} e^{−π n² x}`. -/
noncomputable def thetaS (x : ℝ) : ℝ := ∑' n : ℕ, thetaSTerm n x

/-- First derivative of the full theta function `T = 1 + 2S`. -/
noncomputable def thetaTD (x : ℝ) : ℝ := 2 * (∑' n : ℕ, thetaSDerivTerm n x)

/-- Second derivative of the full theta function `T = 1 + 2S`. -/
noncomputable def thetaTDD (x : ℝ) : ℝ := 2 * (∑' n : ℕ, thetaSDeriv2Term n x)

/-- The Jacobi theta function on the positive imaginary axis, as a real
function: `T(x) = Σ_{n ∈ ℤ} e^{−π n² x} = 1 + 2 S(x)`. -/
noncomputable def thetaT (x : ℝ) : ℝ := 1 + 2 * thetaS x

theorem thetaSTerm_le (n : ℕ) {x : ℝ} (hx : 0 < x) :
    thetaSTerm n x ≤ Real.exp (-Real.pi * x) ^ (n + 1) := by
  unfold thetaSTerm
  have h1 : ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 2 := by
    have h0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.zero_le
    have hpos : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
    nth_rewrite 1 [← pow_one ((n : ℝ) + 1)]
    exact pow_le_pow_right₀ (by linarith) (by norm_num : 1 ≤ 2)
  have h2 : -Real.pi * ((n : ℝ) + 1) ^ 2 * x ≤ -Real.pi * ((n : ℝ) + 1) * x := by
    have hpx : (0 : ℝ) < Real.pi * x := by positivity
    have : Real.pi * ((n : ℝ) + 1) * x ≤ Real.pi * ((n : ℝ) + 1) ^ 2 * x := by
      apply mul_le_mul_of_nonneg_right _ hx.le
      apply mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  calc Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * x)
      ≤ Real.exp (-Real.pi * ((n : ℝ) + 1) * x) := Real.exp_le_exp.mpr h2
    _ = Real.exp (-Real.pi * x) ^ (n + 1) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring

theorem summable_thetaSTerm {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ => thetaSTerm n x := by
  have h := summable_shift_pow_mul_exp' (k := 0)
    (show -Real.pi * x < 0 from by nlinarith [Real.pi_pos])
  simp only [pow_zero, one_mul] at h
  exact Summable.of_nonneg_of_le (fun n => Real.exp_nonneg _)
    (fun n => thetaSTerm_le n hx) h

theorem summable_thetaSDerivTerm {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ => thetaSDerivTerm n x := by
  have h := summable_shift_pow_mul_exp' (k := 2)
    (show -Real.pi * x < 0 from by nlinarith [Real.pi_pos])
  refine Summable.of_norm_bounded (h.mul_left Real.pi) (fun n => ?_)
  unfold thetaSDerivTerm
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _),
    abs_of_nonpos (show -Real.pi * ((n : ℝ) + 1) ^ 2 ≤ 0 from by
      nlinarith [Real.pi_pos, sq_nonneg ((n : ℝ) + 1)]),
    show -(-Real.pi * ((n : ℝ) + 1) ^ 2 : ℝ) = Real.pi * ((n : ℝ) + 1) ^ 2 from by ring]
  have hle := thetaSTerm_le n hx
  unfold thetaSTerm at hle
  calc Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * x) * (Real.pi * ((n : ℝ) + 1) ^ 2)
      = Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * x) := by
        ring
    _ ≤ Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (-Real.pi * x) ^ (n + 1) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-Real.pi * x) ^ (n + 1)) := by
        push_cast
        ring

theorem summable_thetaSDeriv2Term {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ => thetaSDeriv2Term n x := by
  have h := summable_shift_pow_mul_exp' (k := 4)
    (show -Real.pi * x < 0 from by nlinarith [Real.pi_pos])
  refine Summable.of_norm_bounded (h.mul_left (Real.pi ^ 2)) (fun n => ?_)
  unfold thetaSDeriv2Term
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.exp_nonneg _),
    abs_of_nonpos (show -Real.pi * ((n : ℝ) + 1) ^ 2 ≤ 0 from by
      nlinarith [Real.pi_pos, sq_nonneg ((n : ℝ) + 1)]),
    show -(-Real.pi * ((n : ℝ) + 1) ^ 2 : ℝ) = Real.pi * ((n : ℝ) + 1) ^ 2 from by ring]
  have hle := thetaSTerm_le n hx
  unfold thetaSTerm at hle
  have hsq : (Real.pi * ((n : ℝ) + 1) ^ 2) * (Real.pi * ((n : ℝ) + 1) ^ 2)
      = Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 := by ring
  calc Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * x)
        * (Real.pi * ((n : ℝ) + 1) ^ 2) * (Real.pi * ((n : ℝ) + 1) ^ 2)
      = Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4
          * Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * x) := by ring
    _ ≤ Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (-Real.pi * x) ^ (n + 1) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = Real.pi ^ 2 * (((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-Real.pi * x) ^ (n + 1)) := by
        push_cast
        ring

/-- Termwise derivative identity for the theta summands. -/
theorem thetaSTerm_hasDerivAt (n : ℕ) (y : ℝ) :
    HasDerivAt (thetaSTerm n) (thetaSDerivTerm n y) y := by
  unfold thetaSTerm thetaSDerivTerm
  simpa only [mul_one] using
    ((hasDerivAt_id y).const_mul (-Real.pi * ((n : ℝ) + 1) ^ 2)).exp

/-- Second termwise derivative identity. -/
theorem thetaSDerivTerm_hasDerivAt (n : ℕ) (y : ℝ) :
    HasDerivAt (thetaSDerivTerm n) (thetaSDeriv2Term n y) y := by
  unfold thetaSDerivTerm thetaSDeriv2Term
  simpa only [mul_one] using
    (((hasDerivAt_id y).const_mul (-Real.pi * ((n : ℝ) + 1) ^ 2)).exp).mul_const
      (-Real.pi * ((n : ℝ) + 1) ^ 2)

/-- **Termwise differentiation of the theta series**: for `x > 0`,
`S'(x) = Σ_{n ≥ 1} (−π n²) e^{−π n² x}`. -/
theorem hasDerivAt_thetaS {x : ℝ} (hx : 0 < x) :
    HasDerivAt thetaS (∑' n : ℕ, thetaSDerivTerm n x) x := by
  unfold thetaS
  have hx2 : (0 : ℝ) < x / 2 := by linarith
  have hub : Summable fun n : ℕ =>
      Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-Real.pi * (x / 2)) ^ (n + 1)) :=
    (summable_shift_pow_mul_exp' (k := 2)
      (show -Real.pi * (x / 2) < 0 from by nlinarith [Real.pi_pos])).mul_left _
  have hg : ∀ n : ℕ, ∀ y : ℝ, y ∈ Set.Ioi (x / 2) →
      HasDerivAt (thetaSTerm n) (thetaSDerivTerm n y) y :=
    fun n y _ => thetaSTerm_hasDerivAt n y
  have hg' : ∀ n : ℕ, ∀ y : ℝ, y ∈ Set.Ioi (x / 2) → ‖thetaSDerivTerm n y‖
      ≤ Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-Real.pi * (x / 2)) ^ (n + 1)) := by
    intro n y hy
    have hy2 : x / 2 < y := hy
    unfold thetaSDerivTerm
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _),
      abs_of_nonpos (show -Real.pi * ((n : ℝ) + 1) ^ 2 ≤ 0 from by
        nlinarith [Real.pi_pos, sq_nonneg ((n : ℝ) + 1)]),
      show -(-Real.pi * ((n : ℝ) + 1) ^ 2 : ℝ) = Real.pi * ((n : ℝ) + 1) ^ 2 from by ring]
    have h1 : Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * y)
        ≤ Real.exp (-Real.pi * (x / 2)) ^ (n + 1) := by
      have hsq : ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 2 := by
        have h0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.zero_le
        have hpos : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
        nth_rewrite 1 [← pow_one ((n : ℝ) + 1)]
        exact pow_le_pow_right₀ (by linarith) (by norm_num : 1 ≤ 2)
      have h2 : -Real.pi * ((n : ℝ) + 1) ^ 2 * y ≤ -Real.pi * ((n : ℝ) + 1) * (x / 2) := by
        have h3 : Real.pi * ((n : ℝ) + 1) * (x / 2) ≤ Real.pi * ((n : ℝ) + 1) ^ 2 * y := by
          calc Real.pi * ((n : ℝ) + 1) * (x / 2)
              ≤ Real.pi * ((n : ℝ) + 1) * y :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)
            _ ≤ Real.pi * ((n : ℝ) + 1) ^ 2 * y := by
              apply mul_le_mul_of_nonneg_right _ (by linarith : (0 : ℝ) ≤ y)
              apply mul_le_mul_of_nonneg_left hsq (by positivity)
        linarith
      calc Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * y)
          ≤ Real.exp (-Real.pi * ((n : ℝ) + 1) * (x / 2)) := Real.exp_le_exp.mpr h2
        _ = Real.exp (-Real.pi * (x / 2)) ^ (n + 1) := by
            rw [← Real.exp_nat_mul]
            congr 1
            push_cast
            ring
    calc Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * y) * (Real.pi * ((n : ℝ) + 1) ^ 2)
        = Real.pi * (((n : ℝ) + 1) ^ 2 * Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * y)) := by
          ring
      _ ≤ Real.pi * (((n : ℝ) + 1) ^ 2 * Real.exp (-Real.pi * (x / 2)) ^ (n + 1)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h1 (by positivity)) (by positivity)
      _ = Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-Real.pi * (x / 2)) ^ (n + 1)) := by
          rw [Nat.cast_add, Nat.cast_one]
  have hy₀ : (x / 2 + 1 : ℝ) ∈ Set.Ioi (x / 2) := by
    simp only [Set.mem_Ioi]
    linarith
  have hg0 : Summable fun n : ℕ => thetaSTerm n (x / 2 + 1) :=
    summable_thetaSTerm (by linarith)
  have hy : x ∈ Set.Ioi (x / 2 : ℝ) := by
    simp only [Set.mem_Ioi]
    linarith
  exact hasDerivAt_tsum_of_isPreconnected hub isOpen_Ioi isPreconnected_Ioi hg hg' hy₀ hg0 hy

/-- **Second termwise differentiation**: for `x > 0`,
`S''(x) = Σ_{n ≥ 1} (π² n⁴) e^{−π n² x}`. -/
theorem hasDerivAt_thetaSDeriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y => ∑' n : ℕ, thetaSDerivTerm n y)
      (∑' n : ℕ, thetaSDeriv2Term n x) x := by
  have hx2 : (0 : ℝ) < x / 2 := by linarith
  have hub : Summable fun n : ℕ =>
      Real.pi ^ 2 * (((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-Real.pi * (x / 2)) ^ (n + 1)) :=
    (summable_shift_pow_mul_exp' (k := 4)
      (show -Real.pi * (x / 2) < 0 from by nlinarith [Real.pi_pos])).mul_left _
  have hg : ∀ n : ℕ, ∀ y : ℝ, y ∈ Set.Ioi (x / 2) →
      HasDerivAt (thetaSDerivTerm n) (thetaSDeriv2Term n y) y :=
    fun n y _ => thetaSDerivTerm_hasDerivAt n y
  have hg' : ∀ n : ℕ, ∀ y : ℝ, y ∈ Set.Ioi (x / 2) → ‖thetaSDeriv2Term n y‖
      ≤ Real.pi ^ 2 * (((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-Real.pi * (x / 2)) ^ (n + 1)) := by
    intro n y hy
    have hy2 : x / 2 < y := hy
    unfold thetaSDeriv2Term
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.exp_nonneg _),
      abs_of_nonpos (show -Real.pi * ((n : ℝ) + 1) ^ 2 ≤ 0 from by
        nlinarith [Real.pi_pos, sq_nonneg ((n : ℝ) + 1)]),
      show -(-Real.pi * ((n : ℝ) + 1) ^ 2 : ℝ) = Real.pi * ((n : ℝ) + 1) ^ 2 from by ring]
    have h1 : Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * y)
        ≤ Real.exp (-Real.pi * (x / 2)) ^ (n + 1) := by
      have hsq : ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 2 := by
        have h0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.zero_le
        have hpos : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
        nth_rewrite 1 [← pow_one ((n : ℝ) + 1)]
        exact pow_le_pow_right₀ (by linarith) (by norm_num : 1 ≤ 2)
      have h2 : -Real.pi * ((n : ℝ) + 1) ^ 2 * y ≤ -Real.pi * ((n : ℝ) + 1) * (x / 2) := by
        have h3 : Real.pi * ((n : ℝ) + 1) * (x / 2) ≤ Real.pi * ((n : ℝ) + 1) ^ 2 * y := by
          calc Real.pi * ((n : ℝ) + 1) * (x / 2)
              ≤ Real.pi * ((n : ℝ) + 1) * y :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)
            _ ≤ Real.pi * ((n : ℝ) + 1) ^ 2 * y := by
              apply mul_le_mul_of_nonneg_right _ (by linarith : (0 : ℝ) ≤ y)
              apply mul_le_mul_of_nonneg_left hsq (by positivity)
        linarith
      calc Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * y)
          ≤ Real.exp (-Real.pi * ((n : ℝ) + 1) * (x / 2)) := Real.exp_le_exp.mpr h2
        _ = Real.exp (-Real.pi * (x / 2)) ^ (n + 1) := by
            rw [← Real.exp_nat_mul]
            congr 1
            push_cast
            ring
    calc Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * y) * (Real.pi * ((n : ℝ) + 1) ^ 2)
          * (Real.pi * ((n : ℝ) + 1) ^ 2)
        = Real.pi ^ 2 * (((n : ℝ) + 1) ^ 4
            * Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * y)) := by ring
      _ ≤ Real.pi ^ 2 * (((n : ℝ) + 1) ^ 4 * Real.exp (-Real.pi * (x / 2)) ^ (n + 1)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h1 (by positivity)) (by positivity)
      _ = Real.pi ^ 2 * (((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-Real.pi * (x / 2)) ^ (n + 1)) := by
          rw [Nat.cast_add, Nat.cast_one]
  have hy₀ : (x / 2 + 1 : ℝ) ∈ Set.Ioi (x / 2) := by
    simp only [Set.mem_Ioi]
    linarith
  have hg0 : Summable fun n : ℕ => thetaSDerivTerm n (x / 2 + 1) :=
    summable_thetaSDerivTerm (by linarith)
  have hy : x ∈ Set.Ioi (x / 2 : ℝ) := by
    simp only [Set.mem_Ioi]
    linarith
  exact hasDerivAt_tsum_of_isPreconnected hub isOpen_Ioi isPreconnected_Ioi hg hg' hy₀ hg0 hy

/-- The full theta function `T = 1 + 2S` is differentiable with
`T'(x) = 2·S'(x)` for `x > 0`. -/
theorem hasDerivAt_thetaT {x : ℝ} (hx : 0 < x) :
    HasDerivAt thetaT (thetaTD x) x := by
  unfold thetaT thetaTD
  exact ((hasDerivAt_thetaS hx).const_mul 2).const_add 1

/-- `T'` is differentiable with `T''(x) = 2·S''(x)` for `x > 0`. -/
theorem hasDerivAt_thetaTD {x : ℝ} (hx : 0 < x) :
    HasDerivAt thetaTD (thetaTDD x) x := by
  unfold thetaTD thetaTDD
  exact (hasDerivAt_thetaSDeriv hx).const_mul 2

/-- The kernel `G(x) = Σ_{n ≥ 1} (2π² n⁴ x − 3π n²) e^{−π n² x}`
of the `x = e^{4u}` change of variables. -/
noncomputable def phiKernelGTerm (n : ℕ) (x : ℝ) : ℝ :=
  (2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * x - 3 * Real.pi * ((n : ℝ) + 1) ^ 2)
    * Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * x)

/-- `G(x) = Σ_{n ≥ 1} (2π² n⁴ x − 3π n²) e^{−π n² x}`. -/
noncomputable def phiKernelG (x : ℝ) : ℝ := ∑' n : ℕ, phiKernelGTerm n x

theorem summable_phiKernelGTerm {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ => phiKernelGTerm n x := by
  have h := summable_shift_pow_mul_exp' (k := 4)
    (show -Real.pi * x < 0 from by nlinarith [Real.pi_pos])
  refine Summable.of_norm_bounded
    ((h.mul_left (2 * Real.pi ^ 2 * |x|)).add
      ((summable_shift_pow_mul_exp' (k := 2)
        (show -Real.pi * x < 0 from by nlinarith [Real.pi_pos])).mul_left
        (3 * Real.pi))) (fun n => ?_)
  unfold phiKernelGTerm
  rw [Real.norm_eq_abs]
  have hA : (0 : ℝ) ≤ 2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * |x| := by positivity
  have hB : (0 : ℝ) ≤ 3 * Real.pi * ((n : ℝ) + 1) ^ 2 := by positivity
  have hsub : |2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * x - 3 * Real.pi * ((n : ℝ) + 1) ^ 2|
      ≤ 2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * |x| + 3 * Real.pi * ((n : ℝ) + 1) ^ 2 := by
    have h1 : |2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * x|
        = 2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * |x| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4)]
    have h2 : |3 * Real.pi * ((n : ℝ) + 1) ^ 2| = 3 * Real.pi * ((n : ℝ) + 1) ^ 2 :=
      abs_of_nonneg hB
    calc |2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * x - 3 * Real.pi * ((n : ℝ) + 1) ^ 2|
        ≤ |2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * x|
          + |3 * Real.pi * ((n : ℝ) + 1) ^ 2| := abs_sub _ _
      _ = 2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * |x|
          + 3 * Real.pi * ((n : ℝ) + 1) ^ 2 := by rw [h1, h2]
  have hle := thetaSTerm_le n hx
  unfold thetaSTerm at hle
  calc |(2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * x - 3 * Real.pi * ((n : ℝ) + 1) ^ 2)
        * Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * x)|
      = |2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * x - 3 * Real.pi * ((n : ℝ) + 1) ^ 2|
        * Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * x) := by
        rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    _ ≤ (2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * |x| + 3 * Real.pi * ((n : ℝ) + 1) ^ 2)
        * Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * x) :=
        mul_le_mul_of_nonneg_right hsub (Real.exp_nonneg _)
    _ ≤ (2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * |x| + 3 * Real.pi * ((n : ℝ) + 1) ^ 2)
        * Real.exp (-Real.pi * x) ^ (n + 1) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 2 * Real.pi ^ 2 * |x| * (((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-Real.pi * x) ^ (n + 1))
        + 3 * Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-Real.pi * x) ^ (n + 1)) := by
        push_cast
        ring

/-- **Structural identity**: `G(x) = x·T''(x) + (3/2)·T'(x)` for `x > 0`. -/
theorem phiKernelG_eq {x : ℝ} (hx : 0 < x) :
    phiKernelG x = x * thetaTDD x + (3 / 2) * thetaTD x := by
  have hs2 := summable_thetaSDeriv2Term hx
  have hs1 := summable_thetaSDerivTerm hx
  have hterm : ∀ n : ℕ, phiKernelGTerm n x
      = 2 * x * thetaSDeriv2Term n x + 3 * thetaSDerivTerm n x := by
    intro n
    unfold phiKernelGTerm thetaSDeriv2Term thetaSDerivTerm
    ring
  calc phiKernelG x = ∑' n : ℕ, phiKernelGTerm n x := rfl
    _ = ∑' n : ℕ, (2 * x * thetaSDeriv2Term n x + 3 * thetaSDerivTerm n x) :=
        tsum_congr hterm
    _ = 2 * x * (∑' n : ℕ, thetaSDeriv2Term n x)
        + 3 * (∑' n : ℕ, thetaSDerivTerm n x) := by
        rw [(hs2.mul_left (2 * x)).tsum_add (hs1.mul_left 3), tsum_mul_left, tsum_mul_left]
    _ = x * thetaTDD x + (3 / 2) * thetaTD x := by unfold thetaTDD thetaTD; ring

/-- **Change of variables**: `Φ(u) = e^{5u} · G(e^{4u})`. -/
theorem phi_eq_exp_mul_phiKernelG (u : ℝ) :
    phi u = Real.exp (5 * u) * phiKernelG (Real.exp (4 * u)) := by
  have hterm : ∀ n : ℕ, phiTerm (n + 1) u
      = Real.exp (5 * u) * phiKernelGTerm n (Real.exp (4 * u)) := by
    intro n
    unfold phiTerm phiKernelGTerm
    have e1 : Real.exp (9 * u) = Real.exp (5 * u) * Real.exp (4 * u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [e1]
    push_cast
    ring_nf
  calc phi u = ∑' n : ℕ, phiTerm (n + 1) u := rfl
    _ = ∑' n : ℕ, Real.exp (5 * u) * phiKernelGTerm n (Real.exp (4 * u)) :=
        tsum_congr hterm
    _ = Real.exp (5 * u) * phiKernelG (Real.exp (4 * u)) := by
        unfold phiKernelG; rw [tsum_mul_left]

/-! ## Phase 1c 第二块：Jacobi θ 函数方程与 Φ 偶性 -/

/-- Bridge between the real theta function `T` and Mathlib's `jacobiTheta`:
for `x > 0`, `(T x : ℂ) = ϑ(I x)`. -/
theorem thetaT_bridge {x : ℝ} (hx : 0 < x) :
    (thetaT x : ℂ) = jacobiTheta (Complex.I * (x : ℂ)) := by
  have him : 0 < (Complex.I * (x : ℂ)).im := by
    rw [Complex.mul_im]
    simpa using hx
  have hterm : ∀ n : ℕ, (thetaSTerm n x : ℂ)
      = Complex.exp (↑Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * (Complex.I * (x : ℂ))) := by
    intro n
    have e : (Complex.I : ℂ) * Complex.I = -1 := Complex.I_mul_I
    have harg : ((-Real.pi * ((n : ℝ) + 1) ^ 2 * x : ℝ) : ℂ)
        = ↑Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * (Complex.I * (x : ℂ)) := by
      rw [show (↑Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1) ^ 2 * (Complex.I * (x : ℂ))
          = -((↑Real.pi : ℂ) * ((n : ℂ) + 1) ^ 2 * (x : ℂ)) from by
        rw [show (↑Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1) ^ 2 * (Complex.I * (x : ℂ))
            = ((↑Real.pi : ℂ) * ((n : ℂ) + 1) ^ 2 * (x : ℂ)) * (Complex.I * Complex.I) from by
          ring]
        rw [e]
        ring]
      rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow,
        Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_natCast]
      ring
    unfold thetaSTerm
    rw [Complex.ofReal_exp, harg]
  have hS : (thetaS x : ℂ) = ∑' n : ℕ,
      Complex.exp (↑Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * (Complex.I * (x : ℂ))) := by
    unfold thetaS
    rw [Complex.ofReal_tsum]
    exact tsum_congr hterm
  rw [jacobiTheta_eq_tsum_nat him]
  show ((1 + 2 * thetaS x : ℝ) : ℂ)
    = 1 + 2 * ∑' n : ℕ,
      Complex.exp (↑Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * (Complex.I * (x : ℂ)))
  rw [← hS]
  push_cast
  ring

/-- **Jacobi functional equation** for the real theta function:
`√x · T(x) = T(1/x)` for `x > 0`. -/
theorem thetaT_fe {x : ℝ} (hx : 0 < x) :
    Real.sqrt x * thetaT x = thetaT (1 / x) := by
  have him : 0 < (Complex.I * (x : ℂ)).im := by
    rw [Complex.mul_im]
    simpa using hx
  have hθ : jacobiTheta ↑(ModularGroup.S • (⟨Complex.I * (x : ℂ), him⟩ : UpperHalfPlane))
      = (-Complex.I * (Complex.I * (x : ℂ))) ^ (1 / 2 : ℂ)
        * jacobiTheta (Complex.I * (x : ℂ)) :=
    jacobiTheta_S_smul _
  have hS : (↑(ModularGroup.S • (⟨Complex.I * (x : ℂ), him⟩ : UpperHalfPlane)) : ℂ)
      = Complex.I * ((1 / x : ℝ) : ℂ) := by
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk,
      show ((1 / x : ℝ) : ℂ) = (x : ℂ)⁻¹ from by rw [one_div, Complex.ofReal_inv],
      ← neg_inv, UpperHalfPlane.coe_mk, mul_inv, Complex.inv_I]
    ring
  have hF : (-Complex.I * (Complex.I * (x : ℂ))) ^ (1 / 2 : ℂ) = (Real.sqrt x : ℂ) := by
    have e1 : -Complex.I * (Complex.I * (x : ℂ)) = (x : ℂ) := by
      have e : (Complex.I : ℂ) * Complex.I = -1 := Complex.I_mul_I
      calc -Complex.I * (Complex.I * (x : ℂ))
          = -((Complex.I * Complex.I) * (x : ℂ)) := by ring
        _ = -((-1) * (x : ℂ)) := by rw [e]
        _ = (x : ℂ) := by ring
    have he : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by simp
    rw [e1, Real.sqrt_eq_rpow, ← he, ← Complex.ofReal_cpow hx.le (1 / 2 : ℝ)]
  rw [hS, hF, ← thetaT_bridge hx, ← thetaT_bridge (one_div_pos.mpr hx)] at hθ
  rw [← Complex.ofReal_mul] at hθ
  exact (Complex.ofReal_injective hθ).symm

/-- **First derivative of the functional equation**: for `y > 0`,
`T(y)/(2√y) + √y·T'(y) = −T'(1/y)/y²`. -/
theorem thetaT_fe_deriv {y : ℝ} (hy : 0 < y) :
    (1 / (2 * Real.sqrt y)) * thetaT y + Real.sqrt y * thetaTD y
      = -thetaTD (1 / y) / y ^ 2 := by
  have hf : HasDerivAt (fun y => Real.sqrt y * thetaT y)
      ((1 / (2 * Real.sqrt y)) * thetaT y + Real.sqrt y * thetaTD y) y :=
    (Real.hasDerivAt_sqrt hy.ne').mul (hasDerivAt_thetaT hy)
  have hinv : HasDerivAt (fun y : ℝ => (1 / y : ℝ)) (-(y ^ 2)⁻¹) y := by
    simpa [one_div] using hasDerivAt_inv hy.ne'
  have hg : HasDerivAt (fun y => thetaT (1 / y)) (-thetaTD (1 / y) / y ^ 2) y := by
    have h1 := (hasDerivAt_thetaT (one_div_pos.mpr hy)).comp y hinv
    convert h1 using 1
    ring
  have heq : (fun y => Real.sqrt y * thetaT y) =ᶠ[nhds y] (fun y => thetaT (1 / y)) :=
    Filter.eventually_of_mem (Ioi_mem_nhds hy) (fun z hz => thetaT_fe hz)
  exact HasDerivAt.unique ((Filter.EventuallyEq.hasDerivAt_iff heq).mp hf) hg

/-- Normalized first-order consequence of the functional equation:
`x²·T + 2x³·T' + 2√x·T'(1/x) = 0`. -/
theorem thetaT_fe_deriv1_norm {x : ℝ} (hx : 0 < x) :
    x ^ 2 * thetaT x + 2 * x ^ 3 * thetaTD x + 2 * Real.sqrt x * thetaTD (1 / x) = 0 := by
  have hs2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have hspos : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hE1x := thetaT_fe_deriv hx
  have h2s : (2 : ℝ) * Real.sqrt x ≠ 0 := mul_ne_zero (by norm_num) hspos.ne'
  have hmul : ((1 / (2 * Real.sqrt x)) * thetaT x + Real.sqrt x * thetaTD x)
        * (2 * Real.sqrt x * x ^ 2)
      = (-thetaTD (1 / x) / x ^ 2) * (2 * Real.sqrt x * x ^ 2) := by
    rw [hE1x]
  rw [show ((1 / (2 * Real.sqrt x)) * thetaT x + Real.sqrt x * thetaTD x)
        * (2 * Real.sqrt x * x ^ 2)
        = thetaT x * x ^ 2 + 2 * thetaTD x * x ^ 2 * (Real.sqrt x * Real.sqrt x) from by
      field_simp [h2s]] at hmul
  rw [show (-thetaTD (1 / x) / x ^ 2) * (2 * Real.sqrt x * x ^ 2)
        = -(2 * Real.sqrt x * thetaTD (1 / x)) from by
      field_simp [hx.ne']] at hmul
  rw [← pow_two, hs2] at hmul
  linarith [hmul]

/-- Normalized second-order consequence of the functional equation:
`−x³·T + 4x⁴·T' + 4x⁵·T'' = 4√x·T''(1/x) + 8x√x·T'(1/x)`. -/
theorem thetaT_fe_deriv2_norm {x : ℝ} (hx : 0 < x) :
    -x ^ 3 * thetaT x + 4 * x ^ 4 * thetaTD x + 4 * x ^ 5 * thetaTDD x
      = 4 * Real.sqrt x * thetaTDD (1 / x) + 8 * x * Real.sqrt x * thetaTD (1 / x) := by
  have hs2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have hspos : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hL1 : HasDerivAt (fun y : ℝ => (1 / (2 * Real.sqrt y)) * thetaT y)
      ((thetaTD x * (2 * Real.sqrt x) - thetaT x * (2 * (1 / (2 * Real.sqrt x))))
        / (2 * Real.sqrt x) ^ 2) x := by
    have h1 := (hasDerivAt_thetaT hx).div ((Real.hasDerivAt_sqrt hx.ne').const_mul 2)
      (show (2 : ℝ) * Real.sqrt x ≠ 0 from mul_ne_zero (by norm_num) hspos.ne')
    have hfun : (fun y : ℝ => (1 / (2 * Real.sqrt y)) * thetaT y)
        = thetaT / (fun y => 2 * Real.sqrt y) := by
      ext y
      simp only [Pi.div_apply]
      rw [div_eq_mul_inv, one_mul]
      ring
    rw [hfun]
    exact h1
  have hL2 : HasDerivAt (fun y : ℝ => Real.sqrt y * thetaTD y)
      ((1 / (2 * Real.sqrt x)) * thetaTD x + Real.sqrt x * thetaTDD x) x :=
    (Real.hasDerivAt_sqrt hx.ne').mul (hasDerivAt_thetaTD hx)
  have hL : HasDerivAt (fun y : ℝ => (1 / (2 * Real.sqrt y)) * thetaT y
        + Real.sqrt y * thetaTD y)
      ((thetaTD x * (2 * Real.sqrt x) - thetaT x * (2 * (1 / (2 * Real.sqrt x))))
          / (2 * Real.sqrt x) ^ 2
        + ((1 / (2 * Real.sqrt x)) * thetaTD x + Real.sqrt x * thetaTDD x)) x :=
    hL1.add hL2
  have hinv : HasDerivAt (fun y : ℝ => (1 / y : ℝ)) (-(x ^ 2)⁻¹) x := by
    simpa [one_div] using hasDerivAt_inv hx.ne'
  have hR1 : HasDerivAt (fun y : ℝ => thetaTD (1 / y) / y ^ 2)
      (((thetaTDD (1 / x) * (-(x ^ 2)⁻¹)) * x ^ 2 - thetaTD (1 / x) * (1 * x + x * 1))
        / (x ^ 2) ^ 2) x := by
    have hcomp := (hasDerivAt_thetaTD (one_div_pos.mpr hx)).comp x hinv
    have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (1 * x + x * 1) x := by
      simpa [sq] using (hasDerivAt_id x).mul (hasDerivAt_id x)
    have h1 := hcomp.div hpow (show (x : ℝ) ^ 2 ≠ 0 from pow_ne_zero 2 hx.ne')
    have hfun : (fun y : ℝ => thetaTD (1 / y) / y ^ 2)
        = (thetaTD ∘ fun y => 1 / y) / (fun y => y ^ 2) := by
      ext y
      simp only [Pi.div_apply, Function.comp_apply]
    rw [hfun]
    exact h1
  have hR : HasDerivAt (fun y : ℝ => -thetaTD (1 / y) / y ^ 2)
      (-(((thetaTDD (1 / x) * (-(x ^ 2)⁻¹)) * x ^ 2 - thetaTD (1 / x) * (1 * x + x * 1))
        / (x ^ 2) ^ 2)) x := by
    have hfun : (fun y : ℝ => -thetaTD (1 / y) / y ^ 2)
        = -fun y : ℝ => thetaTD (1 / y) / y ^ 2 := by
      ext y
      simp only [Pi.neg_apply]
      rw [neg_div]
    rw [hfun]
    exact hR1.neg
  have heq2 : (fun y : ℝ => (1 / (2 * Real.sqrt y)) * thetaT y + Real.sqrt y * thetaTD y)
      =ᶠ[nhds x] (fun y : ℝ => -thetaTD (1 / y) / y ^ 2) :=
    Filter.eventually_of_mem (Ioi_mem_nhds hx) (fun z hz => thetaT_fe_deriv hz)
  have hE2raw := HasDerivAt.unique ((Filter.EventuallyEq.hasDerivAt_iff heq2).mp hL) hR
  have h2s : (2 : ℝ) * Real.sqrt x ≠ 0 := mul_ne_zero (by norm_num) hspos.ne'
  have hmul : ((thetaTD x * (2 * Real.sqrt x) - thetaT x * (2 * (1 / (2 * Real.sqrt x))))
        / (2 * Real.sqrt x) ^ 2
        + (1 / (2 * Real.sqrt x) * thetaTD x + Real.sqrt x * thetaTDD x))
        * (4 * Real.sqrt x ^ 3 * x ^ 4)
      = (-((thetaTDD (1 / x) * -(x ^ 2)⁻¹ * x ^ 2 - thetaTD (1 / x) * (1 * x + x * 1))
        / (x ^ 2) ^ 2)) * (4 * Real.sqrt x ^ 3 * x ^ 4) := by
    rw [hE2raw]
  rw [show ((thetaTD x * (2 * Real.sqrt x) - thetaT x * (2 * (1 / (2 * Real.sqrt x))))
        / (2 * Real.sqrt x) ^ 2
        + (1 / (2 * Real.sqrt x) * thetaTD x + Real.sqrt x * thetaTDD x))
        * (4 * Real.sqrt x ^ 3 * x ^ 4)
      = (2 * Real.sqrt x ^ 2 * thetaTD x - thetaT x) * x ^ 4
        + (2 * thetaTD x * Real.sqrt x ^ 2 * x ^ 4
          + 4 * Real.sqrt x ^ 4 * x ^ 4 * thetaTDD x) from by
      field_simp [h2s]
      ring] at hmul
  rw [show (-((thetaTDD (1 / x) * -(x ^ 2)⁻¹ * x ^ 2 - thetaTD (1 / x) * (1 * x + x * 1))
        / (x ^ 2) ^ 2)) * (4 * Real.sqrt x ^ 3 * x ^ 4)
      = 4 * Real.sqrt x ^ 3 * thetaTDD (1 / x) + 8 * Real.sqrt x ^ 3 * x * thetaTD (1 / x) from by
      field_simp [hx.ne']
      ring] at hmul
  rw [hs2] at hmul
  have hs3 : Real.sqrt x ^ 3 = x * Real.sqrt x := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hs2]
  have hs4 : Real.sqrt x ^ 4 = x ^ 2 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, hs2, ← pow_two]
  rw [hs3, hs4] at hmul
  have hG : x * ((-x ^ 3 * thetaT x + 4 * x ^ 4 * thetaTD x + 4 * x ^ 5 * thetaTDD x)
      - (4 * Real.sqrt x * thetaTDD (1 / x) + 8 * x * Real.sqrt x * thetaTD (1 / x))) = 0 := by
    linear_combination hmul
  have hG' := (mul_eq_zero.mp hG).resolve_left hx.ne'
  linarith [hG']

/-- **Inversion formula for the kernel `G`**:
`G(1/x) = x^(5/2) · G(x)` for `x > 0`, written as `x²·√x` to stay in `ℕ`-powers. -/
theorem phiKernelG_inv {x : ℝ} (hx : 0 < x) :
    phiKernelG (1 / x) = x ^ 2 * Real.sqrt x * phiKernelG x := by
  rw [phiKernelG_eq (one_div_pos.mpr hx), phiKernelG_eq hx]
  have hs2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have hE1n := thetaT_fe_deriv1_norm hx
  have hE2n := thetaT_fe_deriv2_norm hx
  have hne : (4 : ℝ) * x ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hx.ne')
  have hv : x * (x : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hx.ne'
  have h4 : 4 * x ^ 2 * ((1 / x) * thetaTDD (1 / x) + (3 / 2) * thetaTD (1 / x)
        - x ^ 2 * Real.sqrt x * (x * thetaTDD x + (3 / 2) * thetaTD x)) = 0 := by
    linear_combination -Real.sqrt x * hE2n - x * Real.sqrt x * hE1n
      - (4 * thetaTDD (1 / x) + 6 * x * thetaTD (1 / x)) * hs2
      + 4 * x * thetaTDD (1 / x) * hv
  have h0 := (mul_eq_zero.mp h4).resolve_left hne
  linarith

/-- **Φ is even** (the functional equation of `ζ`, in kernel form):
`Φ(−u) = Φ(u)`. -/
theorem phi_even (u : ℝ) : phi (-u) = phi u := by
  rw [phi_eq_exp_mul_phiKernelG, phi_eq_exp_mul_phiKernelG]
  have h1 : Real.exp (4 * -u) = 1 / Real.exp (4 * u) := by
    rw [show 4 * -u = -(4 * u) from by ring, Real.exp_neg, ← one_div]
  have h5 : Real.exp (5 * -u) = (Real.exp (5 * u))⁻¹ := by
    rw [show 5 * -u = -(5 * u) from by ring, Real.exp_neg]
  rw [h1, phiKernelG_inv (Real.exp_pos _), h5]
  have h8 : Real.exp (4 * u) ^ 2 = Real.exp (8 * u) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have h2 : Real.sqrt (Real.exp (4 * u)) = Real.exp (2 * u) := by
    have h : Real.exp (2 * u) ^ 2 = Real.exp (4 * u) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [← h, Real.sqrt_sq (Real.exp_nonneg _)]
  rw [h8, h2]
  have h10 : Real.exp (8 * u) * Real.exp (2 * u) = Real.exp (5 * u) * Real.exp (5 * u) := by
    have e1 : Real.exp (8 * u) * Real.exp (2 * u) = Real.exp (10 * u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have e2 : Real.exp (5 * u) * Real.exp (5 * u) = Real.exp (10 * u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [e1, e2]
  rw [h10]
  have hne : Real.exp (5 * u) ≠ 0 := (Real.exp_pos _).ne'
  field_simp

/-! ## Prop 目标（晋升纪律见 `docs/implementation-standards.md`） -/

/-- **适定性目标**（Phase 1a）：对每个 `t : ℝ`、`z : ℂ`，被积函数
`e^{t u²} Φ(u) cos(z u)` 在 `(0, ∞)` 上可积。证明路线见调研笔记：
`|Φ(u)| ≤ K (2π² e^{9u} + 3π e^{5u}) e^{−π e^{4u}}`（`u ≥ 0`）配合
`norm_cos_mul_ofReal_le_exp` 与 `exp` 支配。 -/
def heat_integrand_integrable_target : Prop :=
  ∀ t : ℝ, ∀ z : ℂ,
    MeasureTheory.IntegrableOn (heatIntegrand t z) (Set.Ioi 0) MeasureTheory.volume

/-- Phase 1a 收官：`heat_integrand_integrable_target` 已由
`heat_integrand_integrable` 证明。 -/
theorem heat_integrand_integrable_target_proved : heat_integrand_integrable_target :=
  fun t z => heat_integrand_integrable t z

/-- **Φ 偶性目标**（Phase 1c）：`Φ(−u) = Φ(u)`。
经 Poisson 求和等价于 ζ 的函数方程（Riemann）；Mathlib 侧锚点为
`Mathlib/NumberTheory/ModularForms/JacobiTheta`。 -/
def phi_even_target : Prop :=
  ∀ u : ℝ, phi (-u) = phi u

/-- Phase 1c 收官：`phi_even_target` 已由 `phi_even` 证明。 -/
theorem phi_even_target_proved : phi_even_target := phi_even

/-! ## Phase 1d(i)：cosKernel–thetaT 桥与 `completedRiemannZeta₀` 的 Mellin 表达

H₀ 恒等式路线的第一步：把 Mathlib 的 `completedRiemannZeta₀`
（经 `hurwitzEvenFEPair 0` 的 `f_modif` 的 Mellin 变换定义）与本文的
`thetaT` 对接。关键事实：`HurwitzZeta.cosKernel 0 x = thetaT x`（`x > 0`），
以及 `f_modif` 在 `t > 1` / `0 < t < 1` 两段上的具体形态。 -/

/-- cosKernel 0 与 thetaT 的桥接（正实轴上）：两边都等于
`jacobiTheta (I · x)`。 -/
theorem cosKernel_zero_eq_thetaT {x : ℝ} (hx : 0 < x) :
    (HurwitzZeta.cosKernel 0 x : ℂ) = thetaT x := by
  have h2 := HurwitzZeta.cosKernel_def (0 : ℝ) x
  rw [QuotientAddGroup.mk_zero] at h2
  simp only [Complex.ofReal_zero, ← jacobiTheta_eq_jacobiTheta₂] at h2
  rw [h2]
  exact (thetaT_bridge hx).symm

/-- `hurwitzEvenFEPair 0` 的 `f` 就是 `cosKernel 0`（经
`evenKernel_eq_cosKernel_of_zero`）。 -/
theorem fePair_f_apply (x : ℝ) :
    (HurwitzZeta.hurwitzEvenFEPair 0).f x = (HurwitzZeta.cosKernel 0 x : ℂ) := by
  simp [HurwitzZeta.hurwitzEvenFEPair, HurwitzZeta.evenKernel_eq_cosKernel_of_zero]

theorem fePair_f₀ : (HurwitzZeta.hurwitzEvenFEPair 0).f₀ = 1 := by
  simp [HurwitzZeta.hurwitzEvenFEPair]

theorem fePair_g₀ : (HurwitzZeta.hurwitzEvenFEPair 0).g₀ = 1 := rfl

theorem fePair_ε : (HurwitzZeta.hurwitzEvenFEPair 0).ε = 1 := rfl

theorem fePair_k : (HurwitzZeta.hurwitzEvenFEPair 0).k = 1 / 2 := rfl

/-- `f_modif` 在 `t > 1` 段：`f_modif t = thetaT t − 1`（在 `ℂ` 中）。 -/
theorem f_modif_eq_of_one_lt {x : ℝ} (hx : 1 < x) :
    (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x = (thetaT x : ℂ) - 1 := by
  have hx0 : 0 < x := one_pos.trans hx
  have h1 : (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x
      = (HurwitzZeta.hurwitzEvenFEPair 0).f x - (HurwitzZeta.hurwitzEvenFEPair 0).f₀ := by
    unfold WeakFEPair.f_modif
    rw [Pi.add_apply, Set.indicator_of_mem (Set.mem_Ioi.mpr hx) _,
      Set.indicator_of_notMem (Set.notMem_Ioo_of_ge hx.le) _, add_zero]
  rw [h1, fePair_f_apply, fePair_f₀, cosKernel_zero_eq_thetaT hx0]

/-- `f_modif` 在 `0 < t < 1` 段：`f_modif t = thetaT t − t^{−1/2}`（在 `ℂ` 中）。 -/
theorem f_modif_eq_of_mem_Ioo {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x
      = (thetaT x : ℂ) - ((x ^ (-1 / 2 : ℝ) : ℝ) : ℂ) := by
  have h1 : (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x
      = (HurwitzZeta.hurwitzEvenFEPair 0).f x
        - ((HurwitzZeta.hurwitzEvenFEPair 0).ε
            * ((x ^ (-(HurwitzZeta.hurwitzEvenFEPair 0).k) : ℝ) : ℂ))
          • (HurwitzZeta.hurwitzEvenFEPair 0).g₀ := by
    unfold WeakFEPair.f_modif
    rw [Pi.add_apply, Set.indicator_of_notMem (Set.notMem_Ioi.mpr hx1.le) _,
      Set.indicator_of_mem (Set.mem_Ioo.mpr ⟨hx0, hx1⟩) _, zero_add]
  rw [h1, fePair_f_apply, fePair_ε, fePair_k, fePair_g₀, cosKernel_zero_eq_thetaT hx0]
  norm_num [smul_eq_mul]

/-- `completedRiemannZeta₀` 的 Mellin 表达（全局成立，因 `f_modif` 是
strong FE-pair 的核）：`Λ₀(s) = (1/2) · Mellin(f_modif)(s/2)`。 -/
theorem completedRiemannZeta₀_eq_half_mellin (s : ℂ) :
    completedRiemannZeta₀ s
      = (1 / 2) * mellin (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (s / 2) := by
  unfold completedRiemannZeta₀ HurwitzZeta.completedHurwitzZetaEven₀ WeakFEPair.Λ₀
  ring

/-- `u ↦ e^{4u}` 的导数（换元 `t = e^{4u}` 的 Jacobian）。 -/
theorem hasDerivAt_expFourMul (u : ℝ) :
    HasDerivAt (fun v : ℝ ↦ Real.exp (4 * v)) (4 * Real.exp (4 * u)) u := by
  have h := (HasDerivAt.const_mul 4 (hasDerivAt_id u)).exp
  rwa [mul_one, mul_comm] at h

/-- `u ↦ e^{4u}` 单射。 -/
theorem injOn_expFourMul : Set.InjOn (fun v : ℝ ↦ Real.exp (4 * v)) Set.univ := by
  intro a _ b _ h
  have h1 := Real.exp_injective h
  linarith

/-- `u ↦ e^{4u}` 的像为 `(0, ∞)`。 -/
theorem image_expFourMul : (fun v : ℝ ↦ Real.exp (4 * v)) '' Set.univ = Set.Ioi 0 := by
  ext y
  simp only [Set.mem_image, Set.mem_univ, true_and, Set.mem_Ioi]
  constructor
  · rintro ⟨u, -, rfl⟩
    exact Real.exp_pos _
  · intro hy
    exact ⟨Real.log y / 4, by
      rw [mul_div_cancel₀ _ (by norm_num : (4 : ℝ) ≠ 0), Real.exp_log hy]⟩

/-- 换元后被积函数的逐点形态：
`|4e^{4u}| • (↑(e^{4u}))^{s/2−1} • f_modif(e^{4u}) = 4 · e^{2su} · f_modif(e^{4u})`。 -/
theorem mellin_integrand_expFourMul (s : ℂ) (u : ℝ) :
    (|4 * Real.exp (4 * u)| : ℝ) • (((Real.exp (4 * u) : ℝ) : ℂ) ^ (s / 2 - 1)
      • (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp (4 * u)))
    = 4 * (Complex.exp (2 * s * (u : ℂ))
      * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp (4 * u))) := by
  have hexp_pos : 0 < Real.exp (4 * u) := Real.exp_pos _
  set w := (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp (4 * u))
  have hcpow : ((Real.exp (4 * u) : ℝ) : ℂ) ^ (s / 2 - 1)
      = Complex.exp ((4 * u : ℝ) * (s / 2 - 1)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hexp_pos.ne') _,
      ← Complex.ofReal_log hexp_pos.le, Real.log_exp]
  have hmerge : Complex.exp (((4 : ℝ) * u : ℝ) : ℂ)
        * (Complex.exp ((((4 : ℝ) * u : ℝ) : ℂ) * (s / 2 - 1)) * w)
      = Complex.exp (2 * s * (u : ℂ)) * w := by
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [abs_of_pos (by positivity : (0 : ℝ) < 4 * Real.exp (4 * u)),
    Complex.real_smul, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_ofNat, hcpow,
    Complex.ofReal_exp, mul_assoc, hmerge, ← mul_assoc]

/-- 换元 `t = e^{4u}`：Mellin 积分化为全实轴积分
`Λ₀(s) = 2 ∫_ℝ e^{2su} · f_modif(e^{4u}) du`（`dt/t = 4 du`）。
这是 H₀ 恒等式路线的测度论核心。 -/
theorem completedRiemannZeta₀_eq_two_mul_integral (s : ℂ) :
    completedRiemannZeta₀ s
      = 2 * ∫ u : ℝ, Complex.exp (2 * s * (u : ℂ))
          * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp (4 * u)) := by
  rw [completedRiemannZeta₀_eq_half_mellin]
  unfold mellin
  have hsub := MeasureTheory.integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun u _ ↦ (hasDerivAt_expFourMul u).hasDerivWithinAt) injOn_expFourMul
    (fun t ↦ ((t : ℂ) ^ (s / 2 - 1)) • (HurwitzZeta.hurwitzEvenFEPair 0).f_modif t)
  rw [image_expFourMul] at hsub
  rw [hsub, MeasureTheory.Measure.restrict_univ]
  have hcong : (∫ x : ℝ, (|4 * Real.exp (4 * x)| : ℝ)
        • (((Real.exp (4 * x) : ℝ) : ℂ) ^ (s / 2 - 1)
          • (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp (4 * x))))
      = ∫ x : ℝ, 4 * (Complex.exp (2 * s * (x : ℂ))
        * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp (4 * x))) :=
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (mellin_integrand_expFourMul s))
  show (1 / 2 : ℂ) * ∫ x : ℝ, (|4 * Real.exp (4 * x)| : ℝ)
        • (((Real.exp (4 * x) : ℝ) : ℂ) ^ (s / 2 - 1)
          • (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp (4 * x)))
      = 2 * ∫ u : ℝ, Complex.exp (2 * s * (u : ℂ))
        * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp (4 * u))
  have hfact : (∫ x : ℝ, (4 : ℂ) * (Complex.exp (2 * s * (x : ℂ))
        * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp (4 * x))))
      = 4 * ∫ x : ℝ, (Complex.exp (2 * s * (x : ℂ))
        * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp (4 * x))) :=
    MeasureTheory.integral_const_mul 4 _
  rw [hcong, hfact]
  ring

/-- `W(u) = thetaT(e^{4u}) − 1`：f_modif 在 `u > 0` 半轴的实形。 -/
noncomputable def thetaW (u : ℝ) : ℝ := thetaT (Real.exp (4 * u)) - 1

/-- `M(u) = thetaT(e^{4u}) − e^{−2u}`：f_modif 在 `u < 0` 半轴的实形。 -/
noncomputable def thetaM (u : ℝ) : ℝ := thetaT (Real.exp (4 * u)) - Real.exp (-2 * u)

/-- 可积性转移：`u ↦ e^{2su} · f_modif(e^{4u})` 在全实轴可积
（strong FE-pair 的 Mellin 收敛性经换元像传递）。 -/
theorem integrable_expFourMul_f_modif (s : ℂ) :
    MeasureTheory.Integrable (fun u : ℝ ↦ Complex.exp (2 * s * (u : ℂ))
      * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp (4 * u))) := by
  have hP1 : MeasureTheory.IntegrableOn (fun t : ℝ ↦ ((t : ℂ) ^ (s / 2 - 1))
      • (HurwitzZeta.hurwitzEvenFEPair 0).f_modif t) (Set.Ioi 0) :=
    ((HurwitzZeta.hurwitzEvenFEPair 0).toStrongFEPair.hasMellin (s / 2)).1
  have htr := (MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
      MeasurableSet.univ (fun u _ ↦ (hasDerivAt_expFourMul u).hasDerivWithinAt)
      injOn_expFourMul
      (fun t : ℝ ↦ ((t : ℂ) ^ (s / 2 - 1))
        • (HurwitzZeta.hurwitzEvenFEPair 0).f_modif t)).mp
  rw [image_expFourMul] at htr
  have hIntU := htr hP1
  rw [MeasureTheory.integrableOn_univ] at hIntU
  have h4 := hIntU.congr (Filter.Eventually.of_forall (mellin_integrand_expFourMul s))
  have h5 := h4.const_mul ((4 : ℂ)⁻¹)
  refine h5.congr (Filter.Eventually.of_forall ?_)
  intro u
  show (4 : ℂ)⁻¹ * (4 * (Complex.exp (2 * s * (u : ℂ))
      * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp (4 * u))))
    = Complex.exp (2 * s * (u : ℂ))
      * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp (4 * u))
  rw [← mul_assoc, inv_mul_cancel₀ (by norm_num : (4 : ℂ) ≠ 0), one_mul]

/-- 半轴拆分：`Λ₀(s) = 2(A + B)`，其中
`A = ∫₀^∞ e^{2su} W(u) du`，`B = ∫_{−∞}^0 e^{2su} M(u) du`（`W, M` 取实形后 coercion）。
`u = 0` 单点不影响积分（`Iio_ae_eq_Iic`）。 -/
theorem completedRiemannZeta₀_eq_integral_split (s : ℂ) :
    completedRiemannZeta₀ s
      = 2 * ((∫ u in Set.Ioi (0 : ℝ), Complex.exp (2 * s * (u : ℂ)) * (thetaW u : ℂ))
          + (∫ u in Set.Iic (0 : ℝ), Complex.exp (2 * s * (u : ℂ)) * (thetaM u : ℂ))) := by
  rw [completedRiemannZeta₀_eq_two_mul_integral]
  have hInt := integrable_expFourMul_f_modif s
  congr 1
  have hdisj : Disjoint (Set.Iic (0 : ℝ)) (Set.Ioi (0 : ℝ)) :=
    Set.disjoint_left.mpr (fun x hx1 hx2 ↦ by
      rw [Set.mem_Iic] at hx1
      rw [Set.mem_Ioi] at hx2
      linarith)
  have hsplit : (∫ u in Set.Iic (0 : ℝ), Complex.exp (2 * s * (u : ℂ))
        * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp (4 * u)))
      + (∫ u in Set.Ioi (0 : ℝ), Complex.exp (2 * s * (u : ℂ))
        * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp (4 * u)))
      = ∫ u : ℝ, Complex.exp (2 * s * (u : ℂ))
        * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp (4 * u)) := by
    rw [← MeasureTheory.setIntegral_union hdisj measurableSet_Ioi
        hInt.integrableOn hInt.integrableOn,
      Set.Iic_union_Ioi_of_le (le_refl (0 : ℝ)), MeasureTheory.Measure.restrict_univ]
  rw [← hsplit]
  have hA : (∫ u in Set.Ioi (0 : ℝ), Complex.exp (2 * s * (u : ℂ))
        * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp (4 * u)))
      = ∫ u in Set.Ioi (0 : ℝ), Complex.exp (2 * s * (u : ℂ)) * (thetaW u : ℂ) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u hu ↦ ?_)
    rw [Set.mem_Ioi] at hu
    have h1 : (1 : ℝ) < Real.exp (4 * u) :=
      Real.one_lt_exp_iff.mpr (by positivity)
    rw [f_modif_eq_of_one_lt h1]
    simp only [thetaW, Complex.ofReal_sub, Complex.ofReal_one]
  have hB : (∫ u in Set.Iic (0 : ℝ), Complex.exp (2 * s * (u : ℂ))
        * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp (4 * u)))
      = ∫ u in Set.Iic (0 : ℝ), Complex.exp (2 * s * (u : ℂ)) * (thetaM u : ℂ) := by
    rw [(MeasureTheory.setIntegral_congr_set MeasureTheory.Iio_ae_eq_Iic).symm,
      (MeasureTheory.setIntegral_congr_set MeasureTheory.Iio_ae_eq_Iic).symm]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Iio (fun u hu ↦ ?_)
    rw [Set.mem_Iio] at hu
    have hlt1 : Real.exp (4 * u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hrw : (Real.exp (4 * u)) ^ (-1 / 2 : ℝ) = Real.exp (-2 * u) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      ring
    rw [f_modif_eq_of_mem_Ioo (Real.exp_pos _) hlt1, hrw]
    simp only [thetaM, Complex.ofReal_sub]
  rw [hB, hA, add_comm]

/-- **H_t 正则性目标**（Phase 1b）：每个 `H_t` 是偶的整函数。 -/
def h_even_entire_target : Prop :=
  ∀ t : ℝ, Differentiable ℂ (deBruijnNewmanH t) ∧
    ∀ z : ℂ, deBruijnNewmanH t (-z) = deBruijnNewmanH t z

/-- Phase 1b 收官：`h_even_entire_target` 已由 `h_even_entire` 证明。 -/
theorem h_even_entire_target_proved : h_even_entire_target := h_even_entire

/-- **反向热方程目标**（Phase 1b）：`∂_t H_t = −∂_z² H_t`
（Polymath15 的 ξ 热流视角）。 -/
def backward_heat_equation_target : Prop :=
  ∀ t : ℝ, ∀ z : ℂ,
    deriv (fun s : ℝ => deBruijnNewmanH s z) t =
      - iteratedDeriv 2 (fun w : ℂ => deBruijnNewmanH t w) z

/-- The negated second-derivative integral as the negative of the
`t`-derivative integral. -/
theorem integral_neg_sq_heatIntegrand (t : ℝ) (z : ℂ) :
    (∫ u : ℝ in Set.Ioi 0, -((u : ℂ) ^ 2) * heatIntegrand t z u)
      = -(∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand t z u) := by
  rw [← MeasureTheory.integral_neg]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro u _
  exact neg_mul _ _

/-- **反向热方程**（Phase 1c 遗留目标收官）：`∂_t H_t = −∂_z² H_t`。
两侧都化为 `∫_0^∞ u² e^{t u²} Φ(u) cos(z u) du`。 -/
theorem backward_heat_equation (t : ℝ) (z : ℂ) :
    deriv (fun s : ℝ => deBruijnNewmanH s z) t =
      - iteratedDeriv 2 (fun w : ℂ => deBruijnNewmanH t w) z := by
  have h2 : iteratedDeriv 2 (fun w : ℂ => deBruijnNewmanH t w)
      = deriv (deriv (fun w : ℂ => deBruijnNewmanH t w)) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [(hasDerivAt_deBruijnNewmanH_t z t).deriv, h2,
    (hasDerivAt_deriv_deBruijnNewmanH t z).deriv,
    integral_neg_sq_heatIntegrand, neg_neg]

/-- Phase 1c 遗留收官：`backward_heat_equation_target` 已由
`backward_heat_equation` 证明。 -/
theorem backward_heat_equation_target_proved : backward_heat_equation_target :=
  fun t z => backward_heat_equation t z

/-- `H_t` 只有实零点（命题层谓词）。 -/
def AllZerosReal (t : ℝ) : Prop :=
  ∀ z : ℂ, deBruijnNewmanH t z = 0 → z.im = 0

/-- The de Bruijn–Newman constant as the threshold infimum
`Λ := inf { t : H_t has only real zeros }`.
Until de Bruijn's monotonicity and Newman's lower bound are formalized, this
`sInf` value is a placeholder; statements about `Λ` are Prop targets. -/
noncomputable def deBruijnNewmanLambda : ℝ :=
  sInf {t : ℝ | AllZerosReal t}

/-- **de Bruijn 单调性目标**（Phase 2）：实零点性质沿 `t` 向上封闭。 -/
def de_bruijn_monotone_target : Prop :=
  ∀ {t t' : ℝ}, AllZerosReal t → t ≤ t' → AllZerosReal t'

/-- **de Bruijn 上界目标**（Phase 2）：`Λ ≤ 1/2`。 -/
def lambda_le_half_target : Prop :=
  deBruijnNewmanLambda ≤ 1 / 2

/-- **Newman 下界目标**（Phase 3a）：`Λ > −∞`。 -/
def newman_lower_bound_target : Prop :=
  ∃ t₀ : ℝ, ∀ t : ℝ, t ≤ t₀ → ¬ AllZerosReal t

/-- **Rodgers–Tao 目标**（Newman 猜想，arXiv:1801.05914；Forum Math. Pi 8
(2020), e6）：`Λ ≥ 0`。这是研究论文级目标（Phase 3b），依赖 Hadamard
因子分解、零点动力学 ODE 与 Montgomery 对关联估计等缺失基础设施。 -/
def lambda_nonneg_target : Prop :=
  0 ≤ deBruijnNewmanLambda

/-- **RH 的逻辑位置目标**（Phase 2 收官）：`RH ⇔ Λ ≤ 0`。
经 `H_0(z) = (1/8)·Ξ(z/2)` 与阈值性质，本目标不依赖 `Λ ≥ 0`。 -/
def rh_iff_lambda_le_zero_target : Prop :=
  RiemannHypothesis.Statement ↔ deBruijnNewmanLambda ≤ 0

/-!
### Phase 1d(iv)：`W/M` 的导数基础设施与反射表示

为半轴分部积分准备：`W'(u) = 4e^{4u}T'(e^{4u})`，
`W''(u) = 16e^{8u}T''(e^{4u}) + 16e^{4u}T'(e^{4u})`，`M'/M''` 类似；
并由 Jacobi 函数方程给出 `M`、`M'` 在 `u → −∞` 端的反射表示。
-/

/-- `u ↦ e^{−2u}` 的导数。 -/
theorem hasDerivAt_expNegTwoMul (u : ℝ) :
    HasDerivAt (fun v : ℝ ↦ Real.exp (-2 * v)) (-2 * Real.exp (-2 * u)) u := by
  have h := (HasDerivAt.const_mul (-2 : ℝ) (hasDerivAt_id u)).exp
  rwa [mul_one, mul_comm] at h

/-- `u ↦ e^{−4u}` 的导数。 -/
theorem hasDerivAt_expNegFourMul (u : ℝ) :
    HasDerivAt (fun v : ℝ ↦ Real.exp (-4 * v)) (-4 * Real.exp (-4 * u)) u := by
  have h := (HasDerivAt.const_mul (-4 : ℝ) (hasDerivAt_id u)).exp
  rwa [mul_one, mul_comm] at h

/-- `W'(u) = 4e^{4u}·T'(e^{4u})`（链式法则形态）。 -/
noncomputable def thetaWD (u : ℝ) : ℝ := 4 * Real.exp (4 * u) * thetaTD (Real.exp (4 * u))

/-- `W''(u) = 16e^{8u}·T''(e^{4u}) + 16e^{4u}·T'(e^{4u})`。 -/
noncomputable def thetaWDD (u : ℝ) : ℝ :=
  16 * Real.exp (8 * u) * thetaTDD (Real.exp (4 * u))
    + 16 * Real.exp (4 * u) * thetaTD (Real.exp (4 * u))

/-- `M'(u) = W'(u) + 2e^{−2u}`（`M = W + 1 − e^{−2u}`）。 -/
noncomputable def thetaMD (u : ℝ) : ℝ := thetaWD u + 2 * Real.exp (-2 * u)

/-- `M''(u) = W''(u) − 4e^{−2u}`。 -/
noncomputable def thetaMDD (u : ℝ) : ℝ := thetaWDD u - 4 * Real.exp (-2 * u)

/-- `W` 处处可导，导数为 `thetaWD`。 -/
theorem hasDerivAt_thetaW (u : ℝ) : HasDerivAt thetaW (thetaWD u) u := by
  have h1 := (hasDerivAt_thetaT (Real.exp_pos (4 * u))).comp u (hasDerivAt_expFourMul u)
  have h2 := h1.sub (hasDerivAt_const u (1 : ℝ))
  rw [show thetaTD (Real.exp (4 * u)) * (4 * Real.exp (4 * u)) - 0
      = thetaWD u from by unfold thetaWD; ring] at h2
  exact h2

/-- `thetaWD` 处处可导，导数为 `thetaWDD`（乘积法则 + 链式法则）。 -/
theorem hasDerivAt_thetaWD (u : ℝ) : HasDerivAt thetaWD (thetaWDD u) u := by
  have hA : HasDerivAt (fun v : ℝ ↦ 4 * Real.exp (4 * v))
      (4 * (4 * Real.exp (4 * u))) u :=
    (hasDerivAt_expFourMul u).const_mul 4
  have hB := (hasDerivAt_thetaTD (Real.exp_pos (4 * u))).comp u (hasDerivAt_expFourMul u)
  have h := hA.mul hB
  rw [Function.comp_apply, show 4 * (4 * Real.exp (4 * u)) * thetaTD (Real.exp (4 * u))
        + 4 * Real.exp (4 * u) * (thetaTDD (Real.exp (4 * u)) * (4 * Real.exp (4 * u)))
      = thetaWDD u from ?_] at h
  · exact h
  · unfold thetaWDD
    rw [show Real.exp (8 * u) = Real.exp (4 * u) * Real.exp (4 * u) from by
      rw [← Real.exp_add]
      congr 1
      ring]
    ring

/-- `M` 处处可导，导数为 `thetaMD`。 -/
theorem hasDerivAt_thetaM (u : ℝ) : HasDerivAt thetaM (thetaMD u) u := by
  have h1 := (hasDerivAt_thetaT (Real.exp_pos (4 * u))).comp u (hasDerivAt_expFourMul u)
  have h := h1.sub (hasDerivAt_expNegTwoMul u)
  rw [show thetaTD (Real.exp (4 * u)) * (4 * Real.exp (4 * u)) - -2 * Real.exp (-2 * u)
      = thetaMD u from by unfold thetaMD thetaWD; ring] at h
  exact h

/-- `thetaMD` 处处可导，导数为 `thetaMDD`。 -/
theorem hasDerivAt_thetaMD (u : ℝ) : HasDerivAt thetaMD (thetaMDD u) u := by
  have h2 : HasDerivAt (fun v : ℝ ↦ 2 * Real.exp (-2 * v))
      (2 * (-2 * Real.exp (-2 * u))) u :=
    (hasDerivAt_expNegTwoMul u).const_mul 2
  have h := (hasDerivAt_thetaWD u).add h2
  rw [show thetaWDD u + 2 * (-2 * Real.exp (-2 * u)) = thetaMDD u from by
    unfold thetaMDD; ring] at h
  exact h

/-- `M` 的反射表示：`M(u) = 2e^{−2u}·S(e^{−4u})`（Jacobi 函数方程）。
给出 `u → −∞` 端的超指数衰减。 -/
theorem thetaM_eq_reflected (u : ℝ) :
    thetaM u = 2 * Real.exp (-2 * u) * thetaS (Real.exp (-4 * u)) := by
  have hsqrt : Real.sqrt (Real.exp (4 * u)) = Real.exp (2 * u) := by
    rw [Real.sqrt_eq_iff_eq_sq (Real.exp_nonneg _) (Real.exp_nonneg _), pow_two,
      ← Real.exp_add]
    congr 1
    ring
  have hinv : 1 / Real.exp (4 * u) = Real.exp (-4 * u) := by
    rw [show (-4 : ℝ) * u = -(4 * u) from by ring, Real.exp_neg, one_div]
  have hfe := thetaT_fe (Real.exp_pos (4 * u))
  rw [hsqrt, hinv] at hfe
  have hT : thetaT (Real.exp (4 * u)) = Real.exp (-2 * u) * thetaT (Real.exp (-4 * u)) := by
    rw [← hfe]
    rw [show Real.exp (-2 * u) * (Real.exp (2 * u) * thetaT (Real.exp (4 * u)))
        = (Real.exp (-2 * u) * Real.exp (2 * u)) * thetaT (Real.exp (4 * u)) from by ring,
      ← Real.exp_add, show (-2 : ℝ) * u + 2 * u = (0 : ℝ) from by ring, Real.exp_zero,
      one_mul]
  unfold thetaM
  rw [hT]
  unfold thetaT
  ring

/-- `M'` 的反射表示：
`M'(u) = −4e^{−2u}·S(e^{−4u}) − 4e^{−6u}·T'(e^{−4u})`。 -/
theorem thetaMD_eq_reflected (u : ℝ) :
    thetaMD u = -4 * Real.exp (-2 * u) * thetaS (Real.exp (-4 * u))
      - 4 * Real.exp (-6 * u) * thetaTD (Real.exp (-4 * u)) := by
  have hS := (hasDerivAt_thetaS (Real.exp_pos (-4 * u))).comp u (hasDerivAt_expNegFourMul u)
  have hE : HasDerivAt (fun v : ℝ ↦ 2 * Real.exp (-2 * v))
      (2 * (-2 * Real.exp (-2 * u))) u :=
    (hasDerivAt_expNegTwoMul u).const_mul 2
  have hmul := hE.mul hS
  have hder : deriv thetaM u = thetaMD u := (hasDerivAt_thetaM u).deriv
  rw [← hder]
  have hfun : thetaM = fun u : ℝ ↦ 2 * Real.exp (-2 * u) * thetaS (Real.exp (-4 * u)) :=
    funext thetaM_eq_reflected
  rw [hfun]
  have h1 := hmul.deriv
  rw [Function.comp_apply, show 2 * (-2 * Real.exp (-2 * u)) * thetaS (Real.exp (-4 * u))
        + 2 * Real.exp (-2 * u)
          * ((∑' n : ℕ, thetaSDerivTerm n (Real.exp (-4 * u))) * (-4 * Real.exp (-4 * u)))
      = -4 * Real.exp (-2 * u) * thetaS (Real.exp (-4 * u))
        - 4 * Real.exp (-6 * u) * thetaTD (Real.exp (-4 * u)) from ?_] at h1
  · exact h1
  · have hTD : (∑' n : ℕ, thetaSDerivTerm n (Real.exp (-4 * u)))
        = thetaTD (Real.exp (-4 * u)) / 2 := by
      unfold thetaTD
      ring
    rw [hTD, show Real.exp (-6 * u) = Real.exp (-2 * u) * Real.exp (-4 * u) from by
      rw [← Real.exp_add]
      congr 1
      ring]
    ring

/-!
### Phase 1d(iv-b1)：theta 级数在 `x ≥ 1` 的指数衰减界

为 `W/M` 在无穷远端的极限与可积性准备常数与估计：
`|S(x)| ≤ Cs·e^{−πx}`，`|T'(x)| ≤ 2π·Cs₁·e^{−πx}`，
`|T''(x)| ≤ 2π²·K₁·e^{−πx}`（`x ≥ 1`）。
-/

/-- `S` 衰减界常数：`Cs = Σ_{n≥0} e^{−πn} = 1/(1−e^{−π})`。 -/
noncomputable def thetaSConst : ℝ := ∑' n : ℕ, Real.exp (-Real.pi) ^ n

theorem summable_thetaSConst : Summable fun n : ℕ => Real.exp (-Real.pi) ^ n := by
  have hr : ‖Real.exp (-Real.pi)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), Real.exp_lt_one_iff]
    exact neg_lt_zero.mpr Real.pi_pos
  exact summable_geometric_of_norm_lt_one hr

theorem thetaSConst_nonneg : 0 ≤ thetaSConst :=
  tsum_nonneg fun _ => pow_nonneg (Real.exp_nonneg _) _

/-- `S'` 衰减界常数：`Cs₁ = Σ (n+1)² e^{−πn}`。 -/
noncomputable def thetaSD1Const : ℝ :=
  ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-Real.pi) ^ n

theorem summable_thetaSD1Const :
    Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-Real.pi) ^ n := by
  have hr : ‖Real.exp (-Real.pi)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), Real.exp_lt_one_iff]
    exact neg_lt_zero.mpr Real.pi_pos
  have h := (summable_nat_add_iff
      (f := fun m : ℕ => (m : ℝ) ^ 2 * Real.exp (-Real.pi) ^ m) 1).mpr
    (summable_pow_mul_geometric_of_norm_lt_one 2 hr)
  have hne : Real.exp (-Real.pi) ≠ 0 := Real.exp_ne_zero _
  refine (h.mul_left (Real.exp (-Real.pi))⁻¹).congr (fun n => ?_)
  rw [pow_succ]
  field_simp
  ring

theorem thetaSD1Const_nonneg : 0 ≤ thetaSD1Const := tsum_nonneg fun _ => by positivity

/-- `phiTailConst ≥ 1`（第 0 项即为 1）。 -/
theorem one_le_phiTailConst : (1 : ℝ) ≤ phiTailConst := by
  have h := Summable.le_tsum summable_phiTailConst 0 (fun m _ => by positivity)
  have h0 : ((0 + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-Real.pi) ^ 0 = 1 := by simp
  rw [h0] at h
  exact h

/-- `x ≥ 1` 时 `|S(x)| ≤ Cs·e^{−πx}`。 -/
theorem abs_thetaS_le {x : ℝ} (hx : 1 ≤ x) :
    |thetaS x| ≤ thetaSConst * Real.exp (-Real.pi * x) := by
  have hx0 : 0 < x := by linarith
  have hs : Summable fun n : ℕ => Real.exp (-Real.pi * x) * Real.exp (-Real.pi) ^ n :=
    summable_thetaSConst.mul_left _
  have hST : ∀ n : ℕ, thetaSTerm n x ≤ Real.exp (-Real.pi * x) * Real.exp (-Real.pi) ^ n := by
    intro n
    calc thetaSTerm n x ≤ Real.exp (-Real.pi * x) ^ (n + 1) := thetaSTerm_le n hx0
      _ = Real.exp (-Real.pi * x) * Real.exp (-Real.pi * x) ^ n := by rw [pow_succ]; ring
      _ ≤ Real.exp (-Real.pi * x) * Real.exp (-Real.pi) ^ n := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
          apply pow_le_pow_left₀ (Real.exp_nonneg _) _ n
          apply Real.exp_le_exp.mpr
          nlinarith [Real.pi_pos]
  have hn : Summable fun n : ℕ => ‖thetaSTerm n x‖ :=
    Summable.of_norm_bounded hs (fun n => by
      simp only [Real.norm_eq_abs, abs_abs]
      rw [abs_of_nonneg (show (0 : ℝ) ≤ thetaSTerm n x from Real.exp_nonneg _)]
      exact hST n)
  calc |thetaS x| = ‖∑' n : ℕ, thetaSTerm n x‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n : ℕ, ‖thetaSTerm n x‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n : ℕ, Real.exp (-Real.pi * x) * Real.exp (-Real.pi) ^ n :=
        Summable.tsum_le_tsum (fun n => by
          rw [Real.norm_eq_abs,
            abs_of_nonneg (show (0 : ℝ) ≤ thetaSTerm n x from Real.exp_nonneg _)]
          exact hST n) hn hs
    _ = Real.exp (-Real.pi * x) * thetaSConst := by unfold thetaSConst; rw [tsum_mul_left]
    _ = thetaSConst * Real.exp (-Real.pi * x) := by ring

/-- `x ≥ 1` 时 `|T'(x)| ≤ 2π·Cs₁·e^{−πx}`。 -/
theorem abs_thetaTD_le {x : ℝ} (hx : 1 ≤ x) :
    |thetaTD x| ≤ (2 * Real.pi * thetaSD1Const) * Real.exp (-Real.pi * x) := by
  have hx0 : 0 < x := by linarith
  have hs : Summable fun n : ℕ =>
      Real.pi * Real.exp (-Real.pi * x) * (((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-Real.pi) ^ n) :=
    summable_thetaSD1Const.mul_left _
  have hST : ∀ n : ℕ, |thetaSDerivTerm n x| ≤ Real.pi * Real.exp (-Real.pi * x)
      * (((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-Real.pi) ^ n) := by
    intro n
    have h1 : Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * x)
        ≤ Real.exp (-Real.pi * x) * Real.exp (-Real.pi) ^ n := by
      calc Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * x) = thetaSTerm n x := rfl
        _ ≤ Real.exp (-Real.pi * x) ^ (n + 1) := thetaSTerm_le n hx0
        _ = Real.exp (-Real.pi * x) * Real.exp (-Real.pi * x) ^ n := by rw [pow_succ]; ring
        _ ≤ Real.exp (-Real.pi * x) * Real.exp (-Real.pi) ^ n := by
            apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
            apply pow_le_pow_left₀ (Real.exp_nonneg _) _ n
            apply Real.exp_le_exp.mpr
            nlinarith [Real.pi_pos]
    have hneg : -Real.pi * ((n : ℝ) + 1) ^ 2 < 0 := by
      have hp : (0 : ℝ) < Real.pi * ((n : ℝ) + 1) ^ 2 := by positivity
      linarith
    unfold thetaSDerivTerm
    rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _), abs_of_neg hneg]
    calc Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * x) * -(-Real.pi * ((n : ℝ) + 1) ^ 2)
        = (Real.pi * ((n : ℝ) + 1) ^ 2) * Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * x) := by ring
      _ ≤ (Real.pi * ((n : ℝ) + 1) ^ 2)
          * (Real.exp (-Real.pi * x) * Real.exp (-Real.pi) ^ n) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Real.pi * Real.exp (-Real.pi * x)
          * (((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-Real.pi) ^ n) := by push_cast; ring
  have hn : Summable fun n : ℕ => ‖thetaSDerivTerm n x‖ :=
    Summable.of_norm_bounded hs (fun n => by
      simp only [Real.norm_eq_abs, abs_abs]
      exact hST n)
  have h2 : ‖(2 : ℝ)‖ = 2 := by rw [Real.norm_eq_abs]; norm_num
  calc |thetaTD x| = ‖thetaTD x‖ := (Real.norm_eq_abs _).symm
    _ = 2 * ‖∑' n : ℕ, thetaSDerivTerm n x‖ := by unfold thetaTD; rw [norm_mul, h2]
    _ ≤ 2 * ∑' n : ℕ, ‖thetaSDerivTerm n x‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hn) (by norm_num)
    _ ≤ 2 * ∑' n : ℕ, Real.pi * Real.exp (-Real.pi * x)
          * (((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-Real.pi) ^ n) :=
        mul_le_mul_of_nonneg_left (Summable.tsum_le_tsum (fun n => by
          rw [Real.norm_eq_abs]; exact hST n) hn hs) (by norm_num)
    _ = 2 * (Real.pi * Real.exp (-Real.pi * x) * thetaSD1Const) := by
        unfold thetaSD1Const; rw [tsum_mul_left]
    _ = (2 * Real.pi * thetaSD1Const) * Real.exp (-Real.pi * x) := by ring

/-- `x ≥ 1` 时 `|T''(x)| ≤ 2π²·K₁·e^{−πx}`。 -/
theorem abs_thetaTDD_le {x : ℝ} (hx : 1 ≤ x) :
    |thetaTDD x| ≤ (2 * Real.pi ^ 2 * phiTailConst) * Real.exp (-Real.pi * x) := by
  have hx0 : 0 < x := by linarith
  have hs : Summable fun n : ℕ =>
      Real.pi ^ 2 * Real.exp (-Real.pi * x)
        * (((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-Real.pi) ^ n) :=
    summable_phiTailConst.mul_left _
  have hST : ∀ n : ℕ, |thetaSDeriv2Term n x| ≤ Real.pi ^ 2 * Real.exp (-Real.pi * x)
      * (((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-Real.pi) ^ n) := by
    intro n
    have h1 : Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * x)
        ≤ Real.exp (-Real.pi * x) * Real.exp (-Real.pi) ^ n := by
      calc Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * x) = thetaSTerm n x := rfl
        _ ≤ Real.exp (-Real.pi * x) ^ (n + 1) := thetaSTerm_le n hx0
        _ = Real.exp (-Real.pi * x) * Real.exp (-Real.pi * x) ^ n := by rw [pow_succ]; ring
        _ ≤ Real.exp (-Real.pi * x) * Real.exp (-Real.pi) ^ n := by
            apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
            apply pow_le_pow_left₀ (Real.exp_nonneg _) _ n
            apply Real.exp_le_exp.mpr
            nlinarith [Real.pi_pos]
    have hneg : -Real.pi * ((n : ℝ) + 1) ^ 2 < 0 := by
      have hp : (0 : ℝ) < Real.pi * ((n : ℝ) + 1) ^ 2 := by positivity
      linarith
    unfold thetaSDeriv2Term
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.exp_nonneg _), abs_of_neg hneg]
    calc Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * x) * -(-Real.pi * ((n : ℝ) + 1) ^ 2)
          * -(-Real.pi * ((n : ℝ) + 1) ^ 2)
        = (Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4) * Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * x) := by
          ring
      _ ≤ (Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4)
          * (Real.exp (-Real.pi * x) * Real.exp (-Real.pi) ^ n) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Real.pi ^ 2 * Real.exp (-Real.pi * x)
          * (((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-Real.pi) ^ n) := by push_cast; ring
  have hn : Summable fun n : ℕ => ‖thetaSDeriv2Term n x‖ :=
    Summable.of_norm_bounded hs (fun n => by
      simp only [Real.norm_eq_abs, abs_abs]
      exact hST n)
  have h2 : ‖(2 : ℝ)‖ = 2 := by rw [Real.norm_eq_abs]; norm_num
  calc |thetaTDD x| = ‖thetaTDD x‖ := (Real.norm_eq_abs _).symm
    _ = 2 * ‖∑' n : ℕ, thetaSDeriv2Term n x‖ := by unfold thetaTDD; rw [norm_mul, h2]
    _ ≤ 2 * ∑' n : ℕ, ‖thetaSDeriv2Term n x‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hn) (by norm_num)
    _ ≤ 2 * ∑' n : ℕ, Real.pi ^ 2 * Real.exp (-Real.pi * x)
          * (((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-Real.pi) ^ n) :=
        mul_le_mul_of_nonneg_left (Summable.tsum_le_tsum (fun n => by
          rw [Real.norm_eq_abs]; exact hST n) hn hs) (by norm_num)
    _ = 2 * (Real.pi ^ 2 * Real.exp (-Real.pi * x) * phiTailConst) := by
        unfold phiTailConst; rw [tsum_mul_left]
    _ = (2 * Real.pi ^ 2 * phiTailConst) * Real.exp (-Real.pi * x) := by ring

/-!
### Phase 1d(iv-b2)：`W` 侧的界、极限与可积性

`u ≥ 0` 时 `|W| ≤ 2Cs·e^{−πe^{4u}}`、`|W'| ≤ 8πCs₁·e^{4u}e^{−πe^{4u}}`、
`|W''| ≤ (32π²K₁+32πCs₁)e^{8u}e^{−πe^{4u}}`；主引理
`integrableOn_exp_mul_exp_neg` / `tendsto_exp_mul_exp_neg_atTop`
给出任意指数斜率下的可积性与衰减，由此得到 IBP 所需的
`e^{au}·↑W / ↑W' / ↑W''` 可积性与 `↑W·e^{au}, ↑W'·e^{au} → 0`。
-/

/-- `thetaW` 在 `ℝ` 上连续（处处可导）。 -/
theorem continuous_thetaW : Continuous thetaW :=
  continuous_iff_continuousAt.mpr fun u => (hasDerivAt_thetaW u).continuousAt

/-- `thetaWD` 在 `ℝ` 上连续。 -/
theorem continuous_thetaWD : Continuous thetaWD :=
  continuous_iff_continuousAt.mpr fun u => (hasDerivAt_thetaWD u).continuousAt

/-- `thetaWDD` 可测（`W'` 的导数）。 -/
theorem measurable_thetaWDD : Measurable thetaWDD := by
  have h : deriv thetaWD = thetaWDD := funext fun u => (hasDerivAt_thetaWD u).deriv
  rw [← h]
  exact measurable_deriv thetaWD

/-- `u ≥ 0` 时 `|W(u)| ≤ 2Cs·e^{−πe^{4u}}`。 -/
theorem abs_thetaW_le {u : ℝ} (hu : 0 ≤ u) :
    |thetaW u| ≤ 2 * thetaSConst * Real.exp (-(Real.pi * Real.exp (4 * u))) := by
  have h1 : (1:ℝ) ≤ Real.exp (4 * u) := Real.one_le_exp (by linarith)
  have hW : thetaW u = 2 * thetaS (Real.exp (4 * u)) := by
    unfold thetaW thetaT; ring
  rw [hW, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  calc 2 * |thetaS (Real.exp (4 * u))|
      ≤ 2 * (thetaSConst * Real.exp (-Real.pi * Real.exp (4 * u))) :=
        mul_le_mul_of_nonneg_left (abs_thetaS_le h1) (by norm_num)
    _ = 2 * thetaSConst * Real.exp (-(Real.pi * Real.exp (4 * u))) := by
        rw [show (-Real.pi * Real.exp (4 * u)) = -(Real.pi * Real.exp (4 * u)) from by ring]
        ring

/-- `u ≥ 0` 时 `|W'(u)| ≤ 8π·Cs₁·e^{4u}·e^{−πe^{4u}}`。 -/
theorem abs_thetaWD_le {u : ℝ} (hu : 0 ≤ u) :
    |thetaWD u| ≤ 8 * Real.pi * thetaSD1Const * Real.exp (4 * u)
      * Real.exp (-(Real.pi * Real.exp (4 * u))) := by
  have h1 : (1:ℝ) ≤ Real.exp (4 * u) := Real.one_le_exp (by linarith)
  unfold thetaWD
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4),
    abs_of_nonneg (Real.exp_nonneg _)]
  calc 4 * Real.exp (4 * u) * |thetaTD (Real.exp (4 * u))|
      ≤ 4 * Real.exp (4 * u)
        * ((2 * Real.pi * thetaSD1Const) * Real.exp (-Real.pi * Real.exp (4 * u))) :=
        mul_le_mul_of_nonneg_left (abs_thetaTD_le h1) (by positivity)
    _ = 8 * Real.pi * thetaSD1Const * Real.exp (4 * u)
        * Real.exp (-(Real.pi * Real.exp (4 * u))) := by
        rw [show (-Real.pi * Real.exp (4 * u)) = -(Real.pi * Real.exp (4 * u)) from by ring]
        ring

/-- `u ≥ 0` 时 `|W''(u)| ≤ (32π²K₁ + 32πCs₁)·e^{8u}·e^{−πe^{4u}}`。 -/
theorem abs_thetaWDD_le {u : ℝ} (hu : 0 ≤ u) :
    |thetaWDD u| ≤ (32 * Real.pi ^ 2 * phiTailConst + 32 * Real.pi * thetaSD1Const)
      * Real.exp (8 * u) * Real.exp (-(Real.pi * Real.exp (4 * u))) := by
  have h1 : (1:ℝ) ≤ Real.exp (4 * u) := Real.one_le_exp (by linarith)
  have h48 : Real.exp (4 * u) ≤ Real.exp (8 * u) := Real.exp_le_exp.mpr (by linarith)
  have hT : |16 * Real.exp (8 * u) * thetaTDD (Real.exp (4 * u))
      + 16 * Real.exp (4 * u) * thetaTD (Real.exp (4 * u))|
      ≤ 16 * Real.exp (8 * u) * |thetaTDD (Real.exp (4 * u))|
        + 16 * Real.exp (4 * u) * |thetaTD (Real.exp (4 * u))| := by
    calc |16 * Real.exp (8 * u) * thetaTDD (Real.exp (4 * u))
          + 16 * Real.exp (4 * u) * thetaTD (Real.exp (4 * u))|
        ≤ |16 * Real.exp (8 * u) * thetaTDD (Real.exp (4 * u))|
          + |16 * Real.exp (4 * u) * thetaTD (Real.exp (4 * u))| := abs_add_le _ _
      _ = 16 * Real.exp (8 * u) * |thetaTDD (Real.exp (4 * u))|
          + 16 * Real.exp (4 * u) * |thetaTD (Real.exp (4 * u))| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 16),
            abs_of_nonneg (Real.exp_nonneg _), abs_mul, abs_mul,
            abs_of_nonneg (by norm_num : (0:ℝ) ≤ 16), abs_of_nonneg (Real.exp_nonneg _)]
  unfold thetaWDD
  calc |16 * Real.exp (8 * u) * thetaTDD (Real.exp (4 * u))
        + 16 * Real.exp (4 * u) * thetaTD (Real.exp (4 * u))|
      ≤ 16 * Real.exp (8 * u) * |thetaTDD (Real.exp (4 * u))|
        + 16 * Real.exp (4 * u) * |thetaTD (Real.exp (4 * u))| := hT
    _ ≤ 16 * Real.exp (8 * u) * ((2 * Real.pi ^ 2 * phiTailConst)
          * Real.exp (-Real.pi * Real.exp (4 * u)))
        + 16 * Real.exp (8 * u) * ((2 * Real.pi * thetaSD1Const)
          * Real.exp (-Real.pi * Real.exp (4 * u))) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (abs_thetaTDD_le h1) (by positivity)
        · exact mul_le_mul (mul_le_mul_of_nonneg_left h48 (by norm_num))
            (abs_thetaTD_le h1) (abs_nonneg _) (by positivity)
    _ = (32 * Real.pi ^ 2 * phiTailConst + 32 * Real.pi * thetaSD1Const)
        * Real.exp (8 * u) * Real.exp (-(Real.pi * Real.exp (4 * u))) := by
        rw [show (-Real.pi * Real.exp (4 * u)) = -(Real.pi * Real.exp (4 * u)) from by ring]
        ring

/-- 主可积性引理：任意指数斜率 `K`，`u ↦ e^{Ku}·e^{−πe^{4u}}` 在 `(0,∞)` 可积。 -/
theorem integrableOn_exp_mul_exp_neg (K : ℝ) :
    MeasureTheory.IntegrableOn (fun u : ℝ => Real.exp (K * u)
      * Real.exp (-(Real.pi * Real.exp (4 * u)))) (Set.Ioi 0) MeasureTheory.volume := by
  have hcont : Continuous (fun u : ℝ => Real.exp (K * u)
      * Real.exp (-(Real.pi * Real.exp (4 * u)))) := by fun_prop
  apply MeasureTheory.Integrable.mono'
    (integrableOn_heatDominatingFun 0 (max 0 (K - 9)) (le_max_left _ _))
  · exact hcont.continuousOn.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := le_of_lt hu
    have hK : K * u ≤ (9 + max 0 (K - 9)) * u := by
      have h1 : K ≤ 9 + max 0 (K - 9) := by
        have h := le_max_right 0 (K - 9)
        linarith
      exact mul_le_mul_of_nonneg_right h1 hu0
    have hC1 : (1:ℝ) ≤ (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst := by
      have h1 := one_le_phiTailConst
      have h2 : (1:ℝ) ≤ 2 * Real.pi ^ 2 + 3 * Real.pi := by nlinarith [Real.pi_gt_three]
      calc (1:ℝ) = 1 * 1 := by ring
        _ ≤ (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst :=
            mul_le_mul h2 h1 zero_le_one (by positivity)
    calc ‖Real.exp (K * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))‖
        = Real.exp (K * u) * Real.exp (-(Real.pi * Real.exp (4 * u))) := by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      _ ≤ Real.exp (0 * u ^ 2 + (9 + max 0 (K - 9)) * u)
          * Real.exp (-(Real.pi * Real.exp (4 * u))) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
          apply Real.exp_le_exp.mpr
          have h0 : (0:ℝ) * u ^ 2 + (9 + max 0 (K - 9)) * u
              = (9 + max 0 (K - 9)) * u := by ring
          rw [h0]
          exact hK
      _ ≤ (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
          * Real.exp (0 * u ^ 2 + (9 + max 0 (K - 9)) * u)
          * Real.exp (-(Real.pi * Real.exp (4 * u))) := by
          have he : (0:ℝ) ≤ Real.exp (0 * u ^ 2 + (9 + max 0 (K - 9)) * u)
              * Real.exp (-(Real.pi * Real.exp (4 * u))) := by positivity
          calc Real.exp (0 * u ^ 2 + (9 + max 0 (K - 9)) * u)
                * Real.exp (-(Real.pi * Real.exp (4 * u)))
              = 1 * (Real.exp (0 * u ^ 2 + (9 + max 0 (K - 9)) * u)
                * Real.exp (-(Real.pi * Real.exp (4 * u)))) := by ring
            _ ≤ ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst)
                * (Real.exp (0 * u ^ 2 + (9 + max 0 (K - 9)) * u)
                  * Real.exp (-(Real.pi * Real.exp (4 * u)))) :=
                mul_le_mul_of_nonneg_right hC1 he
            _ = (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
                * Real.exp (0 * u ^ 2 + (9 + max 0 (K - 9)) * u)
                * Real.exp (-(Real.pi * Real.exp (4 * u))) := by ring
      _ = heatDominatingFun 0 (max 0 (K - 9)) u := rfl

/-- 主极限引理：`e^{Cu}·e^{−πe^{4u}} → 0`（`u → +∞`，任意 `C`）。 -/
theorem tendsto_exp_mul_exp_neg_atTop (C : ℝ) :
    Filter.Tendsto (fun u : ℝ => Real.exp (C * u)
      * Real.exp (-(Real.pi * Real.exp (4 * u)))) Filter.atTop (nhds 0) := by
  have hquad : ∀ u : ℝ, 0 ≤ u → 4 * Real.pi * u ^ 2 ≤ Real.pi * Real.exp (4 * u) := by
    intro u hu
    have h := Real.add_one_le_exp (2 * u)
    have hnn : (0:ℝ) ≤ 1 + 2 * u := by linarith
    have h1 : (1 + 2 * u) ^ 2 ≤ (Real.exp (2 * u)) ^ 2 :=
      pow_le_pow_left₀ hnn (by linarith) 2
    have h2 : (Real.exp (2 * u)) ^ 2 = Real.exp (4 * u) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have h3 : 4 * u ^ 2 ≤ Real.exp (4 * u) := by nlinarith
    calc 4 * Real.pi * u ^ 2 = Real.pi * (4 * u ^ 2) := by ring
      _ ≤ Real.pi * Real.exp (4 * u) :=
          mul_le_mul_of_nonneg_left h3 (le_of_lt Real.pi_pos)
  refine squeeze_zero' (f := fun u => Real.exp (C * u)
    * Real.exp (-(Real.pi * Real.exp (4 * u)))) (g := fun u => Real.exp (-u)) ?_ ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 0] with u hu
    positivity
  · filter_upwards [Filter.eventually_ge_atTop (max 1 ((C + 1) / (4 * Real.pi)))] with u hu
    have hu1 : (1:ℝ) ≤ u := le_trans (le_max_left _ _) hu
    have hu0 : 0 ≤ u := by linarith
    have hpi4 : (0:ℝ) < 4 * Real.pi := by positivity
    have hC : C + 1 ≤ 4 * Real.pi * u := by
      have h2 := le_trans (le_max_right 1 ((C + 1) / (4 * Real.pi))) hu
      have h3 : (C + 1) / (4 * Real.pi) * (4 * Real.pi) ≤ u * (4 * Real.pi) :=
        mul_le_mul_of_nonneg_right h2 (le_of_lt hpi4)
      rw [div_mul_cancel₀ _ (ne_of_gt hpi4)] at h3
      linarith
    have hmain : C * u - Real.pi * Real.exp (4 * u) ≤ -u := by
      have h3 := hquad u hu0
      nlinarith [hC, h3, hu0]
    calc Real.exp (C * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))
        = Real.exp (C * u + -(Real.pi * Real.exp (4 * u))) := by rw [← Real.exp_add]
      _ = Real.exp (C * u - Real.pi * Real.exp (4 * u)) := by
          congr 1
      _ ≤ Real.exp (-u) := Real.exp_le_exp.mpr hmain
  · exact Real.tendsto_exp_atBot.comp Filter.tendsto_neg_atTop_atBot

/-- D1：`↑W(u)·e^{au} → 0`（`u → +∞`）。 -/
theorem tendsto_thetaW_cexp_atTop (a : ℂ) :
    Filter.Tendsto (fun u : ℝ => (thetaW u : ℂ) * Complex.exp (a * (u : ℂ)))
      Filter.atTop (nhds 0) := by
  have hre : ∀ u : ℝ, (a * (u : ℂ)).re = a.re * u := fun u => by simp [Complex.mul_re]
  have hg : Filter.Tendsto (fun u : ℝ => 2 * thetaSConst * (Real.exp (a.re * u)
      * Real.exp (-(Real.pi * Real.exp (4 * u))))) Filter.atTop
      (nhds (2 * thetaSConst * 0)) :=
    Filter.Tendsto.const_mul _ (tendsto_exp_mul_exp_neg_atTop a.re)
  rw [mul_zero] at hg
  refine squeeze_zero_norm' (f := fun u : ℝ => (thetaW u : ℂ) * Complex.exp (a * (u : ℂ)))
    (a := fun u : ℝ => 2 * thetaSConst * (Real.exp (a.re * u)
      * Real.exp (-(Real.pi * Real.exp (4 * u))))) ?_ hg
  filter_upwards [Filter.eventually_ge_atTop 0] with u hu
  calc ‖(thetaW u : ℂ) * Complex.exp (a * (u : ℂ))‖
      = |thetaW u| * Real.exp (a.re * u) := by
        rw [norm_mul, show ‖(thetaW u : ℂ)‖ = |thetaW u| from RCLike.norm_ofReal _, Complex.norm_exp, hre u]
    _ ≤ (2 * thetaSConst * Real.exp (-(Real.pi * Real.exp (4 * u))))
        * Real.exp (a.re * u) :=
        mul_le_mul_of_nonneg_right (abs_thetaW_le hu) (Real.exp_nonneg _)
    _ = 2 * thetaSConst * (Real.exp (a.re * u)
        * Real.exp (-(Real.pi * Real.exp (4 * u)))) := by ring

/-- D2：`↑W'(u)·e^{au} → 0`（`u → +∞`）。 -/
theorem tendsto_thetaWD_cexp_atTop (a : ℂ) :
    Filter.Tendsto (fun u : ℝ => (thetaWD u : ℂ) * Complex.exp (a * (u : ℂ)))
      Filter.atTop (nhds 0) := by
  have hre : ∀ u : ℝ, (a * (u : ℂ)).re = a.re * u := fun u => by simp [Complex.mul_re]
  have hg : Filter.Tendsto (fun u : ℝ => 8 * Real.pi * thetaSD1Const
      * (Real.exp ((a.re + 4) * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))))
      Filter.atTop (nhds (8 * Real.pi * thetaSD1Const * 0)) :=
    Filter.Tendsto.const_mul _ (tendsto_exp_mul_exp_neg_atTop (a.re + 4))
  rw [mul_zero] at hg
  refine squeeze_zero_norm' (f := fun u : ℝ => (thetaWD u : ℂ) * Complex.exp (a * (u : ℂ)))
    (a := fun u : ℝ => 8 * Real.pi * thetaSD1Const * (Real.exp ((a.re + 4) * u)
      * Real.exp (-(Real.pi * Real.exp (4 * u))))) ?_ hg
  filter_upwards [Filter.eventually_ge_atTop 0] with u hu
  calc ‖(thetaWD u : ℂ) * Complex.exp (a * (u : ℂ))‖
      = |thetaWD u| * Real.exp (a.re * u) := by
        rw [norm_mul, show ‖(thetaWD u : ℂ)‖ = |thetaWD u| from RCLike.norm_ofReal _, Complex.norm_exp, hre u]
    _ ≤ (8 * Real.pi * thetaSD1Const * Real.exp (4 * u)
        * Real.exp (-(Real.pi * Real.exp (4 * u)))) * Real.exp (a.re * u) :=
        mul_le_mul_of_nonneg_right (abs_thetaWD_le hu) (Real.exp_nonneg _)
    _ = 8 * Real.pi * thetaSD1Const * (Real.exp ((a.re + 4) * u)
        * Real.exp (-(Real.pi * Real.exp (4 * u)))) := by
        have e1 : Real.exp ((a.re + 4) * u) = Real.exp (a.re * u) * Real.exp (4 * u) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [e1]
        ring

/-- I1：`e^{au}·↑W(u)` 在 `(0,∞)` 可积。 -/
theorem integrableOn_cexp_thetaW (a : ℂ) :
    MeasureTheory.IntegrableOn (fun u : ℝ => Complex.exp (a * (u : ℂ)) * (thetaW u : ℂ))
      (Set.Ioi 0) MeasureTheory.volume := by
  have hre : ∀ u : ℝ, (a * (u : ℂ)).re = a.re * u := fun u => by simp [Complex.mul_re]
  apply MeasureTheory.Integrable.mono'
    ((integrableOn_exp_mul_exp_neg a.re).const_mul (2 * thetaSConst))
  · exact ((by fun_prop : Measurable (fun u : ℝ => Complex.exp (a * (u : ℂ)))).mul
      (Complex.measurable_ofReal.comp continuous_thetaW.measurable)).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := le_of_lt hu
    calc ‖Complex.exp (a * (u : ℂ)) * (thetaW u : ℂ)‖
        = Real.exp (a.re * u) * |thetaW u| := by
          rw [norm_mul, Complex.norm_exp, hre u, show ‖(thetaW u : ℂ)‖ = |thetaW u| from RCLike.norm_ofReal _]
      _ ≤ Real.exp (a.re * u)
          * (2 * thetaSConst * Real.exp (-(Real.pi * Real.exp (4 * u)))) :=
          mul_le_mul_of_nonneg_left (abs_thetaW_le hu0) (Real.exp_nonneg _)
      _ = 2 * thetaSConst * (Real.exp (a.re * u)
          * Real.exp (-(Real.pi * Real.exp (4 * u)))) := by ring

/-- I2：`e^{au}·↑W'(u)` 在 `(0,∞)` 可积。 -/
theorem integrableOn_cexp_thetaWD (a : ℂ) :
    MeasureTheory.IntegrableOn (fun u : ℝ => Complex.exp (a * (u : ℂ)) * (thetaWD u : ℂ))
      (Set.Ioi 0) MeasureTheory.volume := by
  have hre : ∀ u : ℝ, (a * (u : ℂ)).re = a.re * u := fun u => by simp [Complex.mul_re]
  apply MeasureTheory.Integrable.mono'
    ((integrableOn_exp_mul_exp_neg (a.re + 4)).const_mul (8 * Real.pi * thetaSD1Const))
  · exact ((by fun_prop : Measurable (fun u : ℝ => Complex.exp (a * (u : ℂ)))).mul
      (Complex.measurable_ofReal.comp continuous_thetaWD.measurable)).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := le_of_lt hu
    calc ‖Complex.exp (a * (u : ℂ)) * (thetaWD u : ℂ)‖
        = Real.exp (a.re * u) * |thetaWD u| := by
          rw [norm_mul, Complex.norm_exp, hre u, show ‖(thetaWD u : ℂ)‖ = |thetaWD u| from RCLike.norm_ofReal _]
      _ ≤ Real.exp (a.re * u) * (8 * Real.pi * thetaSD1Const * Real.exp (4 * u)
          * Real.exp (-(Real.pi * Real.exp (4 * u)))) :=
          mul_le_mul_of_nonneg_left (abs_thetaWD_le hu0) (Real.exp_nonneg _)
      _ = 8 * Real.pi * thetaSD1Const * (Real.exp ((a.re + 4) * u)
          * Real.exp (-(Real.pi * Real.exp (4 * u)))) := by
          have e1 : Real.exp ((a.re + 4) * u) = Real.exp (a.re * u) * Real.exp (4 * u) := by
            rw [← Real.exp_add]
            congr 1
            ring
          rw [e1]
          ring

/-- I3：`e^{au}·↑W''(u)` 在 `(0,∞)` 可积。 -/
theorem integrableOn_cexp_thetaWDD (a : ℂ) :
    MeasureTheory.IntegrableOn (fun u : ℝ => Complex.exp (a * (u : ℂ)) * (thetaWDD u : ℂ))
      (Set.Ioi 0) MeasureTheory.volume := by
  have hre : ∀ u : ℝ, (a * (u : ℂ)).re = a.re * u := fun u => by simp [Complex.mul_re]
  apply MeasureTheory.Integrable.mono'
    ((integrableOn_exp_mul_exp_neg (a.re + 8)).const_mul
      (32 * Real.pi ^ 2 * phiTailConst + 32 * Real.pi * thetaSD1Const))
  · exact ((by fun_prop : Measurable (fun u : ℝ => Complex.exp (a * (u : ℂ)))).mul
      (Complex.measurable_ofReal.comp measurable_thetaWDD)).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := le_of_lt hu
    calc ‖Complex.exp (a * (u : ℂ)) * (thetaWDD u : ℂ)‖
        = Real.exp (a.re * u) * |thetaWDD u| := by
          rw [norm_mul, Complex.norm_exp, hre u, show ‖(thetaWDD u : ℂ)‖ = |thetaWDD u| from RCLike.norm_ofReal _]
      _ ≤ Real.exp (a.re * u) * ((32 * Real.pi ^ 2 * phiTailConst
          + 32 * Real.pi * thetaSD1Const) * Real.exp (8 * u)
          * Real.exp (-(Real.pi * Real.exp (4 * u)))) :=
          mul_le_mul_of_nonneg_left (abs_thetaWDD_le hu0) (Real.exp_nonneg _)
      _ = (32 * Real.pi ^ 2 * phiTailConst + 32 * Real.pi * thetaSD1Const)
          * (Real.exp ((a.re + 8) * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))) := by
          have e1 : Real.exp ((a.re + 8) * u) = Real.exp (a.re * u) * Real.exp (8 * u) := by
            rw [← Real.exp_add]
            congr 1
            ring
          rw [e1]
          ring

/-!
### Phase 1d(iv-c)：`M` 侧（`−∞` 端）的界、极限与可积性

反射表示给出 `u ≤ 0` 时
`|M| ≤ 2Cs·e^{−2u}e^{−πe^{−4u}}`，`|M'| ≤ (4Cs·e^{−2u}+8πCs₁·e^{−6u})e^{−πe^{−4u}}`；
`thetaMDD_eq_reflected` 给出 `M''` 反射表示与对应界；
主引理 `tendsto_exp_mul_exp_neg_atBot` / `integrableOn_exp_mul_exp_neg_atBot`
由 `+∞` 端经 `u ↦ −u` 保测换元得到。
-/

/-- `u ↦ e^{−6u}` 的导数。 -/
theorem hasDerivAt_expNegSixMul (u : ℝ) :
    HasDerivAt (fun v : ℝ ↦ Real.exp (-6 * v)) (-6 * Real.exp (-6 * u)) u := by
  have h := (HasDerivAt.const_mul (-6 : ℝ) (hasDerivAt_id u)).exp
  rwa [mul_one, mul_comm] at h

/-- `thetaM` 在 `ℝ` 上连续。 -/
theorem continuous_thetaM : Continuous thetaM :=
  continuous_iff_continuousAt.mpr fun u => (hasDerivAt_thetaM u).continuousAt

/-- `thetaMD` 在 `ℝ` 上连续。 -/
theorem continuous_thetaMD : Continuous thetaMD :=
  continuous_iff_continuousAt.mpr fun u => (hasDerivAt_thetaMD u).continuousAt

/-- `thetaMDD` 可测（`M'` 的导数）。 -/
theorem measurable_thetaMDD : Measurable thetaMDD := by
  have h : deriv thetaMD = thetaMDD := funext fun u => (hasDerivAt_thetaMD u).deriv
  rw [← h]
  exact measurable_deriv thetaMD

/-- 主极限引理（`−∞` 端）：`e^{Cu}·e^{−πe^{−4u}} → 0`（`u → −∞`，任意 `C`）。 -/
theorem tendsto_exp_mul_exp_neg_atBot (C : ℝ) :
    Filter.Tendsto (fun u : ℝ => Real.exp (C * u)
      * Real.exp (-(Real.pi * Real.exp (-4 * u)))) Filter.atBot (nhds 0) := by
  have h := (tendsto_exp_mul_exp_neg_atTop (-C)).comp Filter.tendsto_neg_atBot_atTop
  refine h.congr (fun u => ?_)
  have e1 : (-C) * (-u) = C * u := by ring
  have e2 : (4:ℝ) * (-u) = -4 * u := by ring
  rw [Function.comp_apply, e1, e2]

/-- 主可积性引理（`−∞` 端）：任意 `K`，`u ↦ e^{Ku}·e^{−πe^{−4u}}` 在 `(−∞,0]` 可积。 -/
theorem integrableOn_exp_mul_exp_neg_atBot (K : ℝ) :
    MeasureTheory.IntegrableOn (fun u : ℝ => Real.exp (K * u)
      * Real.exp (-(Real.pi * Real.exp (-4 * u)))) (Set.Iic 0) MeasureTheory.volume := by
  have h := ((MeasureTheory.Measure.measurePreserving_neg MeasureTheory.volume
      ).integrableOn_comp_preimage (Homeomorph.neg ℝ).measurableEmbedding).2
    (integrableOn_exp_mul_exp_neg (-K))
  have hset : (Neg.neg : ℝ → ℝ) ⁻¹' Set.Ioi (0 : ℝ) = Set.Iio (0 : ℝ) := by
    ext u
    simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_Iio]
    exact neg_pos
  rw [hset] at h
  rw [integrableOn_Iic_iff_integrableOn_Iio]
  refine h.congr_fun ?_ measurableSet_Iio
  intro u _
  have e1 : (-K) * (-u) = K * u := by ring
  have e2 : (4:ℝ) * (-u) = -4 * u := by ring
  simp only [Function.comp_apply, e1, e2]

/-- `u ≤ 0` 时 `|M(u)| ≤ 2Cs·e^{−2u}·e^{−πe^{−4u}}`（反射表示）。 -/
theorem abs_thetaM_le {u : ℝ} (hu : u ≤ 0) :
    |thetaM u| ≤ 2 * thetaSConst * Real.exp (-2 * u)
      * Real.exp (-(Real.pi * Real.exp (-4 * u))) := by
  have h1 : (1:ℝ) ≤ Real.exp (-4 * u) := Real.one_le_exp (by linarith)
  rw [thetaM_eq_reflected, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
    abs_of_nonneg (Real.exp_nonneg _)]
  calc 2 * Real.exp (-2 * u) * |thetaS (Real.exp (-4 * u))|
      ≤ 2 * Real.exp (-2 * u) * (thetaSConst * Real.exp (-Real.pi * Real.exp (-4 * u))) :=
        mul_le_mul_of_nonneg_left (abs_thetaS_le h1) (by positivity)
    _ = 2 * thetaSConst * Real.exp (-2 * u) * Real.exp (-(Real.pi * Real.exp (-4 * u))) := by
        rw [show (-Real.pi * Real.exp (-4 * u)) = -(Real.pi * Real.exp (-4 * u)) from by ring]
        ring

/-- `M''` 的反射表示：
`M''(u) = 8e^{−2u}S(e^{−4u}) + 32e^{−6u}T'(e^{−4u}) + 16e^{−10u}T''(e^{−4u})`。 -/
theorem thetaMDD_eq_reflected (u : ℝ) :
    thetaMDD u = 8 * Real.exp (-2 * u) * thetaS (Real.exp (-4 * u))
      + 32 * Real.exp (-6 * u) * thetaTD (Real.exp (-4 * u))
      + 16 * Real.exp (-10 * u) * thetaTDD (Real.exp (-4 * u)) := by
  have hS := (hasDerivAt_thetaS (Real.exp_pos (-4 * u))).comp u (hasDerivAt_expNegFourMul u)
  have hTD := (hasDerivAt_thetaTD (Real.exp_pos (-4 * u))).comp u (hasDerivAt_expNegFourMul u)
  have hE2 : HasDerivAt (fun v : ℝ ↦ -4 * Real.exp (-2 * v))
      ((-4 : ℝ) * (-2 * Real.exp (-2 * u))) u :=
    (hasDerivAt_expNegTwoMul u).const_mul (-4)
  have hE6 : HasDerivAt (fun v : ℝ ↦ 4 * Real.exp (-6 * v))
      ((4 : ℝ) * (-6 * Real.exp (-6 * u))) u :=
    (hasDerivAt_expNegSixMul u).const_mul 4
  have hmul := (hE2.mul hS).sub (hE6.mul hTD)
  have hder : deriv thetaMD u = thetaMDD u := (hasDerivAt_thetaMD u).deriv
  rw [← hder]
  have hfun : thetaMD = fun u : ℝ ↦ -4 * Real.exp (-2 * u) * thetaS (Real.exp (-4 * u))
      - 4 * Real.exp (-6 * u) * thetaTD (Real.exp (-4 * u)) :=
    funext thetaMD_eq_reflected
  rw [hfun]
  have h1 := hmul.deriv
  rw [Function.comp_apply, Function.comp_apply,
    show (-4 : ℝ) * (-2 * Real.exp (-2 * u)) * thetaS (Real.exp (-4 * u))
        + -4 * Real.exp (-2 * u)
          * ((∑' n : ℕ, thetaSDerivTerm n (Real.exp (-4 * u))) * (-4 * Real.exp (-4 * u)))
        - ((4 : ℝ) * (-6 * Real.exp (-6 * u)) * thetaTD (Real.exp (-4 * u))
          + 4 * Real.exp (-6 * u)
            * (thetaTDD (Real.exp (-4 * u)) * (-4 * Real.exp (-4 * u))))
      = 8 * Real.exp (-2 * u) * thetaS (Real.exp (-4 * u))
        + 32 * Real.exp (-6 * u) * thetaTD (Real.exp (-4 * u))
        + 16 * Real.exp (-10 * u) * thetaTDD (Real.exp (-4 * u)) from ?_] at h1
  · exact h1
  · have hTD2 : (∑' n : ℕ, thetaSDerivTerm n (Real.exp (-4 * u)))
        = thetaTD (Real.exp (-4 * u)) / 2 := by
      unfold thetaTD
      ring
    rw [hTD2,
      show Real.exp (-10 * u) = Real.exp (-2 * u) * Real.exp (-4 * u) * Real.exp (-4 * u)
        from by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring,
      show Real.exp (-6 * u) = Real.exp (-2 * u) * Real.exp (-4 * u) from by
        rw [← Real.exp_add]
        congr 1
        ring]
    ring

/-- `u ≤ 0` 时 `|M'(u)|` 的反射衰减界。 -/
theorem abs_thetaMD_le {u : ℝ} (hu : u ≤ 0) :
    |thetaMD u| ≤ 4 * thetaSConst * Real.exp (-2 * u)
        * Real.exp (-(Real.pi * Real.exp (-4 * u)))
      + 8 * Real.pi * thetaSD1Const * Real.exp (-6 * u)
        * Real.exp (-(Real.pi * Real.exp (-4 * u))) := by
  have h1 : (1:ℝ) ≤ Real.exp (-4 * u) := Real.one_le_exp (by linarith)
  rw [thetaMD_eq_reflected]
  calc |-4 * Real.exp (-2 * u) * thetaS (Real.exp (-4 * u))
        - 4 * Real.exp (-6 * u) * thetaTD (Real.exp (-4 * u))|
      = |-4 * Real.exp (-2 * u) * thetaS (Real.exp (-4 * u))
        + -(4 * Real.exp (-6 * u) * thetaTD (Real.exp (-4 * u)))| := by
        rw [sub_eq_add_neg]
    _ ≤ |-4 * Real.exp (-2 * u) * thetaS (Real.exp (-4 * u))|
        + |-(4 * Real.exp (-6 * u) * thetaTD (Real.exp (-4 * u)))| := abs_add_le _ _
    _ ≤ (4 * Real.exp (-2 * u) * (thetaSConst * Real.exp (-Real.pi * Real.exp (-4 * u))))
        + (4 * Real.exp (-6 * u) * ((2 * Real.pi * thetaSD1Const)
          * Real.exp (-Real.pi * Real.exp (-4 * u)))) := by
        apply add_le_add
        · rw [abs_mul, abs_mul, abs_of_neg (by norm_num : (-4:ℝ) < 0), neg_neg,
            abs_of_nonneg (Real.exp_nonneg _)]
          exact mul_le_mul_of_nonneg_left (abs_thetaS_le h1) (by positivity)
        · rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4),
            abs_of_nonneg (Real.exp_nonneg _)]
          exact mul_le_mul_of_nonneg_left (abs_thetaTD_le h1) (by positivity)
    _ = 4 * thetaSConst * Real.exp (-2 * u) * Real.exp (-(Real.pi * Real.exp (-4 * u)))
        + 8 * Real.pi * thetaSD1Const * Real.exp (-6 * u)
          * Real.exp (-(Real.pi * Real.exp (-4 * u))) := by
        rw [show (-Real.pi * Real.exp (-4 * u)) = -(Real.pi * Real.exp (-4 * u)) from by ring]
        ring

/-- `u ≤ 0` 时 `|M''(u)|` 的反射衰减界。 -/
theorem abs_thetaMDD_le {u : ℝ} (hu : u ≤ 0) :
    |thetaMDD u| ≤ 8 * thetaSConst * Real.exp (-2 * u)
        * Real.exp (-(Real.pi * Real.exp (-4 * u)))
      + 64 * Real.pi * thetaSD1Const * Real.exp (-6 * u)
        * Real.exp (-(Real.pi * Real.exp (-4 * u)))
      + 32 * Real.pi ^ 2 * phiTailConst * Real.exp (-10 * u)
        * Real.exp (-(Real.pi * Real.exp (-4 * u))) := by
  have h1 : (1:ℝ) ≤ Real.exp (-4 * u) := Real.one_le_exp (by linarith)
  rw [thetaMDD_eq_reflected]
  calc |8 * Real.exp (-2 * u) * thetaS (Real.exp (-4 * u))
        + 32 * Real.exp (-6 * u) * thetaTD (Real.exp (-4 * u))
        + 16 * Real.exp (-10 * u) * thetaTDD (Real.exp (-4 * u))|
      ≤ |8 * Real.exp (-2 * u) * thetaS (Real.exp (-4 * u))|
        + |32 * Real.exp (-6 * u) * thetaTD (Real.exp (-4 * u))|
        + |16 * Real.exp (-10 * u) * thetaTDD (Real.exp (-4 * u))| := by
        calc |8 * Real.exp (-2 * u) * thetaS (Real.exp (-4 * u))
              + 32 * Real.exp (-6 * u) * thetaTD (Real.exp (-4 * u))
              + 16 * Real.exp (-10 * u) * thetaTDD (Real.exp (-4 * u))|
            ≤ |8 * Real.exp (-2 * u) * thetaS (Real.exp (-4 * u))
              + 32 * Real.exp (-6 * u) * thetaTD (Real.exp (-4 * u))|
              + |16 * Real.exp (-10 * u) * thetaTDD (Real.exp (-4 * u))| := abs_add_le _ _
          _ ≤ (|8 * Real.exp (-2 * u) * thetaS (Real.exp (-4 * u))|
              + |32 * Real.exp (-6 * u) * thetaTD (Real.exp (-4 * u))|)
              + |16 * Real.exp (-10 * u) * thetaTDD (Real.exp (-4 * u))| :=
              add_le_add_left (abs_add_le _ _) _
    _ ≤ (8 * Real.exp (-2 * u) * (thetaSConst * Real.exp (-Real.pi * Real.exp (-4 * u))))
        + (32 * Real.exp (-6 * u) * ((2 * Real.pi * thetaSD1Const)
          * Real.exp (-Real.pi * Real.exp (-4 * u))))
        + (16 * Real.exp (-10 * u) * ((2 * Real.pi ^ 2 * phiTailConst)
          * Real.exp (-Real.pi * Real.exp (-4 * u)))) := by
        apply add_le_add
        · apply add_le_add
          · rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 8),
              abs_of_nonneg (Real.exp_nonneg _)]
            exact mul_le_mul_of_nonneg_left (abs_thetaS_le h1) (by positivity)
          · rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 32),
              abs_of_nonneg (Real.exp_nonneg _)]
            exact mul_le_mul_of_nonneg_left (abs_thetaTD_le h1) (by positivity)
        · rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 16),
            abs_of_nonneg (Real.exp_nonneg _)]
          exact mul_le_mul_of_nonneg_left (abs_thetaTDD_le h1) (by positivity)
    _ = 8 * thetaSConst * Real.exp (-2 * u) * Real.exp (-(Real.pi * Real.exp (-4 * u)))
        + 64 * Real.pi * thetaSD1Const * Real.exp (-6 * u)
          * Real.exp (-(Real.pi * Real.exp (-4 * u)))
        + 32 * Real.pi ^ 2 * phiTailConst * Real.exp (-10 * u)
          * Real.exp (-(Real.pi * Real.exp (-4 * u))) := by
        rw [show (-Real.pi * Real.exp (-4 * u)) = -(Real.pi * Real.exp (-4 * u)) from by ring]
        ring

/-- D3：`↑M(u)·e^{au} → 0`（`u → −∞`）。 -/
theorem tendsto_thetaM_cexp_atBot (a : ℂ) :
    Filter.Tendsto (fun u : ℝ => (thetaM u : ℂ) * Complex.exp (a * (u : ℂ)))
      Filter.atBot (nhds 0) := by
  have hre : ∀ u : ℝ, (a * (u : ℂ)).re = a.re * u := fun u => by simp [Complex.mul_re]
  have hg : Filter.Tendsto (fun u : ℝ => 2 * thetaSConst * (Real.exp ((a.re - 2) * u)
      * Real.exp (-(Real.pi * Real.exp (-4 * u))))) Filter.atBot
      (nhds (2 * thetaSConst * 0)) :=
    Filter.Tendsto.const_mul _ (tendsto_exp_mul_exp_neg_atBot (a.re - 2))
  rw [mul_zero] at hg
  refine squeeze_zero_norm' (f := fun u : ℝ => (thetaM u : ℂ) * Complex.exp (a * (u : ℂ)))
    (a := fun u : ℝ => 2 * thetaSConst * (Real.exp ((a.re - 2) * u)
      * Real.exp (-(Real.pi * Real.exp (-4 * u))))) ?_ hg
  filter_upwards [Filter.eventually_le_atBot 0] with u hu
  calc ‖(thetaM u : ℂ) * Complex.exp (a * (u : ℂ))‖
      = |thetaM u| * Real.exp (a.re * u) := by
        rw [norm_mul, show ‖(thetaM u : ℂ)‖ = |thetaM u| from RCLike.norm_ofReal _,
          Complex.norm_exp, hre u]
    _ ≤ (2 * thetaSConst * Real.exp (-2 * u)
        * Real.exp (-(Real.pi * Real.exp (-4 * u)))) * Real.exp (a.re * u) :=
        mul_le_mul_of_nonneg_right (abs_thetaM_le hu) (Real.exp_nonneg _)
    _ = 2 * thetaSConst * (Real.exp ((a.re - 2) * u)
        * Real.exp (-(Real.pi * Real.exp (-4 * u)))) := by
        have e1 : Real.exp ((a.re - 2) * u) = Real.exp (a.re * u) * Real.exp (-2 * u) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [e1]
        ring

/-- D4：`↑M'(u)·e^{au} → 0`（`u → −∞`）。 -/
theorem tendsto_thetaMD_cexp_atBot (a : ℂ) :
    Filter.Tendsto (fun u : ℝ => (thetaMD u : ℂ) * Complex.exp (a * (u : ℂ)))
      Filter.atBot (nhds 0) := by
  have hre : ∀ u : ℝ, (a * (u : ℂ)).re = a.re * u := fun u => by simp [Complex.mul_re]
  have hg : Filter.Tendsto (fun u : ℝ => 4 * thetaSConst * (Real.exp ((a.re - 2) * u)
        * Real.exp (-(Real.pi * Real.exp (-4 * u))))
      + 8 * Real.pi * thetaSD1Const * (Real.exp ((a.re - 6) * u)
        * Real.exp (-(Real.pi * Real.exp (-4 * u))))) Filter.atBot (nhds 0) := by
    have h1 := Filter.Tendsto.const_mul (4 * thetaSConst)
      (tendsto_exp_mul_exp_neg_atBot (a.re - 2))
    have h2 := Filter.Tendsto.const_mul (8 * Real.pi * thetaSD1Const)
      (tendsto_exp_mul_exp_neg_atBot (a.re - 6))
    rw [mul_zero] at h1 h2
    have h3 := h1.add h2
    rwa [add_zero] at h3
  refine squeeze_zero_norm' (f := fun u : ℝ => (thetaMD u : ℂ) * Complex.exp (a * (u : ℂ)))
    (a := fun u : ℝ => 4 * thetaSConst * (Real.exp ((a.re - 2) * u)
        * Real.exp (-(Real.pi * Real.exp (-4 * u))))
      + 8 * Real.pi * thetaSD1Const * (Real.exp ((a.re - 6) * u)
        * Real.exp (-(Real.pi * Real.exp (-4 * u))))) ?_ hg
  filter_upwards [Filter.eventually_le_atBot 0] with u hu
  calc ‖(thetaMD u : ℂ) * Complex.exp (a * (u : ℂ))‖
      = |thetaMD u| * Real.exp (a.re * u) := by
        rw [norm_mul, show ‖(thetaMD u : ℂ)‖ = |thetaMD u| from RCLike.norm_ofReal _,
          Complex.norm_exp, hre u]
    _ ≤ (4 * thetaSConst * Real.exp (-2 * u)
          * Real.exp (-(Real.pi * Real.exp (-4 * u)))
        + 8 * Real.pi * thetaSD1Const * Real.exp (-6 * u)
          * Real.exp (-(Real.pi * Real.exp (-4 * u)))) * Real.exp (a.re * u) :=
        mul_le_mul_of_nonneg_right (abs_thetaMD_le hu) (Real.exp_nonneg _)
    _ = 4 * thetaSConst * (Real.exp ((a.re - 2) * u)
          * Real.exp (-(Real.pi * Real.exp (-4 * u))))
        + 8 * Real.pi * thetaSD1Const * (Real.exp ((a.re - 6) * u)
          * Real.exp (-(Real.pi * Real.exp (-4 * u)))) := by
        have e2 : Real.exp ((a.re - 2) * u) = Real.exp (a.re * u) * Real.exp (-2 * u) := by
          rw [← Real.exp_add]; congr 1; ring
        have e6 : Real.exp ((a.re - 6) * u) = Real.exp (a.re * u) * Real.exp (-6 * u) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [e2, e6]
        ring

/-- I4：`e^{au}·↑M(u)` 在 `(−∞,0]` 可积。 -/
theorem integrableOn_cexp_thetaM (a : ℂ) :
    MeasureTheory.IntegrableOn (fun u : ℝ => Complex.exp (a * (u : ℂ)) * (thetaM u : ℂ))
      (Set.Iic 0) MeasureTheory.volume := by
  have hre : ∀ u : ℝ, (a * (u : ℂ)).re = a.re * u := fun u => by simp [Complex.mul_re]
  apply MeasureTheory.Integrable.mono'
    ((integrableOn_exp_mul_exp_neg_atBot (a.re - 2)).const_mul (2 * thetaSConst))
  · exact ((by fun_prop : Measurable (fun u : ℝ => Complex.exp (a * (u : ℂ)))).mul
      (Complex.measurable_ofReal.comp continuous_thetaM.measurable)).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Iic] with u hu
    have hu0 : u ≤ 0 := hu
    calc ‖Complex.exp (a * (u : ℂ)) * (thetaM u : ℂ)‖
        = Real.exp (a.re * u) * |thetaM u| := by
          rw [norm_mul, Complex.norm_exp, hre u,
            show ‖(thetaM u : ℂ)‖ = |thetaM u| from RCLike.norm_ofReal _]
      _ ≤ Real.exp (a.re * u) * (2 * thetaSConst * Real.exp (-2 * u)
          * Real.exp (-(Real.pi * Real.exp (-4 * u)))) :=
          mul_le_mul_of_nonneg_left (abs_thetaM_le hu0) (Real.exp_nonneg _)
      _ = 2 * thetaSConst * (Real.exp ((a.re - 2) * u)
          * Real.exp (-(Real.pi * Real.exp (-4 * u)))) := by
          have e1 : Real.exp ((a.re - 2) * u) = Real.exp (a.re * u) * Real.exp (-2 * u) := by
            rw [← Real.exp_add]; congr 1; ring
          rw [e1]
          ring

/-- I5：`e^{au}·↑M'(u)` 在 `(−∞,0]` 可积。 -/
theorem integrableOn_cexp_thetaMD (a : ℂ) :
    MeasureTheory.IntegrableOn (fun u : ℝ => Complex.exp (a * (u : ℂ)) * (thetaMD u : ℂ))
      (Set.Iic 0) MeasureTheory.volume := by
  have hre : ∀ u : ℝ, (a * (u : ℂ)).re = a.re * u := fun u => by simp [Complex.mul_re]
  apply MeasureTheory.Integrable.mono'
    (((integrableOn_exp_mul_exp_neg_atBot (a.re - 2)).const_mul (4 * thetaSConst)).add
      ((integrableOn_exp_mul_exp_neg_atBot (a.re - 6)).const_mul
        (8 * Real.pi * thetaSD1Const)))
  · exact ((by fun_prop : Measurable (fun u : ℝ => Complex.exp (a * (u : ℂ)))).mul
      (Complex.measurable_ofReal.comp continuous_thetaMD.measurable)).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Iic] with u hu
    have hu0 : u ≤ 0 := hu
    calc ‖Complex.exp (a * (u : ℂ)) * (thetaMD u : ℂ)‖
        = Real.exp (a.re * u) * |thetaMD u| := by
          rw [norm_mul, Complex.norm_exp, hre u,
            show ‖(thetaMD u : ℂ)‖ = |thetaMD u| from RCLike.norm_ofReal _]
      _ ≤ Real.exp (a.re * u) * (4 * thetaSConst * Real.exp (-2 * u)
            * Real.exp (-(Real.pi * Real.exp (-4 * u)))
          + 8 * Real.pi * thetaSD1Const * Real.exp (-6 * u)
            * Real.exp (-(Real.pi * Real.exp (-4 * u)))) :=
          mul_le_mul_of_nonneg_left (abs_thetaMD_le hu0) (Real.exp_nonneg _)
      _ = 4 * thetaSConst * (Real.exp ((a.re - 2) * u)
            * Real.exp (-(Real.pi * Real.exp (-4 * u))))
          + 8 * Real.pi * thetaSD1Const * (Real.exp ((a.re - 6) * u)
            * Real.exp (-(Real.pi * Real.exp (-4 * u)))) := by
          have e2 : Real.exp ((a.re - 2) * u) = Real.exp (a.re * u) * Real.exp (-2 * u) := by
            rw [← Real.exp_add]; congr 1; ring
          have e6 : Real.exp ((a.re - 6) * u) = Real.exp (a.re * u) * Real.exp (-6 * u) := by
            rw [← Real.exp_add]; congr 1; ring
          rw [e2, e6]
          ring

/-- I6：`e^{au}·↑M''(u)` 在 `(−∞,0]` 可积。 -/
theorem integrableOn_cexp_thetaMDD (a : ℂ) :
    MeasureTheory.IntegrableOn (fun u : ℝ => Complex.exp (a * (u : ℂ)) * (thetaMDD u : ℂ))
      (Set.Iic 0) MeasureTheory.volume := by
  have hre : ∀ u : ℝ, (a * (u : ℂ)).re = a.re * u := fun u => by simp [Complex.mul_re]
  apply MeasureTheory.Integrable.mono'
    ((((integrableOn_exp_mul_exp_neg_atBot (a.re - 2)).const_mul (8 * thetaSConst)).add
      ((integrableOn_exp_mul_exp_neg_atBot (a.re - 6)).const_mul
        (64 * Real.pi * thetaSD1Const))).add
      ((integrableOn_exp_mul_exp_neg_atBot (a.re - 10)).const_mul
        (32 * Real.pi ^ 2 * phiTailConst)))
  · exact ((by fun_prop : Measurable (fun u : ℝ => Complex.exp (a * (u : ℂ)))).mul
      (Complex.measurable_ofReal.comp measurable_thetaMDD)).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Iic] with u hu
    have hu0 : u ≤ 0 := hu
    calc ‖Complex.exp (a * (u : ℂ)) * (thetaMDD u : ℂ)‖
        = Real.exp (a.re * u) * |thetaMDD u| := by
          rw [norm_mul, Complex.norm_exp, hre u,
            show ‖(thetaMDD u : ℂ)‖ = |thetaMDD u| from RCLike.norm_ofReal _]
      _ ≤ Real.exp (a.re * u) * (8 * thetaSConst * Real.exp (-2 * u)
            * Real.exp (-(Real.pi * Real.exp (-4 * u)))
          + 64 * Real.pi * thetaSD1Const * Real.exp (-6 * u)
            * Real.exp (-(Real.pi * Real.exp (-4 * u)))
          + 32 * Real.pi ^ 2 * phiTailConst * Real.exp (-10 * u)
            * Real.exp (-(Real.pi * Real.exp (-4 * u)))) :=
          mul_le_mul_of_nonneg_left (abs_thetaMDD_le hu0) (Real.exp_nonneg _)
      _ = 8 * thetaSConst * (Real.exp ((a.re - 2) * u)
            * Real.exp (-(Real.pi * Real.exp (-4 * u))))
          + 64 * Real.pi * thetaSD1Const * (Real.exp ((a.re - 6) * u)
            * Real.exp (-(Real.pi * Real.exp (-4 * u))))
          + 32 * Real.pi ^ 2 * phiTailConst * (Real.exp ((a.re - 10) * u)
            * Real.exp (-(Real.pi * Real.exp (-4 * u)))) := by
          have e2 : Real.exp ((a.re - 2) * u) = Real.exp (a.re * u) * Real.exp (-2 * u) := by
            rw [← Real.exp_add]; congr 1; ring
          have e6 : Real.exp ((a.re - 6) * u) = Real.exp (a.re * u) * Real.exp (-6 * u) := by
            rw [← Real.exp_add]; congr 1; ring
          have e10 : Real.exp ((a.re - 10) * u)
              = Real.exp (a.re * u) * Real.exp (-10 * u) := by
            rw [← Real.exp_add]; congr 1; ring
          rw [e2, e6, e10]
          ring

/-!
### Phase 1d(v-1)：核心恒等式与四条半轴分部积分

`16Φ(u) = e^u(W''+2W')`，`M''+2M' = W''+2W'`（奇异项抵消）；
对 `F(u) = e^{au}·↑g(u)`（`g = W, NW, M, NM`）用半轴 FTC
`integral_Ioi/Iic_of_hasDerivAt_of_tendsto'` 得四条 IBP 方程，
边界项分别为 `−W(0), −NW(0), M(0), NM(0)`。
-/

/-- `16Φ(u) = e^u·(W''(u) + 2W'(u))`（`G` 结构恒等式的指数坐标形态）。 -/
theorem sixteen_phi_eq (u : ℝ) :
    16 * phi u = Real.exp u * (thetaWDD u + 2 * thetaWD u) := by
  rw [phi_eq_exp_mul_phiKernelG, phiKernelG_eq (Real.exp_pos (4 * u))]
  unfold thetaWDD thetaWD
  have e5 : Real.exp (5 * u) = Real.exp u * Real.exp (4 * u) := by
    rw [← Real.exp_add]; congr 1; ring
  have e8 : Real.exp (8 * u) = Real.exp (4 * u) * Real.exp (4 * u) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e5, e8]
  ring

/-- `e^{−2u}` 奇异项精确抵消：`M'' + 2M' = W'' + 2W'`。 -/
theorem thetaMDD_add_two_thetaMD_eq (u : ℝ) :
    thetaMDD u + 2 * thetaMD u = thetaWDD u + 2 * thetaWD u := by
  unfold thetaMDD thetaMD
  ring

/-- `NW := W' + 2W`（W 侧 IBP 原函数核）。 -/
noncomputable def thetaNW (u : ℝ) : ℝ := thetaWD u + 2 * thetaW u

/-- `NW' = W'' + 2W'`。 -/
noncomputable def thetaNWD (u : ℝ) : ℝ := thetaWDD u + 2 * thetaWD u

/-- `NM := M' + 2M`（M 侧 IBP 原函数核）。 -/
noncomputable def thetaNM (u : ℝ) : ℝ := thetaMD u + 2 * thetaM u

/-- `NM' = M'' + 2M'`。 -/
noncomputable def thetaNMD (u : ℝ) : ℝ := thetaMDD u + 2 * thetaMD u

theorem hasDerivAt_thetaNW (u : ℝ) : HasDerivAt thetaNW (thetaNWD u) u :=
  (hasDerivAt_thetaWD u).add ((hasDerivAt_thetaW u).const_mul 2)

theorem hasDerivAt_thetaNM (u : ℝ) : HasDerivAt thetaNM (thetaNMD u) u :=
  (hasDerivAt_thetaMD u).add ((hasDerivAt_thetaM u).const_mul 2)

/-- `u ↦ e^{au}·↑g(u)` 的导数（`g` 实值可导）。 -/
theorem hasDerivAt_cexp_mul_ofReal (a : ℂ) {g : ℝ → ℝ} {g' : ℝ} {u : ℝ}
    (hg : HasDerivAt g g' u) :
    HasDerivAt (fun u : ℝ => Complex.exp (a * (u : ℂ)) * (g u : ℂ))
      (Complex.exp (a * (u : ℂ)) * (a * (g u : ℂ) + (g' : ℂ))) u := by
  have h1 : HasDerivAt (fun u : ℝ => (u : ℂ)) ((1 : ℝ) : ℂ) u :=
    (hasDerivAt_id u).ofReal_comp
  have h2 : HasDerivAt (fun u : ℝ => a * (u : ℂ)) a u := by
    have h := h1.const_mul a
    rwa [Complex.ofReal_one, mul_one] at h
  have h := h2.cexp.mul hg.ofReal_comp
  rw [show Complex.exp (a * (u : ℂ)) * a * (g u : ℂ)
      + Complex.exp (a * (u : ℂ)) * (g' : ℂ)
      = Complex.exp (a * (u : ℂ)) * (a * (g u : ℂ) + (g' : ℂ)) from by ring] at h
  exact h

/-- W 侧一阶 IBP：`∫₀^∞ e^{au}(aW + W') = −W(0)`。 -/
theorem integral_Ioi_cexp_thetaW (a : ℂ) :
    ∫ u in Set.Ioi (0 : ℝ), Complex.exp (a * (u : ℂ))
        * (a * (thetaW u : ℂ) + (thetaWD u : ℂ))
      = -(thetaW 0 : ℂ) := by
  have hderiv : ∀ u ∈ Set.Ici (0 : ℝ), HasDerivAt
      (fun u : ℝ => Complex.exp (a * (u : ℂ)) * (thetaW u : ℂ))
      (Complex.exp (a * (u : ℂ)) * (a * (thetaW u : ℂ) + (thetaWD u : ℂ))) u :=
    fun u _ => hasDerivAt_cexp_mul_ofReal a (hasDerivAt_thetaW u)
  have hint : MeasureTheory.IntegrableOn
      (fun u : ℝ => Complex.exp (a * (u : ℂ)) * (a * (thetaW u : ℂ) + (thetaWD u : ℂ)))
      (Set.Ioi 0) MeasureTheory.volume := by
    refine (((integrableOn_cexp_thetaW a).const_mul a).add
      (integrableOn_cexp_thetaWD a)).congr ?_
    filter_upwards with u
    show a * (Complex.exp (a * (u : ℂ)) * (thetaW u : ℂ))
        + Complex.exp (a * (u : ℂ)) * (thetaWD u : ℂ)
      = Complex.exp (a * (u : ℂ)) * (a * (thetaW u : ℂ) + (thetaWD u : ℂ))
    ring
  have htend : Filter.Tendsto (fun u : ℝ => Complex.exp (a * (u : ℂ)) * (thetaW u : ℂ))
      Filter.atTop (nhds 0) :=
    (tendsto_thetaW_cexp_atTop a).congr (fun u => mul_comm _ _)
  have hIBP := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  rwa [show (0 : ℂ) - (Complex.exp (a * ((0 : ℝ) : ℂ)) * (thetaW 0 : ℂ)) = -(thetaW 0 : ℂ)
    from by simp] at hIBP

/-- W 侧二阶 IBP：`∫₀^∞ e^{au}(a·NW + NW') = −NW(0)`。 -/
theorem integral_Ioi_cexp_thetaNW (a : ℂ) :
    ∫ u in Set.Ioi (0 : ℝ), Complex.exp (a * (u : ℂ))
        * (a * (thetaNW u : ℂ) + (thetaNWD u : ℂ))
      = -(thetaNW 0 : ℂ) := by
  have hderiv : ∀ u ∈ Set.Ici (0 : ℝ), HasDerivAt
      (fun u : ℝ => Complex.exp (a * (u : ℂ)) * (thetaNW u : ℂ))
      (Complex.exp (a * (u : ℂ)) * (a * (thetaNW u : ℂ) + (thetaNWD u : ℂ))) u :=
    fun u _ => hasDerivAt_cexp_mul_ofReal a (hasDerivAt_thetaNW u)
  have hW : MeasureTheory.IntegrableOn
      (fun u : ℝ => Complex.exp (a * (u : ℂ)) * (thetaNW u : ℂ))
      (Set.Ioi 0) MeasureTheory.volume := by
    refine ((integrableOn_cexp_thetaWD a).add
      ((integrableOn_cexp_thetaW a).const_mul 2)).congr ?_
    filter_upwards with u
    show Complex.exp (a * (u : ℂ)) * (thetaWD u : ℂ)
        + 2 * (Complex.exp (a * (u : ℂ)) * (thetaW u : ℂ))
      = Complex.exp (a * (u : ℂ)) * (thetaNW u : ℂ)
    unfold thetaNW
    push_cast
    ring
  have hWD : MeasureTheory.IntegrableOn
      (fun u : ℝ => Complex.exp (a * (u : ℂ)) * (thetaNWD u : ℂ))
      (Set.Ioi 0) MeasureTheory.volume := by
    refine ((integrableOn_cexp_thetaWDD a).add
      ((integrableOn_cexp_thetaWD a).const_mul 2)).congr ?_
    filter_upwards with u
    show Complex.exp (a * (u : ℂ)) * (thetaWDD u : ℂ)
        + 2 * (Complex.exp (a * (u : ℂ)) * (thetaWD u : ℂ))
      = Complex.exp (a * (u : ℂ)) * (thetaNWD u : ℂ)
    unfold thetaNWD
    push_cast
    ring
  have hint : MeasureTheory.IntegrableOn
      (fun u : ℝ => Complex.exp (a * (u : ℂ)) * (a * (thetaNW u : ℂ) + (thetaNWD u : ℂ)))
      (Set.Ioi 0) MeasureTheory.volume := by
    refine ((hW.const_mul a).add hWD).congr ?_
    filter_upwards with u
    show a * (Complex.exp (a * (u : ℂ)) * (thetaNW u : ℂ))
        + Complex.exp (a * (u : ℂ)) * (thetaNWD u : ℂ)
      = Complex.exp (a * (u : ℂ)) * (a * (thetaNW u : ℂ) + (thetaNWD u : ℂ))
    ring
  have htend : Filter.Tendsto (fun u : ℝ => Complex.exp (a * (u : ℂ)) * (thetaNW u : ℂ))
      Filter.atTop (nhds 0) := by
    have h1 := (tendsto_thetaWD_cexp_atTop a).congr (fun u => mul_comm _ _)
    have h2 := Filter.Tendsto.const_mul (2 : ℂ)
      ((tendsto_thetaW_cexp_atTop a).congr (fun u => mul_comm _ _))
    rw [mul_zero] at h2
    have h3 := h1.add h2
    rw [add_zero] at h3
    refine h3.congr (fun u => ?_)
    show Complex.exp (a * (u : ℂ)) * (thetaWD u : ℂ)
        + 2 * (Complex.exp (a * (u : ℂ)) * (thetaW u : ℂ))
      = Complex.exp (a * (u : ℂ)) * (thetaNW u : ℂ)
    unfold thetaNW
    push_cast
    ring
  have hIBP := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  rwa [show (0 : ℂ) - (Complex.exp (a * ((0 : ℝ) : ℂ)) * (thetaNW 0 : ℂ)) = -(thetaNW 0 : ℂ)
    from by simp] at hIBP

/-- M 侧一阶 IBP：`∫₋∞⁰ e^{au}(aM + M') = M(0)`。 -/
theorem integral_Iic_cexp_thetaM (a : ℂ) :
    ∫ u in Set.Iic (0 : ℝ), Complex.exp (a * (u : ℂ))
        * (a * (thetaM u : ℂ) + (thetaMD u : ℂ))
      = (thetaM 0 : ℂ) := by
  have hderiv : ∀ u ∈ Set.Iic (0 : ℝ), HasDerivAt
      (fun u : ℝ => Complex.exp (a * (u : ℂ)) * (thetaM u : ℂ))
      (Complex.exp (a * (u : ℂ)) * (a * (thetaM u : ℂ) + (thetaMD u : ℂ))) u :=
    fun u _ => hasDerivAt_cexp_mul_ofReal a (hasDerivAt_thetaM u)
  have hint : MeasureTheory.IntegrableOn
      (fun u : ℝ => Complex.exp (a * (u : ℂ)) * (a * (thetaM u : ℂ) + (thetaMD u : ℂ)))
      (Set.Iic 0) MeasureTheory.volume := by
    refine (((integrableOn_cexp_thetaM a).const_mul a).add
      (integrableOn_cexp_thetaMD a)).congr ?_
    filter_upwards with u
    show a * (Complex.exp (a * (u : ℂ)) * (thetaM u : ℂ))
        + Complex.exp (a * (u : ℂ)) * (thetaMD u : ℂ)
      = Complex.exp (a * (u : ℂ)) * (a * (thetaM u : ℂ) + (thetaMD u : ℂ))
    ring
  have htend : Filter.Tendsto (fun u : ℝ => Complex.exp (a * (u : ℂ)) * (thetaM u : ℂ))
      Filter.atBot (nhds 0) :=
    (tendsto_thetaM_cexp_atBot a).congr (fun u => mul_comm _ _)
  have hIBP := MeasureTheory.integral_Iic_of_hasDerivAt_of_tendsto' hderiv hint htend
  rwa [show Complex.exp (a * ((0 : ℝ) : ℂ)) * (thetaM 0 : ℂ) - 0 = (thetaM 0 : ℂ)
    from by simp] at hIBP

/-- M 侧二阶 IBP：`∫₋∞⁰ e^{au}(a·NM + NM') = NM(0)`。 -/
theorem integral_Iic_cexp_thetaNM (a : ℂ) :
    ∫ u in Set.Iic (0 : ℝ), Complex.exp (a * (u : ℂ))
        * (a * (thetaNM u : ℂ) + (thetaNMD u : ℂ))
      = (thetaNM 0 : ℂ) := by
  have hderiv : ∀ u ∈ Set.Iic (0 : ℝ), HasDerivAt
      (fun u : ℝ => Complex.exp (a * (u : ℂ)) * (thetaNM u : ℂ))
      (Complex.exp (a * (u : ℂ)) * (a * (thetaNM u : ℂ) + (thetaNMD u : ℂ))) u :=
    fun u _ => hasDerivAt_cexp_mul_ofReal a (hasDerivAt_thetaNM u)
  have hM : MeasureTheory.IntegrableOn
      (fun u : ℝ => Complex.exp (a * (u : ℂ)) * (thetaNM u : ℂ))
      (Set.Iic 0) MeasureTheory.volume := by
    refine ((integrableOn_cexp_thetaMD a).add
      ((integrableOn_cexp_thetaM a).const_mul 2)).congr ?_
    filter_upwards with u
    show Complex.exp (a * (u : ℂ)) * (thetaMD u : ℂ)
        + 2 * (Complex.exp (a * (u : ℂ)) * (thetaM u : ℂ))
      = Complex.exp (a * (u : ℂ)) * (thetaNM u : ℂ)
    unfold thetaNM
    push_cast
    ring
  have hMD : MeasureTheory.IntegrableOn
      (fun u : ℝ => Complex.exp (a * (u : ℂ)) * (thetaNMD u : ℂ))
      (Set.Iic 0) MeasureTheory.volume := by
    refine ((integrableOn_cexp_thetaMDD a).add
      ((integrableOn_cexp_thetaMD a).const_mul 2)).congr ?_
    filter_upwards with u
    show Complex.exp (a * (u : ℂ)) * (thetaMDD u : ℂ)
        + 2 * (Complex.exp (a * (u : ℂ)) * (thetaMD u : ℂ))
      = Complex.exp (a * (u : ℂ)) * (thetaNMD u : ℂ)
    unfold thetaNMD
    push_cast
    ring
  have hint : MeasureTheory.IntegrableOn
      (fun u : ℝ => Complex.exp (a * (u : ℂ)) * (a * (thetaNM u : ℂ) + (thetaNMD u : ℂ)))
      (Set.Iic 0) MeasureTheory.volume := by
    refine ((hM.const_mul a).add hMD).congr ?_
    filter_upwards with u
    show a * (Complex.exp (a * (u : ℂ)) * (thetaNM u : ℂ))
        + Complex.exp (a * (u : ℂ)) * (thetaNMD u : ℂ)
      = Complex.exp (a * (u : ℂ)) * (a * (thetaNM u : ℂ) + (thetaNMD u : ℂ))
    ring
  have htend : Filter.Tendsto (fun u : ℝ => Complex.exp (a * (u : ℂ)) * (thetaNM u : ℂ))
      Filter.atBot (nhds 0) := by
    have h1 := (tendsto_thetaMD_cexp_atBot a).congr (fun u => mul_comm _ _)
    have h2 := Filter.Tendsto.const_mul (2 : ℂ)
      ((tendsto_thetaM_cexp_atBot a).congr (fun u => mul_comm _ _))
    rw [mul_zero] at h2
    have h3 := h1.add h2
    rw [add_zero] at h3
    refine h3.congr (fun u => ?_)
    show Complex.exp (a * (u : ℂ)) * (thetaMD u : ℂ)
        + 2 * (Complex.exp (a * (u : ℂ)) * (thetaM u : ℂ))
      = Complex.exp (a * (u : ℂ)) * (thetaNM u : ℂ)
    unfold thetaNM
    push_cast
    ring
  have hIBP := MeasureTheory.integral_Iic_of_hasDerivAt_of_tendsto' hderiv hint htend
  rwa [show Complex.exp (a * ((0 : ℝ) : ℂ)) * (thetaNM 0 : ℂ) - 0 = (thetaNM 0 : ℂ)
    from by simp] at hIBP

/-! ## Phase 1d(vi)：主恒等式组装 —— `H₀(z) = (1/8)·Ξ(z/2)` -/

/-- W 侧解出的二阶方程：`∫₀^∞ e^{au}·NW'(u) du = (a²−2a)·A − NW(0) + a·W(0)`，
其中 `A = ∫₀^∞ e^{au}·W(u) du`。由一阶/二阶两条 IBP 方程线性组合得到。 -/
theorem integral_Ioi_cexp_thetaNWD (a : ℂ) :
    ∫ u in Set.Ioi (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaNWD u : ℂ)
      = (a * a - 2 * a)
          * (∫ u in Set.Ioi (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaW u : ℂ))
        - (thetaNW 0 : ℂ) + a * (thetaW 0 : ℂ) := by
  have hNW : MeasureTheory.IntegrableOn
      (fun u : ℝ => Complex.exp (a * (u : ℂ)) * (thetaNW u : ℂ))
      (Set.Ioi 0) MeasureTheory.volume := by
    refine ((integrableOn_cexp_thetaWD a).add
      ((integrableOn_cexp_thetaW a).const_mul 2)).congr ?_
    filter_upwards with u
    show Complex.exp (a * (u : ℂ)) * (thetaWD u : ℂ)
        + 2 * (Complex.exp (a * (u : ℂ)) * (thetaW u : ℂ))
      = Complex.exp (a * (u : ℂ)) * (thetaNW u : ℂ)
    unfold thetaNW
    push_cast
    ring
  have hNWD : MeasureTheory.IntegrableOn
      (fun u : ℝ => Complex.exp (a * (u : ℂ)) * (thetaNWD u : ℂ))
      (Set.Ioi 0) MeasureTheory.volume := by
    refine ((integrableOn_cexp_thetaWDD a).add
      ((integrableOn_cexp_thetaWD a).const_mul 2)).congr ?_
    filter_upwards with u
    show Complex.exp (a * (u : ℂ)) * (thetaWDD u : ℂ)
        + 2 * (Complex.exp (a * (u : ℂ)) * (thetaWD u : ℂ))
      = Complex.exp (a * (u : ℂ)) * (thetaNWD u : ℂ)
    unfold thetaNWD
    push_cast
    ring
  have h1 : a * (∫ u in Set.Ioi (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaW u : ℂ))
        + (∫ u in Set.Ioi (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaWD u : ℂ))
      = -(thetaW 0 : ℂ) := by
    have e1 : a * (∫ u in Set.Ioi (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaW u : ℂ))
        = ∫ u in Set.Ioi (0 : ℝ), a * (Complex.exp (a * (u : ℂ)) * (thetaW u : ℂ)) :=
      (MeasureTheory.integral_const_mul a _).symm
    have e2 : (∫ u in Set.Ioi (0 : ℝ), a * (Complex.exp (a * (u : ℂ)) * (thetaW u : ℂ)))
          + (∫ u in Set.Ioi (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaWD u : ℂ))
        = ∫ u in Set.Ioi (0 : ℝ), (a * (Complex.exp (a * (u : ℂ)) * (thetaW u : ℂ))
            + Complex.exp (a * (u : ℂ)) * (thetaWD u : ℂ)) :=
      (MeasureTheory.integral_add ((integrableOn_cexp_thetaW a).const_mul a)
        (integrableOn_cexp_thetaWD a)).symm
    have e3 : (∫ u in Set.Ioi (0 : ℝ), (a * (Complex.exp (a * (u : ℂ)) * (thetaW u : ℂ))
            + Complex.exp (a * (u : ℂ)) * (thetaWD u : ℂ)))
        = ∫ u in Set.Ioi (0 : ℝ), Complex.exp (a * (u : ℂ))
            * (a * (thetaW u : ℂ) + (thetaWD u : ℂ)) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro u _
      show a * (Complex.exp (a * (u : ℂ)) * (thetaW u : ℂ))
          + Complex.exp (a * (u : ℂ)) * (thetaWD u : ℂ)
        = Complex.exp (a * (u : ℂ)) * (a * (thetaW u : ℂ) + (thetaWD u : ℂ))
      ring
    exact ((congrArg (· + _) e1).trans (e2.trans e3)).trans (integral_Ioi_cexp_thetaW a)
  have h2 : a * (∫ u in Set.Ioi (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaNW u : ℂ))
        + (∫ u in Set.Ioi (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaNWD u : ℂ))
      = -(thetaNW 0 : ℂ) := by
    have e1 : a * (∫ u in Set.Ioi (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaNW u : ℂ))
        = ∫ u in Set.Ioi (0 : ℝ), a * (Complex.exp (a * (u : ℂ)) * (thetaNW u : ℂ)) :=
      (MeasureTheory.integral_const_mul a _).symm
    have e2 : (∫ u in Set.Ioi (0 : ℝ), a * (Complex.exp (a * (u : ℂ)) * (thetaNW u : ℂ)))
          + (∫ u in Set.Ioi (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaNWD u : ℂ))
        = ∫ u in Set.Ioi (0 : ℝ), (a * (Complex.exp (a * (u : ℂ)) * (thetaNW u : ℂ))
            + Complex.exp (a * (u : ℂ)) * (thetaNWD u : ℂ)) :=
      (MeasureTheory.integral_add (hNW.const_mul a) hNWD).symm
    have e3 : (∫ u in Set.Ioi (0 : ℝ), (a * (Complex.exp (a * (u : ℂ)) * (thetaNW u : ℂ))
            + Complex.exp (a * (u : ℂ)) * (thetaNWD u : ℂ)))
        = ∫ u in Set.Ioi (0 : ℝ), Complex.exp (a * (u : ℂ))
            * (a * (thetaNW u : ℂ) + (thetaNWD u : ℂ)) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro u _
      show a * (Complex.exp (a * (u : ℂ)) * (thetaNW u : ℂ))
          + Complex.exp (a * (u : ℂ)) * (thetaNWD u : ℂ)
        = Complex.exp (a * (u : ℂ)) * (a * (thetaNW u : ℂ) + (thetaNWD u : ℂ))
      ring
    exact ((congrArg (· + _) e1).trans (e2.trans e3)).trans (integral_Ioi_cexp_thetaNW a)
  have hANW : (∫ u in Set.Ioi (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaWD u : ℂ))
        + 2 * (∫ u in Set.Ioi (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaW u : ℂ))
      = ∫ u in Set.Ioi (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaNW u : ℂ) := by
    have e1 : 2 * (∫ u in Set.Ioi (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaW u : ℂ))
        = ∫ u in Set.Ioi (0 : ℝ), 2 * (Complex.exp (a * (u : ℂ)) * (thetaW u : ℂ)) :=
      (MeasureTheory.integral_const_mul 2 _).symm
    have e2 : (∫ u in Set.Ioi (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaWD u : ℂ))
          + (∫ u in Set.Ioi (0 : ℝ), 2 * (Complex.exp (a * (u : ℂ)) * (thetaW u : ℂ)))
        = ∫ u in Set.Ioi (0 : ℝ), (Complex.exp (a * (u : ℂ)) * (thetaWD u : ℂ)
            + 2 * (Complex.exp (a * (u : ℂ)) * (thetaW u : ℂ))) :=
      (MeasureTheory.integral_add (integrableOn_cexp_thetaWD a)
        ((integrableOn_cexp_thetaW a).const_mul 2)).symm
    have e3 : (∫ u in Set.Ioi (0 : ℝ), (Complex.exp (a * (u : ℂ)) * (thetaWD u : ℂ)
            + 2 * (Complex.exp (a * (u : ℂ)) * (thetaW u : ℂ))))
        = ∫ u in Set.Ioi (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaNW u : ℂ) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro u _
      show Complex.exp (a * (u : ℂ)) * (thetaWD u : ℂ)
          + 2 * (Complex.exp (a * (u : ℂ)) * (thetaW u : ℂ))
        = Complex.exp (a * (u : ℂ)) * (thetaNW u : ℂ)
      unfold thetaNW
      push_cast
      ring
    exact (congrArg _ e1).trans (e2.trans e3)
  linear_combination h2 + a * hANW - a * h1

/-- M 侧解出的二阶方程：`∫₋∞⁰ e^{au}·NM'(u) du = (a²−2a)·B + NM(0) − a·M(0)`，
其中 `B = ∫₋∞⁰ e^{au}·M(u) du`；经 `NMD = NWD` 转到 W 侧核。 -/
theorem integral_Iic_cexp_thetaNWD (a : ℂ) :
    ∫ u in Set.Iic (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaNWD u : ℂ)
      = (a * a - 2 * a)
          * (∫ u in Set.Iic (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaM u : ℂ))
        + (thetaNM 0 : ℂ) - a * (thetaM 0 : ℂ) := by
  have hconv : (∫ u in Set.Iic (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaNWD u : ℂ))
      = ∫ u in Set.Iic (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaNMD u : ℂ) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Iic
    intro u _
    show Complex.exp (a * (u : ℂ)) * (thetaNWD u : ℂ)
      = Complex.exp (a * (u : ℂ)) * (thetaNMD u : ℂ)
    rw [show (thetaNWD u : ℂ) = (thetaNMD u : ℂ) from by
      exact_mod_cast (thetaMDD_add_two_thetaMD_eq u).symm]
  have hNM : MeasureTheory.IntegrableOn
      (fun u : ℝ => Complex.exp (a * (u : ℂ)) * (thetaNM u : ℂ))
      (Set.Iic 0) MeasureTheory.volume := by
    refine ((integrableOn_cexp_thetaMD a).add
      ((integrableOn_cexp_thetaM a).const_mul 2)).congr ?_
    filter_upwards with u
    show Complex.exp (a * (u : ℂ)) * (thetaMD u : ℂ)
        + 2 * (Complex.exp (a * (u : ℂ)) * (thetaM u : ℂ))
      = Complex.exp (a * (u : ℂ)) * (thetaNM u : ℂ)
    unfold thetaNM
    push_cast
    ring
  have hNMD : MeasureTheory.IntegrableOn
      (fun u : ℝ => Complex.exp (a * (u : ℂ)) * (thetaNMD u : ℂ))
      (Set.Iic 0) MeasureTheory.volume := by
    refine ((integrableOn_cexp_thetaMDD a).add
      ((integrableOn_cexp_thetaMD a).const_mul 2)).congr ?_
    filter_upwards with u
    show Complex.exp (a * (u : ℂ)) * (thetaMDD u : ℂ)
        + 2 * (Complex.exp (a * (u : ℂ)) * (thetaMD u : ℂ))
      = Complex.exp (a * (u : ℂ)) * (thetaNMD u : ℂ)
    unfold thetaNMD
    push_cast
    ring
  have h3 : a * (∫ u in Set.Iic (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaM u : ℂ))
        + (∫ u in Set.Iic (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaMD u : ℂ))
      = (thetaM 0 : ℂ) := by
    have e1 : a * (∫ u in Set.Iic (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaM u : ℂ))
        = ∫ u in Set.Iic (0 : ℝ), a * (Complex.exp (a * (u : ℂ)) * (thetaM u : ℂ)) :=
      (MeasureTheory.integral_const_mul a _).symm
    have e2 : (∫ u in Set.Iic (0 : ℝ), a * (Complex.exp (a * (u : ℂ)) * (thetaM u : ℂ)))
          + (∫ u in Set.Iic (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaMD u : ℂ))
        = ∫ u in Set.Iic (0 : ℝ), (a * (Complex.exp (a * (u : ℂ)) * (thetaM u : ℂ))
            + Complex.exp (a * (u : ℂ)) * (thetaMD u : ℂ)) :=
      (MeasureTheory.integral_add ((integrableOn_cexp_thetaM a).const_mul a)
        (integrableOn_cexp_thetaMD a)).symm
    have e3 : (∫ u in Set.Iic (0 : ℝ), (a * (Complex.exp (a * (u : ℂ)) * (thetaM u : ℂ))
            + Complex.exp (a * (u : ℂ)) * (thetaMD u : ℂ)))
        = ∫ u in Set.Iic (0 : ℝ), Complex.exp (a * (u : ℂ))
            * (a * (thetaM u : ℂ) + (thetaMD u : ℂ)) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Iic
      intro u _
      show a * (Complex.exp (a * (u : ℂ)) * (thetaM u : ℂ))
          + Complex.exp (a * (u : ℂ)) * (thetaMD u : ℂ)
        = Complex.exp (a * (u : ℂ)) * (a * (thetaM u : ℂ) + (thetaMD u : ℂ))
      ring
    exact ((congrArg (· + _) e1).trans (e2.trans e3)).trans (integral_Iic_cexp_thetaM a)
  have h4 : a * (∫ u in Set.Iic (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaNM u : ℂ))
        + (∫ u in Set.Iic (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaNMD u : ℂ))
      = (thetaNM 0 : ℂ) := by
    have e1 : a * (∫ u in Set.Iic (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaNM u : ℂ))
        = ∫ u in Set.Iic (0 : ℝ), a * (Complex.exp (a * (u : ℂ)) * (thetaNM u : ℂ)) :=
      (MeasureTheory.integral_const_mul a _).symm
    have e2 : (∫ u in Set.Iic (0 : ℝ), a * (Complex.exp (a * (u : ℂ)) * (thetaNM u : ℂ)))
          + (∫ u in Set.Iic (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaNMD u : ℂ))
        = ∫ u in Set.Iic (0 : ℝ), (a * (Complex.exp (a * (u : ℂ)) * (thetaNM u : ℂ))
            + Complex.exp (a * (u : ℂ)) * (thetaNMD u : ℂ)) :=
      (MeasureTheory.integral_add (hNM.const_mul a) hNMD).symm
    have e3 : (∫ u in Set.Iic (0 : ℝ), (a * (Complex.exp (a * (u : ℂ)) * (thetaNM u : ℂ))
            + Complex.exp (a * (u : ℂ)) * (thetaNMD u : ℂ)))
        = ∫ u in Set.Iic (0 : ℝ), Complex.exp (a * (u : ℂ))
            * (a * (thetaNM u : ℂ) + (thetaNMD u : ℂ)) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Iic
      intro u _
      show a * (Complex.exp (a * (u : ℂ)) * (thetaNM u : ℂ))
          + Complex.exp (a * (u : ℂ)) * (thetaNMD u : ℂ)
        = Complex.exp (a * (u : ℂ)) * (a * (thetaNM u : ℂ) + (thetaNMD u : ℂ))
      ring
    exact ((congrArg (· + _) e1).trans (e2.trans e3)).trans (integral_Iic_cexp_thetaNM a)
  have hBNM : (∫ u in Set.Iic (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaMD u : ℂ))
        + 2 * (∫ u in Set.Iic (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaM u : ℂ))
      = ∫ u in Set.Iic (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaNM u : ℂ) := by
    have e1 : 2 * (∫ u in Set.Iic (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaM u : ℂ))
        = ∫ u in Set.Iic (0 : ℝ), 2 * (Complex.exp (a * (u : ℂ)) * (thetaM u : ℂ)) :=
      (MeasureTheory.integral_const_mul 2 _).symm
    have e2 : (∫ u in Set.Iic (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaMD u : ℂ))
          + (∫ u in Set.Iic (0 : ℝ), 2 * (Complex.exp (a * (u : ℂ)) * (thetaM u : ℂ)))
        = ∫ u in Set.Iic (0 : ℝ), (Complex.exp (a * (u : ℂ)) * (thetaMD u : ℂ)
            + 2 * (Complex.exp (a * (u : ℂ)) * (thetaM u : ℂ))) :=
      (MeasureTheory.integral_add (integrableOn_cexp_thetaMD a)
        ((integrableOn_cexp_thetaM a).const_mul 2)).symm
    have e3 : (∫ u in Set.Iic (0 : ℝ), (Complex.exp (a * (u : ℂ)) * (thetaMD u : ℂ)
            + 2 * (Complex.exp (a * (u : ℂ)) * (thetaM u : ℂ))))
        = ∫ u in Set.Iic (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaNM u : ℂ) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Iic
      intro u _
      show Complex.exp (a * (u : ℂ)) * (thetaMD u : ℂ)
          + 2 * (Complex.exp (a * (u : ℂ)) * (thetaM u : ℂ))
        = Complex.exp (a * (u : ℂ)) * (thetaNM u : ℂ)
      unfold thetaNM
      push_cast
      ring
    exact (congrArg _ e1).trans (e2.trans e3)
  have hsolve : (∫ u in Set.Iic (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaNMD u : ℂ))
      = (a * a - 2 * a)
          * (∫ u in Set.Iic (0 : ℝ), Complex.exp (a * (u : ℂ)) * (thetaM u : ℂ))
        + (thetaNM 0 : ℂ) - a * (thetaM 0 : ℂ) := by
    linear_combination h4 + a * hBNM - a * h3
  exact hconv.trans hsolve

/-- 被积函数转换：`e^{au}·NW'(u) = 16·e^{(a−1)u}·Φ(u)`（`sixteen_phi_eq` 的复形式）。 -/
theorem cexp_mul_thetaNWD_eq (a : ℂ) (u : ℝ) :
    Complex.exp (a * (u : ℂ)) * (thetaNWD u : ℂ)
      = 16 * (Complex.exp ((a - 1) * (u : ℂ)) * (phi u : ℂ)) := by
  have h16 : 16 * phi u = Real.exp u * thetaNWD u := sixteen_phi_eq u
  have h16c : (16 : ℂ) * (phi u : ℂ) = (Real.exp u : ℂ) * (thetaNWD u : ℂ) := by
    exact_mod_cast h16
  have hre : (Real.exp u : ℂ) = Complex.exp (u : ℂ) := Complex.ofReal_exp u
  have hN : (thetaNWD u : ℂ) = 16 * (phi u : ℂ) * Complex.exp (-(u : ℂ)) := by
    calc (thetaNWD u : ℂ)
        = Complex.exp (u : ℂ) * (thetaNWD u : ℂ) * Complex.exp (-(u : ℂ)) := by
          have hrw : Complex.exp (u : ℂ) * (thetaNWD u : ℂ) * Complex.exp (-(u : ℂ))
            = (Complex.exp (u : ℂ) * Complex.exp (-(u : ℂ))) * (thetaNWD u : ℂ) := by ring
          rw [hrw, ← Complex.exp_add, show (u : ℂ) + -(u : ℂ) = 0 from by ring,
            Complex.exp_zero, one_mul]
      _ = 16 * (phi u : ℂ) * Complex.exp (-(u : ℂ)) := by
          rw [← show (16 : ℂ) * (phi u : ℂ) = Complex.exp (u : ℂ) * (thetaNWD u : ℂ) from by
            rw [← hre]; exact h16c]
  rw [hN, show (a - 1) * (u : ℂ) = a * (u : ℂ) + -(u : ℂ) from by ring, Complex.exp_add]
  ring

/-- 主恒等式（指数形式）：`16·(∫₀^∞ + ∫₋∞⁰) e^{izu}Φ(u) du
= 2 − ((1+z²)/2)·Λ₀((1+iz)/2)`。由两侧二阶方程、边界相消与
`completedRiemannZeta₀` 的积分表示组装。 -/
theorem sixteen_integral_cexp_phi_eq (z : ℂ) :
    16 * ((∫ u in Set.Ioi (0 : ℝ), Complex.exp (Complex.I * z * (u : ℂ)) * (phi u : ℂ))
        + (∫ u in Set.Iic (0 : ℝ), Complex.exp (Complex.I * z * (u : ℂ)) * (phi u : ℂ)))
      = 2 - ((1 + z * z) / 2) * completedRiemannZeta₀ ((1 + Complex.I * z) / 2) := by
  have hc : (1 + Complex.I * z) * (1 + Complex.I * z) - 2 * (1 + Complex.I * z)
      = -(1 + z * z) := by
    have hII : Complex.I * z * (Complex.I * z) = -(z * z) := by
      calc Complex.I * z * (Complex.I * z)
          = Complex.I * Complex.I * (z * z) := by ring
        _ = -(z * z) := by rw [Complex.I_mul_I]; ring
    linear_combination hII
  have hconvW : (∫ u in Set.Ioi (0 : ℝ), Complex.exp ((1 + Complex.I * z) * (u : ℂ))
        * (thetaNWD u : ℂ))
      = 16 * (∫ u in Set.Ioi (0 : ℝ), Complex.exp (Complex.I * z * (u : ℂ)) * (phi u : ℂ)) := by
    have e1 : (∫ u in Set.Ioi (0 : ℝ), Complex.exp ((1 + Complex.I * z) * (u : ℂ))
          * (thetaNWD u : ℂ))
        = ∫ u in Set.Ioi (0 : ℝ), 16 * (Complex.exp (Complex.I * z * (u : ℂ)) * (phi u : ℂ)) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro u _
      show Complex.exp ((1 + Complex.I * z) * (u : ℂ)) * (thetaNWD u : ℂ)
        = 16 * (Complex.exp (Complex.I * z * (u : ℂ)) * (phi u : ℂ))
      rw [cexp_mul_thetaNWD_eq (1 + Complex.I * z) u,
        show (1 + Complex.I * z) - 1 = Complex.I * z from by ring]
    exact e1.trans (MeasureTheory.integral_const_mul 16 _)
  have hconvM : (∫ u in Set.Iic (0 : ℝ), Complex.exp ((1 + Complex.I * z) * (u : ℂ))
        * (thetaNWD u : ℂ))
      = 16 * (∫ u in Set.Iic (0 : ℝ), Complex.exp (Complex.I * z * (u : ℂ)) * (phi u : ℂ)) := by
    have e1 : (∫ u in Set.Iic (0 : ℝ), Complex.exp ((1 + Complex.I * z) * (u : ℂ))
          * (thetaNWD u : ℂ))
        = ∫ u in Set.Iic (0 : ℝ), 16 * (Complex.exp (Complex.I * z * (u : ℂ)) * (phi u : ℂ)) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Iic
      intro u _
      show Complex.exp ((1 + Complex.I * z) * (u : ℂ)) * (thetaNWD u : ℂ)
        = 16 * (Complex.exp (Complex.I * z * (u : ℂ)) * (phi u : ℂ))
      rw [cexp_mul_thetaNWD_eq (1 + Complex.I * z) u,
        show (1 + Complex.I * z) - 1 = Complex.I * z from by ring]
    exact e1.trans (MeasureTheory.integral_const_mul 16 _)
  have hW : 16 * (∫ u in Set.Ioi (0 : ℝ), Complex.exp (Complex.I * z * (u : ℂ)) * (phi u : ℂ))
      = -(1 + z * z)
          * (∫ u in Set.Ioi (0 : ℝ), Complex.exp ((1 + Complex.I * z) * (u : ℂ))
              * (thetaW u : ℂ))
        - (thetaNW 0 : ℂ) + (1 + Complex.I * z) * (thetaW 0 : ℂ) := by
    have h1 := integral_Ioi_cexp_thetaNWD (1 + Complex.I * z)
    linear_combination hconvW.symm + h1
      + (∫ u in Set.Ioi (0 : ℝ), Complex.exp ((1 + Complex.I * z) * (u : ℂ)) * (thetaW u : ℂ)) * hc
  have hM : 16 * (∫ u in Set.Iic (0 : ℝ), Complex.exp (Complex.I * z * (u : ℂ)) * (phi u : ℂ))
      = -(1 + z * z)
          * (∫ u in Set.Iic (0 : ℝ), Complex.exp ((1 + Complex.I * z) * (u : ℂ))
              * (thetaM u : ℂ))
        + (thetaNM 0 : ℂ) - (1 + Complex.I * z) * (thetaM 0 : ℂ) := by
    have h1 := integral_Iic_cexp_thetaNWD (1 + Complex.I * z)
    linear_combination hconvM.symm + h1
      + (∫ u in Set.Iic (0 : ℝ), Complex.exp ((1 + Complex.I * z) * (u : ℂ)) * (thetaM u : ℂ)) * hc
  have hb : (-(thetaNW 0 : ℂ) + (1 + Complex.I * z) * (thetaW 0 : ℂ))
      + ((thetaNM 0 : ℂ) - (1 + Complex.I * z) * (thetaM 0 : ℂ)) = 2 := by
    have hW0 : thetaW 0 = thetaM 0 := by
      show thetaT (Real.exp (4 * 0)) - 1 = thetaT (Real.exp (4 * 0)) - Real.exp (-2 * 0)
      rw [show (-2 : ℝ) * 0 = 0 from by ring, Real.exp_zero]
    have hMD0 : thetaMD 0 = thetaWD 0 + 2 := by
      show thetaWD 0 + 2 * Real.exp (-2 * 0) = thetaWD 0 + 2
      rw [show (-2 : ℝ) * 0 = 0 from by ring, Real.exp_zero, mul_one]
    have h1 : (thetaNW 0 : ℂ) = (thetaWD 0 : ℂ) + 2 * (thetaW 0 : ℂ) := by
      unfold thetaNW
      push_cast
      ring
    have h2 : (thetaNM 0 : ℂ) = (thetaWD 0 : ℂ) + 2 + 2 * (thetaM 0 : ℂ) := by
      unfold thetaNM
      rw [hMD0]
      push_cast
      ring
    have h3 : (thetaW 0 : ℂ) = (thetaM 0 : ℂ) := by exact_mod_cast hW0
    rw [h1, h2, h3]
    ring
  have hAB : 2 * ((∫ u in Set.Ioi (0 : ℝ), Complex.exp ((1 + Complex.I * z) * (u : ℂ))
          * (thetaW u : ℂ))
        + (∫ u in Set.Iic (0 : ℝ), Complex.exp ((1 + Complex.I * z) * (u : ℂ))
          * (thetaM u : ℂ)))
      = completedRiemannZeta₀ ((1 + Complex.I * z) / 2) := by
    rw [completedRiemannZeta₀_eq_integral_split]
    congr 1
    congr 1
    · apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro u _
      show Complex.exp ((1 + Complex.I * z) * (u : ℂ)) * (thetaW u : ℂ)
        = Complex.exp (2 * ((1 + Complex.I * z) / 2) * (u : ℂ)) * (thetaW u : ℂ)
      rw [show 2 * ((1 + Complex.I * z) / 2) * (u : ℂ) = (1 + Complex.I * z) * (u : ℂ) from by
        ring]
    · apply MeasureTheory.setIntegral_congr_fun measurableSet_Iic
      intro u _
      show Complex.exp ((1 + Complex.I * z) * (u : ℂ)) * (thetaM u : ℂ)
        = Complex.exp (2 * ((1 + Complex.I * z) / 2) * (u : ℂ)) * (thetaM u : ℂ)
      rw [show 2 * ((1 + Complex.I * z) / 2) * (u : ℂ) = (1 + Complex.I * z) * (u : ℂ) from by
        ring]
  linear_combination hW + hM + hb - ((1 + z * z) / 2) * hAB

/-- `u ↦ e^{wu}·Φ(u)` 在 `(0, ∞)` 上可积（任意 `w : ℂ`，双指数衰减吸收线性指数）。 -/
theorem integrableOn_cexp_mul_phi (w : ℂ) :
    MeasureTheory.IntegrableOn (fun u : ℝ => Complex.exp (w * (u : ℂ)) * (phi u : ℂ))
      (Set.Ioi 0) MeasureTheory.volume := by
  have hcont : Continuous (fun u : ℝ => Complex.exp (w * (u : ℂ)) * (phi u : ℂ)) :=
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
      (Complex.continuous_ofReal.comp continuous_phi)
  apply MeasureTheory.Integrable.mono' (integrableOn_heatDominatingFun 0 |w.re| (abs_nonneg _))
  · exact hcont.continuousOn.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := le_of_lt hu
    have h1 : ‖Complex.exp (w * (u : ℂ)) * (phi u : ℂ)‖
        = Real.exp ((w * (u : ℂ)).re) * |phi u| := by
      rw [norm_mul, Complex.norm_exp,
        show ‖(phi u : ℂ)‖ = |phi u| from RCLike.norm_ofReal _]
    rw [h1]
    have hre_eq : (w * (u : ℂ)).re = w.re * u := by simp [Complex.mul_re]
    have hre : (w * (u : ℂ)).re ≤ |w.re| * u := by
      rw [hre_eq]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) hu0
    calc Real.exp ((w * (u : ℂ)).re) * |phi u|
        ≤ Real.exp (|w.re| * u) * ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
            * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))) :=
          mul_le_mul (Real.exp_le_exp.mpr hre) (abs_phi_le u hu0) (abs_nonneg _)
            (Real.exp_nonneg _)
      _ = heatDominatingFun 0 |w.re| u := by
          have e1 : Real.exp (|w.re| * u)
              * ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
                * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u))))
            = (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
              * (Real.exp (|w.re| * u) * Real.exp (9 * u))
              * Real.exp (-(Real.pi * Real.exp (4 * u))) := by ring
          rw [e1, ← Real.exp_add,
            show |w.re| * u + 9 * u = 0 * u ^ 2 + (9 + |w.re|) * u from by ring]
          rfl

/-- parity 换元：`∫₋∞⁰ e^{izu}Φ = ∫₀^∞ e^{−izu}Φ`（`Φ` 偶 + 负号替换）。 -/
theorem integral_Iic_cexp_iz_phi (z : ℂ) :
    (∫ u in Set.Iic (0 : ℝ), Complex.exp (Complex.I * z * (u : ℂ)) * (phi u : ℂ))
      = ∫ u in Set.Ioi (0 : ℝ), Complex.exp ((-(Complex.I * z)) * (u : ℂ)) * (phi u : ℂ) := by
  have h := integral_comp_neg_Iic (0 : ℝ)
    (fun u : ℝ => Complex.exp ((-(Complex.I * z)) * (u : ℂ)) * (phi u : ℂ))
  rw [neg_zero] at h
  have hcongr : (∫ u in Set.Iic (0 : ℝ), Complex.exp (Complex.I * z * (u : ℂ)) * (phi u : ℂ))
      = ∫ u in Set.Iic (0 : ℝ), Complex.exp ((-(Complex.I * z)) * ((-u : ℝ) : ℂ))
          * (phi (-u) : ℂ) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Iic
    intro u _
    show Complex.exp (Complex.I * z * (u : ℂ)) * (phi u : ℂ)
      = Complex.exp ((-(Complex.I * z)) * ((-u : ℝ) : ℂ)) * (phi (-u) : ℂ)
    rw [phi_even u, Complex.ofReal_neg,
      show (-(Complex.I * z)) * -(u : ℂ) = Complex.I * z * (u : ℂ) from by ring]
  exact hcongr.trans h

/-- `H₀(z)` 的被积函数在 `t = 0` 时化简为 `Φ(u)·cos(zu)`。 -/
theorem deBruijnNewmanH_zero_eq_integral (z : ℂ) :
    deBruijnNewmanH 0 z
      = ∫ u in Set.Ioi (0 : ℝ), (phi u : ℂ) * Complex.cos (z * (u : ℂ)) := by
  show (∫ u in Set.Ioi (0 : ℝ), heatIntegrand 0 z u)
    = ∫ u in Set.Ioi (0 : ℝ), (phi u : ℂ) * Complex.cos (z * (u : ℂ))
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro u _
  show heatIntegrand 0 z u = (phi u : ℂ) * Complex.cos (z * (u : ℂ))
  unfold heatIntegrand
  rw [show (0 : ℝ) * u ^ 2 = 0 from by ring, Real.exp_zero, one_mul]

/-- **Phase 1d 收官恒等式**：`H₀(z) = (1/8)·Ξ(z/2)`，即
`deBruijnNewmanH 0 z = (1/8)·completedZeta (1/2 + I·(z/2))`。
由主恒等式（`sixteen_integral_cexp_phi_eq`）、parity 换元
（`integral_Iic_cexp_iz_phi`）与 `cos` 的指数表示组装。 -/
theorem deBruijnNewmanH_zero_eq_completedZeta (z : ℂ) :
    deBruijnNewmanH 0 z
      = (1 / 8) * RiemannHypothesis.completedZeta (1 / 2 + Complex.I * (z / 2)) := by
  have hmaster := sixteen_integral_cexp_phi_eq z
  have hpar := integral_Iic_cexp_iz_phi z
  have hH := deBruijnNewmanH_zero_eq_integral z
  have hsum : (∫ u in Set.Ioi (0 : ℝ), Complex.exp (Complex.I * z * (u : ℂ)) * (phi u : ℂ))
        + (∫ u in Set.Ioi (0 : ℝ), Complex.exp ((-(Complex.I * z)) * (u : ℂ)) * (phi u : ℂ))
      = 2 * (∫ u in Set.Ioi (0 : ℝ), (phi u : ℂ) * Complex.cos (z * (u : ℂ))) := by
    have e1 : (∫ u in Set.Ioi (0 : ℝ), Complex.exp (Complex.I * z * (u : ℂ)) * (phi u : ℂ))
          + (∫ u in Set.Ioi (0 : ℝ), Complex.exp ((-(Complex.I * z)) * (u : ℂ)) * (phi u : ℂ))
        = ∫ u in Set.Ioi (0 : ℝ), (Complex.exp (Complex.I * z * (u : ℂ)) * (phi u : ℂ)
            + Complex.exp ((-(Complex.I * z)) * (u : ℂ)) * (phi u : ℂ)) :=
      (MeasureTheory.integral_add (integrableOn_cexp_mul_phi (Complex.I * z))
        (integrableOn_cexp_mul_phi (-(Complex.I * z)))).symm
    have e2 : (∫ u in Set.Ioi (0 : ℝ), (Complex.exp (Complex.I * z * (u : ℂ)) * (phi u : ℂ)
            + Complex.exp ((-(Complex.I * z)) * (u : ℂ)) * (phi u : ℂ)))
        = ∫ u in Set.Ioi (0 : ℝ), 2 * ((phi u : ℂ) * Complex.cos (z * (u : ℂ))) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro u _
      have h2c : 2 * Complex.cos (z * (u : ℂ))
          = Complex.exp (Complex.I * z * (u : ℂ))
            + Complex.exp ((-(Complex.I * z)) * (u : ℂ)) := by
        unfold Complex.cos
        rw [show -(z * (u : ℂ)) * Complex.I = (-(Complex.I * z)) * (u : ℂ) from by ring,
          show z * (u : ℂ) * Complex.I = Complex.I * z * (u : ℂ) from by ring]
        ring
      show Complex.exp (Complex.I * z * (u : ℂ)) * (phi u : ℂ)
          + Complex.exp ((-(Complex.I * z)) * (u : ℂ)) * (phi u : ℂ)
        = 2 * ((phi u : ℂ) * Complex.cos (z * (u : ℂ)))
      calc Complex.exp (Complex.I * z * (u : ℂ)) * (phi u : ℂ)
            + Complex.exp ((-(Complex.I * z)) * (u : ℂ)) * (phi u : ℂ)
          = (phi u : ℂ) * (Complex.exp (Complex.I * z * (u : ℂ))
              + Complex.exp ((-(Complex.I * z)) * (u : ℂ))) := by ring
        _ = (phi u : ℂ) * (2 * Complex.cos (z * (u : ℂ))) := by rw [← h2c]
        _ = 2 * ((phi u : ℂ) * Complex.cos (z * (u : ℂ))) := by ring
    have e3 : (∫ u in Set.Ioi (0 : ℝ), 2 * ((phi u : ℂ) * Complex.cos (z * (u : ℂ))))
        = 2 * (∫ u in Set.Ioi (0 : ℝ), (phi u : ℂ) * Complex.cos (z * (u : ℂ))) :=
      MeasureTheory.integral_const_mul 2 _
    exact e1.trans (e2.trans e3)
  have hXi : (1 / 8) * RiemannHypothesis.completedZeta (1 / 2 + Complex.I * (z / 2))
      = 1 / 16 - ((1 + z * z) / 64) * completedRiemannZeta₀ ((1 + Complex.I * z) / 2) := by
    have hss : ((1 + Complex.I * z) / 2) * (((1 + Complex.I * z) / 2) - 1)
        = -(1 + z * z) / 4 := by
      have hII : Complex.I * z * (Complex.I * z) = -(z * z) := by
        calc Complex.I * z * (Complex.I * z)
            = Complex.I * Complex.I * (z * z) := by ring
          _ = -(z * z) := by rw [Complex.I_mul_I]; ring
      linear_combination hII / 4
    have hdef : RiemannHypothesis.completedZeta (1 / 2 + Complex.I * (z / 2))
        = (1 / 2) * ((1 + Complex.I * z) / 2) * (((1 + Complex.I * z) / 2) - 1)
            * completedRiemannZeta₀ ((1 + Complex.I * z) / 2)
          - (1 / 2) * (((1 + Complex.I * z) / 2) - 1)
          + (1 / 2) * ((1 + Complex.I * z) / 2) := by
      have hs : (1 / 2 : ℂ) + Complex.I * (z / 2) = (1 + Complex.I * z) / 2 := by ring
      unfold RiemannHypothesis.completedZeta
      rw [hs]
    rw [hdef]
    linear_combination (completedRiemannZeta₀ ((1 + Complex.I * z) / 2) / 16) * hss
  linear_combination hH + (1 / 32) * hmaster - (1 / 2) * hsum - (1 / 2) * hpar - hXi

/-- **Phase 2 桥接引理**：`H₀` 的零点与 `ξ` 的零点一一对应：
`H₀(z) = 0 ↔ ξ(1/2 + I·(z/2)) = 0`（`1/8 ≠ 0` 的直接推论）。
`z = x ∈ ℝ` 时 `1/2 + I·(x/2)` 落在临界线 `Re = 1/2` 上，
故 `H₀` 的实零点对应临界线上的 `ξ` 零点。 -/
theorem deBruijnNewmanH_zero_eq_zero_iff (z : ℂ) :
    deBruijnNewmanH 0 z = 0
      ↔ RiemannHypothesis.completedZeta (1 / 2 + Complex.I * (z / 2)) = 0 := by
  rw [deBruijnNewmanH_zero_eq_completedZeta z]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  · intro h
    rw [h, mul_zero]

/-! ## Phase 2：`AllZerosReal` / `Λ` 的第一批推论（定义见 1713–1721 行） -/

/-- `t = 0` 切片的零点对应（桥接引理的谓词形式）。 -/
theorem allZerosReal_zero_iff_forall_completedZeta :
    AllZerosReal 0 ↔ ∀ z : ℂ,
      RiemannHypothesis.completedZeta (1 / 2 + Complex.I * (z / 2)) = 0 → z.im = 0 :=
  forall_congr' fun z => imp_congr (deBruijnNewmanH_zero_eq_zero_iff z) Iff.rfl

/-- `ξ` 的乘积形式：`completedZeta s = (1/2)·s·(s−1)·Λ(s)`（`s ∉ {0, 1}`）。 -/
theorem completedZeta_eq_of_ne_zero_ne_one (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    RiemannHypothesis.completedZeta s = (1 / 2) * s * (s - 1) * completedRiemannZeta s := by
  have hs1 : (1 - s) ≠ 0 := sub_ne_zero.mpr h1.symm
  unfold RiemannHypothesis.completedZeta
  rw [completedRiemannZeta_eq s]
  field_simp [h0, hs1]
  ring

/-- **`ξ` 零点 ⇔ `ζ` 非平凡零点**：`completedZeta s = 0 ↔ IsNontrivialZero s`。
正向用 `Re ≥ 1` 非零区（`riemannZeta_ne_zero_of_one_le_re`）+ 函数方程排除
`Re ≤ 0`；反向由 `ζ = Λ / Gammaℝ` 与 `Gammaℝ ≠ 0`（`Re s > 0`）得到。 -/
theorem completedZeta_eq_zero_iff (s : ℂ) :
    RiemannHypothesis.completedZeta s = 0 ↔ RiemannHypothesis.IsNontrivialZero s := by
  constructor
  · intro h
    have h0 : s ≠ 0 := by
      intro hs0
      rw [hs0] at h
      unfold RiemannHypothesis.completedZeta at h
      norm_num at h
    have h1 : s ≠ 1 := by
      intro hs1
      rw [hs1] at h
      unfold RiemannHypothesis.completedZeta at h
      norm_num at h
    have hΛ : completedRiemannZeta s = 0 := by
      have h2 := h
      rw [completedZeta_eq_of_ne_zero_ne_one s h0 h1] at h2
      have hne : (1 / 2 : ℂ) * s * (s - 1) ≠ 0 := by
        simp only [ne_eq, mul_ne_zero_iff]
        exact ⟨⟨(by norm_num), h0⟩, sub_ne_zero.mpr h1⟩
      exact (mul_eq_zero.mp h2).resolve_left hne
    have hζ : riemannZeta s = 0 := by
      have h := riemannZeta_def_of_ne_zero h0
      rw [hΛ, zero_div] at h
      exact h
    have hre_pos : 0 < s.re := by
      by_contra hle
      push_neg at hle
      have hre1 : 1 ≤ (1 - s).re := by
        rw [Complex.sub_re, Complex.one_re]
        linarith
      have hne1 : (1 - s) ≠ 0 := fun hh => h1 (sub_eq_zero.mp hh).symm
      have hne2 : (1 - s) ≠ 1 := fun hh => h0 (sub_eq_self.mp hh)
      have hΛ1 : completedRiemannZeta (1 - s) ≠ 0 := by
        have hζ1 : riemannZeta (1 - s) ≠ 0 := riemannZeta_ne_zero_of_one_le_re hre1
        have h3 := riemannZeta_def_of_ne_zero hne1
        exact fun hh => hζ1 (by rw [h3, hh, zero_div])
      have hFE := RiemannHypothesis.functional_equation s
      rw [h, completedZeta_eq_of_ne_zero_ne_one (1 - s) hne1 hne2] at hFE
      have hne12 : (1 / 2 : ℂ) * (1 - s) * ((1 - s) - 1) ≠ 0 := by
        simp only [ne_eq, mul_ne_zero_iff]
        exact ⟨⟨(by norm_num), hne1⟩, by
          rw [show (1 : ℂ) - s - 1 = -s from by ring]
          exact neg_ne_zero.mpr h0⟩
      rcases mul_eq_zero.mp hFE.symm with hh | hh
      · exact hne12 hh
      · exact hΛ1 hh
    have hre_lt : s.re < 1 := by
      by_contra hle
      push_neg at hle
      exact riemannZeta_ne_zero_of_one_le_re hle hζ
    exact ⟨hζ, hre_pos, hre_lt⟩
  · rintro ⟨hζ, hpos, hlt⟩
    have h0 : s ≠ 0 := by
      intro hh
      rw [hh] at hpos
      simp at hpos
    have h1 : s ≠ 1 := by
      intro hh
      rw [hh] at hlt
      simp at hlt
    have hΛ : completedRiemannZeta s = 0 := by
      have hΓ : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hpos
      have h := riemannZeta_def_of_ne_zero h0
      rw [hζ] at h
      rcases div_eq_zero_iff.mp h.symm with hh | hh
      · exact hh
      · exact absurd hh hΓ
    rw [completedZeta_eq_of_ne_zero_ne_one s h0 h1, hΛ, mul_zero]

/-- **Phase 2 核心桥（`t = 0` 切片）**：黎曼猜想 ⇔ `H₀` 只有实零点。
`Statement → AllZerosReal 0`：`H₀ z = 0` 经桥接引理化为 `ξ` 零点即非平凡零点，
`RH` 给出 `Re = 1/2`，即 `z.im = 0`；反向取 `z = −2i(s − 1/2)` 把非平凡零点
`s` 拉回到 `H₀` 的零点，`z.im = 0` 即 `Re s = 1/2`。 -/
theorem statement_iff_allZerosReal_zero :
    RiemannHypothesis.Statement ↔ AllZerosReal 0 := by
  constructor
  · intro hRH z hz0
    have hΞ := (deBruijnNewmanH_zero_eq_zero_iff z).mp hz0
    have hnontriv := (completedZeta_eq_zero_iff _).mp hΞ
    have hre := hRH _ hnontriv
    have hre2 : ((1 : ℂ) / 2 + Complex.I * (z / 2)).re = 1 / 2 - z.im / 2 := by
      have h4 : ((1 : ℂ) / 2).re = 1 / 2 := by
        rw [show (1 : ℂ) / 2 = ((1 / 2 : ℝ) : ℂ) from by
          rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]]
        exact Complex.ofReal_re _
      have h6 : (z / 2 : ℂ).im = z.im / 2 := by
        rw [show z / 2 = z * ((1 / 2 : ℝ) : ℂ) from by
          rw [show ((1 / 2 : ℝ) : ℂ) = 1 / 2 from by
            rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]]; ring]
        rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
        ring
      rw [Complex.add_re, h4, Complex.I_mul_re, h6]
      ring
    rw [hre2] at hre
    linarith
  · intro hAZ s hs
    have hz : (1 / 2 : ℂ) + Complex.I * ((-2 * Complex.I * (s - 1 / 2)) / 2) = s := by
      have hII : Complex.I * ((-2 * Complex.I * (s - 1 / 2)) / 2) = s - 1 / 2 := by
        rw [show Complex.I * ((-2 * Complex.I * (s - 1 / 2)) / 2)
            = -(Complex.I * Complex.I) * (s - 1 / 2) from by ring]
        rw [Complex.I_mul_I]
        ring
      rw [hII]
      ring
    have hz0 : deBruijnNewmanH 0 (-2 * Complex.I * (s - 1 / 2)) = 0 := by
      rw [deBruijnNewmanH_zero_eq_zero_iff, hz]
      exact (completedZeta_eq_zero_iff s).mpr hs
    have him2 : (-2 * Complex.I * (s - 1 / 2) : ℂ).im = 1 - 2 * s.re := by
      have h1 : (-2 * Complex.I : ℂ).re = 0 := by simp
      have h2 : (-2 * Complex.I : ℂ).im = -2 := by simp
      have h3 : (s - 1 / 2 : ℂ).re = s.re - 1 / 2 := by
        have h4 : ((1 : ℂ) / 2).re = 1 / 2 := by
          rw [show (1 : ℂ) / 2 = ((1 / 2 : ℝ) : ℂ) from by
          rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]]
          exact Complex.ofReal_re _
        rw [Complex.sub_re, h4]
      rw [Complex.mul_im, h1, h2, h3]
      ring
    have him := hAZ _ hz0
    rw [him2] at him
    linarith

/-- `H_t` has real coefficients: conjugation symmetry
`H_t (star z) = star (H_t z)`. Together with `deBruijnNewmanH_even`, the
zeros of `H_t` come in orbits of `{z, -z, star z, -star z}`. -/
theorem deBruijnNewmanH_conj (t : ℝ) (z : ℂ) :
    deBruijnNewmanH t (star z) = star (deBruijnNewmanH t z) := by
  unfold deBruijnNewmanH
  show (∫ (u : ℝ) in Set.Ioi 0, heatIntegrand t (star z) u)
      = (starRingEnd ℂ) (∫ (u : ℝ) in Set.Ioi 0, heatIntegrand t z u)
  have e1 : (starRingEnd ℂ) (∫ (u : ℝ) in Set.Ioi 0, heatIntegrand t z u)
      = ∫ (u : ℝ) in Set.Ioi 0, (starRingEnd ℂ) (heatIntegrand t z u) :=
    (integral_conj (f := fun u : ℝ => heatIntegrand t z u)
      (μ := MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)))).symm
  refine Eq.trans ?_ e1.symm
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro u _
  show ((Real.exp (t * u ^ 2) * phi u : ℝ) : ℂ)
      * Complex.cos ((starRingEnd ℂ) z * (u : ℂ))
      = (starRingEnd ℂ)
        (((Real.exp (t * u ^ 2) * phi u : ℝ) : ℂ) * Complex.cos (z * (u : ℂ)))
  rw [map_mul, Complex.conj_ofReal, ← Complex.cos_conj, map_mul, Complex.conj_ofReal]

/-- `Λ ≤ 0` as soon as `H_0` has only real zeros: `0` belongs to the set
whose infimum defines `Λ` (if the set is not bounded below, `sInf` takes
its junk value `sInf ∅ = 0`, which is also `≤ 0`). -/
theorem allZerosReal_zero_lambda_le (h : AllZerosReal 0) :
    deBruijnNewmanLambda ≤ 0 := by
  unfold deBruijnNewmanLambda
  by_cases hb : BddBelow {s : ℝ | AllZerosReal s}
  · exact csInf_le hb h
  · simp [csInf_of_not_bddBelow hb]

/-- **RH ⇒ Λ ≤ 0**（Phase 2 的「容易方向」）：RH 给出 `H_0` 只有实零点，
故 `0 ∈ {t | AllZerosReal t}`，从而 `Λ = sInf {t | AllZerosReal t} ≤ 0`。 -/
theorem lambda_le_zero_of_rh (hRH : RiemannHypothesis.Statement) :
    deBruijnNewmanLambda ≤ 0 :=
  allZerosReal_zero_lambda_le (statement_iff_allZerosReal_zero.mp hRH)

/-- Zeros of `H_t` are invariant under conjugation. -/
theorem deBruijnNewmanH_zero_star {t : ℝ} {z : ℂ} (hz : deBruijnNewmanH t z = 0) :
    deBruijnNewmanH t (star z) = 0 := by
  rw [deBruijnNewmanH_conj, hz, star_zero]

/-- `H_t(z)` is continuous in `t` (in fact differentiable, by
`hasDerivAt_deBruijnNewmanH_t`). -/
theorem continuous_deBruijnNewmanH_t (z : ℂ) :
    Continuous fun t : ℝ => deBruijnNewmanH t z :=
  continuous_iff_continuousAt.mpr
    fun t => (hasDerivAt_deBruijnNewmanH_t z t).continuousAt

/-- The elementary bound `|e^x − 1| ≤ |x|·e^{|x|}` for all real `x`.
(Mathlib only has the `|x| ≤ 1` special case `Complex.abs_exp_sub_one_le`.) -/
theorem abs_exp_sub_one_le_abs_mul_exp_abs (x : ℝ) :
    |Real.exp x - 1| ≤ |x| * Real.exp |x| := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg (by linarith [Real.add_one_le_exp x] : 0 ≤ Real.exp x - 1),
      abs_of_nonneg hx]
    have h1 : 1 - Real.exp (-x) ≤ x := by
      have h := Real.add_one_le_exp (-x)
      linarith
    have h2 : Real.exp x - 1 = Real.exp x * (1 - Real.exp (-x)) := by
      have he : Real.exp x * Real.exp (-x) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      rw [mul_sub, he, mul_one]
    rw [h2]
    calc Real.exp x * (1 - Real.exp (-x)) ≤ Real.exp x * x :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_nonneg _)
      _ = x * Real.exp x := mul_comm _ _
  · have hx' : x < 0 := not_le.mp hx
    have h1 : Real.exp x - 1 < 0 := by
      have h := Real.exp_lt_exp.mpr hx'
      rw [Real.exp_zero] at h
      linarith
    have h2 : 1 - Real.exp x ≤ -x := by linarith [Real.add_one_le_exp x]
    have h3 : (1:ℝ) ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
    have h4 : -x ≤ (-x) * Real.exp (-x) := by
      have h := mul_le_mul_of_nonneg_left h3 (le_of_lt (neg_pos.mpr hx'))
      rwa [mul_one] at h
    rw [abs_of_neg h1, abs_of_neg hx']
    linarith

/-- Local Lipschitz control of `H_t` in `t`: on `|t − t₀| ≤ 1` and
`z ∈ ball z₀ 1`, the difference `H_t(z) − H_{t₀}(z)` is bounded by
`|t − t₀|` times an absolutely convergent dominating integral. -/
theorem dist_deBruijnNewmanH_le (t₀ : ℝ) (z₀ : ℂ) {t : ℝ} {z : ℂ}
    (ht : |t - t₀| ≤ 1) (hz : z ∈ Metric.ball z₀ 1) :
    dist (deBruijnNewmanH t z) (deBruijnNewmanH t₀ z)
      ≤ |t - t₀| * ∫ u : ℝ in Set.Ioi 0,
          heatSqDominatingFun (t₀ + 1) (|z₀.im| + 1) u := by
  rw [dist_eq_norm]
  have hsub : deBruijnNewmanH t z - deBruijnNewmanH t₀ z
      = ∫ u : ℝ in Set.Ioi 0, (heatIntegrand t z u - heatIntegrand t₀ z u) := by
    show (∫ u : ℝ in Set.Ioi 0, heatIntegrand t z u)
        - (∫ u : ℝ in Set.Ioi 0, heatIntegrand t₀ z u) = _
    exact (MeasureTheory.integral_sub
      (f := fun u : ℝ => heatIntegrand t z u) (g := fun u : ℝ => heatIntegrand t₀ z u)
      (μ := MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)))
      (heat_integrand_integrable t z) (heat_integrand_integrable t₀ z)).symm
  calc ‖deBruijnNewmanH t z - deBruijnNewmanH t₀ z‖
      = ‖∫ u : ℝ in Set.Ioi 0, (heatIntegrand t z u - heatIntegrand t₀ z u)‖ := by
        rw [hsub]
    _ ≤ ∫ u : ℝ in Set.Ioi 0, ‖heatIntegrand t z u - heatIntegrand t₀ z u‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ in Set.Ioi 0,
          |t - t₀| * heatSqDominatingFun (t₀ + 1) (|z₀.im| + 1) u := by
        apply MeasureTheory.integral_mono_ae
        · exact ((heat_integrand_integrable t z).sub
            (heat_integrand_integrable t₀ z)).norm
        · exact (integrableOn_heatSqDominatingFun (t₀ + 1) (|z₀.im| + 1)
            (by positivity)).const_mul _
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
          have hu0 : 0 ≤ u := le_of_lt hu
          have hzim : |z.im| ≤ |z₀.im| + 1 := by
            have h2 : |(z - z₀).im| ≤ ‖z - z₀‖ := Complex.abs_im_le_norm _
            have h3 : ‖z - z₀‖ < 1 := by
              rw [← dist_eq_norm]
              exact Metric.mem_ball.mp hz
            have him : z.im - z₀.im = (z - z₀).im := by simp [Complex.sub_im]
            calc |z.im| = |z.im - z₀.im + z₀.im| :=
                  (congrArg abs (sub_add_cancel z.im z₀.im)).symm
              _ ≤ |z.im - z₀.im| + |z₀.im| := abs_add_le _ _
              _ ≤ ‖z - z₀‖ + |z₀.im| := by rw [him]; exact add_le_add_left h2 _
              _ ≤ 1 + |z₀.im| := by linarith [h3.le]
              _ = |z₀.im| + 1 := by ring
          have hdiff : heatIntegrand t z u - heatIntegrand t₀ z u
              = ((phi u * (Real.exp (t * u ^ 2) - Real.exp (t₀ * u ^ 2)) : ℝ) : ℂ)
                * Complex.cos (z * (u : ℂ)) := by
            unfold heatIntegrand
            simp only [Complex.ofReal_mul, Complex.ofReal_sub]
            ring
          rw [hdiff]
          have hn : ‖((phi u * (Real.exp (t * u ^ 2) - Real.exp (t₀ * u ^ 2)) : ℝ) : ℂ)
                * Complex.cos (z * (u : ℂ))‖
              = |phi u| * |Real.exp (t * u ^ 2) - Real.exp (t₀ * u ^ 2)|
                * ‖Complex.cos (z * (u : ℂ))‖ := by
            rw [norm_mul,
              show ‖((phi u * (Real.exp (t * u ^ 2)
                    - Real.exp (t₀ * u ^ 2)) : ℝ) : ℂ)‖
                = |phi u * (Real.exp (t * u ^ 2) - Real.exp (t₀ * u ^ 2))|
              from RCLike.norm_ofReal _,
              abs_mul]
          rw [hn]
          have hexp : |Real.exp (t * u ^ 2) - Real.exp (t₀ * u ^ 2)|
              ≤ |t - t₀| * u ^ 2 * Real.exp ((t₀ + 1) * u ^ 2) := by
            have he : Real.exp (t * u ^ 2) - Real.exp (t₀ * u ^ 2)
                = Real.exp (t₀ * u ^ 2) * (Real.exp ((t - t₀) * u ^ 2) - 1) := by
              have h1 : Real.exp (t * u ^ 2)
                  = Real.exp (t₀ * u ^ 2) * Real.exp ((t - t₀) * u ^ 2) := by
                rw [← Real.exp_add]
                congr 1
                ring
              rw [h1]
              ring
            rw [he, abs_mul, abs_of_pos (Real.exp_pos _)]
            have h2 : |Real.exp ((t - t₀) * u ^ 2) - 1|
                ≤ |(t - t₀) * u ^ 2| * Real.exp |(t - t₀) * u ^ 2| :=
              abs_exp_sub_one_le_abs_mul_exp_abs _
            have h3 : |(t - t₀) * u ^ 2| = |t - t₀| * u ^ 2 := by
              rw [abs_mul, abs_of_nonneg (sq_nonneg u)]
            have h4 : Real.exp |(t - t₀) * u ^ 2| ≤ Real.exp (u ^ 2) := by
              apply Real.exp_le_exp.mpr
              rw [h3]
              calc |t - t₀| * u ^ 2 ≤ 1 * u ^ 2 :=
                    mul_le_mul_of_nonneg_right ht (sq_nonneg u)
                _ = u ^ 2 := one_mul _
            calc Real.exp (t₀ * u ^ 2) * |Real.exp ((t - t₀) * u ^ 2) - 1|
                ≤ Real.exp (t₀ * u ^ 2) * (|t - t₀| * u ^ 2 * Real.exp (u ^ 2)) := by
                  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
                  calc |Real.exp ((t - t₀) * u ^ 2) - 1|
                      ≤ |(t - t₀) * u ^ 2| * Real.exp |(t - t₀) * u ^ 2| := h2
                    _ = |t - t₀| * u ^ 2 * Real.exp |(t - t₀) * u ^ 2| := by rw [h3]
                    _ ≤ |t - t₀| * u ^ 2 * Real.exp (u ^ 2) :=
                        mul_le_mul_of_nonneg_left h4
                          (mul_nonneg (abs_nonneg _) (sq_nonneg u))
              _ = |t - t₀| * u ^ 2 * Real.exp ((t₀ + 1) * u ^ 2) := by
                  have h5 : Real.exp (t₀ * u ^ 2) * Real.exp (u ^ 2)
                      = Real.exp ((t₀ + 1) * u ^ 2) := by
                    rw [← Real.exp_add]
                    congr 1
                    ring
                  rw [show Real.exp (t₀ * u ^ 2) * (|t - t₀| * u ^ 2 * Real.exp (u ^ 2))
                      = |t - t₀| * u ^ 2 * (Real.exp (t₀ * u ^ 2) * Real.exp (u ^ 2))
                    from by ring, h5]
          have hcos : ‖Complex.cos (z * (u : ℂ))‖ ≤ Real.exp ((|z₀.im| + 1) * u) := by
            calc ‖Complex.cos (z * (u : ℂ))‖ ≤ Real.exp |z.im * u| :=
                  norm_cos_mul_ofReal_le_exp z u
              _ = Real.exp (|z.im| * u) := by rw [abs_mul, abs_of_nonneg hu0]
              _ ≤ Real.exp ((|z₀.im| + 1) * u) :=
                  Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hzim hu0)
          have hphi : |phi u| ≤ (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
              * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u))) :=
            abs_phi_le u hu0
          have hb0 : 0 ≤ (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
              * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u))) :=
            mul_nonneg (mul_nonneg
              (mul_nonneg (by positivity) phiTailConst_nonneg)
              (Real.exp_nonneg _)) (Real.exp_nonneg _)
          have hb0' : 0 ≤ (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
              * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))
              * (|t - t₀| * u ^ 2 * Real.exp ((t₀ + 1) * u ^ 2)) :=
            mul_nonneg hb0
              (mul_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg u))
                (Real.exp_nonneg _))
          calc |phi u| * |Real.exp (t * u ^ 2) - Real.exp (t₀ * u ^ 2)|
                * ‖Complex.cos (z * (u : ℂ))‖
              ≤ ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
                  * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u))))
                * (|t - t₀| * u ^ 2 * Real.exp ((t₀ + 1) * u ^ 2))
                * Real.exp ((|z₀.im| + 1) * u) :=
                mul_le_mul (mul_le_mul hphi hexp (abs_nonneg _) hb0) hcos
                  (norm_nonneg _) hb0'
            _ = |t - t₀| * heatSqDominatingFun (t₀ + 1) (|z₀.im| + 1) u := by
                unfold heatSqDominatingFun
                have e1 : ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
                      * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u))))
                    * (|t - t₀| * u ^ 2 * Real.exp ((t₀ + 1) * u ^ 2))
                    * Real.exp ((|z₀.im| + 1) * u)
                  = |t - t₀| * ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
                      * u ^ 2
                      * (Real.exp ((t₀ + 1) * u ^ 2) * Real.exp (9 * u)
                        * Real.exp ((|z₀.im| + 1) * u))
                      * Real.exp (-(Real.pi * Real.exp (4 * u)))) := by ring
                rw [e1, ← Real.exp_add, ← Real.exp_add]
                have e2 : (t₀ + 1) * u ^ 2 + 9 * u + (|z₀.im| + 1) * u
                    = (t₀ + 1) * u ^ 2 + (9 + (|z₀.im| + 1)) * u := by ring
                rw [e2]
    _ = |t - t₀| * ∫ u : ℝ in Set.Ioi 0,
          heatSqDominatingFun (t₀ + 1) (|z₀.im| + 1) u := by
        exact MeasureTheory.integral_const_mul _ _

/-- **Local uniform convergence of the de Bruijn–Newman flow in `t`**:
`H_t → H_{t₀}` locally uniformly as `t → t₀`. This is the analytic input
for a future Hurwitz-type argument that `AllZerosReal` is closed under
decreasing limits of `t`. -/
theorem tendstoLocallyUniformly_deBruijnNewmanH (t₀ : ℝ) :
    TendstoLocallyUniformly (fun t : ℝ => deBruijnNewmanH t)
      (deBruijnNewmanH t₀) (nhds t₀) := by
  intro uu huu z₀
  rw [Metric.mem_uniformity_dist] at huu
  obtain ⟨ε, hε, huε⟩ := huu
  set C := ∫ u : ℝ in Set.Ioi 0, heatSqDominatingFun (t₀ + 1) (|z₀.im| + 1) u
    with hC
  have hC0 : 0 ≤ C := by
    rw [hC]
    apply MeasureTheory.integral_nonneg_of_ae
    filter_upwards with u
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi ^ 2 + 3 * Real.pi)
        phiTailConst_nonneg) (sq_nonneg u)) (Real.exp_nonneg _)) (Real.exp_nonneg _)
  have hC1 : (0:ℝ) < C + 1 := by linarith
  have hδ : (0:ℝ) < min 1 (ε / (C + 1)) := lt_min one_pos (div_pos hε hC1)
  refine ⟨Metric.ball z₀ 1, Metric.ball_mem_nhds z₀ one_pos, ?_⟩
  filter_upwards [Metric.ball_mem_nhds t₀ hδ] with t ht z hz
  apply huε
  have htm : |t - t₀| < min 1 (ε / (C + 1)) := by
    rwa [Metric.mem_ball, Real.dist_eq] at ht
  have ht1 : |t - t₀| ≤ 1 := htm.le.trans (min_le_left _ _)
  have hdest := dist_deBruijnNewmanH_le t₀ z₀ ht1 hz
  rw [dist_comm] at hdest
  have hεC : |t - t₀| * C < ε := by
    have h : |t - t₀| < ε / (C + 1) := htm.trans_le (min_le_right _ _)
    have h2 : C / (C + 1) < 1 := by
      rw [div_lt_one hC1]
      linarith
    calc |t - t₀| * C ≤ (ε / (C + 1)) * C :=
          mul_le_mul_of_nonneg_right h.le hC0
      _ = ε * C / (C + 1) := div_mul_eq_mul_div _ _ _
      _ = ε * (C / (C + 1)) := mul_div_assoc _ _ _
      _ < ε * 1 := mul_lt_mul_of_pos_left h2 hε
      _ = ε := mul_one ε
  exact lt_of_le_of_lt hdest hεC

/-! ## Phase 2(vii)：`Φ` 正性与 `H_t` 的全局非退化 -/

/-- For `u ≥ 0` and `n ≥ 1` every summand of the `Φ` series is nonnegative:
`2π²n⁴e^{9u} ≥ 3πn²e^{5u}` because `2πn² ≥ 2π > 3 ≥ 3e^{−4u}`. -/
theorem phiTerm_nonneg (hu : 0 ≤ u) {n : ℕ} (hn : 1 ≤ n) : 0 ≤ phiTerm n u := by
  unfold phiTerm
  apply mul_nonneg ?_ (Real.exp_nonneg _)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h2 : (3 : ℝ) ≤ 2 * Real.pi * (n : ℝ) ^ 2 := by
    have hpi : (3 : ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_three]
    calc (3 : ℝ) ≤ 2 * Real.pi := hpi.le
      _ = 2 * Real.pi * 1 := (mul_one _).symm
      _ ≤ 2 * Real.pi * (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left (by nlinarith [hn1]) (by positivity)
  have key : 3 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u)
      ≤ 2 * Real.pi ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u) := by
    calc 3 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u)
        ≤ 3 * Real.pi * (n : ℝ) ^ 2 * Real.exp (9 * u) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hu])) (by positivity)
      _ = 3 * (Real.pi * (n : ℝ) ^ 2 * Real.exp (9 * u)) := by ring
      _ ≤ (2 * Real.pi * (n : ℝ) ^ 2) * (Real.pi * (n : ℝ) ^ 2 * Real.exp (9 * u)) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = 2 * Real.pi ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u) := by ring
  linarith

/-- The first `Φ` summand is strictly positive for `u ≥ 0`. -/
theorem phiTerm_one_pos (hu : 0 ≤ u) : 0 < phiTerm 1 u := by
  unfold phiTerm
  simp only [Nat.cast_one, one_pow, mul_one]
  apply mul_pos ?_ (Real.exp_pos _)
  have h2 : Real.exp (5 * u) ≤ Real.exp (9 * u) := Real.exp_le_exp.mpr (by linarith [hu])
  have h3 : 3 * Real.pi * Real.exp (5 * u) < 2 * Real.pi ^ 2 * Real.exp (9 * u) := by
    have hpi : (3 : ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_three]
    have h3π : 3 * Real.pi < 2 * Real.pi ^ 2 := by
      calc 3 * Real.pi = Real.pi * 3 := by ring
        _ < Real.pi * (2 * Real.pi) := mul_lt_mul_of_pos_left hpi Real.pi_pos
        _ = 2 * Real.pi ^ 2 := by ring
    calc 3 * Real.pi * Real.exp (5 * u)
        ≤ 3 * Real.pi * Real.exp (9 * u) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ < (2 * Real.pi ^ 2) * Real.exp (9 * u) :=
          mul_lt_mul_of_pos_right h3π (Real.exp_pos _)
  linarith

/-- `Φ u ≥ 0` for `u ≥ 0`. -/
theorem phi_nonneg (hu : 0 ≤ u) : 0 ≤ phi u :=
  tsum_nonneg fun n => phiTerm_nonneg hu (by omega)

/-- **`Φ` is strictly positive on `[0, ∞)`**: the whole series is nonnegative and
its first summand is strictly positive. -/
theorem phi_pos (hu : 0 ≤ u) : 0 < phi u := by
  refine (phiTerm_one_pos hu).trans_le ?_
  exact (summable_phiTerm u).le_tsum 0 fun j _ => phiTerm_nonneg hu (by omega)

/-- At `z = 0` the `H_t` integral is real: `(H_t 0).re = ∫₀^∞ e^{tu²} Φ(u) du`. -/
theorem deBruijnNewmanH_apply_zero_re (t : ℝ) :
    (deBruijnNewmanH t 0).re = ∫ u in Set.Ioi 0, Real.exp (t * u ^ 2) * phi u := by
  have e1 : ∫ u in Set.Ioi 0, (heatIntegrand t 0 u).re
      = (∫ u in Set.Ioi 0, heatIntegrand t 0 u).re :=
    integral_re (heat_integrand_integrable t 0)
  have e2 : ∫ u in Set.Ioi 0, (heatIntegrand t 0 u).re
      = ∫ u in Set.Ioi 0, Real.exp (t * u ^ 2) * phi u := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro u _
    show (heatIntegrand t 0 u).re = Real.exp (t * u ^ 2) * phi u
    unfold heatIntegrand
    rw [zero_mul, Complex.cos_zero, mul_one, Complex.ofReal_re]
  show (∫ u in Set.Ioi 0, heatIntegrand t 0 u).re = _
  rw [← e1]; exact e2

/-- **Global non-degeneracy in strong form**: `(H_t 0).re > 0` for every `t : ℝ`.
On `[0, 1/16]` one has `Φ ≥ (2π² − 3πe^{5/16})·e^{−πe^{1/4}} > 0` (the key estimate
`e^{5/16} < 2π/3` is certified by cubing), while `e^{tu²}` is bounded below by
`min 1 (exp (t / 256))`; the set integral over `Ioc 0 (1/16)` is therefore strictly
positive. -/
theorem deBruijnNewmanH_zero_re_pos (t : ℝ) : 0 < (deBruijnNewmanH t 0).re := by
  rw [deBruijnNewmanH_apply_zero_re]
  have hexp : Real.exp (5 / 16 : ℝ) < 2 * Real.pi / 3 := by
    have h1 : (Real.exp (5 / 16 : ℝ)) ^ 3 < (2 * Real.pi / 3) ^ 3 := by
      have e1 : (Real.exp (5 / 16 : ℝ)) ^ 3 = Real.exp (15 / 16 : ℝ) := by
        rw [← Real.exp_nat_mul]; congr 1; ring
      have e2 : Real.exp (15 / 16 : ℝ) < Real.exp 1 :=
        Real.exp_strictMono (by norm_num)
      have e3 : Real.exp 1 < (2 * Real.pi / 3) ^ 3 := by
        have h2 : (2 : ℝ) < 2 * Real.pi / 3 := by linarith [Real.pi_gt_three]
        have h8 : (8 : ℝ) < (2 * Real.pi / 3) ^ 3 := by
          have h := pow_lt_pow_left₀ h2 (by norm_num : (0 : ℝ) ≤ 2) three_ne_zero
          norm_num at h
          exact h
        exact lt_trans Real.exp_one_lt_d9 (by linarith [h8])
      rw [e1]; exact lt_trans e2 e3
    exact lt_of_pow_lt_pow_left₀ 3 (by positivity : (0 : ℝ) ≤ 2 * Real.pi / 3) h1
  set b₀ : ℝ := 2 * Real.pi ^ 2 - 3 * Real.pi * Real.exp (5 / 16) with hb₀
  have hb₀pos : 0 < b₀ := by
    have h := mul_lt_mul_of_pos_left hexp (by positivity : (0 : ℝ) < 3 * Real.pi)
    have h2 : 3 * Real.pi * (2 * Real.pi / 3) = 2 * Real.pi ^ 2 := by ring
    rw [hb₀]; linarith
  set e₀ : ℝ := Real.exp (-(Real.pi * Real.exp (1 / 4 : ℝ))) with he₀
  have he₀pos : 0 < e₀ := Real.exp_pos _
  have hpt : ∀ u ∈ Set.Ioc 0 (1 / 16 : ℝ), b₀ * e₀ ≤ phiTerm 1 u := by
    intro u hu
    have eA : (1 : ℝ) ≤ Real.exp (9 * u) := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith [hu.1])
    have eB : Real.exp (5 * u) ≤ Real.exp (5 / 16 : ℝ) :=
      Real.exp_le_exp.mpr (by linarith [hu.2])
    have eC : e₀ ≤ Real.exp (-(Real.pi * Real.exp (4 * u))) := by
      rw [he₀]
      apply Real.exp_le_exp.mpr
      have h4 : Real.exp (4 * u) ≤ Real.exp (1 / 4 : ℝ) :=
        Real.exp_le_exp.mpr (by linarith [hu.2])
      have := mul_le_mul_of_nonneg_left h4 Real.pi_pos.le
      linarith
    have ebr : b₀
        ≤ 2 * Real.pi ^ 2 * Real.exp (9 * u) - 3 * Real.pi * Real.exp (5 * u) := by
      have h1 : (2 : ℝ) * Real.pi ^ 2 ≤ 2 * Real.pi ^ 2 * Real.exp (9 * u) := by
        calc 2 * Real.pi ^ 2 = 2 * Real.pi ^ 2 * 1 := (mul_one _).symm
          _ ≤ 2 * Real.pi ^ 2 * Real.exp (9 * u) :=
            mul_le_mul_of_nonneg_left eA (by positivity)
      have h2 := mul_le_mul_of_nonneg_left eB (by positivity : (0 : ℝ) ≤ 3 * Real.pi)
      rw [hb₀]; linarith
    simp only [phiTerm, Nat.cast_one, one_pow, mul_one]
    exact mul_le_mul ebr eC he₀pos.le (le_trans hb₀pos.le ebr)
  have hphi : ∀ u ∈ Set.Ioc 0 (1 / 16 : ℝ), b₀ * e₀ ≤ phi u := by
    intro u hu
    exact (hpt u hu).trans ((summable_phiTerm u).le_tsum 0
      fun j _ => phiTerm_nonneg hu.1.le (by omega))
  set E : ℝ := min 1 (Real.exp (t * (1 / 16 : ℝ) ^ 2)) with hE
  have hEpos : 0 < E := lt_min zero_lt_one (Real.exp_pos _)
  have hE' : ∀ u ∈ Set.Ioc 0 (1 / 16 : ℝ), E ≤ Real.exp (t * u ^ 2) := by
    intro u hu
    have hu2 : u ^ 2 ≤ (1 / 16 : ℝ) ^ 2 := pow_le_pow_left₀ hu.1.le hu.2 2
    by_cases ht : 0 ≤ t
    · exact (min_le_left _ _).trans (by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg u]))
    · exact (min_le_right _ _).trans (Real.exp_le_exp.mpr (by
        have htn := mul_le_mul_of_nonpos_left hu2 (not_le.mp ht).le
        linarith))
  have hIntR : MeasureTheory.IntegrableOn (fun u => Real.exp (t * u ^ 2) * phi u)
      (Set.Ioi 0) MeasureTheory.volume := by
    apply MeasureTheory.IntegrableOn.congr_fun (heat_integrand_integrable t 0).re
      ?_ measurableSet_Ioi
    intro u _
    show (heatIntegrand t 0 u).re = Real.exp (t * u ^ 2) * phi u
    unfold heatIntegrand
    rw [zero_mul, Complex.cos_zero, mul_one, Complex.ofReal_re]
  have hI1 : (∫ u in Set.Ioc 0 (1 / 16 : ℝ), Real.exp (t * u ^ 2) * phi u)
      ≤ ∫ u in Set.Ioi 0, Real.exp (t * u ^ 2) * phi u := by
    refine MeasureTheory.setIntegral_mono_set hIntR ?_ ?_
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall fun u hu =>
          mul_nonneg (Real.exp_nonneg _) (phi_nonneg hu.le))
    · exact Filter.Eventually.of_forall fun u hu => Set.Ioc_subset_Ioi_self hu
  have hI2 : (∫ u in Set.Ioc 0 (1 / 16 : ℝ), E * (b₀ * e₀))
      ≤ ∫ u in Set.Ioc 0 (1 / 16 : ℝ), Real.exp (t * u ^ 2) * phi u := by
    refine MeasureTheory.setIntegral_mono_on ?_ ?_ measurableSet_Ioc fun u hu => ?_
    · exact MeasureTheory.integrableOn_const
        (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    · exact hIntR.mono_set Set.Ioc_subset_Ioi_self
    · exact mul_le_mul (hE' u hu) (hphi u hu) (mul_nonneg hb₀pos.le he₀pos.le)
        (Real.exp_nonneg _)
  have hI3 : ∫ u in Set.Ioc 0 (1 / 16 : ℝ), E * (b₀ * e₀)
      = (1 / 16 : ℝ) * (E * (b₀ * e₀)) := by
    rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 16 - 0), smul_eq_mul]
    ring
  have hpos : 0 < (1 / 16 : ℝ) * (E * (b₀ * e₀)) :=
    mul_pos (by norm_num) (mul_pos hEpos (mul_pos hb₀pos he₀pos))
  linarith

/-- Every `H_t` is somewhere nonzero (indeed `(H_t 0).re > 0`): the non-degeneracy
hypothesis for Hurwitz / identity-theorem arguments at any time. -/
theorem deBruijnNewmanH_exists_ne_zero (t : ℝ) : ∃ z : ℂ, deBruijnNewmanH t z ≠ 0 := by
  refine ⟨0, fun h => ?_⟩
  have hpos := deBruijnNewmanH_zero_re_pos t
  rw [h, Complex.zero_re] at hpos
  exact lt_irrefl 0 hpos

/-! ## Phase 2(ix)：`∂_t H` 的联合连续性与零点速度 ODE 基础 -/

/-- Auxiliary: if `dist z z₀ < 1` then `|z.im| ≤ |z₀.im| + 1`. -/
theorem abs_im_le_add_one_of_dist_lt_one {z z₀ : ℂ} (hz : dist z z₀ < 1) :
    |z.im| ≤ |z₀.im| + 1 := by
  have h2 : |(z - z₀).im| ≤ ‖z - z₀‖ := Complex.abs_im_le_norm _
  have h3 : ‖z - z₀‖ < 1 := by rw [← dist_eq_norm]; exact hz
  have him : z.im - z₀.im = (z - z₀).im := by simp [Complex.sub_im]
  calc |z.im| = |z.im - z₀.im + z₀.im| :=
        (congrArg abs (sub_add_cancel z.im z₀.im)).symm
    _ ≤ |z.im - z₀.im| + |z₀.im| := abs_add_le _ _
    _ ≤ ‖z - z₀‖ + |z₀.im| := by rw [him]; exact add_le_add_left h2 _
    _ ≤ 1 + |z₀.im| := by linarith [h3.le]
    _ = |z₀.im| + 1 := by ring

/-- Box bound for the `∂_t` integrand (standalone form of the bound used inside
`hasDerivAt_deBruijnNewmanH_t`): for `t ≤ t₁`, `|z.im| ≤ c`, `u ≥ 0`,
`‖u² · heatIntegrand t z u‖ ≤ heatSqDominatingFun t₁ c u`. -/
theorem norm_sq_mul_heatIntegrand_le {t t₁ c : ℝ} (ht : t ≤ t₁) (hc : 0 ≤ c) {z : ℂ}
    (hzim : |z.im| ≤ c) {u : ℝ} (hu : 0 ≤ u) :
    ‖((u : ℂ) ^ 2) * heatIntegrand t z u‖ ≤ heatSqDominatingFun t₁ c u := by
  have hC0 : (0 : ℝ) ≤ (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst :=
    mul_nonneg (by positivity) phiTailConst_nonneg
  have hexp : Real.exp (t * u ^ 2) ≤ Real.exp (t₁ * u ^ 2) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ht (sq_nonneg u))
  have hcos : ‖Complex.cos (z * (u : ℂ))‖ ≤ Real.exp (c * u) := by
    calc ‖Complex.cos (z * (u : ℂ))‖ ≤ Real.exp |z.im * u| :=
          norm_cos_mul_ofReal_le_exp z u
      _ = Real.exp (|z.im| * u) := by rw [abs_mul, abs_of_nonneg hu]
      _ ≤ Real.exp (c * u) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hzim hu)
  have hn : ‖((u : ℂ) ^ 2) * heatIntegrand t z u‖
      = u ^ 2 * (|Real.exp (t * u ^ 2) * phi u| * ‖Complex.cos (z * (u : ℂ))‖) := by
    rw [norm_mul, norm_pow,
      show ‖(u : ℂ)‖ = u from by
        rw [show ‖(u : ℂ)‖ = |u| from RCLike.norm_ofReal u, abs_of_nonneg hu]]
    unfold heatIntegrand
    rw [norm_mul, show ‖((Real.exp (t * u ^ 2) * phi u : ℝ) : ℂ)‖
        = |Real.exp (t * u ^ 2) * phi u| from RCLike.norm_ofReal _]
  rw [hn]
  have hphi : |Real.exp (t * u ^ 2) * phi u|
      ≤ Real.exp (t₁ * u ^ 2) * ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
          * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul hexp (abs_phi_le u hu) (abs_nonneg _) (Real.exp_nonneg _)
  have hb0 : 0 ≤ Real.exp (t₁ * u ^ 2)
      * ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
        * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))) :=
    mul_nonneg (Real.exp_nonneg _)
      (mul_nonneg (mul_nonneg hC0 (Real.exp_nonneg _)) (Real.exp_nonneg _))
  calc u ^ 2 * (|Real.exp (t * u ^ 2) * phi u| * ‖Complex.cos (z * (u : ℂ))‖)
      ≤ u ^ 2 * ((Real.exp (t₁ * u ^ 2)
          * ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
            * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))))
        * Real.exp (c * u)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hphi hcos (norm_nonneg _) hb0) (sq_nonneg u)
    _ = (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst * u ^ 2
          * (Real.exp (t₁ * u ^ 2) * (Real.exp (9 * u) * Real.exp (c * u)))
          * Real.exp (-(Real.pi * Real.exp (4 * u))) := by ring
    _ = (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst * u ^ 2
          * (Real.exp (t₁ * u ^ 2) * Real.exp ((9 + c) * u))
          * Real.exp (-(Real.pi * Real.exp (4 * u))) := by
        have e9c : Real.exp (9 * u) * Real.exp (c * u) = Real.exp ((9 + c) * u) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [e9c]
    _ = heatSqDominatingFun t₁ c u := by
        unfold heatSqDominatingFun
        rw [← Real.exp_add]

/-- **Joint continuity of the time derivative** `∂_t H_t(z)
= ∫₀^∞ u² e^{tu²} Φ(u) cos(zu) du` on `ℝ × ℂ`: dominated convergence with the
`heatSqDominatingFun` box bound `norm_sq_mul_heatIntegrand_le`. -/
theorem continuous_deBruijnNewmanH_tderiv :
    Continuous fun p : ℝ × ℂ =>
      ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand p.1 p.2 u := by
  rw [continuous_iff_continuousAt]
  intro ⟨t₀, z₀⟩
  set μ := MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)) with hμ
  have hmeas : ∀ p : ℝ × ℂ, MeasureTheory.AEStronglyMeasurable
      (fun u : ℝ => ((u : ℂ) ^ 2) * heatIntegrand p.1 p.2 u) μ :=
    fun p => (((Complex.continuous_ofReal.pow 2).mul
      (continuous_heatIntegrand p.1 p.2)).continuousOn.aestronglyMeasurable
      measurableSet_Ioi)
  have hb1 : ∀ᶠ p : ℝ × ℂ in nhds (t₀, z₀), dist p.1 t₀ < 1 :=
    (continuous_fst.tendsto (t₀, z₀)).eventually (Metric.ball_mem_nhds t₀ zero_lt_one)
  have hb2 : ∀ᶠ p : ℝ × ℂ in nhds (t₀, z₀), dist p.2 z₀ < 1 :=
    (continuous_snd.tendsto (t₀, z₀)).eventually (Metric.ball_mem_nhds z₀ zero_lt_one)
  have hbound : ∀ᶠ p : ℝ × ℂ in nhds (t₀, z₀), ∀ᵐ u : ℝ ∂μ,
      ‖((u : ℂ) ^ 2) * heatIntegrand p.1 p.2 u‖
        ≤ heatSqDominatingFun (t₀ + 1) (|z₀.im| + 1) u := by
    filter_upwards [hb1, hb2] with p hp1 hp2
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
    exact norm_sq_mul_heatIntegrand_le (t := p.1) (t₁ := t₀ + 1) (c := |z₀.im| + 1)
      (by
        have h1 : |p.1 - t₀| < 1 := by rw [← Real.dist_eq]; exact hp1
        linarith [(abs_lt.mp h1).2])
      (by positivity) (abs_im_le_add_one_of_dist_lt_one hp2) hu.le
  have hlim : ∀ᵐ u : ℝ ∂μ, Filter.Tendsto
      (fun p : ℝ × ℂ => ((u : ℂ) ^ 2) * heatIntegrand p.1 p.2 u)
      (nhds (t₀, z₀)) (nhds (((u : ℂ) ^ 2) * heatIntegrand t₀ z₀ u)) := by
    apply Filter.Eventually.of_forall
    intro u
    have hcont : Continuous
        (fun p : ℝ × ℂ => ((u : ℂ) ^ 2) * heatIntegrand p.1 p.2 u) := by
      unfold heatIntegrand
      fun_prop
    exact hcont.tendsto (t₀, z₀)
  show Filter.Tendsto _ (nhds (t₀, z₀)) (nhds _)
  exact MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (heatSqDominatingFun (t₀ + 1) (|z₀.im| + 1))
    (Filter.Eventually.of_forall hmeas) hbound
    (integrableOn_heatSqDominatingFun (t₀ + 1) (|z₀.im| + 1) (by positivity)) hlim

/-- **Box bound for the `z`-derivative integrand**: for `t ≤ t₁`, `|z.im| ≤ c`
and `u ≥ 0`, `‖heatIntegrandDeriv t z u‖ ≤ heatDerivDominatingFun t₁ c u`. -/
theorem norm_heatIntegrandDeriv_le {t t₁ c : ℝ} (ht : t ≤ t₁) (hc : 0 ≤ c) {z : ℂ}
    (hzim : |z.im| ≤ c) {u : ℝ} (hu : 0 ≤ u) :
    ‖heatIntegrandDeriv t z u‖ ≤ heatDerivDominatingFun t₁ c u := by
  have hC0 : (0 : ℝ) ≤ (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst :=
    mul_nonneg (by positivity) phiTailConst_nonneg
  have hexp : Real.exp (t * u ^ 2) ≤ Real.exp (t₁ * u ^ 2) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ht (sq_nonneg u))
  have hsin : ‖Complex.sin (z * (u : ℂ))‖ ≤ Real.exp (c * u) := by
    calc ‖Complex.sin (z * (u : ℂ))‖ ≤ Real.exp |z.im * u| :=
          norm_sin_mul_ofReal_le_exp z u
      _ = Real.exp (|z.im| * u) := by rw [abs_mul, abs_of_nonneg hu]
      _ ≤ Real.exp (c * u) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hzim hu)
  have hn : ‖heatIntegrandDeriv t z u‖
      = u * (|Real.exp (t * u ^ 2) * phi u| * ‖Complex.sin (z * (u : ℂ))‖) := by
    unfold heatIntegrandDeriv
    rw [norm_mul, norm_mul, norm_neg,
      show ‖((Real.exp (t * u ^ 2) * phi u : ℝ) : ℂ)‖
        = |Real.exp (t * u ^ 2) * phi u| from RCLike.norm_ofReal _,
      show ‖(u : ℂ)‖ = u from by
        rw [show ‖(u : ℂ)‖ = |u| from RCLike.norm_ofReal u, abs_of_nonneg hu]]
    ring
  rw [hn]
  have hphi : |Real.exp (t * u ^ 2) * phi u|
      ≤ Real.exp (t₁ * u ^ 2) * ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
          * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul hexp (abs_phi_le u hu) (abs_nonneg _) (Real.exp_nonneg _)
  have hb0 : 0 ≤ Real.exp (t₁ * u ^ 2)
      * ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
        * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))) :=
    mul_nonneg (Real.exp_nonneg _)
      (mul_nonneg (mul_nonneg hC0 (Real.exp_nonneg _)) (Real.exp_nonneg _))
  calc u * (|Real.exp (t * u ^ 2) * phi u| * ‖Complex.sin (z * (u : ℂ))‖)
      ≤ u * ((Real.exp (t₁ * u ^ 2)
          * ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst
            * Real.exp (9 * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))))
        * Real.exp (c * u)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hphi hsin (norm_nonneg _) hb0) hu
    _ = (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst * u
          * (Real.exp (t₁ * u ^ 2) * (Real.exp (9 * u) * Real.exp (c * u)))
          * Real.exp (-(Real.pi * Real.exp (4 * u))) := by ring
    _ = (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst * u
          * (Real.exp (t₁ * u ^ 2) * Real.exp ((9 + c) * u))
          * Real.exp (-(Real.pi * Real.exp (4 * u))) := by
        have e9c : Real.exp (9 * u) * Real.exp (c * u) = Real.exp ((9 + c) * u) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [e9c]
    _ = heatDerivDominatingFun t₁ c u := by
        unfold heatDerivDominatingFun
        rw [← Real.exp_add]

/-- **Joint continuity of the `z`-derivative** `∂_z H_t(z)
= ∫₀^∞ e^{tu²} Φ(u) (−sin(zu)) · u du` on `ℝ × ℂ`: dominated convergence with
the `heatDerivDominatingFun` box bound `norm_heatIntegrandDeriv_le`. -/
theorem continuous_deBruijnNewmanH_zderiv :
    Continuous fun p : ℝ × ℂ => deriv (deBruijnNewmanH p.1) p.2 := by
  rw [show (fun p : ℝ × ℂ => deriv (deBruijnNewmanH p.1) p.2)
      = fun p : ℝ × ℂ => ∫ u : ℝ in Set.Ioi 0, heatIntegrandDeriv p.1 p.2 u
      from funext fun p => deriv_deBruijnNewmanH p.1 p.2]
  rw [continuous_iff_continuousAt]
  intro ⟨t₀, z₀⟩
  set μ := MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)) with hμ
  have hmeas : ∀ p : ℝ × ℂ, MeasureTheory.AEStronglyMeasurable
      (fun u : ℝ => heatIntegrandDeriv p.1 p.2 u) μ :=
    fun p => ((continuous_heatIntegrandDeriv p.1 p.2).continuousOn.aestronglyMeasurable
      measurableSet_Ioi)
  have hb1 : ∀ᶠ p : ℝ × ℂ in nhds (t₀, z₀), dist p.1 t₀ < 1 :=
    (continuous_fst.tendsto (t₀, z₀)).eventually (Metric.ball_mem_nhds t₀ zero_lt_one)
  have hb2 : ∀ᶠ p : ℝ × ℂ in nhds (t₀, z₀), dist p.2 z₀ < 1 :=
    (continuous_snd.tendsto (t₀, z₀)).eventually (Metric.ball_mem_nhds z₀ zero_lt_one)
  have hbound : ∀ᶠ p : ℝ × ℂ in nhds (t₀, z₀), ∀ᵐ u : ℝ ∂μ,
      ‖heatIntegrandDeriv p.1 p.2 u‖
        ≤ heatDerivDominatingFun (t₀ + 1) (|z₀.im| + 1) u := by
    filter_upwards [hb1, hb2] with p hp1 hp2
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
    exact norm_heatIntegrandDeriv_le (t := p.1) (t₁ := t₀ + 1) (c := |z₀.im| + 1)
      (by
        have h1 : |p.1 - t₀| < 1 := by rw [← Real.dist_eq]; exact hp1
        linarith [(abs_lt.mp h1).2])
      (by positivity) (abs_im_le_add_one_of_dist_lt_one hp2) hu.le
  have hlim : ∀ᵐ u : ℝ ∂μ, Filter.Tendsto
      (fun p : ℝ × ℂ => heatIntegrandDeriv p.1 p.2 u)
      (nhds (t₀, z₀)) (nhds (heatIntegrandDeriv t₀ z₀ u)) := by
    apply Filter.Eventually.of_forall
    intro u
    have hcont : Continuous (fun p : ℝ × ℂ => heatIntegrandDeriv p.1 p.2 u) := by
      unfold heatIntegrandDeriv
      fun_prop
    exact hcont.tendsto (t₀, z₀)
  show Filter.Tendsto _ (nhds (t₀, z₀)) (nhds _)
  exact MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (heatDerivDominatingFun (t₀ + 1) (|z₀.im| + 1))
    (Filter.Eventually.of_forall hmeas) hbound
    (integrableOn_heatDerivDominatingFun (t₀ + 1) (|z₀.im| + 1) (by positivity)) hlim

/-- **Affine restriction derivative (z-direction)**: the derivative of
`s ↦ H_t(w + s·k)` at `s : ℝ` is `∂_z H_t(w + s·k) · k`. The inner map
`s ↦ w + (s : ℂ) * k` is real-differentiable with derivative `k`, and the outer
map `H_t` is ℂ-differentiable; the chain rule is `HasDerivAt.scomp` (mixed
scalar domains `𝕜 := ℝ`, `𝕜' := ℂ`). -/
theorem hasDerivAt_deBruijnNewmanH_z_affine (t : ℝ) (w k : ℂ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => deBruijnNewmanH t (w + (s : ℂ) * k))
      (deriv (deBruijnNewmanH t) (w + (s : ℂ) * k) * k) s := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 s := by
    simpa using Complex.ofRealCLM.hasDerivAt (x := s)
  have h2 : HasDerivAt (fun s : ℝ => w + (s : ℂ) * k) k s := by
    simpa using (h1.mul_const k).const_add w
  have hg : HasDerivAt (deBruijnNewmanH t)
      (deriv (deBruijnNewmanH t) (w + (s : ℂ) * k)) (w + (s : ℂ) * k) :=
    (differentiable_deBruijnNewmanH t _).hasDerivAt
  have h3 := @HasDerivAt.scomp ℝ _ ℂ _ _ s ℂ _ _ _ IsScalarTower.right _ _ _ _ hg h2
  simpa [Function.comp_def, smul_eq_mul, mul_comm] using h3

/-- **FTC in the z-direction**: the increment of `H_t` along the segment
`w → w + k` is the interval integral of its z-derivative,
`H_t(w + k) − H_t(w) = ∫₀¹ ∂_z H_t(w + s·k)·k ds`. The integrand is jointly
continuous by `continuous_deBruijnNewmanH_zderiv`. -/
theorem deBruijnNewmanH_z_sub_eq_intervalIntegral (t : ℝ) (w k : ℂ) :
    deBruijnNewmanH t (w + k) - deBruijnNewmanH t w
      = ∫ s : ℝ in (0:ℝ)..1,
        deriv (deBruijnNewmanH t) (w + (s : ℂ) * k) * k := by
  have hDcont : Continuous fun s : ℝ =>
      deriv (deBruijnNewmanH t) (w + (s : ℂ) * k) * k :=
    (continuous_deBruijnNewmanH_zderiv.comp
      (continuous_const.prodMk
        ((Complex.continuous_ofReal.mul continuous_const).const_add w))).mul continuous_const
  have hint : IntervalIntegrable
      (deriv fun s : ℝ => deBruijnNewmanH t (w + (s : ℂ) * k))
      MeasureTheory.volume 0 1 := by
    rw [show (deriv fun s : ℝ => deBruijnNewmanH t (w + (s : ℂ) * k))
        = fun s : ℝ => deriv (deBruijnNewmanH t) (w + (s : ℂ) * k) * k
        from funext fun s => (hasDerivAt_deBruijnNewmanH_z_affine t w k s).deriv]
    exact hDcont.continuousOn.intervalIntegrable
  have h2 : ∫ s : ℝ in (0:ℝ)..1, deriv (deBruijnNewmanH t) (w + (s : ℂ) * k) * k
      = deBruijnNewmanH t (w + (1 : ℂ) * k) - deBruijnNewmanH t (w + (0 : ℂ) * k) := by
    rw [intervalIntegral.integral_congr
      fun s _ => (hasDerivAt_deBruijnNewmanH_z_affine t w k s).deriv.symm]
    exact intervalIntegral.integral_deriv_eq_sub
      (fun x _ => (hasDerivAt_deBruijnNewmanH_z_affine t w k x).differentiableAt) hint
  simpa using h2.symm

/-- **The joint real derivative** of `(t, z) ↦ H_t(z)` as a continuous
`ℝ`-linear map: `(h, k) ↦ h • (∂_t H_t(w)) + (∂_z H_t(w)) * k`, where
`∂_t H_t(w)` is the `u²`-weighted heat integral and
`∂_z H_t(w) = deriv (H_t) w`. -/
noncomputable def jointFDerivCLM (t : ℝ) (w : ℂ) : ℝ × ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.fst ℝ ℝ ℂ).smulRight
      (∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand t w u)
    + ((ContinuousLinearMap.mul ℝ ℂ) (deriv (deBruijnNewmanH t) w)).comp
      (ContinuousLinearMap.snd ℝ ℝ ℂ)

/-- Evaluation of `jointFDerivCLM`. -/
theorem jointFDerivCLM_apply (t : ℝ) (w : ℂ) (q : ℝ × ℂ) :
    jointFDerivCLM t w q
      = q.1 • (∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand t w u)
        + deriv (deBruijnNewmanH t) w * q.2 :=
  rfl

/-- **FTC representation**: the increment of `H` in `t` is the interval integral
of its time derivative, `H_t(w) − H_{t₀}(w) = ∫_{t₀}^{t} ∂_s H_s(w) ds`. The
integrand `∂_s H_s(w)` is jointly continuous by
`continuous_deBruijnNewmanH_tderiv`. -/
theorem deBruijnNewmanH_sub_eq_intervalIntegral (t₀ t : ℝ) (w : ℂ) :
    deBruijnNewmanH t w - deBruijnNewmanH t₀ w
      = ∫ s : ℝ in t₀..t, ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand s w u := by
  have hDcont : Continuous fun s : ℝ =>
      ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand s w u :=
    continuous_deBruijnNewmanH_tderiv.comp (continuous_id.prodMk continuous_const)
  have hint : IntervalIntegrable (deriv fun s : ℝ => deBruijnNewmanH s w)
      MeasureTheory.volume t₀ t := by
    rw [show deriv (fun s : ℝ => deBruijnNewmanH s w)
        = fun s : ℝ => ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand s w u
        from funext fun s => (hasDerivAt_deBruijnNewmanH_t w s).deriv]
    exact hDcont.continuousOn.intervalIntegrable
  have h2 : ∫ s : ℝ in t₀..t, ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand s w u
      = deBruijnNewmanH t w - deBruijnNewmanH t₀ w := by
    rw [intervalIntegral.integral_congr
      fun s _ => ((hasDerivAt_deBruijnNewmanH_t w s).deriv).symm]
    exact intervalIntegral.integral_deriv_eq_sub
      (fun x _ => (hasDerivAt_deBruijnNewmanH_t w x).differentiableAt) hint
  exact h2.symm

/-- **Joint differentiability**: `(t, z) ↦ H_t(z)` has the joint real Fréchet
derivative `jointFDerivCLM` at every point `p`. The defect
`H(q) − H(p) − L(q − p)` splits by FTC in each coordinate
(`deBruijnNewmanH_sub_eq_intervalIntegral`,
`deBruijnNewmanH_z_sub_eq_intervalIntegral`) into two interval integrals whose
integrands deviate from their values at `p` by at most `ε/2`
(joint continuity, `continuous_deBruijnNewmanH_tderiv` and
`continuous_deBruijnNewmanH_zderiv`), so the defect is `o(‖q − p‖)`. -/
theorem hasFDerivAt_deBruijnNewmanH_prod (p : ℝ × ℂ) :
    HasFDerivAt (fun q : ℝ × ℂ => deBruijnNewmanH q.1 q.2)
      (jointFDerivCLM p.1 p.2) p := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hcont₁ : ContinuousAt
      (fun r : ℝ × ℂ => ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand r.1 r.2 u) p :=
    continuous_deBruijnNewmanH_tderiv.continuousAt
  have hcont₂ : ContinuousAt (fun r : ℝ × ℂ => deriv (deBruijnNewmanH r.1) r.2) p :=
    continuous_deBruijnNewmanH_zderiv.continuousAt
  rw [Metric.continuousAt_iff] at hcont₁ hcont₂
  obtain ⟨δ₁, hδ₁0, hδ₁⟩ := hcont₁ (ε / 2) (half_pos hε)
  obtain ⟨δ₂, hδ₂0, hδ₂⟩ := hcont₂ (ε / 2) (half_pos hε)
  rw [Metric.eventually_nhds_iff_ball]
  refine ⟨min δ₁ δ₂, lt_min hδ₁0 hδ₂0, fun q hq => ?_⟩
  have hqδ1 : dist q p < δ₁ := lt_of_lt_of_le hq (min_le_left _ _)
  have hqδ2 : dist q p < δ₂ := lt_of_lt_of_le hq (min_le_right _ _)
  have hq1 : dist q.1 p.1 ≤ dist q p := by
    rw [Prod.dist_eq]; exact le_max_left _ _
  have hq2 : dist q.2 p.2 ≤ dist q p := by
    rw [Prod.dist_eq]; exact le_max_right _ _
  -- FTC split of the increment `H(q) − H(p)` into a `t`-piece and a `z`-piece
  have hsplit : deBruijnNewmanH q.1 q.2 - deBruijnNewmanH p.1 p.2
      = (∫ τ : ℝ in p.1..q.1,
          ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand τ q.2 u)
        + ∫ s : ℝ in (0:ℝ)..1,
          deriv (deBruijnNewmanH p.1) (p.2 + (s : ℂ) * (q.2 - p.2)) * (q.2 - p.2) := by
    have h1 := deBruijnNewmanH_sub_eq_intervalIntegral p.1 q.1 q.2
    have h2 := deBruijnNewmanH_z_sub_eq_intervalIntegral p.1 p.2 (q.2 - p.2)
    rw [add_sub_cancel] at h2
    calc deBruijnNewmanH q.1 q.2 - deBruijnNewmanH p.1 p.2
        = (deBruijnNewmanH q.1 q.2 - deBruijnNewmanH p.1 q.2)
          + (deBruijnNewmanH p.1 q.2 - deBruijnNewmanH p.1 p.2) := by ring
      _ = _ := by rw [h1, h2]
  change ‖deBruijnNewmanH q.1 q.2 - deBruijnNewmanH p.1 p.2
      - jointFDerivCLM p.1 p.2 (q - p)‖ ≤ ε * ‖q - p‖
  rw [hsplit, jointFDerivCLM_apply]
  -- the linear part as the same two interval integrals of constants
  have hconst₁ : (q - p).1 •
        (∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand p.1 p.2 u)
      = ∫ τ : ℝ in p.1..q.1,
        ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand p.1 p.2 u := by
    rw [Prod.fst_sub]
    exact (intervalIntegral.integral_const _).symm
  have hconst₂ : deriv (deBruijnNewmanH p.1) p.2 * (q - p).2
      = ∫ s : ℝ in (0:ℝ)..1, deriv (deBruijnNewmanH p.1) p.2 * (q.2 - p.2) := by
    rw [Prod.snd_sub, intervalIntegral.integral_const]
    simp
  rw [hconst₁, hconst₂]
  -- merge each pair of integrals into a single deviation integral
  have hintA : IntervalIntegrable
      (fun τ : ℝ => ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand τ q.2 u)
      MeasureTheory.volume p.1 q.1 :=
    (continuous_deBruijnNewmanH_tderiv.comp
      (continuous_id.prodMk continuous_const)).continuousOn.intervalIntegrable
  have hintA₀ : IntervalIntegrable
      (fun _ : ℝ => ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand p.1 p.2 u)
      MeasureTheory.volume p.1 q.1 := intervalIntegrable_const
  have hintB : IntervalIntegrable
      (fun s : ℝ =>
        deriv (deBruijnNewmanH p.1) (p.2 + (s : ℂ) * (q.2 - p.2)) * (q.2 - p.2))
      MeasureTheory.volume 0 1 :=
    ((continuous_deBruijnNewmanH_zderiv.comp
      (continuous_const.prodMk
        ((Complex.continuous_ofReal.mul continuous_const).const_add p.2))).mul
      continuous_const).continuousOn.intervalIntegrable
  have hintB₀ : IntervalIntegrable
      (fun _ : ℝ => deriv (deBruijnNewmanH p.1) p.2 * (q.2 - p.2))
      MeasureTheory.volume 0 1 := intervalIntegrable_const
  rw [add_sub_add_comm, ← intervalIntegral.integral_sub hintA hintA₀,
    ← intervalIntegral.integral_sub hintB hintB₀]
  -- pointwise deviation bounds along the two segments
  have hA : ∀ τ ∈ Set.uIoc p.1 q.1,
      ‖(∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand τ q.2 u)
          - ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand p.1 p.2 u‖
        ≤ ε / 2 := by
    intro τ hτ
    have hτ1 : dist τ p.1 ≤ dist q.1 p.1 := by
      rw [Real.dist_eq, Real.dist_eq]
      rcases Set.mem_uIcc.mp (Set.uIoc_subset_uIcc hτ) with h | h
      · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ τ - p.1),
            abs_of_nonneg (by linarith : (0:ℝ) ≤ q.1 - p.1)]
        linarith [h.2]
      · rw [abs_of_nonpos (by linarith : τ - p.1 ≤ (0:ℝ)),
            abs_of_nonpos (by linarith : q.1 - p.1 ≤ (0:ℝ))]
        linarith [h.1]
    have hdist : dist (τ, q.2) p < δ₁ := by
      have h1 : dist (τ, q.2) p = max (dist τ p.1) (dist q.2 p.2) := rfl
      rw [h1]
      exact max_lt_iff.mpr ⟨lt_of_le_of_lt (le_trans hτ1 hq1) hqδ1,
        lt_of_le_of_lt hq2 hqδ1⟩
    have hlt := hδ₁ hdist
    rw [dist_eq_norm] at hlt
    exact le_of_lt hlt
  have hB : ∀ s ∈ Set.uIoc (0:ℝ) 1,
      ‖deriv (deBruijnNewmanH p.1) (p.2 + (s : ℂ) * (q.2 - p.2)) * (q.2 - p.2)
          - deriv (deBruijnNewmanH p.1) p.2 * (q.2 - p.2)‖
        ≤ ε / 2 * ‖q.2 - p.2‖ := by
    intro s hs
    have hs01 : 0 ≤ s ∧ s ≤ 1 := by
      rcases Set.mem_uIcc.mp (Set.uIoc_subset_uIcc hs) with h | h
      · exact ⟨h.1, h.2⟩
      · exact ⟨by linarith [h.2], by linarith [h.1]⟩
    have hsabs : |s| ≤ 1 := abs_le.mpr ⟨by linarith [hs01.1], hs01.2⟩
    have hdist : dist (p.1, p.2 + (s : ℂ) * (q.2 - p.2)) p < δ₂ := by
      have h1 : dist (p.1, p.2 + (s : ℂ) * (q.2 - p.2)) p
          = max (dist p.1 p.1) (dist (p.2 + (s : ℂ) * (q.2 - p.2)) p.2) := rfl
      have hcomp : dist (p.2 + (s : ℂ) * (q.2 - p.2)) p.2
          = ‖(s : ℂ) * (q.2 - p.2)‖ := by
        rw [dist_eq_norm]
        congr 1
        ring
      have hle : ‖(s : ℂ) * (q.2 - p.2)‖ ≤ dist q p := by
        calc ‖(s : ℂ) * (q.2 - p.2)‖ = |s| * ‖q.2 - p.2‖ := by
              rw [norm_mul]
              congr 1
              exact RCLike.norm_ofReal (K := ℂ) s
          _ ≤ 1 * ‖q.2 - p.2‖ := mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)
          _ = ‖q.2 - p.2‖ := one_mul _
          _ = dist q.2 p.2 := (dist_eq_norm _ _).symm
          _ ≤ dist q p := hq2
      rw [h1, dist_self, hcomp]
      exact max_lt_iff.mpr ⟨hδ₂0, lt_of_le_of_lt hle hqδ2⟩
    rw [← sub_mul, norm_mul]
    have hlt : ‖deriv (deBruijnNewmanH p.1) (p.2 + (s : ℂ) * (q.2 - p.2))
        - deriv (deBruijnNewmanH p.1) p.2‖ < ε / 2 := by
      have hlt := hδ₂ hdist
      rw [dist_eq_norm] at hlt
      exact hlt
    exact mul_le_mul_of_nonneg_right (le_of_lt hlt) (norm_nonneg _)
  have hboundA := intervalIntegral.norm_integral_le_of_norm_le_const hA
  have hboundB := intervalIntegral.norm_integral_le_of_norm_le_const hB
  calc ‖(∫ τ : ℝ in p.1..q.1,
            (∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand τ q.2 u)
            - ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand p.1 p.2 u)
        + ∫ s : ℝ in (0:ℝ)..1,
          (deriv (deBruijnNewmanH p.1) (p.2 + (s : ℂ) * (q.2 - p.2)) * (q.2 - p.2)
            - deriv (deBruijnNewmanH p.1) p.2 * (q.2 - p.2))‖
      ≤ ‖∫ τ : ℝ in p.1..q.1,
          (∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand τ q.2 u)
          - ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand p.1 p.2 u‖
        + ‖∫ s : ℝ in (0:ℝ)..1,
          (deriv (deBruijnNewmanH p.1) (p.2 + (s : ℂ) * (q.2 - p.2)) * (q.2 - p.2)
            - deriv (deBruijnNewmanH p.1) p.2 * (q.2 - p.2))‖ := norm_add_le _ _
    _ ≤ (ε / 2) * |q.1 - p.1| + (ε / 2 * ‖q.2 - p.2‖) * |1 - (0:ℝ)| :=
        add_le_add hboundA hboundB
    _ = ε / 2 * |q.1 - p.1| + ε / 2 * ‖q.2 - p.2‖ := by norm_num
    _ ≤ ε / 2 * ‖q - p‖ + ε / 2 * ‖q - p‖ :=
        add_le_add
          (mul_le_mul_of_nonneg_left
            (by
              rw [← Real.dist_eq]
              exact hq1.trans_eq (dist_eq_norm q p))
            (le_of_lt (half_pos hε)))
          (mul_le_mul_of_nonneg_left
            ((dist_eq_norm q.2 p.2).symm.trans_le (hq2.trans_eq (dist_eq_norm q p)))
            (le_of_lt (half_pos hε)))
    _ = ε * ‖q - p‖ := by ring

/-- **Continuity of the joint derivative**: `p ↦ jointFDerivCLM p` is
continuous in the operator-norm topology, assembled from
`continuous_deBruijnNewmanH_tderiv` and `continuous_deBruijnNewmanH_zderiv`
through the continuous rank-one trilinear map `smulRightL` and the continuous
composition bilinear map. -/
theorem continuous_jointFDerivCLM :
    Continuous fun p : ℝ × ℂ => jointFDerivCLM p.1 p.2 := by
  have ht : Continuous fun p : ℝ × ℂ =>
      (ContinuousLinearMap.fst ℝ ℝ ℂ).smulRight
        (∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand p.1 p.2 u) := by
    apply ((ContinuousLinearMap.smulRightL ℝ (ℝ × ℂ) ℂ
      (ContinuousLinearMap.fst ℝ ℝ ℂ)).continuous.comp
      continuous_deBruijnNewmanH_tderiv).congr
    intro p
    refine ContinuousLinearMap.ext fun q => ?_
    rfl
  have hz : Continuous fun p : ℝ × ℂ =>
      ((ContinuousLinearMap.mul ℝ ℂ) (deriv (deBruijnNewmanH p.1) p.2)).comp
        (ContinuousLinearMap.snd ℝ ℝ ℂ) :=
    ((ContinuousLinearMap.mul ℝ ℂ).continuous.comp
      continuous_deBruijnNewmanH_zderiv).clm_comp continuous_const
  exact ht.add hz

/-- **Joint strict differentiability**: over `ℝ`, a continuously differentiable
function is strictly differentiable, so `(t, z) ↦ H_t(z)` is strictly
differentiable at every point with derivative `jointFDerivCLM`. This is the
hypothesis package for the implicit function theorem along zero curves. -/
theorem hasStrictFDerivAt_deBruijnNewmanH_prod (p : ℝ × ℂ) :
    HasStrictFDerivAt (fun q : ℝ × ℂ => deBruijnNewmanH q.1 q.2)
      (jointFDerivCLM p.1 p.2) p :=
  hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    (Filter.Eventually.of_forall fun q => hasFDerivAt_deBruijnNewmanH_prod q)
    continuous_jointFDerivCLM.continuousAt

/-- **Diagonal derivative — the zero-transport piece**: if `z(t) → z₀` as
`t → t₀`, then `t ↦ H_t(z(t)) − H_{t₀}(z(t))` has derivative `∂_t H_{t₀}(z₀)`
(the `u²`-weighted heat integral) at `t₀`. Proof: the FTC representation
`deBruijnNewmanH_sub_eq_intervalIntegral` writes the increment as an interval
integral of `s ↦ ∂_s H_s(z(t))`; joint continuity of the time derivative
(`continuous_deBruijnNewmanH_tderiv`) keeps the integrand within `ε/2` of its
value at `(t₀, z₀)` along the whole interval, so the slope is within `ε` of
`∂_t H_{t₀}(z₀)`. This is the transport half of the chain rule for
`t ↦ H_t(z(t))` along a zero trajectory. -/
theorem hasDerivAt_deBruijnNewmanH_diag_sub (z : ℝ → ℂ) (z₀ : ℂ) (t₀ : ℝ)
    (hz : Filter.Tendsto z (nhds t₀) (nhds z₀)) :
    HasDerivAt (fun t : ℝ => deBruijnNewmanH t (z t) - deBruijnNewmanH t₀ (z t))
      (∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand t₀ z₀ u) t₀ := by
  rw [hasDerivAt_iff_tendsto_slope, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hDcont : ContinuousAt (fun p : ℝ × ℂ =>
      ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand p.1 p.2 u) (t₀, z₀) :=
    continuous_deBruijnNewmanH_tderiv.continuousAt
  rw [Metric.continuousAt_iff] at hDcont
  obtain ⟨δ, hδ0, hδ⟩ := hDcont (ε / 2) (half_pos hε)
  rw [Metric.tendsto_nhds_nhds] at hz
  obtain ⟨δ₁, hδ₁0, hδ₁⟩ := hz (δ / 2) (half_pos hδ0)
  refine ⟨min (δ / 2) δ₁, lt_min (half_pos hδ0) hδ₁0, ?_⟩
  intro t htne htd
  have ht1 : dist t t₀ < δ / 2 := lt_of_lt_of_le htd (min_le_left _ _)
  have ht2 : dist (z t) z₀ < δ / 2 := hδ₁ (lt_of_lt_of_le htd (min_le_right _ _))
  have htne' : t ≠ t₀ := by simpa using htne
  have htn0 : t - t₀ ≠ 0 := sub_ne_zero.mpr htne'
  have hDs : ∀ s : ℝ, s ∈ Set.uIoc t₀ t →
      ‖(∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand s (z t) u)
        - ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand t₀ z₀ u‖ ≤ ε / 2 := by
    intro s hsm
    have hst : dist s t₀ ≤ dist t t₀ := by
      rw [Real.dist_eq, Real.dist_eq]
      rcases Set.mem_uIcc.mp (Set.uIoc_subset_uIcc hsm) with h | h
      · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ s - t₀),
            abs_of_nonneg (by linarith : (0:ℝ) ≤ t - t₀)]
        linarith [h.2]
      · rw [abs_of_nonpos (by linarith : s - t₀ ≤ (0:ℝ)),
            abs_of_nonpos (by linarith : t - t₀ ≤ (0:ℝ))]
        linarith [h.1]
    have hpair : dist (s, z t) (t₀, z₀) < δ := by
      rw [Prod.dist_eq, max_lt_iff]
      show dist s t₀ < δ ∧ dist (z t) z₀ < δ
      exact ⟨lt_of_le_of_lt hst (by linarith [ht1]),
        (by linarith [ht2] : dist (z t) z₀ < δ)⟩
    have hthis := hδ hpair
    rw [dist_eq_norm] at hthis
    exact hthis.le
  have hR : ‖∫ s : ℝ in t₀..t,
        ((∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand s (z t) u)
          - ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand t₀ z₀ u)‖
      ≤ (ε / 2) * |t - t₀| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun s hsm => hDs s hsm
  have hF : slope (fun t : ℝ => deBruijnNewmanH t (z t) - deBruijnNewmanH t₀ (z t)) t₀ t
      = (t - t₀)⁻¹ • (deBruijnNewmanH t (z t) - deBruijnNewmanH t₀ (z t)) := by
    show (t - t₀)⁻¹ • ((deBruijnNewmanH t (z t) - deBruijnNewmanH t₀ (z t))
        - (deBruijnNewmanH t₀ (z t₀) - deBruijnNewmanH t₀ (z t₀))) = _
    rw [sub_self, sub_zero]
  have hdec : (t - t₀)⁻¹ • (∫ s : ℝ in t₀..t,
        ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand s (z t) u)
      - ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand t₀ z₀ u
      = (t - t₀)⁻¹ • (∫ s : ℝ in t₀..t,
          ((∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand s (z t) u)
            - ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand t₀ z₀ u)) := by
    have hI1 : IntervalIntegrable (fun s : ℝ =>
          ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand s (z t) u)
        MeasureTheory.volume t₀ t :=
      (continuous_deBruijnNewmanH_tderiv.comp
        (continuous_id.prodMk continuous_const)).continuousOn.intervalIntegrable
    rw [intervalIntegral.integral_sub hI1 intervalIntegrable_const,
      intervalIntegral.integral_const]
    show (t - t₀)⁻¹ • (∫ s : ℝ in t₀..t, ∫ u : ℝ in Set.Ioi 0,
            ((u : ℂ) ^ 2) * heatIntegrand s (z t) u)
          - ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand t₀ z₀ u
        = (t - t₀)⁻¹ • ((∫ s : ℝ in t₀..t, ∫ u : ℝ in Set.Ioi 0,
            ((u : ℂ) ^ 2) * heatIntegrand s (z t) u)
          - (t - t₀) • ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand t₀ z₀ u)
    rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, RCLike.algebraMap_eq_ofReal,
      RCLike.ofReal_inv, mul_sub, ← mul_assoc,
      inv_mul_cancel₀ (RCLike.ofReal_ne_zero (K := ℂ).mpr htn0), one_mul]
  rw [dist_eq_norm, hF, deBruijnNewmanH_sub_eq_intervalIntegral t₀ t (z t), hdec,
    Algebra.smul_def, RCLike.algebraMap_eq_ofReal, norm_mul, RCLike.norm_ofReal, abs_inv]
  calc |t - t₀|⁻¹ * ‖∫ s : ℝ in t₀..t,
          ((∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand s (z t) u)
            - ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand t₀ z₀ u)‖
      ≤ |t - t₀|⁻¹ * ((ε / 2) * |t - t₀|) :=
        mul_le_mul_of_nonneg_left hR (by positivity)
    _ = ε / 2 := by
        have h0 : |t - t₀| ≠ 0 := abs_ne_zero.mpr htn0
        rw [mul_comm |t - t₀|⁻¹ _, mul_assoc, mul_inv_cancel₀ h0, mul_one]
    _ < ε := half_lt_self hε

/-- **Diagonal chain rule**: along a differentiable curve `z : ℝ → ℂ`,
`t ↦ H_t(z(t))` is differentiable with derivative
`∂_t H_{t₀}(z(t₀)) + ∂_z H_{t₀}(z(t₀)) · ż`. Proof: split the diagonal as the
transport piece `t ↦ H_t(z(t)) − H_{t₀}(z(t))`
(`hasDerivAt_deBruijnNewmanH_diag_sub`) plus the frozen-time composition
`t ↦ H_{t₀}(z(t))` (ordinary one-variable chain rule). -/
theorem hasDerivAt_deBruijnNewmanH_diag (z : ℝ → ℂ) (t₀ : ℝ) (ż : ℂ)
    (hz : HasDerivAt z ż t₀) :
    HasDerivAt (fun t : ℝ => deBruijnNewmanH t (z t))
      ((∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand t₀ (z t₀) u)
        + deriv (deBruijnNewmanH t₀) (z t₀) * ż) t₀ := by
  have h1 := hasDerivAt_deBruijnNewmanH_diag_sub z (z t₀) t₀
    hz.continuousAt.tendsto
  have h2 : HasDerivAt (fun t : ℝ => deBruijnNewmanH t₀ (z t))
      (deriv (deBruijnNewmanH t₀) (z t₀) * ż) t₀ :=
    (differentiable_deBruijnNewmanH t₀ (z t₀)).hasDerivAt.comp t₀ hz
  convert h1.add h2 using 2
  simp only [Pi.add_apply, sub_add_cancel]

/-- **Zero-trajectory velocity (implicit differentiation)**: if a differentiable
curve `z : ℝ → ℂ` rides on the zero set of the de Bruijn–Newman family near
`t₀` (`H_t(z(t)) = 0` eventually) and `∂_z H_{t₀}` does not vanish at `z(t₀)`,
then its velocity at `t₀` is `ż = −(∂_t H)/(∂_z H)`. Proof: the diagonal
derivative (`hasDerivAt_deBruijnNewmanH_diag`) must vanish since the diagonal
is eventually the constant zero function, and field algebra isolates `ż`. -/
theorem deBruijnNewman_zero_velocity (z : ℝ → ℂ) (t₀ : ℝ) (ż : ℂ)
    (hz : HasDerivAt z ż t₀)
    (hzero : (fun t : ℝ => deBruijnNewmanH t (z t)) =ᶠ[nhds t₀] 0)
    (hderiv : deriv (deBruijnNewmanH t₀) (z t₀) ≠ 0) :
    ż = -(∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand t₀ (z t₀) u)
      / deriv (deBruijnNewmanH t₀) (z t₀) := by
  have hF0 : HasDerivAt (fun t : ℝ => deBruijnNewmanH t (z t)) 0 t₀ :=
    (Filter.EventuallyEq.hasDerivAt_iff hzero).mpr (hasDerivAt_const t₀ (0 : ℂ))
  have huniq := (hasDerivAt_deBruijnNewmanH_diag z t₀ ż hz).unique hF0
  have hDz : deriv (deBruijnNewmanH t₀) (z t₀) * ż
      = -(∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand t₀ (z t₀) u) :=
    eq_neg_of_add_eq_zero_right huniq
  calc ż = (deriv (deBruijnNewmanH t₀) (z t₀))⁻¹
          * (deriv (deBruijnNewmanH t₀) (z t₀) * ż) := by
        rw [← mul_assoc, inv_mul_cancel₀ hderiv, one_mul]
    _ = (deriv (deBruijnNewmanH t₀) (z t₀))⁻¹
          * (-(∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand t₀ (z t₀) u)) := by
        rw [hDz]
    _ = -(∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand t₀ (z t₀) u)
          / deriv (deBruijnNewmanH t₀) (z t₀) := by
        rw [div_eq_mul_inv, mul_comm]

/-- **Velocity in backward-heat form**: under the hypotheses of
`deBruijnNewman_zero_velocity`, the trajectory velocity at `t₀` is
`ż = (∂²_z H)/(∂_z H)`, via the backward heat equation
`backward_heat_equation` (`∂_t H = −∂²_z H`). This is the de Bruijn zero
velocity `dx/dt = H''/H'` at simple zeros. -/
theorem deBruijnNewman_zero_velocity_heat (z : ℝ → ℂ) (t₀ : ℝ) (ż : ℂ)
    (hz : HasDerivAt z ż t₀)
    (hzero : (fun t : ℝ => deBruijnNewmanH t (z t)) =ᶠ[nhds t₀] 0)
    (hderiv : deriv (deBruijnNewmanH t₀) (z t₀) ≠ 0) :
    ż = iteratedDeriv 2 (deBruijnNewmanH t₀) (z t₀)
      / deriv (deBruijnNewmanH t₀) (z t₀) := by
  have hA : ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand t₀ (z t₀) u
      = - iteratedDeriv 2 (deBruijnNewmanH t₀) (z t₀) :=
    (hasDerivAt_deBruijnNewmanH_t (z t₀) t₀).deriv.symm.trans
      (backward_heat_equation t₀ (z t₀))
  have hv := deBruijnNewman_zero_velocity z t₀ ż hz hzero hderiv
  rw [hA] at hv
  simp only [neg_neg] at hv
  exact hv

/-- **Zero persistence (Rouché core) via the maximum modulus principle**:
if `f` vanishes at `w` with `‖f‖ ≥ m > 0` on the sphere of radius `ρ`
around `w`, and `g` is uniformly within `m / 2` of `f` on that sphere, then
`g` has a zero inside the ball. Classical `f/g` argument: otherwise
`φ = f/g − 1` is DiffContOnCl with `‖φ‖ < 1` on the sphere while
`‖φ(w)‖ = 1`, contradicting the maximum modulus principle. This bypasses
the argument principle, which is not in Mathlib. -/
theorem exists_zero_of_norm_sub_lt {f g : ℂ → ℂ} {w : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hf : DiffContOnCl ℂ f (Metric.ball w ρ))
    (hg : DiffContOnCl ℂ g (Metric.ball w ρ))
    (hfw : f w = 0) {m : ℝ} (hm : ∀ z ∈ Metric.sphere w ρ, m ≤ ‖f z‖)
    (hm0 : 0 < m) (hfg : ∀ z ∈ Metric.sphere w ρ, ‖f z - g z‖ < m / 2) :
    ∃ z ∈ Metric.ball w ρ, g z = 0 := by
  by_contra hcon
  push_neg at hcon
  have hcl : closure (Metric.ball w ρ) = Metric.closedBall w ρ :=
    closure_ball w hρ.ne'
  have hgne : ∀ z ∈ Metric.closedBall w ρ, g z ≠ 0 := by
    intro z hz
    rcases eq_or_ne (dist z w) ρ with h | h
    · have hs : z ∈ Metric.sphere w ρ := by
        rw [Metric.mem_sphere]; exact h
      have h1 : ‖f z‖ ≤ ‖f z - g z‖ + ‖g z‖ := by
        calc ‖f z‖ = ‖(f z - g z) + g z‖ := by rw [sub_add_cancel]
          _ ≤ ‖f z - g z‖ + ‖g z‖ := norm_add_le _ _
      have h2 : 0 < ‖g z‖ := by
        have h3 := hm z hs
        have h4 := hfg z hs
        linarith
      exact norm_pos_iff.mp h2
    · have hz' : z ∈ Metric.ball w ρ := by
        rw [Metric.mem_closedBall] at hz
        rw [Metric.mem_ball]
        exact lt_of_le_of_ne hz h
      exact hcon z hz'
  have hφ : DiffContOnCl ℂ (fun z => f z / g z - 1) (Metric.ball w ρ) := by
    refine ⟨(hf.differentiableOn.div hg.differentiableOn
      fun z hz => hgne z (Metric.ball_subset_closedBall hz)).sub_const 1, ?_⟩
    rw [hcl]
    exact ContinuousOn.sub ((hcl ▸ hf.continuousOn).div (hcl ▸ hg.continuousOn)
      fun z hz => hgne z hz) continuousOn_const
  have hsph : IsCompact (Metric.sphere w ρ) := isCompact_sphere w ρ
  have hsne : (Metric.sphere w ρ).Nonempty := by
    refine ⟨w + (ρ : ℂ), ?_⟩
    rw [Metric.mem_sphere, dist_eq_norm]
    have hw' : w + (ρ : ℂ) - w = (ρ : ℂ) := by ring
    calc ‖w + (ρ : ℂ) - w‖ = ‖(ρ : ℂ)‖ := by rw [hw']
      _ = ‖ρ‖ := RCLike.norm_ofReal ρ
      _ = ρ := by rw [Real.norm_eq_abs, abs_of_nonneg hρ.le]
  obtain ⟨z₀, hz₀, hmax⟩ := hsph.exists_isMaxOn hsne
    (hφ.continuousOn.norm.mono (by
      rw [hcl]
      exact Metric.sphere_subset_closedBall))
  set C := ‖f z₀ / g z₀ - 1‖ with hC
  have hgn : 0 < ‖g z₀‖ := by
    have h3 := hm z₀ hz₀
    have h4 := hfg z₀ hz₀
    have h1 : ‖f z₀‖ ≤ ‖f z₀ - g z₀‖ + ‖g z₀‖ := by
      calc ‖f z₀‖ = ‖(f z₀ - g z₀) + g z₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖f z₀ - g z₀‖ + ‖g z₀‖ := norm_add_le _ _
    linarith
  have hC1 : C < 1 := by
    have heq : f z₀ / g z₀ - 1 = (f z₀ - g z₀) / g z₀ := by
      rw [← div_self (norm_pos_iff.mp hgn), ← sub_div]
    have h3 := hm z₀ hz₀
    have h4 := hfg z₀ hz₀
    have h1 : ‖f z₀‖ ≤ ‖f z₀ - g z₀‖ + ‖g z₀‖ := by
      calc ‖f z₀‖ = ‖(f z₀ - g z₀) + g z₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖f z₀ - g z₀‖ + ‖g z₀‖ := norm_add_le _ _
    rw [hC, heq, norm_div, div_lt_one hgn]
    linarith
  have hle : ∀ z ∈ frontier (Metric.ball w ρ), ‖f z / g z - 1‖ ≤ C := by
    intro z hz
    rw [frontier_ball w hρ.ne'] at hz
    exact hmax hz
  have hwmax := Complex.norm_le_of_forall_mem_frontier_norm_le
    Metric.isBounded_ball hφ hle
    (show w ∈ closure (Metric.ball w ρ) from by
      rw [hcl]
      exact Metric.mem_closedBall_self hρ.le)
  rw [hfw] at hwmax
  have h1 : ‖(0 : ℂ) / g w - 1‖ = 1 := by simp
  rw [h1] at hwmax
  linarith

/-- **Hurwitz zero persistence** for the de Bruijn–Newman family: if `H_{t₀}` vanishes
at `w` and has no other zero in the closed ball `closedBall w ρ` (the isolation
hypothesis), then along any sequence `t n → t₀`, eventually `H_{t n}` has a zero in
the open ball `ball w ρ`. Proof: `‖H_{t₀}‖` attains a positive minimum `m` on the
compact boundary sphere; local uniform convergence of `H_t` to `H_{t₀}` makes
`‖H_{t₀} - H_{t n}‖ < m / 2` on the sphere eventually, and
`exists_zero_of_norm_sub_lt` (the maximum-modulus Rouché core) produces the zero. -/
theorem hurwitz_exists_zero_ball {t₀ : ℝ} {t : ℕ → ℝ} {w : ℂ} {ρ : ℝ}
    (ht : Filter.Tendsto t Filter.atTop (nhds t₀)) (hfw : deBruijnNewmanH t₀ w = 0)
    (hρ : 0 < ρ)
    (hiso : ∀ z ∈ Metric.closedBall w ρ, z ≠ w → deBruijnNewmanH t₀ z ≠ 0) :
    ∀ᶠ n in Filter.atTop, ∃ z ∈ Metric.ball w ρ, deBruijnNewmanH (t n) z = 0 := by
  have hcont : ContinuousOn (fun z => ‖deBruijnNewmanH t₀ z‖) (Metric.sphere w ρ) :=
    (differentiable_deBruijnNewmanH t₀).continuous.continuousOn.norm
  obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_sphere w ρ).exists_isMinOn
    ⟨w + (ρ : ℂ), by
      rw [Metric.mem_sphere, dist_eq_norm]
      have hw' : w + (ρ : ℂ) - w = (ρ : ℂ) := by ring
      calc ‖w + (ρ : ℂ) - w‖ = ‖(ρ : ℂ)‖ := by rw [hw']
        _ = ‖ρ‖ := RCLike.norm_ofReal ρ
        _ = ρ := by rw [Real.norm_eq_abs, abs_of_nonneg hρ.le]⟩ hcont
  have hm0 : 0 < ‖deBruijnNewmanH t₀ z₀‖ := by
    rw [norm_pos_iff]
    apply hiso z₀ (Metric.sphere_subset_closedBall hz₀)
    intro h
    rw [h, Metric.mem_sphere, dist_self] at hz₀
    exact hρ.ne' hz₀.symm
  have hunif : TendstoUniformlyOn (fun t : ℝ => deBruijnNewmanH t) (deBruijnNewmanH t₀)
      (nhds t₀) (Metric.sphere w ρ) :=
    tendstoLocallyUniformly_iff_forall_isCompact.mp
      (tendstoLocallyUniformly_deBruijnNewmanH t₀) _ (isCompact_sphere w ρ)
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  refine (ht.eventually (hunif _ (half_pos hm0))).mono fun n hn => ?_
  exact exists_zero_of_norm_sub_lt hρ
    (differentiable_deBruijnNewmanH t₀).diffContOnCl
    (differentiable_deBruijnNewmanH (t n)).diffContOnCl hfw
    (fun z hz => hmin hz) hm0
    (fun z hz => by
      have h' := hn z hz
      rw [dist_eq_norm] at h'
      exact h')

/-- The property `AllZerosReal` is closed under limits of the parameter: if
`t n → t₀` and every `H_{t n}` has only real zeros, then so does `H_{t₀}` (assuming
`H_{t₀}` is not identically zero). Proof: a non-real zero `z` of `H_{t₀}` would be
isolated (the analytic identity theorem, with global non-degeneracy ruling out the
locally-zero alternative), so Hurwitz persistence `hurwitz_exists_zero_ball` places a
zero of `H_{t n}` within `|z.im| / 2` of `z` for some `n` — necessarily non-real,
contradicting `AllZerosReal (t n)`. -/
theorem allZerosReal_of_tendsto {t₀ : ℝ} {t : ℕ → ℝ}
    (ht : Filter.Tendsto t Filter.atTop (nhds t₀))
    (hfn : ∃ z : ℂ, deBruijnNewmanH t₀ z ≠ 0)
    (hAZR : ∀ n : ℕ, AllZerosReal (t n)) : AllZerosReal t₀ := by
  intro z hz
  by_contra him
  have hAnOn : AnalyticOnNhd ℂ (deBruijnNewmanH t₀) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (differentiable_deBruijnNewmanH t₀)
  have hAn : AnalyticAt ℂ (deBruijnNewmanH t₀) z := hAnOn z (Set.mem_univ z)
  rcases hAn.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · obtain ⟨z', hz'⟩ := hfn
    exact hz' (by
      have heq := hAnOn.eqOn_zero_of_preconnected_of_frequently_eq_zero
        isPreconnected_univ (Set.mem_univ z)
        (hzero.filter_mono nhdsWithin_le_nhds).frequently
      simpa using heq (Set.mem_univ z'))
  · have hne' := eventually_nhdsWithin_iff.mp hne
    obtain ⟨ρ₀, hρ₀, hρ₀'⟩ := Metric.eventually_nhds_iff_ball.mp hne'
    set r := min (ρ₀ / 2) (|z.im| / 2) with hr
    have hr0 : 0 < r := lt_min (half_pos hρ₀) (half_pos (abs_pos.mpr him))
    have hiso : ∀ w ∈ Metric.closedBall z r, w ≠ z → deBruijnNewmanH t₀ w ≠ 0 := by
      intro w hw hwxz
      apply hρ₀' w ?_ (by simpa using hwxz)
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt (Metric.mem_closedBall.mp hw)
        (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hρ₀))
    obtain ⟨n, w, hwball, hwz⟩ := (hurwitz_exists_zero_ball ht hz hr0 hiso).exists
    have hwim : w.im = 0 := hAZR n w hwz
    have hclose : |w.im - z.im| < |z.im| / 2 := by
      have h1 : |w.im - z.im| ≤ ‖w - z‖ := by
        rw [show w.im - z.im = (w - z).im from by simp]
        exact Complex.abs_im_le_norm (w - z)
      have h2 : ‖w - z‖ < r := by
        rw [← dist_eq_norm]
        exact Metric.mem_ball.mp hwball
      exact lt_of_le_of_lt h1 (lt_of_lt_of_le h2 (min_le_right _ _))
    rw [hwim, zero_sub, abs_neg] at hclose
    exact (not_lt.mpr (half_le_self (abs_nonneg z.im))) hclose

/-- `H_0` is not identically zero: at `z = -i` it equals
`(1/8)·ξ(1) = 1/16`. This is the non-degeneracy hypothesis needed for any
Hurwitz-type zero-persistence argument at `t = 0`. -/
theorem deBruijnNewmanH_zero_exists_ne_zero :
    ∃ z : ℂ, deBruijnNewmanH 0 z ≠ 0 := by
  have hξ : RiemannHypothesis.completedZeta 1 = 1 / 2 := by
    unfold RiemannHypothesis.completedZeta
    norm_num
  have hz : (1 : ℂ) / 2 + Complex.I * (-Complex.I / 2) = 1 := by
    have h1 : Complex.I * (-Complex.I / 2) = 1 / 2 := by
      rw [show Complex.I * (-Complex.I / 2) = -(Complex.I * Complex.I) / 2 from by ring,
        Complex.I_mul_I]
      ring
    rw [h1]
    ring
  use -Complex.I
  rw [deBruijnNewmanH_zero_eq_completedZeta, hz, hξ]
  norm_num

/-! ## Phase 2(viii)：零点实性集合的闭性与条件版收官 -/

/-- The zero-reality set `{t | AllZerosReal t}` is closed in `ℝ`: sequential
closedness is `allZerosReal_of_tendsto` (non-degeneracy at the limit time from
`deBruijnNewmanH_exists_ne_zero`), and `ℝ` is a sequential space. -/
theorem isClosed_allZerosReal : IsClosed {t : ℝ | AllZerosReal t} := by
  apply IsSeqClosed.isClosed
  intro t t₀ htm htt₀
  exact allZerosReal_of_tendsto htt₀ (deBruijnNewmanH_exists_ne_zero t₀) htm

/-- If the zero-reality set is nonempty and bounded below, the infimum is a
member: `AllZerosReal Λ`. -/
theorem allZerosReal_lambda (hne : {t : ℝ | AllZerosReal t}.Nonempty)
    (hbdd : BddBelow {t : ℝ | AllZerosReal t}) : AllZerosReal deBruijnNewmanLambda :=
  isClosed_allZerosReal.csInf_mem hne hbdd

/-- If `AllZerosReal` holds at all positive times, it holds at `0`, via the
sequence `1/(n+1) ↓ 0` and Hurwitz closedness. -/
theorem allZerosReal_zero_of_forall_pos (h : ∀ t : ℝ, 0 < t → AllZerosReal t) :
    AllZerosReal 0 := by
  apply allZerosReal_of_tendsto (t := fun n : ℕ => ((n : ℝ) + 1)⁻¹) ?_
    (deBruijnNewmanH_exists_ne_zero 0) (fun n => h _ (by positivity))
  have h1 : Filter.Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  simpa using (Filter.tendsto_add_atTop_iff_nat (f := fun n : ℕ => ((n : ℝ))⁻¹) 1).mpr h1

/-- **Conditional de Bruijn step**: under monotonicity, `Λ ≤ 0` (with the
zero-reality set nonempty) gives `AllZerosReal s` for every positive `s`:
either `csInf_lt_iff` (bounded case) or bare unboundedness supplies a member
below `s`, and monotonicity lifts it to `s`. -/
theorem forall_pos_allZerosReal_of_lambda_le_zero_of_monotone
    (hmono : de_bruijn_monotone_target) (hne : {t : ℝ | AllZerosReal t}.Nonempty)
    (hΛ : deBruijnNewmanLambda ≤ 0) :
    ∀ s : ℝ, 0 < s → AllZerosReal s := by
  intro s hs
  have hlt : deBruijnNewmanLambda < s := lt_of_le_of_lt hΛ hs
  obtain ⟨t, ht, hts⟩ : ∃ t ∈ {t : ℝ | AllZerosReal t}, t < s := by
    by_cases hb : BddBelow {t : ℝ | AllZerosReal t}
    · exact (csInf_lt_iff hb hne).mp hlt
    · exact not_bddBelow_iff.mp hb s
  exact hmono ht hts.le

/-- **Conditional endpoint (Phase 2 target)**: under de Bruijn monotonicity and
nonemptiness of the zero-reality set, `RH ⇔ Λ ≤ 0`. The forward direction is
`lambda_le_zero_of_rh` (unconditional); the reverse lifts `Λ ≤ 0` through
monotonicity to all positive times and closes at `0` by Hurwitz. -/
theorem rh_iff_lambda_le_zero_of_monotone (hmono : de_bruijn_monotone_target)
    (hne : {t : ℝ | AllZerosReal t}.Nonempty) : rh_iff_lambda_le_zero_target := by
  constructor
  · exact lambda_le_zero_of_rh
  · intro hΛ
    apply statement_iff_allZerosReal_zero.mpr
    apply allZerosReal_zero_of_forall_pos
    exact forall_pos_allZerosReal_of_lambda_le_zero_of_monotone hmono hne hΛ

end DeBruijnNewman
end RiemannExplorer
