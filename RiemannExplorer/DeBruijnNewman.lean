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

/-- **The z-partial of the joint derivative**: composing `jointFDerivCLM`
with the right inclusion recovers multiplication by `∂_z H_t(w)`. -/
theorem jointFDerivCLM_comp_inr (t : ℝ) (w : ℂ) :
    (jointFDerivCLM t w).comp (ContinuousLinearMap.inr ℝ ℝ ℂ)
      = ContinuousLinearMap.mul ℝ ℂ (deriv (deBruijnNewmanH t) w) := by
  ext z
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    jointFDerivCLM_apply]
  simp

/-- **Invertibility of the z-partial at a simple zero**: if
`∂_z H_{t₀}(x₀) ≠ 0`, the z-component of the joint real derivative is an
invertible `ℝ`-linear map — the nondegeneracy hypothesis of the implicit
function theorem. The two-sided inverse is multiplication by
`(∂_z H_{t₀}(x₀))⁻¹`. -/
theorem isInvertible_jointFDerivCLM_comp_inr (t₀ : ℝ) (x₀ : ℂ)
    (hD : deriv (deBruijnNewmanH t₀) x₀ ≠ 0) :
    ((fderiv ℝ (fun q : ℝ × ℂ => deBruijnNewmanH q.1 q.2) (t₀, x₀)).comp
      (ContinuousLinearMap.inr ℝ ℝ ℂ)).IsInvertible := by
  have hfd : fderiv ℝ (fun q : ℝ × ℂ => deBruijnNewmanH q.1 q.2) (t₀, x₀)
      = jointFDerivCLM t₀ x₀ :=
    (hasFDerivAt_deBruijnNewmanH_prod (t₀, x₀)).fderiv
  rw [hfd, jointFDerivCLM_comp_inr]
  exact ⟨ContinuousLinearEquiv.equivOfInverse
    (ContinuousLinearMap.mul ℝ ℂ (deriv (deBruijnNewmanH t₀) x₀))
    (ContinuousLinearMap.mul ℝ ℂ (deriv (deBruijnNewmanH t₀) x₀)⁻¹)
    (fun z => inv_mul_cancel_left₀ hD z) (fun z => mul_inv_cancel_left₀ hD z), rfl⟩

/-- **Global `C¹` regularity**: `(t, z) ↦ H_t(z)` is `C¹` over `ℝ`, with
derivative `jointFDerivCLM`. -/
theorem contDiff_one_deBruijnNewmanH_prod :
    ContDiff ℝ 1 (fun q : ℝ × ℂ => deBruijnNewmanH q.1 q.2) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun q => (hasFDerivAt_deBruijnNewmanH_prod q).differentiableAt, ?_⟩
  rw [show (fderiv ℝ fun q : ℝ × ℂ => deBruijnNewmanH q.1 q.2)
      = fun q : ℝ × ℂ => jointFDerivCLM q.1 q.2
      from funext fun q => (hasFDerivAt_deBruijnNewmanH_prod q).fderiv]
  exact continuous_jointFDerivCLM

/-- **IFT zero trajectory through a simple real zero**: if `H_{t₀}(x₀) = 0`
with `x₀` real and `∂_z H_{t₀}(x₀) ≠ 0`, then near `(t₀, x₀)` the zero set of
`(t, z) ↦ H_t(z)` is a differentiable curve `t ↦ ψ(t)` through `x₀` which
stays real. Existence and uniqueness come from the implicit function theorem
(`ContDiffAt.implicitFunction`); reality of `ψ` follows from the conjugation
symmetry `H_t(\bar z) = \overline{H_t(z)}`: the conjugate curve is another
local zero through the same real point, so local uniqueness forces
`ψ(t) = \overline{ψ(t)}`. -/
theorem deBruijnNewman_simple_zero_trajectory (t₀ : ℝ) (x₀ : ℂ)
    (hz : deBruijnNewmanH t₀ x₀ = 0) (hD : deriv (deBruijnNewmanH t₀) x₀ ≠ 0)
    (hx : x₀.im = 0) :
    ∃ ψ : ℝ → ℂ, DifferentiableAt ℝ ψ t₀ ∧ ψ t₀ = x₀
      ∧ (∀ᶠ t in nhds t₀, deBruijnNewmanH t (ψ t) = 0)
      ∧ (∀ᶠ t in nhds t₀, (ψ t).im = 0)
      ∧ (∀ᶠ v in nhds (t₀, x₀), deBruijnNewmanH v.1 v.2 = 0 → v.2 = ψ v.1) := by
  have hCD : ContDiffAt ℝ 1 (fun q : ℝ × ℂ => deBruijnNewmanH q.1 q.2) (t₀, x₀) :=
    contDiff_one_deBruijnNewmanH_prod.contDiffAt
  have hInv := isInvertible_jointFDerivCLM_comp_inr t₀ x₀ hD
  have hstar : star x₀ = x₀ := by
    rw [Complex.star_def, Complex.conj_eq_iff_im]; exact hx
  set ψ := hCD.implicitFunction one_ne_zero hInv with hψ
  have hψCD : ContDiffAt ℝ 1 ψ t₀ := hCD.contDiffAt_implicitFunction one_ne_zero hInv
  have hψ0 : ψ t₀ = x₀ := hCD.implicitFunction_apply_self one_ne_zero hInv
  have hzero : ∀ᶠ t in nhds t₀, deBruijnNewmanH t (ψ t) = 0 := by
    have hev := hCD.eventually_apply_implicitFunction one_ne_zero hInv
    refine hev.mono fun t ht => ?_
    simp only [] at ht
    rwa [hz] at ht
  refine ⟨ψ, hψCD.differentiableAt one_ne_zero, hψ0, hzero, ?_, ?_⟩
  · -- reality via the conjugate curve and local uniqueness
    have htend : Filter.Tendsto (fun t : ℝ => (t, star (ψ t)))
        (nhds t₀) (nhds (t₀, x₀)) := by
      have h1 : ContinuousAt (fun t : ℝ => (t, star (ψ t))) t₀ :=
        continuousAt_id.prodMk
          (continuous_star.continuousAt.comp
            (hψCD.differentiableAt one_ne_zero).continuousAt)
      have h2 : (t₀, star (ψ t₀)) = (t₀, x₀) := by rw [hψ0, hstar]
      exact h2 ▸ h1.tendsto
    have huniq := htend.eventually
      (hCD.eventually_apply_eq_iff_implicitFunction one_ne_zero hInv)
    filter_upwards [huniq, hzero] with t ht hzt
    have hL : (fun q : ℝ × ℂ => deBruijnNewmanH q.1 q.2) (t, star (ψ t))
        = (fun q : ℝ × ℂ => deBruijnNewmanH q.1 q.2) (t₀, x₀) := by
      change deBruijnNewmanH t (star (ψ t)) = deBruijnNewmanH t₀ x₀
      rw [deBruijnNewmanH_conj, hzt, star_zero, hz]
    have him : ψ t = star (ψ t) := ht.mp hL
    rw [Complex.star_def] at him
    exact Complex.conj_eq_iff_im.mp him.symm
  · -- local uniqueness: any nearby zero lies on ψ
    refine (hCD.eventually_apply_eq_iff_implicitFunction one_ne_zero hInv).mono
      fun v hv hv0 => (hv.mp ?_).symm
    exact hv0.trans hz.symm

set_option maxHeartbeats 800000 in
/-- **Local propagation of zero reality (simple zeros, counting-free)**: if
every zero of `H_{t₀}` in a compact set `K` is real and simple, then all zeros
of `H_t` in `K` stay real for `t` near `t₀`. Proof by contradiction: a
sequence of non-real zeros in `K` subconverges to a zero of `H_{t₀}` in `K`
(joint continuity), which is real and simple, so the IFT trajectory is the
unique local zero curve — forcing the subsequence onto a real curve. No
zero-counting (argument principle) is needed: local uniqueness comes from the
implicit function theorem. -/
theorem deBruijnNewman_zeros_stay_real_on_compact (t₀ : ℝ) (K : Set ℂ)
    (hK : IsCompact K)
    (hreal : ∀ z ∈ K, deBruijnNewmanH t₀ z = 0 → z.im = 0)
    (hsimple : ∀ z ∈ K, deBruijnNewmanH t₀ z = 0 → deriv (deBruijnNewmanH t₀) z ≠ 0) :
    ∀ᶠ t in nhds t₀, ∀ z ∈ K, deBruijnNewmanH t z = 0 → z.im = 0 := by
  by_contra h
  rw [Filter.not_eventually] at h
  -- bad times `tₙ → t₀` carrying non-real zeros in `K`
  have hseq : ∀ n : ℕ, ∃ t : ℝ, dist t t₀ < 1 / (n + 1 : ℝ)
      ∧ ¬ (∀ z ∈ K, deBruijnNewmanH t z = 0 → z.im = 0) := by
    intro n
    have h1 : ∃ᶠ t in nhds t₀,
        ¬ (∀ z ∈ K, deBruijnNewmanH t z = 0 → z.im = 0)
        ∧ t ∈ Metric.ball t₀ (1 / (n + 1 : ℝ)) :=
      h.and_eventually (Metric.ball_mem_nhds t₀ (by positivity))
    rcases h1.exists with ⟨t, htP, htd⟩
    exact ⟨t, htd, htP⟩
  choose t htd htP using hseq
  have htT : Filter.Tendsto t Filter.atTop (nhds t₀) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    refine ⟨N, fun n hn => ?_⟩
    calc dist (t n) t₀ < 1 / (n + 1 : ℝ) := htd n
      _ ≤ 1 / (N + 1 : ℝ) := by
          apply one_div_le_one_div_of_le (by positivity)
          exact_mod_cast Nat.add_le_add_right hn 1
      _ < ε := hN
  have hzex : ∀ n : ℕ, ∃ z : ℂ, z ∈ K ∧ deBruijnNewmanH (t n) z = 0 ∧ z.im ≠ 0 := by
    intro n
    have h2 := htP n
    push Not at h2
    exact h2
  choose z hzK hz0 hzim using hzex
  obtain ⟨zstar, hzstarK, φ, hφ, hzT⟩ := hK.tendsto_subseq hzK
  -- the limit point is a zero of `H_{t₀}` in `K`
  have hcontF : Continuous fun q : ℝ × ℂ => deBruijnNewmanH q.1 q.2 :=
    contDiff_one_deBruijnNewmanH_prod.continuous
  have hpair : Filter.Tendsto (fun n => (t (φ n), z (φ n))) Filter.atTop (nhds (t₀, zstar)) :=
    (htT.comp (StrictMono.tendsto_atTop hφ)).prodMk_nhds hzT
  have hlim : Filter.Tendsto (fun n => deBruijnNewmanH (t (φ n)) (z (φ n))) Filter.atTop
      (nhds (deBruijnNewmanH t₀ zstar)) := (hcontF.tendsto (t₀, zstar)).comp hpair
  have h0 : Filter.Tendsto (fun n => deBruijnNewmanH (t (φ n)) (z (φ n))) Filter.atTop
      (nhds 0) :=
    Filter.Tendsto.congr (fun n => (hz0 (φ n)).symm) tendsto_const_nhds
  have hzstar0 : deBruijnNewmanH t₀ zstar = 0 := tendsto_nhds_unique hlim h0
  -- the IFT trajectory through the simple real zero `(t₀, zstar)`
  obtain ⟨ψ, _, _, _, hψreal, hψuniq⟩ :=
    deBruijnNewman_simple_zero_trajectory t₀ zstar hzstar0 (hsimple zstar hzstarK hzstar0)
      (hreal zstar hzstarK hzstar0)
  -- the subsequence lies on the real curve eventually: contradiction
  have hvin : ∀ᶠ n in Filter.atTop, (z (φ n)).im = 0 := by
    filter_upwards [hpair.eventually hψuniq,
      (htT.comp (StrictMono.tendsto_atTop hφ)).eventually hψreal] with n hn1 hn2
    have hn1' : z (φ n) = ψ (t (φ n)) := hn1 (hz0 (φ n))
    rw [hn1']
    exact hn2
  obtain ⟨n, hn⟩ := hvin.exists
  exact hzim (φ n) hn

/-- **The second `z`-derivative**: `∂²_z H_t(z)
= ∫₀^∞ (−u²) · e^{tu²} Φ(u) cos(zu) du`, from the dominated differentiation
`hasDerivAt_integral_heatIntegrandDeriv` and the first-derivative formula. -/
theorem deriv_two_deBruijnNewmanH (t : ℝ) (z : ℂ) :
    deriv (deriv (deBruijnNewmanH t)) z
      = ∫ u : ℝ in Set.Ioi 0, -((u : ℂ) ^ 2) * heatIntegrand t z u := by
  rw [show deriv (deBruijnNewmanH t)
      = fun w : ℂ => ∫ u : ℝ in Set.Ioi 0, heatIntegrandDeriv t w u
      from funext fun w => deriv_deBruijnNewmanH t w]
  exact (hasDerivAt_integral_heatIntegrandDeriv t z).deriv

/-- **The backward heat equation for `H`**: `∂²_z H_t(z)` equals minus the
`u²`-weighted heat integral, i.e. `∂²_z H = −∂_t H`. This is the PDE behind
the de Bruijn magic formula: at a double zero it forces the local model
`H_t(x) ≈ B·((x − x₀)²/2 − (t − t₀))`. -/
theorem deBruijnNewmanH_heat_equation (t : ℝ) (z : ℂ) :
    iteratedDeriv 2 (deBruijnNewmanH t) z
      = -(∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand t z u) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_two_deBruijnNewmanH]
  simp only [neg_mul, MeasureTheory.integral_neg]

/-- **The heat equation, PDE form**: `∂²_z H_t(z) = −∂_t H_t(z)` where the
time derivative is taken with `z` frozen. -/
theorem deBruijnNewmanH_heat_pde (t : ℝ) (z : ℂ) :
    iteratedDeriv 2 (deBruijnNewmanH t) z
      = -(deriv (fun s : ℝ => deBruijnNewmanH s z) t) := by
  rw [deBruijnNewmanH_heat_equation, (hasDerivAt_deBruijnNewmanH_t z t).deriv]

/-- **Joint continuity of `∂²_z H`**: by the heat equation it is minus the
time derivative, which is jointly continuous
(`continuous_deBruijnNewmanH_tderiv`). -/
theorem continuous_deBruijnNewmanH_zderiv_two :
    Continuous fun p : ℝ × ℂ => iteratedDeriv 2 (deBruijnNewmanH p.1) p.2 := by
  rw [show (fun p : ℝ × ℂ => iteratedDeriv 2 (deBruijnNewmanH p.1) p.2)
      = fun p : ℝ × ℂ =>
        -(∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand p.1 p.2 u)
      from funext fun p => deBruijnNewmanH_heat_equation p.1 p.2]
  exact continuous_deBruijnNewmanH_tderiv.neg

/-! ## Phase 2(viii)b：三阶 `z` 导数层（临界曲线预备） -/

/-- Variant of `heat_decay_eventually_le` carrying an extra factor `u³`
(absorbed via `u³ ≤ e^{3u}`). Used for the third `z`-derivative and the
mixed `t`-`z` derivative of the `H_t` integrand. -/
theorem heat_decay_eventually_le_mul3 (t a C : ℝ) (hC : 0 < C) (ha : 0 ≤ a) :
    ∀ᶠ u in Filter.atTop,
      C * u ^ 3 * Real.exp (t * u ^ 2 + a * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))
        ≤ Real.exp (-u) := by
  have hmain := heat_decay_eventually_le t (a + 3) C hC (by linarith)
  filter_upwards [hmain, Filter.eventually_ge_atTop 0] with u hu hu0
  have hule : u ≤ Real.exp u := by
    have h := Real.add_one_le_exp u
    linarith
  have hu3 : u ^ 3 ≤ Real.exp (3 * u) := by
    have huu : u * u ≤ Real.exp u * Real.exp u := mul_self_le_mul_self hu0 hule
    have h1 : u * u * u ≤ Real.exp u * Real.exp u * Real.exp u :=
      mul_le_mul huu hule hu0 (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
    have h2 : Real.exp u * Real.exp u * Real.exp u = Real.exp (3 * u) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc u ^ 3 = u * u * u := by ring
      _ ≤ Real.exp u * Real.exp u * Real.exp u := h1
      _ = Real.exp (3 * u) := h2
  calc C * u ^ 3 * Real.exp (t * u ^ 2 + a * u) * Real.exp (-(Real.pi * Real.exp (4 * u)))
      ≤ C * Real.exp (3 * u) * Real.exp (t * u ^ 2 + a * u)
          * Real.exp (-(Real.pi * Real.exp (4 * u))) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        exact mul_le_mul_of_nonneg_left hu3 (le_of_lt hC)
    _ = C * Real.exp (t * u ^ 2 + (a + 3) * u)
          * Real.exp (-(Real.pi * Real.exp (4 * u))) := by
        have he : Real.exp (3 * u) * Real.exp (t * u ^ 2 + a * u)
            = Real.exp (t * u ^ 2 + (a + 3) * u) := by
          rw [← Real.exp_add]
          congr 1
          ring
        have e1 : C * Real.exp (3 * u) * Real.exp (t * u ^ 2 + a * u)
            * Real.exp (-(Real.pi * Real.exp (4 * u)))
          = C * (Real.exp (3 * u) * Real.exp (t * u ^ 2 + a * u))
            * Real.exp (-(Real.pi * Real.exp (4 * u))) := by ring
        rw [e1, he]
    _ ≤ Real.exp (-u) := hu

/-- Dominating function for the third `z`-derivative (and the mixed
`t`-`z` derivative) of the `H_t` integrand:
`u ↦ (2π² + 3π) · K₁ · u³ · e^{t u² + (9 + c) u} · e^{−π e^{4u}}`. -/
noncomputable def heatCubeDominatingFun (t c : ℝ) (u : ℝ) : ℝ :=
  (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst * u ^ 3
    * Real.exp (t * u ^ 2 + (9 + c) * u)
    * Real.exp (-(Real.pi * Real.exp (4 * u)))

theorem continuous_heatCubeDominatingFun (t c : ℝ) :
    Continuous (heatCubeDominatingFun t c) := by
  unfold heatCubeDominatingFun
  fun_prop

theorem heatCubeDominatingFun_isBigO (t c : ℝ) (hc : 0 ≤ c) :
    Asymptotics.IsBigO Filter.atTop (heatCubeDominatingFun t c)
      fun u : ℝ => Real.exp (-(1:ℝ) * u) := by
  apply Asymptotics.IsBigO.of_bound'
  have hC0 : (0:ℝ) ≤ (2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst :=
    mul_nonneg (by positivity) phiTailConst_nonneg
  have h := heat_decay_eventually_le_mul3 t (9 + c)
    ((2 * Real.pi ^ 2 + 3 * Real.pi) * phiTailConst)
    (mul_pos (by positivity) phiTailConst_pos) (by linarith)
  filter_upwards [h, Filter.eventually_ge_atTop 0] with u hu hu0
  have hdom0 : 0 ≤ heatCubeDominatingFun t c u :=
    mul_nonneg (mul_nonneg (mul_nonneg hC0 (pow_nonneg hu0 3)) (Real.exp_nonneg _))
      (Real.exp_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hdom0, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_nonneg _), neg_mul, one_mul]
  exact hu

theorem integrableOn_heatCubeDominatingFun (t c : ℝ) (hc : 0 ≤ c) :
    MeasureTheory.IntegrableOn (heatCubeDominatingFun t c) (Set.Ioi 0)
      MeasureTheory.volume :=
  integrable_of_isBigO_exp_neg (show (0:ℝ) < 1 by norm_num)
    (continuous_heatCubeDominatingFun t c).continuousOn
    (heatCubeDominatingFun_isBigO t c hc)

/-- **Box bound for the twice-weighted `z`-derivative integrand**: for
`t ≤ t₁`, `|z.im| ≤ c` and `u ≥ 0`,
`‖u² · heatIntegrandDeriv t z u‖ ≤ heatCubeDominatingFun t₁ c u`. -/
theorem norm_sq_mul_heatIntegrandDeriv_le {t t₁ c : ℝ} (ht : t ≤ t₁) (hc : 0 ≤ c)
    {z : ℂ} (hzim : |z.im| ≤ c) {u : ℝ} (hu : 0 ≤ u) :
    ‖((u : ℂ) ^ 2) * heatIntegrandDeriv t z u‖ ≤ heatCubeDominatingFun t₁ c u := by
  have hn : ‖((u : ℂ) ^ 2) * heatIntegrandDeriv t z u‖
      = u ^ 2 * ‖heatIntegrandDeriv t z u‖ := by
    rw [norm_mul, norm_pow,
      show ‖(u : ℂ)‖ = u from by
        rw [show ‖(u : ℂ)‖ = |u| from RCLike.norm_ofReal u, abs_of_nonneg hu]]
  rw [hn]
  calc u ^ 2 * ‖heatIntegrandDeriv t z u‖
      ≤ u ^ 2 * heatDerivDominatingFun t₁ c u :=
        mul_le_mul_of_nonneg_left (norm_heatIntegrandDeriv_le ht hc hzim hu)
          (sq_nonneg u)
    _ = heatCubeDominatingFun t₁ c u := by
        unfold heatCubeDominatingFun heatDerivDominatingFun
        ring

/-- The third `z`-derivative of the integrand integral:
`(∫ −u² · heatIntegrand)' = ∫ −u² · heatIntegrandDeriv`. -/
theorem hasDerivAt_integral_negSq_heatIntegrand (t : ℝ) (z₀ : ℂ) :
    HasDerivAt (fun w : ℂ => ∫ u : ℝ in Set.Ioi 0, -(((u : ℝ) : ℂ) ^ 2) * heatIntegrand t w u)
      (∫ u : ℝ in Set.Ioi 0, -(((u : ℝ) : ℂ) ^ 2) * heatIntegrandDeriv t z₀ u) z₀ := by
  set μ := MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)) with hμ
  have hmeas : ∀ w : ℂ, MeasureTheory.AEStronglyMeasurable
      (fun u : ℝ => -(((u : ℝ) : ℂ) ^ 2) * heatIntegrand t w u) μ :=
    fun w => (((Complex.continuous_ofReal.pow 2).neg.mul
      (continuous_heatIntegrand t w)).continuousOn.aestronglyMeasurable
      measurableSet_Ioi)
  have hderv_meas : MeasureTheory.AEStronglyMeasurable
      (fun u : ℝ => -(((u : ℝ) : ℂ) ^ 2) * heatIntegrandDeriv t z₀ u) μ :=
    (((Complex.continuous_ofReal.pow 2).neg.mul
      (continuous_heatIntegrandDeriv t z₀)).continuousOn.aestronglyMeasurable
      measurableSet_Ioi)
  have hbound : ∀ᵐ u ∂μ, ∀ w ∈ Metric.ball z₀ 1,
      ‖-(((u : ℝ) : ℂ) ^ 2) * heatIntegrandDeriv t w u‖
        ≤ heatCubeDominatingFun t (|z₀.im| + 1) u := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu w hw
    rw [neg_mul, norm_neg]
    exact norm_sq_mul_heatIntegrandDeriv_le (t := t) (t₁ := t) (c := |z₀.im| + 1)
      (le_refl t) (by positivity)
      (abs_im_le_add_one_of_dist_lt_one (Metric.mem_ball.mp hw)) hu.le
  have hint : MeasureTheory.Integrable (heatCubeDominatingFun t (|z₀.im| + 1)) μ :=
    integrableOn_heatCubeDominatingFun t (|z₀.im| + 1) (by positivity)
  have hdiff : ∀ᵐ u ∂μ, ∀ w ∈ Metric.ball z₀ 1,
      HasDerivAt (fun x => -(((u : ℝ) : ℂ) ^ 2) * heatIntegrand t x u)
        (-(((u : ℝ) : ℂ) ^ 2) * heatIntegrandDeriv t w u) w :=
    Filter.Eventually.of_forall fun u w _ =>
      (heat_integrand_hasDerivAt t u w).const_mul (-(((u : ℝ) : ℂ) ^ 2))
  have hFint : MeasureTheory.Integrable
      (fun u : ℝ => -(((u : ℝ) : ℂ) ^ 2) * heatIntegrand t z₀ u) μ := by
    apply MeasureTheory.Integrable.mono'
      (integrableOn_heatSqDominatingFun t |z₀.im| (abs_nonneg _))
    · exact (((Complex.continuous_ofReal.pow 2).neg.mul
        (continuous_heatIntegrand t z₀)).continuousOn.aestronglyMeasurable
        measurableSet_Ioi)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
      rw [neg_mul, norm_neg]
      exact norm_sq_mul_heatIntegrand_le (le_refl t) (abs_nonneg _) (le_refl _) hu.le
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z₀ (by norm_num : (0:ℝ) < 1))
    (Filter.Eventually.of_forall hmeas) hFint hderv_meas hbound hint hdiff).2

/-- **The third `z`-derivative**: `∂³_z H_t(z)
= ∫₀^∞ u³ · e^{tu²} Φ(u) sin(zu) du`, written as `∫ −u² · heatIntegrandDeriv`.
One more dominated differentiation past `deriv_two_deBruijnNewmanH`. -/
theorem deriv_three_deBruijnNewmanH (t : ℝ) (z : ℂ) :
    iteratedDeriv 3 (deBruijnNewmanH t) z
      = ∫ u : ℝ in Set.Ioi 0, -(((u : ℝ) : ℂ) ^ 2) * heatIntegrandDeriv t z u := by
  have hEq : iteratedDeriv 2 (deBruijnNewmanH t)
      = fun w : ℂ => ∫ u : ℝ in Set.Ioi 0, -(((u : ℝ) : ℂ) ^ 2) * heatIntegrand t w u :=
    funext fun w => by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
      exact deriv_two_deBruijnNewmanH t w
  rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ, hEq]
  exact (hasDerivAt_integral_negSq_heatIntegrand t z).deriv

/-- **Joint continuity of `∂³_z H`**: dominated convergence with the
`heatCubeDominatingFun` box bound `norm_sq_mul_heatIntegrandDeriv_le`. -/
theorem continuous_deBruijnNewmanH_zderiv_three :
    Continuous fun p : ℝ × ℂ => iteratedDeriv 3 (deBruijnNewmanH p.1) p.2 := by
  rw [show (fun p : ℝ × ℂ => iteratedDeriv 3 (deBruijnNewmanH p.1) p.2)
      = fun p : ℝ × ℂ =>
        ∫ u : ℝ in Set.Ioi 0, -((u : ℂ) ^ 2) * heatIntegrandDeriv p.1 p.2 u
      from funext fun p => deriv_three_deBruijnNewmanH p.1 p.2]
  rw [continuous_iff_continuousAt]
  intro ⟨t₀, z₀⟩
  set μ := MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)) with hμ
  have hmeas : ∀ p : ℝ × ℂ, MeasureTheory.AEStronglyMeasurable
      (fun u : ℝ => -((u : ℂ) ^ 2) * heatIntegrandDeriv p.1 p.2 u) μ :=
    fun p => (((Complex.continuous_ofReal.pow 2).neg.mul
      (continuous_heatIntegrandDeriv p.1 p.2)).continuousOn.aestronglyMeasurable
      measurableSet_Ioi)
  have hb1 : ∀ᶠ p : ℝ × ℂ in nhds (t₀, z₀), dist p.1 t₀ < 1 :=
    (continuous_fst.tendsto (t₀, z₀)).eventually (Metric.ball_mem_nhds t₀ zero_lt_one)
  have hb2 : ∀ᶠ p : ℝ × ℂ in nhds (t₀, z₀), dist p.2 z₀ < 1 :=
    (continuous_snd.tendsto (t₀, z₀)).eventually (Metric.ball_mem_nhds z₀ zero_lt_one)
  have hbound : ∀ᶠ p : ℝ × ℂ in nhds (t₀, z₀), ∀ᵐ u : ℝ ∂μ,
      ‖-((u : ℂ) ^ 2) * heatIntegrandDeriv p.1 p.2 u‖
        ≤ heatCubeDominatingFun (t₀ + 1) (|z₀.im| + 1) u := by
    filter_upwards [hb1, hb2] with p hp1 hp2
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
    rw [neg_mul, norm_neg]
    exact norm_sq_mul_heatIntegrandDeriv_le (t := p.1) (t₁ := t₀ + 1)
      (c := |z₀.im| + 1)
      (by
        have h1 : |p.1 - t₀| < 1 := by rw [← Real.dist_eq]; exact hp1
        linarith [(abs_lt.mp h1).2])
      (by positivity) (abs_im_le_add_one_of_dist_lt_one hp2) hu.le
  have hlim : ∀ᵐ u : ℝ ∂μ, Filter.Tendsto
      (fun p : ℝ × ℂ => -((u : ℂ) ^ 2) * heatIntegrandDeriv p.1 p.2 u)
      (nhds (t₀, z₀)) (nhds (-((u : ℂ) ^ 2) * heatIntegrandDeriv t₀ z₀ u)) := by
    apply Filter.Eventually.of_forall
    intro u
    have hcont : Continuous
        (fun p : ℝ × ℂ => -((u : ℂ) ^ 2) * heatIntegrandDeriv p.1 p.2 u) := by
      unfold heatIntegrandDeriv
      fun_prop
    exact hcont.tendsto (t₀, z₀)
  show Filter.Tendsto _ (nhds (t₀, z₀)) (nhds _)
  exact MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (heatCubeDominatingFun (t₀ + 1) (|z₀.im| + 1))
    (Filter.Eventually.of_forall hmeas) hbound
    (integrableOn_heatCubeDominatingFun (t₀ + 1) (|z₀.im| + 1) (by positivity)) hlim

/-- The `t`-derivative of the once-`z`-differentiated integrand:
`∂_t [−e^{t u²} Φ(u) sin(z u) · u] = u² · (−e^{t u²} Φ(u) sin(z u) · u)`. -/
theorem heat_integrandDeriv_hasDerivAt_t (u : ℝ) (z : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => heatIntegrandDeriv s z u)
      (((u : ℝ) : ℂ) ^ 2 * heatIntegrandDeriv t z u) t := by
  have h1 : HasDerivAt (fun s : ℝ => Real.exp (s * u ^ 2))
      (Real.exp (t * u ^ 2) * u ^ 2) t := by
    simpa using ((hasDerivAt_id t).mul_const (u ^ 2 : ℝ)).exp
  have h2 : HasDerivAt (fun s : ℝ => Real.exp (s * u ^ 2) * phi u)
      (Real.exp (t * u ^ 2) * u ^ 2 * phi u) t := h1.mul_const (phi u)
  have h3 : HasDerivAt (fun s : ℝ => ((Real.exp (s * u ^ 2) * phi u : ℝ) : ℂ))
      (((Real.exp (t * u ^ 2) * u ^ 2 * phi u : ℝ) : ℂ)) t := h2.ofReal_comp
  have h4 : HasDerivAt (fun s : ℝ => ((Real.exp (s * u ^ 2) * phi u : ℝ) : ℂ)
        * (-Complex.sin (z * (u : ℂ)) * (u : ℂ)))
      ((((Real.exp (t * u ^ 2) * u ^ 2 * phi u : ℝ) : ℂ))
        * (-Complex.sin (z * (u : ℂ)) * (u : ℂ))) t :=
    h3.mul_const _
  refine h4.congr_deriv ?_
  unfold heatIntegrandDeriv
  push_cast
  ring

/-- **The mixed derivative of the `z`-derivative integral**:
`∂_t (∂_z H_t(z)) = ∫₀^∞ u² · e^{tu²} Φ(u) (−sin(zu)) · u du`, by dominated
differentiation in `t` with the `heatCubeDominatingFun` bound. -/
theorem hasDerivAt_deBruijnNewmanH_zderiv_t (z : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => deriv (deBruijnNewmanH s) z)
      (∫ u : ℝ in Set.Ioi 0, ((u : ℝ) : ℂ) ^ 2 * heatIntegrandDeriv t z u) t := by
  set μ := MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)) with hμ
  have hmeas : ∀ s : ℝ, MeasureTheory.AEStronglyMeasurable
      (fun u : ℝ => heatIntegrandDeriv s z u) μ :=
    fun s => (continuous_heatIntegrandDeriv s z).continuousOn.aestronglyMeasurable
      measurableSet_Ioi
  have hderv_meas : MeasureTheory.AEStronglyMeasurable
      (fun u : ℝ => ((u : ℝ) : ℂ) ^ 2 * heatIntegrandDeriv t z u) μ :=
    ((Complex.continuous_ofReal.pow 2).mul
      (continuous_heatIntegrandDeriv t z)).continuousOn.aestronglyMeasurable
      measurableSet_Ioi
  have hbound : ∀ᵐ u ∂μ, ∀ s ∈ Metric.ball t 1,
      ‖(((u : ℝ) : ℂ)) ^ 2 * heatIntegrandDeriv s z u‖
        ≤ heatCubeDominatingFun (t + 1) |z.im| u := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu s hs
    have hs1 : s ≤ t + 1 := by
      have h1 : |s - t| < 1 := by
        rw [← Real.dist_eq]
        exact Metric.mem_ball.mp hs
      have h2 : s - t ≤ |s - t| := le_abs_self _
      linarith
    exact norm_sq_mul_heatIntegrandDeriv_le (t := s) (t₁ := t + 1) (c := |z.im|)
      hs1 (abs_nonneg _) (le_refl _) hu.le
  have hint : MeasureTheory.Integrable (heatCubeDominatingFun (t + 1) |z.im|) μ :=
    integrableOn_heatCubeDominatingFun (t + 1) |z.im| (abs_nonneg _)
  have hdiff : ∀ᵐ u ∂μ, ∀ s ∈ Metric.ball t 1,
      HasDerivAt (fun s' => heatIntegrandDeriv s' z u)
        ((((u : ℝ) : ℂ)) ^ 2 * heatIntegrandDeriv s z u) s :=
    Filter.Eventually.of_forall fun u s _ => heat_integrandDeriv_hasDerivAt_t u z s
  have hFint : MeasureTheory.Integrable (fun u : ℝ => heatIntegrandDeriv t z u) μ :=
    heat_integrandDeriv_integrable t z
  rw [show (fun s : ℝ => deriv (deBruijnNewmanH s) z)
      = fun s : ℝ => ∫ u : ℝ in Set.Ioi 0, heatIntegrandDeriv s z u
      from funext fun s => deriv_deBruijnNewmanH s z]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds t (by norm_num : (0:ℝ) < 1))
    (Filter.Eventually.of_forall hmeas) hFint hderv_meas hbound hint hdiff).2

/-- **The cross derivative identity**: `∂_t (∂_z H) = −∂³_z H`. This is the
backward heat equation `∂_t = −∂²_z` applied to `∂_z H`, and it is what makes
the critical curve `c(t)` (the implicit curve of `∂_z H = 0` at a double zero)
move with velocity `c'(τ) = ∂³_z H / ∂²_z H`. -/
theorem deBruijnNewmanH_cross_derivative (t : ℝ) (z : ℂ) :
    deriv (fun s : ℝ => deriv (deBruijnNewmanH s) z) t
      = -iteratedDeriv 3 (deBruijnNewmanH t) z := by
  rw [(hasDerivAt_deBruijnNewmanH_zderiv_t z t).deriv, deriv_three_deBruijnNewmanH]
  simp only [neg_mul, MeasureTheory.integral_neg, neg_neg]

/-- **Joint continuity of the mixed derivative** `∂_t ∂_z H`: dominated
convergence with the `heatCubeDominatingFun` box bound. Together with
`continuous_deBruijnNewmanH_zderiv_two` this makes `(t, z) ↦ ∂_z H_t(z)`
jointly `C¹`, which is what the implicit function theorem needs to produce
the critical curve at a double zero. -/
theorem continuous_deBruijnNewmanH_crossderiv :
    Continuous fun p : ℝ × ℂ =>
      ∫ u : ℝ in Set.Ioi 0, ((u : ℝ) : ℂ) ^ 2 * heatIntegrandDeriv p.1 p.2 u := by
  rw [continuous_iff_continuousAt]
  intro ⟨t₀, z₀⟩
  set μ := MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)) with hμ
  have hmeas : ∀ p : ℝ × ℂ, MeasureTheory.AEStronglyMeasurable
      (fun u : ℝ => ((u : ℝ) : ℂ) ^ 2 * heatIntegrandDeriv p.1 p.2 u) μ :=
    fun p => (((Complex.continuous_ofReal.pow 2).mul
      (continuous_heatIntegrandDeriv p.1 p.2)).continuousOn.aestronglyMeasurable
      measurableSet_Ioi)
  have hb1 : ∀ᶠ p : ℝ × ℂ in nhds (t₀, z₀), dist p.1 t₀ < 1 :=
    (continuous_fst.tendsto (t₀, z₀)).eventually (Metric.ball_mem_nhds t₀ zero_lt_one)
  have hb2 : ∀ᶠ p : ℝ × ℂ in nhds (t₀, z₀), dist p.2 z₀ < 1 :=
    (continuous_snd.tendsto (t₀, z₀)).eventually (Metric.ball_mem_nhds z₀ zero_lt_one)
  have hbound : ∀ᶠ p : ℝ × ℂ in nhds (t₀, z₀), ∀ᵐ u : ℝ ∂μ,
      ‖(((u : ℝ) : ℂ)) ^ 2 * heatIntegrandDeriv p.1 p.2 u‖
        ≤ heatCubeDominatingFun (t₀ + 1) (|z₀.im| + 1) u := by
    filter_upwards [hb1, hb2] with p hp1 hp2
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
    exact norm_sq_mul_heatIntegrandDeriv_le (t := p.1) (t₁ := t₀ + 1)
      (c := |z₀.im| + 1)
      (by
        have h1 : |p.1 - t₀| < 1 := by rw [← Real.dist_eq]; exact hp1
        linarith [(abs_lt.mp h1).2])
      (by positivity) (abs_im_le_add_one_of_dist_lt_one hp2) hu.le
  have hlim : ∀ᵐ u : ℝ ∂μ, Filter.Tendsto
      (fun p : ℝ × ℂ => ((u : ℝ) : ℂ) ^ 2 * heatIntegrandDeriv p.1 p.2 u)
      (nhds (t₀, z₀)) (nhds (((u : ℝ) : ℂ) ^ 2 * heatIntegrandDeriv t₀ z₀ u)) := by
    apply Filter.Eventually.of_forall
    intro u
    have hcont : Continuous
        (fun p : ℝ × ℂ => ((u : ℝ) : ℂ) ^ 2 * heatIntegrandDeriv p.1 p.2 u) := by
      unfold heatIntegrandDeriv
      fun_prop
    exact hcont.tendsto (t₀, z₀)
  show Filter.Tendsto _ (nhds (t₀, z₀)) (nhds _)
  exact MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (heatCubeDominatingFun (t₀ + 1) (|z₀.im| + 1))
    (Filter.Eventually.of_forall hmeas) hbound
    (integrableOn_heatCubeDominatingFun (t₀ + 1) (|z₀.im| + 1) (by positivity)) hlim

/-! ## Phase 2(viii)c：`z` 导数映射的联合 `C¹`（临界曲线 IFT 预备） -/

/-- **The joint real derivative of the `z`-derivative map** `(t, z) ↦ ∂_z H_t(z)`:
`(h, k) ↦ h • (∂_t ∂_z H_t(w)) + (∂²_z H_t(w)) * k`, where `∂_t ∂_z H` is the
`u²`-weighted integral of `heatIntegrandDeriv` (the cross derivative) and
`∂²_z H_t(w) = deriv (deriv (H_t)) w`. -/
noncomputable def jointFDerivZderivCLM (t : ℝ) (w : ℂ) : ℝ × ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.fst ℝ ℝ ℂ).smulRight
      (∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrandDeriv t w u)
    + ((ContinuousLinearMap.mul ℝ ℂ) (deriv (deriv (deBruijnNewmanH t)) w)).comp
      (ContinuousLinearMap.snd ℝ ℝ ℂ)

/-- Evaluation of `jointFDerivZderivCLM`. -/
theorem jointFDerivZderivCLM_apply (t : ℝ) (w : ℂ) (q : ℝ × ℂ) :
    jointFDerivZderivCLM t w q
      = q.1 • (∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrandDeriv t w u)
        + deriv (deriv (deBruijnNewmanH t)) w * q.2 :=
  rfl

/-- **Joint continuity of `∂²_z H` in `deriv`-form**: the pointwise identity
`iteratedDeriv 2 = deriv ∘ deriv` transports
`continuous_deBruijnNewmanH_zderiv_two`. -/
theorem continuous_deBruijnNewmanH_deriv_two :
    Continuous fun p : ℝ × ℂ => deriv (deriv (deBruijnNewmanH p.1)) p.2 := by
  rw [show (fun p : ℝ × ℂ => deriv (deriv (deBruijnNewmanH p.1)) p.2)
      = fun p : ℝ × ℂ => iteratedDeriv 2 (deBruijnNewmanH p.1) p.2
      from funext fun p => by
        rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]]
  exact continuous_deBruijnNewmanH_zderiv_two

/-- **Affine restriction derivative for the `z`-derivative map**: the
derivative of `s ↦ ∂_z H_t(w + s·k)` at `s : ℝ` is `∂²_z H_t(w + s·k) · k`. -/
theorem hasDerivAt_deBruijnNewmanHzderiv_affine (t : ℝ) (w k : ℂ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => deriv (deBruijnNewmanH t) (w + (s : ℂ) * k))
      (deriv (deriv (deBruijnNewmanH t)) (w + (s : ℂ) * k) * k) s := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 s := by
    simpa using Complex.ofRealCLM.hasDerivAt (x := s)
  have h2 : HasDerivAt (fun s : ℝ => w + (s : ℂ) * k) k s := by
    simpa using (h1.mul_const k).const_add w
  have hg : HasDerivAt (deriv (deBruijnNewmanH t))
      (∫ u : ℝ in Set.Ioi 0, -((u : ℂ) ^ 2) * heatIntegrand t (w + (s : ℂ) * k) u)
      (w + (s : ℂ) * k) :=
    hasDerivAt_deriv_deBruijnNewmanH t (w + (s : ℂ) * k)
  have h3 := @HasDerivAt.scomp ℝ _ ℂ _ _ s ℂ _ _ _ IsScalarTower.right _ _ _ _ hg h2
  have h4 : HasDerivAt (fun s : ℝ => deriv (deBruijnNewmanH t) (w + (s : ℂ) * k))
      ((∫ u : ℝ in Set.Ioi 0, -((u : ℂ) ^ 2) * heatIntegrand t (w + (s : ℂ) * k) u)
        * k) s := by
    simpa [Function.comp_def, smul_eq_mul, mul_comm] using h3
  rw [deriv_two_deBruijnNewmanH]
  exact h4

/-- **FTC in the z-direction for the `z`-derivative map**:
`∂_z H_t(w + k) − ∂_z H_t(w) = ∫₀¹ ∂²_z H_t(w + s·k)·k ds`. The integrand is
jointly continuous by `continuous_deBruijnNewmanH_deriv_two`. -/
theorem deBruijnNewmanHzderiv_z_sub_eq_intervalIntegral (t : ℝ) (w k : ℂ) :
    deriv (deBruijnNewmanH t) (w + k) - deriv (deBruijnNewmanH t) w
      = ∫ s : ℝ in (0:ℝ)..1,
        deriv (deriv (deBruijnNewmanH t)) (w + (s : ℂ) * k) * k := by
  have hDcont : Continuous fun s : ℝ =>
      deriv (deriv (deBruijnNewmanH t)) (w + (s : ℂ) * k) * k :=
    (continuous_deBruijnNewmanH_deriv_two.comp
      (continuous_const.prodMk
        ((Complex.continuous_ofReal.mul continuous_const).const_add w))).mul
      continuous_const
  have hint : IntervalIntegrable
      (deriv fun s : ℝ => deriv (deBruijnNewmanH t) (w + (s : ℂ) * k))
      MeasureTheory.volume 0 1 := by
    rw [show (deriv fun s : ℝ => deriv (deBruijnNewmanH t) (w + (s : ℂ) * k))
        = fun s : ℝ => deriv (deriv (deBruijnNewmanH t)) (w + (s : ℂ) * k) * k
        from funext fun s => (hasDerivAt_deBruijnNewmanHzderiv_affine t w k s).deriv]
    exact hDcont.continuousOn.intervalIntegrable
  have h2 : ∫ s : ℝ in (0:ℝ)..1,
        deriv (deriv (deBruijnNewmanH t)) (w + (s : ℂ) * k) * k
      = deriv (deBruijnNewmanH t) (w + (1 : ℂ) * k)
        - deriv (deBruijnNewmanH t) (w + (0 : ℂ) * k) := by
    rw [intervalIntegral.integral_congr
      fun s _ => (hasDerivAt_deBruijnNewmanHzderiv_affine t w k s).deriv.symm]
    exact intervalIntegral.integral_deriv_eq_sub
      (fun x _ => (hasDerivAt_deBruijnNewmanHzderiv_affine t w k x).differentiableAt)
      hint
  simpa using h2.symm

/-- **Affine restriction derivative for the second `z`-derivative map**: the
derivative of `s ↦ ∂²_z H_t(w + s·k)` at `s : ℝ` is `∂³_z H_t(w + s·k) · k`. -/
theorem hasDerivAt_deBruijnNewmanHzderiv_two_affine (t : ℝ) (w k : ℂ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => deriv (deriv (deBruijnNewmanH t)) (w + (s : ℂ) * k))
      (iteratedDeriv 3 (deBruijnNewmanH t) (w + (s : ℂ) * k) * k) s := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 s := by
    simpa using Complex.ofRealCLM.hasDerivAt (x := s)
  have h2 : HasDerivAt (fun s : ℝ => w + (s : ℂ) * k) k s := by
    simpa using (h1.mul_const k).const_add w
  have hg : HasDerivAt (deriv (deriv (deBruijnNewmanH t)))
      (∫ u : ℝ in Set.Ioi 0, -((u : ℂ) ^ 2)
        * heatIntegrandDeriv t (w + (s : ℂ) * k) u)
      (w + (s : ℂ) * k) := by
    rw [show deriv (deriv (deBruijnNewmanH t))
      = fun w : ℂ => ∫ u : ℝ in Set.Ioi 0, -((u : ℂ) ^ 2) * heatIntegrand t w u
      from funext fun w => deriv_two_deBruijnNewmanH t w]
    exact hasDerivAt_integral_negSq_heatIntegrand t (w + (s : ℂ) * k)
  have h3 := @HasDerivAt.scomp ℝ _ ℂ _ _ s ℂ _ _ _ IsScalarTower.right _ _ _ _ hg h2
  have h4 : HasDerivAt (fun s : ℝ => deriv (deriv (deBruijnNewmanH t)) (w + (s : ℂ) * k))
      ((∫ u : ℝ in Set.Ioi 0, -((u : ℂ) ^ 2)
        * heatIntegrandDeriv t (w + (s : ℂ) * k) u)
        * k) s := by
    simpa [Function.comp_def, smul_eq_mul, mul_comm] using h3
  rw [deriv_three_deBruijnNewmanH]
  exact h4

/-- **FTC in the z-direction for the second `z`-derivative map**:
`∂²_z H_t(w + k) − ∂²_z H_t(w) = ∫₀¹ ∂³_z H_t(w + s·k)·k ds`. The integrand is
jointly continuous by `continuous_deBruijnNewmanH_zderiv_three`. Together with
`deBruijnNewmanH_taylor_two_z` this supplies the order-2 Taylor expansion of
`H_t` in `z` with a cubic integral remainder — the input for excluding
non-real zeros near an exactly-double real zero after the collision. -/
theorem deBruijnNewmanHzderiv_two_z_sub_eq_intervalIntegral (t : ℝ) (w k : ℂ) :
    deriv (deriv (deBruijnNewmanH t)) (w + k) - deriv (deriv (deBruijnNewmanH t)) w
      = ∫ s : ℝ in (0:ℝ)..1,
        iteratedDeriv 3 (deBruijnNewmanH t) (w + (s : ℂ) * k) * k := by
  have hDcont : Continuous fun s : ℝ =>
      iteratedDeriv 3 (deBruijnNewmanH t) (w + (s : ℂ) * k) * k :=
    (continuous_deBruijnNewmanH_zderiv_three.comp
      (continuous_const.prodMk
        ((Complex.continuous_ofReal.mul continuous_const).const_add w))).mul
      continuous_const
  have hint : IntervalIntegrable
      (deriv fun s : ℝ => deriv (deriv (deBruijnNewmanH t)) (w + (s : ℂ) * k))
      MeasureTheory.volume 0 1 := by
    rw [show (deriv fun s : ℝ => deriv (deriv (deBruijnNewmanH t)) (w + (s : ℂ) * k))
        = fun s : ℝ => iteratedDeriv 3 (deBruijnNewmanH t) (w + (s : ℂ) * k) * k
        from funext fun s =>
          (hasDerivAt_deBruijnNewmanHzderiv_two_affine t w k s).deriv]
    exact hDcont.continuousOn.intervalIntegrable
  have h2 : ∫ s : ℝ in (0:ℝ)..1,
        iteratedDeriv 3 (deBruijnNewmanH t) (w + (s : ℂ) * k) * k
      = deriv (deriv (deBruijnNewmanH t)) (w + (1 : ℂ) * k)
        - deriv (deriv (deBruijnNewmanH t)) (w + (0 : ℂ) * k) := by
    rw [intervalIntegral.integral_congr
      fun s _ => (hasDerivAt_deBruijnNewmanHzderiv_two_affine t w k s).deriv.symm]
    exact intervalIntegral.integral_deriv_eq_sub
      (fun x _ =>
        (hasDerivAt_deBruijnNewmanHzderiv_two_affine t w k x).differentiableAt)
      hint
  simpa using h2.symm

/-- **FTC in the t-direction for the `z`-derivative map**:
`∂_z H_t(w) − ∂_z H_{t₀}(w) = ∫_{t₀}^{t} ∂_s ∂_z H_s(w) ds`, with the cross
derivative jointly continuous by `continuous_deBruijnNewmanH_crossderiv`. -/
theorem deBruijnNewmanHzderiv_t_sub_eq_intervalIntegral (t₀ t : ℝ) (w : ℂ) :
    deriv (deBruijnNewmanH t) w - deriv (deBruijnNewmanH t₀) w
      = ∫ s : ℝ in t₀..t,
        ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrandDeriv s w u := by
  have hDcont : Continuous fun s : ℝ =>
      ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrandDeriv s w u :=
    continuous_deBruijnNewmanH_crossderiv.comp (continuous_id.prodMk continuous_const)
  have hint : IntervalIntegrable
      (deriv fun s : ℝ => deriv (deBruijnNewmanH s) w)
      MeasureTheory.volume t₀ t := by
    rw [show (deriv fun s : ℝ => deriv (deBruijnNewmanH s) w)
        = fun s : ℝ => ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrandDeriv s w u
        from funext fun s => (hasDerivAt_deBruijnNewmanH_zderiv_t w s).deriv]
    exact hDcont.continuousOn.intervalIntegrable
  have h2 : ∫ s : ℝ in t₀..t,
        ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrandDeriv s w u
      = deriv (deBruijnNewmanH t) w - deriv (deBruijnNewmanH t₀) w := by
    rw [intervalIntegral.integral_congr
      fun s _ => ((hasDerivAt_deBruijnNewmanH_zderiv_t w s).deriv).symm]
    exact intervalIntegral.integral_deriv_eq_sub
      (fun x _ => (hasDerivAt_deBruijnNewmanH_zderiv_t w x).differentiableAt) hint
  exact h2.symm

/-- **Joint differentiability of the `z`-derivative map**:
`(t, z) ↦ ∂_z H_t(z)` has the joint real Fréchet derivative
`jointFDerivZderivCLM` at every point `p`. The defect splits by FTC in each
coordinate (`deBruijnNewmanHzderiv_t_sub_eq_intervalIntegral`,
`deBruijnNewmanHzderiv_z_sub_eq_intervalIntegral`) into two interval integrals
whose integrands deviate from their values at `p` by at most `ε/2` (joint
continuity of the cross derivative and of `∂²_z H`). -/
theorem hasFDerivAt_deBruijnNewmanHzderiv_prod (p : ℝ × ℂ) :
    HasFDerivAt (fun q : ℝ × ℂ => deriv (deBruijnNewmanH q.1) q.2)
      (jointFDerivZderivCLM p.1 p.2) p := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hcont₁ : ContinuousAt
      (fun r : ℝ × ℂ =>
        ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrandDeriv r.1 r.2 u) p :=
    continuous_deBruijnNewmanH_crossderiv.continuousAt
  have hcont₂ : ContinuousAt
      (fun r : ℝ × ℂ => deriv (deriv (deBruijnNewmanH r.1)) r.2) p :=
    continuous_deBruijnNewmanH_deriv_two.continuousAt
  rw [Metric.continuousAt_iff] at hcont₁ hcont₂
  obtain ⟨δ₁, hδ₁0, hδ₁⟩ := hcont₁ (ε / 2) (half_pos hε)
  obtain ⟨δ₂, hδ₂0, hδ₂⟩ := hcont₂ (ε / 2) (half_pos hε)
  rw [Metric.eventually_nhds_iff_ball]
  refine ⟨min δ₁ δ₂, lt_min_iff.mpr ⟨hδ₁0, hδ₂0⟩, fun q hq => ?_⟩
  have hqδ1 : dist q p < δ₁ := lt_of_lt_of_le hq (min_le_left _ _)
  have hqδ2 : dist q p < δ₂ := lt_of_lt_of_le hq (min_le_right _ _)
  have hq1 : dist q.1 p.1 ≤ dist q p := by
    rw [Prod.dist_eq]; exact le_max_left _ _
  have hq2 : dist q.2 p.2 ≤ dist q p := by
    rw [Prod.dist_eq]; exact le_max_right _ _
  have hsplit : deriv (deBruijnNewmanH q.1) q.2 - deriv (deBruijnNewmanH p.1) p.2
      = (∫ τ : ℝ in p.1..q.1,
          ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrandDeriv τ q.2 u)
        + ∫ s : ℝ in (0:ℝ)..1,
          deriv (deriv (deBruijnNewmanH p.1)) (p.2 + (s : ℂ) * (q.2 - p.2))
            * (q.2 - p.2) := by
    have h1 := deBruijnNewmanHzderiv_t_sub_eq_intervalIntegral p.1 q.1 q.2
    have h2 := deBruijnNewmanHzderiv_z_sub_eq_intervalIntegral p.1 p.2 (q.2 - p.2)
    rw [add_sub_cancel] at h2
    calc deriv (deBruijnNewmanH q.1) q.2 - deriv (deBruijnNewmanH p.1) p.2
        = (deriv (deBruijnNewmanH q.1) q.2 - deriv (deBruijnNewmanH p.1) q.2)
          + (deriv (deBruijnNewmanH p.1) q.2 - deriv (deBruijnNewmanH p.1) p.2) := by
          ring
      _ = _ := by rw [h1, h2]
  change ‖deriv (deBruijnNewmanH q.1) q.2 - deriv (deBruijnNewmanH p.1) p.2
      - jointFDerivZderivCLM p.1 p.2 (q - p)‖ ≤ ε * ‖q - p‖
  rw [hsplit, jointFDerivZderivCLM_apply]
  have hconst₁ : (q - p).1 •
        (∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrandDeriv p.1 p.2 u)
      = ∫ τ : ℝ in p.1..q.1,
        ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrandDeriv p.1 p.2 u := by
    rw [Prod.fst_sub]
    exact (intervalIntegral.integral_const _).symm
  have hconst₂ : deriv (deriv (deBruijnNewmanH p.1)) p.2 * (q - p).2
      = ∫ s : ℝ in (0:ℝ)..1,
        deriv (deriv (deBruijnNewmanH p.1)) p.2 * (q.2 - p.2) := by
    rw [Prod.snd_sub, intervalIntegral.integral_const]
    simp
  rw [hconst₁, hconst₂]
  have hintA : IntervalIntegrable
      (fun τ : ℝ => ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrandDeriv τ q.2 u)
      MeasureTheory.volume p.1 q.1 :=
    (continuous_deBruijnNewmanH_crossderiv.comp
      (continuous_id.prodMk continuous_const)).continuousOn.intervalIntegrable
  have hintA₀ : IntervalIntegrable
      (fun _ : ℝ => ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrandDeriv p.1 p.2 u)
      MeasureTheory.volume p.1 q.1 := intervalIntegrable_const
  have hintB : IntervalIntegrable
      (fun s : ℝ =>
        deriv (deriv (deBruijnNewmanH p.1)) (p.2 + (s : ℂ) * (q.2 - p.2)) * (q.2 - p.2))
      MeasureTheory.volume 0 1 :=
    ((continuous_deBruijnNewmanH_deriv_two.comp
      (continuous_const.prodMk
        ((Complex.continuous_ofReal.mul continuous_const).const_add p.2))).mul
      continuous_const).continuousOn.intervalIntegrable
  have hintB₀ : IntervalIntegrable
      (fun _ : ℝ => deriv (deriv (deBruijnNewmanH p.1)) p.2 * (q.2 - p.2))
      MeasureTheory.volume 0 1 := intervalIntegrable_const
  rw [add_sub_add_comm, ← intervalIntegral.integral_sub hintA hintA₀,
    ← intervalIntegral.integral_sub hintB hintB₀]
  have hA : ∀ τ ∈ Set.uIoc p.1 q.1,
      ‖(∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrandDeriv τ q.2 u)
          - ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrandDeriv p.1 p.2 u‖
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
      ‖deriv (deriv (deBruijnNewmanH p.1)) (p.2 + (s : ℂ) * (q.2 - p.2)) * (q.2 - p.2)
          - deriv (deriv (deBruijnNewmanH p.1)) p.2 * (q.2 - p.2)‖
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
    have hlt : ‖deriv (deriv (deBruijnNewmanH p.1)) (p.2 + (s : ℂ) * (q.2 - p.2))
        - deriv (deriv (deBruijnNewmanH p.1)) p.2‖ < ε / 2 := by
      have hlt := hδ₂ hdist
      rw [dist_eq_norm] at hlt
      exact hlt
    exact mul_le_mul_of_nonneg_right (le_of_lt hlt) (norm_nonneg _)
  have hboundA := intervalIntegral.norm_integral_le_of_norm_le_const hA
  have hboundB := intervalIntegral.norm_integral_le_of_norm_le_const hB
  calc ‖(∫ τ : ℝ in p.1..q.1,
            (∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrandDeriv τ q.2 u)
            - ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrandDeriv p.1 p.2 u)
        + ∫ s : ℝ in (0:ℝ)..1,
          (deriv (deriv (deBruijnNewmanH p.1)) (p.2 + (s : ℂ) * (q.2 - p.2))
              * (q.2 - p.2)
            - deriv (deriv (deBruijnNewmanH p.1)) p.2 * (q.2 - p.2))‖
      ≤ ‖∫ τ : ℝ in p.1..q.1,
          (∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrandDeriv τ q.2 u)
            - ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrandDeriv p.1 p.2 u‖
        + ‖∫ s : ℝ in (0:ℝ)..1,
          (deriv (deriv (deBruijnNewmanH p.1)) (p.2 + (s : ℂ) * (q.2 - p.2))
              * (q.2 - p.2)
            - deriv (deriv (deBruijnNewmanH p.1)) p.2 * (q.2 - p.2))‖ :=
        norm_add_le _ _
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

/-- **Continuity of the joint derivative of the `z`-derivative map**:
`p ↦ jointFDerivZderivCLM p` is continuous, assembled from
`continuous_deBruijnNewmanH_crossderiv` and
`continuous_deBruijnNewmanH_deriv_two`. -/
theorem continuous_jointFDerivZderivCLM :
    Continuous fun p : ℝ × ℂ => jointFDerivZderivCLM p.1 p.2 := by
  have ht : Continuous fun p : ℝ × ℂ =>
      (ContinuousLinearMap.fst ℝ ℝ ℂ).smulRight
        (∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrandDeriv p.1 p.2 u) := by
    apply ((ContinuousLinearMap.smulRightL ℝ (ℝ × ℂ) ℂ
      (ContinuousLinearMap.fst ℝ ℝ ℂ)).continuous.comp
      continuous_deBruijnNewmanH_crossderiv).congr
    intro p
    refine ContinuousLinearMap.ext fun q => ?_
    rfl
  have hz : Continuous fun p : ℝ × ℂ =>
      ((ContinuousLinearMap.mul ℝ ℂ) (deriv (deriv (deBruijnNewmanH p.1)) p.2)).comp
        (ContinuousLinearMap.snd ℝ ℝ ℂ) :=
    ((ContinuousLinearMap.mul ℝ ℂ).continuous.comp
      continuous_deBruijnNewmanH_deriv_two).clm_comp continuous_const
  exact ht.add hz

/-- **Global `C¹` regularity of the `z`-derivative map**:
`(t, z) ↦ ∂_z H_t(z)` is `C¹` over `ℝ`, with derivative
`jointFDerivZderivCLM`. This is the regularity input for the implicit
function theorem producing the critical curve at a double zero. -/
theorem contDiff_one_deBruijnNewmanHzderiv_prod :
    ContDiff ℝ 1 (fun q : ℝ × ℂ => deriv (deBruijnNewmanH q.1) q.2) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun q => (hasFDerivAt_deBruijnNewmanHzderiv_prod q).differentiableAt, ?_⟩
  rw [show (fderiv ℝ fun q : ℝ × ℂ => deriv (deBruijnNewmanH q.1) q.2)
      = fun q : ℝ × ℂ => jointFDerivZderivCLM q.1 q.2
      from funext fun q => (hasFDerivAt_deBruijnNewmanHzderiv_prod q).fderiv]
  exact continuous_jointFDerivZderivCLM

/-- **Conjugation symmetry of the `z`-derivative**: `∂_z H_t(\bar z)
= \overline{∂_z H_t(z)}`, transported through the integral representation
`deriv_deBruijnNewmanH` by `Complex.sin_conj`. This is what keeps the
critical curve real through a real double zero. -/
theorem deBruijnNewmanHzderiv_conj (t : ℝ) (z : ℂ) :
    deriv (deBruijnNewmanH t) (star z) = star (deriv (deBruijnNewmanH t) z) := by
  rw [deriv_deBruijnNewmanH, deriv_deBruijnNewmanH]
  show (∫ (u : ℝ) in Set.Ioi 0, heatIntegrandDeriv t (star z) u)
      = (starRingEnd ℂ) (∫ (u : ℝ) in Set.Ioi 0, heatIntegrandDeriv t z u)
  have e1 : (starRingEnd ℂ) (∫ (u : ℝ) in Set.Ioi 0, heatIntegrandDeriv t z u)
      = ∫ (u : ℝ) in Set.Ioi 0, (starRingEnd ℂ) (heatIntegrandDeriv t z u) :=
    (integral_conj (f := fun u : ℝ => heatIntegrandDeriv t z u)
      (μ := MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)))).symm
  refine Eq.trans ?_ e1.symm
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro u _
  show ((Real.exp (t * u ^ 2) * phi u : ℝ) : ℂ)
      * (-Complex.sin ((starRingEnd ℂ) z * (u : ℂ)) * (u : ℂ))
      = (starRingEnd ℂ)
        (((Real.exp (t * u ^ 2) * phi u : ℝ) : ℂ)
          * (-Complex.sin (z * (u : ℂ)) * (u : ℂ)))
  rw [map_mul, Complex.conj_ofReal, map_mul, map_neg, ← Complex.sin_conj, map_mul,
    Complex.conj_ofReal]

/-- **The z-partial of the joint derivative of the `z`-derivative map**:
composing `jointFDerivZderivCLM` with the right inclusion recovers
multiplication by `∂²_z H_t(w)`. -/
theorem jointFDerivZderivCLM_comp_inr (t : ℝ) (w : ℂ) :
    (jointFDerivZderivCLM t w).comp (ContinuousLinearMap.inr ℝ ℝ ℂ)
      = ContinuousLinearMap.mul ℝ ℂ (deriv (deriv (deBruijnNewmanH t)) w) := by
  ext z
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    jointFDerivZderivCLM_apply]
  simp

/-- **Invertibility of the z-partial at an exactly-double critical point**: if
`∂²_z H_{t₀}(x₀) ≠ 0`, the z-component of the joint real derivative of
`(t, z) ↦ ∂_z H_t(z)` is an invertible `ℝ`-linear map — the nondegeneracy
hypothesis of the implicit function theorem for the critical curve. -/
theorem isInvertible_jointFDerivZderivCLM_comp_inr (t₀ : ℝ) (x₀ : ℂ)
    (hD : deriv (deriv (deBruijnNewmanH t₀)) x₀ ≠ 0) :
    ((fderiv ℝ (fun q : ℝ × ℂ => deriv (deBruijnNewmanH q.1) q.2) (t₀, x₀)).comp
      (ContinuousLinearMap.inr ℝ ℝ ℂ)).IsInvertible := by
  have hfd : fderiv ℝ (fun q : ℝ × ℂ => deriv (deBruijnNewmanH q.1) q.2) (t₀, x₀)
      = jointFDerivZderivCLM t₀ x₀ :=
    (hasFDerivAt_deBruijnNewmanHzderiv_prod (t₀, x₀)).fderiv
  rw [hfd, jointFDerivZderivCLM_comp_inr]
  exact ⟨ContinuousLinearEquiv.equivOfInverse
    (ContinuousLinearMap.mul ℝ ℂ (deriv (deriv (deBruijnNewmanH t₀)) x₀))
    (ContinuousLinearMap.mul ℝ ℂ (deriv (deriv (deBruijnNewmanH t₀)) x₀)⁻¹)
    (fun z => inv_mul_cancel_left₀ hD z) (fun z => mul_inv_cancel_left₀ hD z), rfl⟩

/-- **The critical curve through a double zero (IFT for `∂_z H`)**: at a point
`(τ, x₀)` with `∂_z H_τ(x₀) = 0` (critical) and `∂²_z H_τ(x₀) ≠ 0` (exactly
double), the critical set `∂_z H_t(z) = 0` near `(τ, x₀)` is a differentiable
curve `c(t)` through `x₀`, real-valued near `τ`, with velocity
`c'(τ) = ∂³_z H_τ(x₀) / ∂²_z H_τ(x₀)`. Existence and uniqueness come from the
implicit function theorem; reality from the conjugation symmetry
`deBruijnNewmanHzderiv_conj`; the velocity from the chain rule on
`∂_z H_t(c(t)) = 0` together with the cross-derivative identity
`∂_t ∂_z H = −∂³_z H`. A zero of `H_t` loses simplicity exactly by crossing
this curve, so `c` is the locus of potential zero collisions. -/
theorem deBruijnNewman_critical_curve (τ : ℝ) (x₀ : ℂ)
    (hz : deriv (deBruijnNewmanH τ) x₀ = 0)
    (hD2 : deriv (deriv (deBruijnNewmanH τ)) x₀ ≠ 0)
    (hx : x₀.im = 0) :
    ∃ c : ℝ → ℂ, (∀ᶠ t in nhds τ, DifferentiableAt ℝ c t) ∧ c τ = x₀
      ∧ (∀ᶠ t in nhds τ, deriv (deBruijnNewmanH t) (c t) = 0)
      ∧ (∀ᶠ t in nhds τ, (c t).im = 0)
      ∧ deriv c τ
        = iteratedDeriv 3 (deBruijnNewmanH τ) x₀
          / deriv (deriv (deBruijnNewmanH τ)) x₀ := by
  have hCD : ContDiffAt ℝ 1 (fun q : ℝ × ℂ => deriv (deBruijnNewmanH q.1) q.2)
      (τ, x₀) :=
    contDiff_one_deBruijnNewmanHzderiv_prod.contDiffAt
  have hInv := isInvertible_jointFDerivZderivCLM_comp_inr τ x₀ hD2
  have hstar : star x₀ = x₀ := by
    rw [Complex.star_def, Complex.conj_eq_iff_im]; exact hx
  set c := hCD.implicitFunction one_ne_zero hInv with hc
  have hcCD : ContDiffAt ℝ 1 c τ := hCD.contDiffAt_implicitFunction one_ne_zero hInv
  have hc0 : c τ = x₀ := hCD.implicitFunction_apply_self one_ne_zero hInv
  have hzero : ∀ᶠ t in nhds τ, deriv (deBruijnNewmanH t) (c t) = 0 := by
    have hev := hCD.eventually_apply_implicitFunction one_ne_zero hInv
    refine hev.mono fun t ht => ?_
    simp only [] at ht
    rwa [hz] at ht
  have hcdiff_ev : ∀ᶠ t in nhds τ, DifferentiableAt ℝ c t :=
    (hcCD.eventually (by decide)).mono fun _t ht => ht.differentiableAt_one
  refine ⟨c, hcdiff_ev, hc0, hzero, ?_, ?_⟩
  · -- reality via the conjugate curve and local uniqueness
    have htend : Filter.Tendsto (fun t : ℝ => (t, star (c t)))
        (nhds τ) (nhds (τ, x₀)) := by
      have h1 : ContinuousAt (fun t : ℝ => (t, star (c t))) τ :=
        continuousAt_id.prodMk
          (continuous_star.continuousAt.comp
            (hcCD.differentiableAt one_ne_zero).continuousAt)
      have h2 : (τ, star (c τ)) = (τ, x₀) := by rw [hc0, hstar]
      exact h2 ▸ h1.tendsto
    have huniq := htend.eventually
      (hCD.eventually_apply_eq_iff_implicitFunction one_ne_zero hInv)
    filter_upwards [huniq, hzero] with t ht hzt
    have hL : (fun q : ℝ × ℂ => deriv (deBruijnNewmanH q.1) q.2) (t, star (c t))
        = (fun q : ℝ × ℂ => deriv (deBruijnNewmanH q.1) q.2) (τ, x₀) := by
      change deriv (deBruijnNewmanH t) (star (c t)) = deriv (deBruijnNewmanH τ) x₀
      rw [deBruijnNewmanHzderiv_conj, hzt, star_zero, hz]
    have him : c t = star (c t) := ht.mp hL
    rw [Complex.star_def] at him
    exact Complex.conj_eq_iff_im.mp him.symm
  · -- velocity: chain rule on `∂_z H_t(c(t)) = 0`
    have hg0 : HasDerivAt ((fun q : ℝ × ℂ => deriv (deBruijnNewmanH q.1) q.2)
        ∘ fun t : ℝ => (t, c t)) 0 τ :=
      (hasDerivAt_const (c := (0 : ℂ)) (x := τ)).congr_of_eventuallyEq
        (hzero.mono fun t h => h)
    have hprod : HasFDerivAt (fun t : ℝ => (t, c t))
        ((ContinuousLinearMap.id ℝ ℝ).prod (fderiv ℝ c τ)) τ :=
      (hasFDerivAt_id τ).prodMk (hcCD.differentiableAt one_ne_zero).hasFDerivAt
    have hcomp := (hasFDerivAt_deBruijnNewmanHzderiv_prod (τ, c τ)).comp
      (f := fun t : ℝ => (t, c t)) (x := τ) hprod
    have hval : ((jointFDerivZderivCLM (τ, c τ).1 (τ, c τ).2).comp
        ((ContinuousLinearMap.id ℝ ℝ).prod (fderiv ℝ c τ))) 1
        = (∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrandDeriv τ (c τ) u)
          + deriv (deriv (deBruijnNewmanH τ)) (c τ) * deriv c τ := by
      have hf1 : fderiv ℝ c τ 1 = deriv c τ := by
        have h := (hcCD.differentiableAt one_ne_zero).hasFDerivAt.unique
          (hasDerivAt_iff_hasFDerivAt.mp
            (hcCD.differentiableAt one_ne_zero).hasDerivAt)
        rw [h]
        simp
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
        jointFDerivZderivCLM_apply, hf1]
    have key : (∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrandDeriv τ (c τ) u)
        + deriv (deriv (deBruijnNewmanH τ)) (c τ) * deriv c τ = 0 := by
      have hu := hg0.unique hcomp.hasDerivAt
      rw [hval] at hu
      exact hu.symm
    rw [hc0] at key
    have h1 : deriv (deriv (deBruijnNewmanH τ)) x₀ * deriv c τ
        = -(∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrandDeriv τ x₀ u) := by
      rw [add_comm] at key
      exact eq_neg_of_add_eq_zero_left key
    have h3eq : (∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrandDeriv τ x₀ u)
        = -iteratedDeriv 3 (deBruijnNewmanH τ) x₀ := by
      rw [deriv_three_deBruijnNewmanH]
      simp only [neg_mul, MeasureTheory.integral_neg, neg_neg]
    rw [h3eq, neg_neg] at h1
    rw [eq_comm, div_eq_iff hD2, mul_comm]
    exact h1.symm

/-- **Derivative of `H` along a curve through a critical point**: if `c` is
differentiable at `τ` and `∂_z H_τ(c(τ)) = 0`, then the derivative of
`t ↦ H_t(c(t))` at `τ` is just the time derivative `∂_t H_τ(c(τ))` (the
`u²`-weighted heat integral): the chain-rule term `∂_z H · c'(τ)` drops out.
This is the mechanism making the height of `H` along the critical curve
evolve purely by the heat time derivative. -/
theorem hasDerivAt_deBruijnNewmanH_on_critical_curve (τ : ℝ) (c : ℝ → ℂ)
    (hcdiff : DifferentiableAt ℝ c τ)
    (hz : deriv (deBruijnNewmanH τ) (c τ) = 0) :
    HasDerivAt (fun t : ℝ => deBruijnNewmanH t (c t))
      (∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand τ (c τ) u) τ := by
  have hprod : HasFDerivAt (fun t : ℝ => (t, c t))
      ((ContinuousLinearMap.id ℝ ℝ).prod (fderiv ℝ c τ)) τ :=
    (hasFDerivAt_id τ).prodMk hcdiff.hasFDerivAt
  have hcomp := (hasFDerivAt_deBruijnNewmanH_prod (τ, c τ)).comp
    (f := fun t : ℝ => (t, c t)) (x := τ) hprod
  have hval : ((jointFDerivCLM (τ, c τ).1 (τ, c τ).2).comp
      ((ContinuousLinearMap.id ℝ ℝ).prod (fderiv ℝ c τ))) 1
      = (∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand τ (c τ) u)
        + deriv (deBruijnNewmanH τ) (c τ) * deriv c τ := by
    have hf1 : fderiv ℝ c τ 1 = deriv c τ := by
      have h := hcdiff.hasFDerivAt.unique
        (hasDerivAt_iff_hasFDerivAt.mp hcdiff.hasDerivAt)
      rw [h]
      simp
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      jointFDerivCLM_apply, hf1]
  rw [hz, zero_mul, add_zero] at hval
  have h := hcomp.hasDerivAt
  rw [hval] at h
  exact h

/-- **Height of `H` along the critical curve (FTC form)**: near a critical
time `τ` with `H_τ(x₀) = 0` and `c(τ) = x₀`, if `c` is differentiable and
critical (`∂_z H_t(c(t)) = 0`) on a neighborhood of `τ`, then
`H_t(c(t)) = ∫_τ^t ∂_s H_s(c(s)) ds`.
Since `∂_t H_τ(x₀) = −∂²_z H_τ(x₀)` by the backward heat equation, the height
along the critical curve starts at `0` with slope `−∂²_z H_τ(x₀) ≠ 0` — the
first pillar of the quadratic local model at a double zero. -/
theorem deBruijnNewmanH_critical_height (τ : ℝ) (x₀ : ℂ) (c : ℝ → ℂ)
    (hcdiff : ∀ᶠ t in nhds τ, DifferentiableAt ℝ c t)
    (hcrit : ∀ᶠ t in nhds τ, deriv (deBruijnNewmanH t) (c t) = 0)
    (hc0 : c τ = x₀) (hz0 : deBruijnNewmanH τ x₀ = 0) :
    ∀ᶠ t in nhds τ, deBruijnNewmanH t (c t)
      = ∫ s : ℝ in τ..t,
        ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand s (c s) u := by
  rw [Metric.eventually_nhds_iff] at hcdiff hcrit ⊢
  obtain ⟨δ₁, hδ₁, hD⟩ := hcdiff
  obtain ⟨δ₂, hδ₂, hC⟩ := hcrit
  refine ⟨min δ₁ δ₂, lt_min_iff.mpr ⟨hδ₁, hδ₂⟩, fun t ht => ?_⟩
  have hderivAt : ∀ s : ℝ, dist s τ < min δ₁ δ₂ →
      HasDerivAt (fun r : ℝ => deBruijnNewmanH r (c r))
        (∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand s (c s) u) s := by
    intro s hs
    exact hasDerivAt_deBruijnNewmanH_on_critical_curve s c
      (hD (lt_of_lt_of_le hs (min_le_left _ _)))
      (hC (lt_of_lt_of_le hs (min_le_right _ _)))
  have hmem : ∀ s ∈ Set.uIcc τ t, dist s τ < min δ₁ δ₂ := by
    intro s hs
    have hle : dist s τ ≤ dist t τ := by
      rw [Real.dist_eq, Real.dist_eq]
      rcases Set.mem_uIcc.mp hs with h | h
      · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ s - τ),
          abs_of_nonneg (by linarith : (0:ℝ) ≤ t - τ)]
        linarith [h.2]
      · rw [abs_of_nonpos (by linarith : s - τ ≤ (0:ℝ)),
          abs_of_nonpos (by linarith : t - τ ≤ (0:ℝ))]
        linarith [h.1]
    exact lt_of_le_of_lt hle ht
  have hint : IntervalIntegrable (fun s : ℝ =>
      ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand s (c s) u)
      MeasureTheory.volume τ t := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    have hsd := hmem s hs
    have hcs : ContinuousAt c s :=
      (hD (lt_of_lt_of_le hsd (min_le_left _ _))).continuousAt
    exact (continuous_deBruijnNewmanH_tderiv.continuousAt.comp
      (continuousAt_id.prodMk hcs)).continuousWithinAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hderivAt s (hmem s hs)) hint
  rw [hc0, hz0, sub_zero] at hftc
  exact hftc.symm

/-- **Taylor expansion of order 2 in `z` with iterated-integral remainder**:
`H_t(w + k) = H_t(w) + ∂_z H_t(w)·k
  + ∫₀¹ (∫₀¹ ∂²_z H_t(w + r s·k)·(s k) dr)·k ds`.
Two applications of the `z`-direction FTC
(`deBruijnNewmanH_z_sub_eq_intervalIntegral` and its derivative counterpart
`deBruijnNewmanHzderiv_z_sub_eq_intervalIntegral`); no zero-counting. Along
the critical curve (where `∂_z H_t(c(t)) = 0`) the linear term vanishes and
this becomes the quadratic local model of `H` near a double zero. -/
theorem deBruijnNewmanH_taylor_two_z (t : ℝ) (w k : ℂ) :
    deBruijnNewmanH t (w + k)
      = deBruijnNewmanH t w + deriv (deBruijnNewmanH t) w * k
        + ∫ s : ℝ in (0:ℝ)..1,
          (∫ r : ℝ in (0:ℝ)..1,
            deriv (deriv (deBruijnNewmanH t)) (w + ((r * s : ℝ) : ℂ) * k)
              * ((s : ℂ) * k)) * k := by
  have h1 := deBruijnNewmanH_z_sub_eq_intervalIntegral t w k
  have h2 : ∀ s : ℝ, deriv (deBruijnNewmanH t) (w + (s : ℂ) * k)
      - deriv (deBruijnNewmanH t) w
      = ∫ r : ℝ in (0:ℝ)..1,
        deriv (deriv (deBruijnNewmanH t)) (w + (r : ℂ) * ((s : ℂ) * k))
          * ((s : ℂ) * k) :=
    fun s => deBruijnNewmanHzderiv_z_sub_eq_intervalIntegral t w ((s : ℂ) * k)
  have hconst : deriv (deBruijnNewmanH t) w * k
      = ∫ s : ℝ in (0:ℝ)..1, deriv (deBruijnNewmanH t) w * k := by
    rw [intervalIntegral.integral_const]
    simp
  have hintB : IntervalIntegrable
      (fun s : ℝ => deriv (deBruijnNewmanH t) (w + (s : ℂ) * k) * k)
      MeasureTheory.volume 0 1 :=
    ((continuous_deBruijnNewmanH_zderiv.comp
      (continuous_const.prodMk
        ((Complex.continuous_ofReal.mul continuous_const).const_add w))).mul
      continuous_const).continuousOn.intervalIntegrable
  have hintB₀ : IntervalIntegrable (fun _ : ℝ => deriv (deBruijnNewmanH t) w * k)
      MeasureTheory.volume 0 1 := intervalIntegrable_const
  have hpt : ∀ s : ℝ,
      deriv (deBruijnNewmanH t) (w + (s : ℂ) * k) * k
        - deriv (deBruijnNewmanH t) w * k
      = (∫ r : ℝ in (0:ℝ)..1,
          deriv (deriv (deBruijnNewmanH t)) (w + ((r * s : ℝ) : ℂ) * k)
            * ((s : ℂ) * k)) * k := by
    intro s
    rw [← sub_mul, h2 s]
    apply congrArg (· * k)
    apply intervalIntegral.integral_congr
    intro r _
    have hcast : (r : ℂ) * ((s : ℂ) * k) = ((r * s : ℝ) : ℂ) * k := by
      push_cast
      ring
    show deriv (deriv (deBruijnNewmanH t)) (w + (r : ℂ) * ((s : ℂ) * k)) * ((s : ℂ) * k)
      = deriv (deriv (deBruijnNewmanH t)) (w + ((r * s : ℝ) : ℂ) * k) * ((s : ℂ) * k)
    rw [hcast]
  have h3 : deBruijnNewmanH t (w + k) - deBruijnNewmanH t w
      - deriv (deBruijnNewmanH t) w * k
      = ∫ s : ℝ in (0:ℝ)..1,
        (∫ r : ℝ in (0:ℝ)..1,
          deriv (deriv (deBruijnNewmanH t)) (w + ((r * s : ℝ) : ℂ) * k)
            * ((s : ℂ) * k)) * k := by
    rw [h1, hconst, ← intervalIntegral.integral_sub hintB hintB₀,
      intervalIntegral.integral_congr fun s _ => hpt s]
  rw [sub_sub] at h3
  rw [← h3]
  ring

/-- **Order-2 Taylor expansion of `H_t` in `z` with cubic integral remainder**:
`H_t(w + k) = H_t(w) + ∂_z H_t(w)·k + ∂²_z H_t(w)·k²/2 + R₃`, where `R₃` is the
triple interval integral of `∂³_z H_t` along the segment. Obtained by iterating
the FTC (`deBruijnNewmanHzderiv_two_z_sub_eq_intervalIntegral`) inside the
order-1 remainder of `deBruijnNewmanH_taylor_two_z`. Since `∂³_z H` is jointly
continuous (`continuous_deBruijnNewmanH_zderiv_three`), `R₃` is `O(‖k‖³)` on
compacts — the quantitative input for excluding non-real zeros of `H_t` near an
exactly-double real zero after the collision. -/
theorem deBruijnNewmanH_taylor_three_z (t : ℝ) (w k : ℂ) :
    deBruijnNewmanH t (w + k)
      = deBruijnNewmanH t w + deriv (deBruijnNewmanH t) w * k
        + deriv (deriv (deBruijnNewmanH t)) w * k ^ 2 / 2
        + ∫ s : ℝ in (0:ℝ)..1,
          (∫ r : ℝ in (0:ℝ)..1,
            (∫ q : ℝ in (0:ℝ)..1,
              iteratedDeriv 3 (deBruijnNewmanH t) (w + ((q * r * s : ℝ) : ℂ) * k)
                * (((r * s : ℝ) : ℂ) * k))
              * ((s : ℂ) * k)) * k := by
  -- substitute the D2-FTC into the order-1 remainder, pointwise in `r, s`
  have hsub : ∀ r s : ℝ,
      deriv (deriv (deBruijnNewmanH t)) (w + ((r * s : ℝ) : ℂ) * k)
      = deriv (deriv (deBruijnNewmanH t)) w
        + ∫ q : ℝ in (0:ℝ)..1,
          iteratedDeriv 3 (deBruijnNewmanH t) (w + ((q * r * s : ℝ) : ℂ) * k)
            * (((r * s : ℝ) : ℂ) * k) := by
    intro r s
    have h := deBruijnNewmanHzderiv_two_z_sub_eq_intervalIntegral t w
      (((r * s : ℝ) : ℂ) * k)
    rw [sub_eq_iff_eq_add] at h
    refine (h.trans (add_comm _ _)).trans
      (congrArg (deriv (deriv (deBruijnNewmanH t)) w + ·) ?_)
    apply intervalIntegral.integral_congr
    intro q _
    show iteratedDeriv 3 (deBruijnNewmanH t) (w + (q : ℂ) * (((r * s : ℝ) : ℂ) * k))
        * (((r * s : ℝ) : ℂ) * k)
      = iteratedDeriv 3 (deBruijnNewmanH t) (w + ((q * r * s : ℝ) : ℂ) * k)
        * (((r * s : ℝ) : ℂ) * k)
    have hcast : (q : ℂ) * (((r * s : ℝ) : ℂ) * k) = ((q * r * s : ℝ) : ℂ) * k := by
      push_cast
      ring
    rw [hcast]
  have hpt : ∀ s r : ℝ,
      deriv (deriv (deBruijnNewmanH t)) (w + ((r * s : ℝ) : ℂ) * k) * ((s : ℂ) * k)
      = deriv (deriv (deBruijnNewmanH t)) w * ((s : ℂ) * k)
        + (∫ q : ℝ in (0:ℝ)..1,
            iteratedDeriv 3 (deBruijnNewmanH t) (w + ((q * r * s : ℝ) : ℂ) * k)
              * (((r * s : ℝ) : ℂ) * k)) * ((s : ℂ) * k) := by
    intro s r
    rw [hsub r s, add_mul]
  -- continuity of the parametric q-integral (in `r`), and integrability
  have hcontB : ∀ s : ℝ, Continuous fun r : ℝ =>
      (∫ q : ℝ in (0:ℝ)..1,
        iteratedDeriv 3 (deBruijnNewmanH t) (w + ((q * r * s : ℝ) : ℂ) * k)
          * (((r * s : ℝ) : ℂ) * k)) * ((s : ℂ) * k) := by
    intro s
    refine Continuous.mul ?_ continuous_const
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      ?_ 0 1
    exact (continuous_deBruijnNewmanH_zderiv_three.comp
      (continuous_const.prodMk (continuous_const.add
        ((Complex.continuous_ofReal.comp
          ((continuous_snd.mul continuous_fst).mul continuous_const)).mul
          continuous_const)))).mul
      ((Complex.continuous_ofReal.comp (continuous_fst.mul continuous_const)).mul
        continuous_const)
  have hintA : ∀ s : ℝ, IntervalIntegrable
      (fun _ : ℝ => deriv (deriv (deBruijnNewmanH t)) w * ((s : ℂ) * k))
      MeasureTheory.volume 0 1 :=
    fun _ => intervalIntegrable_const
  have hintB : ∀ s : ℝ, IntervalIntegrable
      (fun r : ℝ => (∫ q : ℝ in (0:ℝ)..1,
          iteratedDeriv 3 (deBruijnNewmanH t) (w + ((q * r * s : ℝ) : ℂ) * k)
            * (((r * s : ℝ) : ℂ) * k)) * ((s : ℂ) * k))
      MeasureTheory.volume 0 1 :=
    fun s => (hcontB s).continuousOn.intervalIntegrable
  -- split the r-integral into the constant (D2) part and the q-integral part
  have hsplit : ∀ s : ℝ,
      (∫ r : ℝ in (0:ℝ)..1,
        deriv (deriv (deBruijnNewmanH t)) (w + ((r * s : ℝ) : ℂ) * k) * ((s : ℂ) * k))
      = (∫ r : ℝ in (0:ℝ)..1, deriv (deriv (deBruijnNewmanH t)) w * ((s : ℂ) * k))
        + ∫ r : ℝ in (0:ℝ)..1,
          (∫ q : ℝ in (0:ℝ)..1,
            iteratedDeriv 3 (deBruijnNewmanH t) (w + ((q * r * s : ℝ) : ℂ) * k)
              * (((r * s : ℝ) : ℂ) * k)) * ((s : ℂ) * k) := by
    intro s
    rw [intervalIntegral.integral_congr fun r _ => hpt s r]
    exact intervalIntegral.integral_add (hintA s) (hintB s)
  have hconst : ∀ s : ℝ,
      (∫ r : ℝ in (0:ℝ)..1, deriv (deriv (deBruijnNewmanH t)) w * ((s : ℂ) * k))
      = deriv (deriv (deBruijnNewmanH t)) w * ((s : ℂ) * k) := by
    intro s
    rw [intervalIntegral.integral_const]
    simp
  -- the outer s-integral of the constant part is `D2(w)·k²/2`
  have houter : (∫ s : ℝ in (0:ℝ)..1,
      deriv (deriv (deBruijnNewmanH t)) w * ((s : ℂ) * k) * k)
      = deriv (deriv (deBruijnNewmanH t)) w * k ^ 2 / 2 := by
    have heq : ∀ s : ℝ,
        deriv (deriv (deBruijnNewmanH t)) w * ((s : ℂ) * k) * k
        = (deriv (deriv (deBruijnNewmanH t)) w * k ^ 2) * (s : ℂ) := by
      intro s
      ring
    rw [intervalIntegral.integral_congr fun s _ => heq s]
    have e : (∫ s : ℝ in (0:ℝ)..1,
        (deriv (deriv (deBruijnNewmanH t)) w * k ^ 2) * (s : ℂ))
        = (deriv (deriv (deBruijnNewmanH t)) w * k ^ 2)
          * ∫ s : ℝ in (0:ℝ)..1, (s : ℂ) :=
      intervalIntegral.integral_const_mul _ _
    have e2 : (∫ s : ℝ in (0:ℝ)..1, (s : ℂ)) = ↑(∫ s : ℝ in (0:ℝ)..1, s) :=
      intervalIntegral.integral_ofReal
    have h3 : (∫ s : ℝ in (0:ℝ)..1, s) = 1 / 2 := by
      rw [integral_id]
      norm_num
    rw [e, e2, h3]
    push_cast
    ring
  -- continuity of the double parametric integral (in `s`), for the final split
  have hcont2 : Continuous fun s : ℝ =>
      (∫ r : ℝ in (0:ℝ)..1,
        (∫ q : ℝ in (0:ℝ)..1,
          iteratedDeriv 3 (deBruijnNewmanH t) (w + ((q * r * s : ℝ) : ℂ) * k)
            * (((r * s : ℝ) : ℂ) * k)) * ((s : ℂ) * k)) * k := by
    refine Continuous.mul ?_ continuous_const
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      ?_ 0 1
    refine Continuous.mul ?_ ?_
    · refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        ?_ 0 1
      exact (continuous_deBruijnNewmanH_zderiv_three.comp
        (continuous_const.prodMk (continuous_const.add
          ((Complex.continuous_ofReal.comp
            ((continuous_snd.mul continuous_fst.snd).mul
              continuous_fst.fst)).mul continuous_const)))).mul
        ((Complex.continuous_ofReal.comp
          (continuous_fst.snd.mul continuous_fst.fst)).mul continuous_const)
    · exact (Complex.continuous_ofReal.comp continuous_fst).mul continuous_const
  have hI1 : IntervalIntegrable
      (fun s : ℝ => deriv (deriv (deBruijnNewmanH t)) w * ((s : ℂ) * k) * k)
      MeasureTheory.volume 0 1 :=
    ((continuous_const.mul
      (Complex.continuous_ofReal.mul continuous_const)).mul
      continuous_const).continuousOn.intervalIntegrable
  have hI2 : IntervalIntegrable
      (fun s : ℝ => (∫ r : ℝ in (0:ℝ)..1,
        (∫ q : ℝ in (0:ℝ)..1,
          iteratedDeriv 3 (deBruijnNewmanH t) (w + ((q * r * s : ℝ) : ℂ) * k)
            * (((r * s : ℝ) : ℂ) * k)) * ((s : ℂ) * k)) * k)
      MeasureTheory.volume 0 1 :=
    hcont2.continuousOn.intervalIntegrable
  -- assemble: the order-1 remainder equals `D2(w)·k²/2 + R₃`
  have key : (∫ s : ℝ in (0:ℝ)..1,
        (∫ r : ℝ in (0:ℝ)..1,
          deriv (deriv (deBruijnNewmanH t)) (w + ((r * s : ℝ) : ℂ) * k)
            * ((s : ℂ) * k)) * k)
      = deriv (deriv (deBruijnNewmanH t)) w * k ^ 2 / 2
        + ∫ s : ℝ in (0:ℝ)..1,
          (∫ r : ℝ in (0:ℝ)..1,
            (∫ q : ℝ in (0:ℝ)..1,
              iteratedDeriv 3 (deBruijnNewmanH t) (w + ((q * r * s : ℝ) : ℂ) * k)
                * (((r * s : ℝ) : ℂ) * k))
              * ((s : ℂ) * k)) * k := by
    have houter' : ∀ s : ℝ,
        (∫ r : ℝ in (0:ℝ)..1,
          deriv (deriv (deBruijnNewmanH t)) (w + ((r * s : ℝ) : ℂ) * k)
            * ((s : ℂ) * k)) * k
        = deriv (deriv (deBruijnNewmanH t)) w * ((s : ℂ) * k) * k
          + (∫ r : ℝ in (0:ℝ)..1,
            (∫ q : ℝ in (0:ℝ)..1,
              iteratedDeriv 3 (deBruijnNewmanH t) (w + ((q * r * s : ℝ) : ℂ) * k)
                * (((r * s : ℝ) : ℂ) * k)) * ((s : ℂ) * k)) * k := by
      intro s
      rw [hsplit s, hconst s, add_mul]
    rw [intervalIntegral.integral_congr fun s _ => houter' s,
      intervalIntegral.integral_add hI1 hI2, houter]
  rw [deBruijnNewmanH_taylor_two_z, key]
  ac_rfl

/-- **Cubic bound on the order-2 Taylor remainder**: if `∂³_z H_t` is bounded by
`M` on the segment from `w` to `w + k`, then the remainder in
`deBruijnNewmanH_taylor_three_z` is at most `M·‖k‖³`. Three nested
`intervalIntegral.norm_integral_le_of_norm_le_const` applications. This is the
quantitative form needed to exclude non-real zeros of `H_t` near an
exactly-double real zero after the collision (the quadratic term dominates the
remainder on scales `‖k‖ ≲ √(t − τ)`). -/
theorem deBruijnNewmanH_taylor_three_z_remainder_norm_le (t : ℝ) (w k : ℂ) (M : ℝ)
    (hM : ∀ q r s : ℝ, q ∈ Set.Icc (0 : ℝ) 1 → r ∈ Set.Icc (0 : ℝ) 1
      → s ∈ Set.Icc (0 : ℝ) 1 →
      ‖iteratedDeriv 3 (deBruijnNewmanH t) (w + ((q * r * s : ℝ) : ℂ) * k)‖ ≤ M) :
    ‖deBruijnNewmanH t (w + k)
        - (deBruijnNewmanH t w + deriv (deBruijnNewmanH t) w * k
          + deriv (deriv (deBruijnNewmanH t)) w * k ^ 2 / 2)‖
      ≤ M * ‖k‖ ^ 3 := by
  have hMnn : 0 ≤ M :=
    (norm_nonneg _).trans (hM 1 1 1 (by norm_num) (by norm_num) (by norm_num))
  have hIoc : ∀ x : ℝ, x ∈ Set.uIoc (0 : ℝ) 1 → 0 < x ∧ x ≤ 1 := by
    intro x hx
    rw [Set.uIoc_of_le zero_le_one] at hx
    exact hx
  rw [deBruijnNewmanH_taylor_three_z, add_sub_cancel_left]
  have hq : ∀ r s : ℝ, r ∈ Set.uIoc (0 : ℝ) 1 → s ∈ Set.uIoc (0 : ℝ) 1 →
      ‖∫ q : ℝ in (0:ℝ)..1,
        iteratedDeriv 3 (deBruijnNewmanH t) (w + ((q * r * s : ℝ) : ℂ) * k)
          * (((r * s : ℝ) : ℂ) * k)‖
      ≤ M * ‖k‖ := by
    intro r s hr hs
    obtain ⟨hr0, hr1⟩ := hIoc r hr
    obtain ⟨hs0, hs1⟩ := hIoc s hs
    have hpt : ∀ q ∈ Set.uIoc (0 : ℝ) 1,
        ‖iteratedDeriv 3 (deBruijnNewmanH t) (w + ((q * r * s : ℝ) : ℂ) * k)
          * (((r * s : ℝ) : ℂ) * k)‖
        ≤ M * ‖k‖ := by
      intro q hqI
      obtain ⟨hq0, hq1⟩ := hIoc q hqI
      have hn : ‖(((r * s : ℝ) : ℂ) * k)‖ ≤ ‖k‖ := by
        have e : ‖(((r * s : ℝ) : ℂ) * k)‖ = (r * s) * ‖k‖ := by
          rw [norm_mul]
          have e2 : ‖((r * s : ℝ) : ℂ)‖ = |r * s| := RCLike.norm_ofReal _
          rw [e2, abs_of_nonneg (mul_nonneg hr0.le hs0.le)]
        rw [e]
        calc (r * s) * ‖k‖ ≤ (1 * 1) * ‖k‖ :=
              mul_le_mul (mul_le_mul hr1 hs1 hs0.le zero_le_one) (le_refl ‖k‖)
                (norm_nonneg _) (by norm_num)
          _ = ‖k‖ := by rw [mul_one, one_mul]
      rw [norm_mul]
      exact mul_le_mul (hM q r s ⟨hq0.le, hq1⟩ ⟨hr0.le, hr1⟩ ⟨hs0.le, hs1⟩) hn
        (norm_nonneg _) hMnn
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (C := M * ‖k‖) hpt
    rwa [sub_zero, abs_one, mul_one] at h1
  have hr : ∀ s : ℝ, s ∈ Set.uIoc (0 : ℝ) 1 →
      ‖∫ r : ℝ in (0:ℝ)..1,
        (∫ q : ℝ in (0:ℝ)..1,
          iteratedDeriv 3 (deBruijnNewmanH t) (w + ((q * r * s : ℝ) : ℂ) * k)
            * (((r * s : ℝ) : ℂ) * k)) * ((s : ℂ) * k)‖
      ≤ M * ‖k‖ ^ 2 := by
    intro s hs
    obtain ⟨hs0, hs1⟩ := hIoc s hs
    have hpt : ∀ r ∈ Set.uIoc (0 : ℝ) 1,
        ‖(∫ q : ℝ in (0:ℝ)..1,
          iteratedDeriv 3 (deBruijnNewmanH t) (w + ((q * r * s : ℝ) : ℂ) * k)
            * (((r * s : ℝ) : ℂ) * k)) * ((s : ℂ) * k)‖
        ≤ M * ‖k‖ ^ 2 := by
      intro r hrI
      obtain ⟨hr0, hr1⟩ := hIoc r hrI
      have hn : ‖((s : ℂ) * k)‖ ≤ ‖k‖ := by
        have e : ‖((s : ℂ) * k)‖ = s * ‖k‖ := by
          rw [norm_mul]
          have e2 : ‖(s : ℂ)‖ = |s| := RCLike.norm_ofReal _
          rw [e2, abs_of_nonneg hs0.le]
        rw [e]
        calc s * ‖k‖ ≤ 1 * ‖k‖ :=
              mul_le_mul hs1 (le_refl ‖k‖) (norm_nonneg _) zero_le_one
          _ = ‖k‖ := one_mul _
      calc ‖(∫ q : ℝ in (0:ℝ)..1,
            iteratedDeriv 3 (deBruijnNewmanH t) (w + ((q * r * s : ℝ) : ℂ) * k)
              * (((r * s : ℝ) : ℂ) * k)) * ((s : ℂ) * k)‖
          = ‖∫ q : ℝ in (0:ℝ)..1,
              iteratedDeriv 3 (deBruijnNewmanH t) (w + ((q * r * s : ℝ) : ℂ) * k)
                * (((r * s : ℝ) : ℂ) * k)‖ * ‖((s : ℂ) * k)‖ :=
            norm_mul _ _
        _ ≤ (M * ‖k‖) * ‖k‖ :=
            mul_le_mul (hq r s hrI hs) hn (norm_nonneg _)
              (mul_nonneg hMnn (norm_nonneg _))
        _ = M * ‖k‖ ^ 2 := by rw [mul_assoc, ← pow_two]
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const
      (C := M * ‖k‖ ^ 2) hpt
    rwa [sub_zero, abs_one, mul_one] at h1
  have hpt : ∀ s ∈ Set.uIoc (0 : ℝ) 1,
      ‖(∫ r : ℝ in (0:ℝ)..1,
        (∫ q : ℝ in (0:ℝ)..1,
          iteratedDeriv 3 (deBruijnNewmanH t) (w + ((q * r * s : ℝ) : ℂ) * k)
            * (((r * s : ℝ) : ℂ) * k)) * ((s : ℂ) * k)) * k‖
      ≤ M * ‖k‖ ^ 3 := by
    intro s hs
    calc ‖(∫ r : ℝ in (0:ℝ)..1,
          (∫ q : ℝ in (0:ℝ)..1,
            iteratedDeriv 3 (deBruijnNewmanH t) (w + ((q * r * s : ℝ) : ℂ) * k)
              * (((r * s : ℝ) : ℂ) * k)) * ((s : ℂ) * k)) * k‖
        = ‖∫ r : ℝ in (0:ℝ)..1,
            (∫ q : ℝ in (0:ℝ)..1,
              iteratedDeriv 3 (deBruijnNewmanH t) (w + ((q * r * s : ℝ) : ℂ) * k)
                * (((r * s : ℝ) : ℂ) * k)) * ((s : ℂ) * k)‖ * ‖k‖ :=
          norm_mul _ _
      _ ≤ (M * ‖k‖ ^ 2) * ‖k‖ :=
          mul_le_mul (hr s hs) (le_refl ‖k‖) (norm_nonneg _)
            (mul_nonneg hMnn (sq_nonneg _))
      _ = M * ‖k‖ ^ 3 := by
          rw [mul_assoc, ← pow_succ]
  have h1 := intervalIntegral.norm_integral_le_of_norm_le_const
    (C := M * ‖k‖ ^ 3) hpt
  rwa [sub_zero, abs_one, mul_one] at h1

/-- **Lipschitz bound for `∂²_z H_t` from a bound on `∂³_z H_t`**: if
`‖∂³_z H_t‖ ≤ M` on the segment from `w` to `w + k`, then
`‖∂²_z H_t(w + k) − ∂²_z H_t(w)‖ ≤ M·‖k‖`. One
`intervalIntegral.norm_integral_le_of_norm_le_const` application to the
z-direction FTC `deBruijnNewmanHzderiv_two_z_sub_eq_intervalIntegral`. Used in
the double-zero exclusion to linearize `∂_z H_t` around the critical curve. -/
theorem deBruijnNewmanHzderiv_two_lipschitz (t : ℝ) (w k : ℂ) (M : ℝ)
    (hM : ∀ q : ℝ, q ∈ Set.Icc (0 : ℝ) 1 →
      ‖iteratedDeriv 3 (deBruijnNewmanH t) (w + (q : ℂ) * k)‖ ≤ M) :
    ‖deriv (deriv (deBruijnNewmanH t)) (w + k) - deriv (deriv (deBruijnNewmanH t)) w‖
      ≤ M * ‖k‖ := by
  have hMnn : 0 ≤ M := (norm_nonneg _).trans (hM 1 (by norm_num))
  rw [deBruijnNewmanHzderiv_two_z_sub_eq_intervalIntegral]
  have hpt : ∀ q ∈ Set.uIoc (0 : ℝ) 1,
      ‖iteratedDeriv 3 (deBruijnNewmanH t) (w + (q : ℂ) * k) * k‖ ≤ M * ‖k‖ := by
    intro q hq
    rw [Set.uIoc_of_le zero_le_one] at hq
    rw [norm_mul]
    exact mul_le_mul (hM q ⟨hq.1.le, hq.2⟩) (le_refl ‖k‖) (norm_nonneg _) hMnn
  have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (C := M * ‖k‖) hpt
  rwa [sub_zero, abs_one, mul_one] at h1

/-- **Injectivity from a near-constant derivative**: if on the segment from
`z₂` to `z₁` the `z`-derivative of `H_t` deviates from a nonzero constant `A`
by at most `‖A‖/2`, then `H_t z₁ = H_t z₂` forces `z₁ = z₂`. Proof: the
z-direction FTC writes `H_t z₁ − H_t z₂ = A·(z₁−z₂) + E` with
`‖E‖ ≤ (‖A‖/2)·‖z₁−z₂‖`, so `‖A‖·‖z₁−z₂‖ ≤ (‖A‖/2)·‖z₁−z₂‖` and `z₁ = z₂`.
This is the uniqueness engine of the double-zero exclusion: applied on the
small disks around `c(t) ± √q` with `A = ∂²_z H_t(c(t))·(±√q)`, together with
conjugation it forces the unique zero in each disk to be real. -/
theorem deBruijnNewman_eq_of_deriv_near_const (t : ℝ) (z₁ z₂ A : ℂ) (hA : A ≠ 0)
    (hdev : ∀ u : ℝ, u ∈ Set.uIcc (0:ℝ) 1 →
      ‖deriv (deBruijnNewmanH t) (z₂ + (u : ℂ) * (z₁ - z₂)) - A‖ ≤ ‖A‖ / 2)
    (heq : deBruijnNewmanH t z₁ = deBruijnNewmanH t z₂) :
    z₁ = z₂ := by
  have hApos : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have hftc := deBruijnNewmanH_z_sub_eq_intervalIntegral t z₂ (z₁ - z₂)
  rw [show z₂ + (z₁ - z₂) = z₁ from by ring, heq, sub_self] at hftc
  set k : ℂ := z₁ - z₂ with hkdef
  have hconst : (∫ u : ℝ in (0:ℝ)..1, A * k) = A * k := by
    rw [intervalIntegral.integral_const]
    simp
  have hintD : IntervalIntegrable
      (fun u : ℝ => deriv (deBruijnNewmanH t) (z₂ + (u : ℂ) * k) * k)
      MeasureTheory.volume 0 1 :=
    ((continuous_deBruijnNewmanH_zderiv.comp
      (continuous_const.prodMk
        ((Complex.continuous_ofReal.mul continuous_const).const_add z₂))).mul
      continuous_const).continuousOn.intervalIntegrable
  have hintC : IntervalIntegrable (fun _ : ℝ => A * k) MeasureTheory.volume 0 1 :=
    intervalIntegrable_const
  have hsplit : (∫ u : ℝ in (0:ℝ)..1,
        deriv (deBruijnNewmanH t) (z₂ + (u : ℂ) * k) * k)
      = A * k + ∫ u : ℝ in (0:ℝ)..1,
        (deriv (deBruijnNewmanH t) (z₂ + (u : ℂ) * k) * k - A * k) := by
    have hpt : ∀ u : ℝ,
        deriv (deBruijnNewmanH t) (z₂ + (u : ℂ) * k) * k
        = A * k + (deriv (deBruijnNewmanH t) (z₂ + (u : ℂ) * k) * k - A * k) := by
      intro u
      ring
    rw [intervalIntegral.integral_congr fun u _ => hpt u,
      intervalIntegral.integral_add hintC (hintD.sub hintC), hconst]
  have hE : ‖∫ u : ℝ in (0:ℝ)..1,
        (deriv (deBruijnNewmanH t) (z₂ + (u : ℂ) * k) * k - A * k)‖
      ≤ ‖A‖ / 2 * ‖k‖ := by
    have hpt : ∀ u ∈ Set.uIoc (0:ℝ) 1,
        ‖deriv (deBruijnNewmanH t) (z₂ + (u : ℂ) * k) * k - A * k‖
        ≤ ‖A‖ / 2 * ‖k‖ := by
      intro u hu
      have hu' : u ∈ Set.uIcc (0:ℝ) 1 := by
        rw [Set.uIoc_of_le zero_le_one] at hu
        exact Set.mem_uIcc.mpr (Or.inl ⟨hu.1.le, hu.2⟩)
      have e : deriv (deBruijnNewmanH t) (z₂ + (u : ℂ) * k) * k - A * k
          = (deriv (deBruijnNewmanH t) (z₂ + (u : ℂ) * k) - A) * k :=
        (sub_mul _ _ _).symm
      rw [e, norm_mul]
      exact mul_le_mul (hdev u hu') (le_refl ‖k‖) (norm_nonneg _)
        (div_nonneg hApos.le zero_le_two)
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const
      (C := ‖A‖ / 2 * ‖k‖) hpt
    rwa [sub_zero, abs_one, mul_one] at h1
  rw [hsplit] at hftc
  have hnorm : ‖A‖ * ‖k‖ ≤ ‖A‖ / 2 * ‖k‖ := by
    have h1 : A * k = -(∫ u : ℝ in (0:ℝ)..1,
        (deriv (deBruijnNewmanH t) (z₂ + (u : ℂ) * k) * k - A * k)) :=
      eq_neg_of_add_eq_zero_left hftc.symm
    calc ‖A‖ * ‖k‖ = ‖A * k‖ := by rw [norm_mul]
      _ ≤ ‖A‖ / 2 * ‖k‖ := by rw [h1, norm_neg]; exact hE
  have hk0 : ‖k‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖k‖ := lt_of_le_of_ne (norm_nonneg k) (Ne.symm hne)
    have h2 : ‖A‖ ≤ ‖A‖ / 2 := le_of_mul_le_mul_right hnorm hpos
    linarith [hApos]
  exact sub_eq_zero.mp (norm_eq_zero.mp hk0)

/-- **Conjugation symmetry of the second `z`-derivative**: `∂²_z H_t(\bar z)
= \overline{∂²_z H_t(z)}`, transported through the integral representation
`deriv_two_deBruijnNewmanH` by `Complex.cos_conj`. Together with the heat
equation this is what makes the curvature at a real double zero real. -/
theorem deBruijnNewmanHzderiv_two_conj (t : ℝ) (z : ℂ) :
    deriv (deriv (deBruijnNewmanH t)) (star z)
      = star (deriv (deriv (deBruijnNewmanH t)) z) := by
  rw [deriv_two_deBruijnNewmanH, deriv_two_deBruijnNewmanH]
  show (∫ (u : ℝ) in Set.Ioi 0, -((u : ℂ) ^ 2) * heatIntegrand t (star z) u)
      = (starRingEnd ℂ) (∫ (u : ℝ) in Set.Ioi 0, -((u : ℂ) ^ 2) * heatIntegrand t z u)
  have e1 : (starRingEnd ℂ) (∫ (u : ℝ) in Set.Ioi 0, -((u : ℂ) ^ 2) * heatIntegrand t z u)
      = ∫ (u : ℝ) in Set.Ioi 0, (starRingEnd ℂ) (-((u : ℂ) ^ 2) * heatIntegrand t z u) :=
    (integral_conj (f := fun u : ℝ => -((u : ℂ) ^ 2) * heatIntegrand t z u)
      (μ := MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)))).symm
  refine Eq.trans ?_ e1.symm
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro u _
  show -((u : ℂ) ^ 2) * (((Real.exp (t * u ^ 2) * phi u : ℝ) : ℂ)
      * Complex.cos ((starRingEnd ℂ) z * (u : ℂ)))
      = (starRingEnd ℂ) (-((u : ℂ) ^ 2) * (((Real.exp (t * u ^ 2) * phi u : ℝ) : ℂ)
        * Complex.cos (z * (u : ℂ))))
  rw [map_mul, map_neg, map_pow, Complex.conj_ofReal, map_mul, Complex.conj_ofReal,
    ← Complex.cos_conj, map_mul, Complex.conj_ofReal]

/-- **Reality of `H_t` at real points**: if `z.im = 0` then `(H_t z).im = 0`,
from the conjugation symmetry `deBruijnNewmanH_conj`. -/
theorem deBruijnNewmanH_im_eq_zero_of_im_eq_zero (t : ℝ) {z : ℂ} (hz : z.im = 0) :
    (deBruijnNewmanH t z).im = 0 := by
  have hstar : star z = z := by
    rw [Complex.star_def, Complex.conj_eq_iff_im]; exact hz
  have h := deBruijnNewmanH_conj t z
  rw [hstar, Complex.star_def] at h
  exact Complex.conj_eq_iff_im.mp h.symm

/-- **Reality of `∂_z H_t` at real points**. -/
theorem deBruijnNewmanHzderiv_im_eq_zero_of_im_eq_zero (t : ℝ) {z : ℂ} (hz : z.im = 0) :
    (deriv (deBruijnNewmanH t) z).im = 0 := by
  have hstar : star z = z := by
    rw [Complex.star_def, Complex.conj_eq_iff_im]; exact hz
  have h := deBruijnNewmanHzderiv_conj t z
  rw [hstar, Complex.star_def] at h
  exact Complex.conj_eq_iff_im.mp h.symm

/-- **Reality of `∂²_z H_t` at real points**. -/
theorem deBruijnNewmanHzderiv_two_im_eq_zero_of_im_eq_zero (t : ℝ) {z : ℂ}
    (hz : z.im = 0) : (deriv (deriv (deBruijnNewmanH t)) z).im = 0 := by
  have hstar : star z = z := by
    rw [Complex.star_def, Complex.conj_eq_iff_im]; exact hz
  have h := deBruijnNewmanHzderiv_two_conj t z
  rw [hstar, Complex.star_def] at h
  exact Complex.conj_eq_iff_im.mp h.symm

/-- **Height–curvature sign opposition along the critical curve (quantitative)**:
at an exactly double real zero `x₀` of `H_τ` (with critical curve `c`), for
`t > τ` sufficiently close, `H_t(c(t))` and `∂²_z H_t(c(t))` are both real and
their (real) product is negative with the quantitative bound
`Re H_t(c(t)) · Re ∂²_z H_t(c(t)) ≤ −(Re ∂²_z H_τ(x₀))²·(t−τ)/4`. Proof: the
height evolves as `H_t(c(t)) = −∫_τ^t ∂²_z H_s(c(s)) ds` (`critical_height` +
backward heat equation), and the curvature stays within `|B|/2` of
`B = Re ∂²_z H_τ(x₀) ≠ 0` by continuity, so the integrand `g(s)·g(t)` is at
least `B²/4` pointwise. This is what makes the quadratic model
`H_t(c(t)) + ½·∂²_z H_t(c(t))·w²` open upward in the real direction for
`t > τ` — the sign pillar of the double-zero exclusion. -/
theorem deBruijnNewman_double_zero_height_mul_curvature (τ : ℝ) (x₀ : ℂ) (c : ℝ → ℂ)
    (hcont : ContinuousAt c τ)
    (hcdiff : ∀ᶠ t in nhds τ, DifferentiableAt ℝ c t)
    (hcrit : ∀ᶠ t in nhds τ, deriv (deBruijnNewmanH t) (c t) = 0)
    (hcreal : ∀ᶠ t in nhds τ, (c t).im = 0)
    (hc0 : c τ = x₀) (hz0 : deBruijnNewmanH τ x₀ = 0)
    (hB : deriv (deriv (deBruijnNewmanH τ)) x₀ ≠ 0)
    (hx : x₀.im = 0) :
    ∀ᶠ t in nhdsWithin τ (Set.Ioi τ),
      (deBruijnNewmanH t (c t)).im = 0
        ∧ (deriv (deriv (deBruijnNewmanH t)) (c t)).im = 0
        ∧ (deBruijnNewmanH t (c t)).re * (deriv (deriv (deBruijnNewmanH t)) (c t)).re
          ≤ -((deriv (deriv (deBruijnNewmanH τ)) x₀).re ^ 2 / 4) * (t - τ) := by
  have hBim : (deriv (deriv (deBruijnNewmanH τ)) x₀).im = 0 :=
    deBruijnNewmanHzderiv_two_im_eq_zero_of_im_eq_zero τ hx
  set B : ℝ := (deriv (deriv (deBruijnNewmanH τ)) x₀).re with hBdef
  have hBne : B ≠ 0 := by
    intro e
    apply hB
    have h := (Complex.re_add_im (deriv (deriv (deBruijnNewmanH τ)) x₀)).symm
    rw [hBim, Complex.ofReal_zero, zero_mul, add_zero, ← hBdef, e,
      Complex.ofReal_zero] at h
    exact h
  -- windows: height formula, differentiability, reality, curvature closeness
  have hh := deBruijnNewmanH_critical_height τ x₀ c hcdiff hcrit hc0 hz0
  have hgCA : ∀ s : ℝ, DifferentiableAt ℝ c s →
      ContinuousAt (fun r : ℝ => (deriv (deriv (deBruijnNewmanH r)) (c r)).re) s := by
    intro s hs
    have h2 : ContinuousAt (fun r : ℝ => (r, c r)) s :=
      continuousAt_id.prodMk hs.continuousAt
    have h3 : ContinuousAt
        ((fun p : ℝ × ℂ => deriv (deriv (deBruijnNewmanH p.1)) p.2)
          ∘ fun r : ℝ => (r, c r)) s :=
      continuous_deBruijnNewmanH_deriv_two.continuousAt.comp h2
    have h4 : ContinuousAt
        ((fun z : ℂ => z.re)
          ∘ ((fun p : ℝ × ℂ => deriv (deriv (deBruijnNewmanH p.1)) p.2)
            ∘ fun r : ℝ => (r, c r))) s :=
      Complex.continuous_re.continuousAt.comp h3
    exact h4
  have hgτ : (deriv (deriv (deBruijnNewmanH τ)) (c τ)).re = B := by
    rw [hc0]
  have hwin : ∀ᶠ s in nhds τ,
      |(deriv (deriv (deBruijnNewmanH s)) (c s)).re - B| < |B| / 2 := by
    obtain ⟨ε, hε, hεP⟩ := Metric.continuousAt_iff.mp
      (hgCA τ (hcdiff.self_of_nhds)) (|B| / 2)
      (div_pos (abs_pos.mpr hBne) two_pos)
    refine Filter.mem_of_superset (Metric.ball_mem_nhds τ hε) fun s hs => ?_
    have h1 := hεP (Metric.mem_ball.mp hs)
    rw [hgτ, Real.dist_eq] at h1
    exact h1
  rw [Metric.eventually_nhds_iff] at hh hcreal hwin hcdiff
  obtain ⟨δ₀, hδ₀, hH0⟩ := hh
  obtain ⟨δ₁, hδ₁, hD1⟩ := hcdiff
  obtain ⟨δ₃, hδ₃, hR3⟩ := hcreal
  obtain ⟨δ₄, hδ₄, hW4⟩ := hwin
  set δ : ℝ := min δ₀ (min δ₁ (min δ₃ δ₄)) with hδdef
  have hδ : 0 < δ := lt_min_iff.mpr ⟨hδ₀, lt_min_iff.mpr ⟨hδ₁, lt_min_iff.mpr ⟨hδ₃, hδ₄⟩⟩⟩
  have hball : ∀ᶠ t in nhdsWithin τ (Set.Ioi τ), dist t τ < δ := by
    have hb : ∀ᶠ s in nhds τ, dist s τ < δ := Metric.ball_mem_nhds τ hδ
    exact hb.filter_mono nhdsWithin_le_nhds
  filter_upwards [hball, self_mem_nhdsWithin] with t htδ htI
  have ht : τ < t := htI
  have hdist_le : ∀ s : ℝ, s ∈ Set.Icc τ t → dist s τ < δ := by
    intro s hs
    have h1 : dist s τ ≤ dist t τ := by
      rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.le),
        abs_of_nonneg (sub_nonneg.mpr hs.1)]
      exact sub_le_sub_right hs.2 τ
    exact lt_of_le_of_lt h1 htδ
  have htδ0 : dist t τ < δ₀ := lt_of_lt_of_le htδ (min_le_left _ _)
  have htδ3 : dist t τ < δ₃ := lt_of_lt_of_le htδ
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have htδ4 : dist t τ < δ₄ := lt_of_lt_of_le htδ
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hs1of : ∀ s : ℝ, s ∈ Set.Icc τ t → dist s τ < δ₁ :=
    fun s hs => lt_of_lt_of_le (hdist_le s hs)
      (le_trans (min_le_right _ _) (min_le_left _ _))
  have hs3of : ∀ s : ℝ, s ∈ Set.Icc τ t → dist s τ < δ₃ :=
    fun s hs => lt_of_lt_of_le (hdist_le s hs)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hs4of : ∀ s : ℝ, s ∈ Set.Icc τ t → dist s τ < δ₄ :=
    fun s hs => lt_of_lt_of_le (hdist_le s hs)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  -- reality of both values at time `t`
  have him1 : (deBruijnNewmanH t (c t)).im = 0 :=
    deBruijnNewmanH_im_eq_zero_of_im_eq_zero t (hR3 htδ3)
  have him2 : (deriv (deriv (deBruijnNewmanH t)) (c t)).im = 0 :=
    deBruijnNewmanHzderiv_two_im_eq_zero_of_im_eq_zero t (hR3 htδ3)
  refine ⟨him1, him2, ?_⟩
  -- the height formula in real form: `Re H_t(c(t)) = −∫_τ^t g`
  have hre : (deBruijnNewmanH t (c t)).re
      = -∫ s : ℝ in τ..t, (deriv (deriv (deBruijnNewmanH s)) (c s)).re := by
    have h1 := hH0 htδ0
    have hJ : ∀ s : ℝ, s ∈ Set.uIcc τ t →
        (∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand s (c s) u)
        = ((-((deriv (deriv (deBruijnNewmanH s)) (c s)).re) : ℝ) : ℂ) := by
      intro s hsI
      have hsI' : s ∈ Set.Icc τ t := Set.uIcc_of_le ht.le ▸ hsI
      have h2 := deBruijnNewmanH_heat_equation s (c s)
      have h3 : iteratedDeriv 2 (deBruijnNewmanH s) (c s)
          = deriv (deriv (deBruijnNewmanH s)) (c s) := by
        rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
      have h23 : -(∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand s (c s) u)
          = deriv (deriv (deBruijnNewmanH s)) (c s) := h2.symm.trans h3
      have h4 : (∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand s (c s) u)
          = -deriv (deriv (deBruijnNewmanH s)) (c s) :=
        neg_eq_iff_eq_neg.mp h23
      have h5 : (deriv (deriv (deBruijnNewmanH s)) (c s)).im = 0 :=
        deBruijnNewmanHzderiv_two_im_eq_zero_of_im_eq_zero s (hR3 (hs3of s hsI'))
      have h6 : deriv (deriv (deBruijnNewmanH s)) (c s)
          = ((deriv (deriv (deBruijnNewmanH s)) (c s)).re : ℂ) := by
        have h := (Complex.re_add_im (deriv (deriv (deBruijnNewmanH s)) (c s))).symm
        rwa [h5, Complex.ofReal_zero, zero_mul, add_zero] at h
      rw [h4, h6]
      simp only [Complex.ofReal_re, Complex.ofReal_neg]
    have hInt : (∫ s : ℝ in τ..t,
        ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand s (c s) u)
        = ∫ s : ℝ in τ..t,
          ((-((deriv (deriv (deBruijnNewmanH s)) (c s)).re) : ℝ) : ℂ) :=
      intervalIntegral.integral_congr fun s hs => hJ s hs
    rw [h1, hInt, intervalIntegral.integral_ofReal]
    simp only [Complex.ofReal_re, intervalIntegral.integral_neg]
  -- pointwise curvature product bound `g(s)·g(t) ≥ B²/4`
  have hgt : ∀ s : ℝ, s ∈ Set.Icc τ t →
      B ^ 2 / 4 ≤ (deriv (deriv (deBruijnNewmanH s)) (c s)).re
        * (deriv (deriv (deBruijnNewmanH t)) (c t)).re := by
    intro s hs
    have h1 := abs_lt.mp (hW4 (hs4of s hs))
    have h2 := abs_lt.mp (hW4 htδ4)
    rcases lt_or_gt_of_ne hBne with hB' | hB'
    · have hb : |B| = -B := abs_of_neg hB'
      rw [hb] at h1 h2
      have hg1 : (deriv (deriv (deBruijnNewmanH s)) (c s)).re < B / 2 := by
        linarith [h1.2]
      have hg2 : (deriv (deriv (deBruijnNewmanH t)) (c t)).re < B / 2 := by
        linarith [h2.2]
      have hnb : (0 : ℝ) < -B / 2 := by linarith
      calc B ^ 2 / 4 = (-B / 2) * (-B / 2) := by ring
        _ ≤ (-(deriv (deriv (deBruijnNewmanH s)) (c s)).re)
            * (-(deriv (deriv (deBruijnNewmanH t)) (c t)).re) :=
          mul_le_mul (by linarith) (by linarith) hnb.le (by linarith)
        _ = (deriv (deriv (deBruijnNewmanH s)) (c s)).re
            * (deriv (deriv (deBruijnNewmanH t)) (c t)).re := by
          rw [neg_mul_neg]
    · have hb : |B| = B := abs_of_pos hB'
      rw [hb] at h1 h2
      have hg1 : B / 2 < (deriv (deriv (deBruijnNewmanH s)) (c s)).re := by
        linarith [h1.1]
      have hg2 : B / 2 < (deriv (deriv (deBruijnNewmanH t)) (c t)).re := by
        linarith [h2.1]
      calc B ^ 2 / 4 = (B / 2) * (B / 2) := by ring
        _ ≤ (deriv (deriv (deBruijnNewmanH s)) (c s)).re
            * (deriv (deriv (deBruijnNewmanH t)) (c t)).re :=
          mul_le_mul hg1.le hg2.le (by linarith) (by linarith)
  -- integrate and assemble
  have hgOn : ContinuousOn (fun s : ℝ => (deriv (deriv (deBruijnNewmanH s)) (c s)).re)
      (Set.Icc τ t) := by
    intro s hs
    exact (hgCA s (hD1 (hs1of s hs))).continuousWithinAt
  have hmono : (t - τ) * (B ^ 2 / 4)
      ≤ ∫ s : ℝ in τ..t,
        (deriv (deriv (deBruijnNewmanH s)) (c s)).re
          * (deriv (deriv (deBruijnNewmanH t)) (c t)).re := by
    have h := intervalIntegral.integral_mono_on ht.le
      (intervalIntegrable_const (μ := MeasureTheory.volume))
      ((hgOn.mul continuousOn_const).intervalIntegrable_of_Icc ht.le) hgt
    rwa [intervalIntegral.integral_const, smul_eq_mul] at h
  rw [hre, neg_mul, ← intervalIntegral.integral_mul_const]
  have hfin : -(∫ s : ℝ in τ..t,
        (deriv (deriv (deBruijnNewmanH s)) (c s)).re
          * (deriv (deriv (deBruijnNewmanH t)) (c t)).re)
      ≤ -(B ^ 2 / 4) * (t - τ) := by
    have h := neg_le_neg hmono
    rw [show -((t - τ) * (B ^ 2 / 4)) = -(B ^ 2 / 4) * (t - τ) from by ring] at h
    exact h
  exact hfin


set_option maxHeartbeats 2000000 in
/-- **Quadratic sign flip along the critical curve (quantitative core of de
Bruijn's collision alternative)**: at a real double zero `(τ, x₀)` of `H`
(`H_τ(x₀) = 0`, `∂_z H_τ(x₀) = 0`, `B := ∂²_z H_τ(x₀) ≠ 0`), with `c` the
critical curve through `x₀`, the heat equation gives
`H(t, c(t)) = −B·(t−τ) + o(t−τ)` while the second-order Taylor expansion in
`z` gives `H(t, c(t) ± 2√(t−τ)) = B·(t−τ) + o(t−τ)`: for `t` slightly
larger than `τ` the values of `H_t` at the critical point and at distance
`2√(t−τ)` on either side have opposite strict signs. All quantities are real
by Phase 2(34); the error control uses only uniform continuity of `∂²_z H`
on a compact box — no zero counting. -/
theorem deBruijnNewman_double_zero_quadratic_signs (τ : ℝ) (x₀ : ℂ) (c : ℝ → ℂ)
    (hcont : ContinuousAt c τ)
    (hcdiff : ∀ᶠ t in nhds τ, DifferentiableAt ℝ c t)
    (hcrit : ∀ᶠ t in nhds τ, deriv (deBruijnNewmanH t) (c t) = 0)
    (hcreal : ∀ᶠ t in nhds τ, (c t).im = 0)
    (hc0 : c τ = x₀)
    (hz0 : deBruijnNewmanH τ x₀ = 0)
    (hB : deriv (deriv (deBruijnNewmanH τ)) x₀ ≠ 0)
    (hx : x₀.im = 0) :
    ∀ᶠ t in nhdsWithin τ (Set.Ioi τ),
      (deBruijnNewmanH t (c t)).re
          * (deBruijnNewmanH t (c t + ((2 * Real.sqrt (t - τ) : ℝ) : ℂ))).re < 0
        ∧ (deBruijnNewmanH t (c t)).re
          * (deBruijnNewmanH t (c t + ((-(2 * Real.sqrt (t - τ)) : ℝ) : ℂ))).re < 0 := by
  set B : ℂ := deriv (deriv (deBruijnNewmanH τ)) x₀ with hBdef
  set D2 : ℝ × ℂ → ℂ := fun p => deriv (deriv (deBruijnNewmanH p.1)) p.2 with hD2def
  -- `B` is real and nonzero
  have hBim : B.im = 0 := deBruijnNewmanHzderiv_two_im_eq_zero_of_im_eq_zero τ hx
  have hBcr : B = (B.re : ℂ) := by
    nth_rewrite 1 [← Complex.re_add_im B]
    rw [hBim]
    simp
  have hBre_ne : B.re ≠ 0 := by
    intro h0
    exact hB (by rw [hBcr, h0, Complex.ofReal_zero])
  have hB_abs_pos : 0 < |B.re| := abs_pos.mpr hBre_ne
  -- uniform continuity of `∂²_z H` on the compact box `K`
  set K : Set (ℝ × ℂ) := Set.Icc (τ - 1) (τ + 1) ×ˢ Metric.closedBall x₀ 1 with hKdef
  have hKcmp : IsCompact K := isCompact_Icc.prod (isCompact_closedBall x₀ 1)
  have huc := hKcmp.uniformContinuousOn_of_continuous
    continuous_deBruijnNewmanH_deriv_two.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨η, hη0, hη⟩ := huc (|B.re| / 8) (by linarith [hB_abs_pos])
  have hD2B : ∀ p : ℝ × ℂ, p ∈ K → dist p (τ, x₀) < η →
      ‖D2 p - B‖ < |B.re| / 8 := by
    intro p hpK hpd
    have h1 := hη p hpK (τ, x₀)
      (Set.mem_prod.mpr ⟨⟨by linarith, by linarith⟩,
        Metric.mem_closedBall_self (by norm_num : (0:ℝ) ≤ 1)⟩) hpd
    rw [dist_eq_norm] at h1
    have h3 : D2 (τ, x₀) = B := rfl
    have h4 : ‖D2 p - D2 (τ, x₀)‖ < |B.re| / 8 := h1
    rwa [h3] at h4
  -- the three `nhds` eventualities and the critical height, as radii
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δc, hδc0, hδc⟩ := hcont (min (η / 4) (1 / 2))
    (lt_min_iff.mpr ⟨by linarith [hη0], by norm_num⟩)
  have hheight := deBruijnNewmanH_critical_height τ x₀ c hcdiff hcrit hc0 hz0
  rw [Metric.eventually_nhds_iff] at hheight hcrit hcreal hcdiff
  obtain ⟨δ₀, hδ₀0, hδ₀⟩ := hheight
  obtain ⟨δ₁, hδ₁0, hδ₁⟩ := hcrit
  obtain ⟨δ₂, hδ₂0, hδ₂⟩ := hcreal
  obtain ⟨δ₃, hδ₃0, hδ₃⟩ := hcdiff
  -- the master radius
  set δq : ℝ := min (min (min (min (min δ₀ δ₁) (min δ₂ δ₃)) δc) (η / 2))
    ((min (η / 8) (1 / 4)) ^ 2) with hδqdef
  have hδq0 : 0 < δq := by
    rw [hδqdef]
    refine lt_min_iff.mpr ⟨lt_min_iff.mpr ⟨lt_min_iff.mpr ⟨lt_min_iff.mpr
      ⟨lt_min_iff.mpr ⟨hδ₀0, hδ₁0⟩, lt_min_iff.mpr ⟨hδ₂0, hδ₃0⟩⟩, hδc0⟩,
      by linarith [hη0]⟩, sq_pos_of_pos (lt_min_iff.mpr ⟨by linarith [hη0], by norm_num⟩)⟩
  have hδq_le₀ : δq ≤ δ₀ :=
    (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _)).trans
      ((min_le_left _ _).trans (min_le_left _ _))
  have hδq_le₁ : δq ≤ δ₁ :=
    (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _)).trans
      ((min_le_left _ _).trans (min_le_right _ _))
  have hδq_le₂ : δq ≤ δ₂ :=
    ((min_le_left _ _).trans (min_le_left _ _)).trans
      ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδq_le₃ : δq ≤ δ₃ :=
    ((min_le_left _ _).trans (min_le_left _ _)).trans
      ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hδq_lec : δq ≤ δc :=
    (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδq_leη : δq ≤ η / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hδq_lesq : δq ≤ (min (η / 8) (1 / 4)) ^ 2 := min_le_right _ _
  have hδq_lt_1 : δq < 1 := by
    have h1 : (min (η / 8) (1 / 4)) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (le_min (by linarith [hη0]) (by norm_num)) (min_le_right _ _) 2
    exact lt_of_le_of_lt (hδq_lesq.trans h1) (by norm_num)
  have hgood : Set.Ioo τ (τ + δq) ∈ nhdsWithin τ (Set.Ioi τ) := by
    rw [← Set.Ioi_inter_Iio]
    exact inter_mem_nhdsWithin _ (Iio_mem_nhds (by linarith [hδq0]))
  refine Filter.mem_of_superset hgood fun t ht => ?_
  have htpos : τ < t := ht.1
  have htp : 0 < t - τ := sub_pos.mpr htpos
  have htδ : t - τ < δq := by linarith [ht.2]
  have htd : dist t τ < δq := by
    rw [Real.dist_eq, abs_of_nonneg (le_of_lt htp)]
    exact htδ
  have hct_im : (c t).im = 0 := hδ₂ (lt_of_lt_of_le htd hδq_le₂)
  have hct_crit : deriv (deBruijnNewmanH t) (c t) = 0 := hδ₁ (lt_of_lt_of_le htd hδq_le₁)
  have hct_height : deBruijnNewmanH t (c t)
      = ∫ s : ℝ in τ..t, ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand s (c s) u :=
    hδ₀ (lt_of_lt_of_le htd hδq_le₀)
  have hcnear : ∀ s : ℝ, dist s τ < δq → dist (c s) x₀ < min (η / 4) (1 / 2) := by
    intro s hs
    have h1 := hδc (lt_of_lt_of_le hs hδq_lec)
    rwa [hc0] at h1
  set Y : ℝ := 2 * Real.sqrt (t - τ) with hYdef
  have hY0 : 0 < Y := by
    rw [hYdef]
    exact mul_pos (by norm_num) (Real.sqrt_pos.mpr htp)
  have hYsq : Y ^ 2 = 4 * (t - τ) := by
    rw [hYdef, mul_pow, Real.sq_sqrt (le_of_lt htp)]
    ring
  have hYlt : Y < min (η / 4) (1 / 2) := by
    have h1 : Real.sqrt (t - τ) < min (η / 8) (1 / 4) := by
      rw [Real.sqrt_lt' (lt_min_iff.mpr ⟨by linarith [hη0], by norm_num⟩)]
      exact lt_of_lt_of_le htδ hδq_lesq
    rw [hYdef]
    have h2 := mul_lt_mul_of_pos_left h1 (by norm_num : (0:ℝ) < 2)
    have h3 : 2 * min (η / 8) (1 / 4) ≤ min (η / 4) (1 / 2) := by
      refine le_min ?_ ?_
      · have h4 := mul_le_mul_of_nonneg_left (min_le_left (η / 8) (1 / 4))
          (by norm_num : (0:ℝ) ≤ 2)
        linarith [h4]
      · have h4 := mul_le_mul_of_nonneg_left (min_le_right (η / 8) (1 / 4))
          (by norm_num : (0:ℝ) ≤ 2)
        linarith [h4]
    exact lt_of_lt_of_le h2 h3
  -- the heat equation, pointwise along the critical curve
  have hheat : ∀ s : ℝ, (∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand s (c s) u)
      = -D2 (s, c s) := by
    intro s
    have h1 := deBruijnNewmanH_heat_equation s (c s)
    have h2 : iteratedDeriv 2 (deBruijnNewmanH s) (c s) = D2 (s, c s) := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rw [h2] at h1
    rw [h1, neg_neg]
  have hccont : ContinuousOn c (Set.uIcc τ t) := by
    rw [Set.uIcc_of_le (le_of_lt htpos)]
    intro s hs
    have hsd : dist s τ < δ₃ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hs.1])]
      have h1 : s - τ ≤ t - τ := by linarith [hs.2]
      have h2 : t - τ < δ₃ := lt_of_lt_of_le htδ hδq_le₃
      linarith [h1, h2]
    exact (hδ₃ hsd).continuousAt.continuousWithinAt
  have hintD2 : IntervalIntegrable (fun s : ℝ => D2 (s, c s)) MeasureTheory.volume τ t :=
    (continuous_deBruijnNewmanH_deriv_two.continuousOn.comp
      (continuousOn_id.prodMk hccont) (Set.mapsTo_univ _ _)).intervalIntegrable
  have hintB : IntervalIntegrable (fun _ : ℝ => B) MeasureTheory.volume τ t :=
    intervalIntegrable_const
  -- Estimate A: `H(t, c(t)) = −B·(t−τ) + o(t−τ)` via the critical height
  have hE0est : ‖deBruijnNewmanH t (c t) + B * ((t - τ : ℝ) : ℂ)‖
      ≤ (|B.re| / 8) * (t - τ) := by
    have h1 : deBruijnNewmanH t (c t) + B * ((t - τ : ℝ) : ℂ)
        = ∫ s : ℝ in τ..t, (B - D2 (s, c s)) := by
      have h2 : (∫ s : ℝ in τ..t,
            ∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand s (c s) u)
          = ∫ s : ℝ in τ..t, -D2 (s, c s) :=
        intervalIntegral.integral_congr fun s _ => hheat s
      have h3 : B * ((t - τ : ℝ) : ℂ) = ∫ s : ℝ in τ..t, B := by
        rw [intervalIntegral.integral_const]
        exact (Complex.real_smul.trans (mul_comm _ _)).symm
      rw [hct_height, h2, h3, intervalIntegral.integral_neg,
        intervalIntegral.integral_sub hintB hintD2, sub_eq_add_neg, add_comm]
    rw [h1]
    calc ‖∫ s : ℝ in τ..t, (B - D2 (s, c s))‖
        ≤ (|B.re| / 8) * |t - τ| :=
          intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => by
            have hsI : s ∈ Set.Ioc τ t := by
              rwa [Set.uIoc_of_le (le_of_lt htpos)] at hs
            have hsd : dist s τ < δq := by
              have h5 : s - τ ≤ t - τ := by linarith [hsI.2]
              rw [Real.dist_eq, abs_of_nonneg (by linarith [hsI.1])]
              linarith [h5, htδ]
            rw [norm_sub_rev]
            apply le_of_lt
            apply hD2B
            · refine Set.mem_prod.mpr ⟨⟨?_, ?_⟩, ?_⟩
              · linarith [hsI.1]
              · have h4 : t - τ < 1 := htδ.trans hδq_lt_1
                linarith [hsI.2, h4]
              · rw [Metric.mem_closedBall]
                exact le_of_lt (lt_of_lt_of_le (hcnear s hsd)
                  ((min_le_right _ _).trans (by norm_num : (1 / 2 : ℝ) ≤ 1)))
            · rw [Prod.dist_eq]
              exact max_lt_iff.mpr
                ⟨(lt_of_lt_of_le hsd hδq_leη).trans (half_lt_self hη0),
                  (hcnear s hsd).trans
                    ((min_le_left _ _).trans_lt (by linarith [hη0]))⟩
        _ = (|B.re| / 8) * (t - τ) := by rw [abs_of_nonneg (le_of_lt htp)]
  -- Taylor-2 at the critical point: the linear term vanishes
  have hT : ∀ y : ℝ, deBruijnNewmanH t (c t + (y : ℂ))
      = deBruijnNewmanH t (c t) + ∫ s : ℝ in (0:ℝ)..1, (∫ r : ℝ in (0:ℝ)..1,
          deriv (deriv (deBruijnNewmanH t)) (c t + ((r * s : ℝ) : ℂ) * (y : ℂ))
            * ((s : ℂ) * (y : ℂ))) * (y : ℂ) := by
    intro y
    have h1 := deBruijnNewmanH_taylor_two_z t (c t) (y : ℂ)
    rw [hct_crit, zero_mul, add_zero] at h1
    exact h1
  -- Estimate B: the remainder is `B·y²/2 + o(y²)`
  have hquad : ∀ y : ℝ, |y| ≤ Y →
      ‖(∫ s : ℝ in (0:ℝ)..1, (∫ r : ℝ in (0:ℝ)..1,
          deriv (deriv (deBruijnNewmanH t)) (c t + ((r * s : ℝ) : ℂ) * (y : ℂ))
            * ((s : ℂ) * (y : ℂ))) * (y : ℂ))
        - B * ((y : ℂ) ^ 2) / 2‖ ≤ (|B.re| / 8) * y ^ 2 := by
    intro y hy
    have hseg : ∀ r s : ℝ, r ∈ Set.Icc (0:ℝ) 1 → s ∈ Set.Icc (0:ℝ) 1 →
        (t, c t + ((r * s : ℝ) : ℂ) * (y : ℂ)) ∈ K
        ∧ dist (t, c t + ((r * s : ℝ) : ℂ) * (y : ℂ)) (τ, x₀) < η := by
      intro r s hr hs
      have hctn : dist (c t) x₀ < min (η / 4) (1 / 2) := hcnear t htd
      have hrs : ‖((r * s : ℝ) : ℂ) * (y : ℂ)‖ ≤ Y := by
        rw [norm_mul, show ‖((r * s : ℝ) : ℂ)‖ = |r * s| from RCLike.norm_ofReal _,
          show ‖(y : ℂ)‖ = |y| from RCLike.norm_ofReal _]
        have h1 : |r * s| ≤ 1 := by
          rw [abs_of_nonneg (mul_nonneg hr.1 hs.1)]
          exact mul_le_one₀ hr.2 hs.1 hs.2
        calc |r * s| * |y| ≤ 1 * Y := mul_le_mul h1 hy (abs_nonneg _) (by norm_num)
          _ = Y := one_mul Y
      have heq : c t + ((r * s : ℝ) : ℂ) * (y : ℂ) - x₀
          = (c t - x₀) + ((r * s : ℝ) : ℂ) * (y : ℂ) := by ring
      have hdist : dist (c t + ((r * s : ℝ) : ℂ) * (y : ℂ)) x₀ < min (η / 2) 1 := by
        have h2 : min (η / 4) (1 / 2) + Y < min (η / 2) 1 := by
          have h3 : min (η / 4) (1 / 2) + Y
              < min (η / 4) (1 / 2) + min (η / 4) (1 / 2) :=
            add_lt_add_of_le_of_lt (le_refl _) hYlt
          have h4 : min (η / 4) (1 / 2) + min (η / 4) (1 / 2) ≤ min (η / 2) 1 := by
            refine le_min ?_ ?_
            · have h5 := min_le_left (η / 4) (1 / 2); linarith [h5]
            · have h5 := min_le_right (η / 4) (1 / 2); linarith [h5]
          exact lt_of_lt_of_le h3 h4
        calc dist (c t + ((r * s : ℝ) : ℂ) * (y : ℂ)) x₀
            = ‖c t + ((r * s : ℝ) : ℂ) * (y : ℂ) - x₀‖ := dist_eq_norm _ _
          _ = ‖(c t - x₀) + ((r * s : ℝ) : ℂ) * (y : ℂ)‖ := by rw [heq]
          _ ≤ ‖c t - x₀‖ + ‖((r * s : ℝ) : ℂ) * (y : ℂ)‖ := norm_add_le _ _
          _ = dist (c t) x₀ + ‖((r * s : ℝ) : ℂ) * (y : ℂ)‖ := by rw [← dist_eq_norm]
          _ < min (η / 4) (1 / 2) + Y := add_lt_add_of_lt_of_le hctn hrs
          _ < min (η / 2) 1 := h2
      refine ⟨Set.mem_prod.mpr ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · linarith [htpos]
      · have h5 : t - τ < 1 := htδ.trans hδq_lt_1
        linarith [h5, htpos]
      · rw [Metric.mem_closedBall]
        exact le_of_lt (lt_of_lt_of_le hdist (min_le_right _ _))
      · rw [Prod.dist_eq]
        exact max_lt_iff.mpr ⟨(lt_of_lt_of_le htd hδq_leη).trans (half_lt_self hη0),
          hdist.trans ((min_le_left _ _).trans_lt (half_lt_self hη0))⟩
    have hinner_eq : ∀ s : ℝ, (∫ r : ℝ in (0:ℝ)..1,
          deriv (deriv (deBruijnNewmanH t)) (c t + ((r * s : ℝ) : ℂ) * (y : ℂ))
            * ((s : ℂ) * (y : ℂ)))
        = deriv (deBruijnNewmanH t) (c t + (s : ℂ) * (y : ℂ))
          - deriv (deBruijnNewmanH t) (c t) := by
      intro s
      have h1 := deBruijnNewmanHzderiv_z_sub_eq_intervalIntegral t (c t)
        ((s : ℂ) * (y : ℂ))
      rw [h1]
      apply intervalIntegral.integral_congr
      intro r _
      have hcast : ((r * s : ℝ) : ℂ) * (y : ℂ) = (r : ℂ) * ((s : ℂ) * (y : ℂ)) := by
        push_cast
        ring
      show deriv (deriv (deBruijnNewmanH t)) (c t + ((r * s : ℝ) : ℂ) * (y : ℂ))
          * ((s : ℂ) * (y : ℂ))
        = deriv (deriv (deBruijnNewmanH t)) (c t + (r : ℂ) * ((s : ℂ) * (y : ℂ)))
          * ((s : ℂ) * (y : ℂ))
      rw [hcast]
    have hR : (∫ s : ℝ in (0:ℝ)..1, (∫ r : ℝ in (0:ℝ)..1,
          deriv (deriv (deBruijnNewmanH t)) (c t + ((r * s : ℝ) : ℂ) * (y : ℂ))
            * ((s : ℂ) * (y : ℂ))) * (y : ℂ))
        = ∫ s : ℝ in (0:ℝ)..1,
          (deriv (deBruijnNewmanH t) (c t + (s : ℂ) * (y : ℂ))
            - deriv (deBruijnNewmanH t) (c t)) * (y : ℂ) := by
      apply intervalIntegral.integral_congr
      intro s _
      show (∫ r : ℝ in (0:ℝ)..1,
          deriv (deriv (deBruijnNewmanH t)) (c t + ((r * s : ℝ) : ℂ) * (y : ℂ))
            * ((s : ℂ) * (y : ℂ))) * (y : ℂ)
        = (deriv (deBruijnNewmanH t) (c t + (s : ℂ) * (y : ℂ))
          - deriv (deBruijnNewmanH t) (c t)) * (y : ℂ)
      rw [hinner_eq s]
    have hBint : ∀ s : ℝ, (∫ r : ℝ in (0:ℝ)..1,
          deriv (deriv (deBruijnNewmanH t)) (c t + ((r * s : ℝ) : ℂ) * (y : ℂ))
            * ((s : ℂ) * (y : ℂ)))
        = (∫ r : ℝ in (0:ℝ)..1,
          (deriv (deriv (deBruijnNewmanH t)) (c t + ((r * s : ℝ) : ℂ) * (y : ℂ)) - B)
            * ((s : ℂ) * (y : ℂ)))
          + B * ((s : ℂ) * (y : ℂ)) := by
      intro s
      have hcr : Continuous fun r : ℝ => c t + ((r * s : ℝ) : ℂ) * (y : ℂ) :=
        continuous_const.add
          ((Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)).mul
            continuous_const)
      have hint1 : IntervalIntegrable (fun r : ℝ =>
          deriv (deriv (deBruijnNewmanH t)) (c t + ((r * s : ℝ) : ℂ) * (y : ℂ))
            * ((s : ℂ) * (y : ℂ))) MeasureTheory.volume 0 1 :=
        ((continuous_deBruijnNewmanH_deriv_two.comp (continuous_const.prodMk hcr)).mul
          continuous_const).intervalIntegrable 0 1
      have hint2 : IntervalIntegrable (fun r : ℝ =>
          (deriv (deriv (deBruijnNewmanH t)) (c t + ((r * s : ℝ) : ℂ) * (y : ℂ)) - B)
            * ((s : ℂ) * (y : ℂ))) MeasureTheory.volume 0 1 :=
        (((continuous_deBruijnNewmanH_deriv_two.comp (continuous_const.prodMk hcr)).sub
          continuous_const).mul continuous_const).intervalIntegrable 0 1
      have e1 : (∫ r : ℝ in (0:ℝ)..1,
            deriv (deriv (deBruijnNewmanH t)) (c t + ((r * s : ℝ) : ℂ) * (y : ℂ))
              * ((s : ℂ) * (y : ℂ)))
          = ∫ r : ℝ in (0:ℝ)..1,
            ((deriv (deriv (deBruijnNewmanH t)) (c t + ((r * s : ℝ) : ℂ) * (y : ℂ)) - B)
              * ((s : ℂ) * (y : ℂ)) + B * ((s : ℂ) * (y : ℂ))) := by
        apply intervalIntegral.integral_congr
        intro r _
        show deriv (deriv (deBruijnNewmanH t)) (c t + ((r * s : ℝ) : ℂ) * (y : ℂ))
            * ((s : ℂ) * (y : ℂ))
          = (deriv (deriv (deBruijnNewmanH t)) (c t + ((r * s : ℝ) : ℂ) * (y : ℂ)) - B)
            * ((s : ℂ) * (y : ℂ)) + B * ((s : ℂ) * (y : ℂ))
        ring
      rw [e1, intervalIntegral.integral_add hint2 intervalIntegrable_const,
        intervalIntegral.integral_const]
      simp
    have hBy : (∫ s : ℝ in (0:ℝ)..1, B * ((s : ℂ) * (y : ℂ)) * (y : ℂ))
        = B * ((y : ℂ) ^ 2) / 2 := by
      have h1 : (∫ s : ℝ in (0:ℝ)..1, (s : ℂ))
          = ((∫ s : ℝ in (0:ℝ)..1, s : ℝ) : ℂ) := intervalIntegral.integral_ofReal
      have hid : (∫ s : ℝ in (0:ℝ)..1, (s : ℂ)) = ((1 / 2 : ℝ) : ℂ) := by
        rw [h1, integral_id]
        norm_num
      have e2a : (∫ s : ℝ in (0:ℝ)..1, B * ((s : ℂ) * (y : ℂ)) * (y : ℂ))
          = ∫ s : ℝ in (0:ℝ)..1, (B * ((y : ℂ) ^ 2)) * (s : ℂ) :=
        intervalIntegral.integral_congr fun s _ => by ring
      have e2b : (∫ s : ℝ in (0:ℝ)..1, (B * ((y : ℂ) ^ 2)) * (s : ℂ))
          = (B * ((y : ℂ) ^ 2)) * ∫ s : ℝ in (0:ℝ)..1, (s : ℂ) :=
        intervalIntegral.integral_const_mul _ _
      rw [e2a, e2b, hid]
      push_cast
      ring
    have hzdcont : Continuous fun s : ℝ =>
        deriv (deBruijnNewmanH t) (c t + (s : ℂ) * (y : ℂ)) :=
      continuous_deBruijnNewmanH_zderiv.comp
        (continuous_const.prodMk
          (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)))
    have hintOuter' : IntervalIntegrable (fun s : ℝ =>
        (deriv (deBruijnNewmanH t) (c t + (s : ℂ) * (y : ℂ))
          - deriv (deBruijnNewmanH t) (c t)) * (y : ℂ)) MeasureTheory.volume 0 1 :=
      ((hzdcont.sub continuous_const).mul continuous_const).intervalIntegrable 0 1
    have hintBy' : IntervalIntegrable (fun s : ℝ => B * ((s : ℂ) * (y : ℂ)) * (y : ℂ))
        MeasureTheory.volume 0 1 :=
      ((continuous_const.mul (Complex.continuous_ofReal.mul continuous_const)).mul
        continuous_const).intervalIntegrable 0 1
    have hfin : (∫ s : ℝ in (0:ℝ)..1, (∫ r : ℝ in (0:ℝ)..1,
          deriv (deriv (deBruijnNewmanH t)) (c t + ((r * s : ℝ) : ℂ) * (y : ℂ))
            * ((s : ℂ) * (y : ℂ))) * (y : ℂ))
        - B * ((y : ℂ) ^ 2) / 2
        = ∫ s : ℝ in (0:ℝ)..1, (∫ r : ℝ in (0:ℝ)..1,
          (deriv (deriv (deBruijnNewmanH t)) (c t + ((r * s : ℝ) : ℂ) * (y : ℂ)) - B)
            * ((s : ℂ) * (y : ℂ))) * (y : ℂ) := by
      rw [hR, ← hBy, ← intervalIntegral.integral_sub hintOuter' hintBy']
      apply intervalIntegral.integral_congr
      intro s _
      show (deriv (deBruijnNewmanH t) (c t + (s : ℂ) * (y : ℂ))
          - deriv (deBruijnNewmanH t) (c t)) * (y : ℂ)
          - B * ((s : ℂ) * (y : ℂ)) * (y : ℂ)
        = (∫ r : ℝ in (0:ℝ)..1,
          (deriv (deriv (deBruijnNewmanH t)) (c t + ((r * s : ℝ) : ℂ) * (y : ℂ)) - B)
            * ((s : ℂ) * (y : ℂ))) * (y : ℂ)
      rw [← hinner_eq s, hBint s]
      ring
    have hC : ∀ s : ℝ, s ∈ Set.uIoc (0:ℝ) 1 →
        ‖(∫ r : ℝ in (0:ℝ)..1,
          (deriv (deriv (deBruijnNewmanH t)) (c t + ((r * s : ℝ) : ℂ) * (y : ℂ)) - B)
            * ((s : ℂ) * (y : ℂ))) * (y : ℂ)‖
        ≤ (|B.re| / 8) * y ^ 2 := by
      intro s hs
      have hs' : s ∈ Set.Ioc (0:ℝ) 1 := by
        rwa [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hs
      have hsI : s ∈ Set.Icc (0:ℝ) 1 := Set.Ioc_subset_Icc_self hs'
      have hs1 : |s| ≤ 1 := by
        rw [abs_of_nonneg (le_of_lt hs'.1)]
        exact hs'.2
      have hpt : ∀ r : ℝ, r ∈ Set.uIoc (0:ℝ) 1 →
          ‖deriv (deriv (deBruijnNewmanH t)) (c t + ((r * s : ℝ) : ℂ) * (y : ℂ)) - B‖
          < |B.re| / 8 := by
        intro r hr
        have hr' : r ∈ Set.Ioc (0:ℝ) 1 := by
          rwa [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hr
        exact hD2B (t, c t + ((r * s : ℝ) : ℂ) * (y : ℂ))
          (hseg r s (Set.Ioc_subset_Icc_self hr') hsI).1
          (hseg r s (Set.Ioc_subset_Icc_self hr') hsI).2
      have hinner : ‖∫ r : ℝ in (0:ℝ)..1,
            (deriv (deriv (deBruijnNewmanH t)) (c t + ((r * s : ℝ) : ℂ) * (y : ℂ)) - B)
              * ((s : ℂ) * (y : ℂ))‖
          ≤ (|B.re| / 8) * (|s| * |y|) := by
        calc ‖∫ r : ℝ in (0:ℝ)..1,
              (deriv (deriv (deBruijnNewmanH t)) (c t + ((r * s : ℝ) : ℂ) * (y : ℂ)) - B)
                * ((s : ℂ) * (y : ℂ))‖
            ≤ ((|B.re| / 8) * (|s| * |y|)) * |1 - 0| :=
              intervalIntegral.norm_integral_le_of_norm_le_const fun r hr => by
                have h2 : ‖((s : ℂ) * (y : ℂ))‖ = |s| * |y| := by
                  rw [norm_mul, show ‖(s : ℂ)‖ = |s| from RCLike.norm_ofReal _,
                    show ‖(y : ℂ)‖ = |y| from RCLike.norm_ofReal _]
                rw [norm_mul, h2]
                exact mul_le_mul_of_nonneg_right (le_of_lt (hpt r hr))
                  (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          _ = (|B.re| / 8) * (|s| * |y|) := by norm_num
      have hyy : |y| * |y| = y ^ 2 := by
        rw [← sq_abs y, pow_two]
      calc ‖(∫ r : ℝ in (0:ℝ)..1,
              (deriv (deriv (deBruijnNewmanH t)) (c t + ((r * s : ℝ) : ℂ) * (y : ℂ)) - B)
                * ((s : ℂ) * (y : ℂ))) * (y : ℂ)‖
          = ‖∫ r : ℝ in (0:ℝ)..1,
              (deriv (deriv (deBruijnNewmanH t)) (c t + ((r * s : ℝ) : ℂ) * (y : ℂ)) - B)
                * ((s : ℂ) * (y : ℂ))‖ * |y| := by
            rw [norm_mul, show ‖(y : ℂ)‖ = |y| from RCLike.norm_ofReal _]
        _ ≤ ((|B.re| / 8) * (|s| * |y|)) * |y| :=
            mul_le_mul_of_nonneg_right hinner (abs_nonneg _)
        _ = ((|B.re| / 8) * |s|) * (|y| * |y|) := by ring
        _ = ((|B.re| / 8) * |s|) * y ^ 2 := by rw [hyy]
        _ ≤ ((|B.re| / 8) * 1) * y ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hs1 (by positivity)) (sq_nonneg y)
        _ = (|B.re| / 8) * y ^ 2 := by ring
    rw [hfin]
    calc ‖∫ s : ℝ in (0:ℝ)..1, (∫ r : ℝ in (0:ℝ)..1,
            (deriv (deriv (deBruijnNewmanH t)) (c t + ((r * s : ℝ) : ℂ) * (y : ℂ)) - B)
              * ((s : ℂ) * (y : ℂ))) * (y : ℂ)‖
        ≤ ((|B.re| / 8) * y ^ 2) * |1 - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hC
      _ = (|B.re| / 8) * y ^ 2 := by norm_num
  -- the three evaluation formulas with small complex errors
  have hE₀ : ∃ E₀ : ℂ, ‖E₀‖ ≤ (|B.re| / 8) * (t - τ)
      ∧ deBruijnNewmanH t (c t) = -B * ((t - τ : ℝ) : ℂ) + E₀ :=
    ⟨deBruijnNewmanH t (c t) + B * ((t - τ : ℝ) : ℂ), hE0est, by ring⟩
  have hE₁ : ∃ E₁ : ℂ, ‖E₁‖ ≤ (|B.re| / 8) * Y ^ 2
      ∧ deBruijnNewmanH t (c t + (Y : ℂ))
        = deBruijnNewmanH t (c t) + B * ((Y : ℂ) ^ 2) / 2 + E₁ := by
    refine ⟨_, hquad Y (abs_of_nonneg (le_of_lt hY0)).le, ?_⟩
    rw [hT Y]
    ring
  have hE₂ : ∃ E₂ : ℂ, ‖E₂‖ ≤ (|B.re| / 8) * Y ^ 2
      ∧ deBruijnNewmanH t (c t + ((-Y : ℝ) : ℂ))
        = deBruijnNewmanH t (c t) + B * (((-Y : ℝ) : ℂ) ^ 2) / 2 + E₂ := by
    have hb : ‖(∫ s : ℝ in (0:ℝ)..1, (∫ r : ℝ in (0:ℝ)..1,
          deriv (deriv (deBruijnNewmanH t)) (c t + ((r * s : ℝ) : ℂ) * ((-Y : ℝ) : ℂ))
            * ((s : ℂ) * ((-Y : ℝ) : ℂ))) * ((-Y : ℝ) : ℂ))
        - B * (((-Y : ℝ) : ℂ) ^ 2) / 2‖ ≤ (|B.re| / 8) * Y ^ 2 := by
      have h := hquad (-Y) ((abs_neg Y).trans (abs_of_nonneg (le_of_lt hY0))).le
      rwa [neg_sq] at h
    refine ⟨_, hb, ?_⟩
    rw [hT (-Y)]
    ring
  obtain ⟨E₀, hE₀n, hE₀eq⟩ := hE₀
  obtain ⟨E₁, hE₁n, hE₁eq⟩ := hE₁
  obtain ⟨E₂, hE₂n, hE₂eq⟩ := hE₂
  have hcastB : B * ((t - τ : ℝ) : ℂ) = ((B.re * (t - τ) : ℝ) : ℂ) := by
    nth_rewrite 1 [hBcr]
    push_cast
    ring
  have hcastBn : -B * ((t - τ : ℝ) : ℂ) = ((-B.re * (t - τ) : ℝ) : ℂ) := by
    nth_rewrite 1 [hBcr]
    push_cast
    ring
  have hevY : deBruijnNewmanH t (c t + (Y : ℂ))
      = B * ((t - τ : ℝ) : ℂ) + (E₀ + E₁) := by
    rw [hE₁eq, hE₀eq]
    have h1 : B * ((Y : ℂ) ^ 2) / 2 = 2 * (B * ((t - τ : ℝ) : ℂ)) := by
      have h2 : (Y : ℂ) ^ 2 = ((4 * (t - τ) : ℝ) : ℂ) := by
        rw [← hYsq]
        push_cast
        ring
      rw [h2]
      push_cast
      ring
    rw [h1]
    ring
  have hevN : deBruijnNewmanH t (c t + ((-Y : ℝ) : ℂ))
      = B * ((t - τ : ℝ) : ℂ) + (E₀ + E₂) := by
    rw [hE₂eq, hE₀eq]
    have h1 : B * (((-Y : ℝ) : ℂ) ^ 2) / 2 = 2 * (B * ((t - τ : ℝ) : ℂ)) := by
      have h2 : ((-Y : ℝ) : ℂ) ^ 2 = ((4 * (t - τ) : ℝ) : ℂ) := by
        have h3 : ((-Y : ℝ) : ℂ) ^ 2 = ((Y ^ 2 : ℝ) : ℂ) := by
          push_cast
          ring
        rw [h3, hYsq]
      rw [h2]
      push_cast
      ring
    rw [h1]
    ring
  have hre0 : (deBruijnNewmanH t (c t)).re = -B.re * (t - τ) + E₀.re := by
    rw [hE₀eq, hcastBn, Complex.add_re, Complex.ofReal_re]
  have hreY : (deBruijnNewmanH t (c t + (Y : ℂ))).re
      = B.re * (t - τ) + (E₀ + E₁).re := by
    rw [hevY, hcastB, Complex.add_re, Complex.ofReal_re]
  have hreN : (deBruijnNewmanH t (c t + ((-Y : ℝ) : ℂ))).re
      = B.re * (t - τ) + (E₀ + E₂).re := by
    rw [hevN, hcastB, Complex.add_re, Complex.ofReal_re]
  have hE₀r : |E₀.re| ≤ (|B.re| / 8) * (t - τ) := (Complex.abs_re_le_norm _).trans hE₀n
  have hE₁r : |(E₀ + E₁).re| ≤ (5 * |B.re| / 8) * (t - τ) := by
    calc |(E₀ + E₁).re| ≤ ‖E₀ + E₁‖ := Complex.abs_re_le_norm _
      _ ≤ ‖E₀‖ + ‖E₁‖ := norm_add_le _ _
      _ ≤ (|B.re| / 8) * (t - τ) + (|B.re| / 8) * Y ^ 2 := add_le_add hE₀n hE₁n
      _ = (5 * |B.re| / 8) * (t - τ) := by rw [hYsq]; ring
  have hE₂r : |(E₀ + E₂).re| ≤ (5 * |B.re| / 8) * (t - τ) := by
    calc |(E₀ + E₂).re| ≤ ‖E₀ + E₂‖ := Complex.abs_re_le_norm _
      _ ≤ ‖E₀‖ + ‖E₂‖ := norm_add_le _ _
      _ ≤ (|B.re| / 8) * (t - τ) + (|B.re| / 8) * Y ^ 2 := add_le_add hE₀n hE₂n
      _ = (5 * |B.re| / 8) * (t - τ) := by rw [hYsq]; ring
  rcases lt_or_gt_of_ne hBre_ne with hBneg | hBpos
  · -- `B.re < 0`: positive at the critical point, negative at `±Y`
    have hBabs : |B.re| = -B.re := abs_of_neg hBneg
    have hg0 : 0 < (deBruijnNewmanH t (c t)).re := by
      rw [hre0]
      have h1 := (abs_le.mp hE₀r).1
      have h2 : |B.re| * (t - τ) = -B.re * (t - τ) := by rw [hBabs]
      have h3 : 0 < |B.re| * (t - τ) := mul_pos hB_abs_pos htp
      linarith
    have hgY : (deBruijnNewmanH t (c t + (Y : ℂ))).re < 0 := by
      rw [hreY]
      have h1 := (abs_le.mp hE₁r).2
      have h2 : |B.re| * (t - τ) = -B.re * (t - τ) := by rw [hBabs]
      have h3 : 0 < |B.re| * (t - τ) := mul_pos hB_abs_pos htp
      linarith
    have hgN : (deBruijnNewmanH t (c t + ((-Y : ℝ) : ℂ))).re < 0 := by
      rw [hreN]
      have h1 := (abs_le.mp hE₂r).2
      have h2 : |B.re| * (t - τ) = -B.re * (t - τ) := by rw [hBabs]
      have h3 : 0 < |B.re| * (t - τ) := mul_pos hB_abs_pos htp
      linarith
    exact ⟨mul_neg_of_pos_of_neg hg0 hgY, mul_neg_of_pos_of_neg hg0 hgN⟩
  · -- `B.re > 0`: mirror image
    have hBabs : |B.re| = B.re := abs_of_pos hBpos
    have hg0 : (deBruijnNewmanH t (c t)).re < 0 := by
      rw [hre0]
      have h1 := (abs_le.mp hE₀r).2
      have h2 : |B.re| * (t - τ) = B.re * (t - τ) := by rw [hBabs]
      have h3 : 0 < |B.re| * (t - τ) := mul_pos hB_abs_pos htp
      linarith
    have hgY : 0 < (deBruijnNewmanH t (c t + (Y : ℂ))).re := by
      rw [hreY]
      have h1 := (abs_le.mp hE₁r).1
      have h2 : |B.re| * (t - τ) = B.re * (t - τ) := by rw [hBabs]
      have h3 : 0 < |B.re| * (t - τ) := mul_pos hB_abs_pos htp
      linarith
    have hgN : 0 < (deBruijnNewmanH t (c t + ((-Y : ℝ) : ℂ))).re := by
      rw [hreN]
      have h1 := (abs_le.mp hE₂r).1
      have h2 : |B.re| * (t - τ) = B.re * (t - τ) := by rw [hBabs]
      have h3 : 0 < |B.re| * (t - τ) := mul_pos hB_abs_pos htp
      linarith
    exact ⟨mul_neg_of_neg_of_pos hg0 hgY, mul_neg_of_neg_of_pos hg0 hgN⟩

/-- **Birth of two real zeros after a double-zero collision**: if `c` is a
real-valued critical curve and the quadratic sign flip of
`deBruijnNewman_double_zero_quadratic_signs` holds on `𝓝[>] τ`, then for `t`
slightly larger than `τ` the function `H_t` has two real zeros straddling the
critical point `c(t)`, each within distance `2√(t−τ)` of it. Proof: apply the
intermediate value theorem to `v ↦ Re(H_t(c(t)+v))` on `[−Y, 0]` and `[0, Y]`
with `Y = 2√(t−τ)`; strictness of the roots follows from the strict sign
flip, and reality of the zeros from Phase 2(34). -/
theorem deBruijnNewman_double_zero_births_real_zeros (τ : ℝ) (c : ℝ → ℂ)
    (hcreal : ∀ᶠ t in nhds τ, (c t).im = 0)
    (hsigns : ∀ᶠ t in nhdsWithin τ (Set.Ioi τ),
      (deBruijnNewmanH t (c t)).re
          * (deBruijnNewmanH t (c t + ((2 * Real.sqrt (t - τ) : ℝ) : ℂ))).re < 0
        ∧ (deBruijnNewmanH t (c t)).re
          * (deBruijnNewmanH t (c t + ((-(2 * Real.sqrt (t - τ)) : ℝ) : ℂ))).re < 0) :
    ∀ᶠ t in nhdsWithin τ (Set.Ioi τ), ∃ z₁ z₂ : ℂ,
      deBruijnNewmanH t z₁ = 0 ∧ deBruijnNewmanH t z₂ = 0
        ∧ z₁.im = 0 ∧ z₂.im = 0 ∧ z₁.re < (c t).re ∧ (c t).re < z₂.re
        ∧ ‖z₁ - c t‖ ≤ 2 * Real.sqrt (t - τ) ∧ ‖z₂ - c t‖ ≤ 2 * Real.sqrt (t - τ) := by
  -- continuity of `v ↦ Re(H_t(c(t)+v))`, for each parameter `t`
  have hgcont : ∀ t : ℝ, Continuous fun v : ℝ =>
      (deBruijnNewmanH t (c t + (v : ℂ))).re :=
    fun t => Complex.continuous_re.comp (contDiff_one_deBruijnNewmanH_prod.continuous.comp
      (continuous_const.prodMk (continuous_const.add Complex.continuous_ofReal)))
  -- IVT root catcher with strict inequalities
  have hroot : ∀ g : ℝ → ℝ, Continuous g → ∀ a b : ℝ, a ≤ b → g a * g b < 0 →
      ∃ y : ℝ, a < y ∧ y < b ∧ g y = 0 := by
    intro g hg a b hab hsign
    have key : ∀ h : ℝ → ℝ, Continuous h → h a < 0 → 0 < h b →
        ∃ y : ℝ, a < y ∧ y < b ∧ h y = 0 := by
      intro h hh ha hb
      have h0 : (0 : ℝ) ∈ Set.Icc (h a) (h b) := ⟨le_of_lt ha, le_of_lt hb⟩
      obtain ⟨y, hyI, hy0⟩ := intermediate_value_Icc hab hh.continuousOn h0
      refine ⟨y, lt_of_le_of_ne hyI.1 ?_, lt_of_le_of_ne' hyI.2 ?_, hy0⟩
      · intro e
        subst e
        rw [hy0] at ha
        exact lt_irrefl _ ha
      · intro e
        subst e
        rw [hy0] at hb
        exact lt_irrefl _ hb
    rcases mul_neg_iff.mp hsign with ⟨hga, hgb⟩ | ⟨hga, hgb⟩
    · obtain ⟨y, h1, h2, h3⟩ := key (fun v => -g v) hg.neg
        (show -g a < 0 from by linarith) (show 0 < -g b from by linarith)
      exact ⟨y, h1, h2, neg_eq_zero.mp h3⟩
    · exact key g hg hga hgb
  filter_upwards [hsigns, hcreal.filter_mono nhdsWithin_le_nhds] with t hsign hct_im
  have hYnn : 0 ≤ 2 * Real.sqrt (t - τ) :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  set Y : ℝ := 2 * Real.sqrt (t - τ) with hYdef
  set g : ℝ → ℝ := fun v => (deBruijnNewmanH t (c t + (v : ℂ))).re with hgdef
  have hg0 : g 0 = (deBruijnNewmanH t (c t)).re := by
    simp only [hgdef, Complex.ofReal_zero, add_zero]
  have hgYv : g Y = (deBruijnNewmanH t (c t + ((2 * Real.sqrt (t - τ) : ℝ) : ℂ))).re := by
    simp only [hgdef, hYdef]
  have hgNv : g (-Y)
      = (deBruijnNewmanH t (c t + ((-(2 * Real.sqrt (t - τ)) : ℝ) : ℂ))).re := by
    simp only [hgdef, hYdef]
  have hgY : g 0 * g Y < 0 := by rw [hg0, hgYv]; exact hsign.1
  have hgN : g (-Y) * g 0 < 0 := by
    rw [hgNv, hg0, mul_comm]
    exact hsign.2
  obtain ⟨y₁, hy₁lo, hy₁hi, hgy₁⟩ := hroot g (hgcont t) (-Y) 0 (neg_nonpos.mpr hYnn) hgN
  obtain ⟨y₂, hy₂lo, hy₂hi, hgy₂⟩ := hroot g (hgcont t) 0 Y hYnn hgY
  -- package each real root as a complex zero of `H_t`
  have hz₁im : (c t + (y₁ : ℂ)).im = 0 := by
    rw [Complex.add_im, Complex.ofReal_im, hct_im, add_zero]
  have hz₂im : (c t + (y₂ : ℂ)).im = 0 := by
    rw [Complex.add_im, Complex.ofReal_im, hct_im, add_zero]
  have hre₁ : (deBruijnNewmanH t (c t + (y₁ : ℂ))).re = 0 := by
    have e : g y₁ = (deBruijnNewmanH t (c t + (y₁ : ℂ))).re := by simp only [hgdef]
    rw [← e, hgy₁]
  have hre₂ : (deBruijnNewmanH t (c t + (y₂ : ℂ))).re = 0 := by
    have e : g y₂ = (deBruijnNewmanH t (c t + (y₂ : ℂ))).re := by simp only [hgdef]
    rw [← e, hgy₂]
  have hHz₁ : deBruijnNewmanH t (c t + (y₁ : ℂ)) = 0 := by
    rw [Complex.ext_iff]
    exact ⟨hre₁, deBruijnNewmanH_im_eq_zero_of_im_eq_zero t hz₁im⟩
  have hHz₂ : deBruijnNewmanH t (c t + (y₂ : ℂ)) = 0 := by
    rw [Complex.ext_iff]
    exact ⟨hre₂, deBruijnNewmanH_im_eq_zero_of_im_eq_zero t hz₂im⟩
  refine ⟨c t + (y₁ : ℂ), c t + (y₂ : ℂ), hHz₁, hHz₂, hz₁im, hz₂im, ?_, ?_, ?_, ?_⟩
  · rw [Complex.add_re, Complex.ofReal_re]
    linarith [hy₁hi]
  · rw [Complex.add_re, Complex.ofReal_re]
    linarith [hy₂lo]
  · rw [show c t + (y₁ : ℂ) - c t = (y₁ : ℂ) from by ring,
      show ‖(y₁ : ℂ)‖ = |y₁| from RCLike.norm_ofReal _, abs_of_neg hy₁hi]
    linarith [hy₁lo]
  · rw [show c t + (y₂ : ℂ) - c t = (y₂ : ℂ) from by ring,
      show ‖(y₂ : ℂ)‖ = |y₂| from RCLike.norm_ofReal _, abs_of_pos hy₂lo]
    linarith [hy₂hi]

/-- **Double-zero collision — full alternative (Phases 2(31)+2(35)+2(36))**: at an
exactly double real zero `x₀` of `H_τ` (i.e. `H_τ(x₀) = 0`, `∂_z H_τ(x₀) = 0`,
`∂²_z H_τ(x₀) ≠ 0`, `x₀ ∈ ℝ`), the zero does not disappear after the collision:
for every `t > τ` sufficiently close to `τ`, `H_t` has two distinct real zeros
`z₁.re < z₂.re` near `x₀` (born from the critical curve `c(t)` by the quadratic
sign flip). This is the collision case of the de Bruijn monotonicity
globalization: simple zeros persist by the implicit function trajectory
(`deBruijnNewman_simple_zero_trajectory`), and exactly-double zeros instantly
re-emerge as two real zeros, so real zeros are never lost in either case. -/
theorem deBruijnNewman_double_zero_full (τ : ℝ) (x₀ : ℂ)
    (hz0 : deBruijnNewmanH τ x₀ = 0)
    (hzder : deriv (deBruijnNewmanH τ) x₀ = 0)
    (hB : deriv (deriv (deBruijnNewmanH τ)) x₀ ≠ 0)
    (hx : x₀.im = 0) :
    ∀ᶠ t in nhdsWithin τ (Set.Ioi τ), ∃ z₁ z₂ : ℂ,
      deBruijnNewmanH t z₁ = 0 ∧ deBruijnNewmanH t z₂ = 0
        ∧ z₁.im = 0 ∧ z₂.im = 0 ∧ z₁.re < z₂.re := by
  obtain ⟨c, hcdiff, hc0, hcrit, hcreal, -⟩ :=
    deBruijnNewman_critical_curve τ x₀ hzder hB hx
  have hcont : ContinuousAt c τ := (hcdiff.self_of_nhds).continuousAt
  have hsigns := deBruijnNewman_double_zero_quadratic_signs τ x₀ c hcont hcdiff hcrit
    hcreal hc0 hz0 hB hx
  have hbirth := deBruijnNewman_double_zero_births_real_zeros τ c hcreal hsigns
  filter_upwards [hbirth] with t ht
  obtain ⟨z₁, z₂, h1, h2, h3, h4, h5, h6, -, -⟩ := ht
  exact ⟨z₁, z₂, h1, h2, h3, h4, h5.trans h6⟩

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

/-! ## Phase 3：远场纲领（far-field program）—— `hnoesc` 的重述与新目标

**Why the old `hnoesc` is the wrong statement**（记录在案，替代
`de_bruijn_monotone_of_simple_and_no_escape` 的远场假设）: that hypothesis
asks for a *single* compact set `K` containing **all** zeros of `H_t` on a right
interval. This is false as stated: every `H_t` is a nontrivial entire function
bounded on the real axis (`|H_t(x)| ≤ ∫₀^∞ e^{tu²}Φ(u)du < ∞` for real `x`),
hence has infinitely many zeros (an entire function with finitely many zeros is
`e^g·P` with `g` a polynomial, and `|e^g|` bounded on `ℝ` forces `g` constant —
contradiction), and its zeros are unbounded in modulus. No single compact set
can contain them.

**The correct replacement splits non-escape into two independent pieces**:
1. **Confinement on compacts（紧区域禁闭）**: on each compact time interval and
   each compact `K ⊆ ℂ`, zeros of `H_t` inside `K` move continuously in `t`
   (compactness + joint continuity: if `tₙ → t₀`, `zₙ ∈ K`, `H_{tₙ}(zₙ) = 0`,
   then a subsequence converges to a zero of `H_{t₀}`). Real-ness inside `K`
   then follows from the local analysis: simple zeros by the IFT trajectory
   (`deBruijnNewman_simple_zero_trajectory` /
   `deBruijnNewman_zeros_stay_real_on_compact`), exactly-double zeros by the
   collision alternative (`deBruijnNewman_double_zero_full`) plus the local
   exclusion theorem (in progress: injectivity on small disks around
   `c(t) ± √q` + conjugation, built on Phases 2(37)–2(41)).
2. **Far-field reality（远场零点实性）**: zeros of large modulus are real,
   uniformly on a right interval — de Bruijn's tail analysis (large zeros are
   asymptotically real with spacing `∼ π/log T`). This is genuinely missing
   analytic input: it needs Jensen/argument-principle zero counting, which
   Mathlib does not have (no Rouché, no argument principle as of this
   toolchain); building it is a separate infrastructure project.

The induction then runs as: `AllZerosReal t₀` ⇒ for `t ∈ [t₀, t₀ + δ)`, any
zero `z` of `H_t` either lies in the confining ball (real by piece 1) or
outside it (real by piece 2). -/

/-- **Restated far-field reality (explicit new target, replacing `hnoesc`)**:
for every time `t₀` there exist a right interval `[t₀, t₀ + δ)` and a radius
`R` such that every zero of `H_t` with `‖z‖ ≥ R` is real, for all `t` in the
interval. Together with confinement on compacts (piece 1 above) this is
exactly the non-escape input of de Bruijn monotonicity. Stated as a `def`
(a hypothesis shape), not assumed: proving it is the far-field project and
requires Jensen-type zero-counting infrastructure that does not yet exist in
this Mathlib. -/
def deBruijnNewmanFarFieldReal (t₀ : ℝ) : Prop :=
  ∃ δ > 0, ∃ R : ℝ, 0 < R ∧
    ∀ t ∈ Set.Ico t₀ (t₀ + δ), ∀ z : ℂ, R ≤ ‖z‖ →
      deBruijnNewmanH t z = 0 → z.im = 0

/-- **Restated compact-confinement property (explicit new target, piece 1)**:
on every compact time interval and every compact `K`, zeros of `H_t` in `K`
stay near zeros of the limit function — the sequential-continuity form of
Hurwitz confinement that, unlike `hnoesc`, is both true and provable from
joint continuity of `H` alone. -/
def deBruijnNewmanCompactConfinement : Prop :=
  ∀ K : Set ℂ, IsCompact K → ∀ t₀ : ℝ, ∀ ts : ℕ → ℝ,
    Filter.Tendsto ts Filter.atTop (nhds t₀) → ∀ zs : ℕ → ℂ,
      (∀ n, zs n ∈ K) → (∀ n, deBruijnNewmanH (ts n) (zs n) = 0) →
      ∃ z₀ : ℂ, z₀ ∈ K ∧ deBruijnNewmanH t₀ z₀ = 0

/-! ## Phase 2(ix)：de Bruijn 单调性的条件化骨架（连续归纳） -/

/-- **Continuous-induction skeleton of de Bruijn monotonicity**: if the
real-zero property is "right-open" at every time where it holds — i.e. it
persists on some right interval `[t₀, t₀ + δ)` — then it is monotone in time.
The zero-reality set is closed (`isClosed_allZerosReal`), so the continuous
induction principle `IsClosed.Icc_subset_of_forall_exists_gt` propagates the
property across any closed interval. The remaining analytic content of de
Bruijn's monotonicity theorem is exactly this right-openness: persistence
through double-zero collisions and exclusion of zeros escaping to infinity. -/
theorem de_bruijn_monotone_of_right_open
    (hopen : ∀ t₀ : ℝ, AllZerosReal t₀ → ∃ δ > 0,
      ∀ t ∈ Set.Ico t₀ (t₀ + δ), AllZerosReal t) :
    de_bruijn_monotone_target := by
  intro t₀ t' ht₀ htt'
  have hsub : Set.Icc t₀ t' ⊆ {t : ℝ | AllZerosReal t} := by
    refine IsClosed.Icc_subset_of_forall_exists_gt
      (isClosed_allZerosReal.inter isClosed_Icc) ht₀ fun x hx y hy => ?_
    obtain ⟨δ, hδ, hδt⟩ := hopen x hx.1
    have hxy : x < y := hy
    exact ⟨min (x + δ / 2) ((x + y) / 2),
      hδt _ ⟨le_of_lt (lt_min_iff.mpr ⟨by linarith, by linarith⟩),
        lt_of_le_of_lt (min_le_left _ _) (by linarith)⟩,
      lt_min_iff.mpr ⟨by linarith, by linarith⟩,
      le_trans (min_le_right _ _) (by linarith)⟩
  exact hsub ⟨htt', le_refl t'⟩

/-- **Reduction of de Bruijn monotonicity to simplicity and non-escape**: if at
every time `t₀` with only real zeros (i) every zero of `H_{t₀}` is simple, and
(ii) no zeros enter from infinity on a right interval — some compact set `K`
contains every zero of `H_t` for `t ∈ [t₀, t₀ + δ)` — then de Bruijn
monotonicity holds. Zeros of `H_t` inside `K` stay real by
`deBruijnNewman_zeros_stay_real_on_compact` (the IFT trajectory theorem, which
needs no zero-counting), and outside `K` there are none, so the property is
right-open and `de_bruijn_monotone_of_right_open` closes the induction. The
two hypotheses are exactly the two remaining analytic gaps: persistence of
simplicity through collisions, and confinement of zeros. -/
theorem de_bruijn_monotone_of_simple_and_no_escape
    (hsimple : ∀ t₀ : ℝ, AllZerosReal t₀ → ∀ z : ℂ, deBruijnNewmanH t₀ z = 0 →
      deriv (deBruijnNewmanH t₀) z ≠ 0)
    (hnoesc : ∀ t₀ : ℝ, AllZerosReal t₀ → ∃ δ > 0, ∃ K : Set ℂ, IsCompact K ∧
      ∀ t ∈ Set.Ico t₀ (t₀ + δ), ∀ z ∉ K, deBruijnNewmanH t z ≠ 0) :
    de_bruijn_monotone_target := by
  apply de_bruijn_monotone_of_right_open
  intro t₀ ht₀
  obtain ⟨δ, hδ, K, hK, hout⟩ := hnoesc t₀ ht₀
  have hreal : ∀ z ∈ K, deBruijnNewmanH t₀ z = 0 → z.im = 0 :=
    fun z _ hz => ht₀ z hz
  have hstay := deBruijnNewman_zeros_stay_real_on_compact t₀ K hK hreal
    (fun z _ hz => hsimple t₀ ht₀ z hz)
  rw [Metric.eventually_nhds_iff] at hstay
  obtain ⟨ε, hε, hεP⟩ := hstay
  refine ⟨min δ (ε / 2), lt_min_iff.mpr ⟨hδ, by linarith⟩, fun t ht z hz => ?_⟩
  have htδ : t < t₀ + δ := lt_of_lt_of_le ht.2 (add_le_add (le_refl t₀) (min_le_left _ _))
  have hdist : dist t t₀ < ε := by
    have ht2 : t < t₀ + min δ (ε / 2) := ht.2
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
    have hmin : min δ (ε / 2) ≤ ε / 2 := min_le_right _ _
    linarith
  by_cases hzK : z ∈ K
  · exact hεP hdist z hzK hz
  · exact absurd hz (hout t ⟨ht.1, htδ⟩ z hzK)

/-! ## Phase 2(x)：零点速度（Rodgers–Tao 向量场雏形） -/

/-- **Zero-trajectory velocity, integral form (first Rodgers–Tao block)**: near a
simple real zero `x₀` of `H_{t₀}`, the implicit-function zero trajectory `ψ`
moves with complex velocity
`ψ'(t₀) = −(∂_t H_{t₀}(x₀)) / (∂_z H_{t₀}(x₀))`,
where `∂_t H` is the `u²`-weighted heat integral. Proof: the identity
`H_t(ψ t) = 0` holds on a neighborhood, so the composite has derivative `0`
at `t₀`; the chain rule through the joint derivative `jointFDerivCLM` gives
`(∂_t H) + (∂_z H) · ψ'(t₀) = 0`, and simplicity lets one divide. -/
theorem deBruijnNewman_simple_zero_velocity (t₀ : ℝ) (x₀ : ℂ)
    (hz : deBruijnNewmanH t₀ x₀ = 0) (hD : deriv (deBruijnNewmanH t₀) x₀ ≠ 0)
    (hx : x₀.im = 0) :
    ∃ ψ : ℝ → ℂ, DifferentiableAt ℝ ψ t₀ ∧ ψ t₀ = x₀
      ∧ (∀ᶠ t in nhds t₀, deBruijnNewmanH t (ψ t) = 0)
      ∧ (∀ᶠ t in nhds t₀, (ψ t).im = 0)
      ∧ deriv ψ t₀
        = -(∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand t₀ x₀ u)
          / deriv (deBruijnNewmanH t₀) x₀ := by
  obtain ⟨ψ, hψdiff, hψ0, hzero, hreal, -⟩ :=
    deBruijnNewman_simple_zero_trajectory t₀ x₀ hz hD hx
  refine ⟨ψ, hψdiff, hψ0, hzero, hreal, ?_⟩
  have hg0 : HasDerivAt ((fun q : ℝ × ℂ => deBruijnNewmanH q.1 q.2)
      ∘ fun t : ℝ => (t, ψ t)) 0 t₀ :=
    (hasDerivAt_const (c := (0 : ℂ)) (x := t₀)).congr_of_eventuallyEq
      (hzero.mono fun t h => h)
  have hprod : HasFDerivAt (fun t : ℝ => (t, ψ t))
      ((ContinuousLinearMap.id ℝ ℝ).prod (fderiv ℝ ψ t₀)) t₀ :=
    (hasFDerivAt_id t₀).prodMk hψdiff.hasFDerivAt
  have hcomp := (hasFDerivAt_deBruijnNewmanH_prod (t₀, ψ t₀)).comp
    (f := fun t : ℝ => (t, ψ t)) (x := t₀) hprod
  have hval : ((jointFDerivCLM (t₀, ψ t₀).1 (t₀, ψ t₀).2).comp
      ((ContinuousLinearMap.id ℝ ℝ).prod (fderiv ℝ ψ t₀))) 1
      = (∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand t₀ (ψ t₀) u)
        + deriv (deBruijnNewmanH t₀) (ψ t₀) * deriv ψ t₀ := by
    have hf1 : fderiv ℝ ψ t₀ 1 = deriv ψ t₀ := by
      have h := hψdiff.hasFDerivAt.unique (hasDerivAt_iff_hasFDerivAt.mp hψdiff.hasDerivAt)
      rw [h]
      simp
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      jointFDerivCLM_apply, hf1]
  have key : (∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand t₀ (ψ t₀) u)
      + deriv (deBruijnNewmanH t₀) (ψ t₀) * deriv ψ t₀ = 0 := by
    have hu := hg0.unique hcomp.hasDerivAt
    rw [hval] at hu
    exact hu.symm
  rw [hψ0] at key
  have h1 : deriv (deBruijnNewmanH t₀) x₀ * deriv ψ t₀
      = -(∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2) * heatIntegrand t₀ x₀ u) := by
    rw [add_comm] at key
    exact eq_neg_of_add_eq_zero_left key
  rw [eq_comm, div_eq_iff hD, mul_comm]
  exact h1.symm

/-- **Zero-trajectory velocity, heat-equation form**: at a simple real zero,
`ψ'(t₀) = (∂²_z H_{t₀}(x₀)) / (∂_z H_{t₀}(x₀))`.
This is the Rodgers–Tao velocity field `ż = H_zz / H_z` at a single zero
(before the Hadamard expansion `H_z/H = Σ 1/(· − zⱼ)` turns it into
`2 Σ_{j ≠ k} 1/(z_k − z_j)`): the minus sign of the backward heat equation
`∂²_z H = −∂_t H` cancels the implicit-function minus sign. -/
theorem deBruijnNewman_simple_zero_velocity_heat (t₀ : ℝ) (x₀ : ℂ)
    (hz : deBruijnNewmanH t₀ x₀ = 0) (hD : deriv (deBruijnNewmanH t₀) x₀ ≠ 0)
    (hx : x₀.im = 0) :
    ∃ ψ : ℝ → ℂ, DifferentiableAt ℝ ψ t₀ ∧ ψ t₀ = x₀
      ∧ (∀ᶠ t in nhds t₀, deBruijnNewmanH t (ψ t) = 0)
      ∧ (∀ᶠ t in nhds t₀, (ψ t).im = 0)
      ∧ deriv ψ t₀
        = iteratedDeriv 2 (deBruijnNewmanH t₀) x₀ / deriv (deBruijnNewmanH t₀) x₀ := by
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := deBruijnNewman_simple_zero_velocity t₀ x₀ hz hD hx
  exact ⟨ψ, h1, h2, h3, h4, by rw [h5, deBruijnNewmanH_heat_equation]⟩

end DeBruijnNewman
end RiemannExplorer
