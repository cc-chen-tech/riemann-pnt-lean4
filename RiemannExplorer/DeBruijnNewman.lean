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

end DeBruijnNewman
end RiemannExplorer
