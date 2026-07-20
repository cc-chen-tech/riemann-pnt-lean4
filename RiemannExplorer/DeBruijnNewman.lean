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

/-- Auxiliary cosine growth bound: `‖cos w‖ ≤ exp |Im w|` for `w : ℂ`.
Proved from `Complex.cos_eq` and `cosh y + |sinh y| = exp |y|`. -/
theorem norm_cos_le_exp_abs_im (w : ℂ) :
    ‖Complex.cos w‖ ≤ Real.exp |w.im| := by
  have hcs : Real.cosh w.im + |Real.sinh w.im| = Real.exp |w.im| := by
    rw [Real.cosh_eq, Real.sinh_eq]
    rcases le_total 0 w.im with hy | hy
    · have h1 : Real.exp (-w.im) ≤ Real.exp w.im := Real.exp_le_exp.mpr (by linarith)
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (Real.exp w.im - Real.exp (-w.im)) / 2),
        abs_of_nonneg hy]
      linarith
    · have h1 : Real.exp w.im ≤ Real.exp (-w.im) := Real.exp_le_exp.mpr (by linarith)
      rw [abs_of_nonpos (by linarith : (Real.exp w.im - Real.exp (-w.im)) / 2 ≤ 0),
        abs_of_nonpos hy]
      linarith
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

/-- Growth control for the oscillatory factor of the `H_t` integrand:
`‖cos (z · u)‖ ≤ exp |Im z · u|` for real `u`. -/
theorem norm_cos_mul_ofReal_le_exp (z : ℂ) (u : ℝ) :
    ‖Complex.cos (z * (u : ℂ))‖ ≤ Real.exp |z.im * u| := by
  have him : (z * (u : ℂ)).im = z.im * u := by simp [Complex.mul_im]
  rw [← him]
  exact norm_cos_le_exp_abs_im _

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

/-! ## Prop 目标（晋升纪律见 `docs/implementation-standards.md`） -/

/-- **适定性目标**（Phase 1a）：对每个 `t : ℝ`、`z : ℂ`，被积函数
`e^{t u²} Φ(u) cos(z u)` 在 `(0, ∞)` 上可积。证明路线见调研笔记：
`|Φ(u)| ≤ K (2π² e^{9u} + 3π e^{5u}) e^{−π e^{4u}}`（`u ≥ 0`）配合
`norm_cos_mul_ofReal_le_exp` 与 `exp` 支配。 -/
def heat_integrand_integrable_target : Prop :=
  ∀ t : ℝ, ∀ z : ℂ,
    MeasureTheory.IntegrableOn (heatIntegrand t z) (Set.Ioi 0) MeasureTheory.volume

/-- **Φ 偶性目标**（Phase 1c）：`Φ(−u) = Φ(u)`。
经 Poisson 求和等价于 ζ 的函数方程（Riemann）；Mathlib 侧锚点为
`Mathlib/NumberTheory/ModularForms/JacobiTheta`。 -/
def phi_even_target : Prop :=
  ∀ u : ℝ, phi (-u) = phi u

/-- **H_t 正则性目标**（Phase 1b）：每个 `H_t` 是偶的整函数。 -/
def h_even_entire_target : Prop :=
  ∀ t : ℝ, Differentiable ℂ (deBruijnNewmanH t) ∧
    ∀ z : ℂ, deBruijnNewmanH t (-z) = deBruijnNewmanH t z

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

end DeBruijnNewman
end RiemannExplorer
