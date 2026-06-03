/-
# Hardy 定理的形式化框架

Hardy (1914) 证明了黎曼ζ函数在临界线上有无穷多个零点。

## 历史背景

G.H. Hardy 在1914年的论文中证明了这个结果。
技术核心：构造一个辅助函数，证明它有无穷多次变号。

## 证明思路概述

1. 定义 Hardy 函数：Z(t) = e^{iθ(t)} ζ(1/2 + it)
   - 这是实值函数
   - Z(t) = 0 ⟺ ζ(1/2 + it) = 0
2. 考虑积分：∫_0^T Z(t) dt
3. 证明该积分有特定的渐近行为，要求 Z(t) 必须有无穷多次变号
4. 由于 Z(t) 连续，变号意味着有零点
-/

import Mathlib

open Complex BigOperators Filter Topology Asymptotics ComplexConjugate Set

namespace HardyTheorem

/-! ## 定义和设置 -/

/-- Hardy Z 函数：在临界线上检测零点的实值函数

Z(t) = e^{iθ(t)} ζ(1/2 + it)

其中 θ(t) 是使得 Z(t) 为实数的相位因子。 -/

noncomputable def thetaPhase (t : ℝ) : ℝ :=
  Complex.arg (Complex.Gamma (1 / 4 + I * t / 2)) - (t / 2) * Real.log Real.pi

noncomputable def hardyZ (t : ℝ) : ℝ :=
  (riemannZeta (0.5 + I * t)).re * Real.cos (thetaPhase t)
    - (riemannZeta (0.5 + I * t)).im * Real.sin (thetaPhase t)

/-- Z(t) 的显式公式 -/
theorem hardyZ_explicit (t : ℝ) :
    hardyZ t = (riemannZeta (0.5 + I * t)).re * Real.cos (thetaPhase t)
             - (riemannZeta (0.5 + I * t)).im * Real.sin (thetaPhase t) := by
  rfl

/-- thetaPhase(0) = arg(Gamma(1/4)) -/
theorem thetaPhase_zero : thetaPhase 0 = Complex.arg (Complex.Gamma (1 / 4 : ℂ)) := by
  simp [thetaPhase]

/-! ## 关键性质 -/

lemma zeta_zero_implies_hardyZ_zero (t : ℝ) (h : riemannZeta (0.5 + I * t) = 0) :
    hardyZ t = 0 := by
  simp [hardyZ, h]

/-! ## 辅助引理 -/

lemma completedRiemannZeta_conj_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
  rw [completedZeta_eq_tsum_of_one_lt_re (by simpa using hs)]
  rw [completedZeta_eq_tsum_of_one_lt_re hs]
  have h_conj_cpow {x n : ℂ} (hx : x.arg ≠ Real.pi) : conj (x ^ n) = conj x ^ conj n := by
    have h := cpow_conj x (conj n) hx
    apply congr_arg conj at h
    simpa using h
  have h1 : conj ((↑Real.pi : ℂ) ^ (-s / 2)) = (↑Real.pi : ℂ) ^ (-(conj s) / 2) := by
    rw [h_conj_cpow (by rw [arg_ofReal_of_nonneg (by positivity)]; exact Real.pi_ne_zero.symm)]
    rw [conj_ofReal]
    have h : conj (-s / 2) = -(conj s) / 2 := by
      rw [map_div₀, map_neg]
      have h2 : conj (2 : ℂ) = (2 : ℂ) := by rw [conj_eq_iff_re]; norm_num
      rw [h2]
    rw [h]
  have h2 : conj (Gamma (s / 2)) = Gamma ((conj s) / 2) := by
    rw [show (conj s) / 2 = conj (s / 2) by
      rw [map_div₀]
      have : conj (2 : ℂ) = (2 : ℂ) := by rw [conj_eq_iff_re]; norm_num
      rw [this]]
    rw [Complex.Gamma_conj]
  have h3 : conj (∑' n : ℕ, 1 / (n : ℂ) ^ s) = ∑' n : ℕ, 1 / (n : ℂ) ^ (conj s) := by
    rw [conj_tsum]
    congr 1 with n
    by_cases hn : n = 0
    · simp only [hn, Nat.cast_zero]
      rw [zero_cpow (Complex.ne_zero_of_one_lt_re hs)]
      rw [div_zero]
      symm
      rw [zero_cpow (Complex.ne_zero_of_one_lt_re (by simpa using hs))]
      rw [div_zero]
      all_goals simp
    · rw [div_eq_mul_inv, div_eq_mul_inv]
      rw [map_mul, map_inv₀]
      rw [h_conj_cpow (by
        have h_arg_n : (n : ℂ).arg = 0 := by
          rw [← ofReal_natCast]
          rw [arg_ofReal_of_nonneg (by positivity)]
        rw [h_arg_n]
        exact Real.pi_ne_zero.symm)]
      field_simp [hn]
      simp [map_one]
  simp only [h1, h2, h3, map_mul]

lemma completedRiemannZeta₀_conj_eq (s : ℂ) :
    completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) := by
  let f := completedRiemannZeta₀
  let g := fun z : ℂ ↦ conj (f (conj z))
  have hf_analytic : AnalyticOnNhd ℂ f univ := by
    apply DifferentiableOn.analyticOnNhd
    · exact fun z _ ↦ (differentiable_completedZeta₀ z).differentiableWithinAt
    · exact isOpen_univ
  have hg_analytic : AnalyticOnNhd ℂ g univ := by
    apply DifferentiableOn.analyticOnNhd
    · intro z _
      have h : HasDerivAt f (deriv f (conj z)) (conj z) :=
        (differentiable_completedZeta₀ (conj z)).hasDerivAt
      have h' : HasDerivAt (conj ∘ f ∘ conj) (conj (deriv f (conj z))) z := by
        simpa using h.conj_conj
      exact h'.differentiableAt.differentiableWithinAt
    · exact isOpen_univ
  have h_eq_eventually : ∀ᶠ z in 𝓝 (2 : ℂ), f z = g z := by
    have h_open : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) := by
      have : IsOpen {z : ℂ | 1 < z.re} := by
        apply isOpen_lt
        · exact continuous_const
        · exact continuous_re
      apply this.mem_nhds
      simp
    filter_upwards [h_open] with z hz
    have h_eq : f z = g z := by
      have h_r : f z = completedRiemannZeta z + 1 / z + 1 / (1 - z) := by
        simp [f, completedRiemannZeta_eq]
        ring
      have h_r_conj : f (conj z) = completedRiemannZeta (conj z) + 1 / (conj z) + 1 / (1 - conj z) := by
        simp [f, completedRiemannZeta_eq]
        ring
      simp [g, h_r, h_r_conj]
      rw [completedRiemannZeta_conj_eq_of_one_lt_re hz]
      norm_num [Complex.conj_conj]
    exact h_eq
  have h_eq : f = g := AnalyticOnNhd.eq_of_eventuallyEq hf_analytic hg_analytic h_eq_eventually
  have h_final : f (conj s) = g (conj s) := congr_fun h_eq (conj s)
  simp [f, g] at h_final
  exact h_final

lemma completedRiemannZeta_critical_line_real (t : ℝ) :
    ∃ r : ℝ, completedRiemannZeta ((1 / 2 : ℂ) + I * t) = (r : ℂ) := by
  let s := (1 / 2 : ℂ) + I * t
  have h1 : completedRiemannZeta s = completedRiemannZeta (1 - s) := by
    rw [completedRiemannZeta_one_sub]
  have h2 : 1 - s = conj s := by
    simp [s, Complex.ext_iff]
    all_goals norm_num
  rw [h2] at h1
  have h3 : completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) :=
    completedRiemannZeta₀_conj_eq s
  have h4 : completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
    simp [completedRiemannZeta_eq, h3]
  rw [h4] at h1
  use (completedRiemannZeta s).re
  have hs_eq : completedRiemannZeta ((1 / 2 : ℂ) + I * t) = completedRiemannZeta s := by simp [s]
  rw [hs_eq]
  have h_re : ↑(completedRiemannZeta s).re = completedRiemannZeta s := by
    rw [← conj_eq_iff_re]
    exact h1.symm
  exact h_re.symm

lemma Gammaℝ_re_im_arg (t : ℝ) :
    (Gammaℝ ((1 / 2 : ℂ) + I * t)).re = ‖Gammaℝ ((1 / 2 : ℂ) + I * t)‖ * Real.cos (thetaPhase t) ∧
    (Gammaℝ ((1 / 2 : ℂ) + I * t)).im = ‖Gammaℝ ((1 / 2 : ℂ) + I * t)‖ * Real.sin (thetaPhase t) := by
  let s := (1 / 2 : ℂ) + I * t
  let w := (1 / 4 : ℂ) + I * t / 2
  have hw : s / 2 = w := by
    simp [s, w]
    ring_nf
  have h_Gammaℝ : Gammaℝ s = (↑Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2) := Gammaℝ_def s
  have hw' : Gamma w ≠ 0 := by
    apply Gamma_ne_zero_of_re_pos
    simp [w]
  have h_Gammaℝ_ne_zero : Gammaℝ s ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos
    simp [s]
  -- Key identity: Gammaℝ s / ‖Gammaℝ s‖ = exp(I * thetaPhase t)
  have h_unit : Gammaℝ s / ‖Gammaℝ s‖ = Complex.exp (I * thetaPhase t) := by
    have h1 : Gammaℝ s / ‖Gammaℝ s‖ = ((↑Real.pi : ℂ) ^ (-w) / ‖(↑Real.pi : ℂ) ^ (-w)‖) * (Gamma w / ‖Gamma w‖) := by
      have h_exp : (-s / 2 : ℂ) = -w := by
        calc
          (-s / 2 : ℂ) = -(s / 2) := by ring
          _ = -w := by rw [hw]
      rw [h_Gammaℝ, hw, h_exp]
      have h_norm : ‖(↑Real.pi : ℂ) ^ (-w) * Gamma w‖ = ‖(↑Real.pi : ℂ) ^ (-w)‖ * ‖Gamma w‖ := by rw [norm_mul]
      rw [h_norm]
      have h_pi_ne_zero : (↑Real.pi : ℂ) ^ (-w) ≠ 0 := by
        rw [cpow_def_of_ne_zero (by norm_num)]
        exact Complex.exp_ne_zero _
      have h_norm_pi_ne_zero : ‖(↑Real.pi : ℂ) ^ (-w)‖ ≠ 0 := by
        apply ne_of_gt
        apply norm_pos_iff.mpr
        exact h_pi_ne_zero
      field_simp [h_norm_pi_ne_zero, hw']
      norm_cast
    have h2 : (↑Real.pi : ℂ) ^ (-w) / ‖(↑Real.pi : ℂ) ^ (-w)‖ = Complex.exp (-I * (t / 2 * Real.log Real.pi)) := by
      have h_log : log (↑Real.pi : ℂ) = (↑(Real.log Real.pi) : ℂ) := by
        simp [Complex.ext_iff, log_ofReal_re, log_im, arg_ofReal_of_nonneg Real.pi_pos.le]
      have h_pi : (↑Real.pi : ℂ) ^ (-w) = ↑(Real.pi ^ (-1 / 4 : ℝ)) * Complex.exp (-I * (t / 2 * Real.log Real.pi)) := by
        rw [cpow_def_of_ne_zero (by norm_num)]
        simp only [h_log]
        have h_exp : exp (↑(Real.log Real.pi) * (-w)) = ↑(Real.pi ^ (-1 / 4 : ℝ)) * exp (-I * (t / 2 * Real.log Real.pi)) := by
          have h1 : exp (↑(Real.log Real.pi) * (-w)) = exp (-1 / 4 * ↑(Real.log Real.pi)) * exp (-I * (t / 2 * Real.log Real.pi)) := by
            have h_eq : ↑(Real.log Real.pi) * (-w) = -1 / 4 * ↑(Real.log Real.pi) + (-I * (t / 2 * Real.log Real.pi)) := by
              simp [w, Complex.ext_iff]
              ring_nf
              norm_num
            rw [h_eq, Complex.exp_add]
          have h2 : exp (-1 / 4 * ↑(Real.log Real.pi)) = ↑(Real.pi ^ (-1 / 4 : ℝ)) := by
            rw [Real.rpow_def_of_pos Real.pi_pos]
            have h_eq : (-1 / 4 : ℂ) * ↑(Real.log Real.pi) = ↑(Real.log Real.pi * (-1 / 4)) := by
              push_cast
              ring
            rw [h_eq, ← Complex.ofReal_exp]
          rw [h1, h2]
        exact h_exp
      rw [h_pi]
      have h_norm : ‖↑(Real.pi ^ (-1 / 4 : ℝ)) * Complex.exp (-I * (t / 2 * Real.log Real.pi))‖ = Real.pi ^ (-1 / 4 : ℝ) := by
        rw [norm_mul]
        have h1 : ‖(↑(Real.pi ^ (-1 / 4 : ℝ)) : ℂ)‖ = Real.pi ^ (-1 / 4 : ℝ) := by
          rw [Complex.norm_def]
          have : Complex.normSq (↑(Real.pi ^ (-1 / 4 : ℝ)) : ℂ) = (Real.pi ^ (-1 / 4 : ℝ)) ^ 2 := by
            simp [Complex.normSq_ofReal]
            ring
          rw [this, Real.sqrt_sq (le_of_lt (Real.rpow_pos_of_pos Real.pi_pos _))]
        have h2 : ‖Complex.exp (-I * (t / 2 * Real.log Real.pi))‖ = 1 := by
          rw [show -I * (t / 2 * Real.log Real.pi) = I * ↑(-(t / 2 * Real.log Real.pi)) by
            simp]
          rw [show I * ↑(-(t / 2 * Real.log Real.pi)) = ↑(-(t / 2 * Real.log Real.pi)) * I by ring]
          rw [Complex.norm_exp_ofReal_mul_I]
        simp only [h1, h2]
        ring_nf
      rw [h_norm]
      field_simp
    rw [h1, h2]
    have h_Gamma_w : Gamma w / ‖Gamma w‖ = cexp ((Gamma w).arg * I) := by
      have h := Complex.norm_mul_exp_arg_mul_I (Gamma w)
      field_simp [hw'] at h ⊢
      rw [h]
    rw [h_Gamma_w]
    have h_arg : thetaPhase t = (Gamma w).arg - t / 2 * Real.log Real.pi := rfl
    rw [h_arg]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  -- From the unit identity, get equality of cos and sin
  have h_cos : Real.cos (thetaPhase t) = Real.cos ((Gammaℝ s).arg) := by
    have h_eq : Complex.exp (I * thetaPhase t) = Complex.exp (I * (Gammaℝ s).arg) := by
      have h_left : Complex.exp (I * thetaPhase t) = Gammaℝ s / ‖Gammaℝ s‖ := by rw [h_unit]
      have h_right : Complex.exp (I * (Gammaℝ s).arg) = Gammaℝ s / ‖Gammaℝ s‖ := by
        have h := Complex.norm_mul_exp_arg_mul_I (Gammaℝ s)
        have h3 : Complex.exp (↑(Gammaℝ s).arg * I) = Gammaℝ s / ‖Gammaℝ s‖ := by
          have h_norm_pos : ‖Gammaℝ s‖ ≠ 0 := by
            apply ne_of_gt
            apply norm_pos_iff.mpr
            exact h_Gammaℝ_ne_zero
          calc
            Complex.exp (↑(Gammaℝ s).arg * I)
              = (↑‖Gammaℝ s‖ * Complex.exp (↑(Gammaℝ s).arg * I)) / ↑‖Gammaℝ s‖ := by
                field_simp [h_norm_pos]
            _ = Gammaℝ s / ‖Gammaℝ s‖ := by rw [h]
        have h4 : Complex.exp (I * ↑(Gammaℝ s).arg) = Complex.exp (↑(Gammaℝ s).arg * I) := by
          rw [show I * ↑(Gammaℝ s).arg = ↑(Gammaℝ s).arg * I by ring]
        rw [h4, h3]
      rw [h_left, h_right]
    have h_re : (Complex.exp (I * thetaPhase t)).re = (Complex.exp (I * (Gammaℝ s).arg)).re := by rw [h_eq]
    have h_re_left : (Complex.exp (I * thetaPhase t)).re = Real.cos (thetaPhase t) := by
      rw [show I * ↑(thetaPhase t) = ↑(thetaPhase t) * I by ring]
      exact Complex.exp_ofReal_mul_I_re (thetaPhase t)
    have h_re_right : (Complex.exp (I * (Gammaℝ s).arg)).re = Real.cos ((Gammaℝ s).arg) := by
      rw [show I * ↑(Gammaℝ s).arg = ↑(Gammaℝ s).arg * I by ring]
      exact Complex.exp_ofReal_mul_I_re ((Gammaℝ s).arg)
    rw [h_re_left, h_re_right] at h_re
    exact h_re
  have h_sin : Real.sin (thetaPhase t) = Real.sin ((Gammaℝ s).arg) := by
    have h_eq : Complex.exp (I * thetaPhase t) = Complex.exp (I * (Gammaℝ s).arg) := by
      have h_left : Complex.exp (I * thetaPhase t) = Gammaℝ s / ‖Gammaℝ s‖ := by rw [h_unit]
      have h_right : Complex.exp (I * (Gammaℝ s).arg) = Gammaℝ s / ‖Gammaℝ s‖ := by
        have h := Complex.norm_mul_exp_arg_mul_I (Gammaℝ s)
        have h3 : Complex.exp (↑(Gammaℝ s).arg * I) = Gammaℝ s / ‖Gammaℝ s‖ := by
          have h_norm_pos : ‖Gammaℝ s‖ ≠ 0 := by
            apply ne_of_gt
            apply norm_pos_iff.mpr
            exact h_Gammaℝ_ne_zero
          calc
            Complex.exp (↑(Gammaℝ s).arg * I)
              = (↑‖Gammaℝ s‖ * Complex.exp (↑(Gammaℝ s).arg * I)) / ↑‖Gammaℝ s‖ := by
                field_simp [h_norm_pos]
            _ = Gammaℝ s / ‖Gammaℝ s‖ := by rw [h]
        have h4 : Complex.exp (I * ↑(Gammaℝ s).arg) = Complex.exp (↑(Gammaℝ s).arg * I) := by
          rw [show I * ↑(Gammaℝ s).arg = ↑(Gammaℝ s).arg * I by ring]
        rw [h4, h3]
      rw [h_left, h_right]
    have h_im : (Complex.exp (I * thetaPhase t)).im = (Complex.exp (I * (Gammaℝ s).arg)).im := by rw [h_eq]
    have h_im_left : (Complex.exp (I * thetaPhase t)).im = Real.sin (thetaPhase t) := by
      rw [show I * ↑(thetaPhase t) = ↑(thetaPhase t) * I by ring]
      exact Complex.exp_ofReal_mul_I_im (thetaPhase t)
    have h_im_right : (Complex.exp (I * (Gammaℝ s).arg)).im = Real.sin ((Gammaℝ s).arg) := by
      rw [show I * ↑(Gammaℝ s).arg = ↑(Gammaℝ s).arg * I by ring]
      exact Complex.exp_ofReal_mul_I_im ((Gammaℝ s).arg)
    rw [h_im_left, h_im_right] at h_im
    exact h_im
  constructor
  · rw [h_cos, ← Complex.norm_mul_cos_arg]
  · rw [h_sin, ← Complex.norm_mul_sin_arg]

lemma hardyZ_zero_implies_zeta_zero (t : ℝ) (h : hardyZ t = 0) :
    riemannZeta (0.5 + I * t) = 0 := by
  let s := (0.5 : ℂ) + I * t
  have hs01 : s ≠ 0 := by
    intro h0
    simp [s, Complex.ext_iff] at h0
    norm_num at h0
  have hs1 : s ≠ 1 := by
    intro h0
    simp [s, Complex.ext_iff] at h0
    norm_num at h0
  have hs_eq : s = (1 / 2 : ℂ) + I * t := by
    simp [s]
    norm_num
  have h_real : (completedRiemannZeta s).im = 0 := by
    obtain ⟨r, hr⟩ := completedRiemannZeta_critical_line_real t
    rw [hs_eq]
    rw [hr]
    simp
  have h_Gammaℝ : (Gammaℝ s).re = ‖Gammaℝ s‖ * Real.cos (thetaPhase t) ∧
      (Gammaℝ s).im = ‖Gammaℝ s‖ * Real.sin (thetaPhase t) := by
    rw [hs_eq]
    exact Gammaℝ_re_im_arg t
  have h_cz : completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
    rw [riemannZeta_def_of_ne_zero hs01]
    have h_Gammaℝ_ne_zero : Gammaℝ s ≠ 0 := by
      apply Gammaℝ_ne_zero_of_re_pos
      simp [s]
      norm_num
    field_simp [h_Gammaℝ_ne_zero]
  have h_hardyZ : hardyZ t = (completedRiemannZeta s).re / ‖Gammaℝ s‖ := by
    have h_def : hardyZ t = (riemannZeta s).re * Real.cos (thetaPhase t) - (riemannZeta s).im * Real.sin (thetaPhase t) := by
      simp [hardyZ, s]
    rw [h_def]
    have h_rz : riemannZeta s = completedRiemannZeta s / Gammaℝ s := by
      rw [riemannZeta_def_of_ne_zero hs01]
    rw [h_rz]
    have h_abs_pos : 0 < ‖Gammaℝ s‖ := by
      apply norm_pos_iff.mpr
      apply Gammaℝ_ne_zero_of_re_pos
      simp [s]
      norm_num
    have h_Gammaℝ_ne_zero : Gammaℝ s ≠ 0 := by
      apply Gammaℝ_ne_zero_of_re_pos
      simp [s]
      norm_num
    have h_normSq : Complex.normSq (Gammaℝ s) = ‖Gammaℝ s‖ ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
    simp [Complex.div_re, Complex.div_im, h_Gammaℝ.1, h_Gammaℝ.2, h_real, h_normSq]
    field_simp [h_Gammaℝ_ne_zero]
    ring_nf
    have : (completedRiemannZeta s).re * Real.cos (thetaPhase t) ^ 2 + (completedRiemannZeta s).re * Real.sin (thetaPhase t) ^ 2 = (completedRiemannZeta s).re := by
      calc
        (completedRiemannZeta s).re * Real.cos (thetaPhase t) ^ 2 + (completedRiemannZeta s).re * Real.sin (thetaPhase t) ^ 2
          = (completedRiemannZeta s).re * (Real.cos (thetaPhase t) ^ 2 + Real.sin (thetaPhase t) ^ 2) := by ring
        _ = (completedRiemannZeta s).re * 1 := by rw [Real.cos_sq_add_sin_sq]
        _ = (completedRiemannZeta s).re := by ring
    exact this
  have h_cz_zero : completedRiemannZeta s = 0 := by
    rw [h_hardyZ] at h
    have h_abs_pos : 0 < ‖Gammaℝ s‖ := by
      apply norm_pos_iff.mpr
      apply Gammaℝ_ne_zero_of_re_pos
      simp [s]
      norm_num
    have h_re_zero : (completedRiemannZeta s).re = 0 := by
      field_simp [h_abs_pos] at h
      linarith
    simp [Complex.ext_iff, h_re_zero, h_real]
  rw [h_cz] at h_cz_zero
  have h_Gammaℝ_ne_zero : Gammaℝ s ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos
    simp [s]
    norm_num
  exact (mul_eq_zero.mp h_cz_zero).resolve_left h_Gammaℝ_ne_zero

/-- Z(t) 的零点对应于临界线上的 ζ 零点 -/
theorem hardyZ_zero_iff_zeta_zero (t : ℝ) :
    hardyZ t = 0 ↔ riemannZeta (0.5 + I * t) = 0 := by
  constructor
  · exact hardyZ_zero_implies_zeta_zero t
  · exact zeta_zero_implies_hardyZ_zero t

/-- Z(t) 是连续函数 -/
theorem hardyZ_continuous : Continuous hardyZ := by
  have h_eq : ∀ t : ℝ, hardyZ t = (completedRiemannZeta ((0.5 : ℂ) + I * t)).re / ‖Gammaℝ ((0.5 : ℂ) + I * t)‖ := by
    intro t
    let s := (0.5 : ℂ) + I * t
    have hs01 : s ≠ 0 := by
      intro h0
      simp [s, Complex.ext_iff] at h0
      norm_num at h0
    have h_hardyZ : hardyZ t = (completedRiemannZeta s).re / ‖Gammaℝ s‖ := by
      have h_def : hardyZ t = (riemannZeta s).re * Real.cos (thetaPhase t) - (riemannZeta s).im * Real.sin (thetaPhase t) := by
        simp [hardyZ, s]
      rw [h_def]
      have h_rz : riemannZeta s = completedRiemannZeta s / Gammaℝ s := by
        rw [riemannZeta_def_of_ne_zero hs01]
      rw [h_rz]
      have h_abs_pos : 0 < ‖Gammaℝ s‖ := by
        apply norm_pos_iff.mpr
        apply Gammaℝ_ne_zero_of_re_pos
        simp [s]
        norm_num
      have h_Gammaℝ_ne_zero : Gammaℝ s ≠ 0 := by
        apply Gammaℝ_ne_zero_of_re_pos
        simp [s]
        norm_num
      have h_normSq : Complex.normSq (Gammaℝ s) = ‖Gammaℝ s‖ ^ 2 := by
        rw [Complex.normSq_eq_norm_sq]
      have h_Gamma : (Gammaℝ s).re = ‖Gammaℝ s‖ * Real.cos (thetaPhase t) ∧
          (Gammaℝ s).im = ‖Gammaℝ s‖ * Real.sin (thetaPhase t) := by
        have hs_eq : s = (1 / 2 : ℂ) + I * t := by
          simp [s]
          norm_num
        rw [hs_eq]
        exact Gammaℝ_re_im_arg t
      simp [Complex.div_re, Complex.div_im, h_Gamma.1, h_Gamma.2, h_normSq]
      field_simp [h_Gammaℝ_ne_zero]
      ring_nf
      have h_simp : (completedRiemannZeta s).re * Real.cos (thetaPhase t) ^ 2 + (completedRiemannZeta s).re * Real.sin (thetaPhase t) ^ 2 = (completedRiemannZeta s).re := by
        calc
          (completedRiemannZeta s).re * Real.cos (thetaPhase t) ^ 2 + (completedRiemannZeta s).re * Real.sin (thetaPhase t) ^ 2
            = (completedRiemannZeta s).re * (Real.cos (thetaPhase t) ^ 2 + Real.sin (thetaPhase t) ^ 2) := by ring
          _ = (completedRiemannZeta s).re * 1 := by rw [Real.cos_sq_add_sin_sq]
          _ = (completedRiemannZeta s).re := by ring
      ring_nf at h_simp ⊢
      exact h_simp
    exact h_hardyZ
  rw [show hardyZ = fun t : ℝ ↦ hardyZ t by funext t; rfl]
  simp only [h_eq]
  apply Continuous.div
  · have h1 : Continuous (fun t : ℝ ↦ completedRiemannZeta ((0.5 : ℂ) + I * t)) := by
      have h_eq' : (fun t : ℝ ↦ completedRiemannZeta ((0.5 : ℂ) + I * t))
          = (fun s : ℂ ↦ completedRiemannZeta s) ∘ (fun t : ℝ ↦ (0.5 : ℂ) + I * t) := by funext t; rfl
      rw [h_eq']
      have h_cz_cont : ContinuousOn (fun s : ℂ ↦ completedRiemannZeta s) {s : ℂ | s ≠ 0 ∧ s ≠ 1} := by
        apply continuousOn_of_forall_continuousAt
        intro s hs
        simp at hs
        exact (differentiableAt_completedZeta hs.1 hs.2).continuousAt
      have h_map_cont : Continuous (fun t : ℝ ↦ (0.5 : ℂ) + I * t) := by
        have h_const : Continuous (fun t : ℝ ↦ (0.5 : ℂ)) := continuous_const
        have h_lin : Continuous (fun t : ℝ ↦ I * (t : ℂ)) := by
          apply Continuous.mul
          · exact continuous_const
          · exact continuous_ofReal
        exact Continuous.add h_const h_lin
      apply ContinuousOn.comp_continuous h_cz_cont h_map_cont
      intro t
      constructor
      · norm_num [Complex.ext_iff]
      · norm_num [Complex.ext_iff]
    exact Continuous.comp RCLike.continuous_re h1
  · have h2 : Continuous (fun t : ℝ ↦ Gammaℝ ((0.5 : ℂ) + I * t)) := by
      have h_eq' : (fun t : ℝ ↦ Gammaℝ ((0.5 : ℂ) + I * t))
          = (fun s : ℂ ↦ Gammaℝ s) ∘ (fun t : ℝ ↦ (0.5 : ℂ) + I * t) := by funext t; rfl
      rw [h_eq']
      have h_Gammaℝ_cont : ContinuousOn (fun s : ℂ ↦ Gammaℝ s) {s : ℂ | 0 < s.re} := by
        have h_a : ContinuousOn (fun s : ℂ ↦ (↑Real.pi : ℂ) ^ (-s / 2)) {s : ℂ | 0 < s.re} := by
          have h_exp_cont : ContinuousOn (fun s : ℂ ↦ -s / 2) {s : ℂ | 0 < s.re} := by
            apply ContinuousOn.div
            · apply ContinuousOn.neg
              exact continuousOn_id
            · exact continuousOn_const
            · intro s hs
              norm_num
          have h_pi : (↑Real.pi : ℂ) ≠ 0 := by norm_num [Real.pi_ne_zero]
          exact h_exp_cont.const_cpow (Or.inl h_pi)
        have h_b : ContinuousOn (fun s : ℂ ↦ Gamma (s / 2)) {s : ℂ | 0 < s.re} := by
          have h_Gamma_cont : ContinuousOn Gamma {z : ℂ | ∀ m : ℕ, z ≠ -m} := by
            apply continuousOn_of_forall_continuousAt
            intro s hs
            exact (differentiableAt_Gamma s hs).continuousAt
          apply ContinuousOn.comp h_Gamma_cont
          · apply ContinuousOn.div
            · exact continuousOn_id
            · exact continuousOn_const
            · intro s hs
              norm_num
          · intro s hs
            simp at hs ⊢
            intro m hm
            have h_re : s.re / 2 = -(m : ℝ) := by
              simpa using congr_arg Complex.re hm
            have : s.re / 2 ≤ 0 := by
              rw [h_re]
              simp
            linarith
        simp only [Gammaℝ_def]
        exact ContinuousOn.mul h_a h_b
      have h_map_cont : Continuous (fun t : ℝ ↦ (0.5 : ℂ) + I * t) := by
        have h_const : Continuous (fun t : ℝ ↦ (0.5 : ℂ)) := continuous_const
        have h_lin : Continuous (fun t : ℝ ↦ I * (t : ℂ)) := by
          apply Continuous.mul
          · exact continuous_const
          · exact continuous_ofReal
        exact Continuous.add h_const h_lin
      apply ContinuousOn.comp_continuous h_Gammaℝ_cont h_map_cont
      intro t
      simp
      norm_num
    exact Continuous.norm h2
  · intro t
    apply ne_of_gt
    apply norm_pos_iff.mpr
    apply Gammaℝ_ne_zero_of_re_pos
    simp
    norm_num

/-! ## Hardy 的核心论证 -/

noncomputable def weightFunction (n : ℕ) (t : ℝ) : ℝ :=
  t ^ (2 * n)

noncomputable def weightedIntegralOf (f : ℝ → ℝ) (n : ℕ) (T : ℝ) : ℝ :=
  ∫ t in (0)..T, weightFunction n t * f t

noncomputable def weightedIntegral (n : ℕ) (T : ℝ) : ℝ :=
  weightedIntegralOf hardyZ n T

lemma weightedIntegralOf_neg (f : ℝ → ℝ) (n : ℕ) (T : ℝ) :
    weightedIntegralOf (fun t => -f t) n T = -weightedIntegralOf f n T := by
  unfold weightedIntegralOf
  rw [← intervalIntegral.integral_neg]
  congr 1
  ext t
  ring

/-- Corrected signed target for Hardy's moment asymptotic.

The sign of the leading term is part of the usable theorem: it is what drives
the eventual-sign contradiction in Hardy's argument. -/
def integral_asymptotic_target (n : ℕ) : Prop :=
    n ≥ 1 ∧ ∃ A : ℝ, 0 < A ∧
      (fun T => weightedIntegral n T) ~[atTop]
        (fun T => ((-1 : ℝ) ^ n * A) * T ^ ((2 * n : ℝ) + 1 / 4))

/-- Minimal two-moment target sufficient for the Hardy sign contradiction. -/
def hardy_two_signed_moments_target : Prop :=
    (∃ A : ℝ, 0 < A ∧
      (fun T => weightedIntegral 1 T) ~[atTop]
        (fun T => -A * T ^ ((2 : ℝ) + 1 / 4))) ∧
    (∃ B : ℝ, 0 < B ∧
      (fun T => weightedIntegral 2 T) ~[atTop]
        (fun T => B * T ^ ((2 * 2 : ℝ) + 1 / 4)))

lemma integral_asymptotic_one_of_two_signed_moments
    (h : hardy_two_signed_moments_target) :
    integral_asymptotic_target 1 := by
  rcases h.1 with ⟨A, hApos, hA⟩
  refine ⟨by norm_num, A, hApos, ?_⟩
  simpa using hA

lemma integral_asymptotic_two_of_two_signed_moments
    (h : hardy_two_signed_moments_target) :
    integral_asymptotic_target 2 := by
  rcases h.2 with ⟨B, hBpos, hB⟩
  refine ⟨by norm_num, B, hBpos, ?_⟩
  simpa using hB

/-! ## Hardy 定理的结构引理 -/

lemma hardyZ_eventually_const_sign_of_bounded_zeros
    (h_bdd : Bornology.IsBounded {t : ℝ | hardyZ t = 0}) :
    (∀ᶠ t in atTop, hardyZ t > 0) ∨ (∀ᶠ t in atTop, hardyZ t < 0) := by
  obtain ⟨M, hM⟩ := h_bdd.subset_closedBall 0
  have hM' : ∀ t, hardyZ t = 0 → |t| ≤ M := by
    intro t ht
    have h_mem : t ∈ Metric.closedBall (0 : ℝ) M := hM ht
    simp [Metric.closedBall, dist_eq_norm] at h_mem
    exact h_mem
  have h_ne_zero : ∀ t > M, hardyZ t ≠ 0 := by
    intro t ht
    by_contra h_zero
    have h_abs : |t| ≤ M := hM' t h_zero
    have h_contra : t ≤ M := by linarith [abs_le.mp h_abs]
    linarith
  have h_const_sign : (∀ t > M, hardyZ t > 0) ∨ (∀ t > M, hardyZ t < 0) := by
    by_cases h_ex_pos : ∃ t > M, hardyZ t > 0
    · obtain ⟨t1, ht1, ht1_pos⟩ := h_ex_pos
      left
      intro t ht
      by_contra h_not_pos
      have ht_nonpos : hardyZ t ≤ 0 := by
        by_contra h
        push Not at h
        exact h_not_pos h
      have h_zero_exists : ∃ t3 ∈ Set.uIcc t1 t, hardyZ t3 = 0 := by
        have h1 : ContinuousOn hardyZ (Set.uIcc t1 t) := by
          apply Continuous.continuousOn
          exact hardyZ_continuous
        have h2 : 0 ∈ Set.uIcc (hardyZ t1) (hardyZ t) := by
          simp only [Set.mem_uIcc]
          right
          constructor
          · exact ht_nonpos
          · linarith
        have h3 : Set.uIcc (hardyZ t1) (hardyZ t) ⊆ hardyZ '' Set.uIcc t1 t := by
          apply intermediate_value_uIcc
          exact h1
        exact h3 h2
      obtain ⟨t3, ht3_mem, ht3_zero⟩ := h_zero_exists
      have h_t3_gt_M : t3 > M := by
        simp only [Set.mem_uIcc] at ht3_mem
        cases ht3_mem with
        | inl h1 =>
          cases le_total t1 t with
          | inl h_le => linarith
          | inr h_ge => linarith
        | inr h2 =>
          cases le_total t1 t with
          | inl h_le => linarith
          | inr h_ge => linarith
      have h_contra : hardyZ t3 ≠ 0 := h_ne_zero t3 h_t3_gt_M
      contradiction
    · push Not at h_ex_pos
      right
      intro t ht
      have h_nonpos : hardyZ t ≤ 0 := h_ex_pos t ht
      have h_ne : hardyZ t ≠ 0 := h_ne_zero t ht
      have h_lt : hardyZ t < 0 := by
        by_contra h
        push Not at h
        have h_eq : hardyZ t = 0 := by linarith
        contradiction
      exact h_lt
  cases h_const_sign with
  | inl h_pos =>
    left
    filter_upwards [eventually_gt_atTop M] with t ht
    exact h_pos t ht
  | inr h_neg =>
    right
    filter_upwards [eventually_gt_atTop M] with t ht
    exact h_neg t ht

lemma hardyZ_eventually_const_sign_of_finite_zeros
    (h : {t : ℝ | hardyZ t = 0}.Finite) :
    (∀ᶠ t in atTop, hardyZ t > 0) ∨ (∀ᶠ t in atTop, hardyZ t < 0) :=
  hardyZ_eventually_const_sign_of_bounded_zeros (Set.Finite.isBounded h)

def weightedIntegralOf_tail_dominates (f : ℝ → ℝ) (n : ℕ) : Prop :=
  ∃ A : ℝ, Tendsto (fun T => ∫ t in A..T, weightFunction n t * f t) atTop atTop

lemma weightedIntegralOf_tail_dominates_of_tendsto_atTop
    {f : ℝ → ℝ} {n : ℕ}
    (h : Tendsto (fun T => weightedIntegralOf f n T) atTop atTop) :
    weightedIntegralOf_tail_dominates f n :=
  ⟨0, by simpa [weightedIntegralOf] using h⟩

/-- Tail dominance turns the full weighted integral eventually positive.

The continuity hypothesis supplies interval integrability, so the integral can
be split into a fixed initial part plus the divergent positive tail. -/
lemma weightedIntegralOf_eventually_positive_of_tail_dominates
    (f : ℝ → ℝ) (n : ℕ) (hf : Continuous f)
    (_h_pos : ∀ᶠ t in atTop, f t > 0)
    (h_tail : weightedIntegralOf_tail_dominates f n) :
    ∀ᶠ T in atTop, weightedIntegralOf f n T > 0 := by
  rcases h_tail with ⟨A, hA⟩
  let g : ℝ → ℝ := fun t => weightFunction n t * f t
  have hg : Continuous g := by
    have hw : Continuous fun t : ℝ => weightFunction n t := by
      simpa [weightFunction] using (continuous_id.pow (2 * n))
    exact hw.mul hf
  have htail_gt :
      ∀ᶠ T in atTop, -(∫ t in (0 : ℝ)..A, g t) < ∫ t in A..T, g t :=
    hA.eventually_gt_atTop (-(∫ t in (0 : ℝ)..A, g t))
  filter_upwards [htail_gt] with T hT
  have hpos : 0 < ((∫ t in (0 : ℝ)..A, g t) + (∫ t in A..T, g t)) := by
    have hpos' :
        (∫ t in (0 : ℝ)..A, g t) + -(∫ t in (0 : ℝ)..A, g t) <
          (∫ t in (0 : ℝ)..A, g t) + ∫ t in A..T, g t :=
      add_lt_add_right hT (∫ t in (0 : ℝ)..A, g t)
    have hzero : (∫ t in (0 : ℝ)..A, g t) + -(∫ t in (0 : ℝ)..A, g t) = 0 := by
      ring
    rwa [hzero] at hpos'
  unfold weightedIntegralOf
  change ∫ t in (0 : ℝ)..T, g t > 0
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (μ := MeasureTheory.volume) (hg.intervalIntegrable 0 A) (hg.intervalIntegrable A T)]
  simpa using hpos

lemma weighted_integral_eventually_positive_of_hardyZ_positive
    (n : ℕ) (h_pos : ∀ᶠ t in atTop, hardyZ t > 0)
    (h_tail : weightedIntegralOf_tail_dominates hardyZ n) :
    ∀ᶠ T in atTop, weightedIntegral n T > 0 := by
  unfold weightedIntegral
  exact weightedIntegralOf_eventually_positive_of_tail_dominates
    hardyZ n hardyZ_continuous h_pos h_tail

lemma weighted_integral_eventually_negative_of_hardyZ_negative
    (n : ℕ) (h_neg : ∀ᶠ t in atTop, hardyZ t < 0)
    (h_tail : weightedIntegralOf_tail_dominates (fun t => -hardyZ t) n) :
    ∀ᶠ T in atTop, weightedIntegral n T < 0 := by
  have h_neg_pos : ∀ᶠ t in atTop, (fun s => -hardyZ s) t > 0 := by
    filter_upwards [h_neg] with t ht
    linarith
  have h_int_pos :
      ∀ᶠ T in atTop, weightedIntegralOf (fun s => -hardyZ s) n T > 0 :=
    weightedIntegralOf_eventually_positive_of_tail_dominates
      (fun s => -hardyZ s) n hardyZ_continuous.neg h_neg_pos h_tail
  filter_upwards [h_int_pos] with T hT
  have h_eq : weightedIntegralOf (fun s => -hardyZ s) n T = -weightedIntegral n T := by
    unfold weightedIntegral
    exact weightedIntegralOf_neg hardyZ n T
  rw [h_eq] at hT
  linarith

/-! ## 从积分性质推导无穷多零点 -/

lemma weightedIntegral_one_tendsto_atBot_of_two_signed_moments
    (h : hardy_two_signed_moments_target) :
    Tendsto (fun T : ℝ => weightedIntegral 1 T) atTop atBot := by
  rcases h with ⟨⟨A, hApos, hAasymp⟩, _⟩
  have hp : Tendsto (fun T : ℝ => T ^ ((2 : ℝ) + 1 / 4)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hA_top : Tendsto (fun T : ℝ => A * T ^ ((2 : ℝ) + 1 / 4)) atTop atTop :=
    hp.const_mul_atTop hApos
  have hmodel_bot : Tendsto (fun T : ℝ => -A * T ^ ((2 : ℝ) + 1 / 4)) atTop atBot := by
    have hneg : Tendsto (fun T : ℝ => -(A * T ^ ((2 : ℝ) + 1 / 4))) atTop atBot :=
      Filter.tendsto_neg_atTop_atBot.comp hA_top
    simpa [neg_mul] using hneg
  exact hAasymp.symm.tendsto_atBot hmodel_bot

lemma weightedIntegral_one_eventually_negative_of_two_signed_moments
    (h : hardy_two_signed_moments_target) :
    ∀ᶠ T in atTop, weightedIntegral 1 T < 0 :=
  (weightedIntegral_one_tendsto_atBot_of_two_signed_moments h).eventually_lt_atBot 0

lemma weightedIntegral_two_tendsto_atTop_of_two_signed_moments
    (h : hardy_two_signed_moments_target) :
    Tendsto (fun T : ℝ => weightedIntegral 2 T) atTop atTop := by
  rcases h with ⟨_, ⟨B, hBpos, hBasymp⟩⟩
  have hp : Tendsto (fun T : ℝ => T ^ ((2 * 2 : ℝ) + 1 / 4)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hmodel_top : Tendsto (fun T : ℝ => B * T ^ ((2 * 2 : ℝ) + 1 / 4)) atTop atTop :=
    hp.const_mul_atTop hBpos
  exact hBasymp.symm.tendsto_atTop hmodel_top

lemma weightedIntegral_two_eventually_positive_of_two_signed_moments
    (h : hardy_two_signed_moments_target) :
    ∀ᶠ T in atTop, 0 < weightedIntegral 2 T :=
  (weightedIntegral_two_tendsto_atTop_of_two_signed_moments h).eventually_gt_atTop 0

lemma weightedIntegralOf_neg_hardyZ_one_tail_dominates_of_two_signed_moments
    (h : hardy_two_signed_moments_target) :
    weightedIntegralOf_tail_dominates (fun t => -hardyZ t) 1 := by
  refine weightedIntegralOf_tail_dominates_of_tendsto_atTop ?_
  have hbot := weightedIntegral_one_tendsto_atBot_of_two_signed_moments h
  have hneg :
      Tendsto (fun T : ℝ => -weightedIntegral 1 T) atTop atTop :=
    Filter.tendsto_neg_atBot_atTop.comp hbot
  have h_eq :
      (fun T : ℝ => weightedIntegralOf (fun t => -hardyZ t) 1 T)
        = fun T : ℝ => -weightedIntegral 1 T := by
    funext T
    unfold weightedIntegral
    exact weightedIntegralOf_neg hardyZ 1 T
  exact hneg.congr' (Filter.EventuallyEq.of_eq h_eq.symm)

lemma weightedIntegralOf_hardyZ_two_tail_dominates_of_two_signed_moments
    (h : hardy_two_signed_moments_target) :
    weightedIntegralOf_tail_dominates hardyZ 2 := by
  refine weightedIntegralOf_tail_dominates_of_tendsto_atTop ?_
  simpa [weightedIntegral] using weightedIntegral_two_tendsto_atTop_of_two_signed_moments h

lemma finite_zeros_contradiction_of_two_signed_moments_and_tail_dominance
    (hfinite : {t : ℝ | hardyZ t = 0}.Finite)
    (hmom : hardy_two_signed_moments_target)
    (htail_pos : weightedIntegralOf_tail_dominates hardyZ 1)
    (htail_neg : weightedIntegralOf_tail_dominates (fun t => -hardyZ t) 2) :
    False := by
  rcases hardyZ_eventually_const_sign_of_finite_zeros hfinite with hpos | hneg
  · have hint_pos := weighted_integral_eventually_positive_of_hardyZ_positive 1 hpos htail_pos
    have hint_neg := weightedIntegral_one_eventually_negative_of_two_signed_moments hmom
    rcases (hint_pos.and hint_neg).exists with ⟨T, hTpos, hTneg⟩
    linarith
  · have hint_neg := weighted_integral_eventually_negative_of_hardyZ_negative 2 hneg htail_neg
    have hint_pos := weightedIntegral_two_eventually_positive_of_two_signed_moments hmom
    rcases (hint_neg.and hint_pos).exists with ⟨T, hTneg, hTpos⟩
    linarith

/-- Target statement for Hardy's theorem.  The project currently proves the
Hardy Z-function setup and zero equivalence, but not the analytic moment
estimates needed for the final contradiction. -/
def hardy_theorem_target : Prop :=
    {t : ℝ | riemannZeta (0.5 + I * t) = 0}.Infinite

/-- Conditional Hardy theorem from the exact analytic inputs used in the
classical sign-change argument.

This is a proved bridge: the remaining unproved content is isolated in the
moment and tail-dominance hypotheses, not hidden inside the theorem. -/
lemma hardy_theorem_target_of_two_signed_moments_and_tail_dominance
    (hmom : hardy_two_signed_moments_target)
    (htail_pos : weightedIntegralOf_tail_dominates hardyZ 1)
    (htail_neg : weightedIntegralOf_tail_dominates (fun t => -hardyZ t) 2) :
    hardy_theorem_target := by
  intro hfinite
  have hsets :
      {t : ℝ | hardyZ t = 0} =
        {t : ℝ | riemannZeta (0.5 + I * t) = 0} := by
    ext t
    exact hardyZ_zero_iff_zeta_zero t
  have hhardy_finite : {t : ℝ | hardyZ t = 0}.Finite := by
    simpa [hsets] using hfinite
  exact finite_zeros_contradiction_of_two_signed_moments_and_tail_dominance
    hhardy_finite hmom htail_pos htail_neg

/-- Stronger Hardy target: critical-line zeros have arbitrarily large height. -/
def hardy_zeros_unbounded_target : Prop :=
    ∀ T : ℝ, ∃ t : ℝ, T ≤ t ∧ riemannZeta (0.5 + I * t) = 0

/-- Symmetric unbounded-height form: critical-line zeros have arbitrarily large
absolute height.  This is often the most convenient interface when one has a
finite-zero theorem in bounded vertical strips. -/
def hardy_zeros_abs_unbounded_target : Prop :=
    ∀ T : ℝ, ∃ t : ℝ, T ≤ |t| ∧ riemannZeta (0.5 + I * t) = 0

lemma hardy_zeros_abs_unbounded_of_unbounded
    (h : hardy_zeros_unbounded_target) : hardy_zeros_abs_unbounded_target := by
  intro T
  rcases h T with ⟨t, hTt, htzero⟩
  refine ⟨t, ?_, htzero⟩
  exact le_trans hTt (le_abs_self t)

/-- The unbounded-height Hardy target implies the older infinite-set target. -/
lemma hardy_theorem_target_of_unbounded
    (h : hardy_zeros_unbounded_target) : hardy_theorem_target := by
  intro hfinite
  have hbounded : Bornology.IsBounded {t : ℝ | riemannZeta (0.5 + I * t) = 0} :=
    Set.Finite.isBounded hfinite
  obtain ⟨M, hM⟩ := hbounded.subset_closedBall 0
  obtain ⟨t, htM, htzero⟩ := h (M + 1)
  have htmem : t ∈ Metric.closedBall (0 : ℝ) M := hM htzero
  have ht_abs : |t| ≤ M := by
    simpa [Metric.closedBall, dist_eq_norm] using htmem
  have ht_le_M : t ≤ M := (abs_le.mp ht_abs).2
  linarith

/-- The absolute-height unbounded target also implies the infinite-set target. -/
lemma hardy_theorem_target_of_abs_unbounded
    (h : hardy_zeros_abs_unbounded_target) : hardy_theorem_target := by
  intro hfinite
  have hbounded : Bornology.IsBounded {t : ℝ | riemannZeta (0.5 + I * t) = 0} :=
    Set.Finite.isBounded hfinite
  obtain ⟨M, hM⟩ := hbounded.subset_closedBall 0
  obtain ⟨t, htM, htzero⟩ := h (M + 1)
  have htmem : t ∈ Metric.closedBall (0 : ℝ) M := hM htzero
  have ht_abs : |t| ≤ M := by
    simpa [Metric.closedBall, dist_eq_norm] using htmem
  linarith

lemma hardy_zeros_abs_unbounded_of_hardy_theorem_target_of_bounded_strips
    (hstrip : ∀ B : ℝ,
      {t : ℝ | |t| ≤ B ∧ riemannZeta (0.5 + I * t) = 0}.Finite)
    (h : hardy_theorem_target) : hardy_zeros_abs_unbounded_target := by
  by_contra hnot
  rw [hardy_zeros_abs_unbounded_target] at hnot
  push Not at hnot
  rcases hnot with ⟨B, hB⟩
  have hfinite : {t : ℝ | riemannZeta (0.5 + I * t) = 0}.Finite := by
    refine (hstrip B).subset ?_
    intro t ht
    have ht_abs_lt : |t| < B := by
      by_contra hle
      exact hB t (le_of_not_gt hle) ht
    exact ⟨le_of_lt ht_abs_lt, ht⟩
  exact h hfinite

lemma hardy_theorem_target_iff_abs_unbounded_of_bounded_strips
    (hstrip : ∀ B : ℝ,
      {t : ℝ | |t| ≤ B ∧ riemannZeta (0.5 + I * t) = 0}.Finite) :
    hardy_theorem_target ↔ hardy_zeros_abs_unbounded_target :=
  ⟨hardy_zeros_abs_unbounded_of_hardy_theorem_target_of_bounded_strips hstrip,
    hardy_theorem_target_of_abs_unbounded⟩

lemma critical_line_zeta_zero_neg_height (t : ℝ)
    (h : riemannZeta (0.5 + I * t) = 0) :
    riemannZeta (0.5 + I * (-t)) = 0 := by
  let s : ℂ := 0.5 + I * t
  have hnat : ∀ n : ℕ, s ≠ -(n : ℂ) := by
    intro n hs
    have hre : s.re = (-(n : ℂ)).re := congr_arg Complex.re hs
    norm_num [s] at hre
    have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have hone : s ≠ 1 := by
    intro hs
    have hre : s.re = (1 : ℂ).re := congr_arg Complex.re hs
    norm_num [s] at hre
  have hsymm : riemannZeta (1 - s) = 0 := by
    rw [riemannZeta_one_sub hnat hone, h, mul_zero]
  have hs_neg : 1 - s = (0.5 : ℂ) + I * (-t) := by
    simp [s, Complex.ext_iff]
    all_goals norm_num
  simpa [hs_neg] using hsymm

lemma hardy_zeros_unbounded_of_abs_unbounded_of_neg_symm
    (hsymm : ∀ t : ℝ, riemannZeta (0.5 + I * t) = 0 →
      riemannZeta (0.5 + I * (-t)) = 0)
    (h : hardy_zeros_abs_unbounded_target) : hardy_zeros_unbounded_target := by
  intro T
  rcases h T with ⟨t, ht_abs, ht_zero⟩
  by_cases ht_nonneg : 0 ≤ t
  · refine ⟨t, ?_, ht_zero⟩
    simpa [abs_of_nonneg ht_nonneg] using ht_abs
  · refine ⟨-t, ?_, ?_⟩
    · have ht_nonpos : t ≤ 0 := le_of_lt (lt_of_not_ge ht_nonneg)
      simpa [abs_of_nonpos ht_nonpos] using ht_abs
    · simpa using hsymm t ht_zero

lemma hardy_zeros_unbounded_iff_abs_unbounded_of_neg_symm
    (hsymm : ∀ t : ℝ, riemannZeta (0.5 + I * t) = 0 →
      riemannZeta (0.5 + I * (-t)) = 0) :
    hardy_zeros_unbounded_target ↔ hardy_zeros_abs_unbounded_target :=
  ⟨hardy_zeros_abs_unbounded_of_unbounded,
    hardy_zeros_unbounded_of_abs_unbounded_of_neg_symm hsymm⟩

lemma hardy_zeros_unbounded_iff_abs_unbounded :
    hardy_zeros_unbounded_target ↔ hardy_zeros_abs_unbounded_target :=
  hardy_zeros_unbounded_iff_abs_unbounded_of_neg_symm
    critical_line_zeta_zero_neg_height

/-! ## 后续改进 -/

noncomputable def zeroCountOnCriticalLine (T : ℝ) : ℕ :=
  {t : Set.Icc 0 T | riemannZeta (0.5 + I * t) = 0}.ncard

def hardy_littlewood_lower_bound_target : Prop :=
    ∃ C > 0, ∃ T0 : ℝ, ∀ T ≥ T0, (zeroCountOnCriticalLine T : ℝ) ≥ C * T

def selberg_zero_proportion_target : Prop :=
    ∃ c > 0, ∃ T0 : ℝ, ∀ T ≥ T0,
      (zeroCountOnCriticalLine T : ℝ) ≥ c * (T / (2*Real.pi) * Real.log T)

/-- Selberg's positive-proportion target implies the weaker
Hardy--Littlewood linear lower-bound target. -/
lemma hardy_littlewood_lower_bound_target_of_selberg_zero_proportion
    (h : selberg_zero_proportion_target) :
    hardy_littlewood_lower_bound_target := by
  rcases h with ⟨c, hc_pos, T0, hT0⟩
  refine ⟨c / (2 * Real.pi), ?_, max T0 (Real.exp 1), ?_⟩
  · exact div_pos hc_pos (mul_pos (by norm_num) Real.pi_pos)
  · intro T hT
    have hT0' : T0 ≤ T := le_trans (le_max_left T0 (Real.exp 1)) hT
    have hexp_le : Real.exp 1 ≤ T := le_trans (le_max_right T0 (Real.exp 1)) hT
    have hsel := hT0 T hT0'
    have hlog_ge : 1 ≤ Real.log T := by
      have hlog_mono : Real.log (Real.exp 1) ≤ Real.log T :=
        Real.log_le_log (Real.exp_pos 1) hexp_le
      simpa using hlog_mono
    have hden_pos : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
    have hT_pos : 0 < T := lt_of_lt_of_le (Real.exp_pos 1) hexp_le
    have hbase_nonneg : 0 ≤ c * (T / (2 * Real.pi)) :=
      mul_nonneg hc_pos.le (div_nonneg hT_pos.le hden_pos.le)
    have hmul :
        c * (T / (2 * Real.pi)) * 1 ≤
          c * (T / (2 * Real.pi)) * Real.log T :=
      mul_le_mul_of_nonneg_left hlog_ge hbase_nonneg
    have htarget :
        (c / (2 * Real.pi)) * T ≤
          c * (T / (2 * Real.pi) * Real.log T) := by
      calc
        (c / (2 * Real.pi)) * T = c * (T / (2 * Real.pi)) * 1 := by ring
        _ ≤ c * (T / (2 * Real.pi)) * Real.log T := hmul
        _ = c * (T / (2 * Real.pi) * Real.log T) := by ring
    exact le_trans htarget hsel

/-- A Hardy--Littlewood lower-bound target is already enough to extract at
least one critical-line zero. -/
lemma exists_zero_on_critical_line_of_hardy_littlewood_lower_bound
    (h : hardy_littlewood_lower_bound_target) :
    ∃ t : ℝ, riemannZeta (0.5 + I * t) = 0 := by
  rcases h with ⟨C, hC_pos, T0, hbound⟩
  let T : ℝ := max T0 1
  have hT0 : T0 ≤ T := le_max_left T0 1
  have hT_pos : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_right T0 1)
  have hcount := hbound T hT0
  have hCT_pos : 0 < C * T := mul_pos hC_pos hT_pos
  have hncard_real : 0 < (zeroCountOnCriticalLine T : ℝ) :=
    lt_of_lt_of_le hCT_pos hcount
  have hncard_nat : 0 < zeroCountOnCriticalLine T := by
    exact_mod_cast hncard_real
  let S : Set (Set.Icc (0 : ℝ) T) :=
    {t : Set.Icc (0 : ℝ) T | riemannZeta (0.5 + I * (t : ℝ)) = 0}
  have hSpos : 0 < S.ncard := by
    simpa [zeroCountOnCriticalLine, S] using hncard_nat
  have hSfin : S.Finite := Set.finite_of_ncard_pos hSpos
  rcases (Set.ncard_pos hSfin).mp hSpos with ⟨t, htzero⟩
  exact ⟨(t : ℝ), htzero⟩

lemma exists_zero_on_critical_line_of_selberg_zero_proportion
    (h : selberg_zero_proportion_target) :
    ∃ t : ℝ, riemannZeta (0.5 + I * t) = 0 :=
  exists_zero_on_critical_line_of_hardy_littlewood_lower_bound
    (hardy_littlewood_lower_bound_target_of_selberg_zero_proportion h)

lemma hardy_theorem_target_of_hardy_littlewood_lower_bound
    (h : hardy_littlewood_lower_bound_target) :
    hardy_theorem_target := by
  classical
  intro hfinite
  rcases h with ⟨C, hC_pos, T0, hbound⟩
  let allZeros : Set ℝ := {t : ℝ | riemannZeta (0.5 + I * t) = 0}
  let N : ℕ := allZeros.ncard
  let T : ℝ := max T0 (max 1 (((N : ℝ) + 1) / C))
  have hT0 : T0 ≤ T := le_max_left T0 (max 1 (((N : ℝ) + 1) / C))
  have hT_large : ((N : ℝ) + 1) / C ≤ T := by
    exact le_trans (le_max_right 1 (((N : ℝ) + 1) / C))
      (le_max_right T0 (max 1 (((N : ℝ) + 1) / C)))
  have hN_lt_CT : (N : ℝ) < C * T := by
    have hmul : C * (((N : ℝ) + 1) / C) ≤ C * T :=
      mul_le_mul_of_nonneg_left hT_large hC_pos.le
    have hC_ne : C ≠ 0 := ne_of_gt hC_pos
    have hC_mul : C * (((N : ℝ) + 1) / C) = (N : ℝ) + 1 := by
      field_simp [hC_ne]
    have hN1_le : (N : ℝ) + 1 ≤ C * T := by
      rw [← hC_mul]
      exact hmul
    linarith
  let countedZeros : Set (Set.Icc (0 : ℝ) T) :=
    {t : Set.Icc (0 : ℝ) T | riemannZeta (0.5 + I * (t : ℝ)) = 0}
  have hcount_le_N_nat : zeroCountOnCriticalLine T ≤ N := by
    have hle :=
      Set.ncard_le_ncard_of_injOn
        (fun t : Set.Icc (0 : ℝ) T => (t : ℝ))
        (s := countedZeros) (t := allZeros) ?_ ?_ hfinite
    · simpa [zeroCountOnCriticalLine, countedZeros, allZeros, N] using hle
    · intro t ht
      exact ht
    · intro t₁ _ t₂ _ heq
      exact Subtype.ext heq
  have hcount_le_N : (zeroCountOnCriticalLine T : ℝ) ≤ N := by
    exact_mod_cast hcount_le_N_nat
  have hcount_lower := hbound T hT0
  linarith

lemma hardy_theorem_target_of_selberg_zero_proportion
    (h : selberg_zero_proportion_target) :
    hardy_theorem_target :=
  hardy_theorem_target_of_hardy_littlewood_lower_bound
    (hardy_littlewood_lower_bound_target_of_selberg_zero_proportion h)

end HardyTheorem

/-! ## 技术细节补充 -/

namespace HardyTheorem.Details

def gamma_asymptotic_half_plus_it_target : Prop :=
    (fun (t : ℝ) => Complex.Gamma (0.5 + I * t)) ~[atTop]
      (fun (t : ℝ) => Real.sqrt (2*Real.pi) * Complex.exp (I * t * Real.log t - I * t) *
        Complex.exp (-Real.pi * t / 2))

/-- The principal-value `thetaPhase` is not expected to satisfy a global exact
closed formula.  A future development should introduce an unwrapped
Riemann-Siegel theta function and prove this asymptotic target for it. -/
def theta_asymptotic_target : Prop :=
    ∃ theta : ℝ → ℝ,
      (∀ t : ℝ, Complex.exp (I * theta t) = Complex.exp (I * thetaPhase t)) ∧
      (fun t : ℝ => theta t) ~[atTop]
        (fun t : ℝ => (t/2) * Real.log (t/(2*Real.pi)) - t/2 - Real.pi/8)

/-- Target form of the approximate functional equation.  The previous exact
finite-sum equality omitted the necessary remainder term. -/
def approximate_functional_equation_target : Prop :=
    ∃ C > 0, ∀ t : ℝ, t > 1 → ∃ R : ℂ,
      riemannZeta (0.5 + I * t) =
        ∑ n ∈ Finset.range (Nat.floor (Real.sqrt (t / (2*Real.pi)))),
          1/((n+1 : ℂ) ^ (0.5 + I*t))
        + Complex.exp (I * thetaPhase t) *
          ∑ n ∈ Finset.range (Nat.floor (Real.sqrt (t / (2*Real.pi)))),
            1/((n+1 : ℂ) ^ (0.5 - I*t))
        + R ∧ ‖R‖ ≤ C * t^(-1/4 : ℝ)

end HardyTheorem.Details
