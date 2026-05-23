/-
# Gamma函数的留数理论

本文件形式化Gamma函数在负整数点处的留数计算。

## 主要结果

1. Gamma函数在 s = -n (n = 0,1,2,...) 处有简单极点
2. 留数公式：Res(Γ, -n) = (-1)ⁿ / n!

## 数学背景

Gamma函数的极限定义：
Γ(s) = lim_{n→∞} n! nˢ / [s(s+1)...(s+n)]

或者等价地，利用函数方程：
Γ(s) = Γ(s+n+1) / [s(s+1)...(s+n)]

在 s = -n 处的留数可以通过极限计算：
Res(Γ, -n) = lim_{s→-n} (s+n)Γ(s)
           = lim_{s→-n} (s+n)Γ(s+n+1) / [s(s+1)...(s+n)]
           = Γ(1) / [(-n)(-n+1)...(-1)]
           = 1 / [(-1)ⁿ n!]
           = (-1)ⁿ / n!

## 参考
- Whittaker & Watson, "A Course of Modern Analysis"
- Ahlfors, "Complex Analysis"
- Mathlib: Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean
-/

import Mathlib

open Complex Filter Real Topology

namespace GammaResidue

/-! ## Gamma函数的极点性质 -/

/-- Gamma函数在负整数处有简单极点 -/
def IsSimplePoleOfGamma (n : ℕ) : Prop :=
  ∃ f : ℂ → ℂ, AnalyticAt ℂ f (-n : ℂ) ∧ f (-n : ℂ) ≠ 0 ∧
    ∀ s : ℂ, (s + (n : ℂ)) ≠ 0 → Gamma s = f s / (s + n)

/-- Gamma函数在 s = 0 处有简单极点，留数为 1 -/
theorem gamma_residue_at_zero :
    Tendsto (fun s : ℂ ↦ s * Complex.Gamma s) (𝓝[≠] 0) (𝓝 1) := by
  have h_key : ∀ s : ℂ, s ≠ 0 → s * Complex.Gamma s = Complex.Gamma (s + 1) := by
    intro s hs
    rw [Complex.Gamma_add_one s hs]

  have h2 : Tendsto (fun s : ℂ ↦ Complex.Gamma (s + 1)) (𝓝[≠] 0) (𝓝 1) := by
    have h_tendsto : Tendsto (fun s : ℂ ↦ s + 1) (𝓝[≠] 0) (𝓝 1) := by
      have h_cont : Continuous (fun s : ℂ ↦ s + 1) := by continuity
      have h_at_0 : Tendsto (fun s : ℂ ↦ s + 1) (𝓝 0) (𝓝 (0 + 1 : ℂ)) :=
        Continuous.tendsto h_cont 0
      simp at h_at_0
      exact Tendsto.mono_left h_at_0 nhdsWithin_le_nhds

    have h_gamma_cont : ContinuousAt Complex.Gamma 1 := by
      apply Complex.continuousAt_Gamma
      intro m
      have h1 : (1 : ℂ) = (1 : ℝ) + (0 : ℝ) * Complex.I := by simp
      have h2 : -(m : ℂ) = (-(m : ℝ) : ℝ) + (0 : ℝ) * Complex.I := by simp
      rw [h1, h2]
      intro h_eq
      have h_re : (1 : ℝ) = -(m : ℝ) := by
        simpa using congr_arg Complex.re h_eq
      have : m = 0 := by linarith [h_re]
      rw [this] at h_re
      norm_num at h_re

    have h_comp : Tendsto (Complex.Gamma ∘ (fun s : ℂ ↦ s + 1)) (𝓝[≠] 0) (𝓝 (Complex.Gamma 1)) :=
      Tendsto.comp (ContinuousAt.tendsto h_gamma_cont) h_tendsto
    rw [Complex.Gamma_one] at h_comp
    exact h_comp

  apply Tendsto.congr'
  · have h_eq : ∀ s : ℂ, s ≠ 0 → s * Complex.Gamma s = Complex.Gamma (s + 1) := h_key
    rw [EventuallyEq, eventually_nhdsWithin_iff]
    apply Eventually.of_forall
    intro s hs
    have h : s * Complex.Gamma s = Complex.Gamma (s + 1) := h_eq s (by simpa using hs)
    exact h.symm
  · exact h2

/-- Gamma函数在 s = -n 处的留数公式 -/
theorem gamma_residue_at_neg_natural (n : ℕ) :
    Tendsto (fun s : ℂ ↦ (s + n) * Complex.Gamma s) (𝓝[≠] (-n : ℂ))
      (𝓝 ((-1 : ℂ) ^ n / (n.factorial : ℂ))) := by

  induction n with
  | zero =>
    simp [show (-0 : ℂ) = 0 by norm_num, show (0 : ℕ).factorial = 1 by norm_num]
    exact gamma_residue_at_zero
  | succ n ih =>
    have h_eq : ∀ s : ℂ, s ≠ 0 ∧ s ≠ -(n + 1 : ℂ) →
        (s + (n + 1 : ℂ)) * Complex.Gamma s =
        ((s + 1) + (n : ℂ)) * Complex.Gamma (s + 1) / s := by
      intro s hs
      have h1 : s ≠ 0 := hs.1
      have h_gamma : Complex.Gamma s = Complex.Gamma (s + 1) / s := by
        have h_rec : Complex.Gamma (s + 1) = s * Complex.Gamma s :=
          Complex.Gamma_add_one s h1
        rw [h_rec]
        field_simp [h1]
      rw [h_gamma]
      field_simp [h1]
      <;> ring

    have h_rewrite : ∀ s : ℂ, s ≠ 0 ∧ s ≠ -(n + 1 : ℂ) →
        (s + (n + 1 : ℂ)) * Complex.Gamma s =
        ((s + 1) + (n : ℂ)) * Complex.Gamma (s + 1) / s := h_eq

    have h_subst : Tendsto (fun s ↦ (s + (n + 1 : ℂ)) * Complex.Gamma s) (𝓝[≠] (-(n + 1 : ℂ)))
        (𝓝 ((-1 : ℂ) ^ (n + 1) / ((n + 1).factorial : ℂ))) := by
      have h_form : ∀ s : ℂ, s ≠ 0 ∧ s ≠ -(n + 1 : ℂ) →
          (s + (n + 1 : ℂ)) * Complex.Gamma s =
          ((s + 1) + (n : ℂ)) * Complex.Gamma (s + 1) / s := h_eq
      apply Tendsto.congr'
      · have h_eventually_ne0 : ∀ᶠ s in 𝓝[≠] (-(n + 1 : ℂ)), s ≠ 0 := by
          suffices {s : ℂ | s ≠ 0} ∈ 𝓝[≠] (-(n + 1 : ℂ)) by
            simpa using this
          rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
          use Metric.ball (-(n + 1 : ℂ)) (1 / 2)
          constructor
          · exact Metric.ball_mem_nhds (-(n + 1 : ℂ)) (by norm_num)
          · intro s ⟨hs1, hs2⟩
            by_contra h0
            have h_s0 : s = 0 := by simpa using h0
            rw [h_s0] at hs1
            have h1 : dist (0 : ℂ) (-(n + 1 : ℂ)) < (1 / 2 : ℝ) := by
              simpa [Metric.mem_ball] using hs1
            have h2 : dist (0 : ℂ) (-(↑n + 1 : ℂ)) ≥ 1 := by
              have h_eq_dist : dist (0 : ℂ) (-(↑n + 1 : ℂ)) = (↑(n + 1 : ℕ) : ℝ) := by
                calc
                  dist (0 : ℂ) (-(↑n + 1 : ℂ))
                      = ‖(0 : ℂ) - (-(↑n + 1 : ℂ))‖ := by rw [dist_eq_norm]
                  _ = ‖(↑n + 1 : ℂ)‖ := by
                    have : (0 : ℂ) - (-(↑n + 1 : ℂ)) = (↑n + 1 : ℂ) := by ring
                    rw [this]
                  _ = ‖(↑(n + 1 : ℕ) : ℂ)‖ := by
                    have : (↑n + 1 : ℂ) = (↑(n + 1 : ℕ) : ℂ) := by simp
                    rw [this]
                  _ = (↑(n + 1 : ℕ) : ℝ) := by
                    rw [Complex.norm_natCast]
                    exact abs_of_nonneg (Nat.cast_nonneg _)
              rw [h_eq_dist]
              exact_mod_cast show (n + 1 : ℕ) ≥ 1 by linarith [Nat.succ_pos n]
            linarith [h1, h2]
        rw [EventuallyEq, ← eventually_nhdsWithin_iff]
        have h_eventually_ne_neg : ∀ᶠ s in 𝓝[≠] (-(n + 1 : ℂ)), s ≠ -(n + 1 : ℂ) := by
          simp only [nhdsWithin, Set.mem_compl_iff, Set.mem_singleton_iff]
          apply eventually_inf_principal.mpr
          apply Eventually.of_forall
          intro s
          simp
        apply (h_eventually_ne0.and h_eventually_ne_neg).mono
        intro s ⟨hne0, hne_neg⟩
        exact (h_form s ⟨hne0, hne_neg⟩).symm
      · have h_num : Tendsto (fun s ↦ ((s + 1) + (n : ℂ)) * Complex.Gamma (s + 1)) (𝓝[≠] (-(n + 1 : ℂ)))
            (𝓝 ((-1 : ℂ) ^ n / (n.factorial : ℂ))) := by
          have h_map : Tendsto (fun s ↦ s + 1) (𝓝[≠] (-(n + 1 : ℂ))) (𝓝[≠] (-(n : ℂ))) := by
            rw [tendsto_nhdsWithin_iff]
            constructor
            · have h_tendsto : Tendsto (fun s : ℂ ↦ s + 1) (𝓝 (-(n + 1 : ℂ))) (𝓝 (-(n : ℂ))) := by
                have h1 : Tendsto (fun s : ℂ ↦ s + 1) (𝓝 (-(n + 1 : ℂ))) (𝓝 (-(n + 1 : ℂ) + 1)) := by
                  have : (fun s : ℂ ↦ s + 1) = (fun s : ℂ ↦ s + (1 : ℂ)) := by funext s; ring_nf
                  rw [this]
                  apply Tendsto.add_const
                  exact tendsto_id
                have h2 : -(n + 1 : ℂ) + 1 = -(n : ℂ) := by ring
                rw [h2] at h1
                exact h1
              exact tendsto_nhdsWithin_of_tendsto_nhds h_tendsto
            · rw [eventually_nhdsWithin_iff]
              apply Eventually.of_forall
              intro s hs_ne
              intro h_eq
              have : s = -(n + 1 : ℂ) := by
                calc
                  s = (s + 1) - 1 := by ring
                  _ = (-(n : ℂ)) - 1 := by rw [h_eq]
                  _ = -(n + 1 : ℂ) := by ring
              contradiction
          exact Tendsto.comp ih h_map
        have h_den : Tendsto (fun s : ℂ ↦ s) (𝓝[≠] (-(n + 1 : ℂ))) (𝓝 (-(n + 1 : ℂ))) := by
          exact tendsto_nhdsWithin_of_tendsto_nhds (by exact tendsto_id)
        have h_den_ne : -(n + 1 : ℂ) ≠ 0 := by
          have hn1_pos : (n + 1 : ℂ) ≠ 0 := by
            have h_pos : (n + 1 : ℕ) > 0 := Nat.succ_pos n
            exact_mod_cast Nat.ne_of_gt h_pos
          intro h_zero
          have : (n + 1 : ℂ) = 0 := by
            calc
              (n + 1 : ℂ) = -(-(n + 1 : ℂ)) := by ring
              _ = -0 := by rw [h_zero]
              _ = 0 := by ring
          contradiction
        have h_div : Tendsto (fun s ↦ ((s + 1) + (n : ℂ)) * Complex.Gamma (s + 1) / s)
            (𝓝[≠] (-(n + 1 : ℂ)))
            (𝓝 (((-1 : ℂ) ^ n / (n.factorial : ℂ)) / (-(n + 1 : ℂ)))) :=
          h_num.div h_den h_den_ne
        convert h_div using 2
        calc
          (-1 : ℂ) ^ (n + 1) / ((n + 1).factorial : ℂ)
              = (-1 : ℂ) ^ n * (-1) / ((n + 1) * n.factorial : ℂ) := by
                rw [pow_succ, Nat.factorial_succ]
                simp [Nat.cast_mul, Nat.cast_add]
          _ = (-1 : ℂ) ^ n / (↑n.factorial : ℂ) * (-1) / (↑n + 1 : ℂ) := by
                field_simp
                <;> ring
          _ = ((-1 : ℂ) ^ n / (↑n.factorial : ℂ)) / (-(↑n + 1 : ℂ)) := by
                field_simp [h_den_ne]
                <;> ring
    have h_fun : (fun s : ℂ ↦ (s + (↑n + 1 : ℂ)) * Complex.Gamma s) = (fun s : ℂ ↦ (s + (↑(n + 1) : ℂ)) * Complex.Gamma s) := by
      funext s
      simp [Nat.cast_add]
    have h_nhds : 𝓝[≠] (-((↑n + 1) : ℂ)) = 𝓝[≠] (-(↑(n + 1) : ℂ)) := by
      simp [Nat.cast_add]
    rw [h_fun, h_nhds] at h_subst
    exact h_subst

/-! ## 辅助引理 -/

/-- Gamma(1) = 1 -/
lemma gamma_one : Complex.Gamma 1 = 1 := Complex.Gamma_one

/-- Gamma(s+1) = s * Gamma(s) (递推公式) -/
lemma gamma_recurrence (s : ℂ) (hs : s ≠ 0) :
    Complex.Gamma (s + 1) = s * Complex.Gamma s := by
  rw [Complex.Gamma_add_one s hs]

end GammaResidue

/-! ## 数值验证的参考实现

以下引理对应数值验证的结果，确保形式化与计算一致。

### 验证点：
- n = 0: s = 0, 留数 = 1 = (-1)⁰ / 0!
- n = 1: s = -1, 留数 = -1 = (-1)¹ / 1!
- n = 2: s = -2, 留数 = 1/2 = (-1)² / 2!
- n = 3: s = -3, 留数 = -1/6 = (-1)³ / 3!
-/

namespace NumericalVerification

open GammaResidue

theorem residue_at_zero_eq_one :
    Tendsto (fun s : ℂ ↦ s * Gamma s) (𝓝[≠] 0) (𝓝 1) :=
  gamma_residue_at_zero

theorem residue_at_minus_one_eq_minus_one :
    Tendsto (fun s : ℂ ↦ (s + 1) * Complex.Gamma s) (𝓝[≠] (-1 : ℂ)) (𝓝 (-1 : ℂ)) := by
  have h := gamma_residue_at_neg_natural 1
  norm_num at h ⊢
  exact h

theorem residue_at_minus_two_eq_half :
    Tendsto (fun s : ℂ ↦ (s + 2) * Gamma s) (𝓝[≠] (-2 : ℂ)) (𝓝 (1 / 2 : ℂ)) := by
  have h := gamma_residue_at_neg_natural 2
  norm_num at h ⊢
  exact h

end NumericalVerification
