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
      simpa using Complex.tendsto_self_mul_Gamma_nhds_zero
  | succ n ih =>
      let a : ℂ := (-(n.succ : ℂ))
      have ha0 : a ≠ 0 := by
        simpa [a] using
          (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr n.succ_ne_zero) :
            (-(n.succ : ℂ)) ≠ 0)
      have h_add : Tendsto (fun s : ℂ => s + 1) (𝓝[≠] a) (𝓝[≠] (-n : ℂ)) := by
        have ha : a + 1 = (-n : ℂ) := by
          simp [a, Nat.cast_succ]
        rw [← ha]
        exact (show Tendsto (fun s : ℂ => s + 1) (𝓝[≠] a) (𝓝[≠] (a + 1)) from by
          refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
          · exact (((continuousAt_id.add continuousAt_const).tendsto).mono_left
              nhdsWithin_le_nhds)
          · filter_upwards [self_mem_nhdsWithin] with s hs
            intro h
            exact hs (add_right_cancel h))
      have h_shift : Tendsto (fun s : ℂ ↦ ((s + 1) + n) * Complex.Gamma (s + 1))
          (𝓝[≠] a) (𝓝 ((-1 : ℂ) ^ n / (n.factorial : ℂ))) := by
        simpa [Function.comp_def, add_assoc, add_comm, add_left_comm] using ih.comp h_add
      have h_inv : Tendsto (fun s : ℂ ↦ s⁻¹) (𝓝[≠] a) (𝓝 a⁻¹) := by
        exact ((continuousAt_inv₀ ha0).tendsto).mono_left nhdsWithin_le_nhds
      have h_prod := h_shift.mul h_inv
      have h_event : (fun s : ℂ ↦ (s + n.succ) * Complex.Gamma s) =ᶠ[𝓝[≠] a]
          (fun s : ℂ ↦ (((s + 1) + n) * Complex.Gamma (s + 1)) * s⁻¹) := by
        filter_upwards [eventually_ne_nhdsWithin ha0] with s hs0
        have hgamma : Complex.Gamma (s + 1) = s * Complex.Gamma s :=
          Complex.Gamma_add_one s hs0
        have hmul (A G z : ℂ) (hz : z ≠ 0) : A * G = (A * (z * G)) * z⁻¹ := by
          calc
            A * G = (A * G) * (z * z⁻¹) := by rw [mul_inv_cancel₀ hz, mul_one]
            _ = (A * (z * G)) * z⁻¹ := by ring_nf
        have hcoef : s + (n.succ : ℂ) = (s + 1) + n := by
          simp [Nat.cast_succ]
          ring
        calc
          (s + n.succ) * Complex.Gamma s
              = ((s + 1) + n) * Complex.Gamma s := by rw [hcoef]
          _ = (((s + 1) + n) * Complex.Gamma (s + 1)) * s⁻¹ := by
              have h := hmul ((s + 1) + n) (Complex.Gamma s) s hs0
              rw [← hgamma] at h
              exact h
      have h_target : ((-1 : ℂ) ^ n / (n.factorial : ℂ)) * a⁻¹ =
          ((-1 : ℂ) ^ n.succ / (n.succ.factorial : ℂ)) := by
        dsimp [a]
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ]
        field_simp [Nat.cast_ne_zero.mpr n.succ_ne_zero,
          Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)]
      have h_final : Tendsto (fun s : ℂ ↦ (s + n.succ) * Complex.Gamma s)
          (𝓝[≠] a) (𝓝 ((-1 : ℂ) ^ n.succ / (n.succ.factorial : ℂ))) := by
        exact Tendsto.congr' h_event.symm (by simpa [h_target] using h_prod)
      simpa [a] using h_final

/-! ## 辅助引理 -/

lemma gamma_residue_value_ne_zero (n : ℕ) :
    ((-1 : ℂ) ^ n / (n.factorial : ℂ)) ≠ 0 := by
  exact div_ne_zero (pow_ne_zero n (by norm_num)) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))

/-- Gamma(1) = 1 -/
lemma gamma_one : Complex.Gamma 1 = 1 := Complex.Gamma_one

/-- Gamma(s+1) = s * Gamma(s) (递推公式) -/
lemma gamma_recurrence (s : ℂ) (hs : s ≠ 0) :
    Complex.Gamma (s + 1) = s * Complex.Gamma s := by
  rw [Complex.Gamma_add_one s hs]

/-- Gamma函数在负整数处有简单极点 -/
theorem IsSimplePoleOfGamma (n : ℕ) :
    ∃ f : ℂ → ℂ, AnalyticAt ℂ f (-n : ℂ) ∧ f (-n : ℂ) ≠ 0 ∧
      ∀ s : ℂ, (s + (n : ℂ)) ≠ 0 → Complex.Gamma s = f s / (s + n) := by
  let c : ℂ := (-n : ℂ)
  let R : ℂ := (-1 : ℂ) ^ n / (n.factorial : ℂ)
  let g : ℂ → ℂ := fun s ↦ (s + n) * Complex.Gamma s
  have hga_event_ana : ∀ᶠ z in nhdsWithin c ({c}ᶜ), AnalyticAt ℂ Complex.Gamma z := by
    simpa [c, Set.compl_eq_univ_diff] using
      (MeromorphicOn.Gamma (s := (Set.univ : Set ℂ)).eventually_analyticAt (by simp))
  have hg_event_diff : ∀ᶠ z in nhdsWithin c ({c}ᶜ), DifferentiableAt ℂ g z := by
    refine hga_event_ana.mono ?_
    intro z hz
    have hdz : DifferentiableAt ℂ (fun t : ℂ ↦ t + (n : ℂ)) z := by
      simpa using
        (differentiableAt_id.add
          (differentiableAt_const : DifferentiableAt ℂ (fun _ : ℂ => (n : ℂ))))
    have hgz : DifferentiableAt ℂ (fun t : ℂ ↦ (t + (n : ℂ)) * Complex.Gamma t) z := by
      simpa using (hdz.mul hz.differentiableAt)
    simpa [g, mul_comm, mul_left_comm, mul_assoc] using hgz
  have hne : ∀ᶠ z in nhdsWithin c ({c}ᶜ), z ≠ c := by
    simpa [Filter.Eventually, Set.mem_setOf_eq] using
      (self_mem_nhdsWithin : ({c}ᶜ : Set ℂ) ∈ nhdsWithin c ({c}ᶜ))
  have hg_update_event : ∀ᶠ z in nhdsWithin c ({c}ᶜ), DifferentiableAt ℂ (Function.update g c R) z := by
    refine (hg_event_diff.and hne).mono ?_
    intro z hz
    rcases hz with ⟨hgd, hzc⟩
    have hEq : (Function.update g c R) =ᶠ[𝓝 z] g := by
      filter_upwards [isOpen_ne.mem_nhds hzc] with x hx
      exact Function.update_of_ne hx R g
    exact hgd.congr_of_eventuallyEq hEq
  have hlim : Tendsto g (𝓝[≠] c) (𝓝 R) := by
    simpa [g, c] using (gamma_residue_at_neg_natural n)
  have hcont : ContinuousAt (Function.update g c R) c := (continuousAt_update_same.2 hlim)
  have h_analytic : AnalyticAt ℂ (Function.update g c R) c :=
    Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hg_update_event hcont
  refine ⟨Function.update g c R, h_analytic, ?_, ?_⟩
  ·
    have hpow : ((-1 : ℂ) ^ n) ≠ 0 := by
      exact pow_ne_zero n (by norm_num : (-1 : ℂ) ≠ 0)
    have hfac : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    simpa [Function.update, c, R] using (div_ne_zero hpow hfac)
  · intro s hs
    have hs' : s ≠ c := by
      exact fun hsc =>
        hs (by
          simp [c, hsc] )
    have hrewrite : Complex.Gamma s = ((s + (n : ℂ)) * Complex.Gamma s) / (s + (n : ℂ)) := by
      field_simp [hs]
    calc
      Complex.Gamma s = ((s + (n : ℂ)) * Complex.Gamma s) / (s + (n : ℂ)) := hrewrite
      _ = Function.update g c R s / (s + (n : ℂ)) := by
        rw [Function.update_of_ne hs']

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
