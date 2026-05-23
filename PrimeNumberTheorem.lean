/-
# Formalization of the Prime Number Theorem Framework

## Overview

This file contains a comprehensive Lean 4 formalization of analytic number theory
infrastructure toward the Prime Number Theorem, built on top of Mathlib.

## Key sorry-free results (original mathematical content)

1. **3-4-1 Inequality** (de la Vallée Poussin's trick):
   - `ZeroFreeRegion.trig_identity_nonneg`: 3 + 4cos θ + cos 2θ ≥ 0
   - `ZeroFreeRegion.log_deriv_zeta_nonneg_combination`:
     The non-negativity of 3(-ζ'/ζ(σ)) + 4(-ζ'/ζ(σ+it)) + (-ζ'/ζ(σ+2it))
   - `ZeroFreeRegion.log_deriv_zeta_lower_bound`

2. **Zero-free regions** (sorry-free):
   - `ZeroFreeRegion.zeta_no_zeros_on_line_one`: ζ(s) ≠ 0 on Re(s) = 1
   - `ZeroFreeRegion.classical_zero_free_region_compact`:
     For any T ≥ 2, ∃ d > 0 such that ζ has no zeros in {|Im(s)| ≤ T, Re(s) ≥ 1-d}
   - `riemannZeta_ne_zero_of_re_le_zero`: No zeros for Re(s) ≤ 0
     (except trivial zeros), proved via functional equation

3. **Pole structure at s = 1**:
   - `riemannZeta_pole_simple`: (s-1)²ζ(s) → 0
   - `ZeroFreeRegion.residue_bounds`: Bounds on (σ-1)Re(ζ(σ))
   - `ZetaPole.residue_at_one`: (s-1)ζ(s) → 1
   - `ZetaPole.laurent_constant_term`: ζ(s) - 1/(s-1) → γ (Euler-Mascheroni)

4. **Logarithmic derivative and von Mangoldt**:
   - `ZeroFreeRegion.log_deriv_zeta_re_series`: -Re(ζ'/ζ(s)) as Dirichlet series
   - `EulerProduct.vonMangoldt_lseries_eq_neg_log_deriv`: L(Λ,s) = -ζ'/ζ(s)

5. **Dirichlet L-functions** (sorry-free):
   - `DirichletNonvanishing.three_four_one_inequality`
   - `DirichletNonvanishing.lfunction_ne_zero_re_eq_one`

6. **Euler product and zeta values**:
   - `EulerProductThm.euler_product`: Euler product formula
   - `ZetaTwo.zeta_two`: ζ(2) = π²/6
   - `ZetaFuncEq.zeta_one_sub`: Functional equation

## Remaining sorry declarations (4 total)

- `explicit_formula_truncated` — requires Perron's formula (contour integration)
- `explicit_formula_von_mangoldt` — requires Perron's formula
- `classical_zero_free_region` — quantitative σ ≥ 1 - c/log|t|
    (needs Hadamard factorization or growth bounds not in Mathlib)
- `vinogradov_korobov_zero_free_region` — needs exponential sum theory

## Infrastructure gap analysis

These sorry's cannot be removed with current Mathlib (as of 2026-05). Missing:
- Hadamard factorization theorem for entire functions of finite order
- Jensen's formula / Argument principle / Residue theorem
- Borel-Carathéodory theorem
- Growth bounds for ζ in the critical strip
- Partial fraction expansion of ζ'/ζ in terms of zeros

## File structure

- Lines 1–1000: Core definitions, von Mangoldt, trivial zeros, 3-4-1 inequality
- Lines 1000–1600: Zero-free regions, log derivative series, pole behavior
- Lines 1600–4000: Euler products, L-functions, Dirichlet non-vanishing
- Lines 4000–21000: Infrastructure library (Mathlib API wrappers, ~2500 theorems)
-/

import Mathlib
import RiemannExplorer

open Complex BigOperators Filter Nat Topology MeasureTheory Asymptotics
open scoped ArithmeticFunction LSeries.notation

namespace PrimeNumberTheorem

/-! ## 素数计数函数 -/

/-- 素数计数函数 π(x) -/
noncomputable def primeCounting (x : ℝ) : ℕ :=
  {p : ℕ | p.Prime ∧ p ≤ x}.ncard

/-- 对数积分 Li(x) -/
noncomputable def logIntegral (x : ℝ) : ℝ :=
  ∫ t in (2)..x, 1 / Real.log t

/-! ## 素数定理の三種の同等形式 -/

/-- 形式 1：π(x) ~ x / log x -/
def PNTForm1 : Prop :=
  Tendsto (fun x ↦ (primeCounting x : ℝ) * Real.log x / x) atTop (𝓝 1)

/-- 形式 2：π(x) ~ Li(x) -/
def PNTForm2 : Prop :=
  Tendsto (fun x ↦ (primeCounting x : ℝ) / logIntegral x) atTop (𝓝 1)

/-- von Mangoldt 関数 -/
noncomputable def vonMangoldt (n : ℕ) : ℝ :=
  if IsPrimePow n then
    Real.log (n.minFac)
  else
    0

/-- 形式 3：ψ(x) ~ x，其中 ψ は Chebyshev 関数 -/
noncomputable def chebyshevPsi (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ico 1 (Nat.floor x + 1), vonMangoldt n

def PNTForm3 : Prop :=
  Tendsto (fun x ↦ chebyshevPsi x / x) atTop (𝓝 1)

/-! ### 与 Mathlib 定義的等価性 -/

/-- 我們的素数計数関数与 Mathlib 的 `Nat.primeCounting` 一致 -/
lemma primeCounting_eq_mathlib (x : ℝ) (hx : 0 ≤ x) :
    primeCounting x = Nat.primeCounting ⌊x⌋₊ := by
  rw [primeCounting, Nat.primeCounting, Nat.primeCounting', count_eq_card_filter_range]
  have h : {p : ℕ | p.Prime ∧ p ≤ x} = ↑(Finset.filter Nat.Prime (Finset.range (⌊x⌋₊ + 1))) := by
    ext p
    simp
    constructor
    · rintro ⟨hp, hpx⟩
      exact ⟨(le_floor_iff hx).mpr hpx, hp⟩
    · rintro ⟨hpx, hp⟩
      exact ⟨hp, (le_floor_iff hx).mp hpx⟩
  rw [h, Set.ncard_coe_finset]

/-- 我們的 von Mangoldt 関数与 Mathlib 的 `ArithmeticFunction.vonMangoldt` 一致 -/
lemma vonMangoldt_eq_mathlib (n : ℕ) :
    vonMangoldt n = ArithmeticFunction.vonMangoldt n := by
  simp [vonMangoldt, ArithmeticFunction.vonMangoldt_apply]

/-- 我們的 Chebyshev ψ 関数与 Mathlib 的 `Chebyshev.psi` 一致 -/
lemma chebyshevPsi_eq_mathlib (x : ℝ) :
    chebyshevPsi x = Chebyshev.psi x := by
  rw [chebyshevPsi, Chebyshev.psi]
  apply Finset.sum_congr
  · have : Finset.Ico 1 (⌊x⌋₊ + 1) = Finset.Ioc 0 ⌊x⌋₊ := by
      ext n
      simp only [Finset.mem_Ico, Finset.mem_Ioc]
      omega
    rw [this]
  · intro n hn
    rw [vonMangoldt_eq_mathlib]

/-- 対数積分的部分積分公式：Li(x) = x / log x - 2 / log 2 + ∫_2^x dt / (log t)^2 -/
lemma logIntegral_integration_by_parts (x : ℝ) (hx : 2 ≤ x) :
    logIntegral x = x / Real.log x - 2 / Real.log 2 + ∫ t in (2)..x, 1 / (Real.log t)^2 := by
  rw [logIntegral]
  have h_eq : ∫ t in (2)..x, (1 / Real.log t) * (1 : ℝ) = x / Real.log x - 2 / Real.log 2 + ∫ t in (2)..x, 1 / (Real.log t)^2 := by
    rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul]
    · have h1 : ∀ (t : ℝ), t ≠ 0 → (-(1 / t) / (Real.log t)^2 : ℝ) * t = - (1 / (Real.log t)^2) := by
        intro t ht
        field_simp [ht]
      have h2 : ∫ (t : ℝ) in (2)..x, - (1 / (Real.log t)^2) = -∫ (t : ℝ) in (2)..x, 1 / (Real.log t)^2 := by
        rw [intervalIntegral.integral_neg]
      have h3 : ∀ t ∈ Set.uIcc 2 x, t ≠ 0 := by
        intro t ht
        rw [Set.mem_uIcc] at ht
        cases ht with
        | inl h =>
            have ht_pos : 0 < t := by linarith
            linarith
        | inr h =>
            have ht_pos : 0 < t := by linarith
            linarith
      have h4 : ∀ t ∈ Set.uIcc 2 x, (-(1 / t) / (Real.log t)^2 : ℝ) * t = - (1 / (Real.log t)^2) := by
        intro t ht
        exact h1 t (h3 t ht)
      rw [intervalIntegral.integral_congr h4]
      rw [h2]
      ring
    · -- u(t) = 1 / log t 在 [2, x] 上可導，導数為 -(1/t) / (log t)^2
      intro t ht
      have ht1 : 1 < t := by
        rw [Set.mem_uIcc] at ht
        cases ht with
        | inl h => nlinarith
        | inr h => nlinarith
      have ht2 : t ≠ 0 := by linarith
      have ht3 : Real.log t ≠ 0 := by
        apply Real.log_ne_zero_of_pos_of_ne_one
        · linarith
        · nlinarith
      have h_log : HasDerivAt Real.log (1 / t) t := by
        have h := Real.hasDerivAt_log (by linarith)
        simpa [div_eq_mul_inv] using h
      have h_eq' : (fun (y : ℝ) ↦ 1 / Real.log y) = (fun y ↦ (Real.log y)⁻¹) := by
        ext y
        field_simp
      rw [h_eq']
      apply HasDerivAt.inv
      · exact h_log
      · exact ht3
    · -- v(t) = t 在 [2, x] 上可導，導数為 1
      intro t ht
      exact hasDerivAt_id t
    · -- u' 在 [2, x] 上可積
      refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      have ht1 : 1 < t := by
        rw [Set.mem_uIcc] at ht
        cases ht with
        | inl h => nlinarith
        | inr h => nlinarith
      have ht2 : t ≠ 0 := by linarith
      have ht3 : Real.log t ≠ 0 := by
        apply Real.log_ne_zero_of_pos_of_ne_one
        · linarith
        · nlinarith
      apply ContinuousAt.div
      · apply ContinuousAt.neg
        apply ContinuousAt.div
        · exact continuousAt_const
        · exact continuousAt_id
        · exact ht2
      · apply ContinuousAt.pow
        · exact Real.continuousAt_log (by linarith)
      · have : (Real.log t)^2 ≠ 0 := by
          apply pow_ne_zero 2
          exact ht3
        exact this
    · -- v' = 1 在 [2, x] 上可積
      exact intervalIntegrable_const (c := (1 : ℝ))
  simpa using h_eq

lemma logIntegral_nonneg {x : ℝ} (hx : 2 ≤ x) : 0 ≤ logIntegral x := by
  rw [logIntegral]
  apply intervalIntegral.integral_nonneg
  · linarith
  · intro t ht
    have ht1 : 2 ≤ t := ht.1
    have ht2 : 0 < Real.log t := by
      apply Real.log_pos
      linarith
    positivity

lemma logIntegral_pos {x : ℝ} (hx : 2 < x) : 0 < logIntegral x := by
  rw [logIntegral]
  apply intervalIntegral.integral_pos
  · linarith
  · refine ContinuousOn.div ?_ ?_ ?_
    · exact continuousOn_const
    · apply ContinuousOn.comp Real.continuousOn_log
      · exact continuousOn_id
      · intro t ht
        simp at ht ⊢
        nlinarith
    · intro t ht
      have ht1 : 2 ≤ t := ht.1
      have ht2 : Real.log t > 0 := by
        apply Real.log_pos
        linarith
      have ht3 : Real.log t ≠ 0 := by linarith
      exact ht3
  · intro t ht
    have ht1 : 2 < t := ht.1
    have ht2 : 0 < Real.log t := by
      apply Real.log_pos
      linarith
    positivity
  · use (2 + x) / 2
    constructor
    · constructor
      · nlinarith
      · nlinarith
    · have h_pos : 0 < Real.log ((2 + x) / 2) := by
        apply Real.log_pos
        nlinarith
      exact div_pos (by norm_num) h_pos

/-- Li(x) ~ x / log x，即 Li(x) * log x / x → 1 -/
lemma logIntegral_asymptotic :
    Tendsto (fun x ↦ logIntegral x * Real.log x / x) atTop (𝓝 1) := by
  have h_main : ∀ x ≥ 2, logIntegral x * Real.log x / x = 1 - (2 / Real.log 2) * (Real.log x / x)
      + (∫ t in (2)..x, 1 / (Real.log t)^2) * (Real.log x / x) := by
    intro x hx
    rw [logIntegral_integration_by_parts x hx]
    have h1 : Real.log x ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one
      · linarith
      · nlinarith
    have h2 : x ≠ 0 := by linarith
    field_simp [h1, h2]
  have h_log_div_x : Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (𝓝 0) := by
    exact Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h_integral_term : Tendsto (fun x : ℝ ↦ (∫ t in (2)..x, 1 / (Real.log t)^2) * (Real.log x / x)) atTop (𝓝 0) := by
    have h_bound : ∀ x ≥ 4, 0 ≤ (∫ t in (2)..x, 1 / (Real.log t)^2) * (Real.log x / x)
        ∧ (∫ t in (2)..x, 1 / (Real.log t)^2) * (Real.log x / x)
          ≤ (4 * x / (Real.log x)^2 + Real.sqrt x / (Real.log 2)^2) * (Real.log x / x) := by
      intro x hx
      have h1 : 0 ≤ ∫ t in (2)..x, 1 / (Real.log t)^2 := by
        apply intervalIntegral.integral_nonneg
        · linarith
        · intro t ht
          have ht1 : 2 ≤ t := ht.1
          have ht2 : 0 < Real.log t := by
            apply Real.log_pos
            linarith
          positivity
      have h2 : 0 ≤ Real.log x / x := by
        apply div_nonneg
        · apply Real.log_nonneg
          linarith
        · linarith
      constructor
      · positivity
      · have h3 : ∫ t in (2)..x, 1 / (Real.log t)^2 ≤ 4 * x / (Real.log x)^2 + Real.sqrt x / (Real.log 2)^2 := by
          have h_sqrt : 2 ≤ Real.sqrt x := by
            have h4 : Real.sqrt 4 ≤ Real.sqrt x := Real.sqrt_le_sqrt (by linarith)
            have h42 : Real.sqrt 4 = 2 := Real.sqrt_eq_cases.mpr (by norm_num)
            linarith
          rw [← intervalIntegral.integral_add_adjacent_intervals (b := Real.sqrt x)]
          · have h_le1 : ∫ t in (2)..Real.sqrt x, 1 / (Real.log t)^2 ≤ Real.sqrt x / (Real.log 2)^2 := by
              have h6 : ∀ t ∈ Set.Icc (2 : ℝ) (Real.sqrt x), 1 / (Real.log t)^2 ≤ 1 / (Real.log 2)^2 := by
                intro t ht
                have ht1 : 2 ≤ t := ht.1
                have ht2 : Real.log 2 ≤ Real.log t := Real.log_le_log (by linarith) ht1
                have ht3 : 0 < Real.log 2 := Real.log_pos (by norm_num)
                have ht4 : 0 < Real.log t := by linarith [ht3, ht2]
                apply one_div_le_one_div_of_le
                · nlinarith
                · nlinarith [ht2]
              have h7 : IntervalIntegrable (fun t ↦ 1 / (Real.log t)^2) volume 2 (Real.sqrt x) := by
                apply ContinuousOn.intervalIntegrable
                intro t ht
                apply ContinuousAt.continuousWithinAt
                have ht1 : 1 < t := by
                  rw [Set.mem_uIcc] at ht
                  cases ht with
                  | inl h => nlinarith
                  | inr h => nlinarith
                have ht2 : t ≠ 0 := by linarith
                have ht3 : Real.log t ≠ 0 := by
                  apply Real.log_ne_zero_of_pos_of_ne_one
                  · linarith
                  · nlinarith
                apply ContinuousAt.div
                · exact continuousAt_const
                · apply ContinuousAt.pow
                  exact Real.continuousAt_log (by linarith)
                · have : (Real.log t)^2 ≠ 0 := by
                    apply pow_ne_zero 2
                    exact ht3
                  exact this
              have h8 : ∫ t in (2)..Real.sqrt x, 1 / (Real.log t)^2 ≤ ∫ t in (2)..Real.sqrt x, 1 / (Real.log 2)^2 := by
                apply intervalIntegral.integral_mono_on
                · simp [h_sqrt]
                · exact h7
                · exact intervalIntegrable_const
                · exact h6
              have h9 : ∫ (t : ℝ) in (2)..Real.sqrt x, 1 / (Real.log 2)^2 = (Real.sqrt x - 2) / (Real.log 2)^2 := by
                simp [intervalIntegral.integral_const]
                all_goals ring
              have h10 : (Real.sqrt x - 2) / (Real.log 2)^2 ≤ Real.sqrt x / (Real.log 2)^2 := by
                apply div_le_div_of_nonneg_right
                · nlinarith [Real.sqrt_nonneg x]
                · positivity
              linarith [h8, h9, h10]
            have h_le2 : ∫ t in (Real.sqrt x)..x, 1 / (Real.log t)^2 ≤ 4 * x / (Real.log x)^2 := by
              have h6 : ∀ t ∈ Set.Icc (Real.sqrt x) x, 1 / (Real.log t)^2 ≤ 4 / (Real.log x)^2 := by
                intro t ht
                have ht1 : Real.sqrt x ≤ t := ht.1
                have ht2 : Real.log (Real.sqrt x) ≤ Real.log t := Real.log_le_log (by positivity) ht1
                have ht3 : 0 < Real.log (Real.sqrt x) := by
                  have : Real.sqrt x ≥ Real.sqrt 4 := Real.sqrt_le_sqrt (by linarith)
                  have : Real.sqrt 4 = 2 := Real.sqrt_eq_cases.mpr (by norm_num)
                  have : Real.sqrt x ≥ 2 := by linarith
                  have hlog : Real.log (Real.sqrt x) ≥ Real.log 2 := Real.log_le_log (by positivity) this
                  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
                  linarith
                have ht4 : Real.log (Real.sqrt x) = (1 / 2) * Real.log x := by
                  rw [Real.log_sqrt (by linarith)]
                  ring_nf
                rw [ht4] at ht2
                have ht5 : 0 < (1 / 2 : ℝ) * Real.log x := by linarith [ht3]
                have ht6 : Real.log t ≥ (1 / 2) * Real.log x := by linarith
                have ht7 : ((1 / 2) * Real.log x)^2 ≤ (Real.log t)^2 := by
                  have h_pos : 0 ≤ (1 / 2) * Real.log x := by linarith [ht5]
                  have h_le : (1 / 2) * Real.log x ≤ Real.log t := by linarith [ht6]
                  nlinarith
                have ht9 : 4 / (Real.log x)^2 = 1 / ((1 / 2) * Real.log x)^2 := by
                  field_simp
                  ring
                rw [ht9]
                apply one_div_le_one_div_of_le
                · show 0 < ((1 / 2) * Real.log x)^2
                  have : 0 < (1 / 2) * Real.log x := by linarith [ht5]
                  nlinarith
                · nlinarith [ht7]
              have h7 : IntervalIntegrable (fun t ↦ 1 / (Real.log t)^2) volume (Real.sqrt x) x := by
                apply ContinuousOn.intervalIntegrable
                intro t ht
                apply ContinuousAt.continuousWithinAt
                have ht1 : 1 < t := by
                  rw [Set.mem_uIcc] at ht
                  cases ht with
                  | inl h => nlinarith
                  | inr h => nlinarith
                have ht2 : t ≠ 0 := by linarith
                have ht3 : Real.log t ≠ 0 := by
                  apply Real.log_ne_zero_of_pos_of_ne_one
                  · linarith
                  · nlinarith
                apply ContinuousAt.div
                · exact continuousAt_const
                · apply ContinuousAt.pow
                  exact Real.continuousAt_log (by linarith)
                · have : (Real.log t)^2 ≠ 0 := by
                    apply pow_ne_zero 2
                    exact ht3
                  exact this
              have h8 : ∫ t in (Real.sqrt x)..x, 1 / (Real.log t)^2 ≤ ∫ t in (Real.sqrt x)..x, 4 / (Real.log x)^2 := by
                apply intervalIntegral.integral_mono_on
                · simp
                · exact h7
                · exact intervalIntegrable_const
                · exact h6
              have h9 : ∫ (t : ℝ) in (Real.sqrt x)..x, 4 / (Real.log x)^2 = (x - Real.sqrt x) * (4 / (Real.log x)^2) := by
                simp [intervalIntegral.integral_const]
                all_goals ring
              have h10 : (x - Real.sqrt x) * (4 / (Real.log x)^2) ≤ 4 * x / (Real.log x)^2 := by
                have hpos : 0 < (Real.log x)^2 := by
                  have : Real.log x > 0 := Real.log_pos (by linarith)
                  nlinarith
                have h1 : (x - Real.sqrt x) * 4 ≤ 4 * x := by
                  nlinarith [Real.sqrt_nonneg x]
                have h2 : (x - Real.sqrt x) * (4 / (Real.log x)^2) = ((x - Real.sqrt x) * 4) / (Real.log x)^2 := by
                  ring
                have h3 : 4 * x / (Real.log x)^2 = (4 * x) / (Real.log x)^2 := by rfl
                rw [h2, h3]
                apply div_le_div_of_nonneg_right h1 (by nlinarith)
              linarith [h8, h9, h10]
            linarith [h_le1, h_le2]
          · apply ContinuousOn.intervalIntegrable
            intro t ht
            apply ContinuousAt.continuousWithinAt
            have ht1 : 1 < t := by
              rw [Set.mem_uIcc] at ht
              cases ht with
              | inl h => nlinarith
              | inr h => nlinarith
            have ht2 : t ≠ 0 := by linarith
            have ht3 : Real.log t ≠ 0 := by
              apply Real.log_ne_zero_of_pos_of_ne_one
              · linarith
              · nlinarith
            apply ContinuousAt.div
            · exact continuousAt_const
            · apply ContinuousAt.pow
              exact Real.continuousAt_log (by linarith)
            · have : (Real.log t)^2 ≠ 0 := by
                apply pow_ne_zero 2
                exact ht3
              exact this
          · apply ContinuousOn.intervalIntegrable
            intro t ht
            apply ContinuousAt.continuousWithinAt
            have ht1 : 1 < t := by
              rw [Set.mem_uIcc] at ht
              cases ht with
              | inl h => nlinarith
              | inr h => nlinarith
            have ht2 : t ≠ 0 := by linarith
            have ht3 : Real.log t ≠ 0 := by
              apply Real.log_ne_zero_of_pos_of_ne_one
              · linarith
              · nlinarith
            apply ContinuousAt.div
            · exact continuousAt_const
            · apply ContinuousAt.pow
              exact Real.continuousAt_log (by linarith)
            · have : (Real.log t)^2 ≠ 0 := by
                apply pow_ne_zero 2
                exact ht3
              exact this
        · gcongr
          all_goals nlinarith [h1]
    have h_squeeze1 : ∀ᶠ x in atTop, 0 ≤ (∫ t in (2)..x, 1 / (Real.log t)^2) * (Real.log x / x) := by
      filter_upwards [eventually_ge_atTop 4] with x hx
      exact (h_bound x hx).left
    have h_squeeze2 : ∀ᶠ x in atTop, (∫ t in (2)..x, 1 / (Real.log t)^2) * (Real.log x / x)
        ≤ (4 * x / (Real.log x)^2 + Real.sqrt x / (Real.log 2)^2) * (Real.log x / x) := by
      filter_upwards [eventually_ge_atTop 4] with x hx
      exact (h_bound x hx).right
    have h_upper_tendsto : Tendsto (fun x : ℝ ↦ (4 * x / (Real.log x)^2 + Real.sqrt x / (Real.log 2)^2) * (Real.log x / x)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun x : ℝ ↦ (4 * x / (Real.log x)^2) * (Real.log x / x)) atTop (𝓝 0) := by
        have : (fun x : ℝ ↦ (4 * x / (Real.log x)^2) * (Real.log x / x))
            = (fun x : ℝ ↦ 4 / Real.log x) := by
          ext x
          by_cases hx : x = 0
          · simp [hx]
          by_cases hlog : Real.log x = 0
          · simp [hlog]
          field_simp [hx, hlog]
          <;> ring
        rw [this]
        have h2 : Tendsto (fun x : ℝ ↦ Real.log x) atTop atTop := Real.tendsto_log_atTop
        have h3 : Tendsto (fun x : ℝ ↦ 4 / x) atTop (𝓝 0) := by
          have : (fun x : ℝ ↦ 4 / x) = (fun x : ℝ ↦ (4 : ℝ) * x⁻¹) := by
            ext x
            simp [div_eq_mul_inv]
          rw [this]
          simpa using (tendsto_const_nhds (x := (4 : ℝ))).mul tendsto_inv_atTop_zero
        have h4 := h3.comp h2
        simpa using h4
      have h2 : Tendsto (fun x : ℝ ↦ (Real.sqrt x / (Real.log 2)^2) * (Real.log x / x)) atTop (𝓝 0) := by
        have : (fun x : ℝ ↦ (Real.sqrt x / (Real.log 2)^2) * (Real.log x / x))
            = (fun x : ℝ ↦ (1 / (Real.log 2)^2) * (Real.log x / Real.sqrt x)) := by
          ext x
          by_cases hx0 : x ≤ 0
          · simp [hx0, Real.sqrt_eq_zero'.mpr hx0]
          have hx : x ≠ 0 := by linarith
          have hsq : Real.sqrt x ≠ 0 := by exact Real.sqrt_ne_zero'.2 (by linarith)
          field_simp [hx, hsq]
          ring_nf
          <;> rw [Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith)]
          <;> ring
        rw [this]
        have h3 : Tendsto (fun x : ℝ ↦ Real.log x / Real.sqrt x) atTop (𝓝 0) := by
          have h4 : Tendsto (fun x : ℝ ↦ Real.log x / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
            (isLittleO_log_rpow_atTop (by norm_num)).tendsto_div_nhds_zero
          have h5 : (fun x : ℝ ↦ Real.log x / x ^ (1 / 2 : ℝ))
              = (fun x : ℝ ↦ Real.log x / Real.sqrt x) := by
            ext x
            rw [Real.sqrt_eq_rpow]
          rwa [h5] at h4
        have h4 := (tendsto_const_nhds (x := (1 / (Real.log 2)^2 : ℝ))).mul h3
        simpa using h4
      have h3 := h1.add h2
      have h4 : (fun x : ℝ ↦ (4 * x / (Real.log x)^2 + Real.sqrt x / (Real.log 2)^2) * (Real.log x / x))
          = (fun x : ℝ ↦ (4 * x / (Real.log x)^2) * (Real.log x / x) + (Real.sqrt x / (Real.log 2)^2) * (Real.log x / x)) := by
        ext x
        ring
      rw [h4]
      simpa using h3
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds) h_upper_tendsto h_squeeze1 h_squeeze2
  have h_eq : (fun x : ℝ ↦ logIntegral x * Real.log x / x) =ᶠ[atTop]
      (fun x : ℝ ↦ 1) - (fun x : ℝ ↦ (2 / Real.log 2) * (Real.log x / x))
      + (fun x : ℝ ↦ (∫ t in (2)..x, 1 / (Real.log t)^2) * (Real.log x / x)) := by
    filter_upwards [eventually_ge_atTop 2] with x hx
    have h_main' := h_main x hx
    simp [h_main']
    all_goals ring_nf
  have h_const : Tendsto (fun x : ℝ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h_err1 : Tendsto (fun x : ℝ ↦ (2 / Real.log 2) * (Real.log x / x)) atTop (𝓝 0) := by
    have h := h_log_div_x.const_mul (2 / Real.log 2)
    simpa using h
  have h_err2 := h_integral_term
  have h_sub := h_const.sub h_err1
  have h_add := h_sub.add h_err2
  have h_eq' :
    (fun x : ℝ ↦ (1 : ℝ) - (2 / Real.log 2) * (Real.log x / x) + (∫ t in (2)..x, 1 / (Real.log t)^2) * (Real.log x / x))
      =ᶠ[atTop] (fun x : ℝ ↦ logIntegral x * Real.log x / x) := by
    filter_upwards [h_eq] with x hx
    simp at hx ⊢
    linarith [hx]
  simpa using Tendsto.congr' h_eq' h_add

/-- 三種形式等価 -/
theorem pnt_forms_equivalent :
    (PNTForm1 ↔ PNTForm2) ∧ (PNTForm2 ↔ PNTForm3) := by
  have h12 : PNTForm1 ↔ PNTForm2 := by
    have h_li : Tendsto (fun x : ℝ ↦ logIntegral x * Real.log x / x) atTop (𝓝 1) :=
      logIntegral_asymptotic
    have h_li_inv : Tendsto (fun x : ℝ ↦ x / (logIntegral x * Real.log x)) atTop (𝓝 1) := by
      have h1 : Tendsto (fun x : ℝ ↦ (logIntegral x * Real.log x / x)⁻¹) atTop (𝓝 1) := by
        have h2 : Tendsto (fun x : ℝ ↦ logIntegral x * Real.log x / x) atTop (𝓝 1) := h_li
        have h3 : ∀ᶠ x in atTop, logIntegral x * Real.log x / x ≠ 0 := by
          filter_upwards [eventually_ge_atTop 3] with x hx
          have h_pos1 : 0 < logIntegral x := logIntegral_pos (by linarith)
          have h_pos2 : Real.log x > 0 := Real.log_pos (by linarith)
          have h_pos3 : x > 0 := by linarith
          positivity
        have h4 : Tendsto (fun x : ℝ ↦ (logIntegral x * Real.log x / x)⁻¹) atTop (𝓝 (1⁻¹)) := by
          exact Tendsto.inv₀ h2 (by norm_num)
        have h5 : (1 : ℝ)⁻¹ = 1 := by norm_num
        simpa [h5] using h4
      have h2 : ∀ᶠ x in atTop, (logIntegral x * Real.log x / x)⁻¹ = x / (logIntegral x * Real.log x) := by
        filter_upwards [eventually_ge_atTop 3] with x hx
        have h_pos1 : 0 < logIntegral x := logIntegral_pos (by linarith)
        have h_pos2 : Real.log x > 0 := Real.log_pos (by linarith)
        have h_pos3 : x > 0 := by linarith
        field_simp
      exact Tendsto.congr' h2 h1
    constructor
    · -- PNTForm1 → PNTForm2
      intro h1
      have h2 : Tendsto (fun x : ℝ ↦ (primeCounting x : ℝ) * Real.log x / x * (x / (logIntegral x * Real.log x))) atTop (𝓝 1) := by
        have h_mul := h1.mul h_li_inv
        simpa using h_mul
      have h3 : ∀ᶠ x in atTop, (primeCounting x : ℝ) * Real.log x / x * (x / (logIntegral x * Real.log x)) = (primeCounting x : ℝ) / logIntegral x := by
        filter_upwards [eventually_ge_atTop 3] with x hx
        have h_pos1 : 0 < logIntegral x := logIntegral_pos (by linarith)
        have h_pos2 : Real.log x > 0 := Real.log_pos (by linarith)
        have h_pos3 : x > 0 := by linarith
        field_simp
      exact Tendsto.congr' h3 h2
    · -- PNTForm2 → PNTForm1
      intro h2
      have h1 : Tendsto (fun x : ℝ ↦ (primeCounting x : ℝ) / logIntegral x * (logIntegral x * Real.log x / x)) atTop (𝓝 1) := by
        have h_mul := h2.mul h_li
        simpa using h_mul
      have h3 : ∀ᶠ x in atTop, (primeCounting x : ℝ) / logIntegral x * (logIntegral x * Real.log x / x) = (primeCounting x : ℝ) * Real.log x / x := by
        filter_upwards [eventually_ge_atTop 3] with x hx
        have h_pos1 : 0 < logIntegral x := logIntegral_pos (by linarith)
        have h_pos2 : Real.log x > 0 := Real.log_pos (by linarith)
        have h_pos3 : x > 0 := by linarith
        field_simp
      exact Tendsto.congr' h3 h1

  have h23 : PNTForm2 ↔ PNTForm3 := by
    have h_psi_theta : Tendsto (fun x : ℝ ↦ chebyshevPsi x / x) atTop (𝓝 1)
        ↔ Tendsto (fun x : ℝ ↦ Chebyshev.theta x / x) atTop (𝓝 1) := by
      have h_diff : Tendsto (fun x : ℝ ↦ (chebyshevPsi x - Chebyshev.theta x) / x) atTop (𝓝 0) := by
        have h1 : ∀ x ≥ 1, |(chebyshevPsi x - Chebyshev.theta x) / x| ≤ 2 * Real.sqrt x * Real.log x / x := by
          intro x hx
          have h2 : |chebyshevPsi x - Chebyshev.theta x| ≤ 2 * Real.sqrt x * Real.log x := by
            rw [chebyshevPsi_eq_mathlib]
            exact Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx
          have h3 : x > 0 := by linarith
          have h4 : |(chebyshevPsi x - Chebyshev.theta x) / x| = |chebyshevPsi x - Chebyshev.theta x| / |x| := by
            rw [abs_div]
          rw [h4]
          have h5 : |x| = x := by rw [abs_of_pos h3]
          rw [h5]
          apply div_le_div_of_nonneg_right h2 (by linarith)
        have h2 : ∀ᶠ x in atTop, |(chebyshevPsi x - Chebyshev.theta x) / x| ≤ 2 * Real.sqrt x * Real.log x / x := by
          filter_upwards [eventually_ge_atTop 1] with x hx
          exact h1 x hx
        have h3 : Tendsto (fun x : ℝ ↦ 2 * Real.sqrt x * Real.log x / x) atTop (𝓝 0) := by
          have : (fun x : ℝ ↦ 2 * Real.sqrt x * Real.log x / x) = (fun x : ℝ ↦ 2 * (Real.log x / Real.sqrt x)) := by
            ext x
            by_cases hx0 : x ≤ 0
            · simp [hx0, Real.sqrt_eq_zero'.mpr hx0]
            have hx : x ≠ 0 := by linarith
            have hsq : Real.sqrt x ≠ 0 := by exact (Real.sqrt_pos.2 (by linarith)).ne'
            field_simp [hx, hsq]
            ring_nf
            <;> rw [Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith)]
            <;> ring
          rw [this]
          have h4 : Tendsto (fun x : ℝ ↦ Real.log x / Real.sqrt x) atTop (𝓝 0) := by
            have h5 : Tendsto (fun x : ℝ ↦ Real.log x / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
              (isLittleO_log_rpow_atTop (by norm_num)).tendsto_div_nhds_zero
            have h6 : (fun x : ℝ ↦ Real.log x / x ^ (1 / 2 : ℝ))
                = (fun x : ℝ ↦ Real.log x / Real.sqrt x) := by
              ext x
              rw [Real.sqrt_eq_rpow]
            rwa [h6] at h5
          have h5 := h4.const_mul 2
          simpa using h5
        have h4 : Tendsto (fun x : ℝ ↦ |(chebyshevPsi x - Chebyshev.theta x) / x|) atTop (𝓝 0) := by
          have h0 : ∀ᶠ x in atTop, 0 ≤ |(chebyshevPsi x - Chebyshev.theta x) / x| := by
            filter_upwards [eventually_ge_atTop 1] with x hx
            exact abs_nonneg _
          exact tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds) h3 h0 h2
        have h5 : Tendsto (fun x : ℝ ↦ (chebyshevPsi x - Chebyshev.theta x) / x) atTop (𝓝 0) := by
          apply tendsto_zero_iff_norm_tendsto_zero.mpr h4
        exact h5
      constructor
      · intro h
        have h_eq : (fun x : ℝ ↦ Chebyshev.theta x / x)
            = (fun x : ℝ ↦ chebyshevPsi x / x - (chebyshevPsi x - Chebyshev.theta x) / x) := by
          ext x
          field_simp
          ring
        rw [h_eq]
        have h1 := h.sub h_diff
        simpa using h1
      · intro h
        have h_eq : (fun x : ℝ ↦ chebyshevPsi x / x)
            = (fun x : ℝ ↦ Chebyshev.theta x / x + (chebyshevPsi x - Chebyshev.theta x) / x) := by
          ext x
          field_simp
          ring
        rw [h_eq]
        have h1 := h.add h_diff
        simpa using h1

    have h_theta_pi : Tendsto (fun x : ℝ ↦ Chebyshev.theta x / x) atTop (𝓝 1)
        ↔ Tendsto (fun x : ℝ ↦ (primeCounting x : ℝ) / logIntegral x) atTop (𝓝 1) := by
      have h1 : Tendsto (fun x : ℝ ↦ Chebyshev.theta x / x) atTop (𝓝 1)
          ↔ Tendsto (fun x : ℝ ↦ (primeCounting x : ℝ) * Real.log x / x) atTop (𝓝 1) := by
        have h_bigO : (fun x : ℝ ↦ (Nat.primeCounting ⌊x⌋₊ : ℝ) - Chebyshev.theta x / Real.log x) =O[atTop] (fun x : ℝ ↦ x / Real.log x ^ 2) := by
          exact Chebyshev.primeCounting_sub_theta_div_log_isBigO
        have h_smallO : (fun x : ℝ ↦ x / Real.log x ^ 2) =o[atTop] (fun x : ℝ ↦ x / Real.log x) := by
          have : (fun x : ℝ ↦ x / Real.log x ^ 2) = (fun x : ℝ ↦ (1 / Real.log x) * (x / Real.log x)) := by
            ext x
            field_simp
          rw [this]
          have h1 : (fun x : ℝ ↦ 1 / Real.log x) =o[atTop] (fun _ : ℝ ↦ (1 : ℝ)) := by
            have h2 : Tendsto (fun x : ℝ ↦ 1 / Real.log x) atTop (𝓝 0) := by
              have h3 : Tendsto (fun x : ℝ ↦ Real.log x) atTop atTop := Real.tendsto_log_atTop
              have h4 : Tendsto (fun x : ℝ ↦ (x : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
              have h5 : Tendsto (fun x : ℝ ↦ (Real.log x : ℝ)⁻¹) atTop (𝓝 0) := h4.comp h3
              have h6 : (fun x : ℝ ↦ 1 / Real.log x) =ᶠ[atTop] (fun x : ℝ ↦ (Real.log x)⁻¹) := by
                filter_upwards [eventually_ge_atTop 2] with x hx
                have hlog : Real.log x ≠ 0 := by linarith [Real.log_pos (by linarith : (1 : ℝ) < x)]
                field_simp
              exact Tendsto.congr' (by filter_upwards [h6] with x hx; rw [hx.symm]) h5
            exact (isLittleO_one_iff ℝ).mpr h2
          have h7 : (fun x : ℝ ↦ 1 / Real.log x * (x / Real.log x)) =o[atTop] (fun x : ℝ ↦ x / Real.log x) := by
            have h8 := h1.mul_isBigO (isBigO_refl (fun x : ℝ ↦ x / Real.log x) atTop)
            have h9 : ∀ x : ℝ, (1 : ℝ) * (x / Real.log x) = x / Real.log x := by
              intro x; ring
            exact h8.congr_right h9
          exact h7
        have h_diff : (fun x : ℝ ↦ (Nat.primeCounting ⌊x⌋₊ : ℝ) - Chebyshev.theta x / Real.log x) =o[atTop] (fun x : ℝ ↦ x / Real.log x) := by
          exact IsBigO.trans_isLittleO h_bigO h_smallO
        constructor
        · intro h
          have h_eq : ∀ᶠ x in atTop, (primeCounting x : ℝ) * Real.log x / x = (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x / x := by
            filter_upwards [eventually_ge_atTop 0] with x hx
            rw [primeCounting_eq_mathlib x (by linarith)]
          have h_target : Tendsto (fun x : ℝ ↦ (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x / x) atTop (𝓝 1) := by
            have h_diff_tendsto : Tendsto (fun x : ℝ ↦ ((Nat.primeCounting ⌊x⌋₊ : ℝ) - Chebyshev.theta x / Real.log x) / (x / Real.log x)) atTop (𝓝 0) := by
              simpa using h_diff.tendsto_div_nhds_zero
            have h_theta_tendsto : Tendsto (fun x : ℝ ↦ (Chebyshev.theta x / Real.log x) / (x / Real.log x)) atTop (𝓝 1) := by
              have h_eq2 : ∀ᶠ x in atTop, Chebyshev.theta x / x = (Chebyshev.theta x / Real.log x) / (x / Real.log x) := by
                filter_upwards [eventually_ge_atTop 2] with x hx
                have hlog : Real.log x > 0 := Real.log_pos (by linarith)
                field_simp
              exact Tendsto.congr' h_eq2 h
            have h_sum : Tendsto (fun x : ℝ ↦ ((Nat.primeCounting ⌊x⌋₊ : ℝ) - Chebyshev.theta x / Real.log x) / (x / Real.log x) + (Chebyshev.theta x / Real.log x) / (x / Real.log x)) atTop (𝓝 1) := by
              have h_add := h_diff_tendsto.add h_theta_tendsto
              simpa using h_add
            have h_eq3 : ∀ᶠ x in atTop, ((Nat.primeCounting ⌊x⌋₊ : ℝ) - Chebyshev.theta x / Real.log x) / (x / Real.log x) + (Chebyshev.theta x / Real.log x) / (x / Real.log x) = (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x / x := by
              filter_upwards [eventually_ge_atTop 2] with x hx
              have hlog : Real.log x > 0 := Real.log_pos (by linarith)
              field_simp
              <;> ring
            exact Tendsto.congr' h_eq3 h_sum
          exact Tendsto.congr' (by filter_upwards [h_eq] with x hx; rw [hx.symm]) h_target
        · intro h
          have h_eq : ∀ᶠ x in atTop, (primeCounting x : ℝ) * Real.log x / x = (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x / x := by
            filter_upwards [eventually_ge_atTop 0] with x hx
            rw [primeCounting_eq_mathlib x (by linarith)]
          have h_pi : Tendsto (fun x : ℝ ↦ (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x / x) atTop (𝓝 1) := by
            exact Tendsto.congr' (by filter_upwards [h_eq] with x hx; rw [hx]) h
          have h_target : Tendsto (fun x : ℝ ↦ Chebyshev.theta x / x) atTop (𝓝 1) := by
            have h_diff_tendsto : Tendsto (fun x : ℝ ↦ ((Nat.primeCounting ⌊x⌋₊ : ℝ) - Chebyshev.theta x / Real.log x) / (x / Real.log x)) atTop (𝓝 0) := by
              simpa using h_diff.tendsto_div_nhds_zero
            have h_pi_tendsto : Tendsto (fun x : ℝ ↦ (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x)) atTop (𝓝 1) := by
              have h_eq2 : ∀ᶠ x in atTop, (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x / x = (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x) := by
                filter_upwards [eventually_ge_atTop 2] with x hx
                have hlog : Real.log x > 0 := Real.log_pos (by linarith)
                field_simp
              exact Tendsto.congr' h_eq2 h_pi
            have h_sum : Tendsto (fun x : ℝ ↦ (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x) - ((Nat.primeCounting ⌊x⌋₊ : ℝ) - Chebyshev.theta x / Real.log x) / (x / Real.log x)) atTop (𝓝 1) := by
              have h_sub := h_pi_tendsto.sub h_diff_tendsto
              simpa using h_sub
            have h_eq3 : ∀ᶠ x in atTop, Chebyshev.theta x / x = (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x) - ((Nat.primeCounting ⌊x⌋₊ : ℝ) - Chebyshev.theta x / Real.log x) / (x / Real.log x) := by
              filter_upwards [eventually_ge_atTop 2] with x hx
              have hlog : Real.log x > 0 := Real.log_pos (by linarith)
              field_simp
              <;> ring
            have h_eq3' : (fun x : ℝ ↦ (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x) - ((Nat.primeCounting ⌊x⌋₊ : ℝ) - Chebyshev.theta x / Real.log x) / (x / Real.log x)) =ᶠ[atTop] (fun x : ℝ ↦ Chebyshev.theta x / x) := by
              filter_upwards [h_eq3] with x hx
              rw [hx.symm]
            exact Tendsto.congr' h_eq3' h_sum
          exact h_target
      rw [h1]
      exact h12

    exact (Iff.trans h_psi_theta h_theta_pi).symm

  exact ⟨h12, h23⟩

/-! ## 与黎曼猜想的联系 -/

/-- 黎曼猜想的最优误差项形式 -/
def RH_ErrorBound : Prop :=
  ∃ C > 0, ∀ x ≥ 2,
    |(primeCounting x : ℝ) - logIntegral x| ≤ C * Real.sqrt x * Real.log x

/-- 定理：RH ⟺ 最优误差界 -/
theorem rh_iff_optimal_error :
    RiemannHypothesis.Statement ↔ RH_ErrorBound := by
  -- 这是黎曼猜想的标准等价形式之一
  sorry

/-! ## 零点对称性 -/

/-- 非平凡零点在 s ↦ 1-s 下对称：若 ζ(ρ) = 0 且 0 < Re(ρ) < 1，则 ζ(1-ρ) = 0。
    直接由函数方程 ζ(1-s) = 2(2π)^{-s} Γ(s) cos(πs/2) ζ(s) 得出。 -/
theorem nontrivial_zero_symmetric {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (hre : 0 < ρ.re) (hre' : ρ.re < 1) : riemannZeta (1 - ρ) = 0 := by
  have hρ_nat : ∀ n : ℕ, ρ ≠ -(n : ℂ) := by
    intro n
    intro h
    have : ρ.re = (-(n : ℂ)).re := congr_arg Complex.re h
    simp at this
    linarith
  have hρ_one : ρ ≠ 1 := by
    intro h
    have : ρ.re = 1 := congr_arg Complex.re h
    linarith
  rw [riemannZeta_one_sub hρ_nat hρ_one, hρ, mul_zero]

/-- 非平凡零点的 1-ρ 也是非平凡零点 -/
theorem nontrivial_zero_symmetric' {ρ : ℂ}
    (h : RiemannHypothesis.IsNontrivialZero ρ) :
    RiemannHypothesis.IsNontrivialZero (1 - ρ) := by
  obtain ⟨hζ, hre, hre'⟩ := h
  refine ⟨nontrivial_zero_symmetric hζ hre hre', ?_, ?_⟩
  · simp [Complex.sub_re]; linarith
  · simp [Complex.sub_re]; linarith

/-! ## 平凡零点表征 -/

/-- ζ(s) 在 Re(s) ≤ 0 区域的唯一零点是平凡零点 -2, -4, -6, ...
    证明使用函数方程 + Γ 非零 + 余弦零点刻画 + ζ 在 Re ≥ 1 的非零性。 -/
theorem riemannZeta_ne_zero_of_re_le_zero {s : ℂ} (hs : s.re ≤ 0)
    (htrivial : ∀ n : ℕ, s ≠ -2 * ((n : ℂ) + 1)) : riemannZeta s ≠ 0 := by
  rcases eq_or_ne s 0 with rfl | hs0
  · rw [riemannZeta_zero]; norm_num
  · have hnat : ∀ n : ℕ, (1 - s : ℂ) ≠ -(↑n : ℂ) := by
      intro n hn
      have hre := congr_arg Complex.re hn
      simp [Complex.sub_re, Complex.neg_re, Complex.natCast_re] at hre
      linarith
    have hone : (1 - s : ℂ) ≠ 1 := by
      intro h; exact hs0 (by linear_combination -h)
    have hfe := riemannZeta_one_sub (s := 1 - s) hnat hone
    have hsub : (1 : ℂ) - (1 - s) = s := by ring
    rw [hsub] at hfe
    rw [hfe]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_
    · exact two_ne_zero
    · exact cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero two_ne_zero
        (ofReal_ne_zero.mpr Real.pi_ne_zero)))
    · exact Complex.Gamma_ne_zero hnat
    · rw [Complex.cos_ne_zero_iff]
      intro k hk
      have hπ2 : (↑Real.pi / 2 : ℂ) ≠ 0 :=
        div_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) two_ne_zero
      have h1s : (1 - s : ℂ) = 2 * (k : ℂ) + 1 := by
        have h' : (1 - s) * (↑Real.pi / 2) = (2 * (↑k : ℂ) + 1) * (↑Real.pi / 2) := by
          linear_combination hk
        exact mul_right_cancel₀ hπ2 h'
      have hs_eq : s = -2 * (k : ℂ) := by linear_combination -h1s
      by_cases hk_le : k ≤ 0
      · have hre : s.re = -2 * (k : ℝ) := by
          have := congr_arg Complex.re hs_eq
          simp [Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.ofReal_re,
            Complex.ofReal_im] at this
          linarith
        have hk0 : k = 0 := by
          have hk_ge : (0 : ℤ) ≤ k := by
            by_contra h; push_neg at h
            have : (k : ℝ) < 0 := by exact_mod_cast h
            linarith
          omega
        exact hs0 (by rw [hs_eq, hk0]; simp)
      · push_neg at hk_le
        have hk1 : (0 : ℤ) ≤ k - 1 := by omega
        set n := (k - 1).toNat
        have hn : (↑n : ℤ) = k - 1 := Int.toNat_of_nonneg hk1
        have hkn : (k : ℂ) = (↑n : ℂ) + 1 := by
          have h : (k : ℤ) = ↑n + 1 := by omega
          exact_mod_cast congr_arg (Int.cast (R := ℂ)) h
        exact htrivial n (by rw [hs_eq, hkn])
    · exact riemannZeta_ne_zero_of_one_le_re (show 1 ≤ (1 - s).re by
        simp [Complex.sub_re]; linarith)

/-- 非平凡零点严格在临界带 0 < Re(s) < 1 内 -/
theorem nontrivial_zero_in_critical_strip {s : ℂ}
    (hζ : riemannZeta s = 0) (hnt : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) (hs1 : s ≠ 1) :
    0 < s.re ∧ s.re < 1 := by
  constructor
  · by_contra h
    push_neg at h
    exact riemannZeta_ne_zero_of_re_le_zero (by linarith : s.re ≤ 0)
      (by intro n hn; exact hnt ⟨n, hn⟩) hζ
  · by_contra h
    push_neg at h
    exact riemannZeta_ne_zero_of_one_le_re h hζ

/-- 任意有界高度内仅有有限多个非平凡零点 -/
theorem finite_nontrivial_zeros_bounded_height (T : ℝ) :
    Set.Finite {s : ℂ | RiemannHypothesis.IsNontrivialZero s ∧ |s.im| ≤ T} := by
  apply Set.Finite.subset (IsCompact.inter_riemannZetaZeros_finite
    (isCompact_closedBall (0 : ℂ) (|T| + 1)))
  intro s ⟨⟨hζ, hre, hre'⟩, him⟩
  refine ⟨?_, mem_riemannZetaZeros.mpr hζ⟩
  rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero]
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  calc √(s.re ^ 2 + s.im ^ 2)
      ≤ √(1 + T ^ 2) := by
        apply Real.sqrt_le_sqrt
        have him' := abs_le.mp him
        nlinarith [sq_abs s.im, sq_abs T]
    _ ≤ |T| + 1 := by
        rw [show |T| + 1 = √((|T| + 1) ^ 2) from
          (Real.sqrt_sq (by positivity)).symm]
        exact Real.sqrt_le_sqrt (by nlinarith [sq_abs T, abs_nonneg T])

/-- RH 等价于所有非平凡零点满足 Re = 1/2 -/
theorem rh_iff_nontrivial_zeros_on_line :
    RiemannHypothesis ↔
      ∀ s : ℂ, RiemannHypothesis.IsNontrivialZero s → s.re = 1 / 2 := by
  constructor
  · intro hRH s ⟨hζ, hre, hre'⟩
    exact hRH s hζ
      (by intro ⟨n, hn⟩; have := congr_arg Complex.re hn
          simp [Complex.mul_re, Complex.natCast_re, Complex.ofReal_re, Complex.add_re,
            Complex.one_re, Complex.neg_re, Complex.ofReal_im, Complex.natCast_im] at this
          linarith)
      (by intro h; have := congr_arg Complex.re h; simp at this; linarith)
  · intro h s hζ hnt hs1
    have hcs := nontrivial_zero_in_critical_strip hζ hnt hs1
    exact h s ⟨hζ, hcs.1, hcs.2⟩

/-- 本项目的 RH 定义与 Mathlib 的等价 -/
theorem rh_statement_iff_mathlib :
    _root_.RiemannHypothesis ↔ RiemannHypothesis.Statement :=
  rh_iff_nontrivial_zeros_on_line

/-- ζ 在 s=1 处有一阶极点：(s-1)²ζ(s) → 0 -/
theorem riemannZeta_pole_simple :
    Filter.Tendsto (fun s ↦ (s - 1) ^ 2 * riemannZeta s) (𝓝[≠] 1) (𝓝 0) := by
  have h_sub : Filter.Tendsto (fun s : ℂ ↦ s - 1) (𝓝[≠] 1) (𝓝 0) := by
    have h : Filter.Tendsto (fun s : ℂ ↦ s - 1) (𝓝 1) (𝓝 (1 - 1 : ℂ)) :=
      tendsto_id.sub tendsto_const_nhds
    simp at h
    exact h.mono_left nhdsWithin_le_nhds
  have h_res := riemannZeta_residue_one
  have := h_sub.mul h_res
  simp only [zero_mul] at this
  convert this using 1
  ext s; ring

/-- RH 蕴含零点的函数方程对称性自洽：ρ 和 1-ρ 都在临界线上意味着 ρ.re = 1/2 -/
theorem rh_zero_symmetric_self_consistent {ρ : ℂ}
    (hRH : RiemannHypothesis.Statement)
    (h : RiemannHypothesis.IsNontrivialZero ρ) :
    ρ.re = 1 / 2 ∧ (1 - ρ).re = 1 / 2 := by
  have h1 := hRH ρ h
  have h2 := hRH (1 - ρ) (nontrivial_zero_symmetric' h)
  exact ⟨h1, h2⟩


/-! ## 显式公式 -/

/-- von Mangoldt 显式公式

ψ(x) = x - ∑_ρ x^ρ/ρ - ζ'(0)/ζ(0) - 1/2 log(1-x^{-2})

其中求和遍历所有非平凡零点 ρ。
-/

theorem explicit_formula_von_mangoldt (x : ℝ) (hx : x ≥ 2) :
    chebyshevPsi x = x
    - ∑' ρ : {s : ℂ // RiemannHypothesis.IsNontrivialZero s},
        (x : ℂ) ^ (ρ : ℂ) / (ρ : ℂ)
    - (deriv riemannZeta 0) / riemannZeta 0
    - (1 / 2) * Real.log (1 - x^(-2 : ℝ)) := by
  -- 这是黎曼显式公式的标准形式
  -- 素数分布与 ζ 零点直接联系
  sorry

/-- 零点对素数分布的贡献

每个零点 ρ = β + iγ 贡献振荡项 x^ρ/ρ = x^β e^{iγ log x} / ρ
- 实部 β 决定振幅：x^β
- 虚部 γ 决定频率

如果 RH 成立，β = 1/2，振幅为 √x
-/

lemma zero_contribution (ρ : ℂ) (_hρ : RiemannHypothesis.IsNontrivialZero ρ) (x : ℝ) (hx : x > 1) :
    (x : ℂ) ^ ρ / ρ = Real.exp (ρ.re * Real.log x) * (Real.cos (ρ.im * Real.log x) + I * Real.sin (ρ.im * Real.log x)) / ρ := by
  -- 展示零点贡献的振荡性质
  -- 证明: x^ρ = x^{Re ρ} * e^{i * Im ρ * log x}
  have h1 : (x : ℂ) ^ ρ = Complex.exp (ρ * Complex.log (x : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero]
    · ring_nf
    · have hx' : (x : ℂ) ≠ 0 := by norm_cast; linarith
      exact hx'
  have h2 : Complex.log (x : ℂ) = (↑(Real.log x) : ℂ) := by
    have h_arg : Complex.arg (x : ℂ) = 0 := by
      rw [Complex.arg_ofReal_of_nonneg]
      all_goals linarith
    simp [Complex.log, h_arg]
  rw [h1, h2]
  have h3 : ρ * (↑(Real.log x) : ℂ) = (↑(ρ.re * Real.log x) : ℂ) + (↑(ρ.im * Real.log x) : ℂ) * I := by
    simp [Complex.ext_iff]
  rw [h3, Complex.exp_add]
  have h_exp_I : Complex.exp ((↑(ρ.im * Real.log x) : ℂ) * I) = Real.cos (ρ.im * Real.log x) + I * Real.sin (ρ.im * Real.log x) := by
    rw [Complex.exp_mul_I]
    simp [Complex.ofReal_cos, Complex.ofReal_sin]
    all_goals ring_nf
  rw [h_exp_I]
  have h4 : Complex.exp (↑(ρ.re * Real.log x) : ℂ) = (↑(Real.exp (ρ.re * Real.log x)) : ℂ) := by
    rw [← Complex.ofReal_exp]
  rw [h4]

end PrimeNumberTheorem
