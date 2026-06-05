/-
# Formalization of the Prime Number Theorem Framework

## Overview

This file contains Lean 4 infrastructure toward analytic number theory statements
around the Prime Number Theorem, built on top of Mathlib.

## Verified and partial results

1. **3-4-1 setup** (de la Vallée Poussin's trick):
   - `ZeroFreeRegion.trig_identity_nonneg`: 3 + 4cos θ + cos 2θ ≥ 0
   - `ZeroFreeRegion.log_deriv_zeta_nonneg_combination`:
     Verified non-negativity of
     3(-ζ'/ζ(σ)) + 4(-ζ'/ζ(σ+it)) + (-ζ'/ζ(σ+2it))
   - `ZeroFreeRegion.log_deriv_zeta_lower_bound`

2. **Zero-free regions**:
   - `ZeroFreeRegion.zeta_no_zeros_on_line_one`: ζ(s) ≠ 0 on Re(s) = 1
   - `ZeroFreeRegion.classical_zero_free_region_compact`:
     Verified compact zero-free region for each bounded height
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

5. **Dirichlet L-functions**:
   - `DirichletNonvanishing.three_four_one_inequality`
   - `DirichletNonvanishing.lfunction_ne_zero_re_eq_one`

6. **Euler product and zeta values**:
   - `EulerProductThm.euler_product`: Euler product formula
   - `ZetaTwo.zeta_two`: ζ(2) = π²/6
   - `ZetaFuncEq.zeta_one_sub`: Functional equation

## Remaining unproved target statements in this file

- `explicit_formula_von_mangoldt` — requires Perron's formula
- `rh_iff_optimal_error` — standard RH equivalence with prime-counting error terms

## Infrastructure gap analysis

Some target theorems require analytic infrastructure that is not yet connected
in this project. Missing or unfinished components include:
- Hadamard factorization theorem for entire functions of finite order
- argument-principle / residue-theorem contour applications
- Borel-Carathéodory/Jensen-style estimates specialized to `ζ'/ζ`
- Growth bounds for ζ in the critical strip
- Partial fraction expansion of ζ'/ζ in terms of zeros

## File structure

This file is currently about 1,000 lines. Earlier notes describing a
21,000-line infrastructure library do not match this checkout.
-/

import Mathlib
import HardyTheorem
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

/-- Jump size of the right-continuous Chebyshev ψ at a real point. -/
noncomputable def jumpVonMangoldt (x : ℝ) : ℝ := by
  classical
  exact if h : ∃ n : ℕ, x = (n : ℝ) then vonMangoldt (Classical.choose h) else 0

/-- Midpoint convention for Chebyshev ψ used by exact explicit formulae. -/
noncomputable def chebyshevPsi0 (x : ℝ) : ℝ :=
  chebyshevPsi x - jumpVonMangoldt x / 2

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
                · have hx_nonneg : 0 ≤ x := by linarith
                  nlinarith [Real.sq_sqrt hx_nonneg, Real.sqrt_nonneg x]
                · exact h7
                · exact intervalIntegrable_const
                · exact h6
              have h9 : ∫ (t : ℝ) in (Real.sqrt x)..x, 4 / (Real.log x)^2 = (x - Real.sqrt x) * (4 / (Real.log x)^2) := by
                rw [intervalIntegral.integral_const]
                simp [smul_eq_mul, div_eq_mul_inv, mul_comm, mul_assoc]
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
          · simp [Real.sqrt_eq_zero'.mpr hx0]
          have hx : x ≠ 0 := by linarith
          have hsq : Real.sqrt x ≠ 0 := by exact Real.sqrt_ne_zero'.2 (by linarith)
          field_simp [hx, hsq]
          ring_nf
          rw [Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith)]
          ring
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

lemma logIntegral_isLittleO_id :
    (fun x : ℝ => logIntegral x) =o[atTop] (fun x : ℝ => x) := by
  have hmain : Tendsto (fun x : ℝ => logIntegral x * Real.log x / x) atTop (𝓝 1) :=
    logIntegral_asymptotic
  have hlog_inv : Tendsto (fun x : ℝ => (Real.log x)⁻¹) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hratio :
      Tendsto
        (fun x : ℝ => (logIntegral x * Real.log x / x) * (Real.log x)⁻¹)
        atTop (𝓝 0) := by
    simpa using hmain.mul hlog_inv
  have heq :
      (fun x : ℝ => (logIntegral x * Real.log x / x) * (Real.log x)⁻¹)
        =ᶠ[atTop] fun x : ℝ => logIntegral x / x := by
    filter_upwards [eventually_ge_atTop (3 : ℝ)] with x hx
    have hlog_ne : Real.log x ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
    field_simp [hlog_ne]
  refine (isLittleO_iff_tendsto' ?_).2 (hratio.congr' heq)
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with x hx hzero
  have hxpos : 0 < x := by linarith
  exact False.elim (hxpos.ne' hzero)

lemma logIntegral_isBigO_id :
    (fun x : ℝ => logIntegral x) =O[atTop] (fun x : ℝ => x) :=
  logIntegral_isLittleO_id.isBigO

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
            · simp [Real.sqrt_eq_zero'.mpr hx0]
            have hx : x ≠ 0 := by linarith
            have hsq : Real.sqrt x ≠ 0 := by exact (Real.sqrt_pos.2 (by linarith)).ne'
            field_simp [hx, hsq]
            ring_nf
            rw [Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith)]
            ring
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
              ring
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
              ring
            have h_eq3' : (fun x : ℝ ↦ (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x) - ((Nat.primeCounting ⌊x⌋₊ : ℝ) - Chebyshev.theta x / Real.log x) / (x / Real.log x)) =ᶠ[atTop] (fun x : ℝ ↦ Chebyshev.theta x / x) := by
              filter_upwards [h_eq3] with x hx
              rw [hx.symm]
            exact Tendsto.congr' h_eq3' h_sum
          exact h_target
      rw [h1]
      exact h12

    exact (Iff.trans h_psi_theta h_theta_pi).symm

  exact ⟨h12, h23⟩

/-- Standalone form of the already-proved equivalence between the
prime-counting and logarithmic-integral PNT targets. -/
lemma PNTForm1_iff_PNTForm2 : PNTForm1 ↔ PNTForm2 :=
  pnt_forms_equivalent.1

lemma PNTForm2_iff_PNTForm1 : PNTForm2 ↔ PNTForm1 :=
  PNTForm1_iff_PNTForm2.symm

/-- Standalone form of the already-proved equivalence between the
logarithmic-integral and Chebyshev-ψ PNT targets. -/
lemma PNTForm2_iff_PNTForm3 : PNTForm2 ↔ PNTForm3 :=
  pnt_forms_equivalent.2

lemma PNTForm3_iff_PNTForm2 : PNTForm3 ↔ PNTForm2 :=
  PNTForm2_iff_PNTForm3.symm

lemma PNTForm2_of_PNTForm1 (h : PNTForm1) : PNTForm2 :=
  PNTForm1_iff_PNTForm2.mp h

lemma PNTForm1_of_PNTForm2 (h : PNTForm2) : PNTForm1 :=
  PNTForm1_iff_PNTForm2.mpr h

lemma PNTForm2_error_isLittleO_logIntegral
    (h : PNTForm2) :
    (fun x : ℝ => (primeCounting x : ℝ) - logIntegral x)
      =o[atTop] (fun x : ℝ => logIntegral x) := by
  have hratio :
      Tendsto (fun x : ℝ => (primeCounting x : ℝ) / logIntegral x - 1)
        atTop (𝓝 0) := by
    simpa using (h.sub tendsto_const_nhds :
      Tendsto (fun x : ℝ => (primeCounting x : ℝ) / logIntegral x - (1 : ℝ))
        atTop (𝓝 (1 - 1)))
  have heq :
      (fun x : ℝ => (primeCounting x : ℝ) / logIntegral x - 1)
        =ᶠ[atTop]
      fun x : ℝ => ((primeCounting x : ℝ) - logIntegral x) / logIntegral x := by
    filter_upwards [eventually_ge_atTop (3 : ℝ)] with x hx
    have hli_ne : logIntegral x ≠ 0 := ne_of_gt (logIntegral_pos (by linarith))
    field_simp [hli_ne]
  refine (isLittleO_iff_tendsto' ?_).2 (hratio.congr' heq)
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with x hx hzero
  have hli_ne : logIntegral x ≠ 0 := ne_of_gt (logIntegral_pos (by linarith))
  exact False.elim (hli_ne hzero)

lemma PNTForm2_of_error_isLittleO_logIntegral
    (h :
      (fun x : ℝ => (primeCounting x : ℝ) - logIntegral x)
        =o[atTop] (fun x : ℝ => logIntegral x)) :
    PNTForm2 := by
  have hratio := h.tendsto_div_nhds_zero
  have hsum :
      Tendsto
        (fun x : ℝ =>
          1 + ((primeCounting x : ℝ) - logIntegral x) / logIntegral x)
        atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add hratio :
      Tendsto
        (fun x : ℝ =>
          (1 : ℝ) + ((primeCounting x : ℝ) - logIntegral x) / logIntegral x)
        atTop (𝓝 ((1 : ℝ) + 0)))
  have heq :
      (fun x : ℝ =>
          1 + ((primeCounting x : ℝ) - logIntegral x) / logIntegral x)
        =ᶠ[atTop] fun x : ℝ => (primeCounting x : ℝ) / logIntegral x := by
    filter_upwards [eventually_ge_atTop (3 : ℝ)] with x hx
    have hli_ne : logIntegral x ≠ 0 := ne_of_gt (logIntegral_pos (by linarith))
    field_simp [hli_ne]
    ring
  exact hsum.congr' heq

lemma PNTForm2_iff_error_isLittleO_logIntegral :
    PNTForm2 ↔
      (fun x : ℝ => (primeCounting x : ℝ) - logIntegral x)
        =o[atTop] (fun x : ℝ => logIntegral x) :=
  ⟨PNTForm2_error_isLittleO_logIntegral,
    PNTForm2_of_error_isLittleO_logIntegral⟩

lemma PNTForm2_error_isLittleO_id
    (h : PNTForm2) :
    (fun x : ℝ => (primeCounting x : ℝ) - logIntegral x)
      =o[atTop] (fun x : ℝ => x) :=
  (PNTForm2_error_isLittleO_logIntegral h).trans logIntegral_isLittleO_id

lemma PNTForm3_of_PNTForm2 (h : PNTForm2) : PNTForm3 :=
  PNTForm2_iff_PNTForm3.mp h

lemma PNTForm2_of_PNTForm3 (h : PNTForm3) : PNTForm2 :=
  PNTForm2_iff_PNTForm3.mpr h

/-- Transitive packaging of the three equivalent PNT formulations. -/
lemma PNTForm1_iff_PNTForm3 : PNTForm1 ↔ PNTForm3 :=
  Iff.trans PNTForm1_iff_PNTForm2 PNTForm2_iff_PNTForm3

lemma PNTForm3_iff_PNTForm1 : PNTForm3 ↔ PNTForm1 :=
  PNTForm1_iff_PNTForm3.symm

lemma PNTForm3_of_PNTForm1 (h : PNTForm1) : PNTForm3 :=
  PNTForm1_iff_PNTForm3.mp h

lemma PNTForm1_of_PNTForm3 (h : PNTForm3) : PNTForm1 :=
  PNTForm1_iff_PNTForm3.mpr h

/-! ## 与黎曼猜想的联系 -/

/-- RH-scale Chebyshev-ψ error target. -/
def RH_PsiErrorBound : Prop :=
  (fun x : ℝ => chebyshevPsi x - x)
    =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2)

/-- RH-scale Chebyshev-θ error target. -/
def RH_ThetaErrorBound : Prop :=
  (fun x : ℝ => Chebyshev.theta x - x)
    =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2)

/-- The standard bound `ψ(x)-θ(x)=O(sqrt x log x)` is small enough for the
RH-scale `sqrt x log^2 x` error term. -/
lemma psi_sub_theta_isBigO_rh_scale :
    (fun x : ℝ => chebyshevPsi x - Chebyshev.theta x)
      =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2) := by
  refine Asymptotics.IsBigO.of_bound 2 ?_
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hx1 : 1 ≤ x := by
    have h_exp_one : (1 : ℝ) ≤ Real.exp 1 := by
      rw [Real.one_le_exp_iff]
      norm_num
    exact le_trans h_exp_one hx
  have hlog1 : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).mpr hx
  have hlog_nonneg : 0 ≤ Real.log x := by linarith
  have hlog_le_sq : Real.log x ≤ (Real.log x)^2 := by nlinarith
  have hmain := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (x := x) hx1
  have hmain' : |chebyshevPsi x - Chebyshev.theta x| ≤ 2 * Real.sqrt x * Real.log x := by
    simpa [chebyshevPsi_eq_mathlib] using hmain
  have hg_nonneg : 0 ≤ Real.sqrt x * (Real.log x)^2 :=
    mul_nonneg (Real.sqrt_nonneg x) (sq_nonneg _)
  have hscale : 2 * Real.sqrt x * Real.log x ≤
      2 * (Real.sqrt x * (Real.log x)^2) := by
    nlinarith [Real.sqrt_nonneg x, hlog_le_sq]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hg_nonneg]
  exact le_trans hmain' hscale

lemma chebyshevTheta_isBigO_id :
    (fun x : ℝ => Chebyshev.theta x) =O[atTop] (fun x : ℝ => x) := by
  refine Asymptotics.IsBigO.of_bound (Real.log 4) ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have htheta_nonneg : 0 ≤ Chebyshev.theta x := Chebyshev.theta_nonneg x
  have htheta_le := Chebyshev.theta_le_log4_mul_x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg htheta_nonneg,
    abs_of_nonneg hx]
  exact htheta_le

lemma mathlibChebyshevPsi_isBigO_id :
    (fun x : ℝ => Chebyshev.psi x) =O[atTop] (fun x : ℝ => x) := by
  refine Asymptotics.IsBigO.of_bound (Real.log 4 + 4) ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have hpsi_nonneg : 0 ≤ Chebyshev.psi x := Chebyshev.psi_nonneg x
  have hpsi_le := Chebyshev.psi_le_const_mul_self hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpsi_nonneg,
    abs_of_nonneg hx]
  exact hpsi_le

lemma chebyshevPsi_isBigO_id :
    (fun x : ℝ => chebyshevPsi x) =O[atTop] (fun x : ℝ => x) := by
  simpa [chebyshevPsi_eq_mathlib] using mathlibChebyshevPsi_isBigO_id

lemma chebyshevPsi_sub_id_isBigO_id :
    (fun x : ℝ => chebyshevPsi x - x) =O[atTop] (fun x : ℝ => x) :=
  chebyshevPsi_isBigO_id.sub (isBigO_refl (fun x : ℝ => x) atTop)

lemma chebyshevTheta_sub_id_isBigO_id :
    (fun x : ℝ => Chebyshev.theta x - x) =O[atTop] (fun x : ℝ => x) :=
  chebyshevTheta_isBigO_id.sub (isBigO_refl (fun x : ℝ => x) atTop)

/-- RH-scale `ψ` error implies the corresponding `θ` error. -/
lemma RH_ThetaErrorBound_of_RH_PsiErrorBound
    (hψ : RH_PsiErrorBound) : RH_ThetaErrorBound := by
  have hdiff := psi_sub_theta_isBigO_rh_scale
  have hsub := hψ.sub hdiff
  have h_eq :
      (fun x : ℝ => (chebyshevPsi x - x) - (chebyshevPsi x - Chebyshev.theta x))
        = (fun x : ℝ => Chebyshev.theta x - x) := by
    funext x
    ring
  simpa [RH_PsiErrorBound, RH_ThetaErrorBound, h_eq] using hsub

/-- RH-scale `θ` error implies the corresponding `ψ` error. -/
lemma RH_PsiErrorBound_of_RH_ThetaErrorBound
    (hθ : RH_ThetaErrorBound) : RH_PsiErrorBound := by
  have hdiff := psi_sub_theta_isBigO_rh_scale
  have hadd := hθ.add hdiff
  have h_eq :
      (fun x : ℝ => (Chebyshev.theta x - x) + (chebyshevPsi x - Chebyshev.theta x))
        = (fun x : ℝ => chebyshevPsi x - x) := by
    funext x
    ring
  simpa [RH_PsiErrorBound, RH_ThetaErrorBound, h_eq] using hadd

lemma RH_PsiErrorBound_iff_RH_ThetaErrorBound :
    RH_PsiErrorBound ↔ RH_ThetaErrorBound :=
  ⟨RH_ThetaErrorBound_of_RH_PsiErrorBound,
    RH_PsiErrorBound_of_RH_ThetaErrorBound⟩

/-- Symmetric orientation of the ψ/θ RH-scale error equivalence. -/
lemma RH_ThetaErrorBound_iff_RH_PsiErrorBound :
    RH_ThetaErrorBound ↔ RH_PsiErrorBound :=
  RH_PsiErrorBound_iff_RH_ThetaErrorBound.symm

/-- An eventual absolute-value estimate is enough to close the `ψ` Big-O target. -/
lemma RH_PsiErrorBound_of_eventual_abs_bound {C : ℝ}
    (h : ∀ᶠ x in atTop,
      |chebyshevPsi x - x| ≤ C * (Real.sqrt x * (Real.log x)^2)) :
    RH_PsiErrorBound := by
  rw [RH_PsiErrorBound]
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hscale_nonneg : 0 ≤ Real.sqrt x * (Real.log x)^2 :=
    mul_nonneg (Real.sqrt_nonneg x) (sq_nonneg _)
  have hsqrt_abs : |Real.sqrt x| = Real.sqrt x :=
    abs_of_nonneg (Real.sqrt_nonneg x)
  have hlog_sq_abs : |(Real.log x)^2| = (Real.log x)^2 :=
    abs_of_nonneg (sq_nonneg _)
  simpa [Real.norm_eq_abs, abs_mul, hsqrt_abs, hlog_sq_abs,
    abs_of_nonneg hscale_nonneg, mul_assoc] using hx

/-- Pointwise textbook-style bounds imply the composable `ψ` Big-O target. -/
lemma RH_PsiErrorBound_of_pointwise {C : ℝ}
    (_hCpos : 0 < C)
    (h : ∀ x ≥ 2,
      |chebyshevPsi x - x| ≤ C * (Real.sqrt x * (Real.log x)^2)) :
    RH_PsiErrorBound :=
  RH_PsiErrorBound_of_eventual_abs_bound (by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    exact h x hx)

/-- An eventual absolute-value estimate is enough to close the `θ` Big-O target. -/
lemma RH_ThetaErrorBound_of_eventual_abs_bound {C : ℝ}
    (h : ∀ᶠ x in atTop,
      |Chebyshev.theta x - x| ≤ C * (Real.sqrt x * (Real.log x)^2)) :
    RH_ThetaErrorBound := by
  rw [RH_ThetaErrorBound]
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hscale_nonneg : 0 ≤ Real.sqrt x * (Real.log x)^2 :=
    mul_nonneg (Real.sqrt_nonneg x) (sq_nonneg _)
  have hsqrt_abs : |Real.sqrt x| = Real.sqrt x :=
    abs_of_nonneg (Real.sqrt_nonneg x)
  have hlog_sq_abs : |(Real.log x)^2| = (Real.log x)^2 :=
    abs_of_nonneg (sq_nonneg _)
  simpa [Real.norm_eq_abs, abs_mul, hsqrt_abs, hlog_sq_abs,
    abs_of_nonneg hscale_nonneg, mul_assoc] using hx

/-- Pointwise textbook-style bounds imply the composable `θ` Big-O target. -/
lemma RH_ThetaErrorBound_of_pointwise {C : ℝ}
    (_hCpos : 0 < C)
    (h : ∀ x ≥ 2,
      |Chebyshev.theta x - x| ≤ C * (Real.sqrt x * (Real.log x)^2)) :
    RH_ThetaErrorBound :=
  RH_ThetaErrorBound_of_eventual_abs_bound (by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    exact h x hx)

/-- RH-scale prime-counting error target in composable asymptotic form. -/
def RH_PrimeCountingLiErrorBound : Prop :=
  (fun x : ℝ => (primeCounting x : ℝ) - logIntegral x)
    =O[atTop] (fun x : ℝ => Real.sqrt x * Real.log x)

/-- Pointwise version of the RH-scale prime-counting error target.

The `=O[atTop]` form above is the target used for future formal composition;
this pointwise form is kept for the classical textbook statement. -/
def RH_ErrorBound : Prop :=
  ∃ C > 0, ∀ x ≥ 2,
    |(primeCounting x : ℝ) - logIntegral x| ≤ C * Real.sqrt x * Real.log x

/-- An eventual absolute-value estimate is enough to close the prime-counting
`Li` Big-O target. -/
lemma RH_PrimeCountingLiErrorBound_of_eventual_abs_bound {C : ℝ}
    (h : ∀ᶠ x in atTop,
      |(primeCounting x : ℝ) - logIntegral x| ≤ C * (Real.sqrt x * Real.log x)) :
    RH_PrimeCountingLiErrorBound := by
  rw [RH_PrimeCountingLiErrorBound]
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hscale_nonneg : 0 ≤ Real.sqrt x * Real.log x :=
    mul_nonneg (Real.sqrt_nonneg x) hlog_nonneg
  have hsqrt_abs : |Real.sqrt x| = Real.sqrt x :=
    abs_of_nonneg (Real.sqrt_nonneg x)
  have hlog_abs : |Real.log x| = Real.log x :=
    abs_of_nonneg hlog_nonneg
  simpa [Real.norm_eq_abs, abs_mul, hsqrt_abs, hlog_abs,
    abs_of_nonneg hscale_nonneg, mul_assoc] using hx

/-- The pointwise textbook error target implies the composable `=O[atTop]`
form used by the rest of the formalization. -/
lemma RH_PrimeCountingLiErrorBound_of_pointwise
    (h : RH_ErrorBound) : RH_PrimeCountingLiErrorBound := by
  rcases h with ⟨C, _hCpos, hC⟩
  exact RH_PrimeCountingLiErrorBound_of_eventual_abs_bound (by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    simpa [mul_assoc] using hC x hx)

/-- Named bridge from the textbook pointwise RH-scale error statement to the
composable prime-counting `=O[atTop]` target. -/
lemma RH_PrimeCountingLiErrorBound_of_RH_ErrorBound
    (h : RH_ErrorBound) : RH_PrimeCountingLiErrorBound :=
  RH_PrimeCountingLiErrorBound_of_pointwise h

/-- On a bounded interval, the elementary count of primes is bounded by the
number of integers up to the right endpoint. -/
lemma primeCounting_le_floor_add_one {x X : ℝ} (hxX : x ≤ X) :
    primeCounting x ≤ ⌊X⌋₊ + 1 := by
  rw [primeCounting]
  have hncard :
      {p : ℕ | p.Prime ∧ (p : ℝ) ≤ x}.ncard ≤
        (Finset.range (⌊X⌋₊ + 1) : Set ℕ).ncard := by
    refine Set.ncard_le_ncard ?_
    intro p hp
    simp only [Set.mem_setOf_eq] at hp
    simp only [Finset.mem_coe, Finset.mem_range]
    have hpX : (p : ℝ) ≤ X := le_trans hp.2 hxX
    have hpfloor : p ≤ ⌊X⌋₊ := Nat.le_floor hpX
    omega
  simpa [Set.ncard_coe_finset] using hncard

lemma primeCounting_isBigO_id :
    (fun x : ℝ => (primeCounting x : ℝ)) =O[atTop] (fun x : ℝ => x) := by
  refine Asymptotics.IsBigO.of_bound 2 ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx_nonneg : 0 ≤ x := by linarith
  have hpc_nat : primeCounting x ≤ ⌊x⌋₊ + 1 :=
    primeCounting_le_floor_add_one (x := x) (X := x) le_rfl
  have hpc_floor : (primeCounting x : ℝ) ≤ ((⌊x⌋₊ + 1 : ℕ) : ℝ) := by
    exact_mod_cast hpc_nat
  have hfloor : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx_nonneg
  have hfloor_add : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ x + 1 := by
    norm_num
    linarith
  have hpc_le : (primeCounting x : ℝ) ≤ 2 * x := by
    linarith
  have hpc_nonneg : 0 ≤ (primeCounting x : ℝ) := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpc_nonneg,
    abs_of_nonneg hx_nonneg]
  exact hpc_le

lemma primeCounting_sub_logIntegral_isBigO_id :
    (fun x : ℝ => (primeCounting x : ℝ) - logIntegral x)
      =O[atTop] (fun x : ℝ => x) := by
  have hpi := primeCounting_isBigO_id
  exact hpi.sub logIntegral_isBigO_id

/-- A crude upper bound for `Li(x)` on a bounded interval. -/
lemma logIntegral_le_interval_bound {x X : ℝ} (hx2 : 2 ≤ x) (hxX : x ≤ X) :
    logIntegral x ≤ (X - 2) / Real.log 2 := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_integrand :
      ∀ t ∈ Set.Icc (2 : ℝ) x, 1 / Real.log t ≤ 1 / Real.log 2 := by
    intro t ht
    have ht2 : 2 ≤ t := ht.1
    have hlog_le : Real.log 2 ≤ Real.log t :=
      Real.log_le_log (by norm_num) ht2
    exact one_div_le_one_div_of_le hlog2_pos hlog_le
  have h_integrable : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume 2 x := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    have ht1 : 1 < t := by
      rw [Set.mem_uIcc] at ht
      cases ht with
      | inl h => linarith
      | inr h => linarith
    have hlog_ne : Real.log t ≠ 0 := by
      exact Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    exact ContinuousAt.div continuousAt_const
      (Real.continuousAt_log (by linarith)) hlog_ne
  have h_li_le_const :
      logIntegral x ≤ ∫ t in (2)..x, 1 / Real.log 2 := by
    rw [logIntegral]
    exact intervalIntegral.integral_mono_on hx2 h_integrable
      intervalIntegrable_const h_integrand
  have h_const :
      ∫ t in (2)..x, 1 / Real.log 2 = (x - 2) / Real.log 2 := by
    rw [intervalIntegral.integral_const]
    simp [smul_eq_mul]
    ring
  have h_linear : (x - 2) / Real.log 2 ≤ (X - 2) / Real.log 2 := by
    exact div_le_div_of_nonneg_right (by linarith) hlog2_pos.le
  linarith

/-- The RH-scale denominator has a positive lower bound on `[2, ∞)`. -/
lemma sqrt_mul_log_lower_bound {x : ℝ} (hx2 : 2 ≤ x) :
    Real.sqrt 2 * Real.log 2 ≤ Real.sqrt x * Real.log x := by
  have hsqrt_le : Real.sqrt 2 ≤ Real.sqrt x :=
    Real.sqrt_le_sqrt hx2
  have hlog_le : Real.log 2 ≤ Real.log x :=
    Real.log_le_log (by norm_num) hx2
  exact mul_le_mul hsqrt_le hlog_le (Real.log_nonneg (by norm_num)) (Real.sqrt_nonneg x)

/-- The finite-interval control needed to turn an eventual RH-scale `Li` error
bound into a pointwise bound.  This deliberately uses only crude estimates:
`π(x)` is bounded by the number of integers up to `X`, `Li(x)` by integrating
the constant `1 / log 2`, and `sqrt x * log x` is bounded below on `x ≥ 2`. -/
lemma primeCounting_logIntegral_finite_interval_bound :
    ∀ X ≥ 2, ∃ C > 0, ∀ x, 2 ≤ x → x ≤ X →
      |(primeCounting x : ℝ) - logIntegral x| ≤
        C * (Real.sqrt x * Real.log x) := by
  intro X hX2
  let B : ℝ := (⌊X⌋₊ + 1 : ℕ) + (X - 2) / Real.log 2
  let D : ℝ := Real.sqrt 2 * Real.log 2
  refine ⟨(B + 1) / D, ?_, ?_⟩
  · have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hD_pos : 0 < D := by
      exact mul_pos (Real.sqrt_pos.2 (by norm_num)) hlog2_pos
    have hB_pos : 0 < B + 1 := by
      have hfloor_nonneg : 0 ≤ ((⌊X⌋₊ + 1 : ℕ) : ℝ) := by positivity
      have hli_bound_nonneg : 0 ≤ (X - 2) / Real.log 2 := by
        exact div_nonneg (by linarith) hlog2_pos.le
      dsimp [B]
      linarith
    exact div_pos hB_pos hD_pos
  · intro x hx2 hxX
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hD_pos : 0 < D := by
      exact mul_pos (Real.sqrt_pos.2 (by norm_num)) hlog2_pos
    have hD_ne : D ≠ 0 := ne_of_gt hD_pos
    have hpi_le_nat : primeCounting x ≤ ⌊X⌋₊ + 1 :=
      primeCounting_le_floor_add_one hxX
    have hpi_le : (primeCounting x : ℝ) ≤ ((⌊X⌋₊ + 1 : ℕ) : ℝ) := by
      exact_mod_cast hpi_le_nat
    have hli_nonneg : 0 ≤ logIntegral x := logIntegral_nonneg hx2
    have hli_le : logIntegral x ≤ (X - 2) / Real.log 2 :=
      logIntegral_le_interval_bound hx2 hxX
    have hdiff_le_B :
        |(primeCounting x : ℝ) - logIntegral x| ≤ B := by
      rw [abs_sub_le_iff]
      constructor
      · dsimp [B]
        linarith
      · dsimp [B]
        linarith
    have hB_le_B1 : B ≤ B + 1 := by linarith
    have hdiff_le_B1 :
        |(primeCounting x : ℝ) - logIntegral x| ≤ B + 1 :=
      le_trans hdiff_le_B hB_le_B1
    have hB1_nonneg : 0 ≤ B + 1 := by
      have hfloor_nonneg : 0 ≤ ((⌊X⌋₊ + 1 : ℕ) : ℝ) := by positivity
      have hli_bound_nonneg : 0 ≤ (X - 2) / Real.log 2 := by
        exact div_nonneg (by linarith) hlog2_pos.le
      dsimp [B]
      linarith
    have hD_le_scale :
        D ≤ Real.sqrt x * Real.log x := by
      simpa [D] using sqrt_mul_log_lower_bound hx2
    have hcoef_nonneg : 0 ≤ (B + 1) / D :=
      div_nonneg hB1_nonneg hD_pos.le
    have hscale :
        B + 1 ≤ ((B + 1) / D) * (Real.sqrt x * Real.log x) := by
      have hmul :
          ((B + 1) / D) * D ≤
            ((B + 1) / D) * (Real.sqrt x * Real.log x) :=
        mul_le_mul_of_nonneg_left hD_le_scale hcoef_nonneg
      have hmul_eq : ((B + 1) / D) * D = B + 1 := by
        field_simp [hD_ne]
      linarith
    exact le_trans hdiff_le_B1 (by simpa [B, D] using hscale)

/-- Reverse bridge from the composable `=O[atTop]` target to the textbook
pointwise RH-scale error target, assuming the missing finite-interval bound.

The finite-interval hypothesis is the exact extra data needed here: the Big-O
hypothesis supplies a positive constant after some threshold, while this
hypothesis supplies a positive constant on the bounded interval before that
threshold. -/
lemma RH_ErrorBound_of_RH_PrimeCountingLiErrorBound_of_finite_intervals
    (h : RH_PrimeCountingLiErrorBound)
    (hfinite : ∀ X ≥ 2, ∃ C > 0, ∀ x, 2 ≤ x → x ≤ X →
      |(primeCounting x : ℝ) - logIntegral x| ≤
        C * (Real.sqrt x * Real.log x)) :
    RH_ErrorBound := by
  rw [RH_PrimeCountingLiErrorBound] at h
  rcases h.exists_pos with ⟨Ctail, hCtail_pos, htailO⟩
  rcases eventually_atTop.mp htailO.bound with ⟨T, htail⟩
  let X : ℝ := max 2 T
  rcases hfinite X (le_max_left 2 T) with ⟨Cinit, hCinit_pos, hinit⟩
  let C : ℝ := max Cinit Ctail
  refine ⟨C, lt_of_lt_of_le hCinit_pos (le_max_left Cinit Ctail), ?_⟩
  intro x hx2
  have hx1 : 1 ≤ x := by linarith
  have hlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hscale_nonneg : 0 ≤ Real.sqrt x * Real.log x :=
    mul_nonneg (Real.sqrt_nonneg x) hlog_nonneg
  by_cases hxX : x ≤ X
  · have hx_init := hinit x hx2 hxX
    have hCinit_le_C : Cinit ≤ C := le_max_left Cinit Ctail
    have hscale :
        Cinit * (Real.sqrt x * Real.log x) ≤
          C * (Real.sqrt x * Real.log x) :=
      mul_le_mul_of_nonneg_right hCinit_le_C hscale_nonneg
    exact le_trans hx_init (by simpa [C, mul_assoc] using hscale)
  · have hX_lt : X < x := lt_of_not_ge hxX
    have hT_le_x : T ≤ x := le_trans (le_max_right 2 T) hX_lt.le
    have hx_tail := htail x hT_le_x
    have hsqrt_abs : |Real.sqrt x| = Real.sqrt x :=
      abs_of_nonneg (Real.sqrt_nonneg x)
    have hlog_abs : |Real.log x| = Real.log x :=
      abs_of_nonneg hlog_nonneg
    have htail_abs :
        |(primeCounting x : ℝ) - logIntegral x| ≤
          Ctail * (Real.sqrt x * Real.log x) := by
      simpa [Real.norm_eq_abs, abs_mul, hsqrt_abs, hlog_abs,
        abs_of_nonneg hscale_nonneg, mul_assoc] using hx_tail
    have hCtail_le_C : Ctail ≤ C := le_max_right Cinit Ctail
    have hscale :
        Ctail * (Real.sqrt x * Real.log x) ≤
          C * (Real.sqrt x * Real.log x) :=
      mul_le_mul_of_nonneg_right hCtail_le_C hscale_nonneg
    exact le_trans htail_abs (by simpa [C, mul_assoc] using hscale)

/-- Reverse bridge from the composable `=O[atTop]` target to the textbook
pointwise RH-scale error target.  The finite initial interval is discharged by
`primeCounting_logIntegral_finite_interval_bound`. -/
lemma RH_ErrorBound_of_RH_PrimeCountingLiErrorBound
    (h : RH_PrimeCountingLiErrorBound) : RH_ErrorBound :=
  RH_ErrorBound_of_RH_PrimeCountingLiErrorBound_of_finite_intervals h
    primeCounting_logIntegral_finite_interval_bound

lemma RH_ErrorBound_iff_RH_PrimeCountingLiErrorBound :
    RH_ErrorBound ↔ RH_PrimeCountingLiErrorBound :=
  ⟨RH_PrimeCountingLiErrorBound_of_RH_ErrorBound,
    RH_ErrorBound_of_RH_PrimeCountingLiErrorBound⟩

lemma RH_PrimeCountingLiErrorBound_iff_RH_ErrorBound :
    RH_PrimeCountingLiErrorBound ↔ RH_ErrorBound :=
  RH_ErrorBound_iff_RH_PrimeCountingLiErrorBound.symm

lemma log_sq_div_sqrt_tendsto_zero :
    Tendsto (fun x : ℝ => (Real.log x)^2 / Real.sqrt x) atTop (𝓝 0) := by
  have hq :
      Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 4 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).tendsto_div_nhds_zero
  have hsq := hq.mul hq
  have heq :
      (fun x : ℝ => (Real.log x / x ^ (1 / 4 : ℝ)) *
          (Real.log x / x ^ (1 / 4 : ℝ)))
        =ᶠ[atTop] fun x : ℝ => (Real.log x)^2 / Real.sqrt x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hxnonneg : 0 ≤ x := le_of_lt hx
    have hxpow_ne : x ^ (1 / 4 : ℝ) ≠ 0 :=
      (Real.rpow_ne_zero hxnonneg (by norm_num : (1 / 4 : ℝ) ≠ 0)).2 hx.ne'
    have hsqrt_eq : Real.sqrt x = x ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow x
    calc
      (Real.log x / x ^ (1 / 4 : ℝ)) *
          (Real.log x / x ^ (1 / 4 : ℝ))
          = (Real.log x)^2 / (x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ)) := by
            field_simp [hxpow_ne]
      _ = (Real.log x)^2 / x ^ (1 / 2 : ℝ) := by
            rw [← Real.rpow_add hx]
            norm_num
      _ = (Real.log x)^2 / Real.sqrt x := by
            rw [hsqrt_eq]
  simpa using hsq.congr' heq

lemma sqrt_mul_log_sq_isLittleO_id :
    (fun x : ℝ => Real.sqrt x * (Real.log x)^2)
      =o[atTop] (fun x : ℝ => x) := by
  have hratio :
      Tendsto (fun x : ℝ => Real.sqrt x * (Real.log x)^2 / x) atTop (𝓝 0) := by
    have heq :
        (fun x : ℝ => Real.sqrt x * (Real.log x)^2 / x)
          =ᶠ[atTop] fun x : ℝ => (Real.log x)^2 / Real.sqrt x := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have hsqrt_pos : Real.sqrt x ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.2 hx)
      have hx_eq : (Real.sqrt x)^2 = x :=
        Real.sq_sqrt (le_of_lt hx)
      calc
        Real.sqrt x * (Real.log x)^2 / x
            = Real.sqrt x * (Real.log x)^2 / (Real.sqrt x)^2 := by
                rw [hx_eq]
        _ = (Real.log x)^2 / Real.sqrt x := by
                field_simp [hsqrt_pos]
    exact log_sq_div_sqrt_tendsto_zero.congr' heq.symm
  refine (isLittleO_iff_tendsto' ?_).2 hratio
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx hzero
  exact (hx.ne' hzero).elim

lemma sqrt_mul_log_isLittleO_logIntegral :
    (fun x : ℝ => Real.sqrt x * Real.log x)
      =o[atTop] (fun x : ℝ => logIntegral x) := by
  have hnum :
      Tendsto (fun x : ℝ => Real.sqrt x * (Real.log x)^2 / x) atTop (𝓝 0) := by
    have heq :
        (fun x : ℝ => Real.sqrt x * (Real.log x)^2 / x)
          =ᶠ[atTop] fun x : ℝ => (Real.log x)^2 / Real.sqrt x := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have hsqrt_pos : Real.sqrt x ≠ 0 := by
        exact ne_of_gt (Real.sqrt_pos.2 hx)
      have hx_eq : (Real.sqrt x)^2 = x :=
        Real.sq_sqrt (le_of_lt hx)
      calc
        Real.sqrt x * (Real.log x)^2 / x
            = Real.sqrt x * (Real.log x)^2 / (Real.sqrt x)^2 := by
                rw [hx_eq]
        _ = (Real.log x)^2 / Real.sqrt x := by
                field_simp [hsqrt_pos]
    exact log_sq_div_sqrt_tendsto_zero.congr' heq.symm
  have hden : Tendsto (fun x : ℝ => logIntegral x * Real.log x / x) atTop (𝓝 1) :=
    logIntegral_asymptotic
  have hratio :
      Tendsto
        (fun x : ℝ =>
          (Real.sqrt x * (Real.log x)^2 / x) /
            (logIntegral x * Real.log x / x))
        atTop (𝓝 0) := by
    simpa using hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
  have heq :
      (fun x : ℝ =>
          (Real.sqrt x * (Real.log x)^2 / x) /
            (logIntegral x * Real.log x / x))
        =ᶠ[atTop] fun x : ℝ => (Real.sqrt x * Real.log x) / logIntegral x := by
    filter_upwards [eventually_ge_atTop (3 : ℝ)] with x hx
    have hxpos : x ≠ 0 := by linarith
    have hlog_pos : Real.log x ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
    have hli_pos : logIntegral x ≠ 0 := ne_of_gt (logIntegral_pos (by linarith))
    field_simp [hxpos, hlog_pos, hli_pos]
  refine (isLittleO_iff_tendsto' ?_).2 (hratio.congr' heq)
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with x hx hzero
  have hli_ne : logIntegral x ≠ 0 := ne_of_gt (logIntegral_pos (by linarith))
  exact (hli_ne hzero).elim

lemma RH_PrimeCountingLiErrorBound.isLittleO_logIntegral
    (h : RH_PrimeCountingLiErrorBound) :
    (fun x : ℝ => (primeCounting x : ℝ) - logIntegral x)
      =o[atTop] (fun x : ℝ => logIntegral x) := by
  rw [RH_PrimeCountingLiErrorBound] at h
  exact h.trans_isLittleO sqrt_mul_log_isLittleO_logIntegral

lemma RH_PrimeCountingLiErrorBound.isLittleO_id
    (h : RH_PrimeCountingLiErrorBound) :
    (fun x : ℝ => (primeCounting x : ℝ) - logIntegral x)
      =o[atTop] (fun x : ℝ => x) :=
  h.isLittleO_logIntegral.trans logIntegral_isLittleO_id

lemma PNTForm2_of_RH_PrimeCountingLiErrorBound
    (h : RH_PrimeCountingLiErrorBound) : PNTForm2 := by
  have hsmall := h.isLittleO_logIntegral
  have hratio := hsmall.tendsto_div_nhds_zero
  have hsum :
      Tendsto
        (fun x : ℝ =>
          1 + ((primeCounting x : ℝ) - logIntegral x) / logIntegral x)
        atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add hratio :
      Tendsto
        (fun x : ℝ =>
          (1 : ℝ) + ((primeCounting x : ℝ) - logIntegral x) / logIntegral x)
        atTop (𝓝 ((1 : ℝ) + 0)))
  have heq :
      (fun x : ℝ =>
          1 + ((primeCounting x : ℝ) - logIntegral x) / logIntegral x)
        =ᶠ[atTop] fun x : ℝ => (primeCounting x : ℝ) / logIntegral x := by
    filter_upwards [eventually_ge_atTop (3 : ℝ)] with x hx
    have hli_ne : logIntegral x ≠ 0 := ne_of_gt (logIntegral_pos (by linarith))
    field_simp [hli_ne]
    ring
  exact hsum.congr' heq

lemma PNTForm1_of_RH_PrimeCountingLiErrorBound
    (h : RH_PrimeCountingLiErrorBound) : PNTForm1 :=
  PNTForm1_of_PNTForm2 (PNTForm2_of_RH_PrimeCountingLiErrorBound h)

lemma PNTForm3_of_RH_PrimeCountingLiErrorBound
    (h : RH_PrimeCountingLiErrorBound) : PNTForm3 :=
  PNTForm3_of_PNTForm2 (PNTForm2_of_RH_PrimeCountingLiErrorBound h)

lemma PNTForm2_of_RH_ErrorBound (h : RH_ErrorBound) : PNTForm2 :=
  PNTForm2_of_RH_PrimeCountingLiErrorBound
    (RH_PrimeCountingLiErrorBound_of_RH_ErrorBound h)

lemma PNTForm1_of_RH_ErrorBound (h : RH_ErrorBound) : PNTForm1 :=
  PNTForm1_of_PNTForm2 (PNTForm2_of_RH_ErrorBound h)

lemma PNTForm3_of_RH_ErrorBound (h : RH_ErrorBound) : PNTForm3 :=
  PNTForm3_of_PNTForm2 (PNTForm2_of_RH_ErrorBound h)

lemma RH_PsiErrorBound.isLittleO_id
    (h : RH_PsiErrorBound) :
    (fun x : ℝ => chebyshevPsi x - x) =o[atTop] (fun x : ℝ => x) := by
  rw [RH_PsiErrorBound] at h
  exact h.trans_isLittleO sqrt_mul_log_sq_isLittleO_id

lemma PNTForm3_of_RH_PsiErrorBound (h : RH_PsiErrorBound) : PNTForm3 := by
  have hsmall := h.isLittleO_id
  have hratio := hsmall.tendsto_div_nhds_zero
  have hsum :
      Tendsto (fun x : ℝ => 1 + (chebyshevPsi x - x) / x) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add hratio :
      Tendsto (fun x : ℝ => (1 : ℝ) + (chebyshevPsi x - x) / x)
        atTop (𝓝 ((1 : ℝ) + 0)))
  have heq :
      (fun x : ℝ => 1 + (chebyshevPsi x - x) / x)
        =ᶠ[atTop] fun x : ℝ => chebyshevPsi x / x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hx_ne : x ≠ 0 := hx.ne'
    field_simp [hx_ne]
    ring
  exact hsum.congr' heq

lemma PNTForm2_of_RH_PsiErrorBound (h : RH_PsiErrorBound) : PNTForm2 :=
  PNTForm2_of_PNTForm3 (PNTForm3_of_RH_PsiErrorBound h)

lemma PNTForm1_of_RH_PsiErrorBound (h : RH_PsiErrorBound) : PNTForm1 :=
  PNTForm1_of_PNTForm3 (PNTForm3_of_RH_PsiErrorBound h)

lemma PNTForm3_of_RH_ThetaErrorBound (h : RH_ThetaErrorBound) : PNTForm3 :=
  PNTForm3_of_RH_PsiErrorBound (RH_PsiErrorBound_of_RH_ThetaErrorBound h)

lemma PNTForm2_of_RH_ThetaErrorBound (h : RH_ThetaErrorBound) : PNTForm2 :=
  PNTForm2_of_PNTForm3 (PNTForm3_of_RH_ThetaErrorBound h)

lemma PNTForm1_of_RH_ThetaErrorBound (h : RH_ThetaErrorBound) : PNTForm1 :=
  PNTForm1_of_PNTForm3 (PNTForm3_of_RH_ThetaErrorBound h)

lemma PNTForms_of_RH_PrimeCountingLiErrorBound
    (h : RH_PrimeCountingLiErrorBound) :
    PNTForm1 ∧ PNTForm2 ∧ PNTForm3 :=
  ⟨PNTForm1_of_RH_PrimeCountingLiErrorBound h,
    PNTForm2_of_RH_PrimeCountingLiErrorBound h,
    PNTForm3_of_RH_PrimeCountingLiErrorBound h⟩

lemma PNTForms_of_RH_ErrorBound (h : RH_ErrorBound) :
    PNTForm1 ∧ PNTForm2 ∧ PNTForm3 :=
  PNTForms_of_RH_PrimeCountingLiErrorBound
    (RH_PrimeCountingLiErrorBound_of_RH_ErrorBound h)

lemma PNTForms_of_RH_PsiErrorBound (h : RH_PsiErrorBound) :
    PNTForm1 ∧ PNTForm2 ∧ PNTForm3 :=
  ⟨PNTForm1_of_RH_PsiErrorBound h,
    PNTForm2_of_RH_PsiErrorBound h,
    PNTForm3_of_RH_PsiErrorBound h⟩

lemma PNTForms_of_RH_ThetaErrorBound (h : RH_ThetaErrorBound) :
    PNTForm1 ∧ PNTForm2 ∧ PNTForm3 :=
  PNTForms_of_RH_PsiErrorBound (RH_PsiErrorBound_of_RH_ThetaErrorBound h)

/-- Target statement: RH iff the RH-scale prime-counting error bound.

This is a standard deep equivalence, but the current project does not provide
the analytic machinery needed to prove it.  Keeping it as a `Prop` records the
target without claiming a proof.
-/
def rh_iff_optimal_error : Prop :=
  RiemannHypothesis.Statement ↔ RH_PrimeCountingLiErrorBound

lemma rh_iff_optimal_error_iff :
    rh_iff_optimal_error ↔
      (RiemannHypothesis.Statement ↔ RH_PrimeCountingLiErrorBound) := by
  rfl

lemma rh_iff_pointwise_error_iff :
    rh_iff_optimal_error ↔
      (RiemannHypothesis.Statement ↔ RH_ErrorBound) := by
  constructor
  · intro h
    constructor
    · intro hRH
      exact RH_ErrorBound_of_RH_PrimeCountingLiErrorBound (h.mp hRH)
    · intro herror
      exact h.mpr (RH_PrimeCountingLiErrorBound_of_RH_ErrorBound herror)
  · intro h
    constructor
    · intro hRH
      exact RH_PrimeCountingLiErrorBound_of_RH_ErrorBound (h.mp hRH)
    · intro herror
      exact h.mpr (RH_ErrorBound_of_RH_PrimeCountingLiErrorBound herror)

/-- Pointwise version of the RH/error equivalence target from two supplied
implications.  This is just the already-proved pointwise/Big-O bridge wrapped
around the target interface. -/
lemma rh_iff_optimal_error_of_pointwise_implications
    (h_forward : RiemannHypothesis.Statement → RH_ErrorBound)
    (h_reverse : RH_ErrorBound → RiemannHypothesis.Statement) :
    rh_iff_optimal_error :=
  (rh_iff_pointwise_error_iff).mpr ⟨h_forward, h_reverse⟩

/-- Packaging lemma for the RH/error equivalence target.

The hard work remains the two implications supplied as hypotheses; this lemma
keeps later developments from reopening the definition of the target. -/
lemma rh_iff_optimal_error_of_implications
    (h_forward : RiemannHypothesis.Statement → RH_PrimeCountingLiErrorBound)
    (h_reverse : RH_PrimeCountingLiErrorBound → RiemannHypothesis.Statement) :
    rh_iff_optimal_error :=
  ⟨h_forward, h_reverse⟩

lemma RH_PrimeCountingLiErrorBound_of_rh_iff_optimal_error
    (h : rh_iff_optimal_error) :
    RiemannHypothesis.Statement → RH_PrimeCountingLiErrorBound :=
  h.mp

lemma RiemannHypothesis_of_rh_iff_optimal_error
    (h : rh_iff_optimal_error) :
    RH_PrimeCountingLiErrorBound → RiemannHypothesis.Statement :=
  h.mpr

lemma RH_ErrorBound_of_rh_iff_optimal_error
    (h : rh_iff_optimal_error) :
    RiemannHypothesis.Statement → RH_ErrorBound := by
  intro hRH
  exact RH_ErrorBound_of_RH_PrimeCountingLiErrorBound (h.mp hRH)

lemma PNTForm2_of_rh_iff_optimal_error
    (h : rh_iff_optimal_error) :
    RiemannHypothesis.Statement → PNTForm2 := by
  intro hRH
  exact PNTForm2_of_RH_PrimeCountingLiErrorBound (h.mp hRH)

lemma PNTForm1_of_rh_iff_optimal_error
    (h : rh_iff_optimal_error) :
    RiemannHypothesis.Statement → PNTForm1 := by
  intro hRH
  exact PNTForm1_of_RH_PrimeCountingLiErrorBound (h.mp hRH)

lemma PNTForm3_of_rh_iff_optimal_error
    (h : rh_iff_optimal_error) :
    RiemannHypothesis.Statement → PNTForm3 := by
  intro hRH
  exact PNTForm3_of_RH_PrimeCountingLiErrorBound (h.mp hRH)

lemma RiemannHypothesis_of_rh_iff_pointwise_error
    (h : rh_iff_optimal_error) :
    RH_ErrorBound → RiemannHypothesis.Statement := by
  intro herror
  exact h.mpr (RH_PrimeCountingLiErrorBound_of_RH_ErrorBound herror)

/-! ## 零点对称性 -/

/-- 非平凡零点在 s ↦ 1-s 下对称：若 ζ(ρ) = 0 且 0 < Re(ρ) < 1，则 ζ(1-ρ) = 0。
    直接由函数方程 ζ(1-s) = 2(2π)^{-s} Γ(s) cos(πs/2) ζ(s) 得出。 -/
theorem nontrivial_zero_symmetric {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (hre : 0 < ρ.re) (hre' : ρ.re < 1) : riemannZeta (1 - ρ) = 0 := by
  have hρ_nat : ∀ n : ℕ, ρ ≠ -(n : ℂ) := by
    intro n h
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
          simp [Complex.mul_re, Complex.intCast_re, Complex.intCast_im] at this
          linarith
        have hk0 : k = 0 := by
          have hk_ge : (0 : ℤ) ≤ k := by
            by_contra h; push Not at h
            have : (k : ℝ) < 0 := by exact_mod_cast h
            linarith
          omega
        exact hs0 (by rw [hs_eq, hk0]; simp)
      · push Not at hk_le
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
    (hζ : riemannZeta s = 0) (hnt : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) (_hs1 : s ≠ 1) :
    0 < s.re ∧ s.re < 1 := by
  constructor
  · by_contra h
    push Not at h
    exact riemannZeta_ne_zero_of_re_le_zero (by linarith : s.re ≤ 0)
      (by intro n hn; exact hnt ⟨n, hn⟩) hζ
  · by_contra h
    push Not at h
    exact riemannZeta_ne_zero_of_one_le_re h hζ

/-- ζ 的零点不能在 `1` 以外的点聚集。 -/
lemma riemannZeta_not_frequently_zero_nhdsNE_of_ne_one {x : ℂ} (hx : x ≠ 1) :
    ¬ ∃ᶠ z in 𝓝[≠] x, riemannZeta z = 0 := by
  intro hfreq
  have hdiff : DifferentiableOn ℂ riemannZeta ({(1 : ℂ)}ᶜ : Set ℂ) := by
    intro z hz
    exact (differentiableAt_riemannZeta (by simpa using hz)).differentiableWithinAt
  have han : AnalyticOnNhd ℂ riemannZeta ({(1 : ℂ)}ᶜ : Set ℂ) :=
    hdiff.analyticOnNhd isOpen_compl_singleton
  have hpre : IsPreconnected ({(1 : ℂ)}ᶜ : Set ℂ) := by
    exact (isConnected_compl_singleton_of_one_lt_rank (E := ℂ)
      (by rw [Complex.rank_real_complex]; norm_num) (1 : ℂ)).isPreconnected
  have hxmem : x ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by
    simpa using hx
  have heq := han.eqOn_zero_of_preconnected_of_frequently_eq_zero hpre hxmem hfreq
  have h2zero : riemannZeta (2 : ℂ) = 0 := by
    have h2mem : (2 : ℂ) ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by norm_num
    simpa using heq h2mem
  exact riemannZeta_ne_zero_of_one_lt_re (s := (2 : ℂ)) (by norm_num) h2zero

/-- 任意有界高度内仅有有限多个非平凡零点。 -/
theorem finite_nontrivial_zeros_bounded_height (T : ℝ) :
    Set.Finite {s : ℂ | RiemannHypothesis.IsNontrivialZero s ∧ |s.im| ≤ T} := by
  classical
  let S : Set ℂ := {s : ℂ | RiemannHypothesis.IsNontrivialZero s ∧ |s.im| ≤ T}
  let K : Set ℂ := Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc (-|T|) |T|
  have hK_compact : IsCompact K := by
    refine (Metric.isCompact_iff_isClosed_bounded (s := K)).mpr ⟨?_, ?_⟩
    · exact IsClosed.reProdIm isClosed_Icc isClosed_Icc
    · exact Bornology.IsBounded.reProdIm (Metric.isBounded_Icc (0 : ℝ) 1)
        (Metric.isBounded_Icc (-|T|) |T|)
  have hS_sub_K : S ⊆ K := by
    intro z hz
    rcases hz with ⟨hznt, him⟩
    rcases hznt with ⟨_hζ, hre0, hre1⟩
    rw [Complex.mem_reProdIm]
    constructor
    · exact ⟨le_of_lt hre0, le_of_lt hre1⟩
    · have him_abs : |z.im| ≤ |T| := le_trans him (le_abs_self T)
      exact abs_le.mp him_abs
  by_contra hfin
  have hS_inf : S.Infinite := Set.not_finite.mp hfin
  obtain ⟨x, _hxK, hxacc⟩ := hS_inf.exists_accPt_of_subset_isCompact hK_compact hS_sub_K
  have hfreqS : ∃ᶠ z in 𝓝[≠] x, z ∈ S := accPt_iff_frequently_nhdsNE.mp hxacc
  have hfreqZ : ∃ᶠ z in 𝓝[≠] x, riemannZeta z = 0 := by
    exact hfreqS.mono fun _z hz => hz.1.1
  by_cases hx1 : x = 1
  · subst x
    have hmul_ne : ∀ᶠ z in 𝓝[≠] (1 : ℂ), (z - 1) * riemannZeta z ≠ 0 :=
      riemannZeta_residue_one.eventually_ne one_ne_zero
    obtain ⟨_z, hz_zero, hz_prod_ne⟩ := (hfreqZ.and_eventually hmul_ne).exists
    exact hz_prod_ne (by rw [hz_zero, mul_zero])
  · exact riemannZeta_not_frequently_zero_nhdsNE_of_ne_one hx1 hfreqZ

/-- Hardy's infinite critical-line zero target implies that the corresponding
real heights are unbounded in absolute value.

The nontrivial input is `finite_nontrivial_zeros_bounded_height`: infinitely
many real critical-line zeros cannot all lie in a bounded vertical strip. -/
theorem hardy_zeros_abs_unbounded_of_hardy_theorem_target
    (h : HardyTheorem.hardy_theorem_target) :
    HardyTheorem.hardy_zeros_abs_unbounded_target := by
  by_contra hnot
  rw [HardyTheorem.hardy_zeros_abs_unbounded_target] at hnot
  push Not at hnot
  rcases hnot with ⟨T, hT⟩
  let linePoint : ℝ → ℂ := fun t => (0.5 : ℂ) + I * t
  let realZeros : Set ℝ := {t : ℝ | riemannZeta (linePoint t) = 0}
  have hreal_inf : realZeros.Infinite := by
    simpa [HardyTheorem.hardy_theorem_target, realZeros, linePoint] using h
  have hcomplex_fin :
      (linePoint '' realZeros).Finite := by
    refine (finite_nontrivial_zeros_bounded_height T).subset ?_
    intro s hs
    rcases hs with ⟨t, ht, rfl⟩
    have ht_bound_lt : |t| < T := by
      by_contra hle
      exact hT t (le_of_not_gt hle) ht
    refine ⟨?_, le_of_lt ?_⟩
    · refine ⟨ht, ?_, ?_⟩
      · norm_num [linePoint]
      · norm_num [linePoint]
    · have him : (linePoint t).im = t := by norm_num [linePoint]
      simpa [him] using ht_bound_lt
  have hinj : Set.InjOn linePoint realZeros := by
    intro t₁ _ t₂ _ h_eq
    have him := congr_arg Complex.im h_eq
    simp [linePoint] at him
    exact him
  have hreal_fin : realZeros.Finite := Set.Finite.of_finite_image hcomplex_fin hinj
  exact hreal_inf hreal_fin

theorem hardy_theorem_target_iff_abs_unbounded :
    HardyTheorem.hardy_theorem_target ↔
      HardyTheorem.hardy_zeros_abs_unbounded_target :=
  ⟨hardy_zeros_abs_unbounded_of_hardy_theorem_target,
    HardyTheorem.hardy_theorem_target_of_abs_unbounded⟩

/-- Hardy's infinite-zero target also forces arbitrarily large positive
critical-line zero heights. -/
theorem hardy_zeros_unbounded_of_hardy_theorem_target
    (h : HardyTheorem.hardy_theorem_target) :
    HardyTheorem.hardy_zeros_unbounded_target :=
  HardyTheorem.hardy_zeros_unbounded_iff_abs_unbounded.mpr
    (hardy_zeros_abs_unbounded_of_hardy_theorem_target h)

theorem hardy_theorem_target_iff_unbounded :
    HardyTheorem.hardy_theorem_target ↔
      HardyTheorem.hardy_zeros_unbounded_target :=
  ⟨hardy_zeros_unbounded_of_hardy_theorem_target,
    HardyTheorem.hardy_theorem_target_of_unbounded⟩

theorem hardy_theorem_target_of_two_signed_moments
    (hmom : HardyTheorem.hardy_two_signed_moments_target) :
    HardyTheorem.hardy_theorem_target :=
  HardyTheorem.hardy_theorem_target_of_two_signed_moments hmom

theorem hardy_theorem_target_of_integral_asymptotic_one_two
    (h1 : HardyTheorem.integral_asymptotic_target 1)
    (h2 : HardyTheorem.integral_asymptotic_target 2) :
    HardyTheorem.hardy_theorem_target :=
  HardyTheorem.hardy_theorem_target_of_integral_asymptotic_one_two h1 h2

/-- The first two Hardy signed moments force arbitrarily large absolute-height
critical-line zeros at the PrimeNumberTheorem layer. -/
theorem hardy_zeros_abs_unbounded_of_two_signed_moments
    (hmom : HardyTheorem.hardy_two_signed_moments_target) :
    HardyTheorem.hardy_zeros_abs_unbounded_target :=
  hardy_zeros_abs_unbounded_of_hardy_theorem_target
    (HardyTheorem.hardy_theorem_target_of_two_signed_moments hmom)

/-- The first two Hardy signed moments also force arbitrarily large positive
critical-line zero heights. -/
theorem hardy_zeros_unbounded_of_two_signed_moments
    (hmom : HardyTheorem.hardy_two_signed_moments_target) :
    HardyTheorem.hardy_zeros_unbounded_target :=
  hardy_zeros_unbounded_of_hardy_theorem_target
    (HardyTheorem.hardy_theorem_target_of_two_signed_moments hmom)

/-- The first two Hardy integral asymptotics force arbitrarily large
absolute-height critical-line zeros at the PrimeNumberTheorem layer. -/
theorem hardy_zeros_abs_unbounded_of_integral_asymptotic_one_two
    (h1 : HardyTheorem.integral_asymptotic_target 1)
    (h2 : HardyTheorem.integral_asymptotic_target 2) :
    HardyTheorem.hardy_zeros_abs_unbounded_target :=
  hardy_zeros_abs_unbounded_of_hardy_theorem_target
    (HardyTheorem.hardy_theorem_target_of_integral_asymptotic_one_two h1 h2)

/-- The first two Hardy integral asymptotics also force arbitrarily large
positive critical-line zero heights. -/
theorem hardy_zeros_unbounded_of_integral_asymptotic_one_two
    (h1 : HardyTheorem.integral_asymptotic_target 1)
    (h2 : HardyTheorem.integral_asymptotic_target 2) :
    HardyTheorem.hardy_zeros_unbounded_target :=
  hardy_zeros_unbounded_of_hardy_theorem_target
    (HardyTheorem.hardy_theorem_target_of_integral_asymptotic_one_two h1 h2)

/-- The Hardy--Littlewood linear lower bound for the number of critical-line
zeros up to height `T` forces those zeros to have unbounded absolute height.

The proof is purely set-theoretic once the lower bound and local finiteness of
nontrivial zeros are available: if every critical-line zero had `|t| < B`, then
`zeroCountOnCriticalLine T` would inject into the finite set of nontrivial zeros
with `|Im s| ≤ B`, while the assumed lower bound makes the count exceed that
fixed finite cardinal for sufficiently large `T`. -/
theorem hardy_zeros_abs_unbounded_of_hardy_littlewood_lower_bound
    (h : HardyTheorem.hardy_littlewood_lower_bound_target) :
    HardyTheorem.hardy_zeros_abs_unbounded_target := by
  classical
  by_contra hnot
  rw [HardyTheorem.hardy_zeros_abs_unbounded_target] at hnot
  push Not at hnot
  rcases hnot with ⟨B, hB⟩
  rcases h with ⟨C, hC_pos, T0, hbound⟩
  let linePoint : ℝ → ℂ := fun t => (0.5 : ℂ) + I * t
  let boundedZeros : Set ℂ :=
    {s : ℂ | RiemannHypothesis.IsNontrivialZero s ∧ |s.im| ≤ B}
  let N : ℕ := boundedZeros.ncard
  let T : ℝ := max T0 (max 0 (((N : ℝ) + 1) / C))
  have hT0 : T0 ≤ T := le_max_left T0 (max 0 (((N : ℝ) + 1) / C))
  have hT_large : ((N : ℝ) + 1) / C ≤ T := by
    exact le_trans (le_max_right 0 (((N : ℝ) + 1) / C))
      (le_max_right T0 (max 0 (((N : ℝ) + 1) / C)))
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
  have hfinite_bounded : boundedZeros.Finite := by
    simpa [boundedZeros] using finite_nontrivial_zeros_bounded_height B
  let countedZeros : Set (Set.Icc (0 : ℝ) T) :=
    {t : Set.Icc (0 : ℝ) T | riemannZeta (linePoint (t : ℝ)) = 0}
  have hcount_le_N_nat : HardyTheorem.zeroCountOnCriticalLine T ≤ N := by
    have hle :=
      Set.ncard_le_ncard_of_injOn
        (fun t : Set.Icc (0 : ℝ) T => linePoint (t : ℝ))
        (s := countedZeros) (t := boundedZeros) ?_ ?_ hfinite_bounded
    · simpa [HardyTheorem.zeroCountOnCriticalLine, countedZeros, linePoint,
        boundedZeros, N] using hle
    · intro t ht
      have htzero : riemannZeta (linePoint (t : ℝ)) = 0 := ht
      have ht_abs_le : |(t : ℝ)| ≤ B := by
        by_contra hle
        exact hB (t : ℝ) (le_of_lt (lt_of_not_ge hle)) htzero
      refine ⟨?_, ?_⟩
      · refine ⟨htzero, ?_, ?_⟩
        · norm_num [linePoint]
        · norm_num [linePoint]
      · have him : (linePoint (t : ℝ)).im = (t : ℝ) := by
          norm_num [linePoint]
        simpa [him] using ht_abs_le
    · intro t₁ _ t₂ _ heq
      apply Subtype.ext
      have him := congr_arg Complex.im heq
      simpa [linePoint] using him
  have hcount_le_N : (HardyTheorem.zeroCountOnCriticalLine T : ℝ) ≤ N := by
    exact_mod_cast hcount_le_N_nat
  have hcount_lower := hbound T hT0
  linarith

/-- The Hardy--Littlewood lower-bound target also gives arbitrarily large
positive critical-line zero heights, using the functional-equation symmetry
formalized in `HardyTheorem`. -/
theorem hardy_zeros_unbounded_of_hardy_littlewood_lower_bound
    (h : HardyTheorem.hardy_littlewood_lower_bound_target) :
    HardyTheorem.hardy_zeros_unbounded_target :=
  HardyTheorem.hardy_zeros_unbounded_iff_abs_unbounded.mpr
    (hardy_zeros_abs_unbounded_of_hardy_littlewood_lower_bound h)

/-- The Hardy--Littlewood lower-bound target implies Hardy's infinite-zero
target via the unbounded-height bridge. -/
theorem hardy_theorem_target_of_hardy_littlewood_lower_bound
    (h : HardyTheorem.hardy_littlewood_lower_bound_target) :
    HardyTheorem.hardy_theorem_target :=
  HardyTheorem.hardy_theorem_target_of_abs_unbounded
    (hardy_zeros_abs_unbounded_of_hardy_littlewood_lower_bound h)

/-- Selberg's positive-proportion target is stronger than Hardy's
unbounded-height target. -/
theorem hardy_zeros_abs_unbounded_of_selberg_zero_proportion
    (h : HardyTheorem.selberg_zero_proportion_target) :
    HardyTheorem.hardy_zeros_abs_unbounded_target :=
  hardy_zeros_abs_unbounded_of_hardy_littlewood_lower_bound
    (HardyTheorem.hardy_littlewood_lower_bound_target_of_selberg_zero_proportion h)

/-- Selberg's positive-proportion target gives arbitrarily large positive
critical-line zero heights. -/
theorem hardy_zeros_unbounded_of_selberg_zero_proportion
    (h : HardyTheorem.selberg_zero_proportion_target) :
    HardyTheorem.hardy_zeros_unbounded_target :=
  hardy_zeros_unbounded_of_hardy_littlewood_lower_bound
    (HardyTheorem.hardy_littlewood_lower_bound_target_of_selberg_zero_proportion h)

/-- Selberg's positive-proportion target implies Hardy's infinite-zero target. -/
theorem hardy_theorem_target_of_selberg_zero_proportion
    (h : HardyTheorem.selberg_zero_proportion_target) :
    HardyTheorem.hardy_theorem_target :=
  HardyTheorem.hardy_theorem_target_of_abs_unbounded
    (hardy_zeros_abs_unbounded_of_selberg_zero_proportion h)

theorem hardy_theorem_target_of_conrey_40_percent_target
    (h : KnownResults.conrey_40_percent_zeros_on_critical_line_target) :
    HardyTheorem.hardy_theorem_target :=
  hardy_theorem_target_of_selberg_zero_proportion
    (KnownResults.conrey_40_percent_zeros_on_critical_line_target_iff_selberg.mp h)

theorem hardy_zeros_abs_unbounded_of_conrey_40_percent_target
    (h : KnownResults.conrey_40_percent_zeros_on_critical_line_target) :
    HardyTheorem.hardy_zeros_abs_unbounded_target :=
  hardy_zeros_abs_unbounded_of_selberg_zero_proportion
    (KnownResults.conrey_40_percent_zeros_on_critical_line_target_iff_selberg.mp h)

theorem hardy_zeros_unbounded_of_conrey_40_percent_target
    (h : KnownResults.conrey_40_percent_zeros_on_critical_line_target) :
    HardyTheorem.hardy_zeros_unbounded_target :=
  hardy_zeros_unbounded_of_selberg_zero_proportion
    (KnownResults.conrey_40_percent_zeros_on_critical_line_target_iff_selberg.mp h)

theorem infinitely_many_zeros_on_critical_line_of_selberg_zero_proportion
    (h : HardyTheorem.selberg_zero_proportion_target) :
    {s : ℂ | s.re = 1 / 2 ∧ riemannZeta s = 0}.Infinite :=
  KnownResults.infinitely_many_zeros_on_critical_line
    (hardy_theorem_target_of_selberg_zero_proportion h)

theorem infinitely_many_zeros_on_critical_line_of_two_signed_moments
    (hmom : HardyTheorem.hardy_two_signed_moments_target) :
    {s : ℂ | s.re = 1 / 2 ∧ riemannZeta s = 0}.Infinite :=
  KnownResults.infinitely_many_zeros_on_critical_line
    (HardyTheorem.hardy_theorem_target_of_two_signed_moments hmom)

theorem infinitely_many_zeros_on_critical_line_of_integral_asymptotic_one_two
    (h1 : HardyTheorem.integral_asymptotic_target 1)
    (h2 : HardyTheorem.integral_asymptotic_target 2) :
    {s : ℂ | s.re = 1 / 2 ∧ riemannZeta s = 0}.Infinite :=
  KnownResults.infinitely_many_zeros_on_critical_line
    (HardyTheorem.hardy_theorem_target_of_integral_asymptotic_one_two h1 h2)

theorem infinitely_many_zeros_on_critical_line_of_hardy_littlewood_lower_bound
    (h : HardyTheorem.hardy_littlewood_lower_bound_target) :
    {s : ℂ | s.re = 1 / 2 ∧ riemannZeta s = 0}.Infinite :=
  KnownResults.infinitely_many_zeros_on_critical_line
    (hardy_theorem_target_of_hardy_littlewood_lower_bound h)

theorem infinitely_many_zeros_on_critical_line_of_conrey_40_percent_target
    (h : KnownResults.conrey_40_percent_zeros_on_critical_line_target) :
    {s : ℂ | s.re = 1 / 2 ∧ riemannZeta s = 0}.Infinite :=
  KnownResults.infinitely_many_zeros_on_critical_line
    (hardy_theorem_target_of_conrey_40_percent_target h)

theorem exists_zero_on_critical_line_of_hardy_littlewood_lower_bound
    (h : HardyTheorem.hardy_littlewood_lower_bound_target) :
    ∃ t : ℝ, riemannZeta (0.5 + I * t) = 0 :=
  HardyTheorem.exists_zero_on_critical_line_of_hardy_littlewood_lower_bound h

theorem exists_zero_on_critical_line_of_two_signed_moments
    (hmom : HardyTheorem.hardy_two_signed_moments_target) :
    ∃ t : ℝ, riemannZeta (0.5 + I * t) = 0 :=
  HardyTheorem.exists_zero_on_critical_line_of_two_signed_moments hmom

theorem exists_zero_on_critical_line_of_integral_asymptotic_one_two
    (h1 : HardyTheorem.integral_asymptotic_target 1)
    (h2 : HardyTheorem.integral_asymptotic_target 2) :
    ∃ t : ℝ, riemannZeta (0.5 + I * t) = 0 :=
  HardyTheorem.exists_zero_on_critical_line_of_integral_asymptotic_one_two h1 h2

theorem exists_zero_on_critical_line_of_selberg_zero_proportion
    (h : HardyTheorem.selberg_zero_proportion_target) :
    ∃ t : ℝ, riemannZeta (0.5 + I * t) = 0 :=
  HardyTheorem.exists_zero_on_critical_line_of_selberg_zero_proportion h

theorem exists_zero_on_critical_line_of_conrey_40_percent_target
    (h : KnownResults.conrey_40_percent_zeros_on_critical_line_target) :
    ∃ t : ℝ, riemannZeta (0.5 + I * t) = 0 :=
  HardyTheorem.exists_zero_on_critical_line_of_selberg_zero_proportion
    (KnownResults.conrey_40_percent_zeros_on_critical_line_target_iff_selberg.mp h)

/-- RH 等价于所有非平凡零点满足 Re = 1/2 -/
theorem rh_iff_nontrivial_zeros_on_line :
    RiemannHypothesis ↔
      ∀ s : ℂ, RiemannHypothesis.IsNontrivialZero s → s.re = 1 / 2 := by
  constructor
  · intro hRH s ⟨hζ, hre, hre'⟩
    exact hRH s hζ
      (by intro ⟨n, hn⟩; have := congr_arg Complex.re hn
          simp [Complex.mul_re, Complex.natCast_re, Complex.add_re,
            Complex.one_re, Complex.neg_re, Complex.natCast_im] at this
          linarith)
      (by intro h; have := congr_arg Complex.re h; simp at this; linarith)
  · intro h s hζ hnt hs1
    have hcs := nontrivial_zero_in_critical_strip hζ hnt hs1
    exact h s ⟨hζ, hcs.1, hcs.2⟩

/-- 本项目的 RH 定义与 Mathlib 的等价 -/
theorem rh_statement_iff_mathlib :
    _root_.RiemannHypothesis ↔ RiemannHypothesis.Statement :=
  rh_iff_nontrivial_zeros_on_line

theorem rh_iff_optimal_error_of_mathlib_implications
    (h_forward : _root_.RiemannHypothesis → RH_PrimeCountingLiErrorBound)
    (h_reverse : RH_PrimeCountingLiErrorBound → _root_.RiemannHypothesis) :
    rh_iff_optimal_error :=
  rh_iff_optimal_error_of_implications
    (fun hRH => h_forward (rh_statement_iff_mathlib.mpr hRH))
    (fun herror => rh_statement_iff_mathlib.mp (h_reverse herror))

theorem rh_iff_optimal_error_of_mathlib_pointwise_implications
    (h_forward : _root_.RiemannHypothesis → RH_ErrorBound)
    (h_reverse : RH_ErrorBound → _root_.RiemannHypothesis) :
    rh_iff_optimal_error :=
  rh_iff_optimal_error_of_pointwise_implications
    (fun hRH => h_forward (rh_statement_iff_mathlib.mpr hRH))
    (fun herror => rh_statement_iff_mathlib.mp (h_reverse herror))

theorem RH_PrimeCountingLiErrorBound_of_mathlib_RH_of_rh_iff_optimal_error
    (h : rh_iff_optimal_error) :
    _root_.RiemannHypothesis → RH_PrimeCountingLiErrorBound := by
  intro hRH
  exact h.mp (rh_statement_iff_mathlib.mp hRH)

theorem RH_ErrorBound_of_mathlib_RH_of_rh_iff_optimal_error
    (h : rh_iff_optimal_error) :
    _root_.RiemannHypothesis → RH_ErrorBound := by
  intro hRH
  exact RH_ErrorBound_of_RH_PrimeCountingLiErrorBound
    (RH_PrimeCountingLiErrorBound_of_mathlib_RH_of_rh_iff_optimal_error h hRH)

theorem mathlib_RH_of_rh_iff_optimal_error
    (h : rh_iff_optimal_error) :
    RH_PrimeCountingLiErrorBound → _root_.RiemannHypothesis := by
  intro herror
  exact rh_statement_iff_mathlib.mpr (h.mpr herror)

theorem mathlib_RH_of_rh_iff_pointwise_error
    (h : rh_iff_optimal_error) :
    RH_ErrorBound → _root_.RiemannHypothesis := by
  intro herror
  exact mathlib_RH_of_rh_iff_optimal_error h
    (RH_PrimeCountingLiErrorBound_of_RH_ErrorBound herror)

theorem PNTForm2_of_mathlib_RH_of_rh_iff_optimal_error
    (h : rh_iff_optimal_error) :
    _root_.RiemannHypothesis → PNTForm2 := by
  intro hRH
  exact PNTForm2_of_RH_PrimeCountingLiErrorBound
    (RH_PrimeCountingLiErrorBound_of_mathlib_RH_of_rh_iff_optimal_error h hRH)

theorem PNTForm1_of_mathlib_RH_of_rh_iff_optimal_error
    (h : rh_iff_optimal_error) :
    _root_.RiemannHypothesis → PNTForm1 := by
  intro hRH
  exact PNTForm1_of_RH_PrimeCountingLiErrorBound
    (RH_PrimeCountingLiErrorBound_of_mathlib_RH_of_rh_iff_optimal_error h hRH)

theorem PNTForm3_of_mathlib_RH_of_rh_iff_optimal_error
    (h : rh_iff_optimal_error) :
    _root_.RiemannHypothesis → PNTForm3 := by
  intro hRH
  exact PNTForm3_of_RH_PrimeCountingLiErrorBound
    (RH_PrimeCountingLiErrorBound_of_mathlib_RH_of_rh_iff_optimal_error h hRH)

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

/-- Finset of nontrivial zeros up to height `T`.

This uses the already-proved local finiteness theorem.  A future exact
explicit formula should replace the unweighted sum below by a multiplicity-
weighted sum once the relevant meromorphic-order API is connected. -/
noncomputable def nontrivialZerosFinset (T : ℝ) : Finset ℂ :=
  (finite_nontrivial_zeros_bounded_height T).toFinset

/-- Height-truncated nontrivial-zero contribution. -/
noncomputable def finiteNontrivialZeroSum (x T : ℝ) : ℂ :=
  ∑ ρ ∈ nontrivialZerosFinset T, (x : ℂ) ^ ρ / ρ

lemma mem_nontrivialZerosFinset {ρ : ℂ} {T : ℝ} :
    ρ ∈ nontrivialZerosFinset T ↔
      RiemannHypothesis.IsNontrivialZero ρ ∧ |ρ.im| ≤ T := by
  unfold nontrivialZerosFinset
  exact Set.Finite.mem_toFinset (finite_nontrivial_zeros_bounded_height T)

lemma nontrivialZerosFinset_eq_empty_iff {T : ℝ} :
    nontrivialZerosFinset T = ∅ ↔
      ¬ ∃ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ ∧ |ρ.im| ≤ T := by
  constructor
  · intro hempty hzero
    rcases hzero with ⟨ρ, hρ⟩
    have hmem : ρ ∈ nontrivialZerosFinset T :=
      mem_nontrivialZerosFinset.mpr hρ
    rw [hempty] at hmem
    simp at hmem
  · intro hnone
    ext ρ
    constructor
    · intro hρ
      exact (hnone ⟨ρ, mem_nontrivialZerosFinset.mp hρ⟩).elim
    · simp

lemma nontrivialZerosFinset_nonempty_iff {T : ℝ} :
    (nontrivialZerosFinset T).Nonempty ↔
      ∃ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ ∧ |ρ.im| ≤ T := by
  constructor
  · intro hne
    rcases hne with ⟨ρ, hρ⟩
    exact ⟨ρ, mem_nontrivialZerosFinset.mp hρ⟩
  · intro hzero
    rcases hzero with ⟨ρ, hρ⟩
    exact ⟨ρ, mem_nontrivialZerosFinset.mpr hρ⟩

lemma nontrivial_zero_mem_nontrivialZerosFinset {ρ : ℂ} {T : ℝ}
    (hρ : RiemannHypothesis.IsNontrivialZero ρ) (hT : |ρ.im| ≤ T) :
    ρ ∈ nontrivialZerosFinset T :=
  mem_nontrivialZerosFinset.mpr ⟨hρ, hT⟩

lemma nontrivialZerosFinset_mono {T U : ℝ} (hTU : T ≤ U) {ρ : ℂ}
    (hρ : ρ ∈ nontrivialZerosFinset T) :
    ρ ∈ nontrivialZerosFinset U := by
  rcases mem_nontrivialZerosFinset.mp hρ with ⟨hzero, hheight⟩
  exact mem_nontrivialZerosFinset.mpr ⟨hzero, le_trans hheight hTU⟩

lemma nontrivialZerosFinset_sdiff_eq_empty_of_le
    {T U : ℝ} (hUT : U ≤ T) :
    nontrivialZerosFinset U \ nontrivialZerosFinset T = ∅ := by
  apply Finset.sdiff_eq_empty_iff_subset.mpr
  intro ρ hρ
  exact nontrivialZerosFinset_mono hUT hρ

lemma not_mem_nontrivialZerosFinset_of_height_lt {ρ : ℂ} {T : ℝ}
    (hT : T < |ρ.im|) :
    ρ ∉ nontrivialZerosFinset T := by
  intro hρ
  exact not_le_of_gt hT (mem_nontrivialZerosFinset.mp hρ).2

lemma mem_nontrivialZerosFinset_sdiff {ρ : ℂ} {T U : ℝ} :
    ρ ∈ (nontrivialZerosFinset U \ nontrivialZerosFinset T) ↔
      RiemannHypothesis.IsNontrivialZero ρ ∧ |ρ.im| ≤ U ∧ T < |ρ.im| := by
  constructor
  · intro hρ
    simp only [Finset.mem_sdiff] at hρ
    rcases mem_nontrivialZerosFinset.mp hρ.1 with ⟨hzero, hheightU⟩
    have hheightT : T < |ρ.im| := by
      by_contra hnot
      have hle : |ρ.im| ≤ T := le_of_not_gt hnot
      exact hρ.2 (mem_nontrivialZerosFinset.mpr ⟨hzero, hle⟩)
    exact ⟨hzero, hheightU, hheightT⟩
  · intro hρ
    rcases hρ with ⟨hzero, hheightU, hheightT⟩
    simp only [Finset.mem_sdiff]
    exact ⟨mem_nontrivialZerosFinset.mpr ⟨hzero, hheightU⟩,
      not_mem_nontrivialZerosFinset_of_height_lt hheightT⟩

lemma nontrivial_zero_ne_zero {ρ : ℂ}
    (hρ : RiemannHypothesis.IsNontrivialZero ρ) : ρ ≠ 0 := by
  intro h0
  have hre : ρ.re = 0 := by simpa using congr_arg Complex.re h0
  linarith [hρ.2.1]

lemma ne_zero_of_mem_nontrivialZerosFinset {ρ : ℂ} {T : ℝ}
    (hρ : ρ ∈ nontrivialZerosFinset T) : ρ ≠ 0 :=
  nontrivial_zero_ne_zero (mem_nontrivialZerosFinset.mp hρ).1

lemma nontrivialZerosFinset_eq_empty_of_neg {T : ℝ} (hT : T < 0) :
    nontrivialZerosFinset T = ∅ := by
  ext ρ
  constructor
  · intro hρ
    have hheight := (mem_nontrivialZerosFinset.mp hρ).2
    have hnonneg : 0 ≤ |ρ.im| := abs_nonneg _
    exfalso
    linarith
  · simp

lemma finiteNontrivialZeroSum_eq_zero_of_neg (x : ℝ) {T : ℝ} (hT : T < 0) :
    finiteNontrivialZeroSum x T = 0 := by
  simp [finiteNontrivialZeroSum, nontrivialZerosFinset_eq_empty_of_neg hT]

lemma finiteNontrivialZeroSum_eq_zero_of_nontrivialZerosFinset_eq_empty
    (x : ℝ) {T : ℝ} (hT : nontrivialZerosFinset T = ∅) :
    finiteNontrivialZeroSum x T = 0 := by
  simp [finiteNontrivialZeroSum, hT]

lemma one_sub_mem_nontrivialZerosFinset {ρ : ℂ} {T : ℝ}
    (hρ : ρ ∈ nontrivialZerosFinset T) :
    1 - ρ ∈ nontrivialZerosFinset T := by
  rcases mem_nontrivialZerosFinset.mp hρ with ⟨hzero, hheight⟩
  refine mem_nontrivialZerosFinset.mpr ⟨nontrivial_zero_symmetric' hzero, ?_⟩
  simpa [Complex.sub_im] using hheight

lemma one_sub_mem_nontrivialZerosFinset_iff {ρ : ℂ} {T : ℝ} :
    1 - ρ ∈ nontrivialZerosFinset T ↔ ρ ∈ nontrivialZerosFinset T := by
  constructor
  · intro hρ
    have h := one_sub_mem_nontrivialZerosFinset hρ
    convert h using 1
    ring
  · exact one_sub_mem_nontrivialZerosFinset

lemma sum_nontrivialZerosFinset_one_sub (T : ℝ) (f : ℂ → ℂ) :
    (∑ ρ ∈ nontrivialZerosFinset T, f (1 - ρ)) =
      ∑ ρ ∈ nontrivialZerosFinset T, f ρ := by
  classical
  refine Finset.sum_nbij' (fun ρ : ℂ => 1 - ρ) (fun ρ : ℂ => 1 - ρ) ?_ ?_ ?_ ?_ ?_
  · intro ρ hρ
    exact one_sub_mem_nontrivialZerosFinset hρ
  · intro ρ hρ
    exact one_sub_mem_nontrivialZerosFinset hρ
  · intro ρ _hρ
    ring
  · intro ρ _hρ
    ring
  · intro ρ _hρ
    rfl

lemma nontrivialZerosFinset_ext_of_height_iff {T U : ℝ}
    (h : ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ →
      (|ρ.im| ≤ T ↔ |ρ.im| ≤ U)) :
    nontrivialZerosFinset T = nontrivialZerosFinset U := by
  ext ρ
  constructor
  · intro hρ
    rcases mem_nontrivialZerosFinset.mp hρ with ⟨hzero, hheight⟩
    exact mem_nontrivialZerosFinset.mpr ⟨hzero, (h ρ hzero).mp hheight⟩
  · intro hρ
    rcases mem_nontrivialZerosFinset.mp hρ with ⟨hzero, hheight⟩
    exact mem_nontrivialZerosFinset.mpr ⟨hzero, (h ρ hzero).mpr hheight⟩

lemma finiteNontrivialZeroSum_congr_finset {x T U : ℝ}
    (h : nontrivialZerosFinset T = nontrivialZerosFinset U) :
    finiteNontrivialZeroSum x T = finiteNontrivialZeroSum x U := by
  simp [finiteNontrivialZeroSum, h]

lemma finiteNontrivialZeroSum_congr_height {x T U : ℝ}
    (h : ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ →
      (|ρ.im| ≤ T ↔ |ρ.im| ≤ U)) :
    finiteNontrivialZeroSum x T = finiteNontrivialZeroSum x U := by
  simp [finiteNontrivialZeroSum, nontrivialZerosFinset_ext_of_height_iff h]

lemma nontrivialZerosFinset_eq_of_global_height_bound {B T : ℝ}
    (hBT : B ≤ T)
    (hbound : ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → |ρ.im| ≤ B) :
    nontrivialZerosFinset T = nontrivialZerosFinset B := by
  refine nontrivialZerosFinset_ext_of_height_iff ?_
  intro ρ hρ
  constructor
  · intro _hT
    exact hbound ρ hρ
  · intro hB
    exact le_trans hB hBT

lemma finiteNontrivialZeroSum_eq_of_global_height_bound {x B T : ℝ}
    (hBT : B ≤ T)
    (hbound : ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → |ρ.im| ≤ B) :
    finiteNontrivialZeroSum x T = finiteNontrivialZeroSum x B :=
  finiteNontrivialZeroSum_congr_finset
    (nontrivialZerosFinset_eq_of_global_height_bound hBT hbound)

lemma finiteNontrivialZeroSum_eq_add_new_zeros {x T U : ℝ} (hTU : T ≤ U) :
    finiteNontrivialZeroSum x U =
      finiteNontrivialZeroSum x T +
        ∑ ρ ∈ (nontrivialZerosFinset U \ nontrivialZerosFinset T),
          (x : ℂ) ^ ρ / ρ := by
  classical
  have hsubset : nontrivialZerosFinset T ⊆ nontrivialZerosFinset U := by
    intro ρ hρ
    exact nontrivialZerosFinset_mono hTU hρ
  rw [finiteNontrivialZeroSum, finiteNontrivialZeroSum]
  have hsum :
      (∑ ρ ∈ (nontrivialZerosFinset U \ nontrivialZerosFinset T),
          (x : ℂ) ^ ρ / ρ)
        + (∑ ρ ∈ nontrivialZerosFinset T, (x : ℂ) ^ ρ / ρ)
        =
      ∑ ρ ∈ nontrivialZerosFinset U, (x : ℂ) ^ ρ / ρ :=
    Finset.sum_sdiff (s₁ := nontrivialZerosFinset T)
      (s₂ := nontrivialZerosFinset U)
      (f := fun ρ : ℂ => (x : ℂ) ^ ρ / ρ) hsubset
  rw [← hsum]
  abel

lemma finiteNontrivialZeroSum_sub_eq_new_zeros {x T U : ℝ} (hTU : T ≤ U) :
    finiteNontrivialZeroSum x U - finiteNontrivialZeroSum x T =
      ∑ ρ ∈ (nontrivialZerosFinset U \ nontrivialZerosFinset T),
        (x : ℂ) ^ ρ / ρ := by
  have h := finiteNontrivialZeroSum_eq_add_new_zeros (x := x) hTU
  rw [h]
  abel

/-- The height-truncated right-hand side appearing in the explicit formula
target, factored out so later contour arguments can rewrite it directly. -/
noncomputable def explicitFormulaApprox (x T : ℝ) : ℂ :=
  (x : ℂ)
    - finiteNontrivialZeroSum x T
    - deriv riemannZeta 0 / riemannZeta 0
    - (1 / 2 : ℂ) * (Real.log (1 - x^(-2 : ℝ)) : ℂ)

lemma explicitFormulaApprox_congr_finset {x T U : ℝ}
    (h : nontrivialZerosFinset T = nontrivialZerosFinset U) :
    explicitFormulaApprox x T = explicitFormulaApprox x U := by
  simp [explicitFormulaApprox, finiteNontrivialZeroSum, h]

lemma explicitFormulaApprox_congr_zero_sum {x T U : ℝ}
    (h : finiteNontrivialZeroSum x T = finiteNontrivialZeroSum x U) :
  explicitFormulaApprox x T = explicitFormulaApprox x U := by
  simp [explicitFormulaApprox, h]

lemma explicitFormulaApprox_congr_height {x T U : ℝ}
    (h : ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ →
      (|ρ.im| ≤ T ↔ |ρ.im| ≤ U)) :
    explicitFormulaApprox x T = explicitFormulaApprox x U :=
  explicitFormulaApprox_congr_zero_sum (finiteNontrivialZeroSum_congr_height h)

lemma explicitFormulaApprox_sub_explicitFormulaApprox
    (x T U : ℝ) :
    explicitFormulaApprox x T - explicitFormulaApprox x U =
      finiteNontrivialZeroSum x U - finiteNontrivialZeroSum x T := by
  simp [explicitFormulaApprox]

lemma explicitFormulaApprox_eq_sub_new_zeros {x T U : ℝ} (hTU : T ≤ U) :
    explicitFormulaApprox x U =
      explicitFormulaApprox x T -
        ∑ ρ ∈ (nontrivialZerosFinset U \ nontrivialZerosFinset T),
          (x : ℂ) ^ ρ / ρ := by
  have hsum := finiteNontrivialZeroSum_eq_add_new_zeros (x := x) hTU
  simp [explicitFormulaApprox, hsum]
  abel

lemma explicitFormulaApprox_sub_eq_new_zeros {x T U : ℝ} (hTU : T ≤ U) :
    explicitFormulaApprox x T - explicitFormulaApprox x U =
      ∑ ρ ∈ (nontrivialZerosFinset U \ nontrivialZerosFinset T),
        (x : ℂ) ^ ρ / ρ := by
  rw [explicitFormulaApprox_eq_sub_new_zeros hTU]
  abel

lemma explicitFormulaApprox_sub_norm_eq_new_zeros
    {x T U : ℝ} (hTU : T ≤ U) :
    ‖explicitFormulaApprox x T - explicitFormulaApprox x U‖ =
      ‖∑ ρ ∈ (nontrivialZerosFinset U \ nontrivialZerosFinset T),
        (x : ℂ) ^ ρ / ρ‖ := by
  rw [explicitFormulaApprox_sub_eq_new_zeros hTU]

lemma explicitFormulaApprox_add_new_zeros {x T U : ℝ} (hTU : T ≤ U) :
    explicitFormulaApprox x U +
      ∑ ρ ∈ (nontrivialZerosFinset U \ nontrivialZerosFinset T),
          (x : ℂ) ^ ρ / ρ =
      explicitFormulaApprox x T := by
  rw [explicitFormulaApprox_eq_sub_new_zeros hTU]
  abel

lemma explicitFormulaApprox_eq_of_global_height_bound {x B T : ℝ}
    (hBT : B ≤ T)
    (hbound : ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → |ρ.im| ≤ B) :
    explicitFormulaApprox x T = explicitFormulaApprox x B :=
  explicitFormulaApprox_congr_zero_sum
    (finiteNontrivialZeroSum_eq_of_global_height_bound hBT hbound)

lemma explicitFormulaApprox_eventually_eq_of_global_height_bound {x B : ℝ}
    (hbound : ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → |ρ.im| ≤ B) :
    (fun T : ℝ => explicitFormulaApprox x T) =ᶠ[atTop]
      fun _T : ℝ => explicitFormulaApprox x B := by
  filter_upwards [eventually_ge_atTop B] with T hBT
  exact explicitFormulaApprox_eq_of_global_height_bound hBT hbound

lemma explicitFormulaApprox_eq_of_neg (x : ℝ) {T : ℝ} (hT : T < 0) :
    explicitFormulaApprox x T =
      (x : ℂ)
        - deriv riemannZeta 0 / riemannZeta 0
        - (1 / 2 : ℂ) * (Real.log (1 - x^(-2 : ℝ)) : ℂ) := by
  simp [explicitFormulaApprox, finiteNontrivialZeroSum_eq_zero_of_neg x hT]

/-- Corrected target shape for the von Mangoldt explicit formula.

The old unordered `tsum` over all zeros is not a safe formal statement.  This
target uses the midpoint function `ψ₀` and a height-truncated symmetric limit.
It is still a target statement, not a proved theorem; completing it requires
Perron's formula, contour shifting, residue calculus, zero multiplicities, and
edge estimates. -/
def explicit_formula_von_mangoldt (x : ℝ) (_hx : x ≥ 2) : Prop :=
  Tendsto
    (fun T : ℝ => explicitFormulaApprox x T)
    atTop
    (𝓝 (chebyshevPsi0 x : ℂ))

lemma explicit_formula_von_mangoldt_iff {x : ℝ} {hx : x ≥ 2} :
    explicit_formula_von_mangoldt x hx ↔
      Tendsto (fun T : ℝ => explicitFormulaApprox x T) atTop
        (𝓝 (chebyshevPsi0 x : ℂ)) := by
  rfl

lemma explicit_formula_von_mangoldt_of_eventually_eq {x : ℝ} {hx : x ≥ 2}
    {F : ℝ → ℂ}
    (hF : F =ᶠ[atTop] fun T : ℝ => explicitFormulaApprox x T)
    (h : Tendsto F atTop (𝓝 (chebyshevPsi0 x : ℂ))) :
    explicit_formula_von_mangoldt x hx := by
  exact Tendsto.congr' hF h

lemma explicit_formula_von_mangoldt_of_eventually_exact {x : ℝ} {hx : x ≥ 2}
    (h : ∀ᶠ T in atTop, explicitFormulaApprox x T = (chebyshevPsi0 x : ℂ)) :
    explicit_formula_von_mangoldt x hx := by
  exact tendsto_nhds_of_eventually_eq h

lemma explicit_formula_von_mangoldt_of_global_height_bound_exact
    {x B : ℝ} {hx : x ≥ 2}
    (hbound : ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → |ρ.im| ≤ B)
    (hB : explicitFormulaApprox x B = (chebyshevPsi0 x : ℂ)) :
    explicit_formula_von_mangoldt x hx := by
  refine explicit_formula_von_mangoldt_of_eventually_exact ?_
  exact (explicitFormulaApprox_eventually_eq_of_global_height_bound
    (x := x) (B := B) hbound).mono fun _T hT => by
      simpa using hT.trans hB

lemma explicitFormulaApprox_eq_chebyshevPsi0_of_global_height_bound
    {x B : ℝ} {hx : x ≥ 2}
    (hbound : ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → |ρ.im| ≤ B)
    (h : explicit_formula_von_mangoldt x hx) :
    explicitFormulaApprox x B = (chebyshevPsi0 x : ℂ) := by
  have hconst :
      Tendsto (fun _T : ℝ => explicitFormulaApprox x B) atTop
        (𝓝 (chebyshevPsi0 x : ℂ)) :=
    Tendsto.congr'
      (explicitFormulaApprox_eventually_eq_of_global_height_bound
        (x := x) (B := B) hbound) h
  exact tendsto_nhds_unique tendsto_const_nhds hconst

lemma explicit_formula_von_mangoldt_iff_global_height_bound_exact
    {x B : ℝ} {hx : x ≥ 2}
    (hbound : ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → |ρ.im| ≤ B) :
    explicit_formula_von_mangoldt x hx ↔
      explicitFormulaApprox x B = (chebyshevPsi0 x : ℂ) :=
  ⟨explicitFormulaApprox_eq_chebyshevPsi0_of_global_height_bound hbound,
    explicit_formula_von_mangoldt_of_global_height_bound_exact hbound⟩

lemma explicit_formula_von_mangoldt_of_error_tendsto_zero {x : ℝ} {hx : x ≥ 2}
    (h : Tendsto (fun T : ℝ =>
      explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ)) atTop (𝓝 0)) :
    explicit_formula_von_mangoldt x hx := by
  have hconst : Tendsto (fun _T : ℝ => (chebyshevPsi0 x : ℂ)) atTop
      (𝓝 (chebyshevPsi0 x : ℂ)) :=
    tendsto_const_nhds
  have hsum := h.add hconst
  have h_eq :
      (fun T : ℝ => explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ)
          + (chebyshevPsi0 x : ℂ))
        = fun T : ℝ => explicitFormulaApprox x T := by
    funext T
    abel
  have hlim :
      (0 : ℂ) + (chebyshevPsi0 x : ℂ) = (chebyshevPsi0 x : ℂ) := by
    simp
  exact hsum.congr' (Filter.EventuallyEq.of_eq h_eq) |>.mono_right (by simp [hlim])

lemma explicit_formula_von_mangoldt_error_tendsto_zero {x : ℝ} {hx : x ≥ 2}
    (h : explicit_formula_von_mangoldt x hx) :
    Tendsto (fun T : ℝ =>
      explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ)) atTop (𝓝 0) := by
  have hconst : Tendsto (fun _T : ℝ => (chebyshevPsi0 x : ℂ)) atTop
      (𝓝 (chebyshevPsi0 x : ℂ)) :=
    tendsto_const_nhds
  simpa [explicit_formula_von_mangoldt] using h.sub hconst

lemma explicit_formula_von_mangoldt_iff_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2} :
    explicit_formula_von_mangoldt x hx ↔
      Tendsto (fun T : ℝ =>
        explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ)) atTop (𝓝 0) :=
  ⟨explicit_formula_von_mangoldt_error_tendsto_zero,
    explicit_formula_von_mangoldt_of_error_tendsto_zero⟩

lemma explicit_formula_von_mangoldt_iff_reverse_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2} :
    explicit_formula_von_mangoldt x hx ↔
      Tendsto (fun T : ℝ =>
        (chebyshevPsi0 x : ℂ) - explicitFormulaApprox x T) atTop (𝓝 0) := by
  constructor
  · intro h
    have hz := explicit_formula_von_mangoldt_error_tendsto_zero h
    have hneg := hz.neg
    simpa [sub_eq_add_neg, add_comm] using hneg
  · intro h
    have hneg := h.neg
    have hz :
        Tendsto (fun T : ℝ =>
          explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ)) atTop (𝓝 0) := by
      simpa [sub_eq_add_neg, add_comm] using hneg
    exact explicit_formula_von_mangoldt_of_error_tendsto_zero hz

lemma explicit_formula_von_mangoldt_reverse_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (h : explicit_formula_von_mangoldt x hx) :
    (fun T : ℝ => (chebyshevPsi0 x : ℂ) - explicitFormulaApprox x T)
        =o[atTop] (fun _T : ℝ => (1 : ℂ)) :=
  (isLittleO_one_iff ℂ).mpr
    ((explicit_formula_von_mangoldt_iff_reverse_error_tendsto_zero).mp h)

lemma explicit_formula_von_mangoldt_of_reverse_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (h : (fun T : ℝ => (chebyshevPsi0 x : ℂ) - explicitFormulaApprox x T)
        =o[atTop] (fun _T : ℝ => (1 : ℂ))) :
    explicit_formula_von_mangoldt x hx :=
  (explicit_formula_von_mangoldt_iff_reverse_error_tendsto_zero).mpr
    ((isLittleO_one_iff ℂ).mp h)

lemma explicit_formula_von_mangoldt_iff_reverse_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2} :
    explicit_formula_von_mangoldt x hx ↔
      (fun T : ℝ => (chebyshevPsi0 x : ℂ) - explicitFormulaApprox x T)
        =o[atTop] (fun _T : ℝ => (1 : ℂ)) :=
  ⟨explicit_formula_von_mangoldt_reverse_error_isLittleO_one,
    explicit_formula_von_mangoldt_of_reverse_error_isLittleO_one⟩

lemma explicit_formula_von_mangoldt_of_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (h : (fun T : ℝ => explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ))
        =o[atTop] (fun _T : ℝ => (1 : ℂ))) :
    explicit_formula_von_mangoldt x hx :=
  explicit_formula_von_mangoldt_of_error_tendsto_zero
    ((isLittleO_one_iff ℂ).mp h)

lemma explicit_formula_von_mangoldt_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (h : explicit_formula_von_mangoldt x hx) :
    (fun T : ℝ => explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ))
        =o[atTop] (fun _T : ℝ => (1 : ℂ)) :=
  (isLittleO_one_iff ℂ).mpr
    (explicit_formula_von_mangoldt_error_tendsto_zero h)

lemma explicit_formula_von_mangoldt_iff_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2} :
    explicit_formula_von_mangoldt x hx ↔
      (fun T : ℝ => explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ))
        =o[atTop] (fun _T : ℝ => (1 : ℂ)) :=
  ⟨explicit_formula_von_mangoldt_error_isLittleO_one,
    explicit_formula_von_mangoldt_of_error_isLittleO_one⟩

lemma explicit_formula_von_mangoldt_re_tendsto
    {x : ℝ} {hx : x ≥ 2}
    (h : explicit_formula_von_mangoldt x hx) :
    Tendsto (fun T : ℝ => (explicitFormulaApprox x T).re) atTop
      (𝓝 (chebyshevPsi0 x)) := by
  simpa [explicit_formula_von_mangoldt] using
    (Complex.continuous_re.tendsto (chebyshevPsi0 x : ℂ)).comp h

lemma explicit_formula_von_mangoldt_im_tendsto_zero
    {x : ℝ} {hx : x ≥ 2}
    (h : explicit_formula_von_mangoldt x hx) :
    Tendsto (fun T : ℝ => (explicitFormulaApprox x T).im) atTop (𝓝 0) := by
  simpa [explicit_formula_von_mangoldt] using
    (Complex.continuous_im.tendsto (chebyshevPsi0 x : ℂ)).comp h

lemma explicit_formula_von_mangoldt_re_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2}
    (h : explicit_formula_von_mangoldt x hx) :
    Tendsto (fun T : ℝ => (explicitFormulaApprox x T).re - chebyshevPsi0 x)
      atTop (𝓝 0) := by
  simpa using
    (Complex.continuous_re.tendsto (0 : ℂ)).comp
      (explicit_formula_von_mangoldt_error_tendsto_zero h)

lemma explicit_formula_von_mangoldt_im_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2}
    (h : explicit_formula_von_mangoldt x hx) :
    Tendsto (fun T : ℝ => (explicitFormulaApprox x T).im) atTop (𝓝 0) :=
  explicit_formula_von_mangoldt_im_tendsto_zero h

lemma explicit_formula_von_mangoldt_of_re_im_tendsto
    {x : ℝ} {hx : x ≥ 2}
    (hre : Tendsto (fun T : ℝ => (explicitFormulaApprox x T).re) atTop
      (𝓝 (chebyshevPsi0 x)))
    (him : Tendsto (fun T : ℝ => (explicitFormulaApprox x T).im) atTop
      (𝓝 0)) :
    explicit_formula_von_mangoldt x hx := by
  have hreC :
      Tendsto (fun T : ℝ => ((explicitFormulaApprox x T).re : ℂ)) atTop
        (𝓝 (chebyshevPsi0 x : ℂ)) := by
    simpa using (Complex.ofRealCLM.continuous.tendsto (chebyshevPsi0 x)).comp hre
  have himC :
      Tendsto (fun T : ℝ => ((explicitFormulaApprox x T).im : ℂ)) atTop
        (𝓝 (0 : ℂ)) := by
    simpa using (Complex.ofRealCLM.continuous.tendsto (0 : ℝ)).comp him
  have hI :
      Tendsto (fun T : ℝ => ((explicitFormulaApprox x T).im : ℂ) * I) atTop
        (𝓝 ((0 : ℂ) * I)) :=
    himC.mul tendsto_const_nhds
  have hsum := hreC.add hI
  have h_eq :
      (fun T : ℝ =>
          ((explicitFormulaApprox x T).re : ℂ) +
            ((explicitFormulaApprox x T).im : ℂ) * I)
        = fun T : ℝ => explicitFormulaApprox x T := by
    funext T
    exact Complex.re_add_im (explicitFormulaApprox x T)
  simpa [explicit_formula_von_mangoldt] using
    hsum.congr' (Filter.EventuallyEq.of_eq h_eq)

lemma explicit_formula_von_mangoldt_of_re_im_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2}
    (hre : Tendsto
      (fun T : ℝ => (explicitFormulaApprox x T).re - chebyshevPsi0 x)
      atTop (𝓝 0))
    (him : Tendsto (fun T : ℝ => (explicitFormulaApprox x T).im)
      atTop (𝓝 0)) :
    explicit_formula_von_mangoldt x hx := by
  have hconst :
      Tendsto (fun _T : ℝ => chebyshevPsi0 x) atTop
        (𝓝 (chebyshevPsi0 x)) :=
    tendsto_const_nhds
  have hsum := hre.add hconst
  have h_eq :
      (fun T : ℝ =>
          (explicitFormulaApprox x T).re - chebyshevPsi0 x +
            chebyshevPsi0 x)
        = fun T : ℝ => (explicitFormulaApprox x T).re := by
    funext T
    ring
  exact explicit_formula_von_mangoldt_of_re_im_tendsto
    (by simpa using hsum.congr' (Filter.EventuallyEq.of_eq h_eq)) him

lemma explicit_formula_von_mangoldt_iff_re_im_tendsto
    {x : ℝ} {hx : x ≥ 2} :
    explicit_formula_von_mangoldt x hx ↔
      Tendsto (fun T : ℝ => (explicitFormulaApprox x T).re) atTop
        (𝓝 (chebyshevPsi0 x)) ∧
      Tendsto (fun T : ℝ => (explicitFormulaApprox x T).im) atTop (𝓝 0) :=
  ⟨fun h => ⟨explicit_formula_von_mangoldt_re_tendsto h,
      explicit_formula_von_mangoldt_im_tendsto_zero h⟩,
    fun h => explicit_formula_von_mangoldt_of_re_im_tendsto h.1 h.2⟩

lemma explicit_formula_von_mangoldt_iff_re_im_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2} :
    explicit_formula_von_mangoldt x hx ↔
      Tendsto
        (fun T : ℝ => (explicitFormulaApprox x T).re - chebyshevPsi0 x)
        atTop (𝓝 0) ∧
      Tendsto (fun T : ℝ => (explicitFormulaApprox x T).im) atTop (𝓝 0) :=
  ⟨fun h => ⟨explicit_formula_von_mangoldt_re_error_tendsto_zero h,
      explicit_formula_von_mangoldt_im_error_tendsto_zero h⟩,
    fun h => explicit_formula_von_mangoldt_of_re_im_error_tendsto_zero h.1 h.2⟩

lemma explicit_formula_von_mangoldt_re_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (h : explicit_formula_von_mangoldt x hx) :
    (fun T : ℝ => (explicitFormulaApprox x T).re - chebyshevPsi0 x)
        =o[atTop] (fun _T : ℝ => (1 : ℝ)) :=
  (isLittleO_one_iff ℝ).mpr
    (explicit_formula_von_mangoldt_re_error_tendsto_zero h)

lemma explicit_formula_von_mangoldt_im_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (h : explicit_formula_von_mangoldt x hx) :
    (fun T : ℝ => (explicitFormulaApprox x T).im)
        =o[atTop] (fun _T : ℝ => (1 : ℝ)) :=
  (isLittleO_one_iff ℝ).mpr
    (explicit_formula_von_mangoldt_im_error_tendsto_zero h)

lemma explicit_formula_von_mangoldt_of_re_im_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (hre :
      (fun T : ℝ => (explicitFormulaApprox x T).re - chebyshevPsi0 x)
        =o[atTop] (fun _T : ℝ => (1 : ℝ)))
    (him : (fun T : ℝ => (explicitFormulaApprox x T).im)
        =o[atTop] (fun _T : ℝ => (1 : ℝ))) :
    explicit_formula_von_mangoldt x hx :=
  explicit_formula_von_mangoldt_of_re_im_error_tendsto_zero
    ((isLittleO_one_iff ℝ).mp hre)
    ((isLittleO_one_iff ℝ).mp him)

lemma explicit_formula_von_mangoldt_iff_re_im_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2} :
    explicit_formula_von_mangoldt x hx ↔
      (fun T : ℝ => (explicitFormulaApprox x T).re - chebyshevPsi0 x)
        =o[atTop] (fun _T : ℝ => (1 : ℝ)) ∧
      (fun T : ℝ => (explicitFormulaApprox x T).im)
        =o[atTop] (fun _T : ℝ => (1 : ℝ)) :=
  ⟨fun h => ⟨explicit_formula_von_mangoldt_re_error_isLittleO_one h,
      explicit_formula_von_mangoldt_im_error_isLittleO_one h⟩,
    fun h => explicit_formula_von_mangoldt_of_re_im_error_isLittleO_one h.1 h.2⟩

lemma explicit_formula_von_mangoldt_norm_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2}
    (h : explicit_formula_von_mangoldt x hx) :
    Tendsto (fun T : ℝ =>
      ‖explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ)‖) atTop (𝓝 0) :=
  tendsto_zero_iff_norm_tendsto_zero.mp
    (explicit_formula_von_mangoldt_error_tendsto_zero h)

lemma explicit_formula_von_mangoldt_reverse_norm_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2}
    (h : explicit_formula_von_mangoldt x hx) :
    Tendsto (fun T : ℝ =>
      ‖(chebyshevPsi0 x : ℂ) - explicitFormulaApprox x T‖) atTop (𝓝 0) := by
  have hnorm := explicit_formula_von_mangoldt_norm_error_tendsto_zero h
  have h_eq :
      (fun T : ℝ => ‖(chebyshevPsi0 x : ℂ) - explicitFormulaApprox x T‖) =
        fun T : ℝ => ‖explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ)‖ := by
    funext T
    rw [norm_sub_rev]
  simpa [h_eq] using hnorm

lemma explicit_formula_von_mangoldt_of_norm_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2}
    (h : Tendsto (fun T : ℝ =>
      ‖explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ)‖) atTop (𝓝 0)) :
    explicit_formula_von_mangoldt x hx :=
  explicit_formula_von_mangoldt_of_error_tendsto_zero
    (tendsto_zero_iff_norm_tendsto_zero.mpr h)

lemma explicit_formula_von_mangoldt_of_reverse_norm_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2}
    (h : Tendsto (fun T : ℝ =>
      ‖(chebyshevPsi0 x : ℂ) - explicitFormulaApprox x T‖) atTop (𝓝 0)) :
    explicit_formula_von_mangoldt x hx := by
  refine explicit_formula_von_mangoldt_of_norm_error_tendsto_zero ?_
  have h_eq :
      (fun T : ℝ => ‖explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ)‖) =
        fun T : ℝ => ‖(chebyshevPsi0 x : ℂ) - explicitFormulaApprox x T‖ := by
    funext T
    rw [norm_sub_rev]
  simpa [h_eq] using h

lemma explicit_formula_von_mangoldt_iff_reverse_norm_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2} :
    explicit_formula_von_mangoldt x hx ↔
      Tendsto (fun T : ℝ =>
        ‖(chebyshevPsi0 x : ℂ) - explicitFormulaApprox x T‖) atTop (𝓝 0) :=
  ⟨explicit_formula_von_mangoldt_reverse_norm_error_tendsto_zero,
    explicit_formula_von_mangoldt_of_reverse_norm_error_tendsto_zero⟩

lemma explicit_formula_von_mangoldt_of_eventually_norm_le
    {x : ℝ} {hx : x ≥ 2} {E : ℝ → ℝ}
    (hE : Tendsto E atTop (𝓝 0))
    (hbound : ∀ᶠ T in atTop,
      ‖explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ)‖ ≤ E T) :
    explicit_formula_von_mangoldt x hx := by
  refine explicit_formula_von_mangoldt_of_norm_error_tendsto_zero ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hE ?_ hbound
  exact Eventually.of_forall fun T =>
    norm_nonneg (explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ))

lemma explicit_formula_von_mangoldt_of_eventually_norm_le_const_mul_inv
    {x C : ℝ} {hx : x ≥ 2}
    (hbound : ∀ᶠ T in atTop,
      ‖explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ)‖ ≤ C * T⁻¹) :
    explicit_formula_von_mangoldt x hx := by
  refine explicit_formula_von_mangoldt_of_eventually_norm_le ?_ hbound
  simpa using
    (tendsto_const_nhds.mul tendsto_inv_atTop_zero :
      Tendsto (fun T : ℝ => C * T⁻¹) atTop (𝓝 (C * 0)))

/-- Coordinate estimates for the real and imaginary errors are enough to close
the explicit-formula target.  This is the shape naturally produced by many
contour estimates before they are repackaged as a complex norm bound. -/
lemma explicit_formula_von_mangoldt_of_eventually_re_im_abs_le
    {x : ℝ} {hx : x ≥ 2} {Ere Eim : ℝ → ℝ}
    (hEre : Tendsto Ere atTop (𝓝 0))
    (hEim : Tendsto Eim atTop (𝓝 0))
    (hre_bound : ∀ᶠ T in atTop,
      |(explicitFormulaApprox x T).re - chebyshevPsi0 x| ≤ Ere T)
    (him_bound : ∀ᶠ T in atTop,
      |(explicitFormulaApprox x T).im| ≤ Eim T) :
    explicit_formula_von_mangoldt x hx := by
  refine explicit_formula_von_mangoldt_of_re_im_error_tendsto_zero ?_ ?_
  · rw [tendsto_zero_iff_abs_tendsto_zero]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      hEre
      (Eventually.of_forall fun T => abs_nonneg _)
      hre_bound
  · rw [tendsto_zero_iff_abs_tendsto_zero]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      hEim
      (Eventually.of_forall fun T => abs_nonneg _)
      him_bound

lemma explicit_formula_von_mangoldt_of_eventually_re_im_abs_le_const_mul_inv
    {x Cre Cim : ℝ} {hx : x ≥ 2}
    (hre_bound : ∀ᶠ T in atTop,
      |(explicitFormulaApprox x T).re - chebyshevPsi0 x| ≤ Cre * T⁻¹)
    (him_bound : ∀ᶠ T in atTop,
      |(explicitFormulaApprox x T).im| ≤ Cim * T⁻¹) :
    explicit_formula_von_mangoldt x hx := by
  refine explicit_formula_von_mangoldt_of_eventually_re_im_abs_le ?_ ?_
    hre_bound him_bound
  · simpa using
      (tendsto_const_nhds.mul tendsto_inv_atTop_zero :
        Tendsto (fun T : ℝ => Cre * T⁻¹) atTop (𝓝 (Cre * 0)))
  · simpa using
      (tendsto_const_nhds.mul tendsto_inv_atTop_zero :
        Tendsto (fun T : ℝ => Cim * T⁻¹) atTop (𝓝 (Cim * 0)))

lemma explicit_formula_von_mangoldt_re_abs_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2}
    (h : explicit_formula_von_mangoldt x hx) :
    Tendsto (fun T : ℝ =>
      |(explicitFormulaApprox x T).re - chebyshevPsi0 x|) atTop (𝓝 0) := by
  simpa using (explicit_formula_von_mangoldt_re_error_tendsto_zero h).abs

lemma explicit_formula_von_mangoldt_im_abs_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2}
    (h : explicit_formula_von_mangoldt x hx) :
    Tendsto (fun T : ℝ => |(explicitFormulaApprox x T).im|) atTop (𝓝 0) := by
  simpa using (explicit_formula_von_mangoldt_im_error_tendsto_zero h).abs

lemma explicit_formula_von_mangoldt_iff_re_im_abs_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2} :
    explicit_formula_von_mangoldt x hx ↔
      Tendsto (fun T : ℝ =>
        |(explicitFormulaApprox x T).re - chebyshevPsi0 x|) atTop (𝓝 0) ∧
      Tendsto (fun T : ℝ => |(explicitFormulaApprox x T).im|) atTop (𝓝 0) := by
  constructor
  · intro h
    exact ⟨explicit_formula_von_mangoldt_re_abs_error_tendsto_zero h,
      explicit_formula_von_mangoldt_im_abs_error_tendsto_zero h⟩
  · intro h
    exact explicit_formula_von_mangoldt_of_re_im_error_tendsto_zero
      ((tendsto_zero_iff_abs_tendsto_zero _).mpr h.1)
      ((tendsto_zero_iff_abs_tendsto_zero _).mpr h.2)

lemma explicit_formula_von_mangoldt_iff_norm_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2} :
    explicit_formula_von_mangoldt x hx ↔
      Tendsto (fun T : ℝ =>
        ‖explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ)‖) atTop (𝓝 0) :=
  ⟨explicit_formula_von_mangoldt_norm_error_tendsto_zero,
    explicit_formula_von_mangoldt_of_norm_error_tendsto_zero⟩

lemma explicit_formula_von_mangoldt_norm_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (h : explicit_formula_von_mangoldt x hx) :
    (fun T : ℝ => ‖explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ)‖)
      =o[atTop] (fun _T : ℝ => (1 : ℝ)) :=
  (isLittleO_one_iff ℝ).mpr
    (explicit_formula_von_mangoldt_norm_error_tendsto_zero h)

lemma explicit_formula_von_mangoldt_of_norm_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (h : (fun T : ℝ => ‖explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ)‖)
      =o[atTop] (fun _T : ℝ => (1 : ℝ))) :
    explicit_formula_von_mangoldt x hx :=
  explicit_formula_von_mangoldt_of_norm_error_tendsto_zero
    ((isLittleO_one_iff ℝ).mp h)

lemma explicit_formula_von_mangoldt_iff_norm_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2} :
    explicit_formula_von_mangoldt x hx ↔
      (fun T : ℝ => ‖explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ)‖)
        =o[atTop] (fun _T : ℝ => (1 : ℝ)) :=
  ⟨explicit_formula_von_mangoldt_norm_error_isLittleO_one,
    explicit_formula_von_mangoldt_of_norm_error_isLittleO_one⟩

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
