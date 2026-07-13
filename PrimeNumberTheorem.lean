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
   - `ZeroFreeRegion.classical_zero_free_region_proved`:
     Verified existence of a de la Vallée Poussin region of width `c / log |t|`
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

- `explicit_formula_von_mangoldt` — the multiplicity-weighted explicit formula;
  requires the remaining Perron/contour and all-height convergence arguments
- `rh_iff_optimal_error` — standard RH equivalence with prime-counting error terms

## Infrastructure gap analysis

The remaining explicit-formula and RH-equivalence targets still require analytic
infrastructure that is not yet connected end to end in this project, including:
- Perron inversion and the required contour-shift error estimates
- global convergence control for the multiplicity-weighted zero sum
- the forward RH-to-prime-error implication
- stronger zero-density or Vinogradov-Korobov estimates for the corresponding targets

## File structure

This file is currently about 9,700 lines. Earlier notes describing a
21,000-line single-file infrastructure library do not match this checkout;
substantial supporting infrastructure now lives in dedicated modules.
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

lemma id_div_log_isLittleO_id :
    (fun x : ℝ => x / Real.log x) =o[atTop] (fun x : ℝ => x) := by
  have hlog_inv :
      Tendsto (fun x : ℝ => (Real.log x)⁻¹) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hratio :
      Tendsto (fun x : ℝ => (x / Real.log x) / x) atTop (𝓝 0) := by
    have heq :
        (fun x : ℝ => (Real.log x)⁻¹)
          =ᶠ[atTop] fun x : ℝ => (x / Real.log x) / x := by
      filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
      have hx_ne : x ≠ 0 := by linarith
      have hlog_ne : Real.log x ≠ 0 :=
        ne_of_gt (Real.log_pos (by linarith))
      field_simp [hx_ne, hlog_ne]
    exact hlog_inv.congr' heq
  refine (isLittleO_iff_tendsto' ?_).2 hratio
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx hzero
  exact False.elim (hx.ne' hzero)

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

lemma PNTForm1_error_isLittleO_main
    (h : PNTForm1) :
    (fun x : ℝ => (primeCounting x : ℝ) - x / Real.log x)
      =o[atTop] (fun x : ℝ => x / Real.log x) := by
  have hratio :
      Tendsto (fun x : ℝ =>
        ((primeCounting x : ℝ) * Real.log x / x) - 1) atTop (𝓝 0) := by
    simpa using (h.sub tendsto_const_nhds :
      Tendsto (fun x : ℝ =>
        (primeCounting x : ℝ) * Real.log x / x - (1 : ℝ))
        atTop (𝓝 (1 - 1)))
  have heq :
      (fun x : ℝ => ((primeCounting x : ℝ) * Real.log x / x) - 1)
        =ᶠ[atTop]
      fun x : ℝ => ((primeCounting x : ℝ) - x / Real.log x) /
        (x / Real.log x) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hx_ne : x ≠ 0 := by linarith
    have hlog_ne : Real.log x ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
    field_simp [hx_ne, hlog_ne]
  refine (isLittleO_iff_tendsto' ?_).2 (hratio.congr' heq)
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx hzero
  have hx_ne : x ≠ 0 := by linarith
  have hlog_ne : Real.log x ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
  exact False.elim ((div_ne_zero hx_ne hlog_ne) hzero)

lemma PNTForm1_of_error_isLittleO_main
    (h : (fun x : ℝ => (primeCounting x : ℝ) - x / Real.log x)
      =o[atTop] (fun x : ℝ => x / Real.log x)) :
    PNTForm1 := by
  have hratio := h.tendsto_div_nhds_zero
  have hsum :
      Tendsto
        (fun x : ℝ =>
          1 + ((primeCounting x : ℝ) - x / Real.log x) /
            (x / Real.log x))
        atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add hratio :
      Tendsto
        (fun x : ℝ =>
          (1 : ℝ) + ((primeCounting x : ℝ) - x / Real.log x) /
            (x / Real.log x))
        atTop (𝓝 ((1 : ℝ) + 0)))
  have heq :
      (fun x : ℝ =>
          1 + ((primeCounting x : ℝ) - x / Real.log x) /
            (x / Real.log x))
        =ᶠ[atTop] fun x : ℝ => (primeCounting x : ℝ) * Real.log x / x := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hx_ne : x ≠ 0 := by linarith
    have hlog_ne : Real.log x ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
    field_simp [hx_ne, hlog_ne]
    ring
  exact hsum.congr' heq

lemma PNTForm1_iff_error_isLittleO_main :
    PNTForm1 ↔
      (fun x : ℝ => (primeCounting x : ℝ) - x / Real.log x)
        =o[atTop] (fun x : ℝ => x / Real.log x) :=
  ⟨PNTForm1_error_isLittleO_main,
    PNTForm1_of_error_isLittleO_main⟩

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

lemma PNTForm3_error_isLittleO_id
    (h : PNTForm3) :
    (fun x : ℝ => chebyshevPsi x - x) =o[atTop] (fun x : ℝ => x) := by
  have hratio :
      Tendsto (fun x : ℝ => chebyshevPsi x / x - 1) atTop (𝓝 0) := by
    simpa using (h.sub tendsto_const_nhds :
      Tendsto (fun x : ℝ => chebyshevPsi x / x - (1 : ℝ)) atTop (𝓝 (1 - 1)))
  have heq :
      (fun x : ℝ => chebyshevPsi x / x - 1)
        =ᶠ[atTop] fun x : ℝ => (chebyshevPsi x - x) / x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hx_ne : x ≠ 0 := hx.ne'
    field_simp [hx_ne]
  refine (isLittleO_iff_tendsto' ?_).2 (hratio.congr' heq)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx hzero
  exact False.elim (hx.ne' hzero)

lemma PNTForm3_of_error_isLittleO_id
    (h : (fun x : ℝ => chebyshevPsi x - x) =o[atTop] (fun x : ℝ => x)) :
    PNTForm3 := by
  have hratio := h.tendsto_div_nhds_zero
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

lemma PNTForm3_iff_error_isLittleO_id :
    PNTForm3 ↔
      (fun x : ℝ => chebyshevPsi x - x) =o[atTop] (fun x : ℝ => x) :=
  ⟨PNTForm3_error_isLittleO_id,
    PNTForm3_of_error_isLittleO_id⟩

lemma PNTForm1_error_isLittleO_id
    (h : PNTForm1) :
    (fun x : ℝ => (primeCounting x : ℝ) - x / Real.log x)
      =o[atTop] (fun x : ℝ => x) :=
  (PNTForm1_error_isLittleO_main h).trans id_div_log_isLittleO_id

lemma PNTForm1_error_isBigO_main
    (h : PNTForm1) :
    (fun x : ℝ => (primeCounting x : ℝ) - x / Real.log x)
      =O[atTop] (fun x : ℝ => x / Real.log x) :=
  (PNTForm1_error_isLittleO_main h).isBigO

lemma PNTForm1_error_isBigO_id
    (h : PNTForm1) :
    (fun x : ℝ => (primeCounting x : ℝ) - x / Real.log x)
      =O[atTop] (fun x : ℝ => x) :=
  (PNTForm1_error_isLittleO_id h).isBigO

lemma PNTForm2_error_isBigO_logIntegral
    (h : PNTForm2) :
    (fun x : ℝ => (primeCounting x : ℝ) - logIntegral x)
      =O[atTop] (fun x : ℝ => logIntegral x) :=
  (PNTForm2_error_isLittleO_logIntegral h).isBigO

lemma PNTForm2_error_isBigO_id
    (h : PNTForm2) :
    (fun x : ℝ => (primeCounting x : ℝ) - logIntegral x)
      =O[atTop] (fun x : ℝ => x) :=
  (PNTForm2_error_isLittleO_id h).isBigO

lemma PNTForm3_error_isBigO_id
    (h : PNTForm3) :
    (fun x : ℝ => chebyshevPsi x - x) =O[atTop] (fun x : ℝ => x) :=
  (PNTForm3_error_isLittleO_id h).isBigO

/-! ## 与黎曼猜想的联系 -/

/-- RH-scale Chebyshev-ψ error target. -/
def RH_PsiErrorBound : Prop :=
  (fun x : ℝ => chebyshevPsi x - x)
    =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2)

/-- RH-scale Chebyshev-θ error target. -/
def RH_ThetaErrorBound : Prop :=
  (fun x : ℝ => Chebyshev.theta x - x)
    =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2)

/-- The jump term separating the right-continuous `ψ` from the midpoint
convention `ψ₀` is negligible at the RH error scale. -/
lemma jumpVonMangoldt_isBigO_rh_scale :
    (fun x : ℝ => jumpVonMangoldt x)
      =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hx1 : 1 ≤ x := by
    have h_exp_one : (1 : ℝ) ≤ Real.exp 1 := by
      rw [Real.one_le_exp_iff]
      norm_num
    exact le_trans h_exp_one hx
  have hlog_ge_one : 1 ≤ Real.log x :=
    (Real.le_log_iff_exp_le hxpos).mpr hx
  have hlog_nonneg : 0 ≤ Real.log x := by linarith
  have hlog_le_sq : Real.log x ≤ (Real.log x)^2 := by nlinarith
  have hsqrt_ge_one : 1 ≤ Real.sqrt x := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have htarget_nonneg : 0 ≤ Real.sqrt x * (Real.log x)^2 :=
    mul_nonneg (Real.sqrt_nonneg x) (sq_nonneg _)
  have hjump_nonneg : 0 ≤ jumpVonMangoldt x := by
    classical
    rw [jumpVonMangoldt]
    split_ifs with h
    · rw [vonMangoldt_eq_mathlib]
      exact ArithmeticFunction.vonMangoldt_nonneg
    · norm_num
  have hjump_le_log : jumpVonMangoldt x ≤ Real.log x := by
    classical
    rw [jumpVonMangoldt]
    split_ifs with h
    · have hchoose := Classical.choose_spec h
      rw [vonMangoldt_eq_mathlib]
      calc
        ArithmeticFunction.vonMangoldt (Classical.choose h) ≤
            Real.log ((Classical.choose h : ℕ) : ℝ) :=
          ArithmeticFunction.vonMangoldt_le_log
        _ = Real.log x := by rw [← hchoose]
    · exact hlog_nonneg
  have hlog_le_scale :
      Real.log x ≤ Real.sqrt x * (Real.log x)^2 := by
    nlinarith [hlog_le_sq, hsqrt_ge_one, sq_nonneg (Real.log x)]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg htarget_nonneg, one_mul]
  exact le_trans (by simpa [abs_of_nonneg hjump_nonneg] using hjump_le_log) hlog_le_scale

/-- The midpoint explicit-formula convention `ψ₀` has the same RH-scale error
target as the right-continuous Chebyshev `ψ`. -/
lemma RH_PsiErrorBound_iff_chebyshevPsi0_sub_id_isBigO :
    RH_PsiErrorBound ↔
      (fun x : ℝ => chebyshevPsi0 x - x)
        =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2) := by
  have hjump_half :
      (fun x : ℝ => jumpVonMangoldt x / 2)
        =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2) := by
    simpa [div_eq_mul_inv, mul_comm] using
      jumpVonMangoldt_isBigO_rh_scale.const_mul_left (1 / 2 : ℝ)
  constructor
  · intro hψ
    rw [RH_PsiErrorBound] at hψ
    have hsub := hψ.sub hjump_half
    have heq :
        (fun x : ℝ => chebyshevPsi x - x - jumpVonMangoldt x / 2) =
          fun x : ℝ => chebyshevPsi0 x - x := by
      funext x
      simp [chebyshevPsi0]
      ring
    simpa [heq] using hsub
  · intro hψ0
    rw [RH_PsiErrorBound]
    have hadd := hψ0.add hjump_half
    have heq :
        (fun x : ℝ => chebyshevPsi0 x - x + jumpVonMangoldt x / 2) =
          fun x : ℝ => chebyshevPsi x - x := by
      funext x
      simp [chebyshevPsi0]
      ring
    simpa [heq] using hadd

/-- Forward direction of `RH_PsiErrorBound_iff_chebyshevPsi0_sub_id_isBigO`. -/
lemma chebyshevPsi0_sub_id_isBigO_of_RH_PsiErrorBound
    (hψ : RH_PsiErrorBound) :
    (fun x : ℝ => chebyshevPsi0 x - x)
      =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2) :=
  RH_PsiErrorBound_iff_chebyshevPsi0_sub_id_isBigO.mp hψ

/-- Reverse direction of `RH_PsiErrorBound_iff_chebyshevPsi0_sub_id_isBigO`. -/
lemma RH_PsiErrorBound_of_chebyshevPsi0_sub_id_isBigO
    (hψ0 :
      (fun x : ℝ => chebyshevPsi0 x - x)
        =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2)) :
    RH_PsiErrorBound :=
  RH_PsiErrorBound_iff_chebyshevPsi0_sub_id_isBigO.mpr hψ0

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

/-- Normalization bridge between the project `chebyshevPsi` RH-scale error
target and Mathlib's `Chebyshev.psi`. -/
lemma RH_PsiErrorBound_iff_mathlibChebyshevPsi_sub_id_isBigO :
    RH_PsiErrorBound ↔
      (fun x : ℝ => Chebyshev.psi x - x)
        =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2) := by
  rw [RH_PsiErrorBound]
  simp [chebyshevPsi_eq_mathlib]

lemma mathlibChebyshevPsi_sub_id_isBigO_of_RH_PsiErrorBound
    (h : RH_PsiErrorBound) :
    (fun x : ℝ => Chebyshev.psi x - x)
      =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2) :=
  RH_PsiErrorBound_iff_mathlibChebyshevPsi_sub_id_isBigO.mp h

lemma RH_PsiErrorBound_of_mathlibChebyshevPsi_sub_id_isBigO
    (h :
      (fun x : ℝ => Chebyshev.psi x - x)
        =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2)) :
    RH_PsiErrorBound :=
  RH_PsiErrorBound_iff_mathlibChebyshevPsi_sub_id_isBigO.mpr h

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

/-- Exact partial-summation error decomposition connecting the project
`primeCounting`/`logIntegral` normalization to Mathlib's Chebyshev `θ`.

This is the algebraic endpoint needed before estimating the integral term:
`π(x)-Li(x)` is the endpoint `θ(x)-x` error divided by `log x`, plus the
corresponding Abel integral error, plus the lower-endpoint constant. -/
lemma primeCounting_sub_logIntegral_eq_theta_error_integral
    {x : ℝ} (hx : 2 ≤ x) :
    (primeCounting x : ℝ) - logIntegral x =
      (Chebyshev.theta x - x) / Real.log x +
        (∫ t in (2)..x,
          (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) +
        2 / Real.log 2 := by
  have hx_nonneg : 0 ≤ x := by linarith
  have hpc :
      (primeCounting x : ℝ) =
        Chebyshev.theta x / Real.log x +
          ∫ t in (2)..x, Chebyshev.theta t / (t * Real.log t ^ 2) := by
    have hpc_eq := primeCounting_eq_mathlib x hx_nonneg
    have hmath := Chebyshev.primeCounting_eq_theta_div_log_add_integral hx
    rw [hpc_eq]
    exact hmath
  have hli := logIntegral_integration_by_parts x hx
  have htheta_int :
      IntervalIntegrable
        (fun t : ℝ => Chebyshev.theta t / (t * Real.log t ^ 2))
        volume 2 x := by
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hx).2
      (Chebyshev.integrableOn_theta_div_id_mul_log_sq x)
  have hone_int :
      IntervalIntegrable (fun t : ℝ => 1 / Real.log t ^ 2) volume 2 x :=
    Chebyshev.intervalIntegrable_one_div_log_sq (by norm_num) (by linarith)
  have hintegral :
      (∫ t in (2)..x, Chebyshev.theta t / (t * Real.log t ^ 2)) -
          ∫ t in (2)..x, 1 / Real.log t ^ 2 =
        ∫ t in (2)..x,
          (Chebyshev.theta t - t) / (t * Real.log t ^ 2) := by
    rw [← intervalIntegral.integral_sub htheta_int hone_int]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht2 : 2 ≤ t := by
      rw [Set.mem_uIcc] at ht
      cases ht with
      | inl h => exact h.1
      | inr h => exact le_trans hx h.1
    have ht_ne : t ≠ 0 := by linarith
    have hlog_ne : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    field_simp [ht_ne, hlog_ne]
  calc
    (primeCounting x : ℝ) - logIntegral x
        = (Chebyshev.theta x / Real.log x +
              ∫ t in (2)..x, Chebyshev.theta t / (t * Real.log t ^ 2)) -
            (x / Real.log x - 2 / Real.log 2 +
              ∫ t in (2)..x, 1 / Real.log t ^ 2) := by
              rw [hpc, hli]
    _ = (Chebyshev.theta x - x) / Real.log x +
          (((∫ t in (2)..x, Chebyshev.theta t / (t * Real.log t ^ 2)) -
            ∫ t in (2)..x, 1 / Real.log t ^ 2)) +
          2 / Real.log 2 := by
            ring
    _ = (Chebyshev.theta x - x) / Real.log x +
          (∫ t in (2)..x,
            (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) +
          2 / Real.log 2 := by
            rw [hintegral]

/-- The endpoint contribution `(θ(x)-x)/log x` has the right RH-scale size
whenever the `θ` RH-scale error target is available. -/
lemma theta_error_div_log_isBigO_sqrt_mul_log
    (hθ : RH_ThetaErrorBound) :
    (fun x : ℝ => (Chebyshev.theta x - x) / Real.log x)
      =O[atTop] (fun x : ℝ => Real.sqrt x * Real.log x) := by
  rw [RH_ThetaErrorBound] at hθ
  rcases hθ.exists_pos with ⟨C, hCpos, hCO⟩
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [hCO.bound, eventually_ge_atTop (Real.exp 1)] with x hxC hx
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hx1 : 1 ≤ x := by
    have h_exp_one : (1 : ℝ) ≤ Real.exp 1 := by
      rw [Real.one_le_exp_iff]
      norm_num
    exact le_trans h_exp_one hx
  have hlog_pos : 0 < Real.log x := by
    have hlog_ge : 1 ≤ Real.log x :=
      (Real.le_log_iff_exp_le hxpos).mpr hx
    linarith
  have hlog_nonneg : 0 ≤ Real.log x := hlog_pos.le
  have hscale_nonneg : 0 ≤ Real.sqrt x * Real.log x :=
    mul_nonneg (Real.sqrt_nonneg x) hlog_nonneg
  have htarget_nonneg : 0 ≤ Real.sqrt x * (Real.log x)^2 :=
    mul_nonneg (Real.sqrt_nonneg x) (sq_nonneg _)
  have hsqrt_abs : |Real.sqrt x| = Real.sqrt x :=
    abs_of_nonneg (Real.sqrt_nonneg x)
  have hlog_abs : |Real.log x| = Real.log x :=
    abs_of_nonneg hlog_nonneg
  have hlog_sq_abs : |(Real.log x)^2| = (Real.log x)^2 :=
    abs_of_nonneg (sq_nonneg _)
  have hxC' :
      |Chebyshev.theta x - x| ≤
        C * (Real.sqrt x * (Real.log x)^2) := by
    simpa [Real.norm_eq_abs, abs_mul, hsqrt_abs, hlog_sq_abs,
      abs_of_nonneg htarget_nonneg, mul_assoc] using hxC
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div, hlog_abs,
    abs_of_nonneg hscale_nonneg]
  calc
    |Chebyshev.theta x - x| / Real.log x
        ≤ (C * (Real.sqrt x * (Real.log x)^2)) / Real.log x :=
          div_le_div_of_nonneg_right hxC' hlog_nonneg
    _ = C * (Real.sqrt x * Real.log x) := by
          field_simp [hlog_pos.ne']

/-- The fixed lower-endpoint constant in the partial-summation decomposition
is negligible at the RH-scale denominator. -/
lemma two_div_log_two_isBigO_sqrt_mul_log :
    (fun _x : ℝ => 2 / Real.log 2)
      =O[atTop] (fun x : ℝ => Real.sqrt x * Real.log x) := by
  let D : ℝ := Real.sqrt 2 * Real.log 2
  let C : ℝ := (2 / Real.log 2) / D
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD_pos : 0 < D := by
    exact mul_pos (Real.sqrt_pos.2 (by norm_num)) hlog2_pos
  have hconst_nonneg : 0 ≤ 2 / Real.log 2 :=
    div_nonneg (by norm_num) hlog2_pos.le
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hscale_lower : D ≤ Real.sqrt x * Real.log x := by
    have hsqrt_le : Real.sqrt 2 ≤ Real.sqrt x :=
      Real.sqrt_le_sqrt hx
    have hlog_le : Real.log 2 ≤ Real.log x :=
      Real.log_le_log (by norm_num) hx
    simpa [D] using
      mul_le_mul hsqrt_le hlog_le (Real.log_nonneg (by norm_num))
        (Real.sqrt_nonneg x)
  have hscale_nonneg : 0 ≤ Real.sqrt x * Real.log x :=
    le_trans hD_pos.le hscale_lower
  have hC_nonneg : 0 ≤ C :=
    div_nonneg hconst_nonneg hD_pos.le
  have hbound : 2 / Real.log 2 ≤ C * (Real.sqrt x * Real.log x) := by
    have hmul : C * D ≤ C * (Real.sqrt x * Real.log x) :=
      mul_le_mul_of_nonneg_left hscale_lower hC_nonneg
    have hCD : C * D = 2 / Real.log 2 := by
      dsimp [C]
      field_simp [ne_of_gt hD_pos]
    linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hconst_nonneg,
    abs_of_nonneg hscale_nonneg]
  exact hbound

/-- Elementary tail integral bound used by RH-scale partial summation:
`∫_A^x dt / sqrt(t) ≤ 2 sqrt(x)` for `0 < A ≤ x`. -/
lemma integral_one_div_sqrt_le_two_sqrt {A x : ℝ}
    (hA : 0 < A) (hAx : A ≤ x) :
    ∫ t in A..x, 1 / Real.sqrt t ≤ 2 * Real.sqrt x := by
  have h_eq :
      (∫ t in A..x, 1 / Real.sqrt t) =
        ∫ t in A..x, t ^ (-1 / 2 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htpos : 0 < t := by
      rw [Set.mem_uIcc] at ht
      cases ht with
      | inl h => exact lt_of_lt_of_le hA h.1
      | inr h => exact lt_of_lt_of_le hA (le_trans hAx h.1)
    calc
      1 / Real.sqrt t = (t ^ (1 / 2 : ℝ))⁻¹ := by
        rw [Real.sqrt_eq_rpow]
        ring_nf
      _ = t ^ (-(1 / 2 : ℝ)) := by
        rw [Real.rpow_neg (le_of_lt htpos)]
      _ = t ^ (-1 / 2 : ℝ) := by ring_nf
  rw [h_eq, integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -1 / 2))]
  norm_num
  rw [Real.sqrt_eq_rpow x]
  have hA_sqrt_nonneg : 0 ≤ A ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (le_of_lt hA) _
  nlinarith

/-- Interval integrability of the Abel integral error kernel on any interval
starting at height at least `2`. -/
lemma intervalIntegrable_theta_error_div_id_log_sq_of_le
    {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable
      (fun t : ℝ => (Chebyshev.theta t - t) / (t * Real.log t ^ 2))
      volume a b := by
  let thetaTerm : ℝ → ℝ :=
    fun t => Chebyshev.theta t / (t * Real.log t ^ 2)
  let oneTerm : ℝ → ℝ := fun t => 1 / Real.log t ^ 2
  let diffTerm : ℝ → ℝ := fun t => thetaTerm t - oneTerm t
  have hb : 2 ≤ b := le_trans ha hab
  have htheta_2b :
      IntervalIntegrable thetaTerm volume 2 b := by
    dsimp [thetaTerm]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hb).2
      (Chebyshev.integrableOn_theta_div_id_mul_log_sq b)
  have htheta_ab : IntervalIntegrable thetaTerm volume a b := by
    refine htheta_2b.mono_set ?_
    exact Set.uIcc_subset_uIcc
      (by
        rw [Set.mem_uIcc]
        left
        exact ⟨ha, hab⟩)
      (by
        rw [Set.mem_uIcc]
        left
        exact ⟨hb, le_rfl⟩)
  have hone_ab : IntervalIntegrable oneTerm volume a b := by
    dsimp [oneTerm]
    exact Chebyshev.intervalIntegrable_one_div_log_sq (by linarith) (by linarith)
  have hdiff : IntervalIntegrable diffTerm volume a b :=
    htheta_ab.sub hone_ab
  have heq :
      Set.EqOn diffTerm
        (fun t : ℝ => (Chebyshev.theta t - t) / (t * Real.log t ^ 2))
        (Set.uIoc a b) := by
    intro t ht
    have htu : t ∈ Set.uIcc a b := Set.uIoc_subset_uIcc ht
    have ht2 : 2 ≤ t := by
      rw [Set.mem_uIcc] at htu
      cases htu with
      | inl h => exact le_trans ha h.1
      | inr h => exact le_trans ha (le_trans hab h.1)
    have ht_ne : t ≠ 0 := by linarith
    have hlog_ne : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    dsimp [diffTerm, thetaTerm, oneTerm]
    field_simp [ht_ne, hlog_ne]
  exact (intervalIntegrable_congr heq).mp hdiff

/-- Under the RH-scale `θ` error target, the Abel integral error in the
partial-summation formula has the right `sqrt x log x` size. -/
lemma theta_error_integral_isBigO_sqrt_mul_log
    (hθ : RH_ThetaErrorBound) :
    (fun x : ℝ =>
      ∫ t in (2)..x,
        (Chebyshev.theta t - t) / (t * Real.log t ^ 2))
      =O[atTop] (fun x : ℝ => Real.sqrt x * Real.log x) := by
  rw [RH_ThetaErrorBound] at hθ
  rcases hθ.exists_pos with ⟨Cθ, hCθ_pos, hθO⟩
  rcases eventually_atTop.mp hθO.bound with ⟨A0, hθ_bound⟩
  let A : ℝ := max (max A0 (Real.exp 1)) 2
  let K : ℝ → ℝ := fun t : ℝ =>
    (Chebyshev.theta t - t) / (t * Real.log t ^ 2)
  let I0 : ℝ := ∫ t in (2)..A, K t
  let D : ℝ := Real.sqrt 2 * Real.log 2
  let C : ℝ := |I0| / D + 2 * Cθ
  have hA2 : 2 ≤ A := le_max_right (max A0 (Real.exp 1)) 2
  have hA0 : A0 ≤ A := le_trans (le_max_left A0 (Real.exp 1))
    (le_max_left (max A0 (Real.exp 1)) 2)
  have hAexp : Real.exp 1 ≤ A := le_trans (le_max_right A0 (Real.exp 1))
    (le_max_left (max A0 (Real.exp 1)) 2)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD_pos : 0 < D := by
    exact mul_pos (Real.sqrt_pos.2 (by norm_num)) hlog2_pos
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop A] with x hxA
  have hx2 : 2 ≤ x := le_trans hA2 hxA
  have hxpos : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hscale_nonneg : 0 ≤ Real.sqrt x * Real.log x :=
    mul_nonneg (Real.sqrt_nonneg x) hlog_nonneg
  have hD_le_scale : D ≤ Real.sqrt x * Real.log x := by
    have hsqrt_le : Real.sqrt 2 ≤ Real.sqrt x :=
      Real.sqrt_le_sqrt hx2
    have hlog_le : Real.log 2 ≤ Real.log x :=
      Real.log_le_log (by norm_num) hx2
    simpa [D] using
      mul_le_mul hsqrt_le hlog_le (Real.log_nonneg (by norm_num))
        (Real.sqrt_nonneg x)
  have hK_2A : IntervalIntegrable K volume 2 A :=
    intervalIntegrable_theta_error_div_id_log_sq_of_le
      (a := 2) (b := A) (by norm_num) hA2
  have hK_Ax : IntervalIntegrable K volume A x :=
    intervalIntegrable_theta_error_div_id_log_sq_of_le hA2 hxA
  have hsplit :
      (∫ t in (2)..x, K t) =
        (∫ t in (2)..A, K t) + ∫ t in A..x, K t := by
    simpa [K] using
      (intervalIntegral.integral_add_adjacent_intervals hK_2A hK_Ax).symm
  have htail_abs :
      |∫ t in A..x, K t| ≤ 2 * Cθ * Real.sqrt x := by
    have habs :
        |∫ t in A..x, K t| ≤ ∫ t in A..x, |K t| :=
      intervalIntegral.abs_integral_le_integral_abs hxA
    have h_absK : IntervalIntegrable (fun t : ℝ => |K t|) volume A x :=
      hK_Ax.abs
    have h_bound_fun :
        IntervalIntegrable (fun t : ℝ => Cθ * (1 / Real.sqrt t)) volume A x := by
      refine ContinuousOn.intervalIntegrable ?_
      intro t ht
      refine ContinuousAt.continuousWithinAt ?_
      exact continuousAt_const.mul
        (continuousAt_const.div (Real.continuous_sqrt.continuousAt)
          (by
            have htpos : 0 < t := by
              rw [Set.mem_uIcc] at ht
              cases ht with
              | inl h => exact lt_of_lt_of_le (by linarith : 0 < A) h.1
              | inr h => exact lt_of_lt_of_le (by linarith : 0 < A) (le_trans hxA h.1)
            exact (Real.sqrt_pos.2 htpos).ne'))
    have hmono :
        (∫ t in A..x, |K t|) ≤
          ∫ t in A..x, Cθ * (1 / Real.sqrt t) := by
      refine intervalIntegral.integral_mono_on hxA h_absK h_bound_fun ?_
      intro t ht
      have htA : A ≤ t := ht.1
      have ht2 : 2 ≤ t := le_trans hA2 htA
      have htpos : 0 < t := by linarith
      have ht1 : 1 ≤ t := by linarith
      have hlog_pos : 0 < Real.log t := by
        have hlog_ge : 1 ≤ Real.log t :=
          (Real.le_log_iff_exp_le htpos).mpr (le_trans hAexp htA)
        linarith
      have hlog_nonneg_t : 0 ≤ Real.log t := hlog_pos.le
      have hsqrt_abs : |Real.sqrt t| = Real.sqrt t :=
        abs_of_nonneg (Real.sqrt_nonneg t)
      have hlog_sq_abs : |(Real.log t)^2| = (Real.log t)^2 :=
        abs_of_nonneg (sq_nonneg _)
      have htarget_nonneg : 0 ≤ Real.sqrt t * (Real.log t)^2 :=
        mul_nonneg (Real.sqrt_nonneg t) (sq_nonneg _)
      have hθt := hθ_bound t (le_trans hA0 htA)
      have hθt_abs :
          |Chebyshev.theta t - t| ≤
            Cθ * (Real.sqrt t * (Real.log t)^2) := by
        simpa [Real.norm_eq_abs, abs_mul, hsqrt_abs, hlog_sq_abs,
          abs_of_nonneg htarget_nonneg, mul_assoc] using hθt
      have ht_ne : t ≠ 0 := by linarith
      have hlog_ne : Real.log t ≠ 0 := hlog_pos.ne'
      have hden_pos : 0 < t * Real.log t ^ 2 := by
        exact mul_pos htpos (sq_pos_of_ne_zero hlog_ne)
      calc
        |K t|
            = |Chebyshev.theta t - t| / (t * Real.log t ^ 2) := by
              simp [K, abs_div, abs_of_pos hden_pos]
        _ ≤ (Cθ * (Real.sqrt t * (Real.log t)^2)) /
              (t * Real.log t ^ 2) :=
              div_le_div_of_nonneg_right hθt_abs hden_pos.le
        _ = Cθ * (1 / Real.sqrt t) := by
              field_simp [ht_ne, hlog_ne, (Real.sqrt_pos.2 htpos).ne']
              rw [Real.sq_sqrt htpos.le]
    have htail_le :
        |∫ t in A..x, K t| ≤
          ∫ t in A..x, Cθ * (1 / Real.sqrt t) :=
      le_trans habs hmono
    have hconst_pull :
        (∫ t in A..x, Cθ * (1 / Real.sqrt t)) =
          Cθ * ∫ t in A..x, 1 / Real.sqrt t := by
      rw [intervalIntegral.integral_const_mul]
    have htail_bound :
        (∫ t in A..x, Cθ * (1 / Real.sqrt t)) ≤
          Cθ * (2 * Real.sqrt x) := by
      rw [hconst_pull]
      exact mul_le_mul_of_nonneg_left
        (integral_one_div_sqrt_le_two_sqrt (by linarith : 0 < A) hxA)
        hCθ_pos.le
    have hrewrite : Cθ * (2 * Real.sqrt x) = 2 * Cθ * Real.sqrt x := by ring
    exact le_trans htail_le (by simpa [hrewrite] using htail_bound)
  have htail_scale :
      |∫ t in A..x, K t| ≤ 2 * Cθ * (Real.sqrt x * Real.log x) := by
    have hlog_ge_one : 1 ≤ Real.log x :=
      (Real.le_log_iff_exp_le hxpos).mpr (le_trans hAexp hxA)
    have hsqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    have htail_mono :
        2 * Cθ * Real.sqrt x ≤
          2 * Cθ * (Real.sqrt x * Real.log x) := by
      have hcoef_nonneg : 0 ≤ 2 * Cθ :=
        mul_nonneg (by norm_num) hCθ_pos.le
      have hsqrt_le : Real.sqrt x ≤ Real.sqrt x * Real.log x := by
        nlinarith
      exact mul_le_mul_of_nonneg_left hsqrt_le hcoef_nonneg
    exact le_trans htail_abs htail_mono
  have hinitial_scale :
      |I0| ≤ (|I0| / D) * (Real.sqrt x * Real.log x) := by
    have hcoef_nonneg : 0 ≤ |I0| / D :=
      div_nonneg (abs_nonneg _) hD_pos.le
    have hmul :
        (|I0| / D) * D ≤ (|I0| / D) * (Real.sqrt x * Real.log x) :=
      mul_le_mul_of_nonneg_left hD_le_scale hcoef_nonneg
    have hmul_eq : (|I0| / D) * D = |I0| := by
      field_simp [ne_of_gt hD_pos]
    linarith
  have htotal :
      |∫ t in (2)..x, K t| ≤ C * (Real.sqrt x * Real.log x) := by
    calc
      |∫ t in (2)..x, K t|
          = |I0 + ∫ t in A..x, K t| := by
            rw [hsplit]
      _ ≤ |I0| + |∫ t in A..x, K t| := abs_add_le _ _
      _ ≤ (|I0| / D) * (Real.sqrt x * Real.log x) +
            2 * Cθ * (Real.sqrt x * Real.log x) :=
            add_le_add hinitial_scale htail_scale
      _ = C * (Real.sqrt x * Real.log x) := by
            dsimp [C]
            ring
  have hsqrt_abs : |Real.sqrt x| = Real.sqrt x :=
    abs_of_nonneg (Real.sqrt_nonneg x)
  have hlog_abs : |Real.log x| = Real.log x :=
    abs_of_nonneg hlog_nonneg
  simpa [K, Real.norm_eq_abs, abs_mul, hsqrt_abs, hlog_abs,
    abs_of_nonneg hscale_nonneg, mul_assoc] using htotal

/-- Conditional partial-summation bridge from the `θ` RH-scale target to the
prime-counting `Li` RH-scale target.

The only remaining analytic input is the Abel integral error estimate, isolated
as `hintegral`. -/
lemma RH_PrimeCountingLiErrorBound_of_RH_ThetaErrorBound_of_integral_error
    (hθ : RH_ThetaErrorBound)
    (hintegral :
      (fun x : ℝ =>
        ∫ t in (2)..x,
          (Chebyshev.theta t - t) / (t * Real.log t ^ 2))
        =O[atTop] (fun x : ℝ => Real.sqrt x * Real.log x)) :
    RH_PrimeCountingLiErrorBound := by
  rw [RH_PrimeCountingLiErrorBound]
  have hend := theta_error_div_log_isBigO_sqrt_mul_log hθ
  have hconst := two_div_log_two_isBigO_sqrt_mul_log
  have hsum := (hend.add hintegral).add hconst
  refine hsum.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  exact (primeCounting_sub_logIntegral_eq_theta_error_integral hx).symm

/-- Same partial-summation bridge with a `ψ` RH-scale hypothesis; the existing
`ψ`/`θ` equivalence discharges the endpoint input. -/
lemma RH_PrimeCountingLiErrorBound_of_RH_PsiErrorBound_of_integral_error
    (hψ : RH_PsiErrorBound)
    (hintegral :
      (fun x : ℝ =>
        ∫ t in (2)..x,
          (Chebyshev.theta t - t) / (t * Real.log t ^ 2))
        =O[atTop] (fun x : ℝ => Real.sqrt x * Real.log x)) :
    RH_PrimeCountingLiErrorBound :=
  RH_PrimeCountingLiErrorBound_of_RH_ThetaErrorBound_of_integral_error
    (RH_ThetaErrorBound_of_RH_PsiErrorBound hψ) hintegral

/-- Closed partial-summation bridge from the `θ` RH-scale target to the
prime-counting `Li` RH-scale target. -/
lemma RH_PrimeCountingLiErrorBound_of_RH_ThetaErrorBound
    (hθ : RH_ThetaErrorBound) : RH_PrimeCountingLiErrorBound :=
  RH_PrimeCountingLiErrorBound_of_RH_ThetaErrorBound_of_integral_error
    hθ (theta_error_integral_isBigO_sqrt_mul_log hθ)

/-- Closed partial-summation bridge from the `ψ` RH-scale target to the
prime-counting `Li` RH-scale target. -/
lemma RH_PrimeCountingLiErrorBound_of_RH_PsiErrorBound
    (hψ : RH_PsiErrorBound) : RH_PrimeCountingLiErrorBound :=
  RH_PrimeCountingLiErrorBound_of_RH_ThetaErrorBound
    (RH_ThetaErrorBound_of_RH_PsiErrorBound hψ)

/-- Closed partial-summation bridge from the midpoint `ψ₀` RH-scale target to
the prime-counting `Li` RH-scale target. -/
lemma RH_PrimeCountingLiErrorBound_of_chebyshevPsi0_sub_id_isBigO
    (hψ0 :
      (fun x : ℝ => chebyshevPsi0 x - x)
        =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2)) :
    RH_PrimeCountingLiErrorBound :=
  RH_PrimeCountingLiErrorBound_of_RH_PsiErrorBound
    (RH_PsiErrorBound_of_chebyshevPsi0_sub_id_isBigO hψ0)

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

/-- RH-scale `θ` error implies the pointwise textbook prime-counting RH error
target. -/
lemma RH_ErrorBound_of_RH_ThetaErrorBound
    (hθ : RH_ThetaErrorBound) : RH_ErrorBound :=
  RH_ErrorBound_of_RH_PrimeCountingLiErrorBound
    (RH_PrimeCountingLiErrorBound_of_RH_ThetaErrorBound hθ)

/-- RH-scale `ψ` error implies the pointwise textbook prime-counting RH error
target. -/
lemma RH_ErrorBound_of_RH_PsiErrorBound
    (hψ : RH_PsiErrorBound) : RH_ErrorBound :=
  RH_ErrorBound_of_RH_ThetaErrorBound
    (RH_ThetaErrorBound_of_RH_PsiErrorBound hψ)

/-- Midpoint `ψ₀` RH-scale error implies the pointwise textbook
prime-counting RH error target. -/
lemma RH_ErrorBound_of_chebyshevPsi0_sub_id_isBigO
    (hψ0 :
      (fun x : ℝ => chebyshevPsi0 x - x)
        =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2)) :
    RH_ErrorBound :=
  RH_ErrorBound_of_RH_PsiErrorBound
    (RH_PsiErrorBound_of_chebyshevPsi0_sub_id_isBigO hψ0)

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

/-- Any positive power dominates `(log x)^2`. -/
lemma log_sq_div_rpow_tendsto_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => (Real.log x)^2 / x ^ a) atTop (𝓝 0) := by
  let b : ℝ := a / 2
  have hb : 0 < b := by
    dsimp [b]
    linarith
  have hq :
      Tendsto (fun x : ℝ => Real.log x / x ^ b) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop hb).tendsto_div_nhds_zero
  have hsq := hq.mul hq
  have heq :
      (fun x : ℝ => (Real.log x / x ^ b) *
          (Real.log x / x ^ b))
        =ᶠ[atTop] fun x : ℝ => (Real.log x)^2 / x ^ a := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hxpow_ne : x ^ b ≠ 0 :=
      (Real.rpow_pos_of_pos hx b).ne'
    calc
      (Real.log x / x ^ b) * (Real.log x / x ^ b)
          = (Real.log x)^2 / (x ^ b * x ^ b) := by
            field_simp [hxpow_ne]
      _ = (Real.log x)^2 / x ^ (b + b) := by
            rw [Real.rpow_add hx]
      _ = (Real.log x)^2 / x ^ a := by
            rw [show b + b = a by dsimp [b]; ring]
  simpa using hsq.congr' heq

/-- The RH-scale `sqrt x * log^2 x` error is smaller than every power `x^θ`
with `θ > 1/2`. -/
lemma sqrt_mul_log_sq_isLittleO_rpow_of_half_lt {θ : ℝ}
    (hθ : (1 / 2 : ℝ) < θ) :
    (fun x : ℝ => Real.sqrt x * (Real.log x)^2)
      =o[atTop] (fun x : ℝ => x ^ θ) := by
  have ha : 0 < θ - (1 / 2 : ℝ) := by linarith
  have hratio :
      Tendsto
        (fun x : ℝ => (Real.sqrt x * (Real.log x)^2) / x ^ θ)
        atTop (𝓝 0) := by
    have hlog := log_sq_div_rpow_tendsto_zero ha
    have heq :
        (fun x : ℝ => (Real.sqrt x * (Real.log x)^2) / x ^ θ)
          =ᶠ[atTop]
            fun x : ℝ => (Real.log x)^2 / x ^ (θ - (1 / 2 : ℝ)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have hx_half_ne : x ^ (1 / 2 : ℝ) ≠ 0 :=
        (Real.rpow_pos_of_pos hx (1 / 2 : ℝ)).ne'
      have hx_gap_ne : x ^ (θ - (1 / 2 : ℝ)) ≠ 0 :=
        (Real.rpow_pos_of_pos hx (θ - (1 / 2 : ℝ))).ne'
      have hsqrt_eq : Real.sqrt x = x ^ (1 / 2 : ℝ) :=
        Real.sqrt_eq_rpow x
      have hpowθ :
          x ^ θ = x ^ (1 / 2 : ℝ) * x ^ (θ - (1 / 2 : ℝ)) := by
        rw [← Real.rpow_add hx]
        ring_nf
      calc
        (Real.sqrt x * (Real.log x)^2) / x ^ θ =
            (x ^ (1 / 2 : ℝ) * (Real.log x)^2) / x ^ θ := by
              rw [hsqrt_eq]
        _ = (x ^ (1 / 2 : ℝ) * (Real.log x)^2) /
            (x ^ (1 / 2 : ℝ) * x ^ (θ - (1 / 2 : ℝ))) := by
              rw [hpowθ]
        _ = (Real.log x)^2 / x ^ (θ - (1 / 2 : ℝ)) := by
              field_simp [hx_half_ne, hx_gap_ne]
    exact hlog.congr' heq.symm
  refine (isLittleO_iff_tendsto' ?_).2 hratio
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx hzero
  exact ((Real.rpow_pos_of_pos hx θ).ne' hzero).elim

/-- The Chebyshev `ψ` and `θ` PNT-normalized forms differ by `o(1)`. -/
lemma chebyshevPsi_sub_theta_div_id_tendsto_zero :
    Tendsto (fun x : ℝ =>
      (chebyshevPsi x - Chebyshev.theta x) / x) atTop (𝓝 0) :=
  (psi_sub_theta_isBigO_rh_scale.trans_isLittleO
    sqrt_mul_log_sq_isLittleO_id).tendsto_div_nhds_zero

/-- The Chebyshev-ψ PNT form is equivalent to the Mathlib Chebyshev-θ
asymptotic.  This exposes the comparison used internally in the equivalence of
the project PNT forms. -/
lemma PNTForm3_iff_chebyshevTheta_asymptotic :
    PNTForm3 ↔
      Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) := by
  constructor
  · intro hψ
    have hdiff := chebyshevPsi_sub_theta_div_id_tendsto_zero
    have hsub :
        Tendsto
          (fun x : ℝ =>
            chebyshevPsi x / x -
              (chebyshevPsi x - Chebyshev.theta x) / x)
          atTop (𝓝 1) := by
      simpa using hψ.sub hdiff
    have heq :
        (fun x : ℝ =>
            chebyshevPsi x / x -
              (chebyshevPsi x - Chebyshev.theta x) / x)
          =ᶠ[atTop] fun x : ℝ => Chebyshev.theta x / x := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      field_simp [hx.ne']
      ring
    exact hsub.congr' heq
  · intro hθ
    have hdiff := chebyshevPsi_sub_theta_div_id_tendsto_zero
    have hadd :
        Tendsto
          (fun x : ℝ =>
            Chebyshev.theta x / x +
              (chebyshevPsi x - Chebyshev.theta x) / x)
          atTop (𝓝 1) := by
      simpa using hθ.add hdiff
    have heq :
        (fun x : ℝ =>
            Chebyshev.theta x / x +
              (chebyshevPsi x - Chebyshev.theta x) / x)
          =ᶠ[atTop] fun x : ℝ => chebyshevPsi x / x := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      field_simp [hx.ne']
      ring
    simpa [PNTForm3] using hadd.congr' heq

lemma PNTForm1_iff_chebyshevTheta_asymptotic :
    PNTForm1 ↔
      Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) :=
  Iff.trans PNTForm1_iff_PNTForm3 PNTForm3_iff_chebyshevTheta_asymptotic

lemma PNTForm2_iff_chebyshevTheta_asymptotic :
    PNTForm2 ↔
      Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) :=
  Iff.trans PNTForm2_iff_PNTForm3 PNTForm3_iff_chebyshevTheta_asymptotic

/-- The project Chebyshev-ψ PNT form is definitionally the Mathlib
Chebyshev-ψ asymptotic after unfolding the local normalization. -/
lemma PNTForm3_iff_mathlibChebyshevPsi_asymptotic :
    PNTForm3 ↔
      Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) := by
  rw [PNTForm3]
  simp [chebyshevPsi_eq_mathlib]

lemma PNTForm1_iff_mathlibChebyshevPsi_asymptotic :
    PNTForm1 ↔
      Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) :=
  Iff.trans PNTForm1_iff_PNTForm3 PNTForm3_iff_mathlibChebyshevPsi_asymptotic

lemma PNTForm2_iff_mathlibChebyshevPsi_asymptotic :
    PNTForm2 ↔
      Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) :=
  Iff.trans PNTForm2_iff_PNTForm3 PNTForm3_iff_mathlibChebyshevPsi_asymptotic

/-- A Mathlib-level Chebyshev-`θ` PNT asymptotic closes all three project PNT
forms.  This isolates the exact remaining upstream-style statement needed for
`PNTForm1`, `PNTForm2`, and `PNTForm3`; the `ψ - θ` gap is already negligible
using the available Chebyshev bound. -/
lemma PNTForms_of_chebyshevTheta_asymptotic
    (hθ : Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1)) :
    PNTForm1 ∧ PNTForm2 ∧ PNTForm3 := by
  have hdiffO :
      (fun x : ℝ => chebyshevPsi x - Chebyshev.theta x)
        =o[atTop] (fun x : ℝ => x) :=
    psi_sub_theta_isBigO_rh_scale.trans_isLittleO sqrt_mul_log_sq_isLittleO_id
  have hdiff :
      Tendsto (fun x : ℝ => (chebyshevPsi x - Chebyshev.theta x) / x)
        atTop (𝓝 0) :=
    hdiffO.tendsto_div_nhds_zero
  have hψ : PNTForm3 := by
    have hsum :
        Tendsto
          (fun x : ℝ =>
            Chebyshev.theta x / x + (chebyshevPsi x - Chebyshev.theta x) / x)
          atTop (𝓝 1) := by
      simpa using hθ.add hdiff
    have heq :
        (fun x : ℝ =>
            Chebyshev.theta x / x + (chebyshevPsi x - Chebyshev.theta x) / x)
          =ᶠ[atTop] fun x : ℝ => chebyshevPsi x / x := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      field_simp [hx.ne']
      ring
    simpa [PNTForm3] using hsum.congr' heq
  exact ⟨PNTForm1_of_PNTForm3 hψ, PNTForm2_of_PNTForm3 hψ, hψ⟩

/-- A Mathlib-level Chebyshev-`ψ` PNT asymptotic closes all three project PNT
forms. -/
lemma PNTForms_of_mathlibChebyshevPsi_asymptotic
    (hψ : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1)) :
    PNTForm1 ∧ PNTForm2 ∧ PNTForm3 := by
  have hlocal : PNTForm3 := by
    simpa [PNTForm3, chebyshevPsi_eq_mathlib] using hψ
  exact ⟨PNTForm1_of_PNTForm3 hlocal, PNTForm2_of_PNTForm3 hlocal, hlocal⟩

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

lemma RH_ErrorBound.isLittleO_logIntegral
    (h : RH_ErrorBound) :
    (fun x : ℝ => (primeCounting x : ℝ) - logIntegral x)
      =o[atTop] (fun x : ℝ => logIntegral x) :=
  (RH_PrimeCountingLiErrorBound_of_RH_ErrorBound h).isLittleO_logIntegral

lemma RH_ErrorBound.isLittleO_id
    (h : RH_ErrorBound) :
    (fun x : ℝ => (primeCounting x : ℝ) - logIntegral x)
      =o[atTop] (fun x : ℝ => x) :=
  (RH_PrimeCountingLiErrorBound_of_RH_ErrorBound h).isLittleO_id

lemma RH_PrimeCountingLiErrorBound.isBigO_logIntegral
    (h : RH_PrimeCountingLiErrorBound) :
    (fun x : ℝ => (primeCounting x : ℝ) - logIntegral x)
      =O[atTop] (fun x : ℝ => logIntegral x) :=
  h.isLittleO_logIntegral.isBigO

lemma RH_PrimeCountingLiErrorBound.isBigO_id
    (h : RH_PrimeCountingLiErrorBound) :
    (fun x : ℝ => (primeCounting x : ℝ) - logIntegral x)
      =O[atTop] (fun x : ℝ => x) :=
  h.isLittleO_id.isBigO

lemma RH_ErrorBound.isBigO_logIntegral
    (h : RH_ErrorBound) :
    (fun x : ℝ => (primeCounting x : ℝ) - logIntegral x)
      =O[atTop] (fun x : ℝ => logIntegral x) :=
  h.isLittleO_logIntegral.isBigO

lemma RH_ErrorBound.isBigO_id
    (h : RH_ErrorBound) :
    (fun x : ℝ => (primeCounting x : ℝ) - logIntegral x)
      =O[atTop] (fun x : ℝ => x) :=
  h.isLittleO_id.isBigO

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

lemma RH_ThetaErrorBound.isLittleO_id
    (h : RH_ThetaErrorBound) :
    (fun x : ℝ => Chebyshev.theta x - x) =o[atTop] (fun x : ℝ => x) := by
  rw [RH_ThetaErrorBound] at h
  exact h.trans_isLittleO sqrt_mul_log_sq_isLittleO_id

lemma RH_PsiErrorBound.isBigO_id
    (h : RH_PsiErrorBound) :
    (fun x : ℝ => chebyshevPsi x - x) =O[atTop] (fun x : ℝ => x) :=
  h.isLittleO_id.isBigO

lemma RH_ThetaErrorBound.isBigO_id
    (h : RH_ThetaErrorBound) :
    (fun x : ℝ => Chebyshev.theta x - x) =O[atTop] (fun x : ℝ => x) :=
  h.isLittleO_id.isBigO

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

/-- Midpoint `ψ₀` RH-scale error implies the Chebyshev form of PNT. -/
lemma PNTForm3_of_chebyshevPsi0_sub_id_isBigO
    (hψ0 :
      (fun x : ℝ => chebyshevPsi0 x - x)
        =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2)) :
    PNTForm3 :=
  PNTForm3_of_RH_PsiErrorBound
    (RH_PsiErrorBound_of_chebyshevPsi0_sub_id_isBigO hψ0)

/-- Midpoint `ψ₀` RH-scale error implies the `π(x) ~ Li(x)` PNT form. -/
lemma PNTForm2_of_chebyshevPsi0_sub_id_isBigO
    (hψ0 :
      (fun x : ℝ => chebyshevPsi0 x - x)
        =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2)) :
    PNTForm2 :=
  PNTForm2_of_RH_PsiErrorBound
    (RH_PsiErrorBound_of_chebyshevPsi0_sub_id_isBigO hψ0)

/-- Midpoint `ψ₀` RH-scale error implies the `π(x) ~ x / log x` PNT form. -/
lemma PNTForm1_of_chebyshevPsi0_sub_id_isBigO
    (hψ0 :
      (fun x : ℝ => chebyshevPsi0 x - x)
        =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2)) :
    PNTForm1 :=
  PNTForm1_of_RH_PsiErrorBound
    (RH_PsiErrorBound_of_chebyshevPsi0_sub_id_isBigO hψ0)

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

lemma PNTForms_of_chebyshevPsi0_sub_id_isBigO
    (hψ0 :
      (fun x : ℝ => chebyshevPsi0 x - x)
        =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2)) :
    PNTForm1 ∧ PNTForm2 ∧ PNTForm3 :=
  PNTForms_of_RH_PsiErrorBound
    (RH_PsiErrorBound_of_chebyshevPsi0_sub_id_isBigO hψ0)

/-- Direct Chebyshev-ψ asymptotic consequence of the `ψ` RH-scale error
target, stated without requiring callers to unfold `PNTForm3`. -/
lemma chebyshevPsi_asymptotic_of_RH_PsiErrorBound
    (hψ : RH_PsiErrorBound) :
    Tendsto (fun x : ℝ => chebyshevPsi x / x) atTop (𝓝 1) :=
  PNTForm3_of_RH_PsiErrorBound hψ

/-- Direct Chebyshev-ψ asymptotic consequence of the `θ` RH-scale error
target. -/
lemma chebyshevPsi_asymptotic_of_RH_ThetaErrorBound
    (hθ : RH_ThetaErrorBound) :
    Tendsto (fun x : ℝ => chebyshevPsi x / x) atTop (𝓝 1) :=
  PNTForm3_of_RH_ThetaErrorBound hθ

/-- Mathlib Chebyshev-ψ asymptotic consequence of the local `ψ` RH-scale
error target. -/
lemma mathlibChebyshevPsi_asymptotic_of_RH_PsiErrorBound
    (hψ : RH_PsiErrorBound) :
    Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) :=
  PNTForm3_iff_mathlibChebyshevPsi_asymptotic.mp
    (PNTForm3_of_RH_PsiErrorBound hψ)

/-- Mathlib Chebyshev-ψ asymptotic consequence of the local `θ` RH-scale
error target. -/
lemma mathlibChebyshevPsi_asymptotic_of_RH_ThetaErrorBound
    (hθ : RH_ThetaErrorBound) :
    Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) :=
  PNTForm3_iff_mathlibChebyshevPsi_asymptotic.mp
    (PNTForm3_of_RH_ThetaErrorBound hθ)

/-- Mathlib Chebyshev-θ asymptotic consequence of the local `θ` RH-scale
error target. -/
lemma chebyshevTheta_asymptotic_of_RH_ThetaErrorBound
    (hθ : RH_ThetaErrorBound) :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) :=
  PNTForm3_iff_chebyshevTheta_asymptotic.mp
    (PNTForm3_of_RH_ThetaErrorBound hθ)

/-- Mathlib Chebyshev-θ asymptotic consequence of the local `ψ` RH-scale
error target. -/
lemma chebyshevTheta_asymptotic_of_RH_PsiErrorBound
    (hψ : RH_PsiErrorBound) :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) :=
  PNTForm3_iff_chebyshevTheta_asymptotic.mp
    (PNTForm3_of_RH_PsiErrorBound hψ)

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

/-- Close the RH/error target from a future RH-to-`ψ` error theorem plus the
reverse implication from the prime-counting error target. -/
lemma rh_iff_optimal_error_of_RH_PsiErrorBound_implications
    (h_forward : RiemannHypothesis.Statement → RH_PsiErrorBound)
    (h_reverse : RH_PrimeCountingLiErrorBound → RiemannHypothesis.Statement) :
    rh_iff_optimal_error :=
  rh_iff_optimal_error_of_implications
    (fun hRH => RH_PrimeCountingLiErrorBound_of_RH_PsiErrorBound (h_forward hRH))
    h_reverse

/-- Close the RH/error target from a future RH-to-`θ` error theorem plus the
reverse implication from the prime-counting error target. -/
lemma rh_iff_optimal_error_of_RH_ThetaErrorBound_implications
    (h_forward : RiemannHypothesis.Statement → RH_ThetaErrorBound)
    (h_reverse : RH_PrimeCountingLiErrorBound → RiemannHypothesis.Statement) :
    rh_iff_optimal_error :=
  rh_iff_optimal_error_of_implications
    (fun hRH => RH_PrimeCountingLiErrorBound_of_RH_ThetaErrorBound (h_forward hRH))
    h_reverse

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

lemma RH_PrimeCountingLiErrorBound_iff_RiemannHypothesis_of_rh_iff_optimal_error
    (h : rh_iff_optimal_error) :
    RH_PrimeCountingLiErrorBound ↔ RiemannHypothesis.Statement :=
  h.symm

lemma RH_ErrorBound_iff_RiemannHypothesis_of_rh_iff_optimal_error
    (h : rh_iff_optimal_error) :
    RH_ErrorBound ↔ RiemannHypothesis.Statement :=
  (rh_iff_pointwise_error_iff.mp h).symm

lemma PNTForms_of_rh_iff_optimal_error
    (h : rh_iff_optimal_error) :
    RiemannHypothesis.Statement → PNTForm1 ∧ PNTForm2 ∧ PNTForm3 := by
  intro hRH
  exact PNTForms_of_RH_PrimeCountingLiErrorBound (h.mp hRH)

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

/-! ### Zero-pair contribution skeleton

This is the finite combinatorial core behind the Stechkin/Heath-Brown pairing
condition `Re F(z) + Re F(center - z) >= 0`.  It deliberately stays independent
of the concrete Laplace transform used in an explicit zero detector.
-/

/-- A contribution function is nonnegative after pairing around `center`. -/
abbrev ZeroPairContributionNonnegative (F : ℂ → ℂ) (center : ℂ) : Prop :=
  ∀ z : ℂ, 0 ≤ (F z).re + (F (center - z)).re

/-- Strip-local Stechkin/Heath-Brown pair positivity.

The positivity assumption is only required for points whose real part lies in
`[0, center]`; this is the shape needed before specializing to a finite family
of zeros known to lie in the relevant strip. -/
abbrev LaplacePairPositive (F : ℂ → ℂ) (center : ℝ) : Prop :=
  ∀ z : ℂ, 0 ≤ z.re → z.re ≤ center →
    0 ≤ (F z).re + (F ((center : ℂ) - z)).re

/-- A stronger pointwise positivity certificate on the strip supplies the
Stechkin/Heath-Brown pair-positivity interface.

This is useful for concrete kernels whose real part is known to be
nonnegative throughout the critical strip: both `z` and `center - z` remain in
the same strip, so their paired contribution is nonnegative. -/
lemma laplacePairPositive_of_re_nonnegative_on_strip
    {F : ℂ → ℂ} {center : ℝ}
    (hF : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ center → 0 ≤ (F z).re) :
    LaplacePairPositive F center := by
  intro z hz_left hz_right
  have hpair_left : 0 ≤ ((center : ℂ) - z).re := by
    simp [Complex.sub_re]
    exact hz_right
  have hpair_right : ((center : ℂ) - z).re ≤ center := by
    simp [Complex.sub_re]
    linarith
  exact add_nonneg (hF z hz_left hz_right)
    (hF ((center : ℂ) - z) hpair_left hpair_right)

/-- Center-one version of
`laplacePairPositive_of_re_nonnegative_on_strip`, matching the zeta
functional-equation pairing `ρ ↦ 1 - ρ`. -/
lemma laplacePairPositive_one_of_re_nonnegative_on_critical_strip
    {F : ℂ → ℂ}
    (hF : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 0 ≤ (F z).re) :
    LaplacePairPositive F 1 :=
  laplacePairPositive_of_re_nonnegative_on_strip (F := F)
    (center := 1) hF

/-- Finite nonnegative real-weighted combinations of complex kernels. -/
noncomputable def weightedKernelCombo
    (K : Finset ℕ) (w : ℕ → ℝ) (F : ℕ → ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ k ∈ K, (w k : ℂ) * F k z

/-- Pointwise strip real-part positivity is preserved by finite nonnegative
real-weighted kernel combinations. -/
lemma weightedKernelCombo_re_nonnegative_on_strip
    {K : Finset ℕ} {w : ℕ → ℝ} {F : ℕ → ℂ → ℂ} {center : ℝ}
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hF : ∀ k ∈ K, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ center →
      0 ≤ (F k z).re) :
    ∀ z : ℂ, 0 ≤ z.re → z.re ≤ center →
      0 ≤ (weightedKernelCombo K w F z).re := by
  intro z hz_left hz_right
  rw [weightedKernelCombo]
  change 0 ≤ Complex.reCLM (∑ k ∈ K, (w k : ℂ) * F k z)
  rw [map_sum]
  refine Finset.sum_nonneg ?_
  intro k hk
  exact by
    simpa [Complex.mul_re] using
      mul_nonneg (hw k hk) (hF k hk z hz_left hz_right)

/-- Strip-local pair positivity is preserved by finite nonnegative real-weighted
kernel combinations. -/
lemma laplacePairPositive_weightedKernelCombo
    {K : Finset ℕ} {w : ℕ → ℝ} {F : ℕ → ℂ → ℂ} {center : ℝ}
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hF : ∀ k ∈ K, LaplacePairPositive (F k) center) :
    LaplacePairPositive (weightedKernelCombo K w F) center := by
  intro z hz_left hz_right
  rw [weightedKernelCombo]
  change 0 ≤ Complex.reCLM (∑ k ∈ K, (w k : ℂ) * F k z) +
    Complex.reCLM (∑ k ∈ K, (w k : ℂ) * F k ((center : ℂ) - z))
  rw [map_sum, map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_nonneg ?_
  intro k hk
  have hpair := hF k hk z hz_left hz_right
  exact by
    simpa [Complex.mul_re, mul_add] using
      mul_nonneg (hw k hk) hpair

/-- Center-one version of finite nonnegative weighted kernel-combination
pair positivity. -/
lemma laplacePairPositive_one_weightedKernelCombo
    {K : Finset ℕ} {w : ℕ → ℝ} {F : ℕ → ℂ → ℂ}
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hF : ∀ k ∈ K, LaplacePairPositive (F k) 1) :
    LaplacePairPositive (weightedKernelCombo K w F) 1 :=
  laplacePairPositive_weightedKernelCombo (center := 1) hw hF

/-- Resolvent/Laplace prototype kernel `z ↦ (a + z)⁻¹`.

For `a ≥ 0` this has nonnegative real part on the right half-plane, matching
the elementary positivity shape behind Laplace-transform zero-pair kernels. -/
noncomputable def resolventLaplaceKernel (a : ℝ) (z : ℂ) : ℂ :=
  ((a : ℂ) + z)⁻¹

/-- The resolvent/Laplace prototype kernel has nonnegative real part on the
closed right half-plane. -/
lemma resolventLaplaceKernel_re_nonnegative_of_nonneg_re
    {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : 0 ≤ z.re) :
    0 ≤ (resolventLaplaceKernel a z).re := by
  rw [resolventLaplaceKernel, Complex.inv_re]
  exact div_nonneg (by
    simp [Complex.add_re]
    exact add_nonneg ha hz) (Complex.normSq_nonneg _)

/-- Pointwise critical-strip positivity of the resolvent/Laplace prototype
kernel. -/
lemma resolventLaplaceKernel_re_nonnegative_on_critical_strip
    {a : ℝ} (ha : 0 ≤ a) :
    ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      0 ≤ (resolventLaplaceKernel a z).re := by
  intro z hz_left _hz_right
  exact resolventLaplaceKernel_re_nonnegative_of_nonneg_re ha hz_left

/-- The resolvent/Laplace prototype supplies strip-local pair positivity for
any real center. -/
lemma laplacePairPositive_resolventLaplaceKernel
    {a center : ℝ} (ha : 0 ≤ a) :
    LaplacePairPositive (resolventLaplaceKernel a) center := by
  intro z hz_left hz_right
  have hpair_left : 0 ≤ ((center : ℂ) - z).re := by
    simp [Complex.sub_re]
    exact hz_right
  exact add_nonneg
    (resolventLaplaceKernel_re_nonnegative_of_nonneg_re ha hz_left)
    (resolventLaplaceKernel_re_nonnegative_of_nonneg_re ha hpair_left)

/-- Center-one resolvent/Laplace pair positivity, in the zeta symmetry
normalization `ρ ↦ 1 - ρ`. -/
lemma laplacePairPositive_one_resolventLaplaceKernel
    {a : ℝ} (ha : 0 ≤ a) :
    LaplacePairPositive (resolventLaplaceKernel a) 1 :=
  laplacePairPositive_resolventLaplaceKernel (center := 1) ha

/-- Symmetric resolvent/Laplace kernel centered at a real point:
`z ↦ (a + z)⁻¹ + (a + center - z)⁻¹`.

This packages the elementary center-reflection kernel used in zero-pair
arguments before introducing more delicate Stechkin/Heath-Brown detectors. -/
noncomputable def symmetricResolventLaplaceKernel
    (a center : ℝ) (z : ℂ) : ℂ :=
  resolventLaplaceKernel a z +
    resolventLaplaceKernel a ((center : ℂ) - z)

/-- The symmetric resolvent/Laplace kernel has nonnegative real part on its
centered strip. -/
lemma symmetricResolventLaplaceKernel_re_nonnegative_on_strip
    {a center : ℝ} (ha : 0 ≤ a) :
    ∀ z : ℂ, 0 ≤ z.re → z.re ≤ center →
      0 ≤ (symmetricResolventLaplaceKernel a center z).re := by
  intro z hz_left hz_right
  have hpair_left : 0 ≤ ((center : ℂ) - z).re := by
    simp [Complex.sub_re]
    exact hz_right
  rw [symmetricResolventLaplaceKernel, Complex.add_re]
  exact add_nonneg
    (resolventLaplaceKernel_re_nonnegative_of_nonneg_re ha hz_left)
    (resolventLaplaceKernel_re_nonnegative_of_nonneg_re ha hpair_left)

/-- The symmetric resolvent/Laplace kernel supplies strip-local pair
positivity at its center. -/
lemma laplacePairPositive_symmetricResolventLaplaceKernel
    {a center : ℝ} (ha : 0 ≤ a) :
    LaplacePairPositive (symmetricResolventLaplaceKernel a center) center :=
  laplacePairPositive_of_re_nonnegative_on_strip
    (symmetricResolventLaplaceKernel_re_nonnegative_on_strip ha)

/-- Center-one symmetric resolvent/Laplace pair positivity, matching the zeta
reflection `ρ ↦ 1 - ρ`. -/
lemma laplacePairPositive_one_symmetricResolventLaplaceKernel
    {a : ℝ} (ha : 0 ≤ a) :
    LaplacePairPositive (symmetricResolventLaplaceKernel a 1) 1 :=
  laplacePairPositive_symmetricResolventLaplaceKernel
    (center := 1) ha

/-- Finite nonnegative combinations of center-reflected symmetric
resolvent/Laplace kernels. -/
noncomputable def symmetricResolventLaplaceKernelCombo
    (K : Finset ℕ) (w a : ℕ → ℝ) (center : ℝ) (z : ℂ) : ℂ :=
  ∑ k ∈ K, (w k : ℂ) * symmetricResolventLaplaceKernel (a k) center z

/-- Centered-strip real-part positivity for finite nonnegative combinations of
symmetric resolvent/Laplace kernels. -/
lemma symmetricResolventLaplaceKernelCombo_re_nonnegative_on_strip
    {K : Finset ℕ} {w a : ℕ → ℝ} {center : ℝ}
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k) :
    ∀ z : ℂ, 0 ≤ z.re → z.re ≤ center →
      0 ≤ (symmetricResolventLaplaceKernelCombo K w a center z).re := by
  intro z hz_left hz_right
  rw [symmetricResolventLaplaceKernelCombo]
  change 0 ≤ Complex.reCLM
    (∑ k ∈ K,
      (w k : ℂ) * symmetricResolventLaplaceKernel (a k) center z)
  rw [map_sum]
  refine Finset.sum_nonneg ?_
  intro k hk
  have hterm :=
    symmetricResolventLaplaceKernel_re_nonnegative_on_strip
      (ha k hk) z hz_left hz_right
  exact by
    simpa [Complex.mul_re] using mul_nonneg (hw k hk) hterm

/-- Finite nonnegative combinations of symmetric resolvent/Laplace kernels
supply strip-local pair positivity. -/
lemma laplacePairPositive_symmetricResolventLaplaceKernelCombo
    {K : Finset ℕ} {w a : ℕ → ℝ} {center : ℝ}
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k) :
    LaplacePairPositive
      (symmetricResolventLaplaceKernelCombo K w a center) center :=
  laplacePairPositive_of_re_nonnegative_on_strip
    (symmetricResolventLaplaceKernelCombo_re_nonnegative_on_strip hw ha)

/-- Center-one pair positivity for finite nonnegative combinations of symmetric
resolvent/Laplace kernels. -/
lemma laplacePairPositive_one_symmetricResolventLaplaceKernelCombo
    {K : Finset ℕ} {w a : ℕ → ℝ}
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k) :
    LaplacePairPositive (symmetricResolventLaplaceKernelCombo K w a 1) 1 :=
  laplacePairPositive_symmetricResolventLaplaceKernelCombo
    (center := 1) hw ha

/-- Signed/damped pair-kernel model `F - κ • G`.

This is the Lean-facing shape of Stechkin-style detector terms, where a
positive kernel is corrected by a controlled shifted kernel rather than only
combined with nonnegative weights. -/
noncomputable def dampedKernel (κ : ℝ) (F G : ℂ → ℂ) (z : ℂ) : ℂ :=
  F z - (κ : ℂ) * G z

/-- Algebraic pair-contribution identity for a damped kernel. -/
lemma dampedKernel_pair_contribution_eq
    (κ center : ℝ) (F G : ℂ → ℂ) (z : ℂ) :
    (dampedKernel κ F G z).re +
      (dampedKernel κ F G ((center : ℂ) - z)).re =
        ((F z).re + (F ((center : ℂ) - z)).re) -
          κ * ((G z).re + (G ((center : ℂ) - z)).re) := by
  simp [dampedKernel, Complex.sub_re, Complex.mul_re]
  ring

/-- Real-part identity for a self-damped kernel. -/
lemma dampedKernel_self_re_eq
    (κ : ℝ) (F : ℂ → ℂ) (z : ℂ) :
    (dampedKernel κ F F z).re = (1 - κ) * (F z).re := by
  simp [dampedKernel, Complex.sub_re, Complex.mul_re]
  ring

/-- Self-damping preserves pointwise strip real-part nonnegativity when the
damping coefficient is at most one. -/
lemma dampedKernel_self_re_nonnegative_on_strip_of_le_one
    {κ center : ℝ} {F : ℂ → ℂ}
    (hκ : κ ≤ 1)
    (hF : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ center -> 0 ≤ (F z).re) :
    ∀ z : ℂ, 0 ≤ z.re → z.re ≤ center ->
      0 ≤ (dampedKernel κ F F z).re := by
  intro z hz_left hz_right
  rw [dampedKernel_self_re_eq]
  exact mul_nonneg (sub_nonneg.mpr hκ) (hF z hz_left hz_right)

/-- Center-one self-damped pointwise real-part nonnegativity supplier. -/
lemma dampedKernel_self_re_nonnegative_on_critical_strip_of_le_one
    {κ : ℝ} {F : ℂ → ℂ}
    (hκ : κ ≤ 1)
    (hF : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 -> 0 ≤ (F z).re) :
    ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 ->
      0 ≤ (dampedKernel κ F F z).re :=
  dampedKernel_self_re_nonnegative_on_strip_of_le_one hκ hF

/-- A controlled signed/damped kernel supplies strip-local pair positivity.

The input is the Stechkin-style real inequality: on the relevant strip, the
paired contribution of `F` dominates `κ` times the paired contribution of `G`. -/
lemma laplacePairPositive_dampedKernel_of_pair_le
    {κ center : ℝ} {F G : ℂ → ℂ}
    (hpair : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ center →
      κ * ((G z).re + (G ((center : ℂ) - z)).re) ≤
        (F z).re + (F ((center : ℂ) - z)).re) :
    LaplacePairPositive (dampedKernel κ F G) center := by
  intro z hz_left hz_right
  rw [dampedKernel_pair_contribution_eq]
  exact sub_nonneg.mpr (hpair z hz_left hz_right)

/-- Center-one version of the damped-kernel pair-positivity bridge, matching
the zeta symmetry `ρ ↦ 1 - ρ`. -/
lemma laplacePairPositive_one_dampedKernel_of_pair_le
    {κ : ℝ} {F G : ℂ → ℂ}
    (hpair : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      κ * ((G z).re + (G (1 - z)).re) ≤
        (F z).re + (F (1 - z)).re) :
    LaplacePairPositive (dampedKernel κ F G) 1 := by
  refine laplacePairPositive_dampedKernel_of_pair_le ?_
  intro z hz_left hz_right
  simpa using hpair z hz_left hz_right

/-- A pair-nonnegative dominated kernel supplies damped pair positivity when
the damping coefficient is at most one.  This is often the easier
Stechkin-facing input shape: prove the shifted kernel pair is nonnegative and
is bounded by the positive kernel pair, then choose any `κ <= 1`. -/
lemma laplacePairPositive_dampedKernel_of_pair_nonneg_le
    {κ center : ℝ} {F G : ℂ → ℂ}
    (hκ : κ ≤ 1)
    (hG_nonneg : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ center →
      0 ≤ (G z).re + (G ((center : ℂ) - z)).re)
    (hGF : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ center →
      (G z).re + (G ((center : ℂ) - z)).re ≤
        (F z).re + (F ((center : ℂ) - z)).re) :
    LaplacePairPositive (dampedKernel κ F G) center := by
  refine laplacePairPositive_dampedKernel_of_pair_le ?_
  intro z hz_left hz_right
  have hG := hG_nonneg z hz_left hz_right
  have hκG :
      κ * ((G z).re + (G ((center : ℂ) - z)).re) ≤
        1 * ((G z).re + (G ((center : ℂ) - z)).re) :=
    mul_le_mul_of_nonneg_right hκ hG
  have hGF' := hGF z hz_left hz_right
  linarith

/-- Center-one version of
`laplacePairPositive_dampedKernel_of_pair_nonneg_le`, matching the zeta
symmetry `ρ ↦ 1 - ρ`. -/
lemma laplacePairPositive_one_dampedKernel_of_pair_nonneg_le
    {κ : ℝ} {F G : ℂ → ℂ}
    (hκ : κ ≤ 1)
    (hG_nonneg : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      0 ≤ (G z).re + (G (1 - z)).re)
    (hGF : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      (G z).re + (G (1 - z)).re ≤
        (F z).re + (F (1 - z)).re) :
    LaplacePairPositive (dampedKernel κ F G) 1 := by
  refine laplacePairPositive_dampedKernel_of_pair_nonneg_le hκ ?_ ?_
  · intro z hz_left hz_right
    simpa using hG_nonneg z hz_left hz_right
  · intro z hz_left hz_right
    simpa using hGF z hz_left hz_right

/-- Self-damping preserves strip-local pair positivity when the damping
coefficient is at most one. -/
lemma laplacePairPositive_dampedKernel_self_of_le_one
    {κ center : ℝ} {F : ℂ → ℂ}
    (hκ : κ ≤ 1) (hF : LaplacePairPositive F center) :
    LaplacePairPositive (dampedKernel κ F F) center := by
  refine laplacePairPositive_dampedKernel_of_pair_le ?_
  intro z hz_left hz_right
  have hp : 0 ≤ (F z).re + (F ((center : ℂ) - z)).re :=
    hF z hz_left hz_right
  have hle :
      κ * ((F z).re + (F ((center : ℂ) - z)).re) ≤
        1 * ((F z).re + (F ((center : ℂ) - z)).re) :=
    mul_le_mul_of_nonneg_right hκ hp
  simpa using hle

/-- Center-one self-damped pair-positivity bridge, matching zeta symmetry. -/
lemma laplacePairPositive_one_dampedKernel_self_of_le_one
    {κ : ℝ} {F : ℂ → ℂ}
    (hκ : κ ≤ 1) (hF : LaplacePairPositive F 1) :
    LaplacePairPositive (dampedKernel κ F F) 1 :=
  laplacePairPositive_dampedKernel_self_of_le_one hκ hF

/-- Concrete center-one pair positivity for the self-damped
resolvent/Laplace prototype kernel. -/
lemma laplacePairPositive_one_selfDampedResolventLaplaceKernel
    {κ a : ℝ} (hκ : κ ≤ 1) (ha : 0 ≤ a) :
    LaplacePairPositive
      (dampedKernel κ (resolventLaplaceKernel a) (resolventLaplaceKernel a))
      1 :=
  laplacePairPositive_one_dampedKernel_self_of_le_one hκ
    (laplacePairPositive_one_resolventLaplaceKernel ha)

/-- Finite nonnegative real-weighted combinations of damped kernels preserve
strip-local pair positivity once each damped summand satisfies its
Stechkin-style pair inequality. -/
lemma laplacePairPositive_weightedDampedKernelCombo_of_pair_le
    {K : Finset ℕ} {w κ : ℕ → ℝ} {F G : ℕ → ℂ → ℂ} {center : ℝ}
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hpair : ∀ k ∈ K, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ center →
      κ k * ((G k z).re + (G k ((center : ℂ) - z)).re) ≤
        (F k z).re + (F k ((center : ℂ) - z)).re) :
    LaplacePairPositive
      (weightedKernelCombo K w (fun k => dampedKernel (κ k) (F k) (G k)))
      center :=
  laplacePairPositive_weightedKernelCombo hw
    (fun k hk => laplacePairPositive_dampedKernel_of_pair_le
      (fun z hz_left hz_right => hpair k hk z hz_left hz_right))

/-- Center-one version of finite nonnegative damped-kernel combination
pair positivity, matching the zeta symmetry `ρ ↦ 1 - ρ`. -/
lemma laplacePairPositive_one_weightedDampedKernelCombo_of_pair_le
    {K : Finset ℕ} {w κ : ℕ → ℝ} {F G : ℕ → ℂ → ℂ}
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hpair : ∀ k ∈ K, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      κ k * ((G k z).re + (G k (1 - z)).re) ≤
        (F k z).re + (F k (1 - z)).re) :
    LaplacePairPositive
      (weightedKernelCombo K w (fun k => dampedKernel (κ k) (F k) (G k)))
      1 := by
  refine laplacePairPositive_weightedDampedKernelCombo_of_pair_le hw ?_
  intro k hk z hz_left hz_right
  simpa using hpair k hk z hz_left hz_right

/-- Finite nonnegative combinations of self-damped pair-positive kernels remain
pair-positive when each damping coefficient is at most one. -/
lemma laplacePairPositive_weightedDampedKernelCombo_self_of_le_one
    {K : Finset ℕ} {w κ : ℕ → ℝ} {F : ℕ → ℂ → ℂ} {center : ℝ}
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (hF : ∀ k ∈ K, LaplacePairPositive (F k) center) :
    LaplacePairPositive
      (weightedKernelCombo K w (fun k => dampedKernel (κ k) (F k) (F k)))
      center :=
  laplacePairPositive_weightedKernelCombo hw
    (fun k hk => laplacePairPositive_dampedKernel_self_of_le_one
      (hκ k hk) (hF k hk))

/-- Center-one version of finite weighted self-damped pair positivity. -/
lemma laplacePairPositive_one_weightedDampedKernelCombo_self_of_le_one
    {K : Finset ℕ} {w κ : ℕ → ℝ} {F : ℕ → ℂ → ℂ}
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (hF : ∀ k ∈ K, LaplacePairPositive (F k) 1) :
    LaplacePairPositive
      (weightedKernelCombo K w (fun k => dampedKernel (κ k) (F k) (F k)))
      1 :=
  laplacePairPositive_weightedDampedKernelCombo_self_of_le_one hw hκ hF

/-- Center-one pair positivity for finite nonnegative combinations of
self-damped resolvent/Laplace prototype kernels. -/
lemma laplacePairPositive_one_weightedSelfDampedResolventLaplaceKernelCombo
    {K : Finset ℕ} {w κ a : ℕ → ℝ}
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (ha : ∀ k ∈ K, 0 ≤ a k) :
    LaplacePairPositive
      (weightedKernelCombo K w
        (fun k => dampedKernel (κ k)
          (resolventLaplaceKernel (a k)) (resolventLaplaceKernel (a k))))
      1 :=
  laplacePairPositive_one_weightedDampedKernelCombo_self_of_le_one
    hw hκ (fun k hk => laplacePairPositive_one_resolventLaplaceKernel (ha k hk))

/-- Finite nonnegative combinations of self-damped pointwise-positive kernels
remain pointwise real-part nonnegative on a strip. -/
lemma weightedDampedKernelCombo_self_re_nonnegative_on_strip_of_le_one
    {K : Finset ℕ} {w κ : ℕ → ℝ} {F : ℕ → ℂ → ℂ} {center : ℝ}
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (hF : ∀ k ∈ K, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ center ->
      0 ≤ (F k z).re) :
    ∀ z : ℂ, 0 ≤ z.re → z.re ≤ center ->
      0 ≤ (weightedKernelCombo K w
        (fun k => dampedKernel (κ k) (F k) (F k)) z).re :=
  weightedKernelCombo_re_nonnegative_on_strip hw
    (fun k hk =>
      dampedKernel_self_re_nonnegative_on_strip_of_le_one
        (hκ k hk) (hF k hk))

/-- Center-one version of weighted self-damped pointwise real-part
nonnegativity. -/
lemma weightedDampedKernelCombo_self_re_nonnegative_on_critical_strip_of_le_one
    {K : Finset ℕ} {w κ : ℕ → ℝ} {F : ℕ → ℂ → ℂ}
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (hF : ∀ k ∈ K, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 ->
      0 ≤ (F k z).re) :
    ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 ->
      0 ≤ (weightedKernelCombo K w
        (fun k => dampedKernel (κ k) (F k) (F k)) z).re :=
  weightedDampedKernelCombo_self_re_nonnegative_on_strip_of_le_one
    hw hκ hF

/-- Finite nonnegative linear combinations of resolvent/Laplace prototype
kernels.  This is a Lean-facing model for detector kernels built by summing
elementary right-half-plane-positive pieces. -/
noncomputable def resolventLaplaceKernelCombo
    (K : Finset ℕ) (w a : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∑ k ∈ K, (w k : ℂ) * resolventLaplaceKernel (a k) z

/-- A finite nonnegative combination of resolvent/Laplace kernels has
nonnegative real part on the closed right half-plane. -/
lemma resolventLaplaceKernelCombo_re_nonnegative_of_nonneg_re
    {K : Finset ℕ} {w a : ℕ → ℝ}
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k)
    {z : ℂ} (hz : 0 ≤ z.re) :
    0 ≤ (resolventLaplaceKernelCombo K w a z).re := by
  rw [resolventLaplaceKernelCombo]
  change 0 ≤ Complex.reCLM
    (∑ k ∈ K, (w k : ℂ) * resolventLaplaceKernel (a k) z)
  rw [map_sum]
  refine Finset.sum_nonneg ?_
  intro k hk
  have hterm :=
    resolventLaplaceKernel_re_nonnegative_of_nonneg_re (ha k hk) hz
  exact by
    simpa [Complex.mul_re] using mul_nonneg (hw k hk) hterm

/-- Critical-strip positivity for finite nonnegative resolvent/Laplace
combinations. -/
lemma resolventLaplaceKernelCombo_re_nonnegative_on_critical_strip
    {K : Finset ℕ} {w a : ℕ → ℝ}
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k) :
    ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      0 ≤ (resolventLaplaceKernelCombo K w a z).re := by
  intro z hz_left _hz_right
  exact resolventLaplaceKernelCombo_re_nonnegative_of_nonneg_re hw ha hz_left

/-- Finite nonnegative resolvent/Laplace combinations supply strip-local pair
positivity. -/
lemma laplacePairPositive_resolventLaplaceKernelCombo
    {K : Finset ℕ} {w a : ℕ → ℝ} {center : ℝ}
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k) :
    LaplacePairPositive (resolventLaplaceKernelCombo K w a) center := by
  intro z hz_left hz_right
  have hpair_left : 0 ≤ ((center : ℂ) - z).re := by
    simp [Complex.sub_re]
    exact hz_right
  exact add_nonneg
    (resolventLaplaceKernelCombo_re_nonnegative_of_nonneg_re hw ha hz_left)
    (resolventLaplaceKernelCombo_re_nonnegative_of_nonneg_re hw ha hpair_left)

/-- Center-one finite nonnegative resolvent/Laplace combinations supply the
zeta zero-pair positivity interface. -/
lemma laplacePairPositive_one_resolventLaplaceKernelCombo
    {K : Finset ℕ} {w a : ℕ → ℝ}
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k) :
    LaplacePairPositive (resolventLaplaceKernelCombo K w a) 1 :=
  laplacePairPositive_resolventLaplaceKernelCombo (center := 1) hw ha

/-- Affine resolvent/Laplace prototype
`z ↦ (a + (b + c z))⁻¹`.

For nonnegative `a`, `b`, and `c`, this is a simple right-half-plane-positive
kernel obtained by precomposing the resolvent prototype with a nonnegative
real affine map. -/
noncomputable def affineResolventLaplaceKernel
    (a b c : ℝ) (z : ℂ) : ℂ :=
  resolventLaplaceKernel a ((b : ℂ) + (c : ℂ) * z)

/-- A nonnegative real affine precomposition preserves right-half-plane
real-part positivity for the resolvent/Laplace prototype. -/
lemma affineResolventLaplaceKernel_re_nonnegative_of_nonneg_re
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    {z : ℂ} (hz : 0 ≤ z.re) :
    0 ≤ (affineResolventLaplaceKernel a b c z).re := by
  rw [affineResolventLaplaceKernel]
  refine resolventLaplaceKernel_re_nonnegative_of_nonneg_re ha ?_
  simp [Complex.add_re, Complex.mul_re, add_nonneg hb (mul_nonneg hc hz)]

/-- Critical-strip positivity for the affine resolvent/Laplace prototype. -/
lemma affineResolventLaplaceKernel_re_nonnegative_on_critical_strip
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      0 ≤ (affineResolventLaplaceKernel a b c z).re := by
  intro z hz_left _hz_right
  exact affineResolventLaplaceKernel_re_nonnegative_of_nonneg_re
    ha hb hc hz_left

/-- The affine resolvent/Laplace prototype supplies strip-local pair
positivity for any real center. -/
lemma laplacePairPositive_affineResolventLaplaceKernel
    {a b c center : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    LaplacePairPositive (affineResolventLaplaceKernel a b c) center := by
  intro z hz_left hz_right
  have hpair_left : 0 ≤ ((center : ℂ) - z).re := by
    simp [Complex.sub_re]
    exact hz_right
  exact add_nonneg
    (affineResolventLaplaceKernel_re_nonnegative_of_nonneg_re
      ha hb hc hz_left)
    (affineResolventLaplaceKernel_re_nonnegative_of_nonneg_re
      ha hb hc hpair_left)

/-- Center-one affine resolvent/Laplace pair positivity. -/
lemma laplacePairPositive_one_affineResolventLaplaceKernel
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    LaplacePairPositive (affineResolventLaplaceKernel a b c) 1 :=
  laplacePairPositive_affineResolventLaplaceKernel
    (center := 1) ha hb hc

/-- Finite nonnegative combinations of affine resolvent/Laplace prototype
kernels. -/
noncomputable def affineResolventLaplaceKernelCombo
    (K : Finset ℕ) (w a b c : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∑ k ∈ K, (w k : ℂ) * affineResolventLaplaceKernel (a k) (b k) (c k) z

/-- A finite nonnegative combination of affine resolvent/Laplace kernels has
nonnegative real part on the closed right half-plane. -/
lemma affineResolventLaplaceKernelCombo_re_nonnegative_of_nonneg_re
    {K : Finset ℕ} {w a b c : ℕ → ℝ}
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k)
    (hb : ∀ k ∈ K, 0 ≤ b k) (hc : ∀ k ∈ K, 0 ≤ c k)
    {z : ℂ} (hz : 0 ≤ z.re) :
    0 ≤ (affineResolventLaplaceKernelCombo K w a b c z).re := by
  rw [affineResolventLaplaceKernelCombo]
  change 0 ≤ Complex.reCLM
    (∑ k ∈ K,
      (w k : ℂ) * affineResolventLaplaceKernel (a k) (b k) (c k) z)
  rw [map_sum]
  refine Finset.sum_nonneg ?_
  intro k hk
  have hterm :=
    affineResolventLaplaceKernel_re_nonnegative_of_nonneg_re
      (ha k hk) (hb k hk) (hc k hk) hz
  exact by
    simpa [Complex.mul_re] using mul_nonneg (hw k hk) hterm

/-- Critical-strip positivity for finite nonnegative affine
resolvent/Laplace combinations. -/
lemma affineResolventLaplaceKernelCombo_re_nonnegative_on_critical_strip
    {K : Finset ℕ} {w a b c : ℕ → ℝ}
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k)
    (hb : ∀ k ∈ K, 0 ≤ b k) (hc : ∀ k ∈ K, 0 ≤ c k) :
    ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      0 ≤ (affineResolventLaplaceKernelCombo K w a b c z).re := by
  intro z hz_left _hz_right
  exact affineResolventLaplaceKernelCombo_re_nonnegative_of_nonneg_re
    hw ha hb hc hz_left

/-- Finite nonnegative affine resolvent/Laplace combinations supply
strip-local pair positivity. -/
lemma laplacePairPositive_affineResolventLaplaceKernelCombo
    {K : Finset ℕ} {w a b c : ℕ → ℝ} {center : ℝ}
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k)
    (hb : ∀ k ∈ K, 0 ≤ b k) (hc : ∀ k ∈ K, 0 ≤ c k) :
    LaplacePairPositive (affineResolventLaplaceKernelCombo K w a b c)
      center := by
  intro z hz_left hz_right
  have hpair_left : 0 ≤ ((center : ℂ) - z).re := by
    simp [Complex.sub_re]
    exact hz_right
  exact add_nonneg
    (affineResolventLaplaceKernelCombo_re_nonnegative_of_nonneg_re
      hw ha hb hc hz_left)
    (affineResolventLaplaceKernelCombo_re_nonnegative_of_nonneg_re
      hw ha hb hc hpair_left)

/-- Center-one finite nonnegative affine resolvent/Laplace combinations supply
the zeta zero-pair positivity interface. -/
lemma laplacePairPositive_one_affineResolventLaplaceKernelCombo
    {K : Finset ℕ} {w a b c : ℕ → ℝ}
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k)
    (hb : ∀ k ∈ K, 0 ≤ b k) (hc : ∀ k ∈ K, 0 ≤ c k) :
    LaplacePairPositive (affineResolventLaplaceKernelCombo K w a b c) 1 :=
  laplacePairPositive_affineResolventLaplaceKernelCombo
    (center := 1) hw ha hb hc

/-- Center-one pair positivity for finite nonnegative combinations of
self-damped affine resolvent/Laplace prototype kernels. -/
lemma laplacePairPositive_one_weightedSelfDampedAffineResolventLaplaceKernelCombo
    {K : Finset ℕ} {w κ a b c : ℕ → ℝ}
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (ha : ∀ k ∈ K, 0 ≤ a k)
    (hb : ∀ k ∈ K, 0 ≤ b k)
    (hc : ∀ k ∈ K, 0 ≤ c k) :
    LaplacePairPositive
      (weightedKernelCombo K w
        (fun k => dampedKernel (κ k)
          (affineResolventLaplaceKernel (a k) (b k) (c k))
          (affineResolventLaplaceKernel (a k) (b k) (c k))))
      1 :=
  laplacePairPositive_one_weightedDampedKernelCombo_self_of_le_one
    hw hκ
    (fun k hk => laplacePairPositive_one_affineResolventLaplaceKernel
      (ha k hk) (hb k hk) (hc k hk))

/-- Center-one pointwise real-part nonnegativity for finite nonnegative
combinations of self-damped affine resolvent/Laplace prototype kernels. -/
lemma weightedSelfDampedAffineResolventLaplaceKernelCombo_re_nonnegative_on_critical_strip
    {K : Finset ℕ} {w κ a b c : ℕ → ℝ}
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (ha : ∀ k ∈ K, 0 ≤ a k)
    (hb : ∀ k ∈ K, 0 ≤ b k)
    (hc : ∀ k ∈ K, 0 ≤ c k) :
    ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      0 ≤ (weightedKernelCombo K w
        (fun k => dampedKernel (κ k)
          (affineResolventLaplaceKernel (a k) (b k) (c k))
          (affineResolventLaplaceKernel (a k) (b k) (c k))) z).re :=
  weightedDampedKernelCombo_self_re_nonnegative_on_critical_strip_of_le_one
    hw hκ
    (fun k hk =>
      affineResolventLaplaceKernel_re_nonnegative_on_critical_strip
        (ha k hk) (hb k hk) (hc k hk))

/-- Direct use of the zero-pair nonnegativity condition. -/
lemma zero_pair_contribution_nonnegative_of_reflection_condition
    {F : ℂ → ℂ} {center z : ℂ}
    (hF : ZeroPairContributionNonnegative F center) :
    0 ≤ (F z).re + (F (center - z)).re :=
  hF z

/-- Finite paired zero contributions are nonnegative if every paired summand
is nonnegative.  A later analytic specialization can instantiate `pair ρ` as
the reflected zero, for example `center - ρ`. -/
lemma finite_zero_sum_nonnegative_of_pairing_condition
    (S : Finset ℂ) (F : ℂ → ℂ) (pair : ℂ → ℂ)
    (hpair : ∀ ρ ∈ S, 0 ≤ (F ρ).re + (F (pair ρ)).re) :
    0 ≤ ∑ ρ ∈ S, ((F ρ).re + (F (pair ρ)).re) :=
  Finset.sum_nonneg hpair

/-- Finite paired contributions are nonnegative from strip-local pair
positivity, provided every point in the finite set lies in the strip. -/
lemma finite_zero_sum_nonnegative_of_laplace_pair_positive
    (S : Finset ℂ) (F : ℂ → ℂ) (center : ℝ)
    (hF : LaplacePairPositive F center)
    (hstrip : ∀ ρ ∈ S, 0 ≤ ρ.re ∧ ρ.re ≤ center) :
    0 ≤ ∑ ρ ∈ S, ((F ρ).re + (F ((center : ℂ) - ρ)).re) :=
  Finset.sum_nonneg (fun ρ hρ => hF ρ (hstrip ρ hρ).1 (hstrip ρ hρ).2)

/-! ### Vertical-line bridges around `Re(s) = 1 / 3`

These lemmas do not prove a new zero-free line.  They isolate the easy formal
reductions needed to turn a future analytic input on the reflected
`Re(s) = 2 / 3` line into a statement about `Re(s) = 1 / 3`.
-/

/-- Zeta has no zeros on the vertical line `Re(s) = σ`. -/
abbrev NoZerosOnVerticalLine (σ : ℝ) : Prop :=
  ∀ s : ℂ, s.re = σ → riemannZeta s ≠ 0

/-- A zero-free vertical line has no nontrivial zeros on that line. -/
theorem not_exists_nontrivial_zero_on_line_of_no_zeros_on_vertical_line
    {σ : ℝ} (hline : NoZerosOnVerticalLine σ) :
    ¬ ∃ s : ℂ, RiemannHypothesis.IsNontrivialZero s ∧ s.re = σ := by
  rintro ⟨s, hnt, hs⟩
  exact (hline s hs) hnt.1

/-- In the critical strip, excluding nontrivial zeros on a vertical line gives
zero-freeness of that line.  The strip hypotheses are necessary: trivial zeros
live outside `0 < Re(s) < 1`. -/
theorem no_zeros_on_vertical_line_of_not_exists_nontrivial_zero_on_line
    {σ : ℝ} (hσ_pos : 0 < σ) (hσ_lt_one : σ < 1)
    (hnone : ¬ ∃ s : ℂ, RiemannHypothesis.IsNontrivialZero s ∧ s.re = σ) :
    NoZerosOnVerticalLine σ := by
  intro s hs hzero
  have hnt : RiemannHypothesis.IsNontrivialZero s := by
    refine ⟨hzero, ?_, ?_⟩
    · linarith [hs, hσ_lt_one]
    · linarith [hs, hσ_pos]
  exact hnone ⟨s, hnt, hs⟩

/-- In the critical strip, zero-freeness of a vertical line is equivalent to
the nonexistence of nontrivial zeros on that line. -/
theorem no_zeros_on_vertical_line_iff_not_exists_nontrivial_zero_on_line
    {σ : ℝ} (hσ_pos : 0 < σ) (hσ_lt_one : σ < 1) :
    NoZerosOnVerticalLine σ ↔
      ¬ ∃ s : ℂ, RiemannHypothesis.IsNontrivialZero s ∧ s.re = σ := by
  constructor
  · exact not_exists_nontrivial_zero_on_line_of_no_zeros_on_vertical_line
  · exact no_zeros_on_vertical_line_of_not_exists_nontrivial_zero_on_line
      hσ_pos hσ_lt_one

/-- A line-free statement at `Re(s) = 1 / 3` follows immediately from RH. -/
theorem no_zeros_on_one_third_of_RH
    (hRH : RiemannHypothesis.Statement) :
    NoZerosOnVerticalLine (1 / 3) := by
  intro s hs hzero
  have hnt : RiemannHypothesis.IsNontrivialZero s := by
    refine ⟨hzero, ?_, ?_⟩
    · nlinarith [hs]
    · nlinarith [hs]
  have hhalf : s.re = 1 / 2 := hRH s hnt
  nlinarith [hs, hhalf]

/-- A zero-free half-plane `Re(s) ≥ 2 / 3` excludes zeros on `Re(s) = 1 / 3`
by the functional-equation symmetry `ρ ↦ 1 - ρ`. -/
theorem no_zeros_on_one_third_of_right_halfplane_two_thirds
    (hRight : ∀ s : ℂ, (2 / 3 : ℝ) ≤ s.re → riemannZeta s ≠ 0) :
    NoZerosOnVerticalLine (1 / 3) := by
  intro s hs hzero
  have hnt : RiemannHypothesis.IsNontrivialZero s := by
    refine ⟨hzero, ?_, ?_⟩
    · nlinarith [hs]
    · nlinarith [hs]
  have hsym : RiemannHypothesis.IsNontrivialZero (1 - s) :=
    nontrivial_zero_symmetric' hnt
  have hre : (1 - s).re = (2 / 3 : ℝ) := by
    have hcalc : (1 : ℝ) - (1 / 3) = 2 / 3 := by norm_num
    simpa [Complex.sub_re, hs] using hcalc
  exact (hRight (1 - s) (le_of_eq hre.symm)) hsym.1

/-- General right-half-plane bridge: if ζ has no zeros in `Re(s) ≥ β`, then
the reflected vertical line `Re(s)=1-β` is zero-free. -/
theorem no_zeros_on_reflected_line_of_right_halfplane
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hRight : ∀ s : ℂ, β ≤ s.re → riemannZeta s ≠ 0) :
    NoZerosOnVerticalLine (1 - β) := by
  intro s hs hzero
  have hnt : RiemannHypothesis.IsNontrivialZero s := by
    refine ⟨hzero, ?_, ?_⟩
    · linarith [hs, hβ_lt_one]
    · linarith [hs, hβ_pos]
  have hsym : RiemannHypothesis.IsNontrivialZero (1 - s) :=
    nontrivial_zero_symmetric' hnt
  have hre : (1 - s).re = β := by
    have hcalc : (1 : ℝ) - (1 - β) = β := by ring
    simp [Complex.sub_re, hs, hcalc]
  exact (hRight (1 - s) (le_of_eq hre.symm)) hsym.1

/-- Existence of a nontrivial zero on `Re(s) = 1 / 3` is equivalent to
existence of a nontrivial zero on the reflected line `Re(s) = 2 / 3`. -/
theorem exists_nontrivial_zero_on_one_third_iff_two_thirds :
    (∃ s : ℂ, RiemannHypothesis.IsNontrivialZero s ∧ s.re = (1 / 3 : ℝ)) ↔
      (∃ s : ℂ, RiemannHypothesis.IsNontrivialZero s ∧ s.re = (2 / 3 : ℝ)) := by
  constructor
  · rintro ⟨s, hnt, hs⟩
    refine ⟨1 - s, nontrivial_zero_symmetric' hnt, ?_⟩
    have hcalc : (1 : ℝ) - (1 / 3) = 2 / 3 := by norm_num
    simpa [Complex.sub_re, hs] using hcalc
  · rintro ⟨s, hnt, hs⟩
    refine ⟨1 - s, nontrivial_zero_symmetric' hnt, ?_⟩
    have hcalc : (1 : ℝ) - (2 / 3) = 1 / 3 := by norm_num
    simpa [Complex.sub_re, hs] using hcalc

/-- General reflected-line existence equivalence for nontrivial zeros:
`ρ ↦ 1-ρ` sends the line `Re(s)=β` to `Re(s)=1-β`, and is its own inverse. -/
theorem exists_nontrivial_zero_on_line_iff_reflected (β : ℝ) :
    (∃ s : ℂ, RiemannHypothesis.IsNontrivialZero s ∧ s.re = β) ↔
      (∃ s : ℂ, RiemannHypothesis.IsNontrivialZero s ∧ s.re = 1 - β) := by
  constructor
  · rintro ⟨s, hnt, hs⟩
    refine ⟨1 - s, nontrivial_zero_symmetric' hnt, ?_⟩
    simp [Complex.sub_re, hs]
  · rintro ⟨s, hnt, hs⟩
    refine ⟨1 - s, nontrivial_zero_symmetric' hnt, ?_⟩
    have hcalc : (1 : ℝ) - (1 - β) = β := by ring
    simp [Complex.sub_re, hs, hcalc]

/-- In the critical strip, zero-freeness of a vertical line is equivalent to
zero-freeness of the reflected line. -/
theorem no_zeros_on_vertical_line_iff_reflected
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1) :
    NoZerosOnVerticalLine β ↔ NoZerosOnVerticalLine (1 - β) := by
  constructor
  · intro hleft s hs hzero
    have hnt : RiemannHypothesis.IsNontrivialZero s := by
      refine ⟨hzero, ?_, ?_⟩
      · linarith [hs, hβ_lt_one]
      · linarith [hs, hβ_pos]
    have hsym : RiemannHypothesis.IsNontrivialZero (1 - s) :=
      nontrivial_zero_symmetric' hnt
    have hre : (1 - s).re = β := by
      have hcalc : (1 : ℝ) - (1 - β) = β := by ring
      simp [Complex.sub_re, hs, hcalc]
    exact hleft (1 - s) hre hsym.1
  · intro hright s hs hzero
    have hnt : RiemannHypothesis.IsNontrivialZero s := by
      refine ⟨hzero, ?_, ?_⟩
      · linarith [hs, hβ_pos]
      · linarith [hs, hβ_lt_one]
    have hsym : RiemannHypothesis.IsNontrivialZero (1 - s) :=
      nontrivial_zero_symmetric' hnt
    have hre : (1 - s).re = 1 - β := by
      simp [Complex.sub_re, hs]
    exact hright (1 - s) hre hsym.1

/-- Specialized reflection bridge: zero-freeness on `Re(s)=2/3` excludes zeros
on `Re(s)=1/3`.  This packages the formal final step in the proposed
explicit-formula/PNT-error route. -/
theorem no_zeros_on_one_third_of_no_zeros_on_two_thirds
    (h : NoZerosOnVerticalLine (2 / 3)) :
    NoZerosOnVerticalLine (1 / 3) := by
  intro s hs hzero
  have hnt : RiemannHypothesis.IsNontrivialZero s := by
    refine ⟨hzero, ?_, ?_⟩
    · nlinarith [hs]
    · nlinarith [hs]
  have hsym : RiemannHypothesis.IsNontrivialZero (1 - s) :=
    nontrivial_zero_symmetric' hnt
  have hre : (1 - s).re = (2 / 3 : ℝ) := by
    have hcalc : (1 : ℝ) - (1 / 3) = 2 / 3 := by norm_num
    simpa [Complex.sub_re, hs] using hcalc
  exact h (1 - s) hre hsym.1

/-- The converse specialized reflection bridge, useful for keeping the two
reflected line formulations interchangeable. -/
theorem no_zeros_on_two_thirds_of_no_zeros_on_one_third
    (h : NoZerosOnVerticalLine (1 / 3)) :
    NoZerosOnVerticalLine (2 / 3) := by
  intro s hs hzero
  have hnt : RiemannHypothesis.IsNontrivialZero s := by
    refine ⟨hzero, ?_, ?_⟩
    · nlinarith [hs]
    · nlinarith [hs]
  have hsym : RiemannHypothesis.IsNontrivialZero (1 - s) :=
    nontrivial_zero_symmetric' hnt
  have hre : (1 - s).re = (1 / 3 : ℝ) := by
    have hcalc : (1 : ℝ) - (2 / 3) = 1 / 3 := by norm_num
    simpa [Complex.sub_re, hs] using hcalc
  exact h (1 - s) hre hsym.1

/-- Route interface for the proposed converse-explicit-formula strategy.

The intended analytic input is: a sufficiently strong PNT error term implies
that no nontrivial zero can lie on the reflected line `Re(s) = 2 / 3`.
This predicate intentionally keeps the hard explicit-formula converse as an
assumption, so the following theorem is only a formal bridge. -/
abbrev NoZerosOnVerticalLineOneThirdOfStrongPNTError
    (StrongPNTError : Prop) : Prop :=
  StrongPNTError →
    ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ →
      ρ.re = (2 / 3 : ℝ) → False

/-- If a chosen strong PNT-error statement excludes nontrivial zeros on
`Re(s) = 2 / 3`, then it also excludes zeta zeros on `Re(s) = 1 / 3`. -/
theorem no_zeros_on_one_third_of_strong_pnt_error_bridge
    {StrongPNTError : Prop}
    (hbridge : NoZerosOnVerticalLineOneThirdOfStrongPNTError StrongPNTError)
    (herror : StrongPNTError) :
    NoZerosOnVerticalLine (1 / 3) := by
  intro s hs hzero
  have hnt : RiemannHypothesis.IsNontrivialZero s := by
    refine ⟨hzero, ?_, ?_⟩
    · nlinarith [hs]
    · nlinarith [hs]
  have hsym : RiemannHypothesis.IsNontrivialZero (1 - s) :=
    nontrivial_zero_symmetric' hnt
  have hre : (1 - s).re = (2 / 3 : ℝ) := by
    have hcalc : (1 : ℝ) - (1 / 3) = 2 / 3 := by norm_num
    simpa [Complex.sub_re, hs] using hcalc
  exact hbridge herror (1 - s) hsym hre

/-- Power-scale Chebyshev-`ψ` error statement `ψ(x) - x = O(x ^ θ)`. -/
abbrev PsiPowerErrorBound (θ : ℝ) : Prop :=
  (fun x : ℝ => chebyshevPsi x - x) =O[atTop] (fun x : ℝ => x ^ θ)

/-- The RH-scale `ψ` error implies every power-scale `ψ` error with exponent
strictly larger than `1/2`. -/
theorem psiPowerErrorBound_of_RH_PsiErrorBound_of_half_lt {θ : ℝ}
    (hθ : (1 / 2 : ℝ) < θ) (h : RH_PsiErrorBound) :
    PsiPowerErrorBound θ := by
  rw [RH_PsiErrorBound] at h
  rw [PsiPowerErrorBound]
  exact Asymptotics.IsLittleO.isBigO
    (h.trans_isLittleO (sqrt_mul_log_sq_isLittleO_rpow_of_half_lt hθ))

/-- A power-scale Chebyshev-`ψ` estimate remains valid after increasing its
exponent. -/
theorem psiPowerErrorBound_mono {a b : ℝ} (hab : a ≤ b)
    (h : PsiPowerErrorBound a) : PsiPowerErrorBound b := by
  apply h.trans
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx_nonneg : 0 ≤ x := le_trans zero_le_one hx
  have hxa_nonneg : 0 ≤ x ^ a := Real.rpow_nonneg hx_nonneg a
  have hxb_nonneg : 0 ≤ x ^ b := Real.rpow_nonneg hx_nonneg b
  simpa [Real.norm_eq_abs, abs_of_nonneg hxa_nonneg,
    abs_of_nonneg hxb_nonneg] using
    (Real.rpow_le_rpow_of_exponent_le hx hab)

/-- An eventual absolute-value estimate closes the power-scale
Chebyshev-`ψ` Big-O predicate. -/
theorem psiPowerErrorBound_of_eventual_abs_bound {θ C : ℝ}
    (h : ∀ᶠ x in atTop,
      |chebyshevPsi x - x| ≤ C * x ^ θ) :
    PsiPowerErrorBound θ := by
  rw [PsiPowerErrorBound]
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with x hx hx_nonneg
  have hscale_nonneg : 0 ≤ x ^ θ := Real.rpow_nonneg hx_nonneg θ
  simpa [Real.norm_eq_abs, abs_of_nonneg hscale_nonneg] using hx

/-- A pointwise eventual-tail estimate closes the power-scale Chebyshev-`ψ`
Big-O predicate. -/
theorem psiPowerErrorBound_of_pointwise {θ C X : ℝ}
    (h : ∀ x ≥ X, |chebyshevPsi x - x| ≤ C * x ^ θ) :
    PsiPowerErrorBound θ :=
  psiPowerErrorBound_of_eventual_abs_bound (by
    filter_upwards [eventually_ge_atTop X] with x hx
    exact h x hx)

/-- Power functions separated by a positive exponent gap are little-o at
`+∞`.  This is the scale comparison used by the single-zero obstruction:
`x^(β-δ)` is asymptotically smaller than `x^β` for `δ > 0`. -/
lemma rpow_sub_delta_isLittleO_rpow_atTop {β delta : ℝ}
    (hdelta_pos : 0 < delta) :
    (fun x : ℝ => x ^ (β - delta)) =o[(atTop : Filter ℝ)]
      (fun x : ℝ => x ^ β) := by
  refine (isLittleO_iff_tendsto' ?_).2 ?_
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx hzero
    exact False.elim ((Real.rpow_pos_of_pos hx β).ne' hzero)
  · have hratio_eq :
        (fun x : ℝ => x ^ (β - delta) / x ^ β) =ᶠ[atTop]
          fun x : ℝ => x ^ (-delta) := by
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
      rw [Real.rpow_sub hx β delta]
      have hxβ_ne : x ^ β ≠ 0 := (Real.rpow_pos_of_pos hx β).ne'
      have hxδ_ne : x ^ delta ≠ 0 :=
        (Real.rpow_pos_of_pos hx delta).ne'
      have hdiv : (x ^ β / x ^ delta) / x ^ β = (x ^ delta)⁻¹ := by
        field_simp [hxβ_ne, hxδ_ne]
      rw [hdiv, Real.rpow_neg hx.le]
    exact (tendsto_rpow_neg_atTop hdelta_pos).congr' hratio_eq.symm

/-- Big-O bounds for real-valued functions can be viewed as complex-valued
bounds after coercing the left side to `ℂ`. -/
lemma isBigO_complex_ofReal_of_isBigO {f g : ℝ → ℝ}
    (h : f =O[(atTop : Filter ℝ)] g) :
    (fun x : ℝ => (f x : ℂ)) =O[(atTop : Filter ℝ)] g := by
  simpa using (Complex.isBigO_ofReal_left.mpr h)

/-! ### Mellin continuation supplied by a power-saving `ψ` error -/

/-- The Chebyshev-`ψ` error cut off below `1`.  The cutoff removes the
irrelevant behavior at zero when taking its Mellin transform. -/
noncomputable def psiErrorAboveOne (x : ℝ) : ℝ :=
  Set.indicator (Set.Ici (1 : ℝ)) (fun y : ℝ => chebyshevPsi y - y) x

/-- Complex-valued form of the cutoff Chebyshev-`ψ` error. -/
noncomputable def psiErrorAboveOneComplex (x : ℝ) : ℂ :=
  (psiErrorAboveOne x : ℂ)

/-- `ψ` is locally integrable on the positive real axis. -/
lemma locallyIntegrableOn_chebyshevPsi :
    LocallyIntegrableOn chebyshevPsi (Set.Ioi (0 : ℝ)) := by
  intro x hx
  refine ⟨Set.Icc (0 : ℝ) (x + 1),
    nhdsWithin_le_nhds (Icc_mem_nhds hx (lt_add_one x)), ?_⟩
  change IntegrableOn (fun t : ℝ => chebyshevPsi t)
    (Set.Icc (0 : ℝ) (x + 1))
  simpa [chebyshevPsi_eq_mathlib, Chebyshev.psi_eq_sum_Icc] using
    (integrableOn_mul_sum_Icc
      (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ))
      (a := (0 : ℝ)) (b := x + 1) (m := 0) (g := fun _ : ℝ => (1 : ℝ))
      (by norm_num)
      (continuousOn_const.integrableOn_Icc))

/-- The cutoff `ψ(x)-x` error is locally integrable on `(0,∞)`. -/
lemma locallyIntegrableOn_psiErrorAboveOne :
    LocallyIntegrableOn psiErrorAboveOne (Set.Ioi (0 : ℝ)) := by
  have hid : LocallyIntegrableOn (fun x : ℝ => x) (Set.Ioi (0 : ℝ)) :=
    continuous_id.locallyIntegrable.locallyIntegrableOn _
  have herr :
      LocallyIntegrableOn (fun x : ℝ => chebyshevPsi x - x)
        (Set.Ioi (0 : ℝ)) :=
    locallyIntegrableOn_chebyshevPsi.sub hid
  intro x hx
  rcases herr x hx with ⟨u, hu, hint⟩
  exact ⟨u, hu, by
    simpa [psiErrorAboveOne] using hint.indicator measurableSet_Ici⟩

/-- Complex coercion preserves local integrability of the cutoff `ψ` error. -/
lemma locallyIntegrableOn_psiErrorAboveOneComplex :
    LocallyIntegrableOn psiErrorAboveOneComplex (Set.Ioi (0 : ℝ)) := by
  simpa [psiErrorAboveOneComplex, Function.comp_def] using
    Complex.ofRealCLM.locallyIntegrableOn_comp
      locallyIntegrableOn_psiErrorAboveOne

/-- A power-scale `ψ` error bound gives the same bound for the cutoff complex
error at infinity. -/
lemma psiErrorAboveOneComplex_isBigO_atTop {θ : ℝ}
    (herror : PsiPowerErrorBound θ) :
    psiErrorAboveOneComplex =O[(atTop : Filter ℝ)] (fun x : ℝ => x ^ θ) := by
  have hcomplex :
      (fun x : ℝ => ((chebyshevPsi x - x : ℝ) : ℂ))
        =O[(atTop : Filter ℝ)] (fun x : ℝ => x ^ θ) :=
    isBigO_complex_ofReal_of_isBigO herror
  refine hcomplex.congr' ?_ (Filter.EventuallyEq.rfl)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  change ((chebyshevPsi x - x : ℝ) : ℂ) = (psiErrorAboveOne x : ℂ)
  norm_cast
  simp [psiErrorAboveOne, hx]

/-- The cutoff error vanishes near zero, hence satisfies every power bound
there. -/
lemma psiErrorAboveOneComplex_isBigO_zero (b : ℝ) :
    psiErrorAboveOneComplex =O[𝓝[>] (0 : ℝ)]
      (fun x : ℝ => x ^ (-b)) := by
  refine Asymptotics.IsBigO.of_bound 0 ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
  have hxnot : ¬ (1 : ℝ) ≤ x := not_le.mpr hx.2
  simp [psiErrorAboveOneComplex, psiErrorAboveOne, hxnot]

/-- The cutoff error has a convergent Mellin transform at `-s` throughout
`Re(s) > θ` under the power bound `ψ(x)-x = O(x^θ)`. -/
theorem mellinConvergent_psiErrorAboveOneComplex_neg_of_power_error
    {θ : ℝ} (herror : PsiPowerErrorBound θ) {s : ℂ} (hs : θ < s.re) :
    MellinConvergent psiErrorAboveOneComplex (-s) := by
  apply mellinConvergent_of_isBigO_rpow
    locallyIntegrableOn_psiErrorAboveOneComplex
    (a := -θ) (b := -s.re - 1)
  · simpa using psiErrorAboveOneComplex_isBigO_atTop herror
  · simp only [Complex.neg_re]
    linarith
  · exact psiErrorAboveOneComplex_isBigO_zero (-s.re - 1)
  · simp only [Complex.neg_re]
    linarith

/-- Integral form of the cutoff Mellin transform. -/
lemma mellin_psiErrorAboveOneComplex_neg_eq_integral (s : ℂ) :
    mellin psiErrorAboveOneComplex (-s) =
      ∫ t in Set.Ioi (1 : ℝ),
        ((chebyshevPsi t - t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  let F : ℝ → ℂ := fun t =>
    ((chebyshevPsi t - t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))
  have hintegrand :
      (fun t : ℝ => (t : ℂ) ^ ((-s) - 1) • psiErrorAboveOneComplex t) =
        fun t : ℝ => Set.indicator (Set.Ici (1 : ℝ)) F t := by
    funext t
    by_cases ht : (1 : ℝ) ≤ t
    · simp only [Set.indicator_apply, Set.mem_Ici, ht, if_true,
        psiErrorAboveOneComplex, psiErrorAboveOne,
        Complex.ofReal_sub, smul_eq_mul, F]
      rw [show -s - 1 = -(s + 1) by ring]
      ring
    · simp only [Set.indicator_apply, Set.mem_Ici, ht, if_false,
        psiErrorAboveOneComplex, psiErrorAboveOne]
      norm_num
  rw [mellin, hintegrand]
  calc
    (∫ t in Set.Ioi (0 : ℝ), Set.indicator (Set.Ici (1 : ℝ)) F t) =
        ∫ t : ℝ, Set.indicator (Set.Ioi (0 : ℝ))
          (Set.indicator (Set.Ici (1 : ℝ)) F) t := by
            rw [integral_indicator measurableSet_Ioi]
    _ = ∫ t : ℝ, Set.indicator (Set.Ici (1 : ℝ)) F t := by
      apply integral_congr_ae
      filter_upwards [] with t
      by_cases ht : (1 : ℝ) ≤ t
      · have ht0 : t ∈ Set.Ioi (0 : ℝ) := lt_of_lt_of_le zero_lt_one ht
        simp only [Set.indicator_apply, Set.mem_Ici, ht, ht0, if_true]
      · simp only [Set.indicator_apply, Set.mem_Ici, ht, if_false,
          Set.mem_Ioi, ite_self]
    _ = ∫ t in Set.Ici (1 : ℝ), F t :=
      integral_indicator measurableSet_Ici
    _ = ∫ t in Set.Ioi (1 : ℝ), F t := integral_Ici_eq_integral_Ioi
    _ = ∫ t in Set.Ioi (1 : ℝ),
        ((chebyshevPsi t - t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := rfl

/-- A power-saving bound `ψ(x)-x = O(x^θ)` makes the Mellin transform of the
cutoff error holomorphic after the change of variables `z ↦ -z` throughout
the half-plane `Re(z) > θ`.

This is the analytic-continuation half of the Landau/Mellin converse route:
once the transform is identified with the logarithmic derivative of `ζ` on
`Re(z) > 1`, uniqueness of analytic continuation can exclude a zeta zero in
the larger half-plane. -/
theorem differentiableAt_mellin_psiErrorAboveOneComplex_neg_of_power_error
    {θ : ℝ} (herror : PsiPowerErrorBound θ) {s : ℂ} (hs : θ < s.re) :
    DifferentiableAt ℂ
      (fun z : ℂ => mellin psiErrorAboveOneComplex (-z)) s := by
  have htop :
      psiErrorAboveOneComplex =O[(atTop : Filter ℝ)]
        (fun x : ℝ => x ^ (-(-θ))) := by
    simpa using psiErrorAboveOneComplex_isBigO_atTop herror
  have hMellin :
      DifferentiableAt ℂ (mellin psiErrorAboveOneComplex) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow
      locallyIntegrableOn_psiErrorAboveOneComplex
      htop
      (by simp only [Complex.neg_re]; linarith)
      (psiErrorAboveOneComplex_isBigO_zero (-s.re - 1))
      (by simp only [Complex.neg_re]; linarith)
  simpa only [Function.comp_apply] using
    hMellin.comp s
      (differentiableAt_id.neg : DifferentiableAt ℂ (fun z : ℂ => -z) s)

/-- On the half-plane of absolute convergence, the Mellin transform of the
cutoff `ψ(x)-x` error is exactly the regularized logarithmic derivative

`s * M(s) = -ζ'(s)/ζ(s) - s/(s-1)`.

Together with
`differentiableAt_mellin_psiErrorAboveOneComplex_neg_of_power_error`, this is
the concrete overlap identity required by the Mellin/Landau zero-exclusion
route. -/
theorem mul_mellin_psiErrorAboveOneComplex_neg_eq_neg_logDeriv_sub_pole
    {s : ℂ} (hs : 1 < s.re) :
    s * mellin psiErrorAboveOneComplex (-s) =
      -deriv riemannZeta s / riemannZeta s - s / (s - 1) := by
  let E : ℝ → ℂ := fun t =>
    ((chebyshevPsi t - t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))
  let A : ℝ → ℂ := fun t =>
    (chebyshevPsi t : ℂ) * (t : ℂ) ^ (-(s + 1))
  let P : ℝ → ℂ := fun t => (t : ℂ) ^ (-s)
  have herror_one : PsiPowerErrorBound 1 := by
    simpa [PsiPowerErrorBound, Real.rpow_one] using chebyshevPsi_sub_id_isBigO_id
  have hconv : MellinConvergent psiErrorAboveOneComplex (-s) :=
    mellinConvergent_psiErrorAboveOneComplex_neg_of_power_error
      (θ := 1) herror_one hs
  have hE : IntegrableOn E (Set.Ioi (1 : ℝ)) := by
    rw [MellinConvergent] at hconv
    have hmono := hconv.mono_set (Set.Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num))
    refine hmono.congr_fun ?_ measurableSet_Ioi
    intro t ht
    have ht_mem : (1 : ℝ) ≤ t := le_of_lt ht
    simp only [psiErrorAboveOneComplex, psiErrorAboveOne,
      Set.indicator_apply, Set.mem_Ici, ht_mem, if_true,
      Complex.ofReal_sub, smul_eq_mul, E]
    rw [show -s - 1 = -(s + 1) by ring]
    ring
  have hP : IntegrableOn P (Set.Ioi (1 : ℝ)) := by
    exact integrableOn_Ioi_cpow_of_lt
      (by simp only [Complex.neg_re]; linarith) zero_lt_one
  have hA : IntegrableOn A (Set.Ioi (1 : ℝ)) := by
    refine (hE.add hP).congr_fun ?_ measurableSet_Ioi
    intro t ht
    have htpos : 0 < t := zero_lt_one.trans ht
    change E t + P t = A t
    have htpower :
        (t : ℂ) * (t : ℂ) ^ (-(s + 1)) = (t : ℂ) ^ (-s) := by
      calc
        (t : ℂ) * (t : ℂ) ^ (-(s + 1)) =
            (t : ℂ) ^ (1 : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
          rw [Complex.cpow_one]
        _ = (t : ℂ) ^ ((1 : ℂ) + (-(s + 1))) := by
          rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr htpos.ne')]
        _ = (t : ℂ) ^ (-s) := by
          congr 1
          ring
    simp only [E, P, A, Complex.ofReal_sub]
    rw [← htpower]
    ring
  have hsplit :
      (∫ t in Set.Ioi (1 : ℝ), E t) =
        (∫ t in Set.Ioi (1 : ℝ), A t) -
          ∫ t in Set.Ioi (1 : ℝ), P t := by
    rw [← integral_sub hA hP]
    apply integral_congr_ae
    refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
    intro t ht
    have htpos : 0 < t := zero_lt_one.trans ht
    have htpower :
        (t : ℂ) * (t : ℂ) ^ (-(s + 1)) = (t : ℂ) ^ (-s) := by
      calc
        (t : ℂ) * (t : ℂ) ^ (-(s + 1)) =
            (t : ℂ) ^ (1 : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
          rw [Complex.cpow_one]
        _ = (t : ℂ) ^ ((1 : ℂ) + (-(s + 1))) := by
          rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr htpos.ne')]
        _ = (t : ℂ) ^ (-s) := by
          congr 1
          ring
    simp only [E, P, A, Complex.ofReal_sub]
    rw [← htpower]
    ring
  have hLseries :
      LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s =
        s * ∫ t in Set.Ioi (1 : ℝ), A t := by
    have hO :
        (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n,
          ArithmeticFunction.vonMangoldt k) =O[atTop]
            fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
      refine (Asymptotics.isBigO_iff).mpr
        ⟨Real.log 4 + 4, Filter.Eventually.of_forall ?_⟩
      intro n
      have hpsi : Chebyshev.psi (n : ℝ) ≤
          (Real.log 4 + 4) * (n : ℝ) :=
        Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n)
      have hsum_eq :
          ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt k =
            Chebyshev.psi (n : ℝ) := by
        rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
        rw [← Finset.insert_Icc_add_one_left_eq_Icc n.zero_le,
          Finset.sum_insert (by aesop)]
        simp [ArithmeticFunction.vonMangoldt]
      have hnonneg :
          0 ≤ ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt k :=
        Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
      calc
        ‖∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt k‖ =
            ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt k :=
          Real.norm_of_nonneg hnonneg
        _ = Chebyshev.psi (n : ℝ) := hsum_eq
        _ ≤ (Real.log 4 + 4) * (n : ℝ) := hpsi
        _ = (Real.log 4 + 4) * ‖(n : ℝ) ^ (1 : ℝ)‖ := by
          simp [Real.rpow_one]
    have hrepr :=
      LSeries_eq_mul_integral_of_nonneg
        (fun n : ℕ => ArithmeticFunction.vonMangoldt n)
        (r := (1 : ℝ)) (by norm_num) (s := s) hs
        hO
        (fun _ => ArithmeticFunction.vonMangoldt_nonneg)
    rw [hrepr]
    congr 1
    apply integral_congr_ae
    refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
    intro t _ht
    have hsum :
        (∑ k ∈ Finset.Icc 1 ⌊t⌋₊,
          (ArithmeticFunction.vonMangoldt k : ℂ)) =
            (chebyshevPsi t : ℂ) := by
      rw [chebyshevPsi_eq_mathlib, Chebyshev.psi_eq_sum_Icc]
      rw [← Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le ⌊t⌋₊),
        Finset.sum_insert (by aesop)]
      simp [ArithmeticFunction.vonMangoldt]
    calc
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊,
          (ArithmeticFunction.vonMangoldt k : ℂ)) *
          (t : ℂ) ^ (-(s + 1)) =
          (chebyshevPsi t : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
        rw [hsum]
      _ = A t := rfl
  have hP_eval :
      (∫ t in Set.Ioi (1 : ℝ), P t) = 1 / (s - 1) := by
    rw [show (∫ t in Set.Ioi (1 : ℝ), P t) =
        ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s) by rfl]
    rw [integral_Ioi_cpow_of_lt
      (by simp only [Complex.neg_re]; linarith) zero_lt_one]
    rw [Complex.ofReal_one, one_cpow]
    rw [show -s + 1 = -(s - 1) by ring, neg_div_neg_eq]
  rw [mellin_psiErrorAboveOneComplex_neg_eq_integral]
  change s * (∫ t in Set.Ioi (1 : ℝ), E t) = _
  rw [hsplit, mul_sub, ← hLseries,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
    hP_eval]
  ring

/-- The Mellin-side model for the regularized logarithmic derivative:
`s * M(-s)` where `M` is the Mellin transform of the cutoff `ψ(x)-x` error. -/
noncomputable def regularizedNegLogDerivModel (s : ℂ) : ℂ :=
  s * mellin psiErrorAboveOneComplex (-s)

/-- Under a `ψ(x)-x = O(x^θ)` input, the Mellin-side regularized
logarithmic-derivative model is differentiable throughout `Re(s) > θ`. -/
theorem differentiableAt_regularizedNegLogDerivModel_of_psi_power_error
    {θ : ℝ} (herror : PsiPowerErrorBound θ) {s : ℂ} (hs : θ < s.re) :
    DifferentiableAt ℂ regularizedNegLogDerivModel s := by
  simpa [regularizedNegLogDerivModel] using
    (differentiableAt_id : DifferentiableAt ℂ (fun z : ℂ => z) s).mul
      (differentiableAt_mellin_psiErrorAboveOneComplex_neg_of_power_error
        herror hs)

/-- Set-level version of
`differentiableAt_regularizedNegLogDerivModel_of_psi_power_error`. -/
theorem differentiableOn_regularizedNegLogDerivModel_of_psi_power_error
    {θ : ℝ} (herror : PsiPowerErrorBound θ) :
    DifferentiableOn ℂ regularizedNegLogDerivModel {s : ℂ | θ < s.re} := by
  intro s hs
  exact (differentiableAt_regularizedNegLogDerivModel_of_psi_power_error
    herror hs).differentiableWithinAt

/-- On the original half-plane of absolute convergence, the Mellin-side model
is the regularized logarithmic derivative of zeta. -/
theorem regularizedNegLogDerivModel_eq_neg_deriv_div_sub_pole
    {s : ℂ} (hs : 1 < s.re) :
    regularizedNegLogDerivModel s =
      -deriv riemannZeta s / riemannZeta s - s / (s - 1) := by
  simpa [regularizedNegLogDerivModel] using
    mul_mellin_psiErrorAboveOneComplex_neg_eq_neg_logDeriv_sub_pole hs

/-- `EqOn` form of the overlap identity between the Mellin-side model and the
regularized logarithmic derivative of zeta. -/
theorem eqOn_regularizedNegLogDerivModel_neg_deriv_div_sub_pole :
    Set.EqOn regularizedNegLogDerivModel
      (fun s : ℂ => -deriv riemannZeta s / riemannZeta s - s / (s - 1))
      {s : ℂ | 1 < s.re} := by
  intro s hs
  exact regularizedNegLogDerivModel_eq_neg_deriv_div_sub_pole hs

/-- Eventually, the selected zero contribution has the expected
`‖ρ‖⁻¹ * x^ρ.re` norm lower bound. -/
lemma eventually_norm_zero_contribution_ge_inv_norm_mul_rpow_re (ρ : ℂ) :
    ∀ᶠ (x : ℝ) in (atTop : Filter ℝ),
      ‖ρ‖⁻¹ * ‖(x : ℝ) ^ ρ.re‖ ≤ ‖-((x : ℂ) ^ ρ / ρ)‖ := by
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
  rw [norm_neg, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hpow_nonneg : 0 ≤ x ^ ρ.re :=
    (Real.rpow_pos_of_pos hx ρ.re).le
  simp [Real.norm_eq_abs, abs_of_nonneg hpow_nonneg, div_eq_mul_inv,
    mul_comm]

/-- Frequent-good-points version of the dominant-term obstruction.

The remainder need not be globally `o(scale)`: it is enough that there are
arbitrarily large good points where the main term has size at least
`c * scale`, the remainder is at most `(c / 4) * scale`, and the decomposition
holds.  A global `O(smaller)` bound with `smaller=o(scale)` would make `f`
small eventually, contradicting one of those good points. -/
theorem not_isBigO_of_frequently_norm_ge_const_mul_and_small_remainder
    {E : Type*} [NormedAddCommGroup E]
    {f main err : ℝ → E} {scale smaller : ℝ → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hgood : ∃ᶠ x in (atTop : Filter ℝ),
      0 < ‖scale x‖ ∧
      c * ‖scale x‖ ≤ ‖main x‖ ∧
      ‖err x‖ ≤ (c / 4) * ‖scale x‖ ∧
      f x = main x + err x)
    (hsmaller : smaller =o[(atTop : Filter ℝ)] scale) :
    ¬ f =O[(atTop : Filter ℝ)] smaller := by
  intro hf_smaller
  have hf_scale : f =o[(atTop : Filter ℝ)] scale :=
    hf_smaller.trans_isLittleO hsmaller
  have hc_quarter : 0 < c / 4 := by positivity
  have hf_small :
      ∀ᶠ x in (atTop : Filter ℝ), ‖f x‖ ≤ (c / 4) * ‖scale x‖ :=
    hf_scale.def hc_quarter
  have hfreq_false : ∃ᶠ x in (atTop : Filter ℝ), False := by
    refine (hgood.and_eventually hf_small).mono ?_
    intro x hx
    rcases hx with ⟨⟨hscale_pos, hmain_lower, herr_small, hdecomp⟩,
      hf_small_x⟩
    have hmain_eq : main x = f x - err x := by
      rw [hdecomp]
      abel
    have hmain_upper_norm : ‖main x‖ ≤ ‖f x‖ + ‖err x‖ := by
      simpa [hmain_eq] using norm_sub_le (f x) (err x)
    have hmain_upper :
        ‖main x‖ ≤ (c / 2) * ‖scale x‖ := by
      calc
        ‖main x‖ ≤ ‖f x‖ + ‖err x‖ := hmain_upper_norm
        _ ≤ (c / 4) * ‖scale x‖ + (c / 4) * ‖scale x‖ :=
          add_le_add hf_small_x herr_small
        _ = (c / 2) * ‖scale x‖ := by ring
    have hhalf_lt : c / 2 < c := by linarith
    have hscale_gap : (c / 2) * ‖scale x‖ < c * ‖scale x‖ :=
      mul_lt_mul_of_pos_right hhalf_lt hscale_pos
    linarith
  exact hfreq_false (Filter.Eventually.of_forall (fun _ => not_false))

/-- Frequent-good-points version of the actual-sign single-zero obstruction.

This weakens the global tail hypothesis expected from a full explicit-formula
converse.  It is enough to have arbitrarily large good points where the
retained tail is at most one quarter of the selected-zero main scale and the
actual-sign complex `ψ` decomposition holds.  A global `ψ` power-saving bound
would make the left side small eventually, contradicting those good points. -/
theorem not_psi_power_error_bound_sub_delta_of_frequently_negative_single_zero_complex_psi_decomposition
    {ρ : ℂ} {delta : ℝ} (hρ_ne : ρ ≠ 0) (hdelta_pos : 0 < delta)
    {remainder : ℝ → ℂ}
    (hgood :
      ∃ᶠ x in (atTop : Filter ℝ),
        ‖remainder x‖ ≤ (‖ρ‖⁻¹ / 4) * ‖(x : ℝ) ^ ρ.re‖ ∧
        ((chebyshevPsi x - x : ℝ) : ℂ) =
          -((x : ℂ) ^ ρ / ρ) + remainder x) :
    ¬ PsiPowerErrorBound (ρ.re - delta) := by
  intro herror
  have hc : 0 < ‖ρ‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hρ_ne)
  have hscale_main :
      ∀ᶠ (x : ℝ) in (atTop : Filter ℝ),
        0 < ‖(x : ℝ) ^ ρ.re‖ ∧
        ‖ρ‖⁻¹ * ‖(x : ℝ) ^ ρ.re‖ ≤ ‖-((x : ℂ) ^ ρ / ρ)‖ := by
    filter_upwards
      [Filter.eventually_gt_atTop (0 : ℝ),
        eventually_norm_zero_contribution_ge_inv_norm_mul_rpow_re ρ] with
      x hx_pos hx_lower
    exact
      ⟨norm_pos_iff.mpr (Real.rpow_pos_of_pos hx_pos ρ.re).ne',
        by simpa using hx_lower⟩
  have hgood_full : ∃ᶠ (x : ℝ) in (atTop : Filter ℝ),
      0 < ‖(x : ℝ) ^ ρ.re‖ ∧
      ‖ρ‖⁻¹ * ‖(x : ℝ) ^ ρ.re‖ ≤ ‖-((x : ℂ) ^ ρ / ρ)‖ ∧
      ‖remainder x‖ ≤ (‖ρ‖⁻¹ / 4) * ‖(x : ℝ) ^ ρ.re‖ ∧
      ((chebyshevPsi x - x : ℝ) : ℂ) =
        -((x : ℂ) ^ ρ / ρ) + remainder x := by
    refine (hgood.and_eventually hscale_main).mono ?_
    intro x hx
    rcases hx with ⟨⟨hrem_small, hdecomp⟩, hscale_pos, hmain_lower⟩
    exact ⟨hscale_pos, hmain_lower, hrem_small, hdecomp⟩
  have hcomplex :
      (fun x : ℝ => ((chebyshevPsi x - x : ℝ) : ℂ))
        =O[atTop] (fun x : ℝ => x ^ (ρ.re - delta)) :=
    isBigO_complex_ofReal_of_isBigO herror
  exact
    not_isBigO_of_frequently_norm_ge_const_mul_and_small_remainder
      (E := ℂ)
      (f := fun x : ℝ => ((chebyshevPsi x - x : ℝ) : ℂ))
      (main := fun x : ℝ => -((x : ℂ) ^ ρ / ρ))
      (err := remainder)
      (scale := fun x : ℝ => x ^ ρ.re)
      (smaller := fun x : ℝ => x ^ (ρ.re - delta))
      (c := ‖ρ‖⁻¹)
      hc hgood_full
      (rpow_sub_delta_isLittleO_rpow_atTop hdelta_pos)
      hcomplex

/-- A concrete form of the proposed strong PNT-error input: some power saving
strictly below the `2 / 3` barrier for `ψ(x) - x`. -/
abbrev PsiPowerErrorBelowTwoThirds : Prop :=
  ∃ θ : ℝ, 0 ≤ θ ∧ θ < (2 / 3 : ℝ) ∧ PsiPowerErrorBound θ

/-- Build the concrete below-`2/3` `ψ`-power-error input from an eventual
absolute-value estimate with exponent strictly below `2/3`. -/
theorem psiPowerErrorBelowTwoThirds_of_eventual_abs_bound
    {θ C : ℝ} (hθ_nonneg : 0 ≤ θ) (hθ_lt : θ < (2 / 3 : ℝ))
    (h : ∀ᶠ x in atTop,
      |chebyshevPsi x - x| ≤ C * x ^ θ) :
    PsiPowerErrorBelowTwoThirds :=
  ⟨θ, hθ_nonneg, hθ_lt, psiPowerErrorBound_of_eventual_abs_bound h⟩

/-- Build the concrete below-`2/3` `ψ`-power-error input from a pointwise
tail estimate with exponent strictly below `2/3`. -/
theorem psiPowerErrorBelowTwoThirds_of_pointwise
    {θ C X : ℝ} (hθ_nonneg : 0 ≤ θ) (hθ_lt : θ < (2 / 3 : ℝ))
    (h : ∀ x ≥ X, |chebyshevPsi x - x| ≤ C * x ^ θ) :
    PsiPowerErrorBelowTwoThirds :=
  psiPowerErrorBelowTwoThirds_of_eventual_abs_bound hθ_nonneg hθ_lt
    (by
      filter_upwards [eventually_ge_atTop X] with x hx
      exact h x hx)

/-- A power-saving statement at exponent `2/3 - delta` supplies the concrete
below-`2/3` `ψ`-power-error input. -/
theorem psiPowerErrorBelowTwoThirds_of_power_saving
    {delta : ℝ} (hdelta_pos : 0 < delta) (hdelta_le : delta ≤ (2 / 3 : ℝ))
    (herror : PsiPowerErrorBound ((2 / 3 : ℝ) - delta)) :
    PsiPowerErrorBelowTwoThirds :=
  ⟨(2 / 3 : ℝ) - delta, by linarith, by linarith, herror⟩

/-- Route interface for the converse explicit-formula step:
`ψ(x) - x = O(x ^ θ)` for some `θ < 2 / 3` rules out nontrivial zeros on
the reflected line `Re(s) = 2 / 3`. -/
abbrev PsiPowerErrorBelowTwoThirdsExcludesLineTwoThirds : Prop :=
  PsiPowerErrorBelowTwoThirds →
    ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ →
      ρ.re = (2 / 3 : ℝ) → False

/-- Concrete `ψ`-error version of the `Re(s) = 1 / 3` bridge.  The hard
analytic input is the converse explicit-formula implication packaged in
`PsiPowerErrorBelowTwoThirdsExcludesLineTwoThirds`. -/
theorem no_zeros_on_one_third_of_psi_power_error_below_two_thirds_bridge
    (hbridge : PsiPowerErrorBelowTwoThirdsExcludesLineTwoThirds)
    (herror : PsiPowerErrorBelowTwoThirds) :
    NoZerosOnVerticalLine (1 / 3) :=
  no_zeros_on_one_third_of_strong_pnt_error_bridge
    (StrongPNTError := PsiPowerErrorBelowTwoThirds) hbridge herror

/-- The same concrete `ψ`-error route also directly excludes zeta zeros on
the reflected line `Re(s)=2/3`. -/
theorem no_zeros_on_two_thirds_of_psi_power_error_below_two_thirds_bridge
    (hbridge : PsiPowerErrorBelowTwoThirdsExcludesLineTwoThirds)
    (herror : PsiPowerErrorBelowTwoThirds) :
    NoZerosOnVerticalLine (2 / 3) := by
  intro s hs hzero
  have hnt : RiemannHypothesis.IsNontrivialZero s := by
    refine ⟨hzero, ?_, ?_⟩
    · nlinarith [hs]
    · nlinarith [hs]
  exact hbridge herror s hnt hs

/-- General power-saving `ψ` error below a real boundary line. -/
abbrev PsiPowerErrorBelowLine (β : ℝ) : Prop :=
  ∃ θ : ℝ, 0 ≤ θ ∧ θ < β ∧ PsiPowerErrorBound θ

/-- Build the general below-line `ψ`-power-error input from an eventual
absolute-value estimate. -/
theorem psiPowerErrorBelowLine_of_eventual_abs_bound
    {β θ C : ℝ} (hθ_nonneg : 0 ≤ θ) (hθ_lt : θ < β)
    (h : ∀ᶠ x in atTop,
      |chebyshevPsi x - x| ≤ C * x ^ θ) :
    PsiPowerErrorBelowLine β :=
  ⟨θ, hθ_nonneg, hθ_lt, psiPowerErrorBound_of_eventual_abs_bound h⟩

/-- Build the general below-line `ψ`-power-error input from a pointwise
tail estimate. -/
theorem psiPowerErrorBelowLine_of_pointwise
    {β θ C X : ℝ} (hθ_nonneg : 0 ≤ θ) (hθ_lt : θ < β)
    (h : ∀ x ≥ X, |chebyshevPsi x - x| ≤ C * x ^ θ) :
    PsiPowerErrorBelowLine β :=
  psiPowerErrorBelowLine_of_eventual_abs_bound hθ_nonneg hθ_lt
    (by
      filter_upwards [eventually_ge_atTop X] with x hx
      exact h x hx)

/-- A power-saving statement at exponent `β - delta` supplies the below-line
`ψ`-power-error input at the boundary `β`. -/
theorem psiPowerErrorBelowLine_of_power_saving
    {β delta : ℝ} (hdelta_pos : 0 < delta) (hθ_nonneg : 0 ≤ β - delta)
    (herror : PsiPowerErrorBound (β - delta)) :
    PsiPowerErrorBelowLine β :=
  ⟨β - delta, hθ_nonneg, by linarith, herror⟩

/-- The concrete `θ < 2/3` `ψ`-error input is the specialization of the
general below-line predicate at `β = 2/3`. -/
theorem psiPowerErrorBelowLine_two_thirds_of_below_two_thirds
    (herror : PsiPowerErrorBelowTwoThirds) :
    PsiPowerErrorBelowLine (2 / 3) := by
  simpa [PsiPowerErrorBelowTwoThirds, PsiPowerErrorBelowLine] using herror

/-- Monotonicity of the below-line `ψ`-power-error predicate in the boundary
line. -/
theorem psiPowerErrorBelowLine_mono {β γ : ℝ}
    (hβγ : β ≤ γ) (herror : PsiPowerErrorBelowLine β) :
    PsiPowerErrorBelowLine γ := by
  rcases herror with ⟨θ, hθ_nonneg, hθ_lt, hθ_bound⟩
  exact ⟨θ, hθ_nonneg, lt_of_lt_of_le hθ_lt hβγ, hθ_bound⟩

/-- A concrete `θ < 2/3` `ψ`-error input is also below any boundary
`β >= 2/3`. -/
theorem psiPowerErrorBelowLine_of_below_two_thirds_of_two_thirds_le
    {β : ℝ} (hβ : (2 / 3 : ℝ) ≤ β)
    (herror : PsiPowerErrorBelowTwoThirds) :
    PsiPowerErrorBelowLine β :=
  psiPowerErrorBelowLine_mono hβ
    (psiPowerErrorBelowLine_two_thirds_of_below_two_thirds herror)

/-- Route interface for the converse explicit-formula principle: a `ψ` error
with exponent below `β` excludes nontrivial zeros on or to the right of
`Re(s) = β`. -/
abbrev PsiPowerErrorBelowLineExcludesZerosRightOf (β : ℝ) : Prop :=
  PsiPowerErrorBelowLine β →
    ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → β ≤ ρ.re → False

/-- Explicit-formula converse target: a power saving below `β` for
Chebyshev-`ψ` excludes nontrivial zeros on or to the right of `Re(s)=β`.

This historical route-interface name remains for the finite-zero/oscillation
path.  The alternative Mellin/Landau converse is proved in
`ZeroFreeRegion.MeromorphicAux`; this proposition is not itself an
unconditional explicit-formula theorem. -/
def ExplicitFormulaConversePowerTarget (β : ℝ) : Prop :=
  PsiPowerErrorBelowLine β →
    ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → β ≤ ρ.re → False

/-- The explicit-formula converse target supplies the general
`ψ`-power-error zero-exclusion interface with the same boundary. -/
theorem psiPowerErrorBelowLineExcludesZerosRightOf_of_explicit_formula_converse_power
    {β : ℝ} (h : ExplicitFormulaConversePowerTarget β) :
    PsiPowerErrorBelowLineExcludesZerosRightOf β := by
  simpa [ExplicitFormulaConversePowerTarget,
    PsiPowerErrorBelowLineExcludesZerosRightOf] using h

/-- The general `ψ`-power-error zero-exclusion interface is the same
route target as the explicitly named explicit-formula converse dependency. -/
theorem explicitFormulaConversePowerTarget_of_psiPowerErrorBelowLineExcludesZerosRightOf
    {β : ℝ} (h : PsiPowerErrorBelowLineExcludesZerosRightOf β) :
    ExplicitFormulaConversePowerTarget β := by
  simpa [ExplicitFormulaConversePowerTarget,
    PsiPowerErrorBelowLineExcludesZerosRightOf] using h

/-- Contrapositive form of the general `ψ`-error zero-exclusion interface: if
there is a nontrivial zero on or to the right of `Re(s)=β`, then the
corresponding below-`β` `ψ` power saving cannot hold. -/
theorem not_psi_power_error_below_line_of_exists_zero_right_of_bridge
    {β : ℝ}
    (hbridge : PsiPowerErrorBelowLineExcludesZerosRightOf β)
    (hzero : ∃ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ ∧ β ≤ ρ.re) :
    ¬ PsiPowerErrorBelowLine β := by
  intro herror
  rcases hzero with ⟨ρ, hρ, hρre⟩
  exact hbridge herror ρ hρ hρre

/-- Contrapositive form with the explicit-formula converse dependency named
directly. -/
theorem not_psi_power_error_below_line_of_exists_zero_right_of_explicit_formula_converse
    {β : ℝ}
    (hbridge : ExplicitFormulaConversePowerTarget β)
    (hzero : ∃ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ ∧ β ≤ ρ.re) :
    ¬ PsiPowerErrorBelowLine β :=
  not_psi_power_error_below_line_of_exists_zero_right_of_bridge
    (psiPowerErrorBelowLineExcludesZerosRightOf_of_explicit_formula_converse_power
      hbridge)
    hzero

/-- Same-line zeta-zero contrapositive: a zeta zero on `Re(s)=β` in the
critical strip is a nontrivial zero on the boundary, so the below-`β` `ψ`
power saving cannot hold under the zero-exclusion route interface. -/
theorem not_psi_power_error_below_line_of_exists_zero_on_line_bridge
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hbridge : PsiPowerErrorBelowLineExcludesZerosRightOf β)
    (hzero : ∃ s : ℂ, riemannZeta s = 0 ∧ s.re = β) :
    ¬ PsiPowerErrorBelowLine β := by
  rcases hzero with ⟨s, hs_zero, hs_re⟩
  have hnt : RiemannHypothesis.IsNontrivialZero s := by
    refine ⟨hs_zero, ?_, ?_⟩
    · nlinarith [hs_re, hβ_pos]
    · nlinarith [hs_re, hβ_lt_one]
  exact
    not_psi_power_error_below_line_of_exists_zero_right_of_bridge
      hbridge ⟨s, hnt, le_of_eq hs_re.symm⟩

/-- Same-line zeta-zero contrapositive with the explicit-formula converse
dependency named directly. -/
theorem not_psi_power_error_below_line_of_exists_zero_on_line_explicit_formula_converse
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hbridge : ExplicitFormulaConversePowerTarget β)
    (hzero : ∃ s : ℂ, riemannZeta s = 0 ∧ s.re = β) :
    ¬ PsiPowerErrorBelowLine β :=
  not_psi_power_error_below_line_of_exists_zero_on_line_bridge
    hβ_pos hβ_lt_one
    (psiPowerErrorBelowLineExcludesZerosRightOf_of_explicit_formula_converse_power
      hbridge)
    hzero

/-- Concrete power-saving contrapositive of the general right-of-line bridge:
if a nontrivial zero lies on or to the right of `Re(s)=β`, then no
`O(x^(β-delta))` `ψ` error can hold once the below-`β` zero-exclusion route is
available. -/
theorem not_psi_power_error_bound_sub_delta_of_exists_zero_right_of_bridge
    {β delta : ℝ} (hdelta_pos : 0 < delta) (hθ_nonneg : 0 ≤ β - delta)
    (hbridge : PsiPowerErrorBelowLineExcludesZerosRightOf β)
    (hzero : ∃ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ ∧ β ≤ ρ.re) :
    ¬ PsiPowerErrorBound (β - delta) := by
  intro herror
  exact
    not_psi_power_error_below_line_of_exists_zero_right_of_bridge
      hbridge hzero
      (psiPowerErrorBelowLine_of_power_saving
        hdelta_pos hθ_nonneg herror)

/-- Same power-saving contrapositive with the explicit-formula converse route
dependency named directly. -/
theorem not_psi_power_error_bound_sub_delta_of_exists_zero_right_of_explicit_formula_converse
    {β delta : ℝ} (hdelta_pos : 0 < delta) (hθ_nonneg : 0 ≤ β - delta)
    (hbridge : ExplicitFormulaConversePowerTarget β)
    (hzero : ∃ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ ∧ β ≤ ρ.re) :
    ¬ PsiPowerErrorBound (β - delta) :=
  not_psi_power_error_bound_sub_delta_of_exists_zero_right_of_bridge
    hdelta_pos hθ_nonneg
    (psiPowerErrorBelowLineExcludesZerosRightOf_of_explicit_formula_converse_power
      hbridge)
    hzero

/-- Same-line zeta-zero power-saving contrapositive: a zeta zero on
`Re(s)=β` in the critical strip rules out the concrete `O(x^(β-delta))` `ψ`
error under the route interface. -/
theorem not_psi_power_error_bound_sub_delta_of_exists_zero_on_line_bridge
    {β delta : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hdelta_pos : 0 < delta) (hθ_nonneg : 0 ≤ β - delta)
    (hbridge : PsiPowerErrorBelowLineExcludesZerosRightOf β)
    (hzero : ∃ s : ℂ, riemannZeta s = 0 ∧ s.re = β) :
    ¬ PsiPowerErrorBound (β - delta) := by
  intro herror
  exact
    not_psi_power_error_below_line_of_exists_zero_on_line_bridge
      hβ_pos hβ_lt_one hbridge hzero
      (psiPowerErrorBelowLine_of_power_saving
        hdelta_pos hθ_nonneg herror)

/-- Same-line zeta-zero power-saving contrapositive with the explicit-formula
converse dependency named directly. -/
theorem not_psi_power_error_bound_sub_delta_of_exists_zero_on_line_explicit_formula_converse
    {β delta : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hdelta_pos : 0 < delta) (hθ_nonneg : 0 ≤ β - delta)
    (hbridge : ExplicitFormulaConversePowerTarget β)
    (hzero : ∃ s : ℂ, riemannZeta s = 0 ∧ s.re = β) :
    ¬ PsiPowerErrorBound (β - delta) :=
  not_psi_power_error_bound_sub_delta_of_exists_zero_on_line_bridge
    hβ_pos hβ_lt_one hdelta_pos hθ_nonneg
    (psiPowerErrorBelowLineExcludesZerosRightOf_of_explicit_formula_converse_power
      hbridge)
    hzero

/-- Reflected-line power-saving contrapositive: a zeta zero on
`Re(s)=1-β` reflects to a nontrivial zero on `Re(s)=β`, so it rules out an
`O(x^(β-delta))` `ψ` error under the same below-`β` zero-exclusion route. -/
theorem not_psi_power_error_bound_sub_delta_of_exists_zero_on_reflected_line_bridge
    {β delta : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hdelta_pos : 0 < delta) (hθ_nonneg : 0 ≤ β - delta)
    (hbridge : PsiPowerErrorBelowLineExcludesZerosRightOf β)
    (hzero : ∃ s : ℂ, riemannZeta s = 0 ∧ s.re = 1 - β) :
    ¬ PsiPowerErrorBound (β - delta) := by
  intro herror
  rcases hzero with ⟨s, hs_zero, hs_re⟩
  have hnt : RiemannHypothesis.IsNontrivialZero s := by
    refine ⟨hs_zero, ?_, ?_⟩
    · nlinarith [hs_re, hβ_lt_one]
    · nlinarith [hs_re, hβ_pos]
  have hsym : RiemannHypothesis.IsNontrivialZero (1 - s) :=
    nontrivial_zero_symmetric' hnt
  have hre : β ≤ (1 - s).re := by
    have hcalc : (1 : ℝ) - (1 - β) = β := by ring
    exact le_of_eq (by simp [Complex.sub_re, hs_re, hcalc])
  exact
    not_psi_power_error_bound_sub_delta_of_exists_zero_right_of_bridge
      hdelta_pos hθ_nonneg hbridge ⟨1 - s, hsym, hre⟩ herror

/-- Reflected-line power-saving contrapositive with the explicit-formula
converse route dependency named directly. -/
theorem not_psi_power_error_bound_sub_delta_of_exists_zero_on_reflected_line_explicit_formula_converse
    {β delta : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hdelta_pos : 0 < delta) (hθ_nonneg : 0 ≤ β - delta)
    (hbridge : ExplicitFormulaConversePowerTarget β)
    (hzero : ∃ s : ℂ, riemannZeta s = 0 ∧ s.re = 1 - β) :
    ¬ PsiPowerErrorBound (β - delta) :=
  not_psi_power_error_bound_sub_delta_of_exists_zero_on_reflected_line_bridge
    hβ_pos hβ_lt_one hdelta_pos hθ_nonneg
    (psiPowerErrorBelowLineExcludesZerosRightOf_of_explicit_formula_converse_power
      hbridge)
    hzero

/-- A concrete below-`2/3` `ψ`-error input cannot coexist with a nontrivial
zero on or to the right of any boundary `γ >= 2/3`, assuming the corresponding
zero-exclusion route interface at `γ`. -/
theorem not_psi_power_error_below_two_thirds_of_exists_zero_right_of_bridge
    {γ : ℝ} (hγ : (2 / 3 : ℝ) ≤ γ)
    (hbridge : PsiPowerErrorBelowLineExcludesZerosRightOf γ)
    (hzero : ∃ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ ∧ γ ≤ ρ.re) :
    ¬ PsiPowerErrorBelowTwoThirds := by
  intro herror
  exact
    not_psi_power_error_below_line_of_exists_zero_right_of_bridge
      hbridge hzero
      (psiPowerErrorBelowLine_of_below_two_thirds_of_two_thirds_le
        hγ herror)

/-- If the `β = 2/3` zero-exclusion route is available, a zeta zero on
`Re(s)=1/3` rules out a below-`2/3` `ψ` power saving.  This is the formal
contrapositive of the proposed explicit-formula/PNT-error bridge. -/
theorem not_psi_power_error_below_two_thirds_of_exists_zero_on_one_third_bridge
    (hbridge : PsiPowerErrorBelowLineExcludesZerosRightOf (2 / 3))
    (hzero : ∃ s : ℂ, riemannZeta s = 0 ∧ s.re = (1 / 3 : ℝ)) :
    ¬ PsiPowerErrorBelowTwoThirds := by
  rcases hzero with ⟨s, hs_zero, hs_re⟩
  have hnt : RiemannHypothesis.IsNontrivialZero s := by
    refine ⟨hs_zero, ?_, ?_⟩
    · nlinarith [hs_re]
    · nlinarith [hs_re]
  have hsym : RiemannHypothesis.IsNontrivialZero (1 - s) :=
    nontrivial_zero_symmetric' hnt
  have hre : (2 / 3 : ℝ) ≤ (1 - s).re := by
    have hcalc : (1 : ℝ) - (1 / 3) = 2 / 3 := by norm_num
    exact le_of_eq (by simpa [Complex.sub_re, hs_re] using hcalc.symm)
  exact
    not_psi_power_error_below_two_thirds_of_exists_zero_right_of_bridge
      (γ := 2 / 3) (by norm_num) hbridge ⟨1 - s, hsym, hre⟩

/-- Power-saving contrapositive of the `Re(s)=1/3` bridge: if a zero exists
on `Re(s)=1/3`, then the specific `O(x^(2/3-delta))` `ψ` error cannot hold,
assuming the `2/3` zero-exclusion route interface. -/
theorem not_psi_power_error_bound_two_thirds_sub_delta_of_exists_zero_on_one_third_bridge
    {delta : ℝ} (hdelta_pos : 0 < delta) (hdelta_le : delta ≤ (2 / 3 : ℝ))
    (hbridge : PsiPowerErrorBelowLineExcludesZerosRightOf (2 / 3))
    (hzero : ∃ s : ℂ, riemannZeta s = 0 ∧ s.re = (1 / 3 : ℝ)) :
    ¬ PsiPowerErrorBound ((2 / 3 : ℝ) - delta) := by
  intro herror
  exact
    not_psi_power_error_below_two_thirds_of_exists_zero_on_one_third_bridge
      hbridge hzero
      (psiPowerErrorBelowTwoThirds_of_power_saving
        hdelta_pos hdelta_le herror)

/-- Same power-saving contrapositive with the explicit-formula converse route
dependency named directly. -/
theorem not_psi_power_error_bound_two_thirds_sub_delta_of_exists_zero_on_one_third_explicit_formula_converse
    {delta : ℝ} (hdelta_pos : 0 < delta) (hdelta_le : delta ≤ (2 / 3 : ℝ))
    (hbridge : ExplicitFormulaConversePowerTarget (2 / 3))
    (hzero : ∃ s : ℂ, riemannZeta s = 0 ∧ s.re = (1 / 3 : ℝ)) :
    ¬ PsiPowerErrorBound ((2 / 3 : ℝ) - delta) :=
  not_psi_power_error_bound_two_thirds_sub_delta_of_exists_zero_on_one_third_bridge
    hdelta_pos hdelta_le
    (psiPowerErrorBelowLineExcludesZerosRightOf_of_explicit_formula_converse_power
      hbridge)
    hzero

/-- Conditional bridge from a general `ψ` power-saving error to a zero-free
vertical line at the same real part. -/
theorem no_zeros_on_vertical_line_of_psi_power_error_bridge
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hbridge : PsiPowerErrorBelowLineExcludesZerosRightOf β)
    (herror : PsiPowerErrorBelowLine β) :
    NoZerosOnVerticalLine β := by
  intro s hs hzero
  have hnt : RiemannHypothesis.IsNontrivialZero s := by
    refine ⟨hzero, ?_, ?_⟩
    · linarith [hs, hβ_pos]
    · linarith [hs, hβ_lt_one]
  exact hbridge herror s hnt (le_of_eq hs.symm)

/-- Same vertical-line bridge with the explicit-formula converse dependency
named directly. -/
theorem no_zeros_on_vertical_line_of_explicit_formula_converse_power
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hbridge : ExplicitFormulaConversePowerTarget β)
    (herror : PsiPowerErrorBelowLine β) :
    NoZerosOnVerticalLine β :=
  no_zeros_on_vertical_line_of_psi_power_error_bridge hβ_pos hβ_lt_one hbridge herror

/-- Reflected-line version of the `ψ` power-saving bridge: if a power saving
below `β` excludes zeros on or to the right of `Re(s)=β`, then it excludes zeros
on the reflected line `Re(s)=1-β`. -/
theorem no_zeros_on_reflected_line_of_psi_power_error_bridge
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hbridge : PsiPowerErrorBelowLineExcludesZerosRightOf β)
    (herror : PsiPowerErrorBelowLine β) :
    NoZerosOnVerticalLine (1 - β) := by
  intro s hs hzero
  have hnt : RiemannHypothesis.IsNontrivialZero s := by
    refine ⟨hzero, ?_, ?_⟩
    · linarith [hs, hβ_lt_one]
    · linarith [hs, hβ_pos]
  have hsym : RiemannHypothesis.IsNontrivialZero (1 - s) :=
    nontrivial_zero_symmetric' hnt
  have hre : (1 - s).re = β := by
    have hcalc : (1 : ℝ) - (1 - β) = β := by ring
    simp [Complex.sub_re, hs, hcalc]
  exact hbridge herror (1 - s) hsym (le_of_eq hre.symm)

/-- Reflected-line bridge with the explicit-formula converse dependency named
directly. -/
theorem no_zeros_on_reflected_line_of_explicit_formula_converse_power
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hbridge : ExplicitFormulaConversePowerTarget β)
    (herror : PsiPowerErrorBelowLine β) :
    NoZerosOnVerticalLine (1 - β) :=
  no_zeros_on_reflected_line_of_psi_power_error_bridge
    hβ_pos hβ_lt_one hbridge herror

/-- Existence-form version of `no_zeros_on_vertical_line_of_psi_power_error_bridge`:
the same conditional `ψ`-error route excludes nontrivial zeros on `Re(s)=β`. -/
theorem not_exists_nontrivial_zero_on_line_of_psi_power_error_bridge
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hbridge : PsiPowerErrorBelowLineExcludesZerosRightOf β)
    (herror : PsiPowerErrorBelowLine β) :
    ¬ ∃ s : ℂ, RiemannHypothesis.IsNontrivialZero s ∧ s.re = β :=
  not_exists_nontrivial_zero_on_line_of_no_zeros_on_vertical_line
    (no_zeros_on_vertical_line_of_psi_power_error_bridge
      hβ_pos hβ_lt_one hbridge herror)

/-- Reflected-line existence-form version of the conditional `ψ`-error route:
the same input excludes nontrivial zeros on `Re(s)=1-β`. -/
theorem not_exists_nontrivial_zero_on_reflected_line_of_psi_power_error_bridge
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hbridge : PsiPowerErrorBelowLineExcludesZerosRightOf β)
    (herror : PsiPowerErrorBelowLine β) :
    ¬ ∃ s : ℂ, RiemannHypothesis.IsNontrivialZero s ∧ s.re = 1 - β :=
  not_exists_nontrivial_zero_on_line_of_no_zeros_on_vertical_line
    (no_zeros_on_reflected_line_of_psi_power_error_bridge
      hβ_pos hβ_lt_one hbridge herror)

/-- Direct power-saving version of the general `ψ`-error bridge: an
`O(x^(β-delta))` input feeds the below-`β` zero-exclusion route and excludes
zeta zeros on `Re(s)=β`. -/
theorem no_zeros_on_vertical_line_of_psi_power_error_bound_sub_delta_bridge
    {β delta : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hdelta_pos : 0 < delta) (hθ_nonneg : 0 ≤ β - delta)
    (hbridge : PsiPowerErrorBelowLineExcludesZerosRightOf β)
    (herror : PsiPowerErrorBound (β - delta)) :
    NoZerosOnVerticalLine β :=
  no_zeros_on_vertical_line_of_psi_power_error_bridge
    hβ_pos hβ_lt_one hbridge
    (psiPowerErrorBelowLine_of_power_saving hdelta_pos hθ_nonneg herror)

/-- Reflected-line power-saving version of the general `ψ`-error bridge. -/
theorem no_zeros_on_reflected_line_of_psi_power_error_bound_sub_delta_bridge
    {β delta : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hdelta_pos : 0 < delta) (hθ_nonneg : 0 ≤ β - delta)
    (hbridge : PsiPowerErrorBelowLineExcludesZerosRightOf β)
    (herror : PsiPowerErrorBound (β - delta)) :
    NoZerosOnVerticalLine (1 - β) :=
  no_zeros_on_reflected_line_of_psi_power_error_bridge
    hβ_pos hβ_lt_one hbridge
    (psiPowerErrorBelowLine_of_power_saving hdelta_pos hθ_nonneg herror)

/-- Direct power-saving version with the explicit-formula converse route
dependency named directly. -/
theorem no_zeros_on_vertical_line_of_explicit_formula_converse_power_bound_sub_delta
    {β delta : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hdelta_pos : 0 < delta) (hθ_nonneg : 0 ≤ β - delta)
    (hbridge : ExplicitFormulaConversePowerTarget β)
    (herror : PsiPowerErrorBound (β - delta)) :
    NoZerosOnVerticalLine β :=
  no_zeros_on_vertical_line_of_psi_power_error_bound_sub_delta_bridge
    hβ_pos hβ_lt_one hdelta_pos hθ_nonneg
    (psiPowerErrorBelowLineExcludesZerosRightOf_of_explicit_formula_converse_power
      hbridge)
    herror

/-- Reflected-line power-saving version with the explicit-formula converse
route dependency named directly. -/
theorem no_zeros_on_reflected_line_of_explicit_formula_converse_power_bound_sub_delta
    {β delta : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hdelta_pos : 0 < delta) (hθ_nonneg : 0 ≤ β - delta)
    (hbridge : ExplicitFormulaConversePowerTarget β)
    (herror : PsiPowerErrorBound (β - delta)) :
    NoZerosOnVerticalLine (1 - β) :=
  no_zeros_on_reflected_line_of_psi_power_error_bound_sub_delta_bridge
    hβ_pos hβ_lt_one hdelta_pos hθ_nonneg
    (psiPowerErrorBelowLineExcludesZerosRightOf_of_explicit_formula_converse_power
      hbridge)
    herror

/-- Existence-form direct power-saving bridge with the explicit-formula
converse route dependency named directly. -/
theorem not_exists_nontrivial_zero_on_line_of_explicit_formula_converse_power_bound_sub_delta
    {β delta : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hdelta_pos : 0 < delta) (hθ_nonneg : 0 ≤ β - delta)
    (hbridge : ExplicitFormulaConversePowerTarget β)
    (herror : PsiPowerErrorBound (β - delta)) :
    ¬ ∃ s : ℂ, RiemannHypothesis.IsNontrivialZero s ∧ s.re = β :=
  not_exists_nontrivial_zero_on_line_of_no_zeros_on_vertical_line
    (no_zeros_on_vertical_line_of_explicit_formula_converse_power_bound_sub_delta
      hβ_pos hβ_lt_one hdelta_pos hθ_nonneg hbridge herror)

/-- Reflected-line existence-form direct power-saving bridge with the
explicit-formula converse route dependency named directly. -/
theorem not_exists_nontrivial_zero_on_reflected_line_of_explicit_formula_converse_power_bound_sub_delta
    {β delta : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hdelta_pos : 0 < delta) (hθ_nonneg : 0 ≤ β - delta)
    (hbridge : ExplicitFormulaConversePowerTarget β)
    (herror : PsiPowerErrorBound (β - delta)) :
    ¬ ∃ s : ℂ, RiemannHypothesis.IsNontrivialZero s ∧ s.re = 1 - β :=
  not_exists_nontrivial_zero_on_line_of_no_zeros_on_vertical_line
    (no_zeros_on_reflected_line_of_explicit_formula_converse_power_bound_sub_delta
      hβ_pos hβ_lt_one hdelta_pos hθ_nonneg hbridge herror)

/-- If a power saving below a smaller boundary `β` is available, it can feed
the general `ψ`-error zero-exclusion interface at any larger boundary `γ`. -/
theorem no_zeros_on_vertical_line_of_psi_power_error_bridge_mono_error
    {β γ : ℝ} (hβγ : β ≤ γ) (hγ_pos : 0 < γ) (hγ_lt_one : γ < 1)
    (hbridge : PsiPowerErrorBelowLineExcludesZerosRightOf γ)
    (herror : PsiPowerErrorBelowLine β) :
    NoZerosOnVerticalLine γ :=
  no_zeros_on_vertical_line_of_psi_power_error_bridge
    hγ_pos hγ_lt_one hbridge
    (psiPowerErrorBelowLine_mono hβγ herror)

/-- Reflected-line version of
`no_zeros_on_vertical_line_of_psi_power_error_bridge_mono_error`. -/
theorem no_zeros_on_reflected_line_of_psi_power_error_bridge_mono_error
    {β γ : ℝ} (hβγ : β ≤ γ) (hγ_pos : 0 < γ) (hγ_lt_one : γ < 1)
    (hbridge : PsiPowerErrorBelowLineExcludesZerosRightOf γ)
    (herror : PsiPowerErrorBelowLine β) :
    NoZerosOnVerticalLine (1 - γ) :=
  no_zeros_on_reflected_line_of_psi_power_error_bridge
    hγ_pos hγ_lt_one hbridge
    (psiPowerErrorBelowLine_mono hβγ herror)

/-- A concrete `θ < 2/3` `ψ`-error input can feed the general
zero-exclusion route at any larger boundary `γ >= 2/3`. -/
theorem no_zeros_on_vertical_line_of_psi_power_error_below_two_thirds_mono_bridge
    {γ : ℝ} (hγ_two_thirds : (2 / 3 : ℝ) ≤ γ) (hγ_lt_one : γ < 1)
    (hbridge : PsiPowerErrorBelowLineExcludesZerosRightOf γ)
    (herror : PsiPowerErrorBelowTwoThirds) :
    NoZerosOnVerticalLine γ :=
  no_zeros_on_vertical_line_of_psi_power_error_bridge_mono_error
    hγ_two_thirds
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2 / 3) hγ_two_thirds)
    hγ_lt_one hbridge
    (psiPowerErrorBelowLine_two_thirds_of_below_two_thirds herror)

/-- Reflected-line version of
`no_zeros_on_vertical_line_of_psi_power_error_below_two_thirds_mono_bridge`. -/
theorem no_zeros_on_reflected_line_of_psi_power_error_below_two_thirds_mono_bridge
    {γ : ℝ} (hγ_two_thirds : (2 / 3 : ℝ) ≤ γ) (hγ_lt_one : γ < 1)
    (hbridge : PsiPowerErrorBelowLineExcludesZerosRightOf γ)
    (herror : PsiPowerErrorBelowTwoThirds) :
    NoZerosOnVerticalLine (1 - γ) :=
  no_zeros_on_reflected_line_of_psi_power_error_bridge_mono_error
    hγ_two_thirds
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2 / 3) hγ_two_thirds)
    hγ_lt_one hbridge
    (psiPowerErrorBelowLine_two_thirds_of_below_two_thirds herror)

/-- If a power saving below a smaller boundary `β` is available, it can feed an
explicit-formula converse target at any larger boundary `γ`. -/
theorem no_zeros_on_vertical_line_of_explicit_formula_converse_power_mono_error
    {β γ : ℝ} (hβγ : β ≤ γ) (hγ_pos : 0 < γ) (hγ_lt_one : γ < 1)
    (hbridge : ExplicitFormulaConversePowerTarget γ)
    (herror : PsiPowerErrorBelowLine β) :
    NoZerosOnVerticalLine γ :=
  no_zeros_on_vertical_line_of_explicit_formula_converse_power
    hγ_pos hγ_lt_one hbridge
    (psiPowerErrorBelowLine_mono hβγ herror)

/-- Reflected-line version of
`no_zeros_on_vertical_line_of_explicit_formula_converse_power_mono_error`. -/
theorem no_zeros_on_reflected_line_of_explicit_formula_converse_power_mono_error
    {β γ : ℝ} (hβγ : β ≤ γ) (hγ_pos : 0 < γ) (hγ_lt_one : γ < 1)
    (hbridge : ExplicitFormulaConversePowerTarget γ)
    (herror : PsiPowerErrorBelowLine β) :
    NoZerosOnVerticalLine (1 - γ) :=
  no_zeros_on_reflected_line_of_explicit_formula_converse_power
    hγ_pos hγ_lt_one hbridge
    (psiPowerErrorBelowLine_mono hβγ herror)

/-- Specialization of the general `ψ`-error bridge to the reflected
`Re(s) = 2 / 3` line, hence to `Re(s) = 1 / 3` by zero symmetry. -/
theorem no_zeros_on_one_third_of_general_psi_power_error_bridge
    (hbridge : PsiPowerErrorBelowLineExcludesZerosRightOf (2 / 3))
    (herror : PsiPowerErrorBelowLine (2 / 3)) :
    NoZerosOnVerticalLine (1 / 3) :=
  no_zeros_on_one_third_of_strong_pnt_error_bridge
    (StrongPNTError := PsiPowerErrorBelowLine (2 / 3))
    (fun herror' ρ hρ hρre => hbridge herror' ρ hρ (le_of_eq hρre.symm))
    herror

/-- Specialization of the explicit-formula converse bridge: excluding
nontrivial zeros on or to the right of `Re(s)=2/3` excludes zeta zeros on the
reflected line `Re(s)=1/3`. -/
theorem no_zeros_on_one_third_of_explicit_formula_converse_power
    (hbridge : ExplicitFormulaConversePowerTarget (2 / 3))
    (herror : PsiPowerErrorBelowLine (2 / 3)) :
    NoZerosOnVerticalLine (1 / 3) :=
  no_zeros_on_one_third_of_general_psi_power_error_bridge hbridge herror

/-- Direct `Re(s)=2/3` specialization of the explicit-formula converse bridge.
-/
theorem no_zeros_on_two_thirds_of_explicit_formula_converse_power
    (hbridge : ExplicitFormulaConversePowerTarget (2 / 3))
    (herror : PsiPowerErrorBelowLine (2 / 3)) :
    NoZerosOnVerticalLine (2 / 3) :=
  no_zeros_on_vertical_line_of_explicit_formula_converse_power
    (β := 2 / 3) (by norm_num) (by norm_num) hbridge herror

/-- Concrete `ψ`-error version of the `Re(s)=1/3` explicit-formula converse
bridge. -/
theorem no_zeros_on_one_third_of_explicit_formula_converse_power_below_two_thirds
    (hbridge : ExplicitFormulaConversePowerTarget (2 / 3))
    (herror : PsiPowerErrorBelowTwoThirds) :
    NoZerosOnVerticalLine (1 / 3) :=
  no_zeros_on_one_third_of_explicit_formula_converse_power hbridge
    (psiPowerErrorBelowLine_two_thirds_of_below_two_thirds herror)

/-- Concrete `ψ`-error version of the `Re(s)=2/3` explicit-formula converse
bridge. -/
theorem no_zeros_on_two_thirds_of_explicit_formula_converse_power_below_two_thirds
    (hbridge : ExplicitFormulaConversePowerTarget (2 / 3))
    (herror : PsiPowerErrorBelowTwoThirds) :
    NoZerosOnVerticalLine (2 / 3) :=
  no_zeros_on_two_thirds_of_explicit_formula_converse_power hbridge
    (psiPowerErrorBelowLine_two_thirds_of_below_two_thirds herror)

/-- Conditional `O(x^(2/3-δ))` bridge to zero-freeness on `Re(s)=1/3`,
assuming the explicit-formula converse route at `2/3`. -/
theorem no_zeros_on_one_third_of_explicit_formula_converse_power_saving
    {delta : ℝ} (hdelta_pos : 0 < delta) (hdelta_le : delta ≤ (2 / 3 : ℝ))
    (hbridge : ExplicitFormulaConversePowerTarget (2 / 3))
    (herror : PsiPowerErrorBound ((2 / 3 : ℝ) - delta)) :
    NoZerosOnVerticalLine (1 / 3) :=
  no_zeros_on_one_third_of_explicit_formula_converse_power_below_two_thirds
    hbridge
    (psiPowerErrorBelowTwoThirds_of_power_saving hdelta_pos hdelta_le herror)

/-- Conditional `O(x^(2/3-δ))` bridge to zero-freeness on `Re(s)=2/3`,
assuming the explicit-formula converse route at `2/3`. -/
theorem no_zeros_on_two_thirds_of_explicit_formula_converse_power_saving
    {delta : ℝ} (hdelta_pos : 0 < delta) (hdelta_le : delta ≤ (2 / 3 : ℝ))
    (hbridge : ExplicitFormulaConversePowerTarget (2 / 3))
    (herror : PsiPowerErrorBound ((2 / 3 : ℝ) - delta)) :
    NoZerosOnVerticalLine (2 / 3) :=
  no_zeros_on_two_thirds_of_explicit_formula_converse_power_below_two_thirds
    hbridge
    (psiPowerErrorBelowTwoThirds_of_power_saving hdelta_pos hdelta_le herror)

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

/-- Critical-line zeta zeros are finite in every bounded height interval.

This packages `finite_nontrivial_zeros_bounded_height` in the real-height
interface used by the Hardy sign-change targets. -/
theorem critical_line_zeta_zeros_bounded_height_finite (B : ℝ) :
    Set.Finite
      {t : ℝ | |t| ≤ B ∧ riemannZeta ((0.5 : ℂ) + I * t) = 0} := by
  classical
  let linePoint : ℝ → ℂ := fun t => (0.5 : ℂ) + I * t
  let realZeros : Set ℝ :=
    {t : ℝ | |t| ≤ B ∧ riemannZeta (linePoint t) = 0}
  have hcomplex_fin :
      (linePoint '' realZeros).Finite := by
    refine (finite_nontrivial_zeros_bounded_height B).subset ?_
    intro s hs
    rcases hs with ⟨t, ht, rfl⟩
    refine ⟨?_, ?_⟩
    · refine ⟨ht.2, ?_, ?_⟩
      · norm_num [linePoint]
      · norm_num [linePoint]
    · have him : (linePoint t).im = t := by
        norm_num [linePoint]
      simpa [him] using ht.1
  have hinj : Set.InjOn linePoint realZeros := by
    intro t₁ _ t₂ _ h_eq
    have him := congr_arg Complex.im h_eq
    simp [linePoint] at him
    exact him
  have hreal_fin : realZeros.Finite :=
    Set.Finite.of_finite_image hcomplex_fin hinj
  simpa [realZeros, linePoint] using hreal_fin

/-- Hardy `Z` zeros are finite in every bounded height interval. -/
theorem hardyZ_zeros_bounded_height_finite (B : ℝ) :
    Set.Finite {t : ℝ | |t| ≤ B ∧ HardyTheorem.hardyZ t = 0} := by
  refine (critical_line_zeta_zeros_bounded_height_finite B).subset ?_
  intro t ht
  exact ⟨ht.1, (HardyTheorem.hardyZ_zero_iff_zeta_zero t).mp ht.2⟩

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

/-- Unconditional Hardy-Z absolute-height form of Hardy's infinite-zero target.

The bounded-strip finiteness hypothesis required by the Hardy-only file is
discharged here from the zeta local-finiteness theorem. -/
theorem hardy_theorem_target_iff_hardyZ_abs_unbounded :
    HardyTheorem.hardy_theorem_target ↔
      ∀ T : ℝ, ∃ t : ℝ, T ≤ |t| ∧ HardyTheorem.hardyZ t = 0 :=
  HardyTheorem.hardy_theorem_target_iff_hardyZ_abs_unbounded_of_hardyZ_bounded_strips
    hardyZ_zeros_bounded_height_finite

/-- Unconditional Hardy-Z positive-height form of Hardy's infinite-zero target. -/
theorem hardy_theorem_target_iff_hardyZ_unbounded :
    HardyTheorem.hardy_theorem_target ↔
      ∀ T : ℝ, ∃ t : ℝ, T ≤ t ∧ HardyTheorem.hardyZ t = 0 :=
  Iff.trans hardy_theorem_target_iff_unbounded
    HardyTheorem.hardy_zeros_unbounded_target_iff_hardyZ_unbounded

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

theorem rh_iff_optimal_error_iff_mathlib :
    rh_iff_optimal_error ↔
      (_root_.RiemannHypothesis ↔ RH_PrimeCountingLiErrorBound) := by
  constructor
  · intro h
    constructor
    · intro hRH
      exact h.mp (rh_statement_iff_mathlib.mp hRH)
    · intro herror
      exact rh_statement_iff_mathlib.mpr (h.mpr herror)
  · intro h
    constructor
    · intro hRH
      exact h.mp (rh_statement_iff_mathlib.mpr hRH)
    · intro herror
      exact rh_statement_iff_mathlib.mp (h.mpr herror)

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

/-- Mathlib-facing pointwise textbook form of the RH/error equivalence target. -/
theorem rh_iff_optimal_error_iff_mathlib_pointwise :
    rh_iff_optimal_error ↔
      (_root_.RiemannHypothesis ↔ RH_ErrorBound) := by
  constructor
  · intro h
    exact ⟨RH_ErrorBound_of_mathlib_RH_of_rh_iff_optimal_error h,
      mathlib_RH_of_rh_iff_pointwise_error h⟩
  · intro h
    exact rh_iff_optimal_error_of_mathlib_pointwise_implications h.mp h.mpr

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

/-- Finset of distinct nontrivial zeros up to height `T`.

This uses the already-proved local finiteness theorem.  Exact contour formulas
must additionally weight each member by its analytic order. -/
noncomputable def nontrivialZerosFinset (T : ℝ) : Finset ℂ :=
  (finite_nontrivial_zeros_bounded_height T).toFinset

/-- Legacy unweighted height-truncated nontrivial-zero contribution.

This is retained for compatibility with the pre-contour helper API.  It is not
the zero sum used by the exact explicit-formula target. -/
noncomputable def finiteNontrivialZeroSum (x T : ℝ) : ℂ :=
  ∑ ρ ∈ nontrivialZerosFinset T, (x : ℂ) ^ ρ / ρ

/-- Height-truncated nontrivial-zero contribution, counted with analytic
multiplicity as required by the residue theorem. -/
noncomputable def finiteNontrivialZeroSumWithMultiplicity (x T : ℝ) : ℂ :=
  ∑ ρ ∈ nontrivialZerosFinset T,
    (analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ

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

lemma nontrivialZerosFinset_subset {T U : ℝ} (hTU : T ≤ U) :
    nontrivialZerosFinset T ⊆ nontrivialZerosFinset U := by
  intro ρ hρ
  exact nontrivialZerosFinset_mono hTU hρ

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

/-! The next two lemmas specialize the abstract zero-pair skeleton to the
finite family of nontrivial zeta zeros used by the explicit-formula
infrastructure below. -/

/-- Finite nontrivial-zero contributions are nonnegative when paired by the
zeta functional-equation symmetry `ρ ↦ 1 - ρ`. -/
lemma nontrivialZerosFinset_pair_sum_nonnegative
    (T : ℝ) (F : ℂ → ℂ)
    (hF : ZeroPairContributionNonnegative F 1) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset T, ((F ρ).re + (F (1 - ρ)).re) :=
  Finset.sum_nonneg (fun ρ _hρ => hF ρ)

/-- Reindex a real-valued finite zero sum by the zeta zero symmetry
`ρ ↦ 1 - ρ`. -/
lemma sum_nontrivialZerosFinset_pair_re (T : ℝ) (F : ℂ → ℂ) :
    (∑ ρ ∈ nontrivialZerosFinset T, (F (1 - ρ)).re) =
      ∑ ρ ∈ nontrivialZerosFinset T, (F ρ).re := by
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

/-- A paired finite zero contribution equals twice the unpaired real-part sum,
after reindexing by `ρ ↦ 1 - ρ`. -/
lemma nontrivialZerosFinset_pair_contribution_eq_two_sum_re
    (T : ℝ) (F : ℂ → ℂ) :
    (∑ ρ ∈ nontrivialZerosFinset T, ((F ρ).re + (F (1 - ρ)).re)) =
      2 * ∑ ρ ∈ nontrivialZerosFinset T, (F ρ).re := by
  rw [Finset.sum_add_distrib, sum_nontrivialZerosFinset_pair_re]
  ring

/-- A global pair-nonnegativity condition also makes the unpaired real-part sum
over height-truncated nontrivial zeros nonnegative. -/
lemma nontrivialZerosFinset_sum_re_nonnegative_of_pair_contribution_nonnegative
    (T : ℝ) (F : ℂ → ℂ)
    (hF : ZeroPairContributionNonnegative F 1) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset T, (F ρ).re := by
  have hpair := nontrivialZerosFinset_pair_sum_nonnegative T F hF
  rw [nontrivialZerosFinset_pair_contribution_eq_two_sum_re] at hpair
  nlinarith

/-- The newly included nontrivial zeros between two height cutoffs are closed
under the zeta symmetry `ρ ↦ 1 - ρ`. -/
lemma one_sub_mem_nontrivialZerosFinset_sdiff {ρ : ℂ} {T U : ℝ}
    (hρ : ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T) :
    1 - ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T := by
  simp only [Finset.mem_sdiff] at hρ ⊢
  exact ⟨one_sub_mem_nontrivialZerosFinset hρ.1, by
    intro hT
    exact hρ.2 ((one_sub_mem_nontrivialZerosFinset_iff).mp hT)⟩

/-- Reindex a real-valued new-zero finite sum by the zeta zero symmetry
`ρ ↦ 1 - ρ`. -/
lemma sum_nontrivialZerosFinset_sdiff_pair_re (T U : ℝ) (F : ℂ → ℂ) :
    (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        (F (1 - ρ)).re) =
      ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T, (F ρ).re := by
  classical
  refine Finset.sum_nbij' (fun ρ : ℂ => 1 - ρ) (fun ρ : ℂ => 1 - ρ)
    ?_ ?_ ?_ ?_ ?_
  · intro ρ hρ
    exact one_sub_mem_nontrivialZerosFinset_sdiff hρ
  · intro ρ hρ
    exact one_sub_mem_nontrivialZerosFinset_sdiff hρ
  · intro ρ _hρ
    ring
  · intro ρ _hρ
    ring
  · intro ρ _hρ
    rfl

/-- A paired contribution over newly included nontrivial zeros equals twice the
unpaired real-part sum. -/
lemma nontrivialZerosFinset_sdiff_pair_contribution_eq_two_sum_re
    (T U : ℝ) (F : ℂ → ℂ) :
    (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
      ((F ρ).re + (F (1 - ρ)).re)) =
      2 * ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        (F ρ).re := by
  rw [Finset.sum_add_distrib, sum_nontrivialZerosFinset_sdiff_pair_re]
  ring

/-- A global pair-nonnegativity condition makes the unpaired real-part sum over
newly included nontrivial zeros nonnegative. -/
lemma nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_pair_contribution_nonnegative
    (T U : ℝ) (F : ℂ → ℂ)
    (hF : ZeroPairContributionNonnegative F 1) :
    0 ≤
      ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T, (F ρ).re := by
  have hpair :
      0 ≤ ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        ((F ρ).re + (F (1 - ρ)).re) :=
    Finset.sum_nonneg (fun ρ _hρ => hF ρ)
  rw [nontrivialZerosFinset_sdiff_pair_contribution_eq_two_sum_re] at hpair
  nlinarith

/-- Strip-local Laplace-pair positivity gives paired-sum nonnegativity over newly
included nontrivial zeros, for any chosen real pairing center.  The caller only
has to supply the strip membership proof for the new-zero block. -/
lemma nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_laplace_pair_positive
    (T U : ℝ) (F : ℂ → ℂ) (center : ℝ)
    (hF : LaplacePairPositive F center)
    (hstrip : ∀ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
      0 ≤ ρ.re ∧ ρ.re ≤ center) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
      ((F ρ).re + (F ((center : ℂ) - ρ)).re) :=
  finite_zero_sum_nonnegative_of_laplace_pair_positive
    (nontrivialZerosFinset U \ nontrivialZerosFinset T) F center hF hstrip

/-- Average paired contribution over newly included nontrivial zeros is
nonnegative from strip-local Laplace-pair positivity.  This does not reindex to
an unpaired sum unless the pairing center is known to preserve the zero set. -/
lemma nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_laplace_pair_positive
    (T U : ℝ) (F : ℂ → ℂ) (center : ℝ)
    (hF : LaplacePairPositive F center)
    (hstrip : ∀ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
      0 ≤ ρ.re ∧ ρ.re ≤ center) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        ((F ρ).re + (F ((center : ℂ) - ρ)).re)) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) :=
  div_nonneg
    (nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_laplace_pair_positive
      T U F center hF hstrip)
    (Nat.cast_nonneg _)

/-- Center-one Laplace-pair positivity gives paired-sum nonnegativity over the
newly included nontrivial zeros between two height cutoffs. -/
lemma nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_laplace_pair_positive_one
    (T U : ℝ) (F : ℂ → ℂ)
    (hF : LaplacePairPositive F 1) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
      ((F ρ).re + (F (1 - ρ)).re) :=
  nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_laplace_pair_positive
    T U F 1 hF (by
      intro ρ hρ
      have hU : ρ ∈ nontrivialZerosFinset U := (Finset.mem_sdiff.mp hρ).1
      rcases mem_nontrivialZerosFinset.mp hU with ⟨hzero, _hheight⟩
      exact ⟨le_of_lt hzero.2.1, le_of_lt hzero.2.2⟩)

/-- Average paired contribution over newly included nontrivial zeros is
nonnegative from center-one Laplace-pair positivity.  This packages the common
critical-strip center used by Stechkin/Heath-Brown pair detectors. -/
lemma nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_laplace_pair_positive_one
    (T U : ℝ) (F : ℂ → ℂ)
    (hF : LaplacePairPositive F 1) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        ((F ρ).re + (F (1 - ρ)).re)) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) :=
  div_nonneg
    (nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_laplace_pair_positive_one
      T U F hF)
    (Nat.cast_nonneg _)

/-- Center-one Laplace-pair positivity makes the unpaired real-part sum over
newly included nontrivial zeros nonnegative. -/
lemma nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_laplace_pair_positive_one
    (T U : ℝ) (F : ℂ → ℂ)
    (hF : LaplacePairPositive F 1) :
    0 ≤
      ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T, (F ρ).re := by
  have hpair :=
    nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_laplace_pair_positive_one
      T U F hF
  rw [nontrivialZerosFinset_sdiff_pair_contribution_eq_two_sum_re] at hpair
  nlinarith

/-- Average real-part contribution over newly included nontrivial zeros is
nonnegative under the global center-one pair-contribution condition.  If the
new-zero finset is empty, Lean's total division convention makes the displayed
average equal to `0`. -/
lemma nontrivialZerosFinset_sdiff_average_re_nonnegative_of_pair_contribution_nonnegative
    (T U : ℝ) (F : ℂ → ℂ)
    (hF : ZeroPairContributionNonnegative F 1) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T, (F ρ).re) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) := by
  exact div_nonneg
    (nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_pair_contribution_nonnegative
      T U F hF)
    (Nat.cast_nonneg _)

/-- Average real-part contribution over newly included nontrivial zeros is
nonnegative under center-one Laplace-pair positivity. -/
lemma nontrivialZerosFinset_sdiff_average_re_nonnegative_of_laplace_pair_positive_one
    (T U : ℝ) (F : ℂ → ℂ)
    (hF : LaplacePairPositive F 1) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T, (F ρ).re) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) := by
  exact div_nonneg
    (nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_laplace_pair_positive_one
      T U F hF)
    (Nat.cast_nonneg _)

/-- Pointwise real-part nonnegativity on the critical strip makes the unpaired
real-part sum over newly included nontrivial zeros nonnegative. -/
lemma nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_re_nonnegative_on_critical_strip
    (T U : ℝ) (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 0 ≤ (F z).re) :
    0 ≤
      ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T, (F ρ).re :=
  nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_laplace_pair_positive_one
    T U F (laplacePairPositive_one_of_re_nonnegative_on_critical_strip hF)

/-- Pointwise real-part nonnegativity on the critical strip makes the average
real-part contribution over newly included nontrivial zeros nonnegative. -/
lemma nontrivialZerosFinset_sdiff_average_re_nonnegative_of_re_nonnegative_on_critical_strip
    (T U : ℝ) (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 0 ≤ (F z).re) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T, (F ρ).re) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_sdiff_average_re_nonnegative_of_laplace_pair_positive_one
    T U F (laplacePairPositive_one_of_re_nonnegative_on_critical_strip hF)

/-- Finite nonnegative weighted kernel combinations with center-one
pair-positive summands give a nonnegative real-part sum over newly included
nontrivial zeros. -/
lemma nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_weightedKernelCombo
    (T U : ℝ) (K : Finset ℕ) (w : ℕ → ℝ) (F : ℕ → ℂ → ℂ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hF : ∀ k ∈ K, LaplacePairPositive (F k) 1) :
    0 ≤
      ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        (weightedKernelCombo K w F ρ).re :=
  nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_laplace_pair_positive_one
    T U (weightedKernelCombo K w F)
    (laplacePairPositive_one_weightedKernelCombo hw hF)

/-- Finite nonnegative weighted kernel combinations with center-one
pair-positive summands give a nonnegative average real-part contribution over
newly included nontrivial zeros. -/
lemma nontrivialZerosFinset_sdiff_average_re_nonnegative_of_weightedKernelCombo
    (T U : ℝ) (K : Finset ℕ) (w : ℕ → ℝ) (F : ℕ → ℂ → ℂ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hF : ∀ k ∈ K, LaplacePairPositive (F k) 1) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        (weightedKernelCombo K w F ρ).re) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_sdiff_average_re_nonnegative_of_laplace_pair_positive_one
    T U (weightedKernelCombo K w F)
    (laplacePairPositive_one_weightedKernelCombo hw hF)

/-- Finite nonnegative weighted kernel combinations with center-one
pair-positive summands give a nonnegative paired sum over newly included
nontrivial zeros. -/
lemma nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_weightedKernelCombo
    (T U : ℝ) (K : Finset ℕ) (w : ℕ → ℝ) (F : ℕ → ℂ → ℂ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hF : ∀ k ∈ K, LaplacePairPositive (F k) 1) :
    0 ≤
      ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        ((weightedKernelCombo K w F ρ).re +
          (weightedKernelCombo K w F (1 - ρ)).re) :=
  nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_laplace_pair_positive_one
    T U (weightedKernelCombo K w F)
    (laplacePairPositive_one_weightedKernelCombo hw hF)

/-- Finite nonnegative weighted kernel combinations with center-one
pair-positive summands give a nonnegative paired average over newly included
nontrivial zeros. -/
lemma nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_weightedKernelCombo
    (T U : ℝ) (K : Finset ℕ) (w : ℕ → ℝ) (F : ℕ → ℂ → ℂ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hF : ∀ k ∈ K, LaplacePairPositive (F k) 1) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        ((weightedKernelCombo K w F ρ).re +
          (weightedKernelCombo K w F (1 - ρ)).re)) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_laplace_pair_positive_one
    T U (weightedKernelCombo K w F)
    (laplacePairPositive_one_weightedKernelCombo hw hF)

/-- The resolvent/Laplace prototype gives a nonnegative real-part sum over
newly included nontrivial zeros. -/
lemma nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_resolventLaplaceKernel
    (T U a : ℝ) (ha : 0 ≤ a) :
    0 ≤
      ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        (resolventLaplaceKernel a ρ).re :=
  nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_re_nonnegative_on_critical_strip
    T U (resolventLaplaceKernel a)
    (resolventLaplaceKernel_re_nonnegative_on_critical_strip ha)

/-- The resolvent/Laplace prototype gives a nonnegative average real-part
contribution over newly included nontrivial zeros. -/
lemma nontrivialZerosFinset_sdiff_average_re_nonnegative_of_resolventLaplaceKernel
    (T U a : ℝ) (ha : 0 ≤ a) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        (resolventLaplaceKernel a ρ).re) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_sdiff_average_re_nonnegative_of_re_nonnegative_on_critical_strip
    T U (resolventLaplaceKernel a)
    (resolventLaplaceKernel_re_nonnegative_on_critical_strip ha)

/-- The resolvent/Laplace prototype gives a nonnegative paired sum over newly
included nontrivial zeros. -/
lemma nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_resolventLaplaceKernel
    (T U a : ℝ) (ha : 0 ≤ a) :
    0 ≤
      ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        ((resolventLaplaceKernel a ρ).re +
          (resolventLaplaceKernel a (1 - ρ)).re) :=
  nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_laplace_pair_positive_one
    T U (resolventLaplaceKernel a)
    (laplacePairPositive_one_resolventLaplaceKernel ha)

/-- The resolvent/Laplace prototype gives a nonnegative paired average over
newly included nontrivial zeros. -/
lemma nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_resolventLaplaceKernel
    (T U a : ℝ) (ha : 0 ≤ a) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        ((resolventLaplaceKernel a ρ).re +
          (resolventLaplaceKernel a (1 - ρ)).re)) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_laplace_pair_positive_one
    T U (resolventLaplaceKernel a)
    (laplacePairPositive_one_resolventLaplaceKernel ha)

/-- The center-one symmetric resolvent/Laplace kernel gives a nonnegative
real-part sum over newly included nontrivial zeros. -/
lemma nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_symmetricResolventLaplaceKernel
    (T U a : ℝ) (ha : 0 ≤ a) :
    0 ≤
      ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        (symmetricResolventLaplaceKernel a 1 ρ).re :=
  nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_re_nonnegative_on_critical_strip
    T U (symmetricResolventLaplaceKernel a 1)
    (symmetricResolventLaplaceKernel_re_nonnegative_on_strip ha)

/-- The center-one symmetric resolvent/Laplace kernel gives a nonnegative
average real-part contribution over newly included nontrivial zeros. -/
lemma nontrivialZerosFinset_sdiff_average_re_nonnegative_of_symmetricResolventLaplaceKernel
    (T U a : ℝ) (ha : 0 ≤ a) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        (symmetricResolventLaplaceKernel a 1 ρ).re) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_sdiff_average_re_nonnegative_of_re_nonnegative_on_critical_strip
    T U (symmetricResolventLaplaceKernel a 1)
    (symmetricResolventLaplaceKernel_re_nonnegative_on_strip ha)

/-- The center-one symmetric resolvent/Laplace kernel gives a nonnegative
paired sum over newly included nontrivial zeros. -/
lemma nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_symmetricResolventLaplaceKernel
    (T U a : ℝ) (ha : 0 ≤ a) :
    0 ≤
      ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        ((symmetricResolventLaplaceKernel a 1 ρ).re +
          (symmetricResolventLaplaceKernel a 1 (1 - ρ)).re) :=
  nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_laplace_pair_positive_one
    T U (symmetricResolventLaplaceKernel a 1)
    (laplacePairPositive_one_symmetricResolventLaplaceKernel ha)

/-- The center-one symmetric resolvent/Laplace kernel gives a nonnegative
paired average over newly included nontrivial zeros. -/
lemma nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_symmetricResolventLaplaceKernel
    (T U a : ℝ) (ha : 0 ≤ a) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        ((symmetricResolventLaplaceKernel a 1 ρ).re +
          (symmetricResolventLaplaceKernel a 1 (1 - ρ)).re)) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_laplace_pair_positive_one
    T U (symmetricResolventLaplaceKernel a 1)
    (laplacePairPositive_one_symmetricResolventLaplaceKernel ha)

/-- The affine resolvent/Laplace prototype gives a nonnegative real-part sum
over newly included nontrivial zeros. -/
lemma nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_affineResolventLaplaceKernel
    (T U a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤
      ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        (affineResolventLaplaceKernel a b c ρ).re :=
  nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_re_nonnegative_on_critical_strip
    T U (affineResolventLaplaceKernel a b c)
    (affineResolventLaplaceKernel_re_nonnegative_on_critical_strip
      ha hb hc)

/-- The affine resolvent/Laplace prototype gives a nonnegative average
real-part contribution over newly included nontrivial zeros. -/
lemma nontrivialZerosFinset_sdiff_average_re_nonnegative_of_affineResolventLaplaceKernel
    (T U a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        (affineResolventLaplaceKernel a b c ρ).re) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_sdiff_average_re_nonnegative_of_re_nonnegative_on_critical_strip
    T U (affineResolventLaplaceKernel a b c)
    (affineResolventLaplaceKernel_re_nonnegative_on_critical_strip
      ha hb hc)

/-- The affine resolvent/Laplace prototype gives a nonnegative paired sum over
newly included nontrivial zeros. -/
lemma nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_affineResolventLaplaceKernel
    (T U a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤
      ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        ((affineResolventLaplaceKernel a b c ρ).re +
          (affineResolventLaplaceKernel a b c (1 - ρ)).re) :=
  nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_laplace_pair_positive_one
    T U (affineResolventLaplaceKernel a b c)
    (laplacePairPositive_one_affineResolventLaplaceKernel
      ha hb hc)

/-- The affine resolvent/Laplace prototype gives a nonnegative paired average
over newly included nontrivial zeros. -/
lemma nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_affineResolventLaplaceKernel
    (T U a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        ((affineResolventLaplaceKernel a b c ρ).re +
          (affineResolventLaplaceKernel a b c (1 - ρ)).re)) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_laplace_pair_positive_one
    T U (affineResolventLaplaceKernel a b c)
    (laplacePairPositive_one_affineResolventLaplaceKernel
      ha hb hc)

/-- Finite nonnegative resolvent/Laplace combinations give a nonnegative
real-part sum over newly included nontrivial zeros. -/
lemma nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_resolventLaplaceKernelCombo
    (T U : ℝ) (K : Finset ℕ) (w a : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k) :
    0 ≤
      ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        (resolventLaplaceKernelCombo K w a ρ).re :=
  nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_re_nonnegative_on_critical_strip
    T U (resolventLaplaceKernelCombo K w a)
    (resolventLaplaceKernelCombo_re_nonnegative_on_critical_strip hw ha)

/-- Finite nonnegative resolvent/Laplace combinations give a nonnegative
average real-part contribution over newly included nontrivial zeros. -/
lemma nontrivialZerosFinset_sdiff_average_re_nonnegative_of_resolventLaplaceKernelCombo
    (T U : ℝ) (K : Finset ℕ) (w a : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        (resolventLaplaceKernelCombo K w a ρ).re) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_sdiff_average_re_nonnegative_of_re_nonnegative_on_critical_strip
    T U (resolventLaplaceKernelCombo K w a)
    (resolventLaplaceKernelCombo_re_nonnegative_on_critical_strip hw ha)

/-- Finite nonnegative resolvent/Laplace combinations give a nonnegative
paired sum over newly included nontrivial zeros. -/
lemma nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_resolventLaplaceKernelCombo
    (T U : ℝ) (K : Finset ℕ) (w a : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k) :
    0 ≤
      ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        ((resolventLaplaceKernelCombo K w a ρ).re +
          (resolventLaplaceKernelCombo K w a (1 - ρ)).re) :=
  nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_laplace_pair_positive_one
    T U (resolventLaplaceKernelCombo K w a)
    (laplacePairPositive_one_resolventLaplaceKernelCombo hw ha)

/-- Finite nonnegative resolvent/Laplace combinations give a nonnegative
paired average over newly included nontrivial zeros. -/
lemma nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_resolventLaplaceKernelCombo
    (T U : ℝ) (K : Finset ℕ) (w a : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        ((resolventLaplaceKernelCombo K w a ρ).re +
          (resolventLaplaceKernelCombo K w a (1 - ρ)).re)) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_laplace_pair_positive_one
    T U (resolventLaplaceKernelCombo K w a)
    (laplacePairPositive_one_resolventLaplaceKernelCombo hw ha)

/-- Finite nonnegative combinations of center-one symmetric
resolvent/Laplace kernels give a nonnegative real-part sum over newly included
nontrivial zeros. -/
lemma nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_symmetricResolventLaplaceKernelCombo
    (T U : ℝ) (K : Finset ℕ) (w a : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k) :
    0 ≤
      ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        (symmetricResolventLaplaceKernelCombo K w a 1 ρ).re :=
  nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_re_nonnegative_on_critical_strip
    T U (symmetricResolventLaplaceKernelCombo K w a 1)
    (symmetricResolventLaplaceKernelCombo_re_nonnegative_on_strip hw ha)

/-- Finite nonnegative combinations of center-one symmetric
resolvent/Laplace kernels give a nonnegative average real-part contribution
over newly included nontrivial zeros. -/
lemma nontrivialZerosFinset_sdiff_average_re_nonnegative_of_symmetricResolventLaplaceKernelCombo
    (T U : ℝ) (K : Finset ℕ) (w a : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        (symmetricResolventLaplaceKernelCombo K w a 1 ρ).re) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_sdiff_average_re_nonnegative_of_re_nonnegative_on_critical_strip
    T U (symmetricResolventLaplaceKernelCombo K w a 1)
    (symmetricResolventLaplaceKernelCombo_re_nonnegative_on_strip hw ha)

/-- Finite nonnegative combinations of center-one symmetric
resolvent/Laplace kernels give a nonnegative paired sum over newly included
nontrivial zeros. -/
lemma nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_symmetricResolventLaplaceKernelCombo
    (T U : ℝ) (K : Finset ℕ) (w a : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k) :
    0 ≤
      ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        ((symmetricResolventLaplaceKernelCombo K w a 1 ρ).re +
          (symmetricResolventLaplaceKernelCombo K w a 1 (1 - ρ)).re) :=
  nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_laplace_pair_positive_one
    T U (symmetricResolventLaplaceKernelCombo K w a 1)
    (laplacePairPositive_one_symmetricResolventLaplaceKernelCombo hw ha)

/-- Finite nonnegative combinations of center-one symmetric
resolvent/Laplace kernels give a nonnegative paired average over newly included
nontrivial zeros. -/
lemma nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_symmetricResolventLaplaceKernelCombo
    (T U : ℝ) (K : Finset ℕ) (w a : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        ((symmetricResolventLaplaceKernelCombo K w a 1 ρ).re +
          (symmetricResolventLaplaceKernelCombo K w a 1 (1 - ρ)).re)) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_laplace_pair_positive_one
    T U (symmetricResolventLaplaceKernelCombo K w a 1)
    (laplacePairPositive_one_symmetricResolventLaplaceKernelCombo hw ha)

/-- Finite nonnegative affine resolvent/Laplace combinations give a
nonnegative real-part sum over newly included nontrivial zeros. -/
lemma nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_affineResolventLaplaceKernelCombo
    (T U : ℝ) (K : Finset ℕ) (w a b c : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k)
    (hb : ∀ k ∈ K, 0 ≤ b k) (hc : ∀ k ∈ K, 0 ≤ c k) :
    0 ≤
      ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        (affineResolventLaplaceKernelCombo K w a b c ρ).re :=
  nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_re_nonnegative_on_critical_strip
    T U (affineResolventLaplaceKernelCombo K w a b c)
    (affineResolventLaplaceKernelCombo_re_nonnegative_on_critical_strip
      hw ha hb hc)

/-- Finite nonnegative affine resolvent/Laplace combinations give a
nonnegative average real-part contribution over newly included nontrivial
zeros. -/
lemma nontrivialZerosFinset_sdiff_average_re_nonnegative_of_affineResolventLaplaceKernelCombo
    (T U : ℝ) (K : Finset ℕ) (w a b c : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k)
    (hb : ∀ k ∈ K, 0 ≤ b k) (hc : ∀ k ∈ K, 0 ≤ c k) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        (affineResolventLaplaceKernelCombo K w a b c ρ).re) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_sdiff_average_re_nonnegative_of_re_nonnegative_on_critical_strip
    T U (affineResolventLaplaceKernelCombo K w a b c)
    (affineResolventLaplaceKernelCombo_re_nonnegative_on_critical_strip
      hw ha hb hc)

/-- Finite nonnegative affine resolvent/Laplace combinations give a
nonnegative paired sum over newly included nontrivial zeros. -/
lemma nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_affineResolventLaplaceKernelCombo
    (T U : ℝ) (K : Finset ℕ) (w a b c : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k)
    (hb : ∀ k ∈ K, 0 ≤ b k) (hc : ∀ k ∈ K, 0 ≤ c k) :
    0 ≤
      ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        ((affineResolventLaplaceKernelCombo K w a b c ρ).re +
          (affineResolventLaplaceKernelCombo K w a b c (1 - ρ)).re) :=
  nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_laplace_pair_positive_one
    T U (affineResolventLaplaceKernelCombo K w a b c)
    (laplacePairPositive_one_affineResolventLaplaceKernelCombo
      hw ha hb hc)

/-- Finite nonnegative affine resolvent/Laplace combinations give a
nonnegative paired average over newly included nontrivial zeros. -/
lemma nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_affineResolventLaplaceKernelCombo
    (T U : ℝ) (K : Finset ℕ) (w a b c : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k)
    (hb : ∀ k ∈ K, 0 ≤ b k) (hc : ∀ k ∈ K, 0 ≤ c k) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        ((affineResolventLaplaceKernelCombo K w a b c ρ).re +
          (affineResolventLaplaceKernelCombo K w a b c (1 - ρ)).re)) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_laplace_pair_positive_one
    T U (affineResolventLaplaceKernelCombo K w a b c)
    (laplacePairPositive_one_affineResolventLaplaceKernelCombo
      hw ha hb hc)

/-- Specialize strip-local Stechkin/Heath-Brown pair positivity to the finite
family of nontrivial zeros up to height `T`. -/
lemma nontrivialZerosFinset_pair_sum_nonnegative_of_laplace_pair_positive
    (T : ℝ) (F : ℂ → ℂ) (center : ℝ)
    (hF : LaplacePairPositive F center)
    (hstrip : ∀ ρ ∈ nontrivialZerosFinset T, 0 ≤ ρ.re ∧ ρ.re ≤ center) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset T,
      ((F ρ).re + (F ((center : ℂ) - ρ)).re) :=
  finite_zero_sum_nonnegative_of_laplace_pair_positive
    (nontrivialZerosFinset T) F center hF hstrip

/-- Average paired contribution over height-truncated nontrivial zeros is
nonnegative from strip-local Laplace-pair positivity. -/
lemma nontrivialZerosFinset_pair_average_nonnegative_of_laplace_pair_positive
    (T : ℝ) (F : ℂ → ℂ) (center : ℝ)
    (hF : LaplacePairPositive F center)
    (hstrip : ∀ ρ ∈ nontrivialZerosFinset T, 0 ≤ ρ.re ∧ ρ.re ≤ center) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset T,
        ((F ρ).re + (F ((center : ℂ) - ρ)).re)) /
        (((nontrivialZerosFinset T).card : ℝ)) :=
  div_nonneg
    (nontrivialZerosFinset_pair_sum_nonnegative_of_laplace_pair_positive
      T F center hF hstrip)
    (Nat.cast_nonneg _)

/-- Center-one specialization of the Stechkin/Heath-Brown pair-positivity
bridge for height-truncated nontrivial zeros.  The critical-strip bounds are
discharged from membership in `nontrivialZerosFinset`. -/
lemma nontrivialZerosFinset_pair_sum_nonnegative_of_laplace_pair_positive_one
    (T : ℝ) (F : ℂ → ℂ)
    (hF : LaplacePairPositive F 1) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset T,
      ((F ρ).re + (F (1 - ρ)).re) :=
  nontrivialZerosFinset_pair_sum_nonnegative_of_laplace_pair_positive
    T F 1 hF (by
      intro ρ hρ
      rcases mem_nontrivialZerosFinset.mp hρ with ⟨hzero, _hheight⟩
      exact ⟨le_of_lt hzero.2.1, le_of_lt hzero.2.2⟩)

/-- Average paired contribution over height-truncated nontrivial zeros is
nonnegative from center-one Laplace-pair positivity. -/
lemma nontrivialZerosFinset_pair_average_nonnegative_of_laplace_pair_positive_one
    (T : ℝ) (F : ℂ → ℂ)
    (hF : LaplacePairPositive F 1) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset T,
        ((F ρ).re + (F (1 - ρ)).re)) /
        (((nontrivialZerosFinset T).card : ℝ)) :=
  div_nonneg
    (nontrivialZerosFinset_pair_sum_nonnegative_of_laplace_pair_positive_one
      T F hF)
    (Nat.cast_nonneg _)

/-- Finite nontrivial-zero paired-sum nonnegativity for a damped detector
kernel, after its Stechkin-style pair inequality has been proved on the
critical strip. -/
theorem nontrivialZerosFinset_pair_sum_nonnegative_of_dampedKernel
    (T κ : ℝ) (F G : ℂ → ℂ)
    (hpair : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      κ * ((G z).re + (G (1 - z)).re) ≤
        (F z).re + (F (1 - z)).re) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset T,
      ((dampedKernel κ F G ρ).re +
        (dampedKernel κ F G (1 - ρ)).re) :=
  nontrivialZerosFinset_pair_sum_nonnegative_of_laplace_pair_positive_one
    T (dampedKernel κ F G)
    (laplacePairPositive_one_dampedKernel_of_pair_le hpair)

/-- Finite nontrivial-zero paired-average nonnegativity for a damped detector
kernel. -/
theorem nontrivialZerosFinset_pair_average_nonnegative_of_dampedKernel
    (T κ : ℝ) (F G : ℂ → ℂ)
    (hpair : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      κ * ((G z).re + (G (1 - z)).re) ≤
        (F z).re + (F (1 - z)).re) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset T,
        ((dampedKernel κ F G ρ).re +
          (dampedKernel κ F G (1 - ρ)).re)) /
        ((nontrivialZerosFinset T).card : ℝ) :=
  nontrivialZerosFinset_pair_average_nonnegative_of_laplace_pair_positive_one
    T (dampedKernel κ F G)
    (laplacePairPositive_one_dampedKernel_of_pair_le hpair)

/-- Finite nontrivial-zero paired-sum nonnegativity for a damped detector
kernel from the pair-nonnegative dominated-kernel input shape. -/
theorem nontrivialZerosFinset_pair_sum_nonnegative_of_dampedKernel_pair_nonneg_le
    (T κ : ℝ) (F G : ℂ → ℂ) (hκ : κ ≤ 1)
    (hG_nonneg : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      0 ≤ (G z).re + (G (1 - z)).re)
    (hGF : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      (G z).re + (G (1 - z)).re ≤
        (F z).re + (F (1 - z)).re) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset T,
      ((dampedKernel κ F G ρ).re +
        (dampedKernel κ F G (1 - ρ)).re) :=
  nontrivialZerosFinset_pair_sum_nonnegative_of_laplace_pair_positive_one
    T (dampedKernel κ F G)
    (laplacePairPositive_one_dampedKernel_of_pair_nonneg_le
      hκ hG_nonneg hGF)

/-- Finite nontrivial-zero paired-average nonnegativity for a damped detector
kernel from the pair-nonnegative dominated-kernel input shape. -/
theorem nontrivialZerosFinset_pair_average_nonnegative_of_dampedKernel_pair_nonneg_le
    (T κ : ℝ) (F G : ℂ → ℂ) (hκ : κ ≤ 1)
    (hG_nonneg : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      0 ≤ (G z).re + (G (1 - z)).re)
    (hGF : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      (G z).re + (G (1 - z)).re ≤
        (F z).re + (F (1 - z)).re) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset T,
        ((dampedKernel κ F G ρ).re +
          (dampedKernel κ F G (1 - ρ)).re)) /
        ((nontrivialZerosFinset T).card : ℝ) :=
  nontrivialZerosFinset_pair_average_nonnegative_of_laplace_pair_positive_one
    T (dampedKernel κ F G)
    (laplacePairPositive_one_dampedKernel_of_pair_nonneg_le
      hκ hG_nonneg hGF)

/-- Finite nontrivial-zero unpaired real-part sum nonnegativity for a damped
detector kernel. -/
theorem nontrivialZerosFinset_sum_re_nonnegative_of_dampedKernel
    (T κ : ℝ) (F G : ℂ → ℂ)
    (hpair : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      κ * ((G z).re + (G (1 - z)).re) ≤
        (F z).re + (F (1 - z)).re) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset T, (dampedKernel κ F G ρ).re := by
  have hpaired :=
    nontrivialZerosFinset_pair_sum_nonnegative_of_dampedKernel
      T κ F G hpair
  rw [nontrivialZerosFinset_pair_contribution_eq_two_sum_re] at hpaired
  nlinarith

/-- Finite nontrivial-zero unpaired real-part average nonnegativity for a
damped detector kernel. -/
theorem nontrivialZerosFinset_average_re_nonnegative_of_dampedKernel
    (T κ : ℝ) (F G : ℂ → ℂ)
    (hpair : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      κ * ((G z).re + (G (1 - z)).re) ≤
        (F z).re + (F (1 - z)).re) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset T, (dampedKernel κ F G ρ).re) /
        ((nontrivialZerosFinset T).card : ℝ) :=
  div_nonneg
    (nontrivialZerosFinset_sum_re_nonnegative_of_dampedKernel
      T κ F G hpair)
    (Nat.cast_nonneg _)

/-- Finite nontrivial-zero unpaired real-part sum nonnegativity for a damped
detector kernel from the pair-nonnegative dominated-kernel input shape. -/
theorem nontrivialZerosFinset_sum_re_nonnegative_of_dampedKernel_pair_nonneg_le
    (T κ : ℝ) (F G : ℂ → ℂ) (hκ : κ ≤ 1)
    (hG_nonneg : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      0 ≤ (G z).re + (G (1 - z)).re)
    (hGF : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      (G z).re + (G (1 - z)).re ≤
        (F z).re + (F (1 - z)).re) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset T, (dampedKernel κ F G ρ).re := by
  have hpair :
      ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
        κ * ((G z).re + (G (1 - z)).re) ≤
          (F z).re + (F (1 - z)).re := by
    intro z hz_left hz_right
    have hG := hG_nonneg z hz_left hz_right
    have hκG :
        κ * ((G z).re + (G (1 - z)).re) ≤
          1 * ((G z).re + (G (1 - z)).re) :=
      mul_le_mul_of_nonneg_right hκ hG
    have hGF' := hGF z hz_left hz_right
    linarith
  exact nontrivialZerosFinset_sum_re_nonnegative_of_dampedKernel
    T κ F G hpair

/-- Finite nontrivial-zero unpaired real-part average nonnegativity for a
damped detector kernel from the pair-nonnegative dominated-kernel input
shape. -/
theorem nontrivialZerosFinset_average_re_nonnegative_of_dampedKernel_pair_nonneg_le
    (T κ : ℝ) (F G : ℂ → ℂ) (hκ : κ ≤ 1)
    (hG_nonneg : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      0 ≤ (G z).re + (G (1 - z)).re)
    (hGF : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      (G z).re + (G (1 - z)).re ≤
        (F z).re + (F (1 - z)).re) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset T, (dampedKernel κ F G ρ).re) /
        ((nontrivialZerosFinset T).card : ℝ) :=
  div_nonneg
    (nontrivialZerosFinset_sum_re_nonnegative_of_dampedKernel_pair_nonneg_le
      T κ F G hκ hG_nonneg hGF)
    (Nat.cast_nonneg _)

/-- Finite nontrivial-zero paired-sum nonnegativity for a self-damped
detector kernel. -/
theorem nontrivialZerosFinset_pair_sum_nonnegative_of_dampedKernel_self
    (T κ : ℝ) (F : ℂ → ℂ)
    (hκ : κ ≤ 1) (hF : LaplacePairPositive F 1) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset T,
      ((dampedKernel κ F F ρ).re +
        (dampedKernel κ F F (1 - ρ)).re) :=
  nontrivialZerosFinset_pair_sum_nonnegative_of_laplace_pair_positive_one
    T (dampedKernel κ F F)
    (laplacePairPositive_one_dampedKernel_self_of_le_one hκ hF)

/-- Finite nontrivial-zero paired-average nonnegativity for a self-damped
detector kernel. -/
theorem nontrivialZerosFinset_pair_average_nonnegative_of_dampedKernel_self
    (T κ : ℝ) (F : ℂ → ℂ)
    (hκ : κ ≤ 1) (hF : LaplacePairPositive F 1) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset T,
        ((dampedKernel κ F F ρ).re +
          (dampedKernel κ F F (1 - ρ)).re)) /
        ((nontrivialZerosFinset T).card : ℝ) :=
  nontrivialZerosFinset_pair_average_nonnegative_of_laplace_pair_positive_one
    T (dampedKernel κ F F)
    (laplacePairPositive_one_dampedKernel_self_of_le_one hκ hF)

/-- Finite nontrivial-zero unpaired real-part sum nonnegativity for a
self-damped detector kernel. -/
theorem nontrivialZerosFinset_sum_re_nonnegative_of_dampedKernel_self
    (T κ : ℝ) (F : ℂ → ℂ)
    (hκ : κ ≤ 1) (hF : LaplacePairPositive F 1) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset T, (dampedKernel κ F F ρ).re := by
  have hpaired :=
    nontrivialZerosFinset_pair_sum_nonnegative_of_dampedKernel_self
      T κ F hκ hF
  rw [nontrivialZerosFinset_pair_contribution_eq_two_sum_re] at hpaired
  nlinarith

/-- Finite nontrivial-zero unpaired real-part sum nonnegativity for the
concrete self-damped resolvent/Laplace prototype kernel. -/
theorem nontrivialZerosFinset_sum_re_nonnegative_of_selfDampedResolventLaplaceKernel
    (T κ a : ℝ) (hκ : κ ≤ 1) (ha : 0 ≤ a) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset T,
      (dampedKernel κ (resolventLaplaceKernel a) (resolventLaplaceKernel a) ρ).re :=
  nontrivialZerosFinset_sum_re_nonnegative_of_dampedKernel_self
    T κ (resolventLaplaceKernel a) hκ
    (laplacePairPositive_one_resolventLaplaceKernel ha)

/-- Finite nontrivial-zero unpaired real-part average nonnegativity for a
self-damped detector kernel. -/
theorem nontrivialZerosFinset_average_re_nonnegative_of_dampedKernel_self
    (T κ : ℝ) (F : ℂ → ℂ)
    (hκ : κ ≤ 1) (hF : LaplacePairPositive F 1) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset T, (dampedKernel κ F F ρ).re) /
        ((nontrivialZerosFinset T).card : ℝ) :=
  div_nonneg
    (nontrivialZerosFinset_sum_re_nonnegative_of_dampedKernel_self
      T κ F hκ hF)
    (Nat.cast_nonneg _)

/-- Finite nontrivial-zero unpaired real-part sum nonnegativity for a
self-damped detector kernel, from pointwise critical-strip real-part
nonnegativity of the original kernel. -/
theorem nontrivialZerosFinset_sum_re_nonnegative_of_dampedKernel_self_re_nonnegative
    (T κ : ℝ) (F : ℂ → ℂ)
    (hκ : κ ≤ 1)
    (hF : ∀ z : ℂ, 0 ≤ z.re -> z.re ≤ 1 -> 0 ≤ (F z).re) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset T, (dampedKernel κ F F ρ).re := by
  have hpaired :=
    nontrivialZerosFinset_pair_sum_nonnegative_of_laplace_pair_positive_one
      T (dampedKernel κ F F)
      (laplacePairPositive_one_of_re_nonnegative_on_critical_strip
        (dampedKernel_self_re_nonnegative_on_critical_strip_of_le_one hκ hF))
  rw [nontrivialZerosFinset_pair_contribution_eq_two_sum_re] at hpaired
  nlinarith

/-- Finite nontrivial-zero unpaired real-part average nonnegativity for a
self-damped detector kernel, from pointwise critical-strip real-part
nonnegativity of the original kernel. -/
theorem nontrivialZerosFinset_average_re_nonnegative_of_dampedKernel_self_re_nonnegative
    (T κ : ℝ) (F : ℂ → ℂ)
    (hκ : κ ≤ 1)
    (hF : ∀ z : ℂ, 0 ≤ z.re -> z.re ≤ 1 -> 0 ≤ (F z).re) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset T, (dampedKernel κ F F ρ).re) /
        ((nontrivialZerosFinset T).card : ℝ) :=
  div_nonneg
    (nontrivialZerosFinset_sum_re_nonnegative_of_dampedKernel_self_re_nonnegative
      T κ F hκ hF)
    (Nat.cast_nonneg _)

/-- New-zero paired-sum nonnegativity for a damped detector kernel. -/
theorem nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_dampedKernel
    (T U κ : ℝ) (F G : ℂ → ℂ)
    (hpair : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      κ * ((G z).re + (G (1 - z)).re) ≤
        (F z).re + (F (1 - z)).re) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
      ((dampedKernel κ F G ρ).re +
        (dampedKernel κ F G (1 - ρ)).re) :=
  nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_laplace_pair_positive_one
    T U (dampedKernel κ F G)
    (laplacePairPositive_one_dampedKernel_of_pair_le hpair)

/-- New-zero paired-average nonnegativity for a damped detector kernel. -/
theorem nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_dampedKernel
    (T U κ : ℝ) (F G : ℂ → ℂ)
    (hpair : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      κ * ((G z).re + (G (1 - z)).re) ≤
        (F z).re + (F (1 - z)).re) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        ((dampedKernel κ F G ρ).re +
          (dampedKernel κ F G (1 - ρ)).re)) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_laplace_pair_positive_one
    T U (dampedKernel κ F G)
    (laplacePairPositive_one_dampedKernel_of_pair_le hpair)

/-- New-zero unpaired real-part sum nonnegativity for a damped detector
kernel. -/
theorem nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_dampedKernel
    (T U κ : ℝ) (F G : ℂ → ℂ)
    (hpair : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      κ * ((G z).re + (G (1 - z)).re) ≤
        (F z).re + (F (1 - z)).re) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
      (dampedKernel κ F G ρ).re :=
  nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_laplace_pair_positive_one
    T U (dampedKernel κ F G)
    (laplacePairPositive_one_dampedKernel_of_pair_le hpair)

/-- New-zero unpaired real-part average nonnegativity for a damped detector
kernel. -/
theorem nontrivialZerosFinset_sdiff_average_re_nonnegative_of_dampedKernel
    (T U κ : ℝ) (F G : ℂ → ℂ)
    (hpair : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      κ * ((G z).re + (G (1 - z)).re) ≤
        (F z).re + (F (1 - z)).re) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        (dampedKernel κ F G ρ).re) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_sdiff_average_re_nonnegative_of_laplace_pair_positive_one
    T U (dampedKernel κ F G)
    (laplacePairPositive_one_dampedKernel_of_pair_le hpair)

/-- New-zero paired-sum nonnegativity for a damped detector kernel from the
pair-nonnegative dominated-kernel input shape. -/
theorem nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_dampedKernel_pair_nonneg_le
    (T U κ : ℝ) (F G : ℂ → ℂ) (hκ : κ ≤ 1)
    (hG_nonneg : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      0 ≤ (G z).re + (G (1 - z)).re)
    (hGF : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      (G z).re + (G (1 - z)).re ≤
        (F z).re + (F (1 - z)).re) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
      ((dampedKernel κ F G ρ).re +
        (dampedKernel κ F G (1 - ρ)).re) :=
  nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_laplace_pair_positive_one
    T U (dampedKernel κ F G)
    (laplacePairPositive_one_dampedKernel_of_pair_nonneg_le
      hκ hG_nonneg hGF)

/-- New-zero paired-average nonnegativity for a damped detector kernel from the
pair-nonnegative dominated-kernel input shape. -/
theorem nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_dampedKernel_pair_nonneg_le
    (T U κ : ℝ) (F G : ℂ → ℂ) (hκ : κ ≤ 1)
    (hG_nonneg : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      0 ≤ (G z).re + (G (1 - z)).re)
    (hGF : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      (G z).re + (G (1 - z)).re ≤
        (F z).re + (F (1 - z)).re) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        ((dampedKernel κ F G ρ).re +
          (dampedKernel κ F G (1 - ρ)).re)) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_laplace_pair_positive_one
    T U (dampedKernel κ F G)
    (laplacePairPositive_one_dampedKernel_of_pair_nonneg_le
      hκ hG_nonneg hGF)

/-- New-zero unpaired real-part sum nonnegativity for a damped detector kernel
from the pair-nonnegative dominated-kernel input shape. -/
theorem nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_dampedKernel_pair_nonneg_le
    (T U κ : ℝ) (F G : ℂ → ℂ) (hκ : κ ≤ 1)
    (hG_nonneg : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      0 ≤ (G z).re + (G (1 - z)).re)
    (hGF : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      (G z).re + (G (1 - z)).re ≤
        (F z).re + (F (1 - z)).re) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
      (dampedKernel κ F G ρ).re :=
  nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_laplace_pair_positive_one
    T U (dampedKernel κ F G)
    (laplacePairPositive_one_dampedKernel_of_pair_nonneg_le
      hκ hG_nonneg hGF)

/-- New-zero unpaired real-part average nonnegativity for a damped detector
kernel from the pair-nonnegative dominated-kernel input shape. -/
theorem nontrivialZerosFinset_sdiff_average_re_nonnegative_of_dampedKernel_pair_nonneg_le
    (T U κ : ℝ) (F G : ℂ → ℂ) (hκ : κ ≤ 1)
    (hG_nonneg : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      0 ≤ (G z).re + (G (1 - z)).re)
    (hGF : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      (G z).re + (G (1 - z)).re ≤
        (F z).re + (F (1 - z)).re) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        (dampedKernel κ F G ρ).re) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_sdiff_average_re_nonnegative_of_laplace_pair_positive_one
    T U (dampedKernel κ F G)
    (laplacePairPositive_one_dampedKernel_of_pair_nonneg_le
      hκ hG_nonneg hGF)

/-- New-zero paired-sum nonnegativity for a self-damped detector kernel. -/
theorem nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_dampedKernel_self
    (T U κ : ℝ) (F : ℂ → ℂ)
    (hκ : κ ≤ 1) (hF : LaplacePairPositive F 1) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
      ((dampedKernel κ F F ρ).re +
        (dampedKernel κ F F (1 - ρ)).re) :=
  nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_laplace_pair_positive_one
    T U (dampedKernel κ F F)
    (laplacePairPositive_one_dampedKernel_self_of_le_one hκ hF)

/-- New-zero paired-average nonnegativity for a self-damped detector kernel. -/
theorem nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_dampedKernel_self
    (T U κ : ℝ) (F : ℂ → ℂ)
    (hκ : κ ≤ 1) (hF : LaplacePairPositive F 1) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        ((dampedKernel κ F F ρ).re +
          (dampedKernel κ F F (1 - ρ)).re)) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_laplace_pair_positive_one
    T U (dampedKernel κ F F)
    (laplacePairPositive_one_dampedKernel_self_of_le_one hκ hF)

/-- New-zero unpaired real-part sum nonnegativity for a self-damped detector
kernel. -/
theorem nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_dampedKernel_self
    (T U κ : ℝ) (F : ℂ → ℂ)
    (hκ : κ ≤ 1) (hF : LaplacePairPositive F 1) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
      (dampedKernel κ F F ρ).re :=
  nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_laplace_pair_positive_one
    T U (dampedKernel κ F F)
    (laplacePairPositive_one_dampedKernel_self_of_le_one hκ hF)

/-- New-zero unpaired real-part sum nonnegativity for the concrete
self-damped resolvent/Laplace prototype kernel. -/
theorem nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_selfDampedResolventLaplaceKernel
    (T U κ a : ℝ) (hκ : κ ≤ 1) (ha : 0 ≤ a) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
      (dampedKernel κ (resolventLaplaceKernel a) (resolventLaplaceKernel a) ρ).re :=
  nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_dampedKernel_self
    T U κ (resolventLaplaceKernel a) hκ
    (laplacePairPositive_one_resolventLaplaceKernel ha)

/-- New-zero unpaired real-part average nonnegativity for a self-damped detector
kernel. -/
theorem nontrivialZerosFinset_sdiff_average_re_nonnegative_of_dampedKernel_self
    (T U κ : ℝ) (F : ℂ → ℂ)
    (hκ : κ ≤ 1) (hF : LaplacePairPositive F 1) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        (dampedKernel κ F F ρ).re) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_sdiff_average_re_nonnegative_of_laplace_pair_positive_one
    T U (dampedKernel κ F F)
    (laplacePairPositive_one_dampedKernel_self_of_le_one hκ hF)

/-- New-zero unpaired real-part sum nonnegativity for a self-damped detector
kernel, from pointwise critical-strip real-part nonnegativity of the original
kernel. -/
theorem nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_dampedKernel_self_re_nonnegative
    (T U κ : ℝ) (F : ℂ → ℂ)
    (hκ : κ ≤ 1)
    (hF : ∀ z : ℂ, 0 ≤ z.re -> z.re ≤ 1 -> 0 ≤ (F z).re) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
      (dampedKernel κ F F ρ).re :=
  nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_re_nonnegative_on_critical_strip
    T U (dampedKernel κ F F)
    (dampedKernel_self_re_nonnegative_on_critical_strip_of_le_one hκ hF)

/-- New-zero unpaired real-part average nonnegativity for a self-damped detector
kernel, from pointwise critical-strip real-part nonnegativity of the original
kernel. -/
theorem nontrivialZerosFinset_sdiff_average_re_nonnegative_of_dampedKernel_self_re_nonnegative
    (T U κ : ℝ) (F : ℂ → ℂ)
    (hκ : κ ≤ 1)
    (hF : ∀ z : ℂ, 0 ≤ z.re -> z.re ≤ 1 -> 0 ≤ (F z).re) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        (dampedKernel κ F F ρ).re) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_sdiff_average_re_nonnegative_of_re_nonnegative_on_critical_strip
    T U (dampedKernel κ F F)
    (dampedKernel_self_re_nonnegative_on_critical_strip_of_le_one hκ hF)

/-- Finite nontrivial-zero paired-sum nonnegativity for a finite nonnegative
combination of damped detector kernels. -/
theorem nontrivialZerosFinset_pair_sum_nonnegative_of_weightedDampedKernelCombo
    (T : ℝ) (K : Finset ℕ) (w κ : ℕ → ℝ) (F G : ℕ → ℂ → ℂ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hpair : ∀ k ∈ K, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      κ k * ((G k z).re + (G k (1 - z)).re) ≤
        (F k z).re + (F k (1 - z)).re) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset T,
      ((weightedKernelCombo K w
          (fun k => dampedKernel (κ k) (F k) (G k)) ρ).re +
        (weightedKernelCombo K w
          (fun k => dampedKernel (κ k) (F k) (G k)) (1 - ρ)).re) :=
  nontrivialZerosFinset_pair_sum_nonnegative_of_laplace_pair_positive_one
    T (weightedKernelCombo K w (fun k => dampedKernel (κ k) (F k) (G k)))
    (laplacePairPositive_one_weightedDampedKernelCombo_of_pair_le hw hpair)

/-- Finite nontrivial-zero paired-average nonnegativity for a finite
nonnegative combination of damped detector kernels. -/
theorem nontrivialZerosFinset_pair_average_nonnegative_of_weightedDampedKernelCombo
    (T : ℝ) (K : Finset ℕ) (w κ : ℕ → ℝ) (F G : ℕ → ℂ → ℂ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hpair : ∀ k ∈ K, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      κ k * ((G k z).re + (G k (1 - z)).re) ≤
        (F k z).re + (F k (1 - z)).re) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset T,
        ((weightedKernelCombo K w
            (fun k => dampedKernel (κ k) (F k) (G k)) ρ).re +
          (weightedKernelCombo K w
            (fun k => dampedKernel (κ k) (F k) (G k)) (1 - ρ)).re)) /
        ((nontrivialZerosFinset T).card : ℝ) :=
  nontrivialZerosFinset_pair_average_nonnegative_of_laplace_pair_positive_one
    T (weightedKernelCombo K w (fun k => dampedKernel (κ k) (F k) (G k)))
    (laplacePairPositive_one_weightedDampedKernelCombo_of_pair_le hw hpair)

/-- Finite nontrivial-zero unpaired real-part sum nonnegativity for a finite
nonnegative combination of damped detector kernels. -/
theorem nontrivialZerosFinset_sum_re_nonnegative_of_weightedDampedKernelCombo
    (T : ℝ) (K : Finset ℕ) (w κ : ℕ → ℝ) (F G : ℕ → ℂ → ℂ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hpair : ∀ k ∈ K, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      κ k * ((G k z).re + (G k (1 - z)).re) ≤
        (F k z).re + (F k (1 - z)).re) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset T,
      (weightedKernelCombo K w
        (fun k => dampedKernel (κ k) (F k) (G k)) ρ).re := by
  have hpaired :=
    nontrivialZerosFinset_pair_sum_nonnegative_of_weightedDampedKernelCombo
      T K w κ F G hw hpair
  rw [nontrivialZerosFinset_pair_contribution_eq_two_sum_re] at hpaired
  nlinarith

/-- Finite nontrivial-zero unpaired real-part average nonnegativity for a
finite nonnegative combination of damped detector kernels. -/
theorem nontrivialZerosFinset_average_re_nonnegative_of_weightedDampedKernelCombo
    (T : ℝ) (K : Finset ℕ) (w κ : ℕ → ℝ) (F G : ℕ → ℂ → ℂ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hpair : ∀ k ∈ K, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      κ k * ((G k z).re + (G k (1 - z)).re) ≤
        (F k z).re + (F k (1 - z)).re) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset T,
        (weightedKernelCombo K w
          (fun k => dampedKernel (κ k) (F k) (G k)) ρ).re) /
        ((nontrivialZerosFinset T).card : ℝ) :=
  div_nonneg
    (nontrivialZerosFinset_sum_re_nonnegative_of_weightedDampedKernelCombo
      T K w κ F G hw hpair)
    (Nat.cast_nonneg _)

/-- New-zero paired-sum nonnegativity for a finite nonnegative combination of
damped detector kernels. -/
theorem nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_weightedDampedKernelCombo
    (T U : ℝ) (K : Finset ℕ) (w κ : ℕ → ℝ) (F G : ℕ → ℂ → ℂ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hpair : ∀ k ∈ K, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      κ k * ((G k z).re + (G k (1 - z)).re) ≤
        (F k z).re + (F k (1 - z)).re) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
      ((weightedKernelCombo K w
          (fun k => dampedKernel (κ k) (F k) (G k)) ρ).re +
        (weightedKernelCombo K w
          (fun k => dampedKernel (κ k) (F k) (G k)) (1 - ρ)).re) :=
  nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_laplace_pair_positive_one
    T U (weightedKernelCombo K w
      (fun k => dampedKernel (κ k) (F k) (G k)))
    (laplacePairPositive_one_weightedDampedKernelCombo_of_pair_le hw hpair)

/-- New-zero paired-average nonnegativity for a finite nonnegative combination
of damped detector kernels. -/
theorem nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_weightedDampedKernelCombo
    (T U : ℝ) (K : Finset ℕ) (w κ : ℕ → ℝ) (F G : ℕ → ℂ → ℂ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hpair : ∀ k ∈ K, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      κ k * ((G k z).re + (G k (1 - z)).re) ≤
        (F k z).re + (F k (1 - z)).re) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        ((weightedKernelCombo K w
            (fun k => dampedKernel (κ k) (F k) (G k)) ρ).re +
          (weightedKernelCombo K w
            (fun k => dampedKernel (κ k) (F k) (G k)) (1 - ρ)).re)) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_laplace_pair_positive_one
    T U (weightedKernelCombo K w
      (fun k => dampedKernel (κ k) (F k) (G k)))
    (laplacePairPositive_one_weightedDampedKernelCombo_of_pair_le hw hpair)

/-- New-zero unpaired real-part sum nonnegativity for a finite nonnegative
combination of damped detector kernels. -/
theorem nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_weightedDampedKernelCombo
    (T U : ℝ) (K : Finset ℕ) (w κ : ℕ → ℝ) (F G : ℕ → ℂ → ℂ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hpair : ∀ k ∈ K, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      κ k * ((G k z).re + (G k (1 - z)).re) ≤
        (F k z).re + (F k (1 - z)).re) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
      (weightedKernelCombo K w
        (fun k => dampedKernel (κ k) (F k) (G k)) ρ).re :=
  nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_laplace_pair_positive_one
    T U (weightedKernelCombo K w
      (fun k => dampedKernel (κ k) (F k) (G k)))
    (laplacePairPositive_one_weightedDampedKernelCombo_of_pair_le hw hpair)

/-- New-zero unpaired real-part average nonnegativity for a finite nonnegative
combination of damped detector kernels. -/
theorem nontrivialZerosFinset_sdiff_average_re_nonnegative_of_weightedDampedKernelCombo
    (T U : ℝ) (K : Finset ℕ) (w κ : ℕ → ℝ) (F G : ℕ → ℂ → ℂ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hpair : ∀ k ∈ K, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      κ k * ((G k z).re + (G k (1 - z)).re) ≤
        (F k z).re + (F k (1 - z)).re) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        (weightedKernelCombo K w
          (fun k => dampedKernel (κ k) (F k) (G k)) ρ).re) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_sdiff_average_re_nonnegative_of_laplace_pair_positive_one
    T U (weightedKernelCombo K w
      (fun k => dampedKernel (κ k) (F k) (G k)))
    (laplacePairPositive_one_weightedDampedKernelCombo_of_pair_le hw hpair)

/-- Finite nontrivial-zero paired-sum nonnegativity for a finite nonnegative
combination of self-damped detector kernels. -/
theorem nontrivialZerosFinset_pair_sum_nonnegative_of_weightedDampedKernelCombo_self
    (T : ℝ) (K : Finset ℕ) (w κ : ℕ → ℝ) (F : ℕ → ℂ → ℂ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (hF : ∀ k ∈ K, LaplacePairPositive (F k) 1) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset T,
      ((weightedKernelCombo K w
          (fun k => dampedKernel (κ k) (F k) (F k)) ρ).re +
        (weightedKernelCombo K w
          (fun k => dampedKernel (κ k) (F k) (F k)) (1 - ρ)).re) :=
  nontrivialZerosFinset_pair_sum_nonnegative_of_laplace_pair_positive_one
    T (weightedKernelCombo K w (fun k => dampedKernel (κ k) (F k) (F k)))
    (laplacePairPositive_one_weightedDampedKernelCombo_self_of_le_one hw hκ hF)

/-- Finite nontrivial-zero paired-sum nonnegativity for finite nonnegative
combinations of self-damped resolvent/Laplace prototype kernels. -/
theorem nontrivialZerosFinset_pair_sum_nonnegative_of_weightedSelfDampedResolventLaplaceKernelCombo
    (T : ℝ) (K : Finset ℕ) (w κ a : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (ha : ∀ k ∈ K, 0 ≤ a k) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset T,
      ((weightedKernelCombo K w
          (fun k => dampedKernel (κ k)
            (resolventLaplaceKernel (a k)) (resolventLaplaceKernel (a k))) ρ).re +
        (weightedKernelCombo K w
          (fun k => dampedKernel (κ k)
            (resolventLaplaceKernel (a k)) (resolventLaplaceKernel (a k)))
            (1 - ρ)).re) :=
  nontrivialZerosFinset_pair_sum_nonnegative_of_weightedDampedKernelCombo_self
    T K w κ (fun k => resolventLaplaceKernel (a k)) hw hκ
    (fun k hk => laplacePairPositive_one_resolventLaplaceKernel (ha k hk))

/-- Finite nontrivial-zero paired-average nonnegativity for a finite nonnegative
combination of self-damped detector kernels. -/
theorem nontrivialZerosFinset_pair_average_nonnegative_of_weightedDampedKernelCombo_self
    (T : ℝ) (K : Finset ℕ) (w κ : ℕ → ℝ) (F : ℕ → ℂ → ℂ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (hF : ∀ k ∈ K, LaplacePairPositive (F k) 1) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset T,
        ((weightedKernelCombo K w
            (fun k => dampedKernel (κ k) (F k) (F k)) ρ).re +
          (weightedKernelCombo K w
            (fun k => dampedKernel (κ k) (F k) (F k)) (1 - ρ)).re)) /
        ((nontrivialZerosFinset T).card : ℝ) :=
  nontrivialZerosFinset_pair_average_nonnegative_of_laplace_pair_positive_one
    T (weightedKernelCombo K w (fun k => dampedKernel (κ k) (F k) (F k)))
    (laplacePairPositive_one_weightedDampedKernelCombo_self_of_le_one hw hκ hF)

/-- Finite nontrivial-zero paired-average nonnegativity for finite nonnegative
combinations of self-damped resolvent/Laplace prototype kernels. -/
theorem nontrivialZerosFinset_pair_average_nonnegative_of_weightedSelfDampedResolventLaplaceKernelCombo
    (T : ℝ) (K : Finset ℕ) (w κ a : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (ha : ∀ k ∈ K, 0 ≤ a k) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset T,
        ((weightedKernelCombo K w
            (fun k => dampedKernel (κ k)
              (resolventLaplaceKernel (a k)) (resolventLaplaceKernel (a k))) ρ).re +
          (weightedKernelCombo K w
            (fun k => dampedKernel (κ k)
              (resolventLaplaceKernel (a k)) (resolventLaplaceKernel (a k)))
              (1 - ρ)).re)) /
        ((nontrivialZerosFinset T).card : ℝ) :=
  nontrivialZerosFinset_pair_average_nonnegative_of_weightedDampedKernelCombo_self
    T K w κ (fun k => resolventLaplaceKernel (a k)) hw hκ
    (fun k hk => laplacePairPositive_one_resolventLaplaceKernel (ha k hk))

/-- Finite nontrivial-zero unpaired real-part sum nonnegativity for a finite
nonnegative combination of self-damped detector kernels. -/
theorem nontrivialZerosFinset_sum_re_nonnegative_of_weightedDampedKernelCombo_self
    (T : ℝ) (K : Finset ℕ) (w κ : ℕ → ℝ) (F : ℕ → ℂ → ℂ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (hF : ∀ k ∈ K, LaplacePairPositive (F k) 1) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset T,
      (weightedKernelCombo K w
        (fun k => dampedKernel (κ k) (F k) (F k)) ρ).re := by
  have hpaired :=
    nontrivialZerosFinset_pair_sum_nonnegative_of_weightedDampedKernelCombo_self
      T K w κ F hw hκ hF
  rw [nontrivialZerosFinset_pair_contribution_eq_two_sum_re] at hpaired
  nlinarith

/-- Finite nontrivial-zero unpaired real-part sum nonnegativity for finite
nonnegative combinations of self-damped resolvent/Laplace prototype kernels. -/
theorem nontrivialZerosFinset_sum_re_nonnegative_of_weightedSelfDampedResolventLaplaceKernelCombo
    (T : ℝ) (K : Finset ℕ) (w κ a : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (ha : ∀ k ∈ K, 0 ≤ a k) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset T,
      (weightedKernelCombo K w
        (fun k => dampedKernel (κ k)
          (resolventLaplaceKernel (a k)) (resolventLaplaceKernel (a k))) ρ).re :=
  nontrivialZerosFinset_sum_re_nonnegative_of_weightedDampedKernelCombo_self
    T K w κ (fun k => resolventLaplaceKernel (a k)) hw hκ
    (fun k hk => laplacePairPositive_one_resolventLaplaceKernel (ha k hk))

/-- Finite nontrivial-zero unpaired real-part average nonnegativity for finite
nonnegative combinations of self-damped resolvent/Laplace prototype kernels. -/
theorem nontrivialZerosFinset_average_re_nonnegative_of_weightedSelfDampedResolventLaplaceKernelCombo
    (T : ℝ) (K : Finset ℕ) (w κ a : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (ha : ∀ k ∈ K, 0 ≤ a k) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset T,
        (weightedKernelCombo K w
          (fun k => dampedKernel (κ k)
            (resolventLaplaceKernel (a k)) (resolventLaplaceKernel (a k))) ρ).re) /
        ((nontrivialZerosFinset T).card : ℝ) :=
  div_nonneg
    (nontrivialZerosFinset_sum_re_nonnegative_of_weightedSelfDampedResolventLaplaceKernelCombo
      T K w κ a hw hκ ha)
    (Nat.cast_nonneg _)

/-- Finite nontrivial-zero unpaired real-part average nonnegativity for a finite
nonnegative combination of self-damped detector kernels. -/
theorem nontrivialZerosFinset_average_re_nonnegative_of_weightedDampedKernelCombo_self
    (T : ℝ) (K : Finset ℕ) (w κ : ℕ → ℝ) (F : ℕ → ℂ → ℂ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (hF : ∀ k ∈ K, LaplacePairPositive (F k) 1) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset T,
        (weightedKernelCombo K w
          (fun k => dampedKernel (κ k) (F k) (F k)) ρ).re) /
        ((nontrivialZerosFinset T).card : ℝ) :=
  div_nonneg
    (nontrivialZerosFinset_sum_re_nonnegative_of_weightedDampedKernelCombo_self
      T K w κ F hw hκ hF)
    (Nat.cast_nonneg _)

/-- Finite nontrivial-zero unpaired real-part sum nonnegativity for a finite
nonnegative combination of self-damped detector kernels, from pointwise
critical-strip real-part nonnegativity of each original kernel. -/
theorem nontrivialZerosFinset_sum_re_nonnegative_of_weightedDampedKernelCombo_self_re_nonnegative
    (T : ℝ) (K : Finset ℕ) (w κ : ℕ → ℝ) (F : ℕ → ℂ → ℂ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (hF : ∀ k ∈ K, ∀ z : ℂ, 0 ≤ z.re -> z.re ≤ 1 ->
      0 ≤ (F k z).re) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset T,
      (weightedKernelCombo K w
        (fun k => dampedKernel (κ k) (F k) (F k)) ρ).re := by
  have hpaired :=
    nontrivialZerosFinset_pair_sum_nonnegative_of_laplace_pair_positive_one
      T (weightedKernelCombo K w
        (fun k => dampedKernel (κ k) (F k) (F k)))
      (laplacePairPositive_one_of_re_nonnegative_on_critical_strip
        (weightedDampedKernelCombo_self_re_nonnegative_on_critical_strip_of_le_one
          hw hκ hF))
  rw [nontrivialZerosFinset_pair_contribution_eq_two_sum_re] at hpaired
  nlinarith

/-- Finite nontrivial-zero unpaired real-part average nonnegativity for a finite
nonnegative combination of self-damped detector kernels, from pointwise
critical-strip real-part nonnegativity of each original kernel. -/
theorem nontrivialZerosFinset_average_re_nonnegative_of_weightedDampedKernelCombo_self_re_nonnegative
    (T : ℝ) (K : Finset ℕ) (w κ : ℕ → ℝ) (F : ℕ → ℂ → ℂ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (hF : ∀ k ∈ K, ∀ z : ℂ, 0 ≤ z.re -> z.re ≤ 1 ->
      0 ≤ (F k z).re) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset T,
        (weightedKernelCombo K w
          (fun k => dampedKernel (κ k) (F k) (F k)) ρ).re) /
        ((nontrivialZerosFinset T).card : ℝ) :=
  div_nonneg
    (nontrivialZerosFinset_sum_re_nonnegative_of_weightedDampedKernelCombo_self_re_nonnegative
      T K w κ F hw hκ hF)
    (Nat.cast_nonneg _)

/-- New-zero paired-sum nonnegativity for a finite nonnegative combination of
self-damped detector kernels. -/
theorem nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_weightedDampedKernelCombo_self
    (T U : ℝ) (K : Finset ℕ) (w κ : ℕ → ℝ) (F : ℕ → ℂ → ℂ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (hF : ∀ k ∈ K, LaplacePairPositive (F k) 1) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
      ((weightedKernelCombo K w
          (fun k => dampedKernel (κ k) (F k) (F k)) ρ).re +
        (weightedKernelCombo K w
          (fun k => dampedKernel (κ k) (F k) (F k)) (1 - ρ)).re) :=
  nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_laplace_pair_positive_one
    T U (weightedKernelCombo K w
      (fun k => dampedKernel (κ k) (F k) (F k)))
    (laplacePairPositive_one_weightedDampedKernelCombo_self_of_le_one hw hκ hF)

/-- New-zero paired-sum nonnegativity for finite nonnegative combinations of
self-damped resolvent/Laplace prototype kernels. -/
theorem nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_weightedSelfDampedResolventLaplaceKernelCombo
    (T U : ℝ) (K : Finset ℕ) (w κ a : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (ha : ∀ k ∈ K, 0 ≤ a k) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
      ((weightedKernelCombo K w
          (fun k => dampedKernel (κ k)
            (resolventLaplaceKernel (a k)) (resolventLaplaceKernel (a k))) ρ).re +
        (weightedKernelCombo K w
          (fun k => dampedKernel (κ k)
            (resolventLaplaceKernel (a k)) (resolventLaplaceKernel (a k)))
            (1 - ρ)).re) :=
  nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_weightedDampedKernelCombo_self
    T U K w κ (fun k => resolventLaplaceKernel (a k)) hw hκ
    (fun k hk => laplacePairPositive_one_resolventLaplaceKernel (ha k hk))

/-- New-zero paired-average nonnegativity for a finite nonnegative combination of
self-damped detector kernels. -/
theorem nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_weightedDampedKernelCombo_self
    (T U : ℝ) (K : Finset ℕ) (w κ : ℕ → ℝ) (F : ℕ → ℂ → ℂ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (hF : ∀ k ∈ K, LaplacePairPositive (F k) 1) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        ((weightedKernelCombo K w
            (fun k => dampedKernel (κ k) (F k) (F k)) ρ).re +
          (weightedKernelCombo K w
            (fun k => dampedKernel (κ k) (F k) (F k)) (1 - ρ)).re)) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_laplace_pair_positive_one
    T U (weightedKernelCombo K w
      (fun k => dampedKernel (κ k) (F k) (F k)))
    (laplacePairPositive_one_weightedDampedKernelCombo_self_of_le_one hw hκ hF)

/-- New-zero paired-average nonnegativity for finite nonnegative combinations of
self-damped resolvent/Laplace prototype kernels. -/
theorem nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_weightedSelfDampedResolventLaplaceKernelCombo
    (T U : ℝ) (K : Finset ℕ) (w κ a : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (ha : ∀ k ∈ K, 0 ≤ a k) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        ((weightedKernelCombo K w
            (fun k => dampedKernel (κ k)
              (resolventLaplaceKernel (a k)) (resolventLaplaceKernel (a k))) ρ).re +
          (weightedKernelCombo K w
            (fun k => dampedKernel (κ k)
              (resolventLaplaceKernel (a k)) (resolventLaplaceKernel (a k)))
              (1 - ρ)).re)) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_weightedDampedKernelCombo_self
    T U K w κ (fun k => resolventLaplaceKernel (a k)) hw hκ
    (fun k hk => laplacePairPositive_one_resolventLaplaceKernel (ha k hk))

/-- New-zero unpaired real-part sum nonnegativity for a finite nonnegative
combination of self-damped detector kernels. -/
theorem nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_weightedDampedKernelCombo_self
    (T U : ℝ) (K : Finset ℕ) (w κ : ℕ → ℝ) (F : ℕ → ℂ → ℂ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (hF : ∀ k ∈ K, LaplacePairPositive (F k) 1) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
      (weightedKernelCombo K w
        (fun k => dampedKernel (κ k) (F k) (F k)) ρ).re :=
  nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_laplace_pair_positive_one
    T U (weightedKernelCombo K w
      (fun k => dampedKernel (κ k) (F k) (F k)))
    (laplacePairPositive_one_weightedDampedKernelCombo_self_of_le_one hw hκ hF)

/-- New-zero unpaired real-part sum nonnegativity for finite nonnegative
combinations of self-damped resolvent/Laplace prototype kernels. -/
theorem nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_weightedSelfDampedResolventLaplaceKernelCombo
    (T U : ℝ) (K : Finset ℕ) (w κ a : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (ha : ∀ k ∈ K, 0 ≤ a k) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
      (weightedKernelCombo K w
        (fun k => dampedKernel (κ k)
          (resolventLaplaceKernel (a k)) (resolventLaplaceKernel (a k))) ρ).re :=
  nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_weightedDampedKernelCombo_self
    T U K w κ (fun k => resolventLaplaceKernel (a k)) hw hκ
    (fun k hk => laplacePairPositive_one_resolventLaplaceKernel (ha k hk))

/-- New-zero unpaired real-part average nonnegativity for finite nonnegative
combinations of self-damped resolvent/Laplace prototype kernels. -/
theorem nontrivialZerosFinset_sdiff_average_re_nonnegative_of_weightedSelfDampedResolventLaplaceKernelCombo
    (T U : ℝ) (K : Finset ℕ) (w κ a : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (ha : ∀ k ∈ K, 0 ≤ a k) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        (weightedKernelCombo K w
          (fun k => dampedKernel (κ k)
            (resolventLaplaceKernel (a k)) (resolventLaplaceKernel (a k))) ρ).re) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) :=
  div_nonneg
    (nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_weightedSelfDampedResolventLaplaceKernelCombo
      T U K w κ a hw hκ ha)
    (Nat.cast_nonneg _)

/-- Finite nontrivial-zero paired-sum nonnegativity for finite nonnegative
combinations of self-damped affine resolvent/Laplace prototype kernels. -/
theorem nontrivialZerosFinset_pair_sum_nonnegative_of_weightedSelfDampedAffineResolventLaplaceKernelCombo
    (T : ℝ) (K : Finset ℕ) (w κ a b c : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (ha : ∀ k ∈ K, 0 ≤ a k)
    (hb : ∀ k ∈ K, 0 ≤ b k)
    (hc : ∀ k ∈ K, 0 ≤ c k) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset T,
      ((weightedKernelCombo K w
          (fun k => dampedKernel (κ k)
            (affineResolventLaplaceKernel (a k) (b k) (c k))
            (affineResolventLaplaceKernel (a k) (b k) (c k))) ρ).re +
        (weightedKernelCombo K w
          (fun k => dampedKernel (κ k)
            (affineResolventLaplaceKernel (a k) (b k) (c k))
            (affineResolventLaplaceKernel (a k) (b k) (c k)))
            (1 - ρ)).re) :=
  nontrivialZerosFinset_pair_sum_nonnegative_of_weightedDampedKernelCombo_self
    T K w κ (fun k => affineResolventLaplaceKernel (a k) (b k) (c k))
    hw hκ
    (fun k hk => laplacePairPositive_one_affineResolventLaplaceKernel
      (ha k hk) (hb k hk) (hc k hk))

/-- Finite nontrivial-zero paired-average nonnegativity for finite nonnegative
combinations of self-damped affine resolvent/Laplace prototype kernels. -/
theorem nontrivialZerosFinset_pair_average_nonnegative_of_weightedSelfDampedAffineResolventLaplaceKernelCombo
    (T : ℝ) (K : Finset ℕ) (w κ a b c : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (ha : ∀ k ∈ K, 0 ≤ a k)
    (hb : ∀ k ∈ K, 0 ≤ b k)
    (hc : ∀ k ∈ K, 0 ≤ c k) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset T,
        ((weightedKernelCombo K w
            (fun k => dampedKernel (κ k)
              (affineResolventLaplaceKernel (a k) (b k) (c k))
              (affineResolventLaplaceKernel (a k) (b k) (c k))) ρ).re +
          (weightedKernelCombo K w
            (fun k => dampedKernel (κ k)
              (affineResolventLaplaceKernel (a k) (b k) (c k))
              (affineResolventLaplaceKernel (a k) (b k) (c k)))
              (1 - ρ)).re)) /
        ((nontrivialZerosFinset T).card : ℝ) :=
  nontrivialZerosFinset_pair_average_nonnegative_of_weightedDampedKernelCombo_self
    T K w κ (fun k => affineResolventLaplaceKernel (a k) (b k) (c k))
    hw hκ
    (fun k hk => laplacePairPositive_one_affineResolventLaplaceKernel
      (ha k hk) (hb k hk) (hc k hk))

/-- Finite nontrivial-zero unpaired real-part sum nonnegativity for finite
nonnegative combinations of self-damped affine resolvent/Laplace prototype
kernels. -/
theorem nontrivialZerosFinset_sum_re_nonnegative_of_weightedSelfDampedAffineResolventLaplaceKernelCombo
    (T : ℝ) (K : Finset ℕ) (w κ a b c : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (ha : ∀ k ∈ K, 0 ≤ a k)
    (hb : ∀ k ∈ K, 0 ≤ b k)
    (hc : ∀ k ∈ K, 0 ≤ c k) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset T,
      (weightedKernelCombo K w
        (fun k => dampedKernel (κ k)
          (affineResolventLaplaceKernel (a k) (b k) (c k))
          (affineResolventLaplaceKernel (a k) (b k) (c k))) ρ).re :=
  nontrivialZerosFinset_sum_re_nonnegative_of_weightedDampedKernelCombo_self
    T K w κ (fun k => affineResolventLaplaceKernel (a k) (b k) (c k))
    hw hκ
    (fun k hk => laplacePairPositive_one_affineResolventLaplaceKernel
      (ha k hk) (hb k hk) (hc k hk))

/-- Finite nontrivial-zero unpaired real-part average nonnegativity for finite
nonnegative combinations of self-damped affine resolvent/Laplace prototype
kernels. -/
theorem nontrivialZerosFinset_average_re_nonnegative_of_weightedSelfDampedAffineResolventLaplaceKernelCombo
    (T : ℝ) (K : Finset ℕ) (w κ a b c : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (ha : ∀ k ∈ K, 0 ≤ a k)
    (hb : ∀ k ∈ K, 0 ≤ b k)
    (hc : ∀ k ∈ K, 0 ≤ c k) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset T,
        (weightedKernelCombo K w
          (fun k => dampedKernel (κ k)
            (affineResolventLaplaceKernel (a k) (b k) (c k))
            (affineResolventLaplaceKernel (a k) (b k) (c k))) ρ).re) /
        ((nontrivialZerosFinset T).card : ℝ) :=
  nontrivialZerosFinset_average_re_nonnegative_of_weightedDampedKernelCombo_self
    T K w κ (fun k => affineResolventLaplaceKernel (a k) (b k) (c k))
    hw hκ
    (fun k hk => laplacePairPositive_one_affineResolventLaplaceKernel
      (ha k hk) (hb k hk) (hc k hk))

/-- New-zero paired-sum nonnegativity for finite nonnegative combinations of
self-damped affine resolvent/Laplace prototype kernels. -/
theorem nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_weightedSelfDampedAffineResolventLaplaceKernelCombo
    (T U : ℝ) (K : Finset ℕ) (w κ a b c : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (ha : ∀ k ∈ K, 0 ≤ a k)
    (hb : ∀ k ∈ K, 0 ≤ b k)
    (hc : ∀ k ∈ K, 0 ≤ c k) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
      ((weightedKernelCombo K w
          (fun k => dampedKernel (κ k)
            (affineResolventLaplaceKernel (a k) (b k) (c k))
            (affineResolventLaplaceKernel (a k) (b k) (c k))) ρ).re +
        (weightedKernelCombo K w
          (fun k => dampedKernel (κ k)
            (affineResolventLaplaceKernel (a k) (b k) (c k))
            (affineResolventLaplaceKernel (a k) (b k) (c k)))
            (1 - ρ)).re) :=
  nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_weightedDampedKernelCombo_self
    T U K w κ (fun k => affineResolventLaplaceKernel (a k) (b k) (c k))
    hw hκ
    (fun k hk => laplacePairPositive_one_affineResolventLaplaceKernel
      (ha k hk) (hb k hk) (hc k hk))

/-- New-zero paired-average nonnegativity for finite nonnegative combinations
of self-damped affine resolvent/Laplace prototype kernels. -/
theorem nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_weightedSelfDampedAffineResolventLaplaceKernelCombo
    (T U : ℝ) (K : Finset ℕ) (w κ a b c : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (ha : ∀ k ∈ K, 0 ≤ a k)
    (hb : ∀ k ∈ K, 0 ≤ b k)
    (hc : ∀ k ∈ K, 0 ≤ c k) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        ((weightedKernelCombo K w
            (fun k => dampedKernel (κ k)
              (affineResolventLaplaceKernel (a k) (b k) (c k))
              (affineResolventLaplaceKernel (a k) (b k) (c k))) ρ).re +
          (weightedKernelCombo K w
            (fun k => dampedKernel (κ k)
              (affineResolventLaplaceKernel (a k) (b k) (c k))
              (affineResolventLaplaceKernel (a k) (b k) (c k)))
              (1 - ρ)).re)) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_weightedDampedKernelCombo_self
    T U K w κ (fun k => affineResolventLaplaceKernel (a k) (b k) (c k))
    hw hκ
    (fun k hk => laplacePairPositive_one_affineResolventLaplaceKernel
      (ha k hk) (hb k hk) (hc k hk))

/-- New-zero unpaired real-part sum nonnegativity for finite nonnegative
combinations of self-damped affine resolvent/Laplace prototype kernels. -/
theorem nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_weightedSelfDampedAffineResolventLaplaceKernelCombo
    (T U : ℝ) (K : Finset ℕ) (w κ a b c : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (ha : ∀ k ∈ K, 0 ≤ a k)
    (hb : ∀ k ∈ K, 0 ≤ b k)
    (hc : ∀ k ∈ K, 0 ≤ c k) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
      (weightedKernelCombo K w
        (fun k => dampedKernel (κ k)
          (affineResolventLaplaceKernel (a k) (b k) (c k))
          (affineResolventLaplaceKernel (a k) (b k) (c k))) ρ).re :=
  nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_weightedDampedKernelCombo_self
    T U K w κ (fun k => affineResolventLaplaceKernel (a k) (b k) (c k))
    hw hκ
    (fun k hk => laplacePairPositive_one_affineResolventLaplaceKernel
      (ha k hk) (hb k hk) (hc k hk))

/-- New-zero unpaired real-part average nonnegativity for finite nonnegative
combinations of self-damped affine resolvent/Laplace prototype kernels. -/
theorem nontrivialZerosFinset_sdiff_average_re_nonnegative_of_weightedSelfDampedAffineResolventLaplaceKernelCombo
    (T U : ℝ) (K : Finset ℕ) (w κ a b c : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (ha : ∀ k ∈ K, 0 ≤ a k)
    (hb : ∀ k ∈ K, 0 ≤ b k)
    (hc : ∀ k ∈ K, 0 ≤ c k) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        (weightedKernelCombo K w
          (fun k => dampedKernel (κ k)
            (affineResolventLaplaceKernel (a k) (b k) (c k))
            (affineResolventLaplaceKernel (a k) (b k) (c k))) ρ).re) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) :=
  div_nonneg
    (nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_weightedSelfDampedAffineResolventLaplaceKernelCombo
      T U K w κ a b c hw hκ ha hb hc)
    (Nat.cast_nonneg _)

/-- New-zero unpaired real-part average nonnegativity for a finite nonnegative
combination of self-damped detector kernels. -/
theorem nontrivialZerosFinset_sdiff_average_re_nonnegative_of_weightedDampedKernelCombo_self
    (T U : ℝ) (K : Finset ℕ) (w κ : ℕ → ℝ) (F : ℕ → ℂ → ℂ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (hF : ∀ k ∈ K, LaplacePairPositive (F k) 1) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        (weightedKernelCombo K w
          (fun k => dampedKernel (κ k) (F k) (F k)) ρ).re) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_sdiff_average_re_nonnegative_of_laplace_pair_positive_one
    T U (weightedKernelCombo K w
      (fun k => dampedKernel (κ k) (F k) (F k)))
    (laplacePairPositive_one_weightedDampedKernelCombo_self_of_le_one hw hκ hF)

/-- New-zero unpaired real-part sum nonnegativity for a finite nonnegative
combination of self-damped detector kernels, from pointwise critical-strip
real-part nonnegativity of each original kernel. -/
theorem nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_weightedDampedKernelCombo_self_re_nonnegative
    (T U : ℝ) (K : Finset ℕ) (w κ : ℕ → ℝ) (F : ℕ → ℂ → ℂ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (hF : ∀ k ∈ K, ∀ z : ℂ, 0 ≤ z.re -> z.re ≤ 1 ->
      0 ≤ (F k z).re) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
      (weightedKernelCombo K w
        (fun k => dampedKernel (κ k) (F k) (F k)) ρ).re :=
  nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_re_nonnegative_on_critical_strip
    T U (weightedKernelCombo K w
      (fun k => dampedKernel (κ k) (F k) (F k)))
    (weightedDampedKernelCombo_self_re_nonnegative_on_critical_strip_of_le_one
      hw hκ hF)

/-- New-zero unpaired real-part average nonnegativity for a finite nonnegative
combination of self-damped detector kernels, from pointwise critical-strip
real-part nonnegativity of each original kernel. -/
theorem nontrivialZerosFinset_sdiff_average_re_nonnegative_of_weightedDampedKernelCombo_self_re_nonnegative
    (T U : ℝ) (K : Finset ℕ) (w κ : ℕ → ℝ) (F : ℕ → ℂ → ℂ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (hF : ∀ k ∈ K, ∀ z : ℂ, 0 ≤ z.re -> z.re ≤ 1 ->
      0 ≤ (F k z).re) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        (weightedKernelCombo K w
          (fun k => dampedKernel (κ k) (F k) (F k)) ρ).re) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_sdiff_average_re_nonnegative_of_re_nonnegative_on_critical_strip
    T U (weightedKernelCombo K w
      (fun k => dampedKernel (κ k) (F k) (F k)))
    (weightedDampedKernelCombo_self_re_nonnegative_on_critical_strip_of_le_one
      hw hκ hF)

/-- Center-one Laplace-pair positivity also makes the unpaired real-part sum
nonnegative, after reindexing the reflected half of the paired sum by
`ρ ↦ 1 - ρ`. -/
lemma nontrivialZerosFinset_sum_re_nonnegative_of_laplace_pair_positive_one
    (T : ℝ) (F : ℂ → ℂ)
    (hF : LaplacePairPositive F 1) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset T, (F ρ).re := by
  have hpair :=
    nontrivialZerosFinset_pair_sum_nonnegative_of_laplace_pair_positive_one
      T F hF
  rw [nontrivialZerosFinset_pair_contribution_eq_two_sum_re] at hpair
  nlinarith

/-- Pointwise real-part nonnegativity on the critical strip makes the unpaired
real-part sum over height-truncated nontrivial zeros nonnegative. -/
lemma nontrivialZerosFinset_sum_re_nonnegative_of_re_nonnegative_on_critical_strip
    (T : ℝ) (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 0 ≤ (F z).re) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset T, (F ρ).re :=
  nontrivialZerosFinset_sum_re_nonnegative_of_laplace_pair_positive_one
    T F (laplacePairPositive_one_of_re_nonnegative_on_critical_strip hF)

/-- Pointwise real-part nonnegativity on the critical strip makes the average
real-part contribution over height-truncated nontrivial zeros nonnegative. -/
lemma nontrivialZerosFinset_average_re_nonnegative_of_re_nonnegative_on_critical_strip
    (T : ℝ) (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 0 ≤ (F z).re) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset T, (F ρ).re) /
        (((nontrivialZerosFinset T).card : ℝ)) :=
  div_nonneg
    (nontrivialZerosFinset_sum_re_nonnegative_of_re_nonnegative_on_critical_strip
      T F hF)
    (Nat.cast_nonneg _)

/-- Finite nontrivial-zero unpaired real-part sum nonnegativity for finite
nonnegative combinations of self-damped affine resolvent/Laplace prototype
kernels, using their pointwise critical-strip real-part nonnegativity. -/
theorem nontrivialZerosFinset_sum_re_nonnegative_of_weightedSelfDampedAffineResolventLaplaceKernelCombo_re_nonnegative
    (T : ℝ) (K : Finset ℕ) (w κ a b c : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (ha : ∀ k ∈ K, 0 ≤ a k)
    (hb : ∀ k ∈ K, 0 ≤ b k)
    (hc : ∀ k ∈ K, 0 ≤ c k) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset T,
      (weightedKernelCombo K w
        (fun k => dampedKernel (κ k)
          (affineResolventLaplaceKernel (a k) (b k) (c k))
          (affineResolventLaplaceKernel (a k) (b k) (c k))) ρ).re :=
  nontrivialZerosFinset_sum_re_nonnegative_of_re_nonnegative_on_critical_strip
    T (weightedKernelCombo K w
      (fun k => dampedKernel (κ k)
        (affineResolventLaplaceKernel (a k) (b k) (c k))
        (affineResolventLaplaceKernel (a k) (b k) (c k))))
    (weightedSelfDampedAffineResolventLaplaceKernelCombo_re_nonnegative_on_critical_strip
      hw hκ ha hb hc)

/-- Finite nontrivial-zero unpaired real-part average nonnegativity for finite
nonnegative combinations of self-damped affine resolvent/Laplace prototype
kernels, using their pointwise critical-strip real-part nonnegativity. -/
theorem nontrivialZerosFinset_average_re_nonnegative_of_weightedSelfDampedAffineResolventLaplaceKernelCombo_re_nonnegative
    (T : ℝ) (K : Finset ℕ) (w κ a b c : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (ha : ∀ k ∈ K, 0 ≤ a k)
    (hb : ∀ k ∈ K, 0 ≤ b k)
    (hc : ∀ k ∈ K, 0 ≤ c k) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset T,
        (weightedKernelCombo K w
          (fun k => dampedKernel (κ k)
            (affineResolventLaplaceKernel (a k) (b k) (c k))
            (affineResolventLaplaceKernel (a k) (b k) (c k))) ρ).re) /
        ((nontrivialZerosFinset T).card : ℝ) :=
  nontrivialZerosFinset_average_re_nonnegative_of_re_nonnegative_on_critical_strip
    T (weightedKernelCombo K w
      (fun k => dampedKernel (κ k)
        (affineResolventLaplaceKernel (a k) (b k) (c k))
        (affineResolventLaplaceKernel (a k) (b k) (c k))))
    (weightedSelfDampedAffineResolventLaplaceKernelCombo_re_nonnegative_on_critical_strip
      hw hκ ha hb hc)

/-- New-zero unpaired real-part sum nonnegativity for finite nonnegative
combinations of self-damped affine resolvent/Laplace prototype kernels, using
their pointwise critical-strip real-part nonnegativity. -/
theorem nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_weightedSelfDampedAffineResolventLaplaceKernelCombo_re_nonnegative
    (T U : ℝ) (K : Finset ℕ) (w κ a b c : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (ha : ∀ k ∈ K, 0 ≤ a k)
    (hb : ∀ k ∈ K, 0 ≤ b k)
    (hc : ∀ k ∈ K, 0 ≤ c k) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
      (weightedKernelCombo K w
        (fun k => dampedKernel (κ k)
          (affineResolventLaplaceKernel (a k) (b k) (c k))
          (affineResolventLaplaceKernel (a k) (b k) (c k))) ρ).re :=
  nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_re_nonnegative_on_critical_strip
    T U (weightedKernelCombo K w
      (fun k => dampedKernel (κ k)
        (affineResolventLaplaceKernel (a k) (b k) (c k))
        (affineResolventLaplaceKernel (a k) (b k) (c k))))
    (weightedSelfDampedAffineResolventLaplaceKernelCombo_re_nonnegative_on_critical_strip
      hw hκ ha hb hc)

/-- New-zero unpaired real-part average nonnegativity for finite nonnegative
combinations of self-damped affine resolvent/Laplace prototype kernels, using
their pointwise critical-strip real-part nonnegativity. -/
theorem nontrivialZerosFinset_sdiff_average_re_nonnegative_of_weightedSelfDampedAffineResolventLaplaceKernelCombo_re_nonnegative
    (T U : ℝ) (K : Finset ℕ) (w κ a b c : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hκ : ∀ k ∈ K, κ k ≤ 1)
    (ha : ∀ k ∈ K, 0 ≤ a k)
    (hb : ∀ k ∈ K, 0 ≤ b k)
    (hc : ∀ k ∈ K, 0 ≤ c k) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset U \ nontrivialZerosFinset T,
        (weightedKernelCombo K w
          (fun k => dampedKernel (κ k)
            (affineResolventLaplaceKernel (a k) (b k) (c k))
            (affineResolventLaplaceKernel (a k) (b k) (c k))) ρ).re) /
        (((nontrivialZerosFinset U \ nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_sdiff_average_re_nonnegative_of_re_nonnegative_on_critical_strip
    T U (weightedKernelCombo K w
      (fun k => dampedKernel (κ k)
        (affineResolventLaplaceKernel (a k) (b k) (c k))
        (affineResolventLaplaceKernel (a k) (b k) (c k))))
    (weightedSelfDampedAffineResolventLaplaceKernelCombo_re_nonnegative_on_critical_strip
      hw hκ ha hb hc)

/-- Finite nonnegative weighted kernel combinations with center-one
pair-positive summands give a nonnegative real-part sum over height-truncated
nontrivial zeros. -/
lemma nontrivialZerosFinset_sum_re_nonnegative_of_weightedKernelCombo
    (T : ℝ) (K : Finset ℕ) (w : ℕ → ℝ) (F : ℕ → ℂ → ℂ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hF : ∀ k ∈ K, LaplacePairPositive (F k) 1) :
    0 ≤
      ∑ ρ ∈ nontrivialZerosFinset T,
        (weightedKernelCombo K w F ρ).re :=
  nontrivialZerosFinset_sum_re_nonnegative_of_laplace_pair_positive_one
    T (weightedKernelCombo K w F)
    (laplacePairPositive_one_weightedKernelCombo hw hF)

/-- Finite nonnegative weighted kernel combinations with center-one
pair-positive summands give a nonnegative average real-part contribution over
height-truncated nontrivial zeros. -/
lemma nontrivialZerosFinset_average_re_nonnegative_of_weightedKernelCombo
    (T : ℝ) (K : Finset ℕ) (w : ℕ → ℝ) (F : ℕ → ℂ → ℂ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hF : ∀ k ∈ K, LaplacePairPositive (F k) 1) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset T,
        (weightedKernelCombo K w F ρ).re) /
        (((nontrivialZerosFinset T).card : ℝ)) :=
  div_nonneg
    (nontrivialZerosFinset_sum_re_nonnegative_of_weightedKernelCombo
      T K w F hw hF)
    (Nat.cast_nonneg _)

/-- Finite nonnegative weighted kernel combinations with center-one
pair-positive summands give a nonnegative paired sum over height-truncated
nontrivial zeros. -/
lemma nontrivialZerosFinset_pair_sum_nonnegative_of_weightedKernelCombo
    (T : ℝ) (K : Finset ℕ) (w : ℕ → ℝ) (F : ℕ → ℂ → ℂ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hF : ∀ k ∈ K, LaplacePairPositive (F k) 1) :
    0 ≤
      ∑ ρ ∈ nontrivialZerosFinset T,
        ((weightedKernelCombo K w F ρ).re +
          (weightedKernelCombo K w F (1 - ρ)).re) :=
  nontrivialZerosFinset_pair_sum_nonnegative_of_laplace_pair_positive_one
    T (weightedKernelCombo K w F)
    (laplacePairPositive_one_weightedKernelCombo hw hF)

/-- Finite nonnegative weighted kernel combinations with center-one
pair-positive summands give a nonnegative paired average over height-truncated
nontrivial zeros. -/
lemma nontrivialZerosFinset_pair_average_nonnegative_of_weightedKernelCombo
    (T : ℝ) (K : Finset ℕ) (w : ℕ → ℝ) (F : ℕ → ℂ → ℂ)
    (hw : ∀ k ∈ K, 0 ≤ w k)
    (hF : ∀ k ∈ K, LaplacePairPositive (F k) 1) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset T,
        ((weightedKernelCombo K w F ρ).re +
          (weightedKernelCombo K w F (1 - ρ)).re)) /
        (((nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_pair_average_nonnegative_of_laplace_pair_positive_one
    T (weightedKernelCombo K w F)
    (laplacePairPositive_one_weightedKernelCombo hw hF)

/-- The resolvent/Laplace prototype gives a nonnegative real-part sum over
height-truncated nontrivial zeros. -/
lemma nontrivialZerosFinset_sum_re_nonnegative_of_resolventLaplaceKernel
    (T a : ℝ) (ha : 0 ≤ a) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset T, (resolventLaplaceKernel a ρ).re :=
  nontrivialZerosFinset_sum_re_nonnegative_of_re_nonnegative_on_critical_strip
    T (resolventLaplaceKernel a)
    (resolventLaplaceKernel_re_nonnegative_on_critical_strip ha)

/-- The resolvent/Laplace prototype gives a nonnegative average real-part
contribution over height-truncated nontrivial zeros. -/
lemma nontrivialZerosFinset_average_re_nonnegative_of_resolventLaplaceKernel
    (T a : ℝ) (ha : 0 ≤ a) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset T, (resolventLaplaceKernel a ρ).re) /
        (((nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_average_re_nonnegative_of_re_nonnegative_on_critical_strip
    T (resolventLaplaceKernel a)
    (resolventLaplaceKernel_re_nonnegative_on_critical_strip ha)

/-- The resolvent/Laplace prototype gives a nonnegative paired sum over
height-truncated nontrivial zeros. -/
lemma nontrivialZerosFinset_pair_sum_nonnegative_of_resolventLaplaceKernel
    (T a : ℝ) (ha : 0 ≤ a) :
    0 ≤ ∑ ρ ∈ nontrivialZerosFinset T,
      ((resolventLaplaceKernel a ρ).re +
        (resolventLaplaceKernel a (1 - ρ)).re) :=
  nontrivialZerosFinset_pair_sum_nonnegative_of_laplace_pair_positive_one
    T (resolventLaplaceKernel a)
    (laplacePairPositive_one_resolventLaplaceKernel ha)

/-- The resolvent/Laplace prototype gives a nonnegative paired average over
height-truncated nontrivial zeros. -/
lemma nontrivialZerosFinset_pair_average_nonnegative_of_resolventLaplaceKernel
    (T a : ℝ) (ha : 0 ≤ a) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset T,
        ((resolventLaplaceKernel a ρ).re +
          (resolventLaplaceKernel a (1 - ρ)).re)) /
        (((nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_pair_average_nonnegative_of_laplace_pair_positive_one
    T (resolventLaplaceKernel a)
    (laplacePairPositive_one_resolventLaplaceKernel ha)

/-- The center-one symmetric resolvent/Laplace kernel gives a nonnegative
real-part sum over height-truncated nontrivial zeros. -/
lemma nontrivialZerosFinset_sum_re_nonnegative_of_symmetricResolventLaplaceKernel
    (T a : ℝ) (ha : 0 ≤ a) :
    0 ≤
      ∑ ρ ∈ nontrivialZerosFinset T,
        (symmetricResolventLaplaceKernel a 1 ρ).re :=
  nontrivialZerosFinset_sum_re_nonnegative_of_re_nonnegative_on_critical_strip
    T (symmetricResolventLaplaceKernel a 1)
    (symmetricResolventLaplaceKernel_re_nonnegative_on_strip ha)

/-- The center-one symmetric resolvent/Laplace kernel gives a nonnegative
average real-part contribution over height-truncated nontrivial zeros. -/
lemma nontrivialZerosFinset_average_re_nonnegative_of_symmetricResolventLaplaceKernel
    (T a : ℝ) (ha : 0 ≤ a) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset T,
        (symmetricResolventLaplaceKernel a 1 ρ).re) /
        (((nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_average_re_nonnegative_of_re_nonnegative_on_critical_strip
    T (symmetricResolventLaplaceKernel a 1)
    (symmetricResolventLaplaceKernel_re_nonnegative_on_strip ha)

/-- The center-one symmetric resolvent/Laplace kernel gives a nonnegative
paired sum over height-truncated nontrivial zeros. -/
lemma nontrivialZerosFinset_pair_sum_nonnegative_of_symmetricResolventLaplaceKernel
    (T a : ℝ) (ha : 0 ≤ a) :
    0 ≤
      ∑ ρ ∈ nontrivialZerosFinset T,
        ((symmetricResolventLaplaceKernel a 1 ρ).re +
          (symmetricResolventLaplaceKernel a 1 (1 - ρ)).re) :=
  nontrivialZerosFinset_pair_sum_nonnegative_of_laplace_pair_positive_one
    T (symmetricResolventLaplaceKernel a 1)
    (laplacePairPositive_one_symmetricResolventLaplaceKernel ha)

/-- The center-one symmetric resolvent/Laplace kernel gives a nonnegative
paired average over height-truncated nontrivial zeros. -/
lemma nontrivialZerosFinset_pair_average_nonnegative_of_symmetricResolventLaplaceKernel
    (T a : ℝ) (ha : 0 ≤ a) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset T,
        ((symmetricResolventLaplaceKernel a 1 ρ).re +
          (symmetricResolventLaplaceKernel a 1 (1 - ρ)).re)) /
        (((nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_pair_average_nonnegative_of_laplace_pair_positive_one
    T (symmetricResolventLaplaceKernel a 1)
    (laplacePairPositive_one_symmetricResolventLaplaceKernel ha)

/-- The affine resolvent/Laplace prototype gives a nonnegative real-part sum
over height-truncated nontrivial zeros. -/
lemma nontrivialZerosFinset_sum_re_nonnegative_of_affineResolventLaplaceKernel
    (T a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤
      ∑ ρ ∈ nontrivialZerosFinset T,
        (affineResolventLaplaceKernel a b c ρ).re :=
  nontrivialZerosFinset_sum_re_nonnegative_of_re_nonnegative_on_critical_strip
    T (affineResolventLaplaceKernel a b c)
    (affineResolventLaplaceKernel_re_nonnegative_on_critical_strip
      ha hb hc)

/-- The affine resolvent/Laplace prototype gives a nonnegative average
real-part contribution over height-truncated nontrivial zeros. -/
lemma nontrivialZerosFinset_average_re_nonnegative_of_affineResolventLaplaceKernel
    (T a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset T,
        (affineResolventLaplaceKernel a b c ρ).re) /
        (((nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_average_re_nonnegative_of_re_nonnegative_on_critical_strip
    T (affineResolventLaplaceKernel a b c)
    (affineResolventLaplaceKernel_re_nonnegative_on_critical_strip
      ha hb hc)

/-- The affine resolvent/Laplace prototype gives a nonnegative paired sum over
height-truncated nontrivial zeros. -/
lemma nontrivialZerosFinset_pair_sum_nonnegative_of_affineResolventLaplaceKernel
    (T a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤
      ∑ ρ ∈ nontrivialZerosFinset T,
        ((affineResolventLaplaceKernel a b c ρ).re +
          (affineResolventLaplaceKernel a b c (1 - ρ)).re) :=
  nontrivialZerosFinset_pair_sum_nonnegative_of_laplace_pair_positive_one
    T (affineResolventLaplaceKernel a b c)
    (laplacePairPositive_one_affineResolventLaplaceKernel
      ha hb hc)

/-- The affine resolvent/Laplace prototype gives a nonnegative paired average
over height-truncated nontrivial zeros. -/
lemma nontrivialZerosFinset_pair_average_nonnegative_of_affineResolventLaplaceKernel
    (T a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset T,
        ((affineResolventLaplaceKernel a b c ρ).re +
          (affineResolventLaplaceKernel a b c (1 - ρ)).re)) /
        (((nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_pair_average_nonnegative_of_laplace_pair_positive_one
    T (affineResolventLaplaceKernel a b c)
    (laplacePairPositive_one_affineResolventLaplaceKernel
      ha hb hc)

/-- Finite nonnegative resolvent/Laplace combinations give a nonnegative
real-part sum over height-truncated nontrivial zeros. -/
lemma nontrivialZerosFinset_sum_re_nonnegative_of_resolventLaplaceKernelCombo
    (T : ℝ) (K : Finset ℕ) (w a : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k) :
    0 ≤
      ∑ ρ ∈ nontrivialZerosFinset T,
        (resolventLaplaceKernelCombo K w a ρ).re :=
  nontrivialZerosFinset_sum_re_nonnegative_of_re_nonnegative_on_critical_strip
    T (resolventLaplaceKernelCombo K w a)
    (resolventLaplaceKernelCombo_re_nonnegative_on_critical_strip hw ha)

/-- Finite nonnegative resolvent/Laplace combinations give a nonnegative
average real-part contribution over height-truncated nontrivial zeros. -/
lemma nontrivialZerosFinset_average_re_nonnegative_of_resolventLaplaceKernelCombo
    (T : ℝ) (K : Finset ℕ) (w a : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset T,
        (resolventLaplaceKernelCombo K w a ρ).re) /
        (((nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_average_re_nonnegative_of_re_nonnegative_on_critical_strip
    T (resolventLaplaceKernelCombo K w a)
    (resolventLaplaceKernelCombo_re_nonnegative_on_critical_strip hw ha)

/-- Finite nonnegative resolvent/Laplace combinations give a nonnegative
paired sum over height-truncated nontrivial zeros. -/
lemma nontrivialZerosFinset_pair_sum_nonnegative_of_resolventLaplaceKernelCombo
    (T : ℝ) (K : Finset ℕ) (w a : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k) :
    0 ≤
      ∑ ρ ∈ nontrivialZerosFinset T,
        ((resolventLaplaceKernelCombo K w a ρ).re +
          (resolventLaplaceKernelCombo K w a (1 - ρ)).re) :=
  nontrivialZerosFinset_pair_sum_nonnegative_of_laplace_pair_positive_one
    T (resolventLaplaceKernelCombo K w a)
    (laplacePairPositive_one_resolventLaplaceKernelCombo hw ha)

/-- Finite nonnegative resolvent/Laplace combinations give a nonnegative
paired average over height-truncated nontrivial zeros. -/
lemma nontrivialZerosFinset_pair_average_nonnegative_of_resolventLaplaceKernelCombo
    (T : ℝ) (K : Finset ℕ) (w a : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset T,
        ((resolventLaplaceKernelCombo K w a ρ).re +
          (resolventLaplaceKernelCombo K w a (1 - ρ)).re)) /
        (((nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_pair_average_nonnegative_of_laplace_pair_positive_one
    T (resolventLaplaceKernelCombo K w a)
    (laplacePairPositive_one_resolventLaplaceKernelCombo hw ha)

/-- Finite nonnegative combinations of center-one symmetric
resolvent/Laplace kernels give a nonnegative real-part sum over
height-truncated nontrivial zeros. -/
lemma nontrivialZerosFinset_sum_re_nonnegative_of_symmetricResolventLaplaceKernelCombo
    (T : ℝ) (K : Finset ℕ) (w a : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k) :
    0 ≤
      ∑ ρ ∈ nontrivialZerosFinset T,
        (symmetricResolventLaplaceKernelCombo K w a 1 ρ).re :=
  nontrivialZerosFinset_sum_re_nonnegative_of_re_nonnegative_on_critical_strip
    T (symmetricResolventLaplaceKernelCombo K w a 1)
    (symmetricResolventLaplaceKernelCombo_re_nonnegative_on_strip hw ha)

/-- Finite nonnegative combinations of center-one symmetric
resolvent/Laplace kernels give a nonnegative average real-part contribution
over height-truncated nontrivial zeros. -/
lemma nontrivialZerosFinset_average_re_nonnegative_of_symmetricResolventLaplaceKernelCombo
    (T : ℝ) (K : Finset ℕ) (w a : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset T,
        (symmetricResolventLaplaceKernelCombo K w a 1 ρ).re) /
        (((nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_average_re_nonnegative_of_re_nonnegative_on_critical_strip
    T (symmetricResolventLaplaceKernelCombo K w a 1)
    (symmetricResolventLaplaceKernelCombo_re_nonnegative_on_strip hw ha)

/-- Finite nonnegative combinations of center-one symmetric
resolvent/Laplace kernels give a nonnegative paired sum over height-truncated
nontrivial zeros. -/
lemma nontrivialZerosFinset_pair_sum_nonnegative_of_symmetricResolventLaplaceKernelCombo
    (T : ℝ) (K : Finset ℕ) (w a : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k) :
    0 ≤
      ∑ ρ ∈ nontrivialZerosFinset T,
        ((symmetricResolventLaplaceKernelCombo K w a 1 ρ).re +
          (symmetricResolventLaplaceKernelCombo K w a 1 (1 - ρ)).re) :=
  nontrivialZerosFinset_pair_sum_nonnegative_of_laplace_pair_positive_one
    T (symmetricResolventLaplaceKernelCombo K w a 1)
    (laplacePairPositive_one_symmetricResolventLaplaceKernelCombo hw ha)

/-- Finite nonnegative combinations of center-one symmetric
resolvent/Laplace kernels give a nonnegative paired average over
height-truncated nontrivial zeros. -/
lemma nontrivialZerosFinset_pair_average_nonnegative_of_symmetricResolventLaplaceKernelCombo
    (T : ℝ) (K : Finset ℕ) (w a : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset T,
        ((symmetricResolventLaplaceKernelCombo K w a 1 ρ).re +
          (symmetricResolventLaplaceKernelCombo K w a 1 (1 - ρ)).re)) /
        (((nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_pair_average_nonnegative_of_laplace_pair_positive_one
    T (symmetricResolventLaplaceKernelCombo K w a 1)
    (laplacePairPositive_one_symmetricResolventLaplaceKernelCombo hw ha)

/-- Finite nonnegative affine resolvent/Laplace combinations give a
nonnegative real-part sum over height-truncated nontrivial zeros. -/
lemma nontrivialZerosFinset_sum_re_nonnegative_of_affineResolventLaplaceKernelCombo
    (T : ℝ) (K : Finset ℕ) (w a b c : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k)
    (hb : ∀ k ∈ K, 0 ≤ b k) (hc : ∀ k ∈ K, 0 ≤ c k) :
    0 ≤
      ∑ ρ ∈ nontrivialZerosFinset T,
        (affineResolventLaplaceKernelCombo K w a b c ρ).re :=
  nontrivialZerosFinset_sum_re_nonnegative_of_re_nonnegative_on_critical_strip
    T (affineResolventLaplaceKernelCombo K w a b c)
    (affineResolventLaplaceKernelCombo_re_nonnegative_on_critical_strip
      hw ha hb hc)

/-- Finite nonnegative affine resolvent/Laplace combinations give a
nonnegative average real-part contribution over height-truncated nontrivial
zeros. -/
lemma nontrivialZerosFinset_average_re_nonnegative_of_affineResolventLaplaceKernelCombo
    (T : ℝ) (K : Finset ℕ) (w a b c : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k)
    (hb : ∀ k ∈ K, 0 ≤ b k) (hc : ∀ k ∈ K, 0 ≤ c k) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset T,
        (affineResolventLaplaceKernelCombo K w a b c ρ).re) /
        (((nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_average_re_nonnegative_of_re_nonnegative_on_critical_strip
    T (affineResolventLaplaceKernelCombo K w a b c)
    (affineResolventLaplaceKernelCombo_re_nonnegative_on_critical_strip
      hw ha hb hc)

/-- Finite nonnegative affine resolvent/Laplace combinations give a
nonnegative paired sum over height-truncated nontrivial zeros. -/
lemma nontrivialZerosFinset_pair_sum_nonnegative_of_affineResolventLaplaceKernelCombo
    (T : ℝ) (K : Finset ℕ) (w a b c : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k)
    (hb : ∀ k ∈ K, 0 ≤ b k) (hc : ∀ k ∈ K, 0 ≤ c k) :
    0 ≤
      ∑ ρ ∈ nontrivialZerosFinset T,
        ((affineResolventLaplaceKernelCombo K w a b c ρ).re +
          (affineResolventLaplaceKernelCombo K w a b c (1 - ρ)).re) :=
  nontrivialZerosFinset_pair_sum_nonnegative_of_laplace_pair_positive_one
    T (affineResolventLaplaceKernelCombo K w a b c)
    (laplacePairPositive_one_affineResolventLaplaceKernelCombo
      hw ha hb hc)

/-- Finite nonnegative affine resolvent/Laplace combinations give a
nonnegative paired average over height-truncated nontrivial zeros. -/
lemma nontrivialZerosFinset_pair_average_nonnegative_of_affineResolventLaplaceKernelCombo
    (T : ℝ) (K : Finset ℕ) (w a b c : ℕ → ℝ)
    (hw : ∀ k ∈ K, 0 ≤ w k) (ha : ∀ k ∈ K, 0 ≤ a k)
    (hb : ∀ k ∈ K, 0 ≤ b k) (hc : ∀ k ∈ K, 0 ≤ c k) :
    0 ≤
      (∑ ρ ∈ nontrivialZerosFinset T,
        ((affineResolventLaplaceKernelCombo K w a b c ρ).re +
          (affineResolventLaplaceKernelCombo K w a b c (1 - ρ)).re)) /
        (((nontrivialZerosFinset T).card : ℝ)) :=
  nontrivialZerosFinset_pair_average_nonnegative_of_laplace_pair_positive_one
    T (affineResolventLaplaceKernelCombo K w a b c)
    (laplacePairPositive_one_affineResolventLaplaceKernelCombo
      hw ha hb hc)

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

/-- The change in the finite nontrivial-zero sum between two height cutoffs is
bounded by the sum of the norms of the newly included zero contributions. -/
lemma norm_finiteNontrivialZeroSum_sub_le_new_zeros_sum_norm
    {x T U : ℝ} (hTU : T ≤ U) :
    ‖finiteNontrivialZeroSum x U - finiteNontrivialZeroSum x T‖ ≤
      ∑ ρ ∈ (nontrivialZerosFinset U \ nontrivialZerosFinset T),
        ‖(x : ℂ) ^ ρ / ρ‖ := by
  rw [finiteNontrivialZeroSum_sub_eq_new_zeros hTU]
  exact norm_sum_le _ _

lemma finiteNontrivialZeroSum_eq_of_sdiff_eq_empty
    {x T U : ℝ} (hTU : T ≤ U)
    (hnew : nontrivialZerosFinset U \ nontrivialZerosFinset T = ∅) :
    finiteNontrivialZeroSum x U = finiteNontrivialZeroSum x T := by
  have h := finiteNontrivialZeroSum_eq_add_new_zeros (x := x) hTU
  simpa [hnew] using h

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

lemma explicitFormulaApprox_eq_of_sdiff_eq_empty
    {x T U : ℝ} (hTU : T ≤ U)
    (hnew : nontrivialZerosFinset U \ nontrivialZerosFinset T = ∅) :
    explicitFormulaApprox x U = explicitFormulaApprox x T := by
  rw [explicitFormulaApprox_eq_sub_new_zeros (x := x) hTU]
  simp [hnew]

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

/-- Triangle-inequality bound for the change in explicit-formula truncations
by the newly included zero contributions. -/
lemma norm_explicitFormulaApprox_sub_le_new_zeros_sum_norm
    {x T U : ℝ} (hTU : T ≤ U) :
    ‖explicitFormulaApprox x T - explicitFormulaApprox x U‖ ≤
      ∑ ρ ∈ (nontrivialZerosFinset U \ nontrivialZerosFinset T),
        ‖(x : ℂ) ^ ρ / ρ‖ := by
  rw [explicitFormulaApprox_sub_norm_eq_new_zeros hTU]
  exact norm_sum_le _ _

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

/-- A global height bound on nontrivial zeros implies that, eventually, no new
zeros appear above the base cutoff. -/
lemma nontrivialZerosFinset_eventually_sdiff_eq_empty_of_global_height_bound
    {B : ℝ}
    (hbound : ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → |ρ.im| ≤ B) :
    ∀ᶠ T in atTop, nontrivialZerosFinset T \ nontrivialZerosFinset B = ∅ := by
  filter_upwards [eventually_ge_atTop B] with T hBT
  rw [nontrivialZerosFinset_eq_of_global_height_bound hBT hbound]
  simp

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

/-- Legacy symmetric-height target whose zero sum omits multiplicity.

This predicate is retained only for the existing conditional helper API.  It
is not the mathematically correct final explicit formula unless every
nontrivial zeta zero is simple, which is unknown. -/
def explicit_formula_von_mangoldt_unweighted (x : ℝ) (_hx : x ≥ 2) : Prop :=
  Tendsto
    (fun T : ℝ => explicitFormulaApprox x T)
    atTop
    (𝓝 (chebyshevPsi0 x : ℂ))

/-- Multiplicity-aware symmetric-height approximation in the von Mangoldt
explicit formula. -/
noncomputable def explicitFormulaApproxWithMultiplicity (x T : ℝ) : ℂ :=
  (x : ℂ)
    - finiteNontrivialZeroSumWithMultiplicity x T
    - deriv riemannZeta 0 / riemannZeta 0
    - (1 / 2 : ℂ) * (Real.log (1 - x^(-2 : ℝ)) : ℂ)

/-- Correct target shape for the von Mangoldt explicit formula.

The midpoint function `ψ₀` handles prime-power discontinuities, the height
cutoff gives the symmetric summation convention, and `analyticOrderNatAt`
counts every nontrivial zero with its analytic multiplicity.  This remains a
target statement until the proved cofinal contour limit is promoted to all
real truncation heights. -/
def explicit_formula_von_mangoldt (x : ℝ) (_hx : x ≥ 2) : Prop :=
  Tendsto
    (fun T : ℝ => explicitFormulaApproxWithMultiplicity x T)
    atTop
    (𝓝 (chebyshevPsi0 x : ℂ))

lemma finiteNontrivialZeroSumWithMultiplicity_eq_add_new_zeros
    {x T U : ℝ} (hTU : T ≤ U) :
    finiteNontrivialZeroSumWithMultiplicity x U =
      finiteNontrivialZeroSumWithMultiplicity x T +
        ∑ ρ ∈ (nontrivialZerosFinset U \ nontrivialZerosFinset T),
          (analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ := by
  classical
  have hsubset : nontrivialZerosFinset T ⊆ nontrivialZerosFinset U := by
    intro ρ hρ
    exact nontrivialZerosFinset_mono hTU hρ
  rw [finiteNontrivialZeroSumWithMultiplicity,
    finiteNontrivialZeroSumWithMultiplicity]
  have hsum :
      (∑ ρ ∈ (nontrivialZerosFinset U \ nontrivialZerosFinset T),
          (analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ) +
        (∑ ρ ∈ nontrivialZerosFinset T,
          (analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ) =
      ∑ ρ ∈ nontrivialZerosFinset U,
        (analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ :=
    Finset.sum_sdiff (s₁ := nontrivialZerosFinset T)
      (s₂ := nontrivialZerosFinset U)
      (f := fun ρ : ℂ =>
        (analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ) hsubset
  rw [← hsum]
  abel

lemma explicitFormulaApproxWithMultiplicity_sub_eq_new_zeros
    {x T U : ℝ} (hTU : T ≤ U) :
    explicitFormulaApproxWithMultiplicity x T -
        explicitFormulaApproxWithMultiplicity x U =
      ∑ ρ ∈ (nontrivialZerosFinset U \ nontrivialZerosFinset T),
        (analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ := by
  simp only [explicitFormulaApproxWithMultiplicity]
  rw [finiteNontrivialZeroSumWithMultiplicity_eq_add_new_zeros hTU]
  abel

lemma norm_explicitFormulaApproxWithMultiplicity_sub_le_new_zeros_sum_norm
    {x T U : ℝ} (hTU : T ≤ U) :
    ‖explicitFormulaApproxWithMultiplicity x T -
        explicitFormulaApproxWithMultiplicity x U‖ ≤
      ∑ ρ ∈ (nontrivialZerosFinset U \ nontrivialZerosFinset T),
        ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ := by
  rw [explicitFormulaApproxWithMultiplicity_sub_eq_new_zeros hTU]
  exact norm_sum_le _ _

lemma explicit_formula_von_mangoldt_iff {x : ℝ} {hx : x ≥ 2} :
    explicit_formula_von_mangoldt x hx ↔
      Tendsto (fun T : ℝ => explicitFormulaApproxWithMultiplicity x T)
        atTop (𝓝 (chebyshevPsi0 x : ℂ)) := by
  rfl

lemma explicit_formula_von_mangoldt_of_eventually_eq {x : ℝ} {hx : x ≥ 2}
    {F : ℝ → ℂ}
    (hF : F =ᶠ[atTop]
      fun T : ℝ => explicitFormulaApproxWithMultiplicity x T)
    (h : Tendsto F atTop (𝓝 (chebyshevPsi0 x : ℂ))) :
    explicit_formula_von_mangoldt x hx := by
  exact Tendsto.congr' hF h

lemma explicit_formula_von_mangoldt_of_eventually_exact {x : ℝ} {hx : x ≥ 2}
    (h : ∀ᶠ T in atTop,
      explicitFormulaApproxWithMultiplicity x T = (chebyshevPsi0 x : ℂ)) :
    explicit_formula_von_mangoldt x hx := by
  exact tendsto_nhds_of_eventually_eq h

lemma explicit_formula_von_mangoldt_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2} (h : explicit_formula_von_mangoldt x hx) :
    Tendsto (fun T : ℝ =>
      explicitFormulaApproxWithMultiplicity x T - (chebyshevPsi0 x : ℂ))
      atTop (𝓝 0) := by
  simpa [explicit_formula_von_mangoldt] using
    h.sub (tendsto_const_nhds : Tendsto
      (fun _T : ℝ => (chebyshevPsi0 x : ℂ)) atTop
      (𝓝 (chebyshevPsi0 x : ℂ)))

lemma explicit_formula_von_mangoldt_of_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2}
    (h : Tendsto (fun T : ℝ =>
      explicitFormulaApproxWithMultiplicity x T - (chebyshevPsi0 x : ℂ))
      atTop (𝓝 0)) :
    explicit_formula_von_mangoldt x hx := by
  have hsum := h.add (tendsto_const_nhds : Tendsto
    (fun _T : ℝ => (chebyshevPsi0 x : ℂ)) atTop
    (𝓝 (chebyshevPsi0 x : ℂ)))
  simpa only [sub_add_cancel, zero_add] using hsum

lemma explicit_formula_von_mangoldt_iff_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2} :
    explicit_formula_von_mangoldt x hx ↔
      Tendsto (fun T : ℝ =>
        explicitFormulaApproxWithMultiplicity x T - (chebyshevPsi0 x : ℂ))
        atTop (𝓝 0) :=
  ⟨explicit_formula_von_mangoldt_error_tendsto_zero,
    explicit_formula_von_mangoldt_of_error_tendsto_zero⟩

lemma explicit_formula_von_mangoldt_unweighted_iff {x : ℝ} {hx : x ≥ 2} :
    explicit_formula_von_mangoldt_unweighted x hx ↔
      Tendsto (fun T : ℝ => explicitFormulaApprox x T) atTop
        (𝓝 (chebyshevPsi0 x : ℂ)) := by
  rfl

lemma explicit_formula_von_mangoldt_unweighted_of_eventually_eq {x : ℝ} {hx : x ≥ 2}
    {F : ℝ → ℂ}
    (hF : F =ᶠ[atTop] fun T : ℝ => explicitFormulaApprox x T)
    (h : Tendsto F atTop (𝓝 (chebyshevPsi0 x : ℂ))) :
    explicit_formula_von_mangoldt_unweighted x hx := by
  exact Tendsto.congr' hF h

lemma explicit_formula_von_mangoldt_unweighted_of_eventually_exact {x : ℝ} {hx : x ≥ 2}
    (h : ∀ᶠ T in atTop, explicitFormulaApprox x T = (chebyshevPsi0 x : ℂ)) :
    explicit_formula_von_mangoldt_unweighted x hx := by
  exact tendsto_nhds_of_eventually_eq h

lemma explicit_formula_von_mangoldt_unweighted_of_global_height_bound_exact
    {x B : ℝ} {hx : x ≥ 2}
    (hbound : ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → |ρ.im| ≤ B)
    (hB : explicitFormulaApprox x B = (chebyshevPsi0 x : ℂ)) :
    explicit_formula_von_mangoldt_unweighted x hx := by
  refine explicit_formula_von_mangoldt_unweighted_of_eventually_exact ?_
  exact (explicitFormulaApprox_eventually_eq_of_global_height_bound
    (x := x) (B := B) hbound).mono fun _T hT => by
      simpa using hT.trans hB

lemma explicit_formula_von_mangoldt_unweighted_of_eventually_no_new_zeros
    {x B : ℝ} {hx : x ≥ 2}
    (hnew : ∀ᶠ T in atTop,
      B ≤ T ∧ nontrivialZerosFinset T \ nontrivialZerosFinset B = ∅)
    (hB : explicitFormulaApprox x B = (chebyshevPsi0 x : ℂ)) :
    explicit_formula_von_mangoldt_unweighted x hx := by
  refine explicit_formula_von_mangoldt_unweighted_of_eventually_exact ?_
  filter_upwards [hnew] with T hT
  exact (explicitFormulaApprox_eq_of_sdiff_eq_empty
    (x := x) hT.1 hT.2).trans hB

lemma explicitFormulaApprox_eq_chebyshevPsi0_of_global_height_bound
    {x B : ℝ} {hx : x ≥ 2}
    (hbound : ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → |ρ.im| ≤ B)
    (h : explicit_formula_von_mangoldt_unweighted x hx) :
    explicitFormulaApprox x B = (chebyshevPsi0 x : ℂ) := by
  have hconst :
      Tendsto (fun _T : ℝ => explicitFormulaApprox x B) atTop
        (𝓝 (chebyshevPsi0 x : ℂ)) :=
    Tendsto.congr'
      (explicitFormulaApprox_eventually_eq_of_global_height_bound
        (x := x) (B := B) hbound) h
  exact tendsto_nhds_unique tendsto_const_nhds hconst

lemma explicit_formula_von_mangoldt_unweighted_iff_global_height_bound_exact
    {x B : ℝ} {hx : x ≥ 2}
    (hbound : ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → |ρ.im| ≤ B) :
    explicit_formula_von_mangoldt_unweighted x hx ↔
      explicitFormulaApprox x B = (chebyshevPsi0 x : ℂ) :=
  ⟨explicitFormulaApprox_eq_chebyshevPsi0_of_global_height_bound hbound,
    explicit_formula_von_mangoldt_unweighted_of_global_height_bound_exact hbound⟩

lemma explicit_formula_von_mangoldt_unweighted_of_error_tendsto_zero {x : ℝ} {hx : x ≥ 2}
    (h : Tendsto (fun T : ℝ =>
      explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ)) atTop (𝓝 0)) :
    explicit_formula_von_mangoldt_unweighted x hx := by
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

lemma explicit_formula_von_mangoldt_unweighted_error_tendsto_zero {x : ℝ} {hx : x ≥ 2}
    (h : explicit_formula_von_mangoldt_unweighted x hx) :
    Tendsto (fun T : ℝ =>
      explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ)) atTop (𝓝 0) := by
  have hconst : Tendsto (fun _T : ℝ => (chebyshevPsi0 x : ℂ)) atTop
      (𝓝 (chebyshevPsi0 x : ℂ)) :=
    tendsto_const_nhds
  simpa [explicit_formula_von_mangoldt_unweighted] using h.sub hconst

lemma explicit_formula_von_mangoldt_unweighted_iff_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2} :
    explicit_formula_von_mangoldt_unweighted x hx ↔
      Tendsto (fun T : ℝ =>
        explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ)) atTop (𝓝 0) :=
  ⟨explicit_formula_von_mangoldt_unweighted_error_tendsto_zero,
    explicit_formula_von_mangoldt_unweighted_of_error_tendsto_zero⟩

lemma explicit_formula_von_mangoldt_unweighted_iff_reverse_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2} :
    explicit_formula_von_mangoldt_unweighted x hx ↔
      Tendsto (fun T : ℝ =>
        (chebyshevPsi0 x : ℂ) - explicitFormulaApprox x T) atTop (𝓝 0) := by
  constructor
  · intro h
    have hz := explicit_formula_von_mangoldt_unweighted_error_tendsto_zero h
    have hneg := hz.neg
    simpa [sub_eq_add_neg, add_comm] using hneg
  · intro h
    have hneg := h.neg
    have hz :
        Tendsto (fun T : ℝ =>
          explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ)) atTop (𝓝 0) := by
      simpa [sub_eq_add_neg, add_comm] using hneg
    exact explicit_formula_von_mangoldt_unweighted_of_error_tendsto_zero hz

lemma explicit_formula_von_mangoldt_unweighted_reverse_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (h : explicit_formula_von_mangoldt_unweighted x hx) :
    (fun T : ℝ => (chebyshevPsi0 x : ℂ) - explicitFormulaApprox x T)
        =o[atTop] (fun _T : ℝ => (1 : ℂ)) :=
  (isLittleO_one_iff ℂ).mpr
    ((explicit_formula_von_mangoldt_unweighted_iff_reverse_error_tendsto_zero).mp h)

lemma explicit_formula_von_mangoldt_unweighted_of_reverse_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (h : (fun T : ℝ => (chebyshevPsi0 x : ℂ) - explicitFormulaApprox x T)
        =o[atTop] (fun _T : ℝ => (1 : ℂ))) :
    explicit_formula_von_mangoldt_unweighted x hx :=
  (explicit_formula_von_mangoldt_unweighted_iff_reverse_error_tendsto_zero).mpr
    ((isLittleO_one_iff ℂ).mp h)

lemma explicit_formula_von_mangoldt_unweighted_iff_reverse_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2} :
    explicit_formula_von_mangoldt_unweighted x hx ↔
      (fun T : ℝ => (chebyshevPsi0 x : ℂ) - explicitFormulaApprox x T)
        =o[atTop] (fun _T : ℝ => (1 : ℂ)) :=
  ⟨explicit_formula_von_mangoldt_unweighted_reverse_error_isLittleO_one,
    explicit_formula_von_mangoldt_unweighted_of_reverse_error_isLittleO_one⟩

lemma explicit_formula_von_mangoldt_unweighted_of_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (h : (fun T : ℝ => explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ))
        =o[atTop] (fun _T : ℝ => (1 : ℂ))) :
    explicit_formula_von_mangoldt_unweighted x hx :=
  explicit_formula_von_mangoldt_unweighted_of_error_tendsto_zero
    ((isLittleO_one_iff ℂ).mp h)

lemma explicit_formula_von_mangoldt_unweighted_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (h : explicit_formula_von_mangoldt_unweighted x hx) :
    (fun T : ℝ => explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ))
        =o[atTop] (fun _T : ℝ => (1 : ℂ)) :=
  (isLittleO_one_iff ℂ).mpr
    (explicit_formula_von_mangoldt_unweighted_error_tendsto_zero h)

lemma explicit_formula_von_mangoldt_unweighted_iff_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2} :
    explicit_formula_von_mangoldt_unweighted x hx ↔
      (fun T : ℝ => explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ))
        =o[atTop] (fun _T : ℝ => (1 : ℂ)) :=
  ⟨explicit_formula_von_mangoldt_unweighted_error_isLittleO_one,
    explicit_formula_von_mangoldt_unweighted_of_error_isLittleO_one⟩

lemma explicit_formula_von_mangoldt_unweighted_re_tendsto
    {x : ℝ} {hx : x ≥ 2}
    (h : explicit_formula_von_mangoldt_unweighted x hx) :
    Tendsto (fun T : ℝ => (explicitFormulaApprox x T).re) atTop
      (𝓝 (chebyshevPsi0 x)) := by
  simpa [explicit_formula_von_mangoldt_unweighted] using
    (Complex.continuous_re.tendsto (chebyshevPsi0 x : ℂ)).comp h

lemma explicit_formula_von_mangoldt_unweighted_im_tendsto_zero
    {x : ℝ} {hx : x ≥ 2}
    (h : explicit_formula_von_mangoldt_unweighted x hx) :
    Tendsto (fun T : ℝ => (explicitFormulaApprox x T).im) atTop (𝓝 0) := by
  simpa [explicit_formula_von_mangoldt_unweighted] using
    (Complex.continuous_im.tendsto (chebyshevPsi0 x : ℂ)).comp h

lemma explicit_formula_von_mangoldt_unweighted_re_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2}
    (h : explicit_formula_von_mangoldt_unweighted x hx) :
    Tendsto (fun T : ℝ => (explicitFormulaApprox x T).re - chebyshevPsi0 x)
      atTop (𝓝 0) := by
  simpa using
    (Complex.continuous_re.tendsto (0 : ℂ)).comp
      (explicit_formula_von_mangoldt_unweighted_error_tendsto_zero h)

lemma explicit_formula_von_mangoldt_unweighted_im_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2}
    (h : explicit_formula_von_mangoldt_unweighted x hx) :
    Tendsto (fun T : ℝ => (explicitFormulaApprox x T).im) atTop (𝓝 0) :=
  explicit_formula_von_mangoldt_unweighted_im_tendsto_zero h

lemma explicit_formula_von_mangoldt_unweighted_of_re_im_tendsto
    {x : ℝ} {hx : x ≥ 2}
    (hre : Tendsto (fun T : ℝ => (explicitFormulaApprox x T).re) atTop
      (𝓝 (chebyshevPsi0 x)))
    (him : Tendsto (fun T : ℝ => (explicitFormulaApprox x T).im) atTop
      (𝓝 0)) :
    explicit_formula_von_mangoldt_unweighted x hx := by
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
  simpa [explicit_formula_von_mangoldt_unweighted] using
    hsum.congr' (Filter.EventuallyEq.of_eq h_eq)

lemma explicit_formula_von_mangoldt_unweighted_of_re_im_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2}
    (hre : Tendsto
      (fun T : ℝ => (explicitFormulaApprox x T).re - chebyshevPsi0 x)
      atTop (𝓝 0))
    (him : Tendsto (fun T : ℝ => (explicitFormulaApprox x T).im)
      atTop (𝓝 0)) :
    explicit_formula_von_mangoldt_unweighted x hx := by
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
  exact explicit_formula_von_mangoldt_unweighted_of_re_im_tendsto
    (by simpa using hsum.congr' (Filter.EventuallyEq.of_eq h_eq)) him

lemma explicit_formula_von_mangoldt_unweighted_iff_re_im_tendsto
    {x : ℝ} {hx : x ≥ 2} :
    explicit_formula_von_mangoldt_unweighted x hx ↔
      Tendsto (fun T : ℝ => (explicitFormulaApprox x T).re) atTop
        (𝓝 (chebyshevPsi0 x)) ∧
      Tendsto (fun T : ℝ => (explicitFormulaApprox x T).im) atTop (𝓝 0) :=
  ⟨fun h => ⟨explicit_formula_von_mangoldt_unweighted_re_tendsto h,
      explicit_formula_von_mangoldt_unweighted_im_tendsto_zero h⟩,
    fun h => explicit_formula_von_mangoldt_unweighted_of_re_im_tendsto h.1 h.2⟩

lemma explicit_formula_von_mangoldt_unweighted_iff_re_im_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2} :
    explicit_formula_von_mangoldt_unweighted x hx ↔
      Tendsto
        (fun T : ℝ => (explicitFormulaApprox x T).re - chebyshevPsi0 x)
        atTop (𝓝 0) ∧
      Tendsto (fun T : ℝ => (explicitFormulaApprox x T).im) atTop (𝓝 0) :=
  ⟨fun h => ⟨explicit_formula_von_mangoldt_unweighted_re_error_tendsto_zero h,
      explicit_formula_von_mangoldt_unweighted_im_error_tendsto_zero h⟩,
    fun h => explicit_formula_von_mangoldt_unweighted_of_re_im_error_tendsto_zero h.1 h.2⟩

lemma explicit_formula_von_mangoldt_unweighted_re_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (h : explicit_formula_von_mangoldt_unweighted x hx) :
    (fun T : ℝ => (explicitFormulaApprox x T).re - chebyshevPsi0 x)
        =o[atTop] (fun _T : ℝ => (1 : ℝ)) :=
  (isLittleO_one_iff ℝ).mpr
    (explicit_formula_von_mangoldt_unweighted_re_error_tendsto_zero h)

lemma explicit_formula_von_mangoldt_unweighted_im_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (h : explicit_formula_von_mangoldt_unweighted x hx) :
    (fun T : ℝ => (explicitFormulaApprox x T).im)
        =o[atTop] (fun _T : ℝ => (1 : ℝ)) :=
  (isLittleO_one_iff ℝ).mpr
    (explicit_formula_von_mangoldt_unweighted_im_error_tendsto_zero h)

lemma explicit_formula_von_mangoldt_unweighted_of_re_im_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (hre :
      (fun T : ℝ => (explicitFormulaApprox x T).re - chebyshevPsi0 x)
        =o[atTop] (fun _T : ℝ => (1 : ℝ)))
    (him : (fun T : ℝ => (explicitFormulaApprox x T).im)
        =o[atTop] (fun _T : ℝ => (1 : ℝ))) :
    explicit_formula_von_mangoldt_unweighted x hx :=
  explicit_formula_von_mangoldt_unweighted_of_re_im_error_tendsto_zero
    ((isLittleO_one_iff ℝ).mp hre)
    ((isLittleO_one_iff ℝ).mp him)

lemma explicit_formula_von_mangoldt_unweighted_iff_re_im_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2} :
    explicit_formula_von_mangoldt_unweighted x hx ↔
      (fun T : ℝ => (explicitFormulaApprox x T).re - chebyshevPsi0 x)
        =o[atTop] (fun _T : ℝ => (1 : ℝ)) ∧
      (fun T : ℝ => (explicitFormulaApprox x T).im)
        =o[atTop] (fun _T : ℝ => (1 : ℝ)) :=
  ⟨fun h => ⟨explicit_formula_von_mangoldt_unweighted_re_error_isLittleO_one h,
      explicit_formula_von_mangoldt_unweighted_im_error_isLittleO_one h⟩,
    fun h => explicit_formula_von_mangoldt_unweighted_of_re_im_error_isLittleO_one h.1 h.2⟩

lemma explicit_formula_von_mangoldt_unweighted_norm_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2}
    (h : explicit_formula_von_mangoldt_unweighted x hx) :
    Tendsto (fun T : ℝ =>
      ‖explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ)‖) atTop (𝓝 0) :=
  tendsto_zero_iff_norm_tendsto_zero.mp
    (explicit_formula_von_mangoldt_unweighted_error_tendsto_zero h)

lemma explicit_formula_von_mangoldt_unweighted_reverse_norm_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2}
    (h : explicit_formula_von_mangoldt_unweighted x hx) :
    Tendsto (fun T : ℝ =>
      ‖(chebyshevPsi0 x : ℂ) - explicitFormulaApprox x T‖) atTop (𝓝 0) := by
  have hnorm := explicit_formula_von_mangoldt_unweighted_norm_error_tendsto_zero h
  have h_eq :
      (fun T : ℝ => ‖(chebyshevPsi0 x : ℂ) - explicitFormulaApprox x T‖) =
        fun T : ℝ => ‖explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ)‖ := by
    funext T
    rw [norm_sub_rev]
  simpa [h_eq] using hnorm

lemma explicit_formula_von_mangoldt_unweighted_of_norm_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2}
    (h : Tendsto (fun T : ℝ =>
      ‖explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ)‖) atTop (𝓝 0)) :
    explicit_formula_von_mangoldt_unweighted x hx :=
  explicit_formula_von_mangoldt_unweighted_of_error_tendsto_zero
    (tendsto_zero_iff_norm_tendsto_zero.mpr h)

lemma explicit_formula_von_mangoldt_unweighted_of_reverse_norm_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2}
    (h : Tendsto (fun T : ℝ =>
      ‖(chebyshevPsi0 x : ℂ) - explicitFormulaApprox x T‖) atTop (𝓝 0)) :
    explicit_formula_von_mangoldt_unweighted x hx := by
  refine explicit_formula_von_mangoldt_unweighted_of_norm_error_tendsto_zero ?_
  have h_eq :
      (fun T : ℝ => ‖explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ)‖) =
        fun T : ℝ => ‖(chebyshevPsi0 x : ℂ) - explicitFormulaApprox x T‖ := by
    funext T
    rw [norm_sub_rev]
  simpa [h_eq] using h

lemma explicit_formula_von_mangoldt_unweighted_iff_reverse_norm_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2} :
    explicit_formula_von_mangoldt_unweighted x hx ↔
      Tendsto (fun T : ℝ =>
        ‖(chebyshevPsi0 x : ℂ) - explicitFormulaApprox x T‖) atTop (𝓝 0) :=
  ⟨explicit_formula_von_mangoldt_unweighted_reverse_norm_error_tendsto_zero,
    explicit_formula_von_mangoldt_unweighted_of_reverse_norm_error_tendsto_zero⟩

lemma explicit_formula_von_mangoldt_unweighted_reverse_norm_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (h : explicit_formula_von_mangoldt_unweighted x hx) :
    (fun T : ℝ =>
      ‖(chebyshevPsi0 x : ℂ) - explicitFormulaApprox x T‖)
        =o[atTop] (fun _T : ℝ => (1 : ℝ)) :=
  (isLittleO_one_iff ℝ).mpr
    (explicit_formula_von_mangoldt_unweighted_reverse_norm_error_tendsto_zero h)

lemma explicit_formula_von_mangoldt_unweighted_of_reverse_norm_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (h : (fun T : ℝ =>
      ‖(chebyshevPsi0 x : ℂ) - explicitFormulaApprox x T‖)
        =o[atTop] (fun _T : ℝ => (1 : ℝ))) :
    explicit_formula_von_mangoldt_unweighted x hx :=
  explicit_formula_von_mangoldt_unweighted_of_reverse_norm_error_tendsto_zero
    ((isLittleO_one_iff ℝ).mp h)

lemma explicit_formula_von_mangoldt_unweighted_iff_reverse_norm_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2} :
    explicit_formula_von_mangoldt_unweighted x hx ↔
      (fun T : ℝ =>
        ‖(chebyshevPsi0 x : ℂ) - explicitFormulaApprox x T‖)
          =o[atTop] (fun _T : ℝ => (1 : ℝ)) :=
  ⟨explicit_formula_von_mangoldt_unweighted_reverse_norm_error_isLittleO_one,
    explicit_formula_von_mangoldt_unweighted_of_reverse_norm_error_isLittleO_one⟩

lemma explicit_formula_von_mangoldt_unweighted_of_eventually_norm_le
    {x : ℝ} {hx : x ≥ 2} {E : ℝ → ℝ}
    (hE : Tendsto E atTop (𝓝 0))
    (hbound : ∀ᶠ T in atTop,
      ‖explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ)‖ ≤ E T) :
    explicit_formula_von_mangoldt_unweighted x hx := by
  refine explicit_formula_von_mangoldt_unweighted_of_norm_error_tendsto_zero ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hE ?_ hbound
  exact Eventually.of_forall fun T =>
    norm_nonneg (explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ))

lemma explicit_formula_von_mangoldt_unweighted_of_eventually_reverse_norm_le
    {x : ℝ} {hx : x ≥ 2} {E : ℝ → ℝ}
    (hE : Tendsto E atTop (𝓝 0))
    (hbound : ∀ᶠ T in atTop,
      ‖(chebyshevPsi0 x : ℂ) - explicitFormulaApprox x T‖ ≤ E T) :
    explicit_formula_von_mangoldt_unweighted x hx := by
  refine explicit_formula_von_mangoldt_unweighted_of_eventually_norm_le hE ?_
  filter_upwards [hbound] with T hT
  rwa [norm_sub_rev]

/-- A Big-O norm error estimate against any function tending to zero closes the
legacy unweighted compatibility predicate. -/
lemma explicit_formula_von_mangoldt_unweighted_of_norm_error_isBigO_tendsto_zero
    {x : ℝ} {hx : x ≥ 2} {E : ℝ → ℝ}
    (hE : Tendsto E atTop (𝓝 0))
    (hO :
      (fun T : ℝ => ‖explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ)‖)
        =O[atTop] E) :
    explicit_formula_von_mangoldt_unweighted x hx := by
  rcases hO.exists_pos with ⟨C, _hCpos, hCO⟩
  refine explicit_formula_von_mangoldt_unweighted_of_eventually_norm_le
    (E := fun T : ℝ => C * ‖E T‖) ?_ ?_
  · have hEnorm :
        Tendsto (fun T : ℝ => ‖E T‖) atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mp hE
    simpa using
      (tendsto_const_nhds.mul hEnorm :
        Tendsto (fun T : ℝ => C * ‖E T‖) atTop (𝓝 (C * 0)))
  · filter_upwards [hCO.bound] with T hT
    have hnorm_nonneg :
        0 ≤ ‖explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ)‖ :=
      norm_nonneg _
    simpa [Real.norm_eq_abs, abs_of_nonneg hnorm_nonneg] using hT

lemma explicit_formula_von_mangoldt_unweighted_of_reverse_norm_error_isBigO_tendsto_zero
    {x : ℝ} {hx : x ≥ 2} {E : ℝ → ℝ}
    (hE : Tendsto E atTop (𝓝 0))
    (hO :
      (fun T : ℝ => ‖(chebyshevPsi0 x : ℂ) - explicitFormulaApprox x T‖)
        =O[atTop] E) :
    explicit_formula_von_mangoldt_unweighted x hx := by
  refine explicit_formula_von_mangoldt_unweighted_of_norm_error_isBigO_tendsto_zero hE ?_
  have h_eq :
      (fun T : ℝ => ‖explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ)‖) =
        fun T : ℝ => ‖(chebyshevPsi0 x : ℂ) - explicitFormulaApprox x T‖ := by
    funext T
    rw [norm_sub_rev]
  simpa [h_eq] using hO

lemma explicit_formula_von_mangoldt_unweighted_of_eventually_norm_le_const_mul_inv
    {x C : ℝ} {hx : x ≥ 2}
    (hbound : ∀ᶠ T in atTop,
      ‖explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ)‖ ≤ C * T⁻¹) :
    explicit_formula_von_mangoldt_unweighted x hx := by
  refine explicit_formula_von_mangoldt_unweighted_of_eventually_norm_le ?_ hbound
  simpa using
    (tendsto_const_nhds.mul tendsto_inv_atTop_zero :
      Tendsto (fun T : ℝ => C * T⁻¹) atTop (𝓝 (C * 0)))

lemma explicit_formula_von_mangoldt_unweighted_of_eventually_reverse_norm_le_const_mul_inv
    {x C : ℝ} {hx : x ≥ 2}
    (hbound : ∀ᶠ T in atTop,
      ‖(chebyshevPsi0 x : ℂ) - explicitFormulaApprox x T‖ ≤ C * T⁻¹) :
    explicit_formula_von_mangoldt_unweighted x hx := by
  refine explicit_formula_von_mangoldt_unweighted_of_eventually_reverse_norm_le ?_ hbound
  simpa using
    (tendsto_const_nhds.mul tendsto_inv_atTop_zero :
      Tendsto (fun T : ℝ => C * T⁻¹) atTop (𝓝 (C * 0)))

/-- Coordinate estimates for the real and imaginary errors are enough to close
the legacy unweighted compatibility predicate. This is the shape naturally produced by many
contour estimates before they are repackaged as a complex norm bound. -/
lemma explicit_formula_von_mangoldt_unweighted_of_eventually_re_im_abs_le
    {x : ℝ} {hx : x ≥ 2} {Ere Eim : ℝ → ℝ}
    (hEre : Tendsto Ere atTop (𝓝 0))
    (hEim : Tendsto Eim atTop (𝓝 0))
    (hre_bound : ∀ᶠ T in atTop,
      |(explicitFormulaApprox x T).re - chebyshevPsi0 x| ≤ Ere T)
    (him_bound : ∀ᶠ T in atTop,
      |(explicitFormulaApprox x T).im| ≤ Eim T) :
    explicit_formula_von_mangoldt_unweighted x hx := by
  refine explicit_formula_von_mangoldt_unweighted_of_re_im_error_tendsto_zero ?_ ?_
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

/-- Big-O estimates for the real and imaginary explicit-formula errors,
against functions tending to zero, close the legacy unweighted compatibility predicate.

This is the natural interface for contour-error estimates that are proved in
separate real and imaginary parts rather than as one complex norm estimate. -/
lemma explicit_formula_von_mangoldt_unweighted_of_re_im_abs_error_isBigO_tendsto_zero
    {x : ℝ} {hx : x ≥ 2} {Ere Eim : ℝ → ℝ}
    (hEre : Tendsto Ere atTop (𝓝 0))
    (hEim : Tendsto Eim atTop (𝓝 0))
    (hreO :
      (fun T : ℝ => |(explicitFormulaApprox x T).re - chebyshevPsi0 x|)
        =O[atTop] Ere)
    (himO :
      (fun T : ℝ => |(explicitFormulaApprox x T).im|)
        =O[atTop] Eim) :
    explicit_formula_von_mangoldt_unweighted x hx := by
  rcases hreO.exists_pos with ⟨Cre, _hCre_pos, hCreO⟩
  rcases himO.exists_pos with ⟨Cim, _hCim_pos, hCimO⟩
  refine explicit_formula_von_mangoldt_unweighted_of_eventually_re_im_abs_le
    (Ere := fun T : ℝ => Cre * ‖Ere T‖)
    (Eim := fun T : ℝ => Cim * ‖Eim T‖) ?_ ?_ ?_ ?_
  · have hnorm :
        Tendsto (fun T : ℝ => ‖Ere T‖) atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mp hEre
    simpa using
      (tendsto_const_nhds.mul hnorm :
        Tendsto (fun T : ℝ => Cre * ‖Ere T‖) atTop (𝓝 (Cre * 0)))
  · have hnorm :
        Tendsto (fun T : ℝ => ‖Eim T‖) atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mp hEim
    simpa using
      (tendsto_const_nhds.mul hnorm :
        Tendsto (fun T : ℝ => Cim * ‖Eim T‖) atTop (𝓝 (Cim * 0)))
  · filter_upwards [hCreO.bound] with T hT
    have hnonneg :
        0 ≤ |(explicitFormulaApprox x T).re - chebyshevPsi0 x| :=
      abs_nonneg _
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hT
  · filter_upwards [hCimO.bound] with T hT
    have hnonneg :
        0 ≤ |(explicitFormulaApprox x T).im| :=
      abs_nonneg _
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hT

lemma explicit_formula_von_mangoldt_unweighted_of_eventually_re_im_abs_le_const_mul_inv
    {x Cre Cim : ℝ} {hx : x ≥ 2}
    (hre_bound : ∀ᶠ T in atTop,
      |(explicitFormulaApprox x T).re - chebyshevPsi0 x| ≤ Cre * T⁻¹)
    (him_bound : ∀ᶠ T in atTop,
      |(explicitFormulaApprox x T).im| ≤ Cim * T⁻¹) :
    explicit_formula_von_mangoldt_unweighted x hx := by
  refine explicit_formula_von_mangoldt_unweighted_of_eventually_re_im_abs_le ?_ ?_
    hre_bound him_bound
  · simpa using
      (tendsto_const_nhds.mul tendsto_inv_atTop_zero :
        Tendsto (fun T : ℝ => Cre * T⁻¹) atTop (𝓝 (Cre * 0)))
  · simpa using
      (tendsto_const_nhds.mul tendsto_inv_atTop_zero :
        Tendsto (fun T : ℝ => Cim * T⁻¹) atTop (𝓝 (Cim * 0)))

lemma explicit_formula_von_mangoldt_unweighted_re_abs_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2}
    (h : explicit_formula_von_mangoldt_unweighted x hx) :
    Tendsto (fun T : ℝ =>
      |(explicitFormulaApprox x T).re - chebyshevPsi0 x|) atTop (𝓝 0) := by
  simpa using (explicit_formula_von_mangoldt_unweighted_re_error_tendsto_zero h).abs

lemma explicit_formula_von_mangoldt_unweighted_im_abs_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2}
    (h : explicit_formula_von_mangoldt_unweighted x hx) :
    Tendsto (fun T : ℝ => |(explicitFormulaApprox x T).im|) atTop (𝓝 0) := by
  simpa using (explicit_formula_von_mangoldt_unweighted_im_error_tendsto_zero h).abs

lemma explicit_formula_von_mangoldt_unweighted_iff_re_im_abs_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2} :
    explicit_formula_von_mangoldt_unweighted x hx ↔
      Tendsto (fun T : ℝ =>
        |(explicitFormulaApprox x T).re - chebyshevPsi0 x|) atTop (𝓝 0) ∧
      Tendsto (fun T : ℝ => |(explicitFormulaApprox x T).im|) atTop (𝓝 0) := by
  constructor
  · intro h
    exact ⟨explicit_formula_von_mangoldt_unweighted_re_abs_error_tendsto_zero h,
      explicit_formula_von_mangoldt_unweighted_im_abs_error_tendsto_zero h⟩
  · intro h
    exact explicit_formula_von_mangoldt_unweighted_of_re_im_error_tendsto_zero
      ((tendsto_zero_iff_abs_tendsto_zero _).mpr h.1)
      ((tendsto_zero_iff_abs_tendsto_zero _).mpr h.2)

lemma explicit_formula_von_mangoldt_unweighted_re_abs_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (h : explicit_formula_von_mangoldt_unweighted x hx) :
    (fun T : ℝ =>
      |(explicitFormulaApprox x T).re - chebyshevPsi0 x|)
        =o[atTop] (fun _T : ℝ => (1 : ℝ)) :=
  (isLittleO_one_iff ℝ).mpr
    (explicit_formula_von_mangoldt_unweighted_re_abs_error_tendsto_zero h)

lemma explicit_formula_von_mangoldt_unweighted_im_abs_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (h : explicit_formula_von_mangoldt_unweighted x hx) :
    (fun T : ℝ => |(explicitFormulaApprox x T).im|)
        =o[atTop] (fun _T : ℝ => (1 : ℝ)) :=
  (isLittleO_one_iff ℝ).mpr
    (explicit_formula_von_mangoldt_unweighted_im_abs_error_tendsto_zero h)

lemma explicit_formula_von_mangoldt_unweighted_of_re_im_abs_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (hre :
      (fun T : ℝ =>
        |(explicitFormulaApprox x T).re - chebyshevPsi0 x|)
          =o[atTop] (fun _T : ℝ => (1 : ℝ)))
    (him : (fun T : ℝ => |(explicitFormulaApprox x T).im|)
        =o[atTop] (fun _T : ℝ => (1 : ℝ))) :
    explicit_formula_von_mangoldt_unweighted x hx :=
  (explicit_formula_von_mangoldt_unweighted_iff_re_im_abs_error_tendsto_zero).mpr
    ⟨(isLittleO_one_iff ℝ).mp hre,
      (isLittleO_one_iff ℝ).mp him⟩

lemma explicit_formula_von_mangoldt_unweighted_iff_re_im_abs_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2} :
    explicit_formula_von_mangoldt_unweighted x hx ↔
      (fun T : ℝ =>
        |(explicitFormulaApprox x T).re - chebyshevPsi0 x|)
          =o[atTop] (fun _T : ℝ => (1 : ℝ)) ∧
      (fun T : ℝ => |(explicitFormulaApprox x T).im|)
          =o[atTop] (fun _T : ℝ => (1 : ℝ)) :=
  ⟨fun h => ⟨explicit_formula_von_mangoldt_unweighted_re_abs_error_isLittleO_one h,
      explicit_formula_von_mangoldt_unweighted_im_abs_error_isLittleO_one h⟩,
    fun h => explicit_formula_von_mangoldt_unweighted_of_re_im_abs_error_isLittleO_one
      h.1 h.2⟩

lemma explicit_formula_von_mangoldt_unweighted_iff_norm_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2} :
    explicit_formula_von_mangoldt_unweighted x hx ↔
      Tendsto (fun T : ℝ =>
        ‖explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ)‖) atTop (𝓝 0) :=
  ⟨explicit_formula_von_mangoldt_unweighted_norm_error_tendsto_zero,
    explicit_formula_von_mangoldt_unweighted_of_norm_error_tendsto_zero⟩

lemma explicit_formula_von_mangoldt_unweighted_norm_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (h : explicit_formula_von_mangoldt_unweighted x hx) :
    (fun T : ℝ => ‖explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ)‖)
      =o[atTop] (fun _T : ℝ => (1 : ℝ)) :=
  (isLittleO_one_iff ℝ).mpr
    (explicit_formula_von_mangoldt_unweighted_norm_error_tendsto_zero h)

lemma explicit_formula_von_mangoldt_unweighted_of_norm_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (h : (fun T : ℝ => ‖explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ)‖)
      =o[atTop] (fun _T : ℝ => (1 : ℝ))) :
    explicit_formula_von_mangoldt_unweighted x hx :=
  explicit_formula_von_mangoldt_unweighted_of_norm_error_tendsto_zero
    ((isLittleO_one_iff ℝ).mp h)

lemma explicit_formula_von_mangoldt_unweighted_iff_norm_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2} :
    explicit_formula_von_mangoldt_unweighted x hx ↔
      (fun T : ℝ => ‖explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ)‖)
        =o[atTop] (fun _T : ℝ => (1 : ℝ)) :=
  ⟨explicit_formula_von_mangoldt_unweighted_norm_error_isLittleO_one,
    explicit_formula_von_mangoldt_unweighted_of_norm_error_isLittleO_one⟩

/-- Norm of a single nontrivial-zero contribution in the explicit formula. -/
lemma norm_zero_contribution_eq (ρ : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ ρ / ρ‖ = x ^ ρ.re / ‖ρ‖ := by
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx]

/-- Under RH, each nontrivial-zero contribution has `sqrt x` amplitude. -/
lemma norm_zero_contribution_eq_sqrt_of_RH
    (hRH : RiemannHypothesis.Statement)
    {ρ : ℂ} (hρ : RiemannHypothesis.IsNontrivialZero ρ)
    {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ ρ / ρ‖ = Real.sqrt x / ‖ρ‖ := by
  rw [norm_zero_contribution_eq ρ hx, hRH ρ hρ, Real.sqrt_eq_rpow]

/-- Under RH, a finite sum of nontrivial-zero contributions is bounded by
`sqrt x` times the reciprocal-norm sum of the zeros. -/
lemma norm_sum_zero_contributions_le_sqrt_mul_sum_inv_norm_of_RH
    (hRH : RiemannHypothesis.Statement)
    {x : ℝ} (hx : 0 < x) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, RiemannHypothesis.IsNontrivialZero ρ) :
    ‖∑ ρ ∈ S, (x : ℂ) ^ ρ / ρ‖ ≤
      Real.sqrt x * ∑ ρ ∈ S, ‖ρ‖⁻¹ := by
  calc
    ‖∑ ρ ∈ S, (x : ℂ) ^ ρ / ρ‖
        ≤ ∑ ρ ∈ S, ‖(x : ℂ) ^ ρ / ρ‖ := norm_sum_le S _
    _ = ∑ ρ ∈ S, Real.sqrt x / ‖ρ‖ := by
          refine Finset.sum_congr rfl ?_
          intro ρ hρ
          exact norm_zero_contribution_eq_sqrt_of_RH hRH (hS ρ hρ) hx
    _ = Real.sqrt x * ∑ ρ ∈ S, ‖ρ‖⁻¹ := by
          simp [div_eq_mul_inv, Finset.mul_sum]

/-- RH bound for the height-truncated nontrivial-zero sum. -/
lemma norm_finiteNontrivialZeroSum_le_sqrt_mul_sum_inv_norm_of_RH
    (hRH : RiemannHypothesis.Statement)
    {x T : ℝ} (hx : 0 < x) :
    ‖finiteNontrivialZeroSum x T‖ ≤
      Real.sqrt x * ∑ ρ ∈ nontrivialZerosFinset T, ‖ρ‖⁻¹ := by
  exact norm_sum_zero_contributions_le_sqrt_mul_sum_inv_norm_of_RH
    hRH hx (nontrivialZerosFinset T)
    (fun ρ hρ => (mem_nontrivialZerosFinset.mp hρ).1)

/-- RH bound for the newly appearing zeros between two truncation heights. -/
lemma norm_new_zero_contribution_sum_le_sqrt_mul_sum_inv_norm_of_RH
    (hRH : RiemannHypothesis.Statement)
    {x T U : ℝ} (hx : 0 < x) :
    ‖∑ ρ ∈ (nontrivialZerosFinset U \ nontrivialZerosFinset T),
        (x : ℂ) ^ ρ / ρ‖ ≤
      Real.sqrt x *
        ∑ ρ ∈ (nontrivialZerosFinset U \ nontrivialZerosFinset T), ‖ρ‖⁻¹ := by
  exact norm_sum_zero_contributions_le_sqrt_mul_sum_inv_norm_of_RH
    hRH hx (nontrivialZerosFinset U \ nontrivialZerosFinset T)
    (fun ρ hρ => (mem_nontrivialZerosFinset_sdiff.mp hρ).1)

/-- Under RH, a nontrivial zero has norm at least `1/2`. -/
lemma norm_nontrivial_zero_ge_half_of_RH
    (hRH : RiemannHypothesis.Statement)
    {ρ : ℂ} (hρ : RiemannHypothesis.IsNontrivialZero ρ) :
    (1 / 2 : ℝ) ≤ ‖ρ‖ := by
  have hle : |ρ.re| ≤ ‖ρ‖ := Complex.abs_re_le_norm ρ
  have habs : |ρ.re| = (1 / 2 : ℝ) := by
    rw [hRH ρ hρ]
    norm_num
  simpa [habs] using hle

/-- Under RH, the reciprocal norm of a nontrivial zero is at most `2`. -/
lemma inv_norm_nontrivial_zero_le_two_of_RH
    (hRH : RiemannHypothesis.Statement)
    {ρ : ℂ} (hρ : RiemannHypothesis.IsNontrivialZero ρ) :
    ‖ρ‖⁻¹ ≤ (2 : ℝ) := by
  have hhalf := norm_nontrivial_zero_ge_half_of_RH hRH hρ
  have hnorm_pos : 0 < ‖ρ‖ :=
    norm_pos_iff.mpr (nontrivial_zero_ne_zero hρ)
  have hmul : (1 : ℝ) ≤ 2 * ‖ρ‖ := by
    nlinarith
  have hdiv : (1 : ℝ) / ‖ρ‖ ≤ 2 := by
    rw [div_le_iff₀ hnorm_pos]
    exact hmul
  simpa [one_div] using hdiv

/-- RH bounds any finite reciprocal-norm sum by twice the number of zeros. -/
lemma sum_inv_norm_le_two_card_of_RH
    (hRH : RiemannHypothesis.Statement) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, RiemannHypothesis.IsNontrivialZero ρ) :
    (∑ ρ ∈ S, ‖ρ‖⁻¹) ≤ (2 : ℝ) * S.card := by
  calc
    (∑ ρ ∈ S, ‖ρ‖⁻¹) ≤ ∑ ρ ∈ S, (2 : ℝ) := by
      refine Finset.sum_le_sum ?_
      intro ρ hρ
      exact inv_norm_nontrivial_zero_le_two_of_RH hRH (hS ρ hρ)
    _ = (2 : ℝ) * S.card := by
      rw [Finset.sum_const]
      simp [nsmul_eq_mul]
      ring

/-- RH bounds the height-truncated reciprocal-norm zero sum by the zero count. -/
lemma sum_inv_norm_nontrivialZerosFinset_le_two_card_of_RH
    (hRH : RiemannHypothesis.Statement) (T : ℝ) :
    (∑ ρ ∈ nontrivialZerosFinset T, ‖ρ‖⁻¹) ≤
      (2 : ℝ) * (nontrivialZerosFinset T).card := by
  exact sum_inv_norm_le_two_card_of_RH hRH (nontrivialZerosFinset T)
    (fun ρ hρ => (mem_nontrivialZerosFinset.mp hρ).1)

/-- RH bounds the reciprocal-norm sum over newly appearing zeros by their count. -/
lemma sum_inv_norm_new_zeros_le_two_card_of_RH
    (hRH : RiemannHypothesis.Statement) (T U : ℝ) :
    (∑ ρ ∈ (nontrivialZerosFinset U \ nontrivialZerosFinset T), ‖ρ‖⁻¹) ≤
      (2 : ℝ) * (nontrivialZerosFinset U \ nontrivialZerosFinset T).card := by
  exact sum_inv_norm_le_two_card_of_RH hRH
    (nontrivialZerosFinset U \ nontrivialZerosFinset T)
    (fun ρ hρ => (mem_nontrivialZerosFinset_sdiff.mp hρ).1)

/-- RH count-bound for the height-truncated nontrivial-zero sum. -/
lemma norm_finiteNontrivialZeroSum_le_sqrt_mul_two_card_of_RH
    (hRH : RiemannHypothesis.Statement)
    {x T : ℝ} (hx : 0 < x) :
    ‖finiteNontrivialZeroSum x T‖ ≤
      Real.sqrt x * ((2 : ℝ) * (nontrivialZerosFinset T).card) := by
  have hbound :=
    norm_finiteNontrivialZeroSum_le_sqrt_mul_sum_inv_norm_of_RH hRH hx
      (T := T)
  have hsum := sum_inv_norm_nontrivialZerosFinset_le_two_card_of_RH hRH T
  exact hbound.trans (mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg x))

/-- RH count-bound for the new-zero contribution between two truncation heights. -/
lemma norm_new_zero_contribution_sum_le_sqrt_mul_two_card_of_RH
    (hRH : RiemannHypothesis.Statement)
    {x T U : ℝ} (hx : 0 < x) :
    ‖∑ ρ ∈ (nontrivialZerosFinset U \ nontrivialZerosFinset T),
        (x : ℂ) ^ ρ / ρ‖ ≤
      Real.sqrt x *
        ((2 : ℝ) * (nontrivialZerosFinset U \ nontrivialZerosFinset T).card) := by
  have hbound :=
    norm_new_zero_contribution_sum_le_sqrt_mul_sum_inv_norm_of_RH hRH hx
      (T := T) (U := U)
  have hsum := sum_inv_norm_new_zeros_le_two_card_of_RH hRH T U
  exact hbound.trans (mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg x))

/-- RH Cauchy-type bound for two height truncations of the explicit-formula
approximation, measured by the reciprocal-norm sum of newly included zeros. -/
lemma norm_explicitFormulaApprox_sub_le_sqrt_mul_sum_inv_norm_of_RH
    (hRH : RiemannHypothesis.Statement)
    {x T U : ℝ} (hx : 0 < x) (hTU : T ≤ U) :
    ‖explicitFormulaApprox x T - explicitFormulaApprox x U‖ ≤
      Real.sqrt x *
        ∑ ρ ∈ (nontrivialZerosFinset U \ nontrivialZerosFinset T), ‖ρ‖⁻¹ := by
  rw [explicitFormulaApprox_sub_norm_eq_new_zeros hTU]
  exact norm_new_zero_contribution_sum_le_sqrt_mul_sum_inv_norm_of_RH
    hRH hx

/-- RH Cauchy-type bound for two height truncations of the explicit-formula
approximation, measured by the number of newly included zeros. -/
lemma norm_explicitFormulaApprox_sub_le_sqrt_mul_two_card_of_RH
    (hRH : RiemannHypothesis.Statement)
    {x T U : ℝ} (hx : 0 < x) (hTU : T ≤ U) :
    ‖explicitFormulaApprox x T - explicitFormulaApprox x U‖ ≤
      Real.sqrt x *
        ((2 : ℝ) * (nontrivialZerosFinset U \ nontrivialZerosFinset T).card) := by
  rw [explicitFormulaApprox_sub_norm_eq_new_zeros hTU]
  exact norm_new_zero_contribution_sum_le_sqrt_mul_two_card_of_RH hRH hx

/-- Real-part version of the RH Cauchy-type truncation bound, measured by the
reciprocal-norm sum of newly included zeros. -/
lemma abs_re_explicitFormulaApprox_sub_le_sqrt_mul_sum_inv_norm_of_RH
    (hRH : RiemannHypothesis.Statement)
    {x T U : ℝ} (hx : 0 < x) (hTU : T ≤ U) :
    |(explicitFormulaApprox x T - explicitFormulaApprox x U).re| ≤
      Real.sqrt x *
        ∑ ρ ∈ (nontrivialZerosFinset U \ nontrivialZerosFinset T), ‖ρ‖⁻¹ :=
  (Complex.abs_re_le_norm _).trans
    (norm_explicitFormulaApprox_sub_le_sqrt_mul_sum_inv_norm_of_RH
      hRH hx hTU)

/-- Imaginary-part version of the RH Cauchy-type truncation bound, measured by
the reciprocal-norm sum of newly included zeros. -/
lemma abs_im_explicitFormulaApprox_sub_le_sqrt_mul_sum_inv_norm_of_RH
    (hRH : RiemannHypothesis.Statement)
    {x T U : ℝ} (hx : 0 < x) (hTU : T ≤ U) :
    |(explicitFormulaApprox x T - explicitFormulaApprox x U).im| ≤
      Real.sqrt x *
        ∑ ρ ∈ (nontrivialZerosFinset U \ nontrivialZerosFinset T), ‖ρ‖⁻¹ :=
  (Complex.abs_im_le_norm _).trans
    (norm_explicitFormulaApprox_sub_le_sqrt_mul_sum_inv_norm_of_RH
      hRH hx hTU)

/-- Real-part version of the RH Cauchy-type truncation bound, measured by the
number of newly included zeros. -/
lemma abs_re_explicitFormulaApprox_sub_le_sqrt_mul_two_card_of_RH
    (hRH : RiemannHypothesis.Statement)
    {x T U : ℝ} (hx : 0 < x) (hTU : T ≤ U) :
    |(explicitFormulaApprox x T - explicitFormulaApprox x U).re| ≤
      Real.sqrt x *
        ((2 : ℝ) * (nontrivialZerosFinset U \ nontrivialZerosFinset T).card) :=
  (Complex.abs_re_le_norm _).trans
    (norm_explicitFormulaApprox_sub_le_sqrt_mul_two_card_of_RH hRH hx hTU)

/-- Imaginary-part version of the RH Cauchy-type truncation bound, measured by
the number of newly included zeros. -/
lemma abs_im_explicitFormulaApprox_sub_le_sqrt_mul_two_card_of_RH
    (hRH : RiemannHypothesis.Statement)
    {x T U : ℝ} (hx : 0 < x) (hTU : T ≤ U) :
    |(explicitFormulaApprox x T - explicitFormulaApprox x U).im| ≤
      Real.sqrt x *
        ((2 : ℝ) * (nontrivialZerosFinset U \ nontrivialZerosFinset T).card) :=
  (Complex.abs_im_le_norm _).trans
    (norm_explicitFormulaApprox_sub_le_sqrt_mul_two_card_of_RH hRH hx hTU)

/-- If no new zeros appear eventually above the base cutoff, then the finite
new-zero contribution itself is eventually zero. -/
lemma new_zero_contribution_sum_eventually_zero_of_eventually_sdiff_eq_empty
    {x B : ℝ}
    (hnew : ∀ᶠ T in atTop,
      nontrivialZerosFinset T \ nontrivialZerosFinset B = ∅) :
    (fun T : ℝ =>
      ∑ ρ ∈ (nontrivialZerosFinset T \ nontrivialZerosFinset B),
        (x : ℂ) ^ ρ / ρ) =ᶠ[atTop] fun _T : ℝ => 0 := by
  filter_upwards [hnew] with T hT
  simp [hT]

/-- If no new zeros appear eventually above the base cutoff, then the finite
new-zero contribution tends to zero. -/
lemma new_zero_contribution_sum_tendsto_zero_of_eventually_sdiff_eq_empty
    {x B : ℝ}
    (hnew : ∀ᶠ T in atTop,
      nontrivialZerosFinset T \ nontrivialZerosFinset B = ∅) :
    Tendsto
      (fun T : ℝ =>
        ∑ ρ ∈ (nontrivialZerosFinset T \ nontrivialZerosFinset B),
          (x : ℂ) ^ ρ / ρ)
      atTop (𝓝 0) :=
  tendsto_nhds_of_eventually_eq
    (new_zero_contribution_sum_eventually_zero_of_eventually_sdiff_eq_empty hnew)

/-- If no new zeros appear eventually above the base cutoff, then the
sum-of-norms new-zero tail is eventually zero. -/
lemma new_zero_contribution_sum_norm_eventually_zero_of_eventually_sdiff_eq_empty
    {x B : ℝ}
    (hnew : ∀ᶠ T in atTop,
      nontrivialZerosFinset T \ nontrivialZerosFinset B = ∅) :
    (fun T : ℝ =>
      ∑ ρ ∈ (nontrivialZerosFinset T \ nontrivialZerosFinset B),
        ‖(x : ℂ) ^ ρ / ρ‖) =ᶠ[atTop] fun _T : ℝ => 0 := by
  filter_upwards [hnew] with T hT
  simp [hT]

/-- If no new zeros appear eventually above the base cutoff, then the
sum-of-norms new-zero tail tends to zero. -/
lemma new_zero_contribution_sum_norm_tendsto_zero_of_eventually_sdiff_eq_empty
    {x B : ℝ}
    (hnew : ∀ᶠ T in atTop,
      nontrivialZerosFinset T \ nontrivialZerosFinset B = ∅) :
    Tendsto
      (fun T : ℝ =>
        ∑ ρ ∈ (nontrivialZerosFinset T \ nontrivialZerosFinset B),
          ‖(x : ℂ) ^ ρ / ρ‖)
      atTop (𝓝 0) :=
  tendsto_nhds_of_eventually_eq
    (new_zero_contribution_sum_norm_eventually_zero_of_eventually_sdiff_eq_empty
      (x := x) hnew)

/-- Direct explicit-formula bridge from a stable base truncation and a
vanishing new-zero contribution tail.

This is the non-RH version of the later tail interfaces: if future Perron or
contour arguments identify one base truncation with `ψ₀(x)` and separately show
that the newly added zero contribution tends to zero, then the legacy
unweighted compatibility predicate follows. -/
lemma explicit_formula_von_mangoldt_unweighted_of_base_and_new_zero_contribution_tendsto_zero
    {x B : ℝ} {hx : x ≥ 2}
    (hB : explicitFormulaApprox x B = (chebyshevPsi0 x : ℂ))
    (htail :
      Tendsto
        (fun T : ℝ =>
          ∑ ρ ∈ (nontrivialZerosFinset T \ nontrivialZerosFinset B),
            (x : ℂ) ^ ρ / ρ)
        atTop (𝓝 0)) :
    explicit_formula_von_mangoldt_unweighted x hx := by
  refine explicit_formula_von_mangoldt_unweighted_of_error_tendsto_zero ?_
  have hdiff :
      (fun T : ℝ => explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ))
        =ᶠ[atTop]
      fun T : ℝ =>
        -∑ ρ ∈ (nontrivialZerosFinset T \ nontrivialZerosFinset B),
          (x : ℂ) ^ ρ / ρ := by
    filter_upwards [eventually_ge_atTop B] with T hBT
    rw [explicitFormulaApprox_eq_sub_new_zeros (x := x) hBT, hB]
    abel
  have htail_neg :
      Tendsto
        (fun T : ℝ =>
          -∑ ρ ∈ (nontrivialZerosFinset T \ nontrivialZerosFinset B),
            (x : ℂ) ^ ρ / ρ)
        atTop (𝓝 0) := by
    simpa using htail.neg
  exact Tendsto.congr' hdiff.symm htail_neg

/-- Direct explicit-formula bridge from a base identity and eventual absence
of new zero terms, routed through the vanishing contribution-tail interface. -/
lemma explicit_formula_von_mangoldt_unweighted_of_base_and_eventually_no_new_zeros_via_contribution_tail
    {x B : ℝ} {hx : x ≥ 2}
    (hB : explicitFormulaApprox x B = (chebyshevPsi0 x : ℂ))
    (hnew : ∀ᶠ T in atTop,
      nontrivialZerosFinset T \ nontrivialZerosFinset B = ∅) :
    explicit_formula_von_mangoldt_unweighted x hx :=
  explicit_formula_von_mangoldt_unweighted_of_base_and_new_zero_contribution_tendsto_zero
    hB
    (new_zero_contribution_sum_tendsto_zero_of_eventually_sdiff_eq_empty
      (x := x) hnew)

/-- Norm-tail version of
`explicit_formula_von_mangoldt_unweighted_of_base_and_new_zero_contribution_tendsto_zero`.

This is often the natural output of contour estimates: once the norm of the
new-zero contribution tends to zero, the complex contribution itself tends to
zero. -/
lemma explicit_formula_von_mangoldt_unweighted_of_base_and_new_zero_contribution_norm_tendsto_zero
    {x B : ℝ} {hx : x ≥ 2}
    (hB : explicitFormulaApprox x B = (chebyshevPsi0 x : ℂ))
    (htail :
      Tendsto
        (fun T : ℝ =>
          ‖∑ ρ ∈ (nontrivialZerosFinset T \ nontrivialZerosFinset B),
            (x : ℂ) ^ ρ / ρ‖)
        atTop (𝓝 0)) :
  explicit_formula_von_mangoldt_unweighted x hx :=
  explicit_formula_von_mangoldt_unweighted_of_base_and_new_zero_contribution_tendsto_zero
    hB (tendsto_zero_iff_norm_tendsto_zero.mpr htail)

/-- Sum-of-norms tail version of the direct new-zero contribution bridge.

This is the most common finite-output shape for zero-contribution estimates:
it is enough to show that the sum of the norms of the newly added terms tends
to zero. -/
lemma explicit_formula_von_mangoldt_unweighted_of_base_and_new_zero_contribution_sum_norm_tendsto_zero
    {x B : ℝ} {hx : x ≥ 2}
    (hB : explicitFormulaApprox x B = (chebyshevPsi0 x : ℂ))
    (htail :
      Tendsto
        (fun T : ℝ =>
          ∑ ρ ∈ (nontrivialZerosFinset T \ nontrivialZerosFinset B),
            ‖(x : ℂ) ^ ρ / ρ‖)
        atTop (𝓝 0)) :
  explicit_formula_von_mangoldt_unweighted x hx := by
  refine explicit_formula_von_mangoldt_unweighted_of_base_and_new_zero_contribution_norm_tendsto_zero
    hB ?_
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds htail
    (Eventually.of_forall fun _T => norm_nonneg _)
    (Eventually.of_forall fun _T => norm_sum_le _ _)

/-- Little-o sum-of-norms tail version of the direct new-zero contribution
bridge. -/
lemma explicit_formula_von_mangoldt_unweighted_of_base_and_new_zero_contribution_sum_norm_isLittleO_one
    {x B : ℝ} {hx : x ≥ 2}
    (hB : explicitFormulaApprox x B = (chebyshevPsi0 x : ℂ))
    (htail :
      (fun T : ℝ =>
        ∑ ρ ∈ (nontrivialZerosFinset T \ nontrivialZerosFinset B),
          ‖(x : ℂ) ^ ρ / ρ‖) =o[atTop] (fun _T : ℝ => (1 : ℝ))) :
  explicit_formula_von_mangoldt_unweighted x hx :=
  explicit_formula_von_mangoldt_unweighted_of_base_and_new_zero_contribution_sum_norm_tendsto_zero
    hB ((isLittleO_one_iff ℝ).mp htail)

/-- A vanishing eventual sum-of-norms bound for the new-zero contribution
closes the legacy unweighted compatibility predicate from a stable base truncation. -/
lemma explicit_formula_von_mangoldt_unweighted_of_base_and_eventually_new_zero_contribution_sum_norm_le
    {x B : ℝ} {hx : x ≥ 2} {E : ℝ → ℝ}
    (hB : explicitFormulaApprox x B = (chebyshevPsi0 x : ℂ))
    (hE : Tendsto E atTop (𝓝 0))
    (hbound :
      ∀ᶠ T in atTop,
        (∑ ρ ∈ (nontrivialZerosFinset T \ nontrivialZerosFinset B),
          ‖(x : ℂ) ^ ρ / ρ‖) ≤ E T) :
    explicit_formula_von_mangoldt_unweighted x hx := by
  refine explicit_formula_von_mangoldt_unweighted_of_base_and_new_zero_contribution_sum_norm_tendsto_zero
    hB ?_
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hE
    (Eventually.of_forall fun _T =>
      Finset.sum_nonneg fun _ρ _hρ => norm_nonneg _)
    hbound

/-- Big-O sum-of-norms tail version of the direct new-zero contribution
bridge. -/
lemma explicit_formula_von_mangoldt_unweighted_of_base_and_new_zero_contribution_sum_norm_isBigO_tendsto_zero
    {x B : ℝ} {hx : x ≥ 2} {E : ℝ → ℝ}
    (hB : explicitFormulaApprox x B = (chebyshevPsi0 x : ℂ))
    (hE : Tendsto E atTop (𝓝 0))
    (hO :
      (fun T : ℝ =>
        ∑ ρ ∈ (nontrivialZerosFinset T \ nontrivialZerosFinset B),
          ‖(x : ℂ) ^ ρ / ρ‖) =O[atTop] E) :
    explicit_formula_von_mangoldt_unweighted x hx := by
  rcases hO.exists_pos with ⟨C, _hCpos, hCO⟩
  refine explicit_formula_von_mangoldt_unweighted_of_base_and_eventually_new_zero_contribution_sum_norm_le
    hB (E := fun T : ℝ => C * ‖E T‖) ?_ ?_
  · have hEnorm : Tendsto (fun T : ℝ => ‖E T‖) atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mp hE
    simpa using
      (tendsto_const_nhds.mul hEnorm :
        Tendsto (fun T : ℝ => C * ‖E T‖) atTop (𝓝 (C * 0)))
  · filter_upwards [hCO.bound] with T hT
    have hnonneg :
        0 ≤ ∑ ρ ∈ (nontrivialZerosFinset T \ nontrivialZerosFinset B),
          ‖(x : ℂ) ^ ρ / ρ‖ :=
      Finset.sum_nonneg fun _ρ _hρ => norm_nonneg _
    have hnonneg' :
        0 ≤ ∑ ρ ∈ (nontrivialZerosFinset T \ nontrivialZerosFinset B),
          ‖(x : ℂ) ^ ρ‖ / ‖ρ‖ := by
      simpa [norm_div] using hnonneg
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg', norm_div] using hT

/-- A vanishing eventual norm bound for the new-zero contribution closes the
legacy unweighted compatibility predicate from a stable base truncation. -/
lemma explicit_formula_von_mangoldt_unweighted_of_base_and_eventually_new_zero_contribution_norm_le
    {x B : ℝ} {hx : x ≥ 2} {E : ℝ → ℝ}
    (hB : explicitFormulaApprox x B = (chebyshevPsi0 x : ℂ))
    (hE : Tendsto E atTop (𝓝 0))
    (hbound :
      ∀ᶠ T in atTop,
        ‖∑ ρ ∈ (nontrivialZerosFinset T \ nontrivialZerosFinset B),
          (x : ℂ) ^ ρ / ρ‖ ≤ E T) :
    explicit_formula_von_mangoldt_unweighted x hx := by
  refine explicit_formula_von_mangoldt_unweighted_of_base_and_new_zero_contribution_norm_tendsto_zero
    hB ?_
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hE
    (Eventually.of_forall fun _T => norm_nonneg _) hbound

/-- Big-O norm-tail version of the direct new-zero contribution bridge. -/
lemma explicit_formula_von_mangoldt_unweighted_of_base_and_new_zero_contribution_norm_isBigO_tendsto_zero
    {x B : ℝ} {hx : x ≥ 2} {E : ℝ → ℝ}
    (hB : explicitFormulaApprox x B = (chebyshevPsi0 x : ℂ))
    (hE : Tendsto E atTop (𝓝 0))
    (hO :
      (fun T : ℝ =>
        ‖∑ ρ ∈ (nontrivialZerosFinset T \ nontrivialZerosFinset B),
          (x : ℂ) ^ ρ / ρ‖) =O[atTop] E) :
    explicit_formula_von_mangoldt_unweighted x hx := by
  rcases hO.exists_pos with ⟨C, _hCpos, hCO⟩
  refine explicit_formula_von_mangoldt_unweighted_of_base_and_eventually_new_zero_contribution_norm_le
    hB (E := fun T : ℝ => C * ‖E T‖) ?_ ?_
  · have hEnorm : Tendsto (fun T : ℝ => ‖E T‖) atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mp hE
    simpa using
      (tendsto_const_nhds.mul hEnorm :
        Tendsto (fun T : ℝ => C * ‖E T‖) atTop (𝓝 (C * 0)))
  · filter_upwards [hCO.bound] with T hT
    have hnonneg :
        0 ≤ ‖∑ ρ ∈ (nontrivialZerosFinset T \ nontrivialZerosFinset B),
          (x : ℂ) ^ ρ / ρ‖ := norm_nonneg _
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hT

/-- If no new zeros appear eventually above the base cutoff, then the reciprocal
norm tail used in the RH truncation bound tends to zero. -/
lemma new_zero_inv_norm_tail_tendsto_zero_of_eventually_sdiff_eq_empty
    {x B : ℝ}
    (hnew : ∀ᶠ T in atTop,
      nontrivialZerosFinset T \ nontrivialZerosFinset B = ∅) :
    Tendsto
      (fun T : ℝ =>
        Real.sqrt x *
          ∑ ρ ∈ (nontrivialZerosFinset T \ nontrivialZerosFinset B), ‖ρ‖⁻¹)
      atTop (𝓝 0) := by
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [hnew] with T hT
  simp [hT]

/-- If no new zeros appear eventually above the base cutoff, then the zero-count
tail used in the RH truncation bound tends to zero. -/
lemma new_zero_card_tail_tendsto_zero_of_eventually_sdiff_eq_empty
    {x B : ℝ}
    (hnew : ∀ᶠ T in atTop,
      nontrivialZerosFinset T \ nontrivialZerosFinset B = ∅) :
    Tendsto
      (fun T : ℝ =>
        Real.sqrt x *
          ((2 : ℝ) * (nontrivialZerosFinset T \ nontrivialZerosFinset B).card))
      atTop (𝓝 0) := by
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [hnew] with T hT
  simp [hT]

/-- Under a global height bound on nontrivial zeros, the new-zero contribution
above the base cutoff is eventually zero. -/
lemma new_zero_contribution_sum_eventually_zero_of_global_height_bound
    {x B : ℝ}
    (hbound : ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → |ρ.im| ≤ B) :
    (fun T : ℝ =>
      ∑ ρ ∈ (nontrivialZerosFinset T \ nontrivialZerosFinset B),
        (x : ℂ) ^ ρ / ρ) =ᶠ[atTop] fun _T : ℝ => 0 :=
  new_zero_contribution_sum_eventually_zero_of_eventually_sdiff_eq_empty
    (nontrivialZerosFinset_eventually_sdiff_eq_empty_of_global_height_bound hbound)

/-- Under a global height bound on nontrivial zeros, the sum-of-norms
new-zero tail is eventually zero. -/
lemma new_zero_contribution_sum_norm_eventually_zero_of_global_height_bound
    {x B : ℝ}
    (hbound : ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → |ρ.im| ≤ B) :
    (fun T : ℝ =>
      ∑ ρ ∈ (nontrivialZerosFinset T \ nontrivialZerosFinset B),
        ‖(x : ℂ) ^ ρ / ρ‖) =ᶠ[atTop] fun _T : ℝ => 0 :=
  new_zero_contribution_sum_norm_eventually_zero_of_eventually_sdiff_eq_empty
    (nontrivialZerosFinset_eventually_sdiff_eq_empty_of_global_height_bound hbound)

/-- Under a global height bound on nontrivial zeros, the sum-of-norms
new-zero tail tends to zero. -/
lemma new_zero_contribution_sum_norm_tendsto_zero_of_global_height_bound
    {x B : ℝ}
    (hbound : ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → |ρ.im| ≤ B) :
    Tendsto
      (fun T : ℝ =>
        ∑ ρ ∈ (nontrivialZerosFinset T \ nontrivialZerosFinset B),
          ‖(x : ℂ) ^ ρ / ρ‖)
      atTop (𝓝 0) :=
  new_zero_contribution_sum_norm_tendsto_zero_of_eventually_sdiff_eq_empty
    (nontrivialZerosFinset_eventually_sdiff_eq_empty_of_global_height_bound hbound)

/-- Under a global height bound on nontrivial zeros, the reciprocal-norm
new-zero tail used in the RH truncation bound tends to zero. -/
lemma new_zero_inv_norm_tail_tendsto_zero_of_global_height_bound
    {x B : ℝ}
    (hbound : ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → |ρ.im| ≤ B) :
    Tendsto
      (fun T : ℝ =>
        Real.sqrt x *
          ∑ ρ ∈ (nontrivialZerosFinset T \ nontrivialZerosFinset B), ‖ρ‖⁻¹)
      atTop (𝓝 0) :=
  new_zero_inv_norm_tail_tendsto_zero_of_eventually_sdiff_eq_empty
    (nontrivialZerosFinset_eventually_sdiff_eq_empty_of_global_height_bound hbound)

/-- Under a global height bound on nontrivial zeros, the new-zero count tail
used in the RH truncation bound tends to zero. -/
lemma new_zero_card_tail_tendsto_zero_of_global_height_bound
    {x B : ℝ}
    (hbound : ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → |ρ.im| ≤ B) :
    Tendsto
      (fun T : ℝ =>
        Real.sqrt x *
          ((2 : ℝ) * (nontrivialZerosFinset T \ nontrivialZerosFinset B).card))
      atTop (𝓝 0) :=
  new_zero_card_tail_tendsto_zero_of_eventually_sdiff_eq_empty
    (nontrivialZerosFinset_eventually_sdiff_eq_empty_of_global_height_bound hbound)

/-- Conditional explicit-formula bridge from an RH tail bound stated with the
reciprocal-norm sum over newly included zeros.

The hard analytic input remains the base identity `hB` and the tail estimate
`htail`; this lemma only packages the already-proved RH truncation-gap bound
into the `explicit_formula_von_mangoldt_unweighted` convergence target. -/
lemma explicit_formula_von_mangoldt_unweighted_of_RH_base_and_new_zero_sum_tendsto_zero
    (hRH : RiemannHypothesis.Statement)
    {x B : ℝ} {hx : x ≥ 2}
    (hB : explicitFormulaApprox x B = (chebyshevPsi0 x : ℂ))
    (htail :
      Tendsto
        (fun T : ℝ =>
          Real.sqrt x *
            ∑ ρ ∈ (nontrivialZerosFinset T \ nontrivialZerosFinset B), ‖ρ‖⁻¹)
        atTop (𝓝 0)) :
    explicit_formula_von_mangoldt_unweighted x hx := by
  have hxpos : 0 < x := by linarith
  refine explicit_formula_von_mangoldt_unweighted_of_eventually_norm_le htail ?_
  filter_upwards [eventually_ge_atTop B] with T hBT
  have hgap :=
    norm_explicitFormulaApprox_sub_le_sqrt_mul_sum_inv_norm_of_RH
      hRH hxpos (T := B) (U := T) hBT
  calc
    ‖explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ)‖
        = ‖explicitFormulaApprox x B - explicitFormulaApprox x T‖ := by
          rw [← hB, norm_sub_rev]
    _ ≤ Real.sqrt x *
          ∑ ρ ∈ (nontrivialZerosFinset T \ nontrivialZerosFinset B), ‖ρ‖⁻¹ :=
          hgap

/-- Conditional explicit-formula bridge from an RH tail bound stated with the
count of newly included zeros. -/
lemma explicit_formula_von_mangoldt_unweighted_of_RH_base_and_new_zero_card_tendsto_zero
    (hRH : RiemannHypothesis.Statement)
    {x B : ℝ} {hx : x ≥ 2}
    (hB : explicitFormulaApprox x B = (chebyshevPsi0 x : ℂ))
    (htail :
      Tendsto
        (fun T : ℝ =>
          Real.sqrt x *
            ((2 : ℝ) * (nontrivialZerosFinset T \ nontrivialZerosFinset B).card))
        atTop (𝓝 0)) :
    explicit_formula_von_mangoldt_unweighted x hx := by
  have hxpos : 0 < x := by linarith
  refine explicit_formula_von_mangoldt_unweighted_of_eventually_norm_le htail ?_
  filter_upwards [eventually_ge_atTop B] with T hBT
  have hgap :=
    norm_explicitFormulaApprox_sub_le_sqrt_mul_two_card_of_RH
      hRH hxpos (T := B) (U := T) hBT
  calc
    ‖explicitFormulaApprox x T - (chebyshevPsi0 x : ℂ)‖
        = ‖explicitFormulaApprox x B - explicitFormulaApprox x T‖ := by
          rw [← hB, norm_sub_rev]
    _ ≤ Real.sqrt x *
          ((2 : ℝ) * (nontrivialZerosFinset T \ nontrivialZerosFinset B).card) :=
          hgap

/-- Conditional explicit-formula bridge obtained by composing the RH
reciprocal-norm tail bound with eventual absence of new zero terms.  This keeps
the hard input as the base identity `hB`; the tail convergence is discharged
from `hnew`. -/
lemma explicit_formula_von_mangoldt_unweighted_of_RH_base_and_eventually_no_new_zeros_via_sum_tail
    (hRH : RiemannHypothesis.Statement)
    {x B : ℝ} {hx : x ≥ 2}
    (hB : explicitFormulaApprox x B = (chebyshevPsi0 x : ℂ))
    (hnew : ∀ᶠ T in atTop,
      nontrivialZerosFinset T \ nontrivialZerosFinset B = ∅) :
    explicit_formula_von_mangoldt_unweighted x hx :=
  explicit_formula_von_mangoldt_unweighted_of_RH_base_and_new_zero_sum_tendsto_zero
    hRH hB
    (new_zero_inv_norm_tail_tendsto_zero_of_eventually_sdiff_eq_empty
      (x := x) hnew)

/-- Count-tail version of
`explicit_formula_von_mangoldt_unweighted_of_RH_base_and_eventually_no_new_zeros_via_sum_tail`. -/
lemma explicit_formula_von_mangoldt_unweighted_of_RH_base_and_eventually_no_new_zeros_via_card_tail
    (hRH : RiemannHypothesis.Statement)
    {x B : ℝ} {hx : x ≥ 2}
    (hB : explicitFormulaApprox x B = (chebyshevPsi0 x : ℂ))
    (hnew : ∀ᶠ T in atTop,
      nontrivialZerosFinset T \ nontrivialZerosFinset B = ∅) :
    explicit_formula_von_mangoldt_unweighted x hx :=
  explicit_formula_von_mangoldt_unweighted_of_RH_base_and_new_zero_card_tendsto_zero
    hRH hB
    (new_zero_card_tail_tendsto_zero_of_eventually_sdiff_eq_empty
      (x := x) hnew)

/-- Non-RH route from a global zero-height bound through the sum-of-norms
new-zero tail interface.  The hard input remains the base identity `hB`; this
lemma only packages the fact that a global height bound makes the finite tail
eventually empty. -/
lemma explicit_formula_von_mangoldt_unweighted_of_base_and_global_height_bound_via_sum_norm_tail
    {x B : ℝ} {hx : x ≥ 2}
    (hB : explicitFormulaApprox x B = (chebyshevPsi0 x : ℂ))
    (hbound : ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → |ρ.im| ≤ B) :
    explicit_formula_von_mangoldt_unweighted x hx :=
  explicit_formula_von_mangoldt_unweighted_of_base_and_new_zero_contribution_sum_norm_tendsto_zero
    hB
    (new_zero_contribution_sum_norm_tendsto_zero_of_global_height_bound
      (x := x) hbound)

/-- RH-tail route from a global zero-height bound.  The stronger exact bridge
`explicit_formula_von_mangoldt_unweighted_of_global_height_bound_exact` already avoids the
RH hypothesis; this lemma records the same stability through the explicit
new-zero-tail interface. -/
lemma explicit_formula_von_mangoldt_unweighted_of_RH_base_and_global_height_bound_via_sum_tail
    (hRH : RiemannHypothesis.Statement)
    {x B : ℝ} {hx : x ≥ 2}
    (hB : explicitFormulaApprox x B = (chebyshevPsi0 x : ℂ))
    (hbound : ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → |ρ.im| ≤ B) :
    explicit_formula_von_mangoldt_unweighted x hx :=
  explicit_formula_von_mangoldt_unweighted_of_RH_base_and_new_zero_sum_tendsto_zero
    hRH hB
    (new_zero_inv_norm_tail_tendsto_zero_of_global_height_bound
      (x := x) hbound)

/-- Count-tail version of
`explicit_formula_von_mangoldt_unweighted_of_RH_base_and_global_height_bound_via_sum_tail`. -/
lemma explicit_formula_von_mangoldt_unweighted_of_RH_base_and_global_height_bound_via_card_tail
    (hRH : RiemannHypothesis.Statement)
    {x B : ℝ} {hx : x ≥ 2}
    (hB : explicitFormulaApprox x B = (chebyshevPsi0 x : ℂ))
    (hbound : ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → |ρ.im| ≤ B) :
    explicit_formula_von_mangoldt_unweighted x hx :=
  explicit_formula_von_mangoldt_unweighted_of_RH_base_and_new_zero_card_tendsto_zero
    hRH hB
    (new_zero_card_tail_tendsto_zero_of_global_height_bound
      (x := x) hbound)

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
