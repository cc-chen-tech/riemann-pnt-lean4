import HardyTheorem.SelbergFirstMomentContour
import HardyTheorem.SelbergFirstMomentBridge

open Complex MeasureTheory Set
open scoped Interval

namespace HardyTheorem

/-!
# From the S4 contour mass to the completed first moment

This module keeps the final analytic implication separate from the eventual
integer parameter choice.  A linear lower bound for the holomorphic contour
auxiliary, the exact critical-line modulus identity, and uniform lower
Stirling together force the `T^(3/4)` absolute first moment.
-/

/-- A `T / 4` lower bound furnished by the S4 rectangle implies the required
completed absolute first moment.  No condition on how `X` depends on `T` is
needed here; that dependence enters only when the horizontal errors are
absorbed into the contour main term. -/
theorem exists_pos_mul_rpow_three_quarters_le_integral_abs_selbergCompletedMollifiedF_of_contour :
    ∃ c : ℝ, 0 < c ∧
      ∀ T delta : ℝ, ∀ X : ℕ,
        2 ≤ T → 0 ≤ delta → delta ≤ 1 / T →
        T / 4 ≤
          ‖∫ t in T / 2..T,
              selbergFirstMomentAuxiliary X ((1 / 2 : ℂ) + I * t)‖ →
        c * T ^ (3 / 4 : ℝ) ≤
          ∫ t in T / 2..T, |selbergCompletedMollifiedF delta X t| := by
  obtain ⟨A, hA, hstirling⟩ :=
    exists_pos_rpow_neg_quarter_le_norm_GammaR_mul_selbergTilt
  let q : ℝ := 1 / (2 * Real.sqrt (2 * Real.pi))
  have hq : 0 < q := by
    dsimp only [q]
    positivity
  refine ⟨q * A / 4, by positivity, ?_⟩
  intro T delta X hT hdelta0 hdelta hcontour
  have hTpos : 0 < T := by linarith
  have hhalf : T / 2 ≤ T := by linarith
  let G : ℝ → ℂ := fun t =>
    selbergFirstMomentAuxiliary X ((1 / 2 : ℂ) + I * t)
  let k : ℝ := q * A * T ^ (-(1 / 4 : ℝ))
  have hk : 0 ≤ k := by
    dsimp only [k]
    positivity
  have hGcont : ContinuousOn G (Set.Icc (T / 2) T) := by
    intro t ht
    have htpos : 0 < t := by linarith [ht.1]
    have hs1 : (1 / 2 : ℂ) + I * (t : ℂ) ≠ 1 := by
      intro hs
      have him := congrArg Complex.im hs
      norm_num at him
      linarith
    have hM : DifferentiableAt ℂ (selbergSqrtZetaMollifier X)
        ((1 / 2 : ℂ) + I * t) := by
      exact ((analyticOnNhd_selbergMollifier X
        (fun n => (selbergSqrtZetaTaperedCoeff X n : ℂ)))
          ((1 / 2 : ℂ) + I * t) (Set.mem_univ _)).differentiableAt
    have haux : ContinuousAt (selbergFirstMomentAuxiliary X)
        ((1 / 2 : ℂ) + I * t) := by
      unfold selbergFirstMomentAuxiliary
      exact (((differentiableAt_riemannZeta hs1).mul hM).mul hM).continuousAt
    have hpath : ContinuousAt (fun u : ℝ =>
        (1 / 2 : ℂ) + I * u) t := by fun_prop
    have hcomp : ContinuousAt
        (selbergFirstMomentAuxiliary X ∘ fun u : ℝ =>
          (1 / 2 : ℂ) + I * u) t :=
      ContinuousAt.comp (f := fun u : ℝ => (1 / 2 : ℂ) + I * u)
        haux hpath
    change ContinuousWithinAt
      (selbergFirstMomentAuxiliary X ∘ fun u : ℝ =>
        (1 / 2 : ℂ) + I * u) (Set.Icc (T / 2) T) t
    exact hcomp.continuousWithinAt
  have hGnormCont : ContinuousOn (fun t => ‖G t‖)
      (Set.uIcc (T / 2) T) := by
    rw [Set.uIcc_of_le hhalf]
    exact hGcont.norm
  have hGnormInt : IntervalIntegrable (fun t => ‖G t‖) volume (T / 2) T :=
    hGnormCont.intervalIntegrable
  have hweightedInt : IntervalIntegrable (fun t => k * ‖G t‖)
      volume (T / 2) T := hGnormInt.const_mul k
  have hFabsInt : IntervalIntegrable
      (fun t => |selbergCompletedMollifiedF delta X t|)
      volume (T / 2) T :=
    (continuous_selbergCompletedMollifiedF delta X).abs.intervalIntegrable _ _
  have hpoint : ∀ t ∈ Set.Icc (T / 2) T,
      k * ‖G t‖ ≤ |selbergCompletedMollifiedF delta X t| := by
    intro t ht
    have hst := hstirling T delta t hT hdelta0 hdelta ht.1 ht.2
    rw [abs_selbergCompletedMollifiedF_eq_gamma_tilt_mul_abs_sqrtZeta,
      abs_selbergSqrtZetaMollifiedHardyZ_eq_norm_zeta_mul_mollifier_sq]
    dsimp only [k, q, G]
    unfold selbergFirstMomentAuxiliary
    calc
      (1 / (2 * Real.sqrt (2 * Real.pi)) * A *
          T ^ (-(1 / 4 : ℝ))) *
          ‖riemannZeta ((1 / 2 : ℂ) + I * ↑t) *
              selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * ↑t) *
            selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * ↑t)‖ =
        (1 / (2 * Real.sqrt (2 * Real.pi))) *
          (A * T ^ (-(1 / 4 : ℝ))) *
          ‖riemannZeta ((1 / 2 : ℂ) + I * ↑t) *
              selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * ↑t) *
            selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * ↑t)‖ := by ring
      _ ≤ (1 / (2 * Real.sqrt (2 * Real.pi))) *
          (‖Gammaℝ ((1 / 2 : ℂ) + I * ↑t)‖ *
            Real.exp ((Real.pi / 4 - delta / 2) * t)) *
          ‖riemannZeta ((1 / 2 : ℂ) + I * ↑t) *
              selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * ↑t) *
            selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * ↑t)‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hst hq.le) (norm_nonneg _)
      _ = (1 / (2 * Real.sqrt (2 * Real.pi))) *
          ‖Gammaℝ ((1 / 2 : ℂ) + I * ↑t)‖ *
          Real.exp ((Real.pi / 4 - delta / 2) * t) *
          ‖riemannZeta ((1 / 2 : ℂ) + I * ↑t) *
              selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * ↑t) *
            selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * ↑t)‖ := by ring
  have hmono := intervalIntegral.integral_mono_on hhalf hweightedInt hFabsInt hpoint
  have hnorm := intervalIntegral.norm_integral_le_integral_norm
    (μ := volume) (f := G) hhalf
  have hpow : T ^ (-(1 / 4 : ℝ)) * T = T ^ (3 / 4 : ℝ) := by
    calc
      T ^ (-(1 / 4 : ℝ)) * T =
          T ^ (-(1 / 4 : ℝ)) * T ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = T ^ (-(1 / 4 : ℝ) + 1) := by rw [Real.rpow_add hTpos]
      _ = T ^ (3 / 4 : ℝ) := by norm_num
  calc
    (q * A / 4) * T ^ (3 / 4 : ℝ) =
        k * (T / 4) := by
      dsimp only [k]
      rw [← hpow]
      ring
    _ ≤ k * ‖∫ t in T / 2..T, G t‖ :=
      mul_le_mul_of_nonneg_left hcontour hk
    _ ≤ k * (∫ t in T / 2..T, ‖G t‖) :=
      mul_le_mul_of_nonneg_left hnorm hk
    _ = ∫ t in T / 2..T, k * ‖G t‖ := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ ∫ t in T / 2..T, |selbergCompletedMollifiedF delta X t| := hmono

/-- Fully assembled S4a except for the elementary eventual parameter
absorption.  The last two hypotheses say exactly that the fixed right-edge
remainder and the two horizontal edges each consume at most `T / 8` of the
`T / 2` contour main term. -/
theorem exists_pos_rpow_three_quarters_firstMoment_of_horizontal_absorption :
    ∃ c C T0 : ℝ, 0 < c ∧ 0 < C ∧ 2 ≤ T0 ∧
      ∀ T delta : ℝ, ∀ X : ℕ,
        T0 ≤ T → 2 ≤ X → 0 ≤ delta → delta ≤ 1 / T →
        16 / Real.log 2 ≤ T / 8 →
        2 * C * X * Real.sqrt (T / 2) ≤ T / 8 →
        c * T ^ (3 / 4 : ℝ) ≤
          ∫ t in T / 2..T, |selbergCompletedMollifiedF delta X t| := by
  obtain ⟨c, hc, hbridge⟩ :=
    exists_pos_mul_rpow_three_quarters_le_integral_abs_selbergCompletedMollifiedF_of_contour
  obtain ⟨C, T0, hC, hT0, hcontour⟩ :=
    exists_norm_intervalIntegral_selbergFirstMomentAuxiliary_dyadic_lower
  refine ⟨c, C, T0, hc, hC, hT0, ?_⟩
  intro T delta X hT hX hdelta0 hdelta hright hhorizontal
  have hlower := hcontour T X hT hX
  apply hbridge T delta X (hT0.trans hT) hdelta0 hdelta
  linarith

end HardyTheorem
