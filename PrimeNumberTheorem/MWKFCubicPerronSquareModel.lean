import PrimeNumberTheorem.MWKFCubicZetaPoleFactorization

open Complex MeasureTheory

namespace PrimeNumberTheorem.MWKFCubic

/-!
# The square double-Perron main model

This file evaluates the literal iterated full-height vertical integral that
appears as the square model in the cubic diagonal calculation.  It is formula
(4.10) of the accompanying research note after parametrizing both vertical
lines by real ordinates.  The proof uses the already established full Mellin
inversion formula in each variable and the exact normalization `1 / (2*pi)`.

No zeta contour shift or error estimate is used here.
-/

/-- One full-height vertical Perron kernel with natural cutoff `N`. -/
noncomputable def cubicPerronSquareVerticalKernel
    (N : ℕ) (sigma u : ℝ) : ℂ :=
  (N : ℂ) ^ ((sigma : ℂ) + u * I) *
    (1 / (((sigma : ℂ) + u * I) ^ 2))

/-- The separated two-variable kernel in the square double-Perron model. -/
noncomputable def cubicPerronSquareKernel
    (N : ℕ) (sigma u v : ℝ) : ℂ :=
  cubicPerronSquareVerticalKernel N sigma u *
    cubicPerronSquareVerticalKernel N sigma v

/-- The literally iterated, normalized double vertical integral. -/
noncomputable def cubicPerronSquareModelIntegral
    (N : ℕ) (sigma : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) ^ 2 *
    ∫ u : ℝ, ∫ v : ℝ, cubicPerronSquareKernel N sigma u v

private theorem cubicPerronSquareVerticalIntegral_eq_log
    {N : ℕ} {sigma : ℝ} (hsigma : 0 < sigma) (hN : 1 ≤ N) :
    (1 / (2 * Real.pi) : ℂ) *
        ∫ u : ℝ, cubicPerronSquareVerticalKernel N sigma u =
      (Real.log (N : ℝ) : ℂ) := by
  have hNpos : 0 < N := by omega
  calc
    (1 / (2 * Real.pi) : ℂ) *
          ∫ u : ℝ, cubicPerronSquareVerticalKernel N sigma u =
        HardyTheorem.perronLogCutoff ((1 : ℝ) / (N : ℝ)) := by
      simpa [cubicPerronSquareVerticalKernel] using
        (HardyTheorem.perronKernel_ratio_integral_eq
          (sigma := sigma) (Y := (N : ℝ)) (n := (1 : ℝ))
          hsigma (by exact_mod_cast hNpos) one_pos)
    _ = (Real.log ((N : ℝ) / (1 : ℝ)) : ℂ) := by
      simpa using
        (HardyTheorem.perronLogCutoff_nat_div_eq_log
          (n := 1) (Y := N) Nat.one_pos hNpos hN)
    _ = (Real.log (N : ℝ) : ℂ) := by simp

/-- Exact evaluation of the square model:

`(2*pi)^(-2) * integral_u integral_v N^(sigma+iu)/(sigma+iu)^2
  * N^(sigma+iv)/(sigma+iv)^2 = (log N)^2`.

The assumption `1 ≤ N` includes the vanishing boundary case `N = 1`. -/
theorem cubicPerronSquareModelIntegral_eq_log_sq
    {N : ℕ} {sigma : ℝ} (hsigma : 0 < sigma) (hN : 1 ≤ N) :
    cubicPerronSquareModelIntegral N sigma =
      (Real.log (N : ℝ) : ℂ) ^ 2 := by
  let f : ℝ → ℂ := cubicPerronSquareVerticalKernel N sigma
  have hdouble :
      (∫ u : ℝ, ∫ v : ℝ, cubicPerronSquareKernel N sigma u v) =
        (∫ u : ℝ, f u) * (∫ v : ℝ, f v) := by
    calc
      (∫ u : ℝ, ∫ v : ℝ, cubicPerronSquareKernel N sigma u v) =
          ∫ u : ℝ, f u * (∫ v : ℝ, f v) := by
        apply integral_congr_ae
        filter_upwards with u
        unfold cubicPerronSquareKernel f
        rw [integral_const_mul]
      _ = (∫ u : ℝ, f u) * (∫ v : ℝ, f v) := by
        rw [integral_mul_const]
  have hsingle :
      (1 / (2 * Real.pi) : ℂ) * (∫ u : ℝ, f u) =
        (Real.log (N : ℝ) : ℂ) := by
    simpa [f] using cubicPerronSquareVerticalIntegral_eq_log hsigma hN
  unfold cubicPerronSquareModelIntegral
  rw [hdouble]
  calc
    (1 / (2 * Real.pi) : ℂ) ^ 2 *
          ((∫ u : ℝ, f u) * ∫ v : ℝ, f v) =
        ((1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ, f u) ^ 2 := by ring
    _ = (Real.log (N : ℝ) : ℂ) ^ 2 := by rw [hsingle]

end PrimeNumberTheorem.MWKFCubic
