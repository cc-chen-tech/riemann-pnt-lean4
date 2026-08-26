import HardyTheorem.SelbergPerronKernel
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.LSeries.Basic

open Complex MeasureTheory Filter
open scoped LSeries.notation Topology

namespace HardyTheorem

/-!
# Absolute logarithmic Perron inversion for an L-series

The square denominator makes the full vertical integral absolutely convergent.  Absolute
convergence of the L-series on the chosen line then gives a genuine Tonelli interchange, after
which `SelbergPerronKernel` evaluates every term exactly.
-/

noncomputable def selbergPerronLine (sigma t : ℝ) : ℂ :=
  (sigma : ℂ) + t * I

noncomputable def selbergPerronLSeriesTerm
    (coeff : ℕ → ℂ) (Y sigma : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  (Y : ℂ) ^ selbergPerronLine sigma t *
    LSeries.term coeff (selbergPerronLine sigma t) n *
      (1 / (selbergPerronLine sigma t) ^ 2)

noncomputable def selbergPerronLSeriesIntegrand
    (coeff : ℕ → ℂ) (Y sigma : ℝ) (t : ℝ) : ℂ :=
  (Y : ℂ) ^ selbergPerronLine sigma t *
    L coeff (selbergPerronLine sigma t) *
      (1 / (selbergPerronLine sigma t) ^ 2)

theorem selbergPerronLSeriesIntegrand_eq_tsum
    (coeff : ℕ → ℂ) (Y sigma t : ℝ) :
    selbergPerronLSeriesIntegrand coeff Y sigma t =
      ∑' n : ℕ, selbergPerronLSeriesTerm coeff Y sigma n t := by
  unfold selbergPerronLSeriesIntegrand selbergPerronLSeriesTerm LSeries
  rw [← tsum_mul_left, ← tsum_mul_right]

private theorem selbergPerronLine_re (sigma t : ℝ) :
    (selbergPerronLine sigma t).re = sigma := by
  simp [selbergPerronLine]

private theorem selbergPerronLine_ne_zero {sigma : ℝ} (hsigma : 0 < sigma) (t : ℝ) :
    selbergPerronLine sigma t ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  rw [selbergPerronLine_re] at hre
  norm_num at hre
  linarith

private theorem continuous_selbergPerronLSeriesTerm
    (coeff : ℕ → ℂ) {Y sigma : ℝ} (hY : 0 < Y) (hsigma : 0 < sigma) (n : ℕ) :
    Continuous (selbergPerronLSeriesTerm coeff Y sigma n) := by
  by_cases hn : n = 0
  · subst n
    have hz : selbergPerronLSeriesTerm coeff Y sigma 0 =
        fun _ : ℝ => (0 : ℂ) := by
      funext t
      simp [selbergPerronLSeriesTerm]
    rw [hz]
    exact continuous_const
  · have hline : Continuous (selbergPerronLine sigma) := by
      unfold selbergPerronLine
      fun_prop
    have hYpow : Continuous fun t : ℝ =>
        (Y : ℂ) ^ selbergPerronLine sigma t :=
      hline.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hY.ne'))
    have hnpow : Continuous fun t : ℝ =>
        (n : ℂ) ^ selbergPerronLine sigma t :=
      hline.const_cpow (Or.inl (Nat.cast_ne_zero.mpr hn))
    have hterm : Continuous fun t : ℝ =>
        LSeries.term coeff (selbergPerronLine sigma t) n := by
      simpa [LSeries.term_of_ne_zero hn] using
        continuous_const.div₀ hnpow (fun _ =>
          cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr hn)))
    have hkernel : Continuous fun t : ℝ =>
        1 / (selbergPerronLine sigma t) ^ 2 := by
      exact continuous_const.div₀ (hline.pow 2)
        (fun t => pow_ne_zero 2 (selbergPerronLine_ne_zero hsigma t))
    exact (hYpow.mul hterm).mul hkernel

private theorem norm_selbergPerronLSeriesTerm_eq
    (coeff : ℕ → ℂ) {Y sigma : ℝ} (hY : 0 < Y) (n : ℕ) (t : ℝ) :
    ‖selbergPerronLSeriesTerm coeff Y sigma n t‖ =
      Y ^ sigma * ‖LSeries.term coeff (sigma : ℂ) n‖ *
        ‖(1 / (selbergPerronLine sigma t) ^ 2 : ℂ)‖ := by
  have hterm :
      ‖LSeries.term coeff (selbergPerronLine sigma t) n‖ =
        ‖LSeries.term coeff (sigma : ℂ) n‖ := by
    simp [LSeries.norm_term_eq, selbergPerronLine_re]
  unfold selbergPerronLSeriesTerm
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY,
    selbergPerronLine_re, hterm]

theorem integrable_selbergPerronLSeriesTerm
    (coeff : ℕ → ℂ) {Y sigma : ℝ} (hY : 0 < Y) (hsigma : 0 < sigma) (n : ℕ) :
    Integrable (selbergPerronLSeriesTerm coeff Y sigma n) := by
  have hkernel : Integrable (fun t : ℝ =>
      (1 / (selbergPerronLine sigma t) ^ 2 : ℂ)) := by
    have h := verticalIntegrable_inv_sq hsigma
    unfold VerticalIntegrable at h
    simpa [selbergPerronLine, one_div] using h
  have hnormInt : Integrable (fun t : ℝ =>
      ‖selbergPerronLSeriesTerm coeff Y sigma n t‖) := by
    have h := hkernel.norm.const_mul
      (Y ^ sigma * ‖LSeries.term coeff (sigma : ℂ) n‖)
    convert h using 1
    funext t
    exact norm_selbergPerronLSeriesTerm_eq coeff hY n t
  exact (integrable_norm_iff
    (continuous_selbergPerronLSeriesTerm coeff hY hsigma n).aestronglyMeasurable).mp hnormInt

theorem summable_integral_norm_selbergPerronLSeriesTerm
    (coeff : ℕ → ℂ) {Y sigma : ℝ} (hY : 0 < Y) (hsigma : 0 < sigma)
    (hsum : LSeriesSummable coeff (sigma : ℂ)) :
    Summable (fun n : ℕ => ∫ t : ℝ,
      ‖selbergPerronLSeriesTerm coeff Y sigma n t‖) := by
  let K : ℝ := ∫ t : ℝ, ‖(1 / (selbergPerronLine sigma t) ^ 2 : ℂ)‖
  have htermNorm : Summable fun n : ℕ =>
      ‖LSeries.term coeff (sigma : ℂ) n‖ := by
    exact hsum.norm
  have hmajor : Summable fun n : ℕ =>
      (Y ^ sigma * K) * ‖LSeries.term coeff (sigma : ℂ) n‖ :=
    htermNorm.mul_left (Y ^ sigma * K)
  apply hmajor.congr
  intro n
  have heq :
      (∫ t : ℝ, ‖selbergPerronLSeriesTerm coeff Y sigma n t‖) =
        (Y ^ sigma * ‖LSeries.term coeff (sigma : ℂ) n‖) * K := by
    rw [integral_congr_ae (Eventually.of_forall fun t =>
      norm_selbergPerronLSeriesTerm_eq coeff hY n t)]
    rw [integral_const_mul]
  rw [heq]
  ring

theorem integral_selbergPerronLSeriesIntegrand_eq_tsum_integral
    (coeff : ℕ → ℂ) {Y sigma : ℝ} (hY : 0 < Y) (hsigma : 0 < sigma)
    (hsum : LSeriesSummable coeff (sigma : ℂ)) :
    (∫ t : ℝ, selbergPerronLSeriesIntegrand coeff Y sigma t) =
      ∑' n : ℕ, ∫ t : ℝ, selbergPerronLSeriesTerm coeff Y sigma n t := by
  rw [integral_congr_ae (Eventually.of_forall
    (selbergPerronLSeriesIntegrand_eq_tsum coeff Y sigma))]
  exact (integral_tsum_of_summable_integral_norm
    (fun n => integrable_selbergPerronLSeriesTerm coeff hY hsigma n)
    (summable_integral_norm_selbergPerronLSeriesTerm coeff hY hsigma hsum)).symm

theorem normalized_integral_selbergPerronLSeriesTerm_eq
    (coeff : ℕ → ℂ) {Y sigma : ℝ} (hY : 0 < Y) (hsigma : 0 < sigma) (n : ℕ) :
    (1 / (2 * Real.pi) : ℂ) *
        (∫ t : ℝ, selbergPerronLSeriesTerm coeff Y sigma n t) =
      coeff n * perronLogCutoff (n / Y) := by
  by_cases hn : n = 0
  · subst n
    simp [selbergPerronLSeriesTerm, LSeries.term, perronLogCutoff]
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hpoint (t : ℝ) :
        selbergPerronLSeriesTerm coeff Y sigma n t =
          coeff n *
            (((Y : ℂ) ^ selbergPerronLine sigma t /
                (n : ℂ) ^ selbergPerronLine sigma t) *
              (1 / (selbergPerronLine sigma t) ^ 2)) := by
      unfold selbergPerronLSeriesTerm
      rw [LSeries.term_of_ne_zero hn]
      ring
    rw [integral_congr_ae (Eventually.of_forall hpoint), integral_const_mul]
    calc
      (1 / (2 * Real.pi) : ℂ) *
          (coeff n * ∫ t : ℝ,
            ((Y : ℂ) ^ selbergPerronLine sigma t /
                (n : ℂ) ^ selbergPerronLine sigma t) *
              (1 / (selbergPerronLine sigma t) ^ 2)) =
        coeff n *
          ((1 / (2 * Real.pi) : ℂ) *
            ∫ t : ℝ,
              ((Y : ℂ) ^ selbergPerronLine sigma t /
                  (n : ℂ) ^ selbergPerronLine sigma t) *
                (1 / (selbergPerronLine sigma t) ^ 2)) := by ring
      _ = coeff n * perronLogCutoff (n / Y) := by
        simpa [selbergPerronLine] using congrArg (coeff n * ·)
          (perronKernel_ratio_integral_eq hsigma hY hnpos)

theorem normalized_integral_selbergPerronLSeries_eq
    (coeff : ℕ → ℂ) {Y sigma : ℝ} (hY : 0 < Y) (hsigma : 0 < sigma)
    (hsum : LSeriesSummable coeff (sigma : ℂ)) :
    (1 / (2 * Real.pi) : ℂ) *
        (∫ t : ℝ, selbergPerronLSeriesIntegrand coeff Y sigma t) =
      ∑' n : ℕ, coeff n * perronLogCutoff (n / Y) := by
  rw [integral_selbergPerronLSeriesIntegrand_eq_tsum_integral
    coeff hY hsigma hsum, ← tsum_mul_left]
  apply tsum_congr
  intro n
  exact normalized_integral_selbergPerronLSeriesTerm_eq coeff hY hsigma n

end HardyTheorem
