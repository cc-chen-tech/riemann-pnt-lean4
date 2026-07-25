import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import WeilExtremalKernels.ArchimedeanRankTwoIntegral

/-!
# The archimedean `h₊` weight

This module defines the real archimedean density

`h₊(t) = Re digamma(1/4 + i*t/2) - log pi`

used by the finite Guinand-Weil dictionary.  It proves analyticity of
`digamma` in the right half-plane, continuity of `h₊`, and continuity of the
paper's actual scalar rank-two weight.  It also proves the algebraic
nonnegativity and logarithmic-envelope transfers once the corresponding
pointwise facts about `h₊` are supplied.

The hard estimates `0 ≤ h₊(t)` and `h₊(t) ≤ log t` for `t ≥ 7` are not proved
here.  They require the digamma partial-fraction/derivative bounds and the
certified endpoint estimate described in the paper.
-/

namespace WeilExtremalKernels

open Complex

theorem analyticAt_Gamma_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ Gamma s := by
  let U : Set ℂ := {z | 0 < z.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const continuous_re
  have hdiff : DifferentiableOn ℂ Gamma U := by
    intro z hz
    apply (differentiableAt_Gamma z ?_).differentiableWithinAt
    intro m hm
    have hre := congrArg Complex.re hm
    norm_num at hre
    have hzpos : 0 < z.re := hz
    have hmnonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  exact (hdiff.analyticOnNhd hUopen) s hs

theorem analyticAt_digamma_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ digamma s := by
  rw [digamma_def]
  have hGamma := analyticAt_Gamma_of_re_pos hs
  simpa only [logDeriv_apply] using
    hGamma.deriv.div hGamma (Gamma_ne_zero_of_re_pos hs)

/-- The paper's real archimedean density. -/
noncomputable def archimedeanHPlus (t : ℝ) : ℝ :=
  (digamma ((1 / 4 : ℝ) + (t / 2 : ℝ) * I)).re - Real.log Real.pi

theorem continuous_archimedeanHPlus : Continuous archimedeanHPlus := by
  apply continuous_iff_continuousAt.2
  intro t
  have hs :
      0 < (((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I).re := by
    norm_num
  have hdigamma :=
    (analyticAt_digamma_of_re_pos hs).continuousAt
  unfold archimedeanHPlus
  fun_prop

/-- The actual scalar multiplier in the paper's rank-two density. -/
noncomputable def paperArchimedeanWeight (L rho r : ℝ) : ℝ :=
  archimedeanHPlus r * Real.sin (L * r / 2) ^ 2 /
    (Real.pi ^ 2 * rho)

theorem continuous_paperArchimedeanWeight (L rho : ℝ) :
    Continuous (paperArchimedeanWeight L rho) := by
  unfold paperArchimedeanWeight
  have hphase : Continuous (fun r : ℝ => L * r / 2) := by fun_prop
  exact (continuous_archimedeanHPlus.mul
    ((Real.continuous_sin.comp hphase).pow 2)).div_const _

theorem paperArchimedeanWeight_nonneg
    {L rho r : ℝ} (hrho : 0 < rho) (hh : 0 ≤ archimedeanHPlus r) :
    0 ≤ paperArchimedeanWeight L rho r := by
  unfold paperArchimedeanWeight
  positivity

/-- The logarithmic envelope used to integrate the explicit tail budget. -/
theorem paperArchimedeanWeight_le_log_envelope
    {L rho r : ℝ} (hrho : 0 < rho)
    (hh0 : 0 ≤ archimedeanHPlus r)
    (hhlog : archimedeanHPlus r ≤ Real.log r) :
    paperArchimedeanWeight L rho r ≤
      Real.log r / (Real.pi ^ 2 * rho) := by
  have hsin1 : Real.sin (L * r / 2) ^ 2 ≤ 1 :=
    Real.sin_sq_le_one _
  have hnum :
      archimedeanHPlus r * Real.sin (L * r / 2) ^ 2 ≤ Real.log r := by
    calc
      archimedeanHPlus r * Real.sin (L * r / 2) ^ 2 ≤
          archimedeanHPlus r * 1 :=
        mul_le_mul_of_nonneg_left hsin1 hh0
      _ ≤ Real.log r := by simpa using hhlog
  unfold paperArchimedeanWeight
  exact div_le_div_of_nonneg_right hnum
    (mul_nonneg (sq_nonneg _) hrho.le)

end WeilExtremalKernels
