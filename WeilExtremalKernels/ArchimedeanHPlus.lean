import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import HardyTheorem.VerticalGammaAsymptotic
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

/-- The archimedean density is twice the vertical `Gammaℝ` phase velocity
already analyzed by the Hardy-theorem infrastructure. -/
theorem archimedeanHPlus_eq_two_mul_verticalGammaPhaseVelocity
    (t : ℝ) :
    archimedeanHPlus t =
      2 * HardyTheorem.verticalGammaPhaseVelocity t := by
  have harg :
      (((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I) =
        (1 / 4 : ℂ) + I * (t : ℂ) / 2 := by
    push_cast
    ring
  unfold archimedeanHPlus HardyTheorem.verticalGammaPhaseVelocity
  rw [harg]
  ring

/-- The proved second-order Stirling remainder makes `h₊` asymptotic to its
elementary logarithmic model. -/
theorem tendsto_archimedeanHPlus_sub_log_model_atTop :
    Filter.Tendsto
      (fun t : ℝ =>
        archimedeanHPlus t - Real.log (t / (2 * Real.pi)))
      Filter.atTop (nhds 0) := by
  obtain ⟨C, hC, hbound⟩ :=
    HardyTheorem.exists_abs_verticalGammaPhaseVelocity_sub_deriv_thetaModel_le_inv_sq
  have hpow :
      Filter.Tendsto (fun t : ℝ => t ^ 2)
        Filter.atTop Filter.atTop := by
    simpa [pow_two] using
      Filter.tendsto_id.atTop_mul_atTop₀ Filter.tendsto_id
  have hmajor :
      Filter.Tendsto (fun t : ℝ => (2 * C) / t ^ 2)
        Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hpow
  have habs :
      Filter.Tendsto
        (fun t : ℝ =>
          |archimedeanHPlus t - Real.log (t / (2 * Real.pi))|)
        Filter.atTop (nhds 0) := by
    have hnonneg :
        ∀ᶠ t : ℝ in Filter.atTop,
          0 ≤ |archimedeanHPlus t - Real.log (t / (2 * Real.pi))| :=
      Filter.Eventually.of_forall fun t => abs_nonneg _
    have hle :
        ∀ᶠ t : ℝ in Filter.atTop,
          |archimedeanHPlus t - Real.log (t / (2 * Real.pi))| ≤
            (2 * C) / t ^ 2 := by
      filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
      have ht0 : 0 < t := zero_lt_one.trans_le ht
      have hraw := hbound t ht
      rw [HardyTheorem.deriv_thetaModel ht0] at hraw
      rw [archimedeanHPlus_eq_two_mul_verticalGammaPhaseVelocity]
      have hscale :
          2 * HardyTheorem.verticalGammaPhaseVelocity t -
              Real.log (t / (2 * Real.pi)) =
            2 *
              (HardyTheorem.verticalGammaPhaseVelocity t -
                (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi))) := by
        ring
      rw [hscale, abs_mul]
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      calc
        2 *
            |HardyTheorem.verticalGammaPhaseVelocity t -
              (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi))| ≤
            2 * (C / t ^ 2) :=
          mul_le_mul_of_nonneg_left hraw (by norm_num)
        _ = (2 * C) / t ^ 2 := by ring
    exact squeeze_zero' hnonneg hle hmajor
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 habs

/-- There is a non-explicit tail on which the actual archimedean density is
nonnegative and lies below the logarithmic envelope used by the scalar tail
integral. The paper's explicit threshold `t ≥ 7` remains a separate
quantitative problem. -/
theorem exists_eventually_archimedeanHPlus_bounds :
    ∃ T0 : ℝ, ∀ t : ℝ, T0 ≤ t →
      0 ≤ archimedeanHPlus t ∧
        archimedeanHPlus t ≤ Real.log t := by
  have herr := tendsto_archimedeanHPlus_sub_log_model_atTop
  have hratio :
      Filter.Tendsto (fun t : ℝ => t / (2 * Real.pi))
        Filter.atTop Filter.atTop :=
    Filter.tendsto_id.atTop_div_const (by positivity)
  have hlog :
      Filter.Tendsto (fun t : ℝ => Real.log (t / (2 * Real.pi)))
        Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp hratio
  have herrLower :
      ∀ᶠ t : ℝ in Filter.atTop,
        -1 < archimedeanHPlus t - Real.log (t / (2 * Real.pi)) :=
    herr.eventually_const_lt (by norm_num)
  have hlogLower :
      ∀ᶠ t : ℝ in Filter.atTop, 1 ≤ Real.log (t / (2 * Real.pi)) :=
    hlog.eventually_ge_atTop 1
  have hnonneg :
      ∀ᶠ t : ℝ in Filter.atTop, 0 ≤ archimedeanHPlus t := by
    filter_upwards [herrLower, hlogLower] with t he hl
    linarith
  have hlogTwoPiPos : 0 < Real.log (2 * Real.pi) :=
    Real.log_pos (by nlinarith [Real.pi_gt_three])
  have hconst :
      Filter.Tendsto (fun _ : ℝ => Real.log (2 * Real.pi))
        Filter.atTop (nhds (Real.log (2 * Real.pi))) :=
    tendsto_const_nhds
  have hpositive :
      ∀ᶠ t : ℝ in Filter.atTop,
        0 <
          Real.log (2 * Real.pi) -
            (archimedeanHPlus t - Real.log (t / (2 * Real.pi))) := by
    have hlim := hconst.sub herr
    have hv : 0 < Real.log (2 * Real.pi) - 0 := by
      simpa using hlogTwoPiPos
    exact hlim.eventually_const_lt hv
  have htpos : ∀ᶠ t : ℝ in Filter.atTop, 0 < t :=
    Filter.eventually_gt_atTop 0
  have hupper :
      ∀ᶠ t : ℝ in Filter.atTop, archimedeanHPlus t ≤ Real.log t := by
    filter_upwards [hpositive, htpos] with t hp ht
    rw [Real.log_div ht.ne'
      (by positivity : (2 * Real.pi : ℝ) ≠ 0)] at hp
    linarith
  rcases Filter.eventually_atTop.1 (hnonneg.and hupper) with ⟨T0, hT0⟩
  exact ⟨T0, hT0⟩

/-- The eventual `h₊` bounds may be taken beyond `1`, which is the range
needed by the logarithmic improper-integral formula. -/
theorem exists_one_le_eventually_archimedeanHPlus_bounds :
    ∃ T0 : ℝ, 1 ≤ T0 ∧ ∀ t : ℝ, T0 ≤ t →
      0 ≤ archimedeanHPlus t ∧
        archimedeanHPlus t ≤ Real.log t := by
  obtain ⟨T0, hT0⟩ := exists_eventually_archimedeanHPlus_bounds
  refine ⟨max 1 T0, le_max_left _ _, ?_⟩
  intro t ht
  exact hT0 t ((le_max_right 1 T0).trans ht)

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
