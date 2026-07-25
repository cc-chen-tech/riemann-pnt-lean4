import WeilExtremalKernels.ArchimedeanHPlus

open Complex WeilExtremalKernels

example {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ Gamma s :=
  analyticAt_Gamma_of_re_pos hs

example {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ digamma s :=
  analyticAt_digamma_of_re_pos hs

example : Continuous archimedeanHPlus :=
  continuous_archimedeanHPlus

example (t : ℝ) :
    archimedeanHPlus t =
      2 * HardyTheorem.verticalGammaPhaseVelocity t :=
  archimedeanHPlus_eq_two_mul_verticalGammaPhaseVelocity t

example :
    Filter.Tendsto
      (fun t : ℝ =>
        archimedeanHPlus t - Real.log (t / (2 * Real.pi)))
      Filter.atTop (nhds 0) :=
  tendsto_archimedeanHPlus_sub_log_model_atTop

example :
    ∃ T0 : ℝ, ∀ t : ℝ, T0 ≤ t →
      0 ≤ archimedeanHPlus t ∧
        archimedeanHPlus t ≤ Real.log t :=
  exists_eventually_archimedeanHPlus_bounds

example (L rho : ℝ) :
    Continuous (paperArchimedeanWeight L rho) :=
  continuous_paperArchimedeanWeight L rho

example {L rho r : ℝ} (hrho : 0 < rho)
    (hh : 0 ≤ archimedeanHPlus r) :
    0 ≤ paperArchimedeanWeight L rho r :=
  paperArchimedeanWeight_nonneg hrho hh

example {L rho r : ℝ} (hrho : 0 < rho)
    (hh0 : 0 ≤ archimedeanHPlus r)
    (hhlog : archimedeanHPlus r ≤ Real.log r) :
    paperArchimedeanWeight L rho r ≤
      Real.log r / (Real.pi ^ 2 * rho) :=
  paperArchimedeanWeight_le_log_envelope hrho hh0 hhlog
