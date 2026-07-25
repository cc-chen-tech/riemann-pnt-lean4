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
