import WeilExtremalKernels.ArchimedeanTailBudget

open Filter MeasureTheory Set WeilExtremalKernels
open scoped Topology

example {b x : ℝ}
    (hb : b ≠ 0) (hx : x ≠ 0) (hxb : x - b ≠ 0) :
    HasDerivAt (archimedeanTailPrimitive b)
      (Real.log x / (x - b) ^ 2) x :=
  hasDerivAt_archimedeanTailPrimitive hb hx hxb

example (b : ℝ) :
    Tendsto (archimedeanTailPrimitive b) atTop (𝓝 0) :=
  tendsto_archimedeanTailPrimitive_atTop b

example {b T : ℝ} (hb : 0 < b) (hT : b < T) (hT1 : 1 ≤ T) :
    ∫ r in Ioi T, Real.log r / (r - b) ^ 2 =
      Real.log T / (T - b) + b⁻¹ * Real.log (T / (T - b)) :=
  integral_Ioi_log_div_sub_sq hb hT hT1
