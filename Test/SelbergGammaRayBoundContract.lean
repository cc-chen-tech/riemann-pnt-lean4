import HardyTheorem.SelbergGammaRayBound

open Complex

namespace HardyTheorem

example (s : ℂ) : Differentiable ℂ (gammaLogKernel s) :=
  differentiable_gammaLogKernel s

example (s : ℂ) (x y : ℝ) :
    ‖gammaLogKernel s ((x : ℂ) + y * I)‖ =
      Real.exp
        (s.re * x - s.im * y - Real.exp x * Real.cos y) :=
  norm_gammaLogKernel s x y

example (s : ℂ) (R eta : ℝ) :
    (∫ x : ℝ in -R..R, gammaLogKernel s x) -
        (∫ x : ℝ in -R..R, gammaLogKernel s (x + eta * I)) +
      I • (∫ y : ℝ in 0..eta, gammaLogKernel s (R + y * I)) -
      I • (∫ y : ℝ in 0..eta, gammaLogKernel s (-R + y * I)) = 0 :=
  integral_boundary_rect_gammaLogKernel s R eta

example (s : ℂ) {eta y : ℝ}
    (heta0 : 0 ≤ eta) (hetaPi : eta ≤ Real.pi / 2)
    (hy : y ∈ Set.Icc 0 eta) (R : ℝ) :
    ‖gammaLogKernel s ((R : ℂ) + y * I)‖ ≤
      Real.exp
        (s.re * R + |s.im| * eta - Real.exp R * Real.cos eta) :=
  norm_gammaLogKernel_right_le s heta0 hetaPi hy R

example (s : ℂ) {eta y : ℝ}
    (heta0 : 0 ≤ eta) (hetaPi : eta ≤ Real.pi / 2)
    (hy : y ∈ Set.Icc 0 eta) (R : ℝ) :
    ‖gammaLogKernel s ((-R : ℂ) + y * I)‖ ≤
      Real.exp (-s.re * R + |s.im| * eta) :=
  norm_gammaLogKernel_left_le s heta0 hetaPi hy R

example (s : ℂ) {eta : ℝ}
    (heta0 : 0 ≤ eta) (hetaPi : eta ≤ Real.pi / 2) (R : ℝ) :
    ‖∫ y : ℝ in 0..eta, gammaLogKernel s (R + y * I)‖ ≤
      Real.exp
          (s.re * R + |s.im| * eta - Real.exp R * Real.cos eta) * eta :=
  norm_integral_gammaLogKernel_right_le s heta0 hetaPi R

example (s : ℂ) {eta : ℝ}
    (heta0 : 0 ≤ eta) (hetaPi : eta ≤ Real.pi / 2) (R : ℝ) :
    ‖∫ y : ℝ in 0..eta, gammaLogKernel s (-R + y * I)‖ ≤
      Real.exp (-s.re * R + |s.im| * eta) * eta :=
  norm_integral_gammaLogKernel_left_le s heta0 hetaPi R

example (s : ℂ) {eta : ℝ}
    (heta0 : 0 ≤ eta) (hetaPi : eta ≤ Real.pi / 2)
    (hs : 0 < s.re) :
    Filter.Tendsto
      (fun R : ℝ =>
        ∫ y : ℝ in 0..eta, gammaLogKernel s (-R + y * I))
      Filter.atTop (nhds 0) :=
  tendsto_integral_gammaLogKernel_left_atTop s heta0 hetaPi hs

example (s : ℂ) {eta : ℝ}
    (heta0 : 0 ≤ eta) (hetaPi : eta < Real.pi / 2) :
    Filter.Tendsto
      (fun R : ℝ =>
        ∫ y : ℝ in 0..eta, gammaLogKernel s (R + y * I))
      Filter.atTop (nhds 0) :=
  tendsto_integral_gammaLogKernel_right_atTop s heta0 hetaPi

example (s : ℂ) {eta : ℝ}
    (heta0 : 0 ≤ eta) (hetaPi : eta < Real.pi / 2)
    (hs : 0 < s.re) :
    Filter.Tendsto
      (fun R : ℝ =>
        (∫ x : ℝ in -R..R, gammaLogKernel s x) -
          ∫ x : ℝ in -R..R, gammaLogKernel s (x + eta * I))
      Filter.atTop (nhds 0) :=
  tendsto_sub_integral_gammaLogKernel_horizontal_atTop
    s heta0 hetaPi hs

example (s : ℂ) (hs : 0 < s.re) :
    MeasureTheory.Integrable (fun x : ℝ => gammaLogKernel s x) :=
  integrable_gammaLogKernel_real s hs

example (s : ℂ) (hs : 0 < s.re) :
    (∫ x : ℝ, gammaLogKernel s x) = Complex.Gamma s :=
  integral_gammaLogKernel_real_eq_Gamma s hs

example (sigma c : ℝ) (hsigma : 0 < sigma) (hc : 0 < c) :
    MeasureTheory.Integrable
      (fun x : ℝ => Real.exp (sigma * x - c * Real.exp x)) :=
  integrable_gammaLogEnvelope sigma c hsigma hc

example (sigma c : ℝ) (hsigma : 0 < sigma) (hc : 0 < c) :
    (∫ x : ℝ, Real.exp (sigma * x - c * Real.exp x)) =
      c ^ (-sigma) * Real.Gamma sigma :=
  integral_gammaLogEnvelope_eq_real_Gamma sigma c hsigma hc

example (s : ℂ) {eta : ℝ}
    (heta0 : 0 ≤ eta) (hetaPi : eta < Real.pi / 2)
    (hs : 0 < s.re) :
    MeasureTheory.Integrable
      (fun x : ℝ => gammaLogKernel s (x + eta * I)) :=
  integrable_gammaLogKernel_horizontal s heta0 hetaPi hs

example (s : ℂ) {eta : ℝ}
    (heta0 : 0 ≤ eta) (hetaPi : eta < Real.pi / 2)
    (hs : 0 < s.re) :
    (∫ x : ℝ, gammaLogKernel s x) =
      ∫ x : ℝ, gammaLogKernel s (x + eta * I) :=
  integral_gammaLogKernel_eq_integral_shift s heta0 hetaPi hs

example (s : ℂ) {eta : ℝ}
    (heta0 : 0 ≤ eta) (hetaPi : eta < Real.pi / 2)
    (hs : 0 < s.re) :
    (∫ x : ℝ, gammaLogKernel s (x + eta * I)) =
      Complex.Gamma s :=
  integral_gammaLogKernel_shift_eq_Gamma s heta0 hetaPi hs

example (s : ℂ) {eta : ℝ}
    (heta0 : 0 ≤ eta) (hetaPi : eta < Real.pi / 2)
    (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤
      Real.Gamma s.re * (Real.cos eta) ^ (-s.re) *
        Real.exp (-eta * |s.im|) :=
  norm_Gamma_le_real_Gamma_mul_cos_rpow_mul_exp_neg_abs_im
    s heta0 hetaPi hs

#print axioms differentiable_gammaLogKernel
#print axioms norm_gammaLogKernel
#print axioms integral_boundary_rect_gammaLogKernel
#print axioms norm_gammaLogKernel_right_le
#print axioms norm_gammaLogKernel_left_le
#print axioms norm_integral_gammaLogKernel_right_le
#print axioms norm_integral_gammaLogKernel_left_le
#print axioms tendsto_integral_gammaLogKernel_left_atTop
#print axioms tendsto_integral_gammaLogKernel_right_atTop
#print axioms tendsto_sub_integral_gammaLogKernel_horizontal_atTop
#print axioms integrable_gammaLogKernel_real
#print axioms integral_gammaLogKernel_real_eq_Gamma
#print axioms integrable_gammaLogEnvelope
#print axioms integral_gammaLogEnvelope_eq_real_Gamma
#print axioms integrable_gammaLogKernel_horizontal
#print axioms integral_gammaLogKernel_eq_integral_shift
#print axioms integral_gammaLogKernel_shift_eq_Gamma
#print axioms norm_Gamma_le_real_Gamma_mul_cos_rpow_mul_exp_neg_abs_im

end HardyTheorem
