import PrimeNumberTheorem.VKEdgePiOverTwoCenteredContourDecay

open Complex Filter Polynomial Set Topology
open scoped BigOperators

namespace PrimeNumberTheorem.VKEdgePiOverTwo

#check centeredPoleRadius
#check real_sq_add_q_mul_sub_centeredPoleRadius_sq_le
#check norm_localizedGaussianWeightAtCenter_left_le
#check norm_localizedGaussianWeightAtCenter_horizontal_le
#check norm_localizedRegularizedLogDerivIntegrandAtCenter_right_le_gaussian
#check eventually_centeredPoleRadius_le_linearHeight
#check CenteredConcreteLocalizedContourSlice
#check exists_centeredConcreteLocalizedContourSlice
#check centeredLocalizedContourScaleValid
#check selectedCenteredConcreteLocalizedContourSlice
#check selectedLocalizedContourRemainderAtCenter
#check selectedLocalizedZeroResidueSumAtCenter
#check selected_localizedPsiGaussianAverageAtCenter_eq
#check tendsto_selectedLocalizedContourRemainderAtCenter
#check selectedLocalizedFarZeroResidueSumAtCenter
#check selectedLocalizedZeroResidueSumAtCenter_nearZeroFilter_eq_target_add_far
#check selectedLocalizedZeroResidueSumAtCenter_nearZeroFilter_eq_far_of_ne_zero
#check tendsto_selectedLocalizedFarZeroResidueSumAtCenter
#check tendsto_selectedLocalizedZeroResidueSumAtCenter_nearZeroFilter
#check tendsto_selectedLocalizedZeroResidueSumAtCenter_nearZeroFilter_of_ne_zero

example (q : ℝ) : centeredPoleRadius q = q + 5 := by
  rfl

example {q a : ℝ} (hq : 0 < q) (ha : |a| ≤ 1) :
    a ^ 2 + q * a - centeredPoleRadius q ^ 2 ≤ -8 :=
  real_sq_add_q_mul_sub_centeredPoleRadius_sq_le hq ha

example (q : ℝ) (A : ℂ[X]) {u v t m : ℝ}
    (hq : 16 ≤ q) (hu : 0 < u) (hu1 : u < 1) (hm : 0 ≤ m) :
    ‖localizedGaussianWeightAtCenter q A
        ((u : ℂ) + I * v) m
        ((-1 : ℂ) + I * t)‖ ≤
      ‖A.eval (((-1 : ℂ) + I * t) - ((u : ℂ) + I * v))‖ *
        Real.exp (-15 * m - m * (t - v) ^ 2) :=
  norm_localizedGaussianWeightAtCenter_left_le q A hq hu hu1 hm

example (q : ℝ) (A : ℂ[X]) {u v σ t m : ℝ}
    (hq : 16 ≤ q) (hu : 0 < u) (hu1 : u < 1)
    (hσlo : -1 ≤ σ) (hσhi : σ ≤ u + 2) (hm : 0 ≤ m) :
    ‖localizedGaussianWeightAtCenter q A
        ((u : ℂ) + I * v) m ((σ : ℂ) + I * t)‖ ≤
      ‖A.eval (((σ : ℂ) + I * t) - ((u : ℂ) + I * v))‖ *
        Real.exp (m * ((4 + 2 * q) - (t - v) ^ 2)) :=
  norm_localizedGaussianWeightAtCenter_horizontal_le
    q A hq hu hu1 hσlo hσhi hm

example {q : ℝ} {A : ℂ[X]} {u v m : ℝ}
    (slice : CenteredConcreteLocalizedContourSlice q A u v m) :
    slice.height ∈ Set.Icc (12 * m + |v|) (12 * m + |v| + 1) :=
  slice.height_mem

example (q : ℝ) (A : ℂ[X]) (u v m : ℝ)
    (hinvalid : ¬ centeredLocalizedContourScaleValid q A u m) :
    selectedLocalizedContourRemainderAtCenter q A u v m = 0 := by
  simp [selectedLocalizedContourRemainderAtCenter, hinvalid]

example (q : ℝ) (A : ℂ[X]) (u v m : ℝ)
    (hinvalid : ¬ centeredLocalizedContourScaleValid q A u m) :
    selectedLocalizedZeroResidueSumAtCenter q A u v m = 0 := by
  simp [selectedLocalizedZeroResidueSumAtCenter, hinvalid]

example (q : ℝ) (A : ℂ[X]) {u v m : ℝ}
    (hvalid : centeredLocalizedContourScaleValid q A u m) :
    localizedPsiGaussianAverageAtCenter q A
        ((u : ℂ) + I * v) m =
      -(2 * Real.pi : ℂ) *
          selectedLocalizedZeroResidueSumAtCenter q A u v m +
        selectedLocalizedContourRemainderAtCenter q A u v m :=
  selected_localizedPsiGaussianAverageAtCenter_eq q A hvalid

example (q : ℝ) (A : ℂ[X]) {u : ℝ}
    (hq : 16 ≤ q) (hu : 0 < u) (hu1 : u < 1) (v : ℝ) :
    Tendsto
      (selectedLocalizedContourRemainderAtCenter q A u v)
      atTop (𝓝 0) :=
  tendsto_selectedLocalizedContourRemainderAtCenter q A hq hu hu1 v

example (q : ℝ) {u v : ℝ}
    (hq : 16 ≤ q) (hu : 0 < u) (hu1 : u < 1)
    (hzero : riemannZeta ((u : ℂ) + I * v) = 0) :
    Tendsto
      (selectedLocalizedZeroResidueSumAtCenter q
        (localizedNearZeroFilter
          ((u : ℂ) + I * v) (centeredPoleRadius q)) u v)
      atTop
      (𝓝 (analyticOrderNatAt riemannZeta
        ((u : ℂ) + I * v) : ℂ)) :=
  tendsto_selectedLocalizedZeroResidueSumAtCenter_nearZeroFilter
    q hq hu hu1 hzero

example (q : ℝ) {u v : ℝ}
    (hq : 16 ≤ q) (hu : 0 < u) (hu1 : u < 1)
    (hne : riemannZeta ((u : ℂ) + I * v) ≠ 0) :
    Tendsto
      (selectedLocalizedZeroResidueSumAtCenter q
        (localizedNearZeroFilter
          ((u : ℂ) + I * v) (centeredPoleRadius q)) u v)
      atTop (𝓝 0) :=
  tendsto_selectedLocalizedZeroResidueSumAtCenter_nearZeroFilter_of_ne_zero
    q hq hu hu1 hne

end PrimeNumberTheorem.VKEdgePiOverTwo
