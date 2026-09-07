import PrimeNumberTheorem.CarlsonGaussianLeftStrip

open Complex MeasureTheory Set
open PrimeNumberTheorem.CarlsonZeroDensity

-- The regularizer bound must hold on the whole closed left strip,
-- not just at its right endpoint.
example {s : ℂ} (hs : s.re ∈ Icc (1 / 2 : ℝ) (2 / 3)) :
    ‖(s + 1) / (s - 1)‖ ≤ 5 :=
  norm_add_one_div_sub_one_le_five_on_leftStrip hs

-- Both genuine integrability and the quantitative moment survive moving
-- the line; this rules out relying on a nonintegrable default integral.
example {Delta w x : ℝ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    (hx : x ∈ Icc (1 / 2 : ℝ) (2 / 3)) :
    Integrable (fun t : ℝ => carlsonGaussianWeight Delta w t *
      ‖twoScaleMollifiedZetaError Y0 Y1 ((x : ℂ) + I * (t : ℂ))‖ ^ 2) ∧
    (∫ t : ℝ, carlsonGaussianWeight Delta w t *
      ‖twoScaleMollifiedZetaError Y0 Y1 ((x : ℂ) + I * (t : ℂ))‖ ^ 2) ≤
      25 * ‖carlsonGaussianPoleFreeLpValueTotal Delta w Y0 Y1
        hDelta hY0 hY01 (x : ℂ)‖ ^ 2 :=
  gaussian_twoScaleError_leftStrip_integrable_and_le hDelta hY0 hY01 hx

example {Delta U V x L : ℝ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    (hx : x ∈ Icc (1 / 2 : ℝ) (2 / 3)) (hL : 0 ≤ L)
    (hLocal : ∀ w ∈ carlsonGaussianCoverCenters Delta U V,
      ‖carlsonGaussianPoleFreeLpValueTotal Delta w Y0 Y1
        hDelta hY0 hY01 (x : ℂ)‖ ^ 2 ≤ L) :
    (∫ t : ℝ, (Icc U V).indicator (fun t =>
      ‖twoScaleMollifiedZetaError Y0 Y1 ((x : ℂ) + I * (t : ℂ))‖ ^ 2) t) ≤
      Real.exp (1 / 4 : ℝ) *
        (((Nat.floor ((V - U) / Delta) + 1 : ℕ) : ℝ) * (25 * L)) :=
  integral_indicator_Icc_twoScaleError_leftStrip_le hDelta hY0 hY01 hx hL hLocal

#print axioms norm_add_one_div_sub_one_le_five_on_leftStrip
#print axioms gaussian_twoScaleError_leftStrip_integrable_and_le
#print axioms integral_indicator_Icc_twoScaleError_leftStrip_le
