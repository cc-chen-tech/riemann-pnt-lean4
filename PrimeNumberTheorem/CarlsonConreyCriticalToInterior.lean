import PrimeNumberTheorem.CarlsonConreyCriticalBoundaryReduction

/-!
# End-to-end critical-moment to Carlson interior-moment bridge

This composes the exact Conrey product normalization, pole removal,
Hilbert-valued three-lines theorem, right-boundary plateau decay, and finite
Gaussian covering.  The only remaining hypotheses are the two one-scale
critical-line product moments themselves.
-/

open Complex Set MeasureTheory

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- Exact critical-boundary norm majorant produced by two one-scale Conrey
product moment bounds. -/
noncomputable def carlsonConreyCriticalEndpointBound
    (Delta : ℝ) (Y0 Y1 : ℕ) (C0 C1 : ℝ) : ℝ :=
  Real.exp ((1 / 2 : ℝ) ^ 2 / Delta ^ 2) *
    (2 * conreyOuterMultiplier Y0 Y1 ^ 2 *
        (2 * C1 + 2 * Real.sqrt (Real.pi / (1 / Delta ^ 2))) +
      2 * conreyInnerMultiplier Y0 Y1 ^ 2 *
        (2 * C0 + 2 * Real.sqrt (Real.pi / (1 / Delta ^ 2))))

/-- Exact `Re(s)=4` norm majorant from the inverse-cube plateau tail. -/
noncomputable def carlsonConreyRightEndpointBound
    (Delta : ℝ) (Y0 : ℕ) : ℝ :=
  Real.exp (16 / Delta ^ 2) *
    ((10 / 3 : ℝ) * (1 / (Y0 : ℝ) ^ 3)) ^ 2 *
      Real.sqrt (Real.pi / (1 / Delta ^ 2))

/-- Exact local `Re(s)=2/3` norm majorant after interpolation. -/
noncomputable def carlsonConreyTwoThirdsLocalBound
    (Delta : ℝ) (Y0 Y1 : ℕ) (C0 C1 : ℝ) : ℝ :=
  carlsonConreyCriticalEndpointBound Delta Y0 Y1 C0 C1 ^ (20 / 21 : ℝ) *
    carlsonConreyRightEndpointBound Delta Y0 ^ (1 / 21 : ℝ)

/-- The endpoint and interpolated bounds are nonnegative when the two product
moment bounds are nonnegative. -/
theorem carlsonConreyTwoThirdsLocalBound_nonneg
    {Delta C0 C1 : ℝ} {Y0 Y1 : ℕ} (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) :
    0 ≤ carlsonConreyTwoThirdsLocalBound Delta Y0 Y1 C0 C1 := by
  unfold carlsonConreyTwoThirdsLocalBound
  exact mul_nonneg (Real.rpow_nonneg (by
    unfold carlsonConreyCriticalEndpointBound
    positivity) _) (Real.rpow_nonneg (by
      unfold carlsonConreyRightEndpointBound
      positivity) _)

/-- Two uniform one-scale Conrey product moments imply the ordinary
two-scale Carlson error second-moment bound on a full interval. -/
theorem integral_indicator_Icc_norm_sq_twoScaleMollifiedZetaError_two_thirds_le_of_conrey_products
    {Delta U V C0 C1 : ℝ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1)
    (hProductInt0 : ∀ w ∈ carlsonGaussianCoverCenters Delta U V,
      Integrable fun t : ℝ => carlsonGaussianWeight Delta w t *
        ‖linearLogSelbergMollifiedZetaProduct Y0
          (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2)
    (hProductInt1 : ∀ w ∈ carlsonGaussianCoverCenters Delta U V,
      Integrable fun t : ℝ => carlsonGaussianWeight Delta w t *
        ‖linearLogSelbergMollifiedZetaProduct Y1
          (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2)
    (hProductBound0 : ∀ w ∈ carlsonGaussianCoverCenters Delta U V,
      (∫ t : ℝ, carlsonGaussianWeight Delta w t *
        ‖linearLogSelbergMollifiedZetaProduct Y0
          (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2) ≤ C0)
    (hProductBound1 : ∀ w ∈ carlsonGaussianCoverCenters Delta U V,
      (∫ t : ℝ, carlsonGaussianWeight Delta w t *
        ‖linearLogSelbergMollifiedZetaProduct Y1
          (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2) ≤ C1) :
    (∫ t : ℝ, (Icc U V).indicator (fun t =>
        ‖twoScaleMollifiedZetaError Y0 Y1
          (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2) t) ≤
      Real.exp (1 / 4 : ℝ) *
        (((Nat.floor ((V - U) / Delta) + 1 : ℕ) : ℝ) *
          (25 * carlsonConreyTwoThirdsLocalBound
            Delta Y0 Y1 C0 C1)) := by
  have hY0one : 1 ≤ Y0 := by omega
  apply integral_indicator_Icc_norm_sq_twoScaleMollifiedZetaError_two_thirds_le
    hDelta hY0one hY01
    (carlsonConreyTwoThirdsLocalBound_nonneg hC0 hC1)
  intro w hw
  have hcriticalOriginal :=
    norm_sq_carlsonGaussianPoleFreeLpValue_half_le_of_conrey_product_components
      hDelta hY0 hY01 (hProductInt0 w hw) (hProductInt1 w hw)
        (hProductBound0 w hw) (hProductBound1 w hw)
  have hcriticalTotal :
      ‖carlsonGaussianPoleFreeLpValueTotal Delta w Y0 Y1
          hDelta hY0one hY01 ((1 / 2 : ℝ) : ℂ)‖ ^ 2 ≤
        carlsonConreyCriticalEndpointBound Delta Y0 Y1 C0 C1 := by
    rw [carlsonGaussianPoleFreeLpValueTotal_eq hDelta hY0one hY01
      (by norm_num : (((1 / 2 : ℝ) : ℂ).re) ∈ Icc (1 / 2 : ℝ) 4)]
    simpa [carlsonConreyCriticalEndpointBound] using hcriticalOriginal
  have hinterp :=
    norm_sq_carlsonGaussianPoleFreeLpValueTotal_two_thirds_le_of_left_bound
      hDelta hY0one hY01 hcriticalTotal
  rw [carlsonGaussianPoleFreeLpValueTotal_eq hDelta hY0one hY01
    (by norm_num : (((2 / 3 : ℝ) : ℂ).re) ∈ Icc (1 / 2 : ℝ) 4)] at hinterp
  simpa [carlsonConreyTwoThirdsLocalBound,
    carlsonConreyRightEndpointBound] using hinterp

end CarlsonZeroDensity
end PrimeNumberTheorem
