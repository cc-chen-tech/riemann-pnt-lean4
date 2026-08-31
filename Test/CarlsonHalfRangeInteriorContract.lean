import PrimeNumberTheorem.CarlsonHalfRangeInterior

open Complex Filter MeasureTheory Set
open PrimeNumberTheorem.CarlsonZeroDensity

example {Delta U V w : ℝ} (hDelta : 0 < Delta) (hUV : U ≤ V)
    (hw : w ∈ carlsonGaussianCoverCenters Delta U V) :
    U ≤ w ∧ w ≤ V + Delta / 2 :=
  carlsonGaussianCoverCenters_mem_bounds hDelta hUV hw

example : ∀ᶠ V : ℝ in atTop, 0 < 16 * V ^ (19 / 20 : ℝ) ∧
    16 * V ^ (19 / 20 : ℝ) ≤ V :=
  eventually_halfRangeDelta_pos_le_height

example : ∃ C > (0 : ℝ), ∀ᶠ V : ℝ in atTop, ∀ Y0 Y1 : ℕ,
    2 ≤ Y0 → Y0 < Y1 → (Y1 : ℝ) ≤ V ^ (9 / 20 : ℝ) →
    let Delta := 16 * V ^ (19 / 20 : ℝ)
    let B := C * V ^ (19 / 20 : ℝ) * (1 + Real.log V) ^ 6
    (∫ t : ℝ, (Icc (2 * V) (5 * V / 2)).indicator (fun t =>
      ‖twoScaleMollifiedZetaError Y0 Y1
        (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2) t) ≤
      Real.exp (1 / 4 : ℝ) *
        (((Nat.floor (((5 * V / 2) - 2 * V) / Delta) + 1 : ℕ) : ℝ) *
          (25 * carlsonConreyTwoThirdsLocalBound Delta Y0 Y1 B B)) :=
  exists_eventually_halfRange_interior_moment_le_explicit

#print axioms carlsonGaussianCoverCenters_mem_bounds
#print axioms eventually_halfRangeDelta_pos_le_height
#print axioms exists_eventually_halfRange_interior_moment_le_explicit
