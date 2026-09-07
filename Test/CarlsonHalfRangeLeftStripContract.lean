import PrimeNumberTheorem.CarlsonHalfRangeLeftStrip

open Complex Filter MeasureTheory Set
open PrimeNumberTheorem.CarlsonZeroDensity

-- A single C and eventual threshold work for every allowed line and length.
-- There is no AFE, critical moment, or interpolation hypothesis.
example : ∃ C > (0 : ℝ), ∀ᶠ V : ℝ in atTop, ∀ Y0 Y1 : ℕ,
    2 ≤ Y0 → Y0 < Y1 → (Y1 : ℝ) ≤ V ^ (9 / 20 : ℝ) →
    ∀ x ∈ Icc (1 / 2 : ℝ) (2 / 3),
    let Delta := 16 * V ^ (19 / 20 : ℝ)
    let B := C * V ^ (19 / 20 : ℝ) * (1 + Real.log V) ^ 6
    (∫ t : ℝ, (Icc (2 * V) (5 * V / 2)).indicator (fun t =>
      ‖twoScaleMollifiedZetaError Y0 Y1 ((x : ℂ) + I * (t : ℂ))‖ ^ 2) t) ≤
      Real.exp (1 / 4 : ℝ) *
        (((Nat.floor (((5 * V / 2) - 2 * V) / Delta) + 1 : ℕ) : ℝ) *
          (25 * carlsonConreyLeftStripLocalBound x Delta Y0 Y1 B B)) :=
  exists_eventually_halfRange_leftStrip_moment_le_explicit

#print axioms exists_eventually_halfRange_leftStrip_moment_le_explicit
