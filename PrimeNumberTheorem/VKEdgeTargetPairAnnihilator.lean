import PrimeNumberTheorem.VKEdgeResidualAmplification

open Complex MeasureTheory Set

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- The symmetric three-point detector with prescribed killed frequency. -/
def symmetricFrequencyAnnihilator
    (h gamma : ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  f (y + h) - 2 * Real.cos (gamma * h) * f y + f (y - h)

/-- A cosine of frequency `lambda` is an eigenfunction of the symmetric
detector, with the displayed exact multiplier. -/
theorem symmetricFrequencyAnnihilator_cosineZeroPair
    (h gamma m lambda phase y : ℝ) :
    symmetricFrequencyAnnihilator h gamma
        (cosineZeroPair m lambda phase) y =
      2 * (Real.cos (lambda * h) - Real.cos (gamma * h)) *
        cosineZeroPair m lambda phase y := by
  have hplus :
      Real.cos (lambda * (y + h) - phase) =
        Real.cos (lambda * y - phase) * Real.cos (lambda * h) -
          Real.sin (lambda * y - phase) * Real.sin (lambda * h) := by
    rw [show lambda * (y + h) - phase =
      (lambda * y - phase) + lambda * h by ring]
    exact Real.cos_add _ _
  have hminus :
      Real.cos (lambda * (y - h) - phase) =
        Real.cos (lambda * y - phase) * Real.cos (lambda * h) +
          Real.sin (lambda * y - phase) * Real.sin (lambda * h) := by
    rw [show lambda * (y - h) - phase =
      (lambda * y - phase) - lambda * h by ring]
    exact Real.cos_sub _ _
  simp only [symmetricFrequencyAnnihilator, cosineZeroPair]
  rw [hplus, hminus]
  ring

/-- The detector annihilates the selected conjugate cosine pair pointwise. -/
theorem symmetricFrequencyAnnihilator_targetPair_eq_zero
    (h gamma m phase y : ℝ) :
    symmetricFrequencyAnnihilator h gamma
        (cosineZeroPair m gamma phase) y = 0 := by
  rw [symmetricFrequencyAnnihilator_cosineZeroPair]
  ring

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
