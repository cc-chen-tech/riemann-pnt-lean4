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

private theorem symmetricFrequencyAnnihilator_sub
    (h gamma : ℝ) (f p : ℝ → ℝ) (y : ℝ) :
    symmetricFrequencyAnnihilator h gamma (fun z => f z - p z) y =
      symmetricFrequencyAnnihilator h gamma f y -
        symmetricFrequencyAnnihilator h gamma p y := by
  simp only [symmetricFrequencyAnnihilator]
  ring

/-- The normalized PNT error after applying the detector which kills the
selected zero ordinate. -/
def annihilatedNormalizedPsiError
    (rho : ℂ) (h y : ℝ) : ℝ :=
  symmetricFrequencyAnnihilator h rho.im (normalizedPsiError rho) y

/-- Applying the detector to the full normalized error is exactly the same as
applying it to the residual after subtracting the selected conjugate pair. -/
theorem annihilatedNormalizedPsiError_eq_residual
    (rho : ℂ) (h y : ℝ) :
    annihilatedNormalizedPsiError rho h y =
      symmetricFrequencyAnnihilator h rho.im
        (normalizedPsiResidual rho) y := by
  have htarget :
      symmetricFrequencyAnnihilator h rho.im
          (normalizedTargetZeroPair rho) y = 0 := by
    simpa only [normalizedTargetZeroPair] using
      symmetricFrequencyAnnihilator_targetPair_eq_zero
        h rho.im (analyticOrderNatAt riemannZeta rho : ℝ) rho.arg y
  unfold annihilatedNormalizedPsiError normalizedPsiResidual
  rw [symmetricFrequencyAnnihilator_sub, htarget, sub_zero]

/-- Exact arithmetic form of the target-annihilated detector: a signed
three-scale correlation of the classical PNT error. -/
theorem annihilatedNormalizedPsiError_eq_threeScale
    (rho : ℂ) (h y : ℝ) :
    annihilatedNormalizedPsiError rho h y =
      ‖rho‖ * Real.exp (-rho.re * y) *
        (Real.exp (-rho.re * h) *
            (chebyshevPsi (Real.exp (y + h)) - Real.exp (y + h)) -
          2 * Real.cos (rho.im * h) *
            (chebyshevPsi (Real.exp y) - Real.exp y) +
          Real.exp (rho.re * h) *
            (chebyshevPsi (Real.exp (y - h)) - Real.exp (y - h))) := by
  have hplus :
      Real.exp (-rho.re * (y + h)) =
        Real.exp (-rho.re * y) * Real.exp (-rho.re * h) := by
    rw [show -rho.re * (y + h) = -rho.re * y + -rho.re * h by ring,
      Real.exp_add]
  have hminus :
      Real.exp (-rho.re * (y - h)) =
        Real.exp (-rho.re * y) * Real.exp (rho.re * h) := by
    rw [show -rho.re * (y - h) = -rho.re * y + rho.re * h by ring,
      Real.exp_add]
  simp only [annihilatedNormalizedPsiError, symmetricFrequencyAnnihilator,
    normalizedPsiError, hplus, hminus]
  ring

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
