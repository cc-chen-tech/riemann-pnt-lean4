import PrimeNumberTheorem.VKEdgePiOverTwoGaussianMellin

open Complex MeasureTheory

open PrimeNumberTheorem.VKEdgePiOverTwo

#check integral_verticalGaussian_eq

example {m : ℝ} (hm : 0 < m) (c r : ℝ) :
    (∫ t : ℝ,
        Complex.exp
          ((m : ℂ) * ((c : ℂ) + I * t) ^ 2 +
            (r : ℂ) * ((c : ℂ) + I * t))) =
      (2 * Real.pi : ℂ) * (normalizedGaussian m r : ℂ) :=
  integral_verticalGaussian_eq hm c r
