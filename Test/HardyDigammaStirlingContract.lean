import HardyTheorem.VerticalGammaAsymptotic

open Complex MeasureTheory Set

example {z : ℂ} (hz : 0 < z.re) :
    Complex.digamma z =
      Complex.log z - (2 * z)⁻¹ - (12 * z ^ 2)⁻¹ +
        ∫ u in Set.Ioi (0 : ℝ),
          ((periodizedBernoulli 2 (u : AddCircle (1 : ℝ)) : ℝ) : ℂ) /
            (z + u) ^ 3 :=
  HardyTheorem.digamma_eq_stirling_with_periodizedBernoulli hz
