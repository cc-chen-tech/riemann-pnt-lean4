import PrimeNumberTheorem.VKEdgeResidualAmplificationNoGo

open PrimeNumberTheorem.VKEdgePiOverTwo

open scoped Interval

namespace Test

#check
  (@integral_Icc_cosinePairModel_sq_ge :
    ∀ {m gamma phase a b : ℝ},
      a ≤ b →
      gamma ≠ 0 →
      2 * m ^ 2 * (b - a) - 2 * m ^ 2 / |gamma| ≤
        ∫ y in Set.Icc a b,
          cosinePairModel m gamma phase y ^ 2)

#check
  (@integral_Icc_cosinePairModel_sq_ge_linear :
    ∀ {m gamma phase a b : ℝ},
      a ≤ b →
      gamma ≠ 0 →
      2 / |gamma| ≤ b - a →
      m ^ 2 * (b - a) ≤
        ∫ y in Set.Icc a b,
          cosinePairModel m gamma phase y ^ 2)

#check
  (@pureCosineModel_linearEnergy_and_annihilator_zero :
    ∀ {m gamma phase a b h : ℝ},
      a ≤ b →
      gamma ≠ 0 →
      2 / |gamma| ≤ b - a →
      m ^ 2 * (b - a) ≤
          ∫ y in Set.Icc a b,
            cosinePairModel m gamma phase y ^ 2 ∧
        (∫ y in Set.Icc a b,
          symmetricFrequencyAnnihilator h gamma
            (cosinePairModel m gamma phase) y ^ 2) = 0)

end Test
