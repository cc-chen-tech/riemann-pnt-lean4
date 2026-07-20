import PrimeNumberTheorem.CarneiroLittmannNormalization

namespace PrimeNumberTheorem
namespace DirichletPolynomial

example (x : ℝ) : 0 ≤ carneiroLittmannSincSquareBase x :=
  carneiroLittmannSincSquareBase_nonneg x

example (x : ℝ) :
    carneiroLittmannSincSquareBase x ≤
      4 * (1 + ‖x‖) ^ (-2 : ℝ) :=
  carneiroLittmannSincSquareBase_le_japanese x

example : MeasureTheory.Integrable carneiroLittmannSincSquareBase :=
  integrable_carneiroLittmannSincSquareBase

example : MeasureTheory.Integrable carneiroLittmannSincSquare :=
  integrable_carneiroLittmannSincSquare

example (x : ℝ) :
    (∫ t : ℝ in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
      Complex.exp ((2 * Real.pi * x * t : ℝ) * Complex.I)) =
        (Real.sinc (Real.pi * x) : ℂ) :=
  intervalIntegral_cexp_two_pi_mul_eq_sinc x

example :
    (∫ x, carneiroLittmannSincSquare x) =
      ∫ x, carneiroLittmannSincSquareBase x :=
  integral_carneiroLittmannSincSquare_eq_base

example (x : ℝ) :
    carneiroLittmannDerivative x =
      carneiroLittmannTranslationPotential (x + 1) -
        carneiroLittmannTranslationPotential x +
          carneiroLittmannSincSquare x :=
  carneiroLittmannDerivative_eq_translationDifference_add_sincSquare x

example : MeasureTheory.Integrable carneiroLittmannTranslationDifference :=
  integrable_carneiroLittmannTranslationDifference

example : (∫ x, carneiroLittmannTranslationDifference x) = 0 :=
  integral_carneiroLittmannTranslationDifference_eq_zero

example :
    (∫ x, carneiroLittmannDerivative x) =
      ∫ x, carneiroLittmannSincSquareBase x :=
  integral_carneiroLittmannDerivative_eq_sincSquareBase

example :
    (∫ x, carneiroLittmannDerivative x) =
      (∫ x, carneiroLittmannTranslationDifference x) +
        ∫ x, carneiroLittmannSincSquareBase x :=
  integral_carneiroLittmannDerivative_eq_translationDifference_add_base

#print axioms carneiroLittmannSincSquareBase_nonneg
#print axioms carneiroLittmannSincSquareBase_le_japanese
#print axioms integrable_carneiroLittmannSincSquareBase
#print axioms integrable_carneiroLittmannSincSquare
#print axioms intervalIntegral_cexp_two_pi_mul_eq_sinc
#print axioms integral_carneiroLittmannSincSquare_eq_base
#print axioms carneiroLittmannDerivative_eq_translationDifference_add_sincSquare
#print axioms integrable_carneiroLittmannTranslationDifference
#print axioms integral_carneiroLittmannTranslationDifference_eq_zero
#print axioms integral_carneiroLittmannDerivative_eq_sincSquareBase
#print axioms integral_carneiroLittmannDerivative_eq_translationDifference_add_base

end DirichletPolynomial
end PrimeNumberTheorem
