import PrimeNumberTheorem.CarneiroLittmannExtremal

namespace PrimeNumberTheorem
namespace DirichletPolynomial

example : carneiroLittmannDerivative (-1) = 1 :=
  carneiroLittmannDerivative_neg_one

example : carneiroLittmannDerivative 0 = 0 :=
  carneiroLittmannDerivative_zero

example (x : ℝ) (hxNegOne : x ≠ -1) (hxZero : x ≠ 0) :
    carneiroLittmannDerivative x =
      -(Real.sin (Real.pi * x)) ^ 2 /
        (Real.pi ^ 2 * x * (x + 1) ^ 2) :=
  carneiroLittmannDerivative_eq_formula hxNegOne hxZero

example {x : ℝ} (hx : x < 0) :
    0 ≤ carneiroLittmannDerivative x :=
  carneiroLittmannDerivative_nonneg_of_neg hx

example {x : ℝ} (hx : 0 < x) :
    carneiroLittmannDerivative x ≤ 0 :=
  carneiroLittmannDerivative_nonpos_of_pos hx

example (x : ℝ) : x * carneiroLittmannDerivative x ≤ 0 :=
  mul_carneiroLittmannDerivative_nonpos x

example {x : ℝ} (hxNegOne : x ≠ -1) :
    carneiroLittmannDerivative x =
      -x * (Real.sinc (Real.pi * x)) ^ 2 / (x + 1) ^ 2 :=
  carneiroLittmannDerivative_eq_sinc_zeroChart hxNegOne

example {x : ℝ} (hxZero : x ≠ 0) :
    carneiroLittmannDerivative x =
      -(Real.sinc (Real.pi * (x + 1))) ^ 2 / x :=
  carneiroLittmannDerivative_eq_sinc_negOneChart hxZero

example : ContinuousAt carneiroLittmannDerivative 0 :=
  continuousAt_carneiroLittmannDerivative_zero

example : ContinuousAt carneiroLittmannDerivative (-1) :=
  continuousAt_carneiroLittmannDerivative_neg_one

example : Continuous carneiroLittmannDerivative :=
  continuous_carneiroLittmannDerivative

example : carneiroLittmannPrimitive 0 = 0 :=
  carneiroLittmannPrimitive_zero

example (x : ℝ) :
    HasDerivAt carneiroLittmannPrimitive (carneiroLittmannDerivative x) x :=
  hasDerivAt_carneiroLittmannPrimitive x

example : MonotoneOn carneiroLittmannPrimitive (Set.Iic 0) :=
  monotoneOn_carneiroLittmannPrimitive_Iic

example : AntitoneOn carneiroLittmannPrimitive (Set.Ici 0) :=
  antitoneOn_carneiroLittmannPrimitive_Ici

#print axioms carneiroLittmannDerivative_neg_one
#print axioms carneiroLittmannDerivative_zero
#print axioms carneiroLittmannDerivative_eq_formula
#print axioms carneiroLittmannDerivative_nonneg_of_neg
#print axioms carneiroLittmannDerivative_nonpos_of_pos
#print axioms mul_carneiroLittmannDerivative_nonpos
#print axioms carneiroLittmannDerivative_eq_sinc_zeroChart
#print axioms carneiroLittmannDerivative_eq_sinc_negOneChart
#print axioms continuousAt_carneiroLittmannDerivative_zero
#print axioms continuousAt_carneiroLittmannDerivative_neg_one
#print axioms continuous_carneiroLittmannDerivative
#print axioms carneiroLittmannPrimitive_zero
#print axioms hasDerivAt_carneiroLittmannPrimitive
#print axioms monotoneOn_carneiroLittmannPrimitive_Iic
#print axioms antitoneOn_carneiroLittmannPrimitive_Ici

end DirichletPolynomial
end PrimeNumberTheorem
