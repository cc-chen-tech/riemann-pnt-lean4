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

#print axioms carneiroLittmannDerivative_neg_one
#print axioms carneiroLittmannDerivative_zero
#print axioms carneiroLittmannDerivative_eq_formula
#print axioms carneiroLittmannDerivative_nonneg_of_neg
#print axioms carneiroLittmannDerivative_nonpos_of_pos
#print axioms mul_carneiroLittmannDerivative_nonpos

end DirichletPolynomial
end PrimeNumberTheorem
