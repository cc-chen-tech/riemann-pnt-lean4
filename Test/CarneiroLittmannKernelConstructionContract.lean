import PrimeNumberTheorem.CarneiroLittmannKernelConstruction

namespace PrimeNumberTheorem
namespace DirichletPolynomial

example {x : ℝ} (hx : x ≤ 0) :
    0 ≤ carneiroLittmannCumulative x :=
  carneiroLittmannCumulative_nonneg_of_nonpos hx

example {x : ℝ} (hx : 0 ≤ x) :
    1 ≤ carneiroLittmannCumulative x :=
  one_le_carneiroLittmannCumulative_of_nonneg hx

example (x : ℝ) : 0 ≤ carneiroLittmannKernelError x :=
  carneiroLittmannKernelError_nonneg x

example {deltaSmall deltaLarge : ℝ}
    (hsmall : 0 < deltaSmall) (hle : deltaSmall ≤ deltaLarge) (t : ℝ) :
    carneiroLittmannKernelError (deltaLarge * t) ≤
      carneiroLittmannKernelError (deltaSmall * t) :=
  carneiroLittmannKernelError_dilation_antitone hsmall hle t

example {x : ℝ} (hx : 1 ≤ x) :
    carneiroLittmannKernelError x ≤ x ^ (-2 : ℝ) / 2 :=
  carneiroLittmannKernelError_le_rpow_neg_two_of_one_le hx

example {x : ℝ} (hx : x ≤ -2) :
    carneiroLittmannKernelError x ≤ 2 * (-x) ^ (-2 : ℝ) :=
  carneiroLittmannKernelError_le_two_mul_neg_rpow_neg_two_of_le_neg_two hx

example : MeasureTheory.Integrable carneiroLittmannKernelError :=
  integrable_carneiroLittmannKernelError

#print axioms carneiroLittmannCumulative_nonneg_of_nonpos
#print axioms one_le_carneiroLittmannCumulative_of_nonneg
#print axioms carneiroLittmannKernelError_nonneg
#print axioms carneiroLittmannKernelError_dilation_antitone
#print axioms carneiroLittmannKernelError_le_rpow_neg_two_of_one_le
#print axioms carneiroLittmannKernelError_le_two_mul_neg_rpow_neg_two_of_le_neg_two
#print axioms integrable_carneiroLittmannKernelError

end DirichletPolynomial
end PrimeNumberTheorem
