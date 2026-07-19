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

#print axioms carneiroLittmannCumulative_nonneg_of_nonpos
#print axioms one_le_carneiroLittmannCumulative_of_nonneg
#print axioms carneiroLittmannKernelError_nonneg
#print axioms carneiroLittmannKernelError_dilation_antitone

end DirichletPolynomial
end PrimeNumberTheorem
