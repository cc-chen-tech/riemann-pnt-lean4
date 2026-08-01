import PrimeNumberTheorem.QPowerDetectorMass

open Polynomial
open scoped BigOperators

namespace PrimeNumberTheorem.PrimeSideDetector

#check (polynomialPositiveMassAt : Real → Polynomial Real → Real)
#check (polynomialNegativeMassAt : Real → Polynomial Real → Real)
#check (polynomialWeightedL1At : Real → Polynomial Real → Real)

#check (polynomial_eval_eq_positive_sub_negative :
  forall (r : Real) (p : Polynomial Real),
    p.eval r = polynomialPositiveMassAt r p -
      polynomialNegativeMassAt r p)

#check (@polynomialNegativeMassAt_eq_half_weightedL1At :
  forall {r : Real} {p : Polynomial Real},
    0 ≤ r → p.eval r = 0 →
    polynomialNegativeMassAt r p = polynomialWeightedL1At r p / 2)

#check (@normalizedQPowerPolynomial_negativeMass_eq_half :
  forall {q : Nat} {realNodes : Finset Real}
      {pairNodes : Finset Complex} {z0 : Complex},
    q ≠ 0 →
    polynomialNegativeMassAt ((q : Real)⁻¹)
        (normalizedQPowerPolynomial q realNodes pairNodes z0) =
      polynomialWeightedL1At ((q : Real)⁻¹)
        (normalizedQPowerPolynomial q realNodes pairNodes z0) / 2)

end PrimeNumberTheorem.PrimeSideDetector
