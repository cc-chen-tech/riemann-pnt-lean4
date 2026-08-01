import PrimeNumberTheorem.QPowerDetectorScaleBarrier

open Polynomial

namespace PrimeNumberTheorem.PrimeSideDetector

#check (norm_evalRealPolynomial_le_polynomialWeightedL1At_norm :
  forall (p : Polynomial Real) (z : Complex),
    ‖evalRealPolynomial p z‖ ≤ polynomialWeightedL1At ‖z‖ p)

#check (@polynomialWeightedL1At_le_ratio_pow_of_natDegree_le :
  forall {r R : Real} (p : Polynomial Real) (N : Nat),
    0 < r → r ≤ R → p.natDegree ≤ N →
      polynomialWeightedL1At R p ≤
        (R / r) ^ N * polynomialWeightedL1At r p)

#check (norm_qPowerNode :
  forall {q : Nat} (s : Complex), 0 < q →
    ‖qPowerNode q s‖ = (q : Real) ^ (-s.re))

#check (@qPowerDetector_weightedL1At_one_lower :
  forall {q N : Nat} {p : Polynomial Real} {s0 : Complex},
    1 < q → s0.re ≤ 1 → p.natDegree ≤ N →
      qPowerDetector q p s0 = 1 →
        (((q : Real)⁻¹ / ‖qPowerNode q s0‖) ^ N) ≤
          polynomialWeightedL1At ((q : Real)⁻¹) p)

#check (@qPowerDetector_negativeMassAt_one_lower :
  forall {q N : Nat} {p : Polynomial Real} {s0 : Complex},
    1 < q → s0.re ≤ 1 → p.natDegree ≤ N →
      qPowerDetector q p s0 = 1 → qPowerDetector q p 1 = 0 →
        (1 / 2 : Real) *
            (((q : Real)⁻¹ / ‖qPowerNode q s0‖) ^ N) ≤
          polynomialNegativeMassAt ((q : Real)⁻¹) p)

#check (@qPowerDetector_supportCompatible_negativeMass_loss :
  forall {q N : Nat} {p : Polynomial Real} {s0 : Complex} {x : Real},
    1 < q → s0.re < 1 → p.natDegree ≤ N →
      qPowerDetector q p s0 = 1 → qPowerDetector q p 1 = 0 →
      0 < x → (q : Real) ^ N ≤ x →
        x ^ s0.re / 2 ≤
          x * polynomialNegativeMassAt ((q : Real)⁻¹) p)

end PrimeNumberTheorem.PrimeSideDetector
