import PrimeNumberTheorem.QPowerDetectorAlgebra

open Polynomial

namespace PrimeNumberTheorem.PrimeSideDetector

#check (qPowerNode : Nat → Complex → Complex)
#check (@qPowerNode_one :
  forall {q : Nat}, q ≠ 0 → qPowerNode q 1 = ((q : Real)⁻¹ : Complex))
#check (evalRealPolynomial : Polynomial Real → Complex → Complex)
#check (realNodeFactor : Real → Polynomial Real)
#check (conjugatePairFactor : Complex → Polynomial Real)
#check (realLinearInterpolator : Complex → Complex → Polynomial Real)

#check (evalRealPolynomial_realNodeFactor_self :
  forall r : Real, evalRealPolynomial (realNodeFactor r) r = 0)

#check (evalRealPolynomial_conjugatePairFactor_left :
  forall z : Complex, evalRealPolynomial (conjugatePairFactor z) z = 0)

#check (evalRealPolynomial_conjugatePairFactor_right :
  forall z : Complex,
    evalRealPolynomial (conjugatePairFactor z) (star z) = 0)

#check (@evalRealPolynomial_realLinearInterpolator :
  forall {z w : Complex},
    (z.im = 0 → w.im = 0) →
    evalRealPolynomial (realLinearInterpolator z w) z = w)

#check (qPowerAnnihilator :
  Nat → Finset Real → Finset Complex → Polynomial Real)

#check (@normalizedQPowerPolynomial :
  Nat → Finset Real → Finset Complex → Complex → Polynomial Real)

#check (@normalizedQPowerPolynomial_eval_target :
  forall {q : Nat} {realNodes : Finset Real}
      {pairNodes : Finset Complex} {z0 : Complex},
    evalRealPolynomial (qPowerAnnihilator q realNodes pairNodes) z0 ≠ 0 →
    evalRealPolynomial
      (normalizedQPowerPolynomial q realNodes pairNodes z0) z0 = 1)

#check (@normalizedQPowerPolynomial_eval_main :
  forall {q : Nat} {realNodes : Finset Real}
      {pairNodes : Finset Complex} {z0 : Complex},
    q ≠ 0 →
    evalRealPolynomial
      (normalizedQPowerPolynomial q realNodes pairNodes z0)
      ((q : Real)⁻¹) = 0)

#check (@normalizedQPowerPolynomial_eval_realNode :
  forall {q : Nat} {realNodes : Finset Real}
      {pairNodes : Finset Complex} {z0 : Complex} {r : Real},
    r ∈ realNodes →
    evalRealPolynomial
      (normalizedQPowerPolynomial q realNodes pairNodes z0) r = 0)

#check (@normalizedQPowerPolynomial_eval_pairNode :
  forall {q : Nat} {realNodes : Finset Real}
      {pairNodes : Finset Complex} {z0 z : Complex},
    z ∈ pairNodes →
    evalRealPolynomial
      (normalizedQPowerPolynomial q realNodes pairNodes z0) z = 0)

#check (qPowerDetector : Nat → Polynomial Real → Complex → Complex)

#check (qPowerDetector_eq_polynomial_eval :
  forall (q : Nat) (H : Polynomial Real) (s : Complex),
    qPowerDetector q H s = evalRealPolynomial H (qPowerNode q s))

#check (qPowerDetector_eq_coeff_sum :
  forall (q : Nat) (H : Polynomial Real) (s : Complex),
    qPowerDetector q H s =
      ∑ k ∈ H.support, (H.coeff k : Complex) * (qPowerNode q s) ^ k)

#check (normalizedQPowerDetector :
  Nat → Finset Real → Finset Complex → Complex → Complex → Complex)

#check (@normalizedQPowerDetector_at_target :
  forall {q : Nat} {realNodes : Finset Real}
      {pairNodes : Finset Complex} {s0 : Complex},
    evalRealPolynomial (qPowerAnnihilator q realNodes pairNodes)
        (qPowerNode q s0) ≠ 0 →
    normalizedQPowerDetector q realNodes pairNodes s0 s0 = 1)

#check (@normalizedQPowerDetector_at_one :
  forall {q : Nat} {realNodes : Finset Real}
      {pairNodes : Finset Complex} {s0 : Complex},
    q ≠ 0 → normalizedQPowerDetector q realNodes pairNodes s0 1 = 0)

end PrimeNumberTheorem.PrimeSideDetector
