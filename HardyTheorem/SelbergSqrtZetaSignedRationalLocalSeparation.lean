import HardyTheorem.SelbergSqrtZetaSignedRationalRealCollected
import PrimeNumberTheorem.CarneiroLittmannProfile

/-!
# Local-separation mean square for the signed rational Selberg model

The pairwise reciprocal-gap budget treats every off-diagonal pair
independently.  The Montgomery--Vaughan inequality instead charges each
collected rational frequency only by its nearest-neighbour separation.  This
is the form in which the reduced-ratio arithmetic can control the model
without a quadratic collision loss.
-/

open Complex MeasureTheory
open scoped BigOperators

namespace HardyTheorem

/-- The rationally collected signed phase has a Montgomery--Vaughan
mean-square bound involving only the local separation at each supported
frequency. -/
theorem
    integral_normSq_selbergSqrtZetaSignedRationalCollectedPolynomial_le_localSeparation
    (N X : ℕ) {a b : ℝ} (hab : a ≤ b)
    (hS : (selbergSqrtZetaSignedRationalSupport N X).Nontrivial) :
    (∫ t in a..b,
        Complex.normSq
          (selbergSqrtZetaSignedRationalCollectedPolynomial N X t)) ≤
      (b - a) *
          ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
            Complex.normSq
              (selbergSqrtZetaSignedRationalCoeff N X q) +
        4 * Real.pi *
          ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
            Complex.normSq
                (selbergSqrtZetaSignedRationalCoeff N X q) /
              PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
                (selbergSqrtZetaSignedRationalSupport N X)
                selbergSqrtZetaSignedRationalFrequency q := by
  have hmean :=
    PrimeNumberTheorem.DirichletPolynomial.finiteExponentialSum_meanSquare_le_localSeparation
      (S := selbergSqrtZetaSignedRationalSupport N X)
      (c := selbergSqrtZetaSignedRationalCoeff N X)
      (omega := selbergSqrtZetaSignedRationalFrequency)
      hab hS (selbergSqrtZetaSignedRationalFrequency_injOn N X)
  simpa only [
    selbergSqrtZetaSignedRationalCollectedPolynomial,
    MathlibAux.exponentialPolynomial,
    PrimeNumberTheorem.DirichletPolynomial.finiteExponentialSum,
    Complex.normSq_eq_norm_sq] using hmean

end HardyTheorem
