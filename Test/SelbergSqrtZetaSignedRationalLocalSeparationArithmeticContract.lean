import HardyTheorem.SelbergSqrtZetaSignedRationalLocalSeparationArithmetic

open Complex MeasureTheory
open scoped BigOperators

namespace HardyTheorem

example {N X : ℕ}
    (hS : (selbergSqrtZetaSignedRationalSupport N X).Nontrivial)
    {q : ℚ} (hq : q ∈ selbergSqrtZetaSignedRationalSupport N X) :
    1 / ((N * X ^ 2 : ℕ) : ℝ) ≤
      PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
        (selbergSqrtZetaSignedRationalSupport N X)
        selbergSqrtZetaSignedRationalFrequency q :=
  one_div_nat_mul_sq_le_localFrequencySeparation_of_mem_rationalSupport
    hS hq

example {N X : ℕ} (hN : 0 < N) (hX : 0 < X)
    (hS : (selbergSqrtZetaSignedRationalSupport N X).Nontrivial) :
    (∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) /
          PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
            (selbergSqrtZetaSignedRationalSupport N X)
            selbergSqrtZetaSignedRationalFrequency q) ≤
      ((N * X ^ 2 : ℕ) : ℝ) *
        ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
          Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) :=
  sum_normSq_div_localFrequencySeparation_le_arithmeticEnergy
    hN hX hS

example (N X : ℕ) {a b : ℝ} (hab : a ≤ b)
    (hN : 0 < N) (hX : 0 < X)
    (hS : (selbergSqrtZetaSignedRationalSupport N X).Nontrivial) :
    (∫ t in a..b,
        Complex.normSq
          (selbergSqrtZetaSignedRationalCollectedPolynomial N X t)) ≤
      (b - a + 4 * Real.pi * ((N * X ^ 2 : ℕ) : ℝ)) *
        ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
          Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) :=
  integral_normSq_rationalCollectedPolynomial_le_arithmeticEnergy
    N X hab hN hX hS

end HardyTheorem
