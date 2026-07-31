import HardyTheorem.SelbergSqrtZetaSignedRationalCoeffCoprimeRayReindex
import HardyTheorem.SelbergSqrtZetaSignedRationalReducedSeparation

/-!
# Reduced-ray form of the local-separation energy

This file combines two exact inputs:

* the local logarithmic separation at a reduced key `a / b`;
* the coefficient reindexing over the positive scales on the coprime ray
  `(a, b)`.

The resulting bound keeps the scale sum inside `normSq`.  In particular, it
does not discard cancellation between different scales on the same ray.
-/

open scoped BigOperators

namespace HardyTheorem

/-- The local-separation weighted contribution of a supported reduced key is
bounded by the reduced geometric weight times the squared norm of the exact
coefficient sum along its coprime ray. -/
theorem normSq_div_localFrequencySeparation_le_reducedRayWeight
    {N X a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hQ : (selbergSqrtZetaSignedRationalSupport N X).Nontrivial)
    (hq : (a : ℚ) / (b : ℚ) ∈
      selbergSqrtZetaSignedRationalSupport N X) :
    Complex.normSq
          (selbergSqrtZetaSignedRationalCoeff N X
            ((a : ℚ) / (b : ℚ))) /
        PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
          (selbergSqrtZetaSignedRationalSupport N X)
          selbergSqrtZetaSignedRationalFrequency
          ((a : ℚ) / (b : ℚ)) ≤
      ((X * min (a * N) b + 1 : ℕ) : ℝ) *
        Complex.normSq
          (∑ d ∈ selbergSqrtZetaSignedCoprimeRayScaleSupport N X a b,
            (selbergSqrtZetaSignedRationalPairCoeff N X
              (b * d, a * d) : ℂ)) := by
  rw [←
    selbergSqrtZetaSignedRationalCoeff_reduced_eq_coprimeRayScaleSum
      N X a b hab hb]
  exact
    normSq_div_localFrequencySeparation_le_reducedWeight
      ha hb hab hQ hq

end HardyTheorem
