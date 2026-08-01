import HardyTheorem.SelbergSqrtZetaSignedCoprimeRayLogExpansion
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

private theorem inv_sqrt_mul_sq_eq_inv_mul_sq
    {x : ℝ} (hx : 0 ≤ x) (y : ℝ) :
    ((Real.sqrt x)⁻¹ * y) ^ 2 = x⁻¹ * y ^ 2 := by
  rw [mul_pow, inv_pow, Real.sq_sqrt hx]

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

/-- Harmonic normalization of the reduced-ray energy.  This is the form used
when summing over coprime numerator-denominator pairs: the square-root factor
becomes exactly `1 / (a*b)`, while the full signed bilinear scale sum remains
inside one square. -/
theorem normSq_div_localFrequencySeparation_le_reducedRayBilinearWeight
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
        (((a * b : ℕ) : ℝ)⁻¹ *
          (selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b
            (selbergSqrtZetaTaperedCoeff X)
            (selbergSqrtZetaTaperedCoeff X)) ^ 2) := by
  have h :=
    normSq_div_localFrequencySeparation_le_reducedRayWeight
      ha hb hab hQ hq
  rw [← Complex.ofReal_sum,
    selbergSqrtZetaSignedCoprimeRayScaleSum_eq_invSqrt_mul_bilinearScaleSum,
    Complex.normSq_ofReal,
    ← pow_two,
    inv_sqrt_mul_sq_eq_inv_mul_sq (by positivity)] at h
  simpa only [Nat.cast_mul] using h

/-- The same reduced-ray estimate with the exact four-term logarithmic
expansion exposed.  The arithmetic cancellation remains inside one square. -/
theorem normSq_div_localFrequencySeparation_le_reducedRayLogExpansionWeight
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
        ((Real.sqrt (a * b))⁻¹ *
          (selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b
              selbergSqrtZetaCoeff selbergSqrtZetaCoeff -
            (Real.log X)⁻¹ *
              (selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b
                  selbergSqrtZetaLogCoeff selbergSqrtZetaCoeff +
                selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b
                  selbergSqrtZetaCoeff selbergSqrtZetaLogCoeff) +
            (Real.log X)⁻¹ ^ 2 *
              selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b
                selbergSqrtZetaLogCoeff selbergSqrtZetaLogCoeff)) ^ 2 := by
  have h :=
    normSq_div_localFrequencySeparation_le_reducedRayWeight
      ha hb hab hQ hq
  rw [← Complex.ofReal_sum,
    selbergSqrtZetaSignedCoprimeRayScaleSum_eq_invSqrt_mul_logExpansion,
    Complex.normSq_ofReal] at h
  simpa only [pow_two] using h

end HardyTheorem
