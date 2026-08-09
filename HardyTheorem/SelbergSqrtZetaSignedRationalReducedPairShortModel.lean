import HardyTheorem.SelbergSqrtZetaSignedRationalReducedPairEnergy
import HardyTheorem.SelbergSqrtZetaSignedRationalShortKernelLocalSeparation

/-!
# Reduced-pair arithmetic bound for the actual short model

This file substitutes the canonical coprime-pair energy into the analytic
local-separation estimate for the actual rational short model.  The output no
longer contains an abstract nearest-neighbour denominator.
-/

open Complex MeasureTheory
open scoped BigOperators

namespace HardyTheorem

/-- The actual rational short-model square energy is controlled by the
diagonal coefficient energy and the two explicit canonical reduced-pair sums
(complete main term and boundary defect). -/
theorem
    integral_normSq_selbergSqrtZetaSignedRationalShortModel_le_reducedPairComplete_add_boundary
    (kappa T : ℝ) (X : ℕ) {H : ℝ}
    (hT : 0 < T) (hH : 0 ≤ H) (hroom : H ≤ T)
    (hQ :
      (selbergSqrtZetaSignedRationalSupport
        (firstZetaApproximationCutoff T) X).Nontrivial) :
    (∫ t in T..2 * T - H,
        Complex.normSq
          (selbergSqrtZetaSignedRationalShortModel T X H t)) ≤
      H ^ 2 *
        ((T - H) *
            ∑ q ∈ selbergSqrtZetaSignedRationalSupport
                (firstZetaApproximationCutoff T) X,
              Complex.normSq
                (selbergSqrtZetaSignedRationalCoeff
                  (firstZetaApproximationCutoff T) X q) +
          4 * Real.pi *
            ∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport
                (firstZetaApproximationCutoff T) X,
              (2 *
                  (((X *
                      min (p.1 * firstZetaApproximationCutoff T) p.2 +
                        1 : ℕ) : ℝ) *
                    ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
                      (selbergSqrtZetaSignedReducedRayCompleteTerm
                        (firstZetaApproximationCutoff T) X p.1 p.2) ^ 2)) +
                2 *
                  (((X *
                      min (p.1 * firstZetaApproximationCutoff T) p.2 +
                        1 : ℕ) : ℝ) *
                    ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
                      (selbergSqrtZetaSignedReducedRayBoundaryTerm
                        (firstZetaApproximationCutoff T) X p.1 p.2) ^ 2)))) := by
  have hmodel :=
    integral_normSq_selbergSqrtZetaSignedRationalShortModel_le_localSeparation
      kappa T X hT hH hroom hQ
  have hpair :=
    sum_normSq_div_localFrequencySeparation_le_reducedPairComplete_add_boundary
      hQ
  have hfourPi : 0 ≤ 4 * Real.pi := by positivity
  have hinner :
      (T - H) *
            ∑ q ∈ selbergSqrtZetaSignedRationalSupport
                (firstZetaApproximationCutoff T) X,
              Complex.normSq
                (selbergSqrtZetaSignedRationalCoeff
                  (firstZetaApproximationCutoff T) X q) +
          4 * Real.pi *
            ∑ q ∈ selbergSqrtZetaSignedRationalSupport
                (firstZetaApproximationCutoff T) X,
              Complex.normSq
                  (selbergSqrtZetaSignedRationalCoeff
                    (firstZetaApproximationCutoff T) X q) /
                PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
                  (selbergSqrtZetaSignedRationalSupport
                    (firstZetaApproximationCutoff T) X)
                  selbergSqrtZetaSignedRationalFrequency q ≤
        (T - H) *
            ∑ q ∈ selbergSqrtZetaSignedRationalSupport
                (firstZetaApproximationCutoff T) X,
              Complex.normSq
                (selbergSqrtZetaSignedRationalCoeff
                  (firstZetaApproximationCutoff T) X q) +
          4 * Real.pi *
            ∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport
                (firstZetaApproximationCutoff T) X,
              (2 *
                  (((X *
                      min (p.1 * firstZetaApproximationCutoff T) p.2 +
                        1 : ℕ) : ℝ) *
                    ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
                      (selbergSqrtZetaSignedReducedRayCompleteTerm
                        (firstZetaApproximationCutoff T) X p.1 p.2) ^ 2)) +
                2 *
                  (((X *
                      min (p.1 * firstZetaApproximationCutoff T) p.2 +
                        1 : ℕ) : ℝ) *
                    ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
                      (selbergSqrtZetaSignedReducedRayBoundaryTerm
                        (firstZetaApproximationCutoff T) X p.1 p.2) ^ 2))) := by
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hpair hfourPi)
  exact hmodel.trans (mul_le_mul_of_nonneg_left hinner (sq_nonneg H))

end HardyTheorem
