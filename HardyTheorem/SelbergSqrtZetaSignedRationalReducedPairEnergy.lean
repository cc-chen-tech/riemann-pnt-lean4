import HardyTheorem.SelbergSqrtZetaSignedRationalReducedPairSupport
import HardyTheorem.SelbergSqrtZetaSignedReducedRayCompleteBoundary

/-!
# Global reduced-pair energy for the signed Selberg model

The rational support is canonically equivalent to a finite support of positive
coprime numerator-denominator pairs.  Reindexing the complete
local-separation weighted energy through that equivalence turns every term
into its sharp reduced-ray weight.

No ray cardinality estimate is used: each full signed scale sum remains inside
one square.
-/

open scoped BigOperators

namespace HardyTheorem

/-- The complete local-separation weighted energy is bounded by the canonical
sum of harmonic-normalized signed bilinear ray energies. -/
theorem
    sum_normSq_div_localFrequencySeparation_le_reducedPairBilinearEnergy
    {N X : ℕ}
    (hQ : (selbergSqrtZetaSignedRationalSupport N X).Nontrivial) :
    (∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) /
          PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
            (selbergSqrtZetaSignedRationalSupport N X)
            selbergSqrtZetaSignedRationalFrequency q) ≤
      ∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
        ((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
          ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
            (selbergSqrtZetaSignedCoprimeRayBilinearScaleSum
              N X p.1 p.2
              (selbergSqrtZetaTaperedCoeff X)
              (selbergSqrtZetaTaperedCoeff X)) ^ 2) := by
  rw [
    sum_selbergSqrtZetaSignedRationalSupport_eq_reducedPairSupport
      N X (fun q =>
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) /
          PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
            (selbergSqrtZetaSignedRationalSupport N X)
            selbergSqrtZetaSignedRationalFrequency q)]
  apply Finset.sum_le_sum
  intro p hp
  have hpFacts :=
    selbergSqrtZetaSignedRationalReducedPairSupport_mem_iff.mp hp
  simpa only [selbergSqrtZetaSignedReducedPairKey] using
    normSq_div_localFrequencySeparation_le_reducedRayBilinearWeight
      hpFacts.1 hpFacts.2.1 hpFacts.2.2.1 hQ hpFacts.2.2.2

/-- Global reduced-pair energy with every ray split exactly into its complete
two-taper main term and boundary truncation defect. -/
theorem
    sum_normSq_div_localFrequencySeparation_le_reducedPairCompleteBoundaryEnergy
    {N X : ℕ}
    (hQ : (selbergSqrtZetaSignedRationalSupport N X).Nontrivial) :
    (∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) /
          PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
            (selbergSqrtZetaSignedRationalSupport N X)
            selbergSqrtZetaSignedRationalFrequency q) ≤
      ∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
        ((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
          ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
            (selbergSqrtZetaSignedReducedRayCompleteTerm N X p.1 p.2 +
              selbergSqrtZetaSignedReducedRayBoundaryTerm
                N X p.1 p.2) ^ 2) := by
  rw [
    sum_selbergSqrtZetaSignedRationalSupport_eq_reducedPairSupport
      N X (fun q =>
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) /
          PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
            (selbergSqrtZetaSignedRationalSupport N X)
            selbergSqrtZetaSignedRationalFrequency q)]
  apply Finset.sum_le_sum
  intro p hp
  have hpFacts :=
    selbergSqrtZetaSignedRationalReducedPairSupport_mem_iff.mp hp
  simpa only [selbergSqrtZetaSignedReducedPairKey] using
    normSq_div_localFrequencySeparation_le_reducedRayCompleteBoundaryWeight
      hpFacts.1 hpFacts.2.1 hpFacts.2.2.1 hQ hpFacts.2.2.2

/-- Separating the complete and boundary pieces costs only the fixed factor
`2`; cancellation inside each piece is still retained. -/
theorem
    sum_normSq_div_localFrequencySeparation_le_reducedPairComplete_add_boundary
    {N X : ℕ}
    (hQ : (selbergSqrtZetaSignedRationalSupport N X).Nontrivial) :
    (∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) /
          PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
            (selbergSqrtZetaSignedRationalSupport N X)
            selbergSqrtZetaSignedRationalFrequency q) ≤
      ∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
        (2 * (((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
          ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
            (selbergSqrtZetaSignedReducedRayCompleteTerm
              N X p.1 p.2) ^ 2)) +
        2 * (((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
          ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
            (selbergSqrtZetaSignedReducedRayBoundaryTerm
              N X p.1 p.2) ^ 2))) := by
  calc
    (∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) /
          PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
            (selbergSqrtZetaSignedRationalSupport N X)
            selbergSqrtZetaSignedRationalFrequency q) ≤
        ∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
          ((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
            ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
              (selbergSqrtZetaSignedReducedRayCompleteTerm N X p.1 p.2 +
                selbergSqrtZetaSignedReducedRayBoundaryTerm
                  N X p.1 p.2) ^ 2) :=
      sum_normSq_div_localFrequencySeparation_le_reducedPairCompleteBoundaryEnergy
        hQ
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p hp
      let w : ℝ :=
        ((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
          (((p.1 * p.2 : ℕ) : ℝ)⁻¹)
      have hw : 0 ≤ w := by
        dsimp only [w]
        positivity
      have hsquare :
          (selbergSqrtZetaSignedReducedRayCompleteTerm N X p.1 p.2 +
              selbergSqrtZetaSignedReducedRayBoundaryTerm N X p.1 p.2) ^ 2 ≤
            2 * (selbergSqrtZetaSignedReducedRayCompleteTerm
              N X p.1 p.2) ^ 2 +
            2 * (selbergSqrtZetaSignedReducedRayBoundaryTerm
              N X p.1 p.2) ^ 2 := by
        nlinarith [sq_nonneg
          (selbergSqrtZetaSignedReducedRayCompleteTerm N X p.1 p.2 -
            selbergSqrtZetaSignedReducedRayBoundaryTerm N X p.1 p.2)]
      calc
        ((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
              ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
                (selbergSqrtZetaSignedReducedRayCompleteTerm N X p.1 p.2 +
                  selbergSqrtZetaSignedReducedRayBoundaryTerm
                    N X p.1 p.2) ^ 2) =
            w * (selbergSqrtZetaSignedReducedRayCompleteTerm N X p.1 p.2 +
              selbergSqrtZetaSignedReducedRayBoundaryTerm
                N X p.1 p.2) ^ 2 := by
              dsimp only [w]
              ring
        _ ≤ w * (2 * (selbergSqrtZetaSignedReducedRayCompleteTerm
                N X p.1 p.2) ^ 2 +
              2 * (selbergSqrtZetaSignedReducedRayBoundaryTerm
                N X p.1 p.2) ^ 2) :=
          mul_le_mul_of_nonneg_left hsquare hw
        _ = 2 * (((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
              ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
                (selbergSqrtZetaSignedReducedRayCompleteTerm
                  N X p.1 p.2) ^ 2)) +
            2 * (((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
              ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
                (selbergSqrtZetaSignedReducedRayBoundaryTerm
                  N X p.1 p.2) ^ 2)) := by
              dsimp only [w]
              ring

end HardyTheorem
