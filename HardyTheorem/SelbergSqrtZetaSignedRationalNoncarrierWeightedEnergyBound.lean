import HardyTheorem.SelbergSqrtZetaSignedRationalNoncarrierEnergy
import HardyTheorem.SelbergSqrtZetaSignedReducedRayCompleteBoundary
import HardyTheorem.SelbergSqrtZetaSignedReducedRayBoundaryTaperEnergy

/-!
# Weighted energy of the signed rational noncarrier

The ratio-one carrier is deleted before the full-support local-separation
energy is reindexed by canonical positive coprime pairs.  The resulting bound
keeps the erased `(1,1)` pair absent and retains all signed scale cancellation
inside each complete reduced-ray square.
-/

open scoped BigOperators

namespace HardyTheorem

/-- The full-support local-separation cost of the canonical noncarrier pairs is
bounded pointwise by the exact complete-plus-boundary reduced-ray energy.  The
carrier pair `(1,1)` is absent on both sides. -/
theorem
    sum_normSq_div_fullLocalSeparation_reducedPairErase_le_completeBoundaryWeightedEnergy
    {N X : ℕ}
    (hQ : (selbergSqrtZetaSignedRationalSupport N X).Nontrivial) :
    (∑ p ∈ (selbergSqrtZetaSignedRationalReducedPairSupport N X).erase (1, 1),
        Complex.normSq
              (selbergSqrtZetaSignedRationalCoeff N X
                (selbergSqrtZetaSignedReducedPairKey p)) /
            PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
              (selbergSqrtZetaSignedRationalSupport N X)
              selbergSqrtZetaSignedRationalFrequency
              (selbergSqrtZetaSignedReducedPairKey p)) ≤
      ∑ p ∈ (selbergSqrtZetaSignedRationalReducedPairSupport N X).erase (1, 1),
        ((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
          ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
            (selbergSqrtZetaSignedReducedRayCompleteTerm N X p.1 p.2 +
              selbergSqrtZetaSignedReducedRayBoundaryTerm N X p.1 p.2) ^ 2) := by
  classical
  apply Finset.sum_le_sum
  intro p hp
  have hpFull :
      p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X :=
    Finset.mem_of_mem_erase hp
  have hpFacts :=
    selbergSqrtZetaSignedRationalReducedPairSupport_mem_iff.mp hpFull
  simpa only [selbergSqrtZetaSignedReducedPairKey] using
    normSq_div_localFrequencySeparation_le_reducedRayCompleteBoundaryWeight
      hpFacts.1 hpFacts.2.1 hpFacts.2.2.1 hQ hpFacts.2.2.2

/-- Splitting the exact complete-plus-boundary square costs the fixed factor
`2`, while every complete and boundary scale sum remains signed and the
carrier pair remains deleted. -/
theorem
    sum_normSq_div_fullLocalSeparation_reducedPairErase_le_complete_add_boundary
    {N X : ℕ}
    (hQ : (selbergSqrtZetaSignedRationalSupport N X).Nontrivial) :
    (∑ p ∈ (selbergSqrtZetaSignedRationalReducedPairSupport N X).erase (1, 1),
        Complex.normSq
              (selbergSqrtZetaSignedRationalCoeff N X
                (selbergSqrtZetaSignedReducedPairKey p)) /
            PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
              (selbergSqrtZetaSignedRationalSupport N X)
              selbergSqrtZetaSignedRationalFrequency
              (selbergSqrtZetaSignedReducedPairKey p)) ≤
      ∑ p ∈ (selbergSqrtZetaSignedRationalReducedPairSupport N X).erase (1, 1),
        (2 * (((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
          ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
            (selbergSqrtZetaSignedReducedRayCompleteTerm
              N X p.1 p.2) ^ 2)) +
        2 * (((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
          ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
            (selbergSqrtZetaSignedReducedRayBoundaryTerm
              N X p.1 p.2) ^ 2))) := by
  calc
    (∑ p ∈ (selbergSqrtZetaSignedRationalReducedPairSupport N X).erase (1, 1),
        Complex.normSq
              (selbergSqrtZetaSignedRationalCoeff N X
                (selbergSqrtZetaSignedReducedPairKey p)) /
            PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
              (selbergSqrtZetaSignedRationalSupport N X)
              selbergSqrtZetaSignedRationalFrequency
              (selbergSqrtZetaSignedReducedPairKey p)) ≤
        ∑ p ∈ (selbergSqrtZetaSignedRationalReducedPairSupport N X).erase (1, 1),
          ((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
            ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
              (selbergSqrtZetaSignedReducedRayCompleteTerm N X p.1 p.2 +
                selbergSqrtZetaSignedReducedRayBoundaryTerm
                  N X p.1 p.2) ^ 2) :=
      sum_normSq_div_fullLocalSeparation_reducedPairErase_le_completeBoundaryWeightedEnergy
        hQ
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p hp
      let w : ℝ :=
        ((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
          (((p.1 * p.2 : ℕ) : ℝ)⁻¹)
      let complete :=
        selbergSqrtZetaSignedReducedRayCompleteTerm N X p.1 p.2
      let boundary :=
        selbergSqrtZetaSignedReducedRayBoundaryTerm N X p.1 p.2
      have hw : 0 ≤ w := by
        dsimp only [w]
        positivity
      have hsquare :
          (complete + boundary) ^ 2 ≤
            2 * complete ^ 2 + 2 * boundary ^ 2 := by
        nlinarith [sq_nonneg (complete - boundary)]
      calc
        ((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
              ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
                (selbergSqrtZetaSignedReducedRayCompleteTerm N X p.1 p.2 +
                  selbergSqrtZetaSignedReducedRayBoundaryTerm
                    N X p.1 p.2) ^ 2) =
            w * (complete + boundary) ^ 2 := by
              dsimp only [w, complete, boundary]
              ring
        _ ≤ w * (2 * complete ^ 2 + 2 * boundary ^ 2) :=
          mul_le_mul_of_nonneg_left hsquare hw
        _ =
            2 * (((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
              ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
                (selbergSqrtZetaSignedReducedRayCompleteTerm
                  N X p.1 p.2) ^ 2)) +
            2 * (((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
              ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
                (selbergSqrtZetaSignedReducedRayBoundaryTerm
                  N X p.1 p.2) ^ 2)) := by
              dsimp only [w, complete, boundary]
              ring

/-- The strongest directly available explicit boundary replacement.  Only the
boundary square is enlarged to its harmonic-tail taper majorant; the deleted
support and signed complete-ray square are unchanged. -/
theorem
    sum_normSq_div_fullLocalSeparation_reducedPairErase_le_complete_add_explicitBoundary
    {N X : ℕ} (hX : 2 ≤ X)
    (hQ : (selbergSqrtZetaSignedRationalSupport N X).Nontrivial) :
    (∑ p ∈ (selbergSqrtZetaSignedRationalReducedPairSupport N X).erase (1, 1),
        Complex.normSq
              (selbergSqrtZetaSignedRationalCoeff N X
                (selbergSqrtZetaSignedReducedPairKey p)) /
            PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
              (selbergSqrtZetaSignedRationalSupport N X)
              selbergSqrtZetaSignedRationalFrequency
              (selbergSqrtZetaSignedReducedPairKey p)) ≤
      ∑ p ∈ (selbergSqrtZetaSignedRationalReducedPairSupport N X).erase (1, 1),
        (2 * (((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
          ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
            (selbergSqrtZetaSignedReducedRayCompleteTerm
              N X p.1 p.2) ^ 2)) +
        2 * (((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
          ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
            ((∑ d ∈ Finset.Ioc
                (min N X / p.2)
                (min (X / p.1) (N * X / p.2)),
                (d : ℝ)⁻¹) ^ 2 *
              (harmonic X : ℝ) *
              (4 * (X : ℝ) ^ 2 / (Real.log X) ^ 2))))) := by
  calc
    (∑ p ∈ (selbergSqrtZetaSignedRationalReducedPairSupport N X).erase (1, 1),
        Complex.normSq
              (selbergSqrtZetaSignedRationalCoeff N X
                (selbergSqrtZetaSignedReducedPairKey p)) /
            PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
              (selbergSqrtZetaSignedRationalSupport N X)
              selbergSqrtZetaSignedRationalFrequency
              (selbergSqrtZetaSignedReducedPairKey p)) ≤
        ∑ p ∈ (selbergSqrtZetaSignedRationalReducedPairSupport N X).erase (1, 1),
          (2 * (((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
            ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
              (selbergSqrtZetaSignedReducedRayCompleteTerm
                N X p.1 p.2) ^ 2)) +
          2 * (((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
            ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
              (selbergSqrtZetaSignedReducedRayBoundaryTerm
                N X p.1 p.2) ^ 2))) :=
      sum_normSq_div_fullLocalSeparation_reducedPairErase_le_complete_add_boundary
        hQ
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p hp
      apply add_le_add_right
      let weight : ℝ :=
        2 * ((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
          (((p.1 * p.2 : ℕ) : ℝ)⁻¹)
      let majorant : ℝ :=
        (∑ d ∈ Finset.Ioc
            (min N X / p.2)
            (min (X / p.1) (N * X / p.2)),
            (d : ℝ)⁻¹) ^ 2 *
          (harmonic X : ℝ) *
          (4 * (X : ℝ) ^ 2 / (Real.log X) ^ 2)
      have hweight : 0 ≤ weight := by
        dsimp only [weight]
        positivity
      have hboundary :
          (selbergSqrtZetaSignedReducedRayBoundaryTerm
            N X p.1 p.2) ^ 2 ≤ majorant := by
        simpa only [majorant] using
          selbergSqrtZetaSignedReducedRayBoundaryTerm_sq_le_four_mul_harmonicTail_sq_mul_harmonic_mul_sq_div_log_sq
            (N := N) (X := X) (a := p.1) (b := p.2) hX
      calc
        2 * (((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
              ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
                (selbergSqrtZetaSignedReducedRayBoundaryTerm
                  N X p.1 p.2) ^ 2)) =
            weight *
              (selbergSqrtZetaSignedReducedRayBoundaryTerm
                N X p.1 p.2) ^ 2 := by
              dsimp only [weight]
              ring
        _ ≤ weight * majorant :=
          mul_le_mul_of_nonneg_left hboundary hweight
        _ = 2 * (((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
              ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
                ((∑ d ∈ Finset.Ioc
                    (min N X / p.2)
                    (min (X / p.1) (N * X / p.2)),
                    (d : ℝ)⁻¹) ^ 2 *
                  (harmonic X : ℝ) *
                  (4 * (X : ℝ) ^ 2 / (Real.log X) ^ 2)))) := by
              dsimp only [weight, majorant]
              ring

end HardyTheorem
