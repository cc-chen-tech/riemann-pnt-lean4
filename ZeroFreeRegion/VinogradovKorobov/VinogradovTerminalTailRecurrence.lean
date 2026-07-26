import ZeroFreeRegion.VinogradovKorobov.VinogradovShiftedTerminalScale
import ZeroFreeRegion.VinogradovKorobov.VinogradovTailResidueReparameterization

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- Cauchy separation followed by one exact residue reconditioning step on the
tail.  This keeps the true scale-`b+1` tail moments instead of replacing the
tail by its ambient tuple count. -/
theorem norm_normalizedVinogradovMixedModConditionedMoment_sq_le_nextScaleTail
    (p B a b k r t X Y : ℕ) [Fact p.Prime] [NeZero (p ^ B)]
    (ht : 0 < t) (xi eta : ℤ) :
    ‖normalizedVinogradovMixedModConditionedMoment
        p B a b k r t X Y xi eta‖ ^ 2 ≤
      normalizedVinogradovMixedMainNormMoment p B a k (2 * r) X xi *
        ((p : ℝ) ^ (2 * (2 * t) - 1) *
          ∑ rho : ZMod p,
            normalizedVinogradovMixedTailNormMoment p B (b + 1) k (2 * t)
              (vinogradovTailResidueLength p Y rho)
              (vinogradovTailResidueRefinedCenter p b eta rho)) := by
  have hcauchy :=
    norm_normalizedVinogradovMixedModConditionedMoment_sq_le_separateMoments
      p B a b k r t X Y xi eta
  have htail :=
    normalizedVinogradovMixedTailNormMoment_le_nextScaleResidueSum
      p B b k (2 * t) Y (by omega) eta
  have hmain :
      0 ≤ normalizedVinogradovMixedMainNormMoment
        p B a k (2 * r) X xi := by
    unfold normalizedVinogradovMixedMainNormMoment
    positivity
  exact hcauchy.trans (mul_le_mul_of_nonneg_left htail hmain)

/-- The whole shifted terminal layer now has a nontrivial recursive bound.
The old terminal estimate used `Y^(2t)` pointwise; this squared estimate keeps
the endpoint-sensitive scale-`b+1` tail moments under the center-pair sum. -/
theorem normalizedVinogradovShiftedTerminalMixedMomentSum_sq_le_nextScaleTail
    (p a b k r t Y : ℕ) [Fact p.Prime] (ht : 0 < t) :
    normalizedVinogradovShiftedTerminalMixedMomentSum
        p a b k r t Y ^ 2 ≤
      ((vinogradovCenterPairCongruentSet p a b b).card : ℝ) *
        ∑ z ∈ vinogradovCenterPairCongruentSet p a b b,
          normalizedVinogradovMixedMainNormMoment
              p ((k - r + 1) * b) a k (2 * r) (p ^ b * Y)
                (vinogradovCenterValue z.1) *
            ((p : ℝ) ^ (2 * (2 * t) - 1) *
              ∑ rho : ZMod p,
                normalizedVinogradovMixedTailNormMoment
                  p ((k - r + 1) * b) (b + 1) k (2 * t)
                    (vinogradovTailResidueLength p Y rho)
                    (vinogradovTailResidueRefinedCenter p b
                      (vinogradovCenterValue z.2 - (p : ℤ) ^ b) rho)) := by
  letI : NeZero (p ^ ((k - r + 1) * b)) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let S := vinogradovCenterPairCongruentSet p a b b
  let F : (Fin (p ^ a) × Fin (p ^ b)) → ℝ := fun z ↦
    ‖normalizedVinogradovMixedModConditionedMoment
      p ((k - r + 1) * b) a b k r t (p ^ b * Y) Y
        (vinogradovCenterValue z.1)
        (vinogradovCenterValue z.2 - (p : ℤ) ^ b)‖
  let G : (Fin (p ^ a) × Fin (p ^ b)) → ℝ := fun z ↦
    normalizedVinogradovMixedMainNormMoment
        p ((k - r + 1) * b) a k (2 * r) (p ^ b * Y)
          (vinogradovCenterValue z.1) *
      ((p : ℝ) ^ (2 * (2 * t) - 1) *
        ∑ rho : ZMod p,
          normalizedVinogradovMixedTailNormMoment
            p ((k - r + 1) * b) (b + 1) k (2 * t)
              (vinogradovTailResidueLength p Y rho)
              (vinogradovTailResidueRefinedCenter p b
                (vinogradovCenterValue z.2 - (p : ℤ) ^ b) rho))
  have hpoint : ∀ z ∈ S, F z ^ 2 ≤ G z := by
    intro z hz
    exact
      norm_normalizedVinogradovMixedModConditionedMoment_sq_le_nextScaleTail
        p ((k - r + 1) * b) a b k r t (p ^ b * Y) Y ht
          (vinogradovCenterValue z.1)
          (vinogradovCenterValue z.2 - (p : ℤ) ^ b)
  have hsum : (∑ z ∈ S, F z ^ 2) ≤ ∑ z ∈ S, G z := by
    exact Finset.sum_le_sum fun z hz ↦ hpoint z hz
  have hcs :=
    Finset.sum_mul_sq_le_sq_mul_sq S (fun _ ↦ (1 : ℝ)) F
  unfold normalizedVinogradovShiftedTerminalMixedMomentSum
  change (∑ z ∈ S, F z) ^ 2 ≤ (S.card : ℝ) * ∑ z ∈ S, G z
  calc
    (∑ z ∈ S, F z) ^ 2 ≤
        (S.card : ℝ) * ∑ z ∈ S, F z ^ 2 := by
      simpa [Finset.sum_const, nsmul_eq_mul] using hcs
    _ ≤ (S.card : ℝ) * ∑ z ∈ S, G z :=
      mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg S.card)

end

end ZeroFreeRegion.VinogradovKorobov
