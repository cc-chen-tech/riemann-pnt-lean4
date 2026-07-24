import ZeroFreeRegion.VinogradovKorobov.VinogradovMixedRecurrence
import ZeroFreeRegion.VinogradovKorobov.VinogradovMixedTailMoment

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- The optimized pointwise mixed-moment saving survives averaging over the
actual unit-separated center-pair stratum used by the recurrence. -/
theorem
    normalizedVinogradovUnitSeparatedMixedMomentAverage_le_optimizedBalancedTail_sqrt
    (p a k r : ℕ) [Fact p.Prime]
    (hr : 0 < r) (h2rk : 2 * r ≤ k) (hkp : k < p) :
    normalizedVinogradovUnitSeparatedMixedMomentAverage
        p a 2 k r (vinogradovBalancedTailLength k r) p p ≤
      Real.sqrt
        (2 * ((2 * r).factorial : ℝ) *
          ((vinogradovBalancedTailLength k r).factorial : ℝ) *
            (p : ℝ) ^
              (2 * r + 3 * vinogradovBalancedTailLength k r)) := by
  have hpow :
      p ^ (2 - 1) < p ^ 2 :=
    Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by omega)
  have hcardNat :
      0 < (vinogradovUnitSeparatedCenterPairSet p a 2).card := by
    rw [card_vinogradovUnitSeparatedCenterPairSet p a 2 (by omega)]
    exact Nat.mul_pos (pow_pos (Fact.out : p.Prime).pos a)
      (Nat.sub_pos_of_lt hpow)
  have hcardReal :
      (0 : ℝ) <
        (vinogradovUnitSeparatedCenterPairSet p a 2).card := by
    exact_mod_cast hcardNat
  unfold normalizedVinogradovUnitSeparatedMixedMomentAverage
  apply (div_le_iff₀ hcardReal).2
  unfold normalizedVinogradovUnitSeparatedMixedMomentSum
  calc
    (∑ z ∈ vinogradovUnitSeparatedCenterPairSet p a 2,
      ‖normalizedVinogradovMixedModConditionedMoment
        p ((k - r + 1) * 2) a 2 k r
          (vinogradovBalancedTailLength k r) p p
          (vinogradovCenterValue z.1)
          (vinogradovCenterValue z.2)‖) ≤
        ∑ _z ∈ vinogradovUnitSeparatedCenterPairSet p a 2,
          Real.sqrt
            (2 * ((2 * r).factorial : ℝ) *
              ((vinogradovBalancedTailLength k r).factorial : ℝ) *
                (p : ℝ) ^
                  (2 * r +
                    3 * vinogradovBalancedTailLength k r)) := by
      apply Finset.sum_le_sum
      intro z _hz
      exact Real.le_sqrt_of_sq_le
        (norm_normalizedVinogradovMixedModConditionedMoment_sq_le_primeScale_optimizedBalancedTail_powerSaving
          p a k r hr h2rk hkp
          (vinogradovCenterValue z.1)
          (vinogradovCenterValue z.2))
    _ = (vinogradovUnitSeparatedCenterPairSet p a 2).card *
          Real.sqrt
            (2 * ((2 * r).factorial : ℝ) *
              ((vinogradovBalancedTailLength k r).factorial : ℝ) *
                (p : ℝ) ^
                  (2 * r +
                    3 * vinogradovBalancedTailLength k r)) := by
      simp
    _ = Real.sqrt
          (2 * ((2 * r).factorial : ℝ) *
            ((vinogradovBalancedTailLength k r).factorial : ℝ) *
              (p : ℝ) ^
                (2 * r +
                  3 * vinogradovBalancedTailLength k r)) *
          (vinogradovUnitSeparatedCenterPairSet p a 2).card := by
      ring

end

end ZeroFreeRegion.VinogradovKorobov
