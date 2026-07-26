import ZeroFreeRegion.VinogradovKorobov.VinogradovMixedDecomposition

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- At equal center scales, membership in the terminal congruence layer
forces the two one-based centers themselves to be equal. -/
theorem eq_of_mem_vinogradovCenterPairCongruentSet_self
    (p b : ℕ) [Fact p.Prime]
    (z : Fin (p ^ b) × Fin (p ^ b))
    (hz : z ∈ vinogradovCenterPairCongruentSet p b b b) :
    z.1 = z.2 := by
  letI : NeZero (p ^ b) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  apply (vinogradovCompleteResidueEquiv (p ^ b)).injective
  rw [vinogradovCompleteResidueEquiv_apply,
    vinogradovCompleteResidueEquiv_apply]
  have hzmod :=
    (mem_vinogradovCenterPairCongruentSet_iff p b b b z).mp hz
  simpa [vinogradovCenterValue, Nat.cast_add, Nat.cast_one] using hzmod

/-- After shifting the second terminal center by `p^b`, an equal-scale
terminal pair has exact difference `p^b` with coprime factor one. -/
theorem shifted_centerDifference_eq_primePower_of_terminal_self
    (p b : ℕ) [Fact p.Prime]
    (z : Fin (p ^ b) × Fin (p ^ b))
    (hz : z ∈ vinogradovCenterPairCongruentSet p b b b) :
    vinogradovCenterValue z.1 -
        (vinogradovCenterValue z.2 - (p : ℤ) ^ b) =
      (1 : ℤ) * (p : ℤ) ^ b := by
  rw [eq_of_mem_vinogradovCenterPairCongruentSet_self p b z hz]
  ring

/-- At equal center scales the shifted terminal layer is itself a genuine
far-scale branch at `gamma = b`; it need not be discarded with the ambient
tuple bound when the terminal far-scale size condition is available. -/
theorem
    normalizedVinogradovShiftedTerminalMixedMomentSum_le_farScaleMoment_self
    (p b k r t Y : ℕ) [Fact p.Prime]
    (hrk : r ≤ k) (hkp : k < p) (hb : 0 < b)
    (hbudget : b * (k - r) + b * r ≤ (k - r + 1) * b)
    (htail : (k - r + 1) * b ≤ b * (r + 1))
    (hscale : p ^ b * Y ≤
      p ^ b * p ^ vinogradovFarScale k r b b b) :
    normalizedVinogradovShiftedTerminalMixedMomentSum
        p b b k r t Y ≤
      (p ^ b : ℕ) *
        (‖normalizedVinogradovMomentMod
          (p ^ vinogradovFarScale k r b b b) r r
            (p ^ vinogradovFarScale k r b b b)‖ *
          (Y ^ (2 * t) : ℝ)) := by
  letI : NeZero (p ^ ((k - r + 1) * b)) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  unfold normalizedVinogradovShiftedTerminalMixedMomentSum
  calc
    (∑ z ∈ vinogradovCenterPairCongruentSet p b b b,
      ‖normalizedVinogradovMixedModConditionedMoment
        p ((k - r + 1) * b) b b k r t (p ^ b * Y) Y
          (vinogradovCenterValue z.1)
          (vinogradovCenterValue z.2 - (p : ℤ) ^ b)‖) ≤
      ∑ _z ∈ vinogradovCenterPairCongruentSet p b b b,
        (‖normalizedVinogradovMomentMod
          (p ^ vinogradovFarScale k r b b b) r r
            (p ^ vinogradovFarScale k r b b b)‖ *
          (Y ^ (2 * t) : ℝ)) := by
      apply Finset.sum_le_sum
      intro z hz
      exact norm_normalizedVinogradovMixedModConditionedMoment_le_farScaleMoment
        p b b k r t (p ^ b * Y) Y b
          (vinogradovCenterValue z.1)
          (vinogradovCenterValue z.2 - (p : ℤ) ^ b) 1
          hrk hkp hb le_rfl hbudget htail
          (shifted_centerDifference_eq_primePower_of_terminal_self p b z hz)
          isCoprime_one_right hscale
    _ = (p ^ b : ℕ) *
        (‖normalizedVinogradovMomentMod
          (p ^ vinogradovFarScale k r b b b) r r
            (p ^ vinogradovFarScale k r b b b)‖ *
          (Y ^ (2 * t) : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul,
        card_vinogradovCenterPairCongruentSet_self]

/-- Equal main and tail center scales allow every exact layer, including the
shifted terminal layer, to feed a far-scale ordinary moment. -/
theorem
    normalizedVinogradovShiftedAllCenterMixedMomentSum_le_allScales_self
    (p b k r t Y : ℕ) [Fact p.Prime]
    (hrk : r ≤ k) (hkp : k < p) (hb : 0 < b)
    (hbudget : ∀ gamma ≤ b,
      gamma * (k - r) + b * r ≤ (k - r + 1) * b)
    (htail : (k - r + 1) * b ≤ b * (r + 1))
    (hscale : ∀ gamma ≤ b,
      p ^ b * Y ≤ p ^ b * p ^ vinogradovFarScale k r b b gamma) :
    normalizedVinogradovShiftedAllCenterMixedMomentSum
        p ((k - r + 1) * b) b b k r t Y ≤
      (∑ gamma ∈ Finset.range b,
        (vinogradovCenterPairExactScaleSet p b b gamma).card *
          (‖normalizedVinogradovMomentMod
            (p ^ vinogradovFarScale k r b b gamma) r r
              (p ^ vinogradovFarScale k r b b gamma)‖ *
            (Y ^ (2 * t) : ℝ))) +
        (p ^ b : ℕ) *
          (‖normalizedVinogradovMomentMod
            (p ^ vinogradovFarScale k r b b b) r r
              (p ^ vinogradovFarScale k r b b b)‖ *
            (Y ^ (2 * t) : ℝ)) := by
  rw [
    normalizedVinogradovShiftedAllCenterMixedMomentSum_eq_exactScales_add_terminal]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro gamma hgamma
    have hgb : gamma < b := Finset.mem_range.mp hgamma
    exact
      normalizedVinogradovShiftedExactScaleMixedMomentSum_le_farScaleMoment
        p b b k r t Y gamma hrk hkp hb hgb hgb.le
          (hbudget gamma hgb.le) htail (hscale gamma hgb.le)
  · exact
      normalizedVinogradovShiftedTerminalMixedMomentSum_le_farScaleMoment_self
        p b k r t Y hrk hkp hb (hbudget b le_rfl) htail
          (hscale b le_rfl)

/-- Ordinary-moment form of the equal-scale recurrence with no trivially
discarded center layer. -/
theorem norm_normalizedVinogradovMomentMod_le_allScales_self
    (p b k r t Y : ℕ) [Fact p.Prime]
    (hr : 0 < r) (ht : 0 < t)
    (hrk : r ≤ k) (hkp : k < p) (hb : 0 < b)
    (hbudget : ∀ gamma ≤ b,
      gamma * (k - r) + b * r ≤ (k - r + 1) * b)
    (htail : (k - r + 1) * b ≤ b * (r + 1))
    (hscale : ∀ gamma ≤ b,
      p ^ b * Y ≤ p ^ b * p ^ vinogradovFarScale k r b b gamma) :
    ‖normalizedVinogradovMomentMod
        (p ^ ((k - r + 1) * b)) k (r + t) (p ^ b * Y)‖ ≤
      (((p ^ b : ℕ) : ℝ) ^ (2 * r - 1)) *
        (((p ^ b : ℕ) : ℝ) ^ (2 * t - 1)) *
          ((∑ gamma ∈ Finset.range b,
            (vinogradovCenterPairExactScaleSet p b b gamma).card *
              (‖normalizedVinogradovMomentMod
                (p ^ vinogradovFarScale k r b b gamma) r r
                  (p ^ vinogradovFarScale k r b b gamma)‖ *
                (Y ^ (2 * t) : ℝ))) +
            (p ^ b : ℕ) *
              (‖normalizedVinogradovMomentMod
                (p ^ vinogradovFarScale k r b b b) r r
                  (p ^ vinogradovFarScale k r b b b)‖ *
                (Y ^ (2 * t) : ℝ))) := by
  letI : NeZero (p ^ b) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  letI : NeZero (p ^ ((k - r + 1) * b)) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  calc
    ‖normalizedVinogradovMomentMod
        (p ^ ((k - r + 1) * b)) k (r + t) (p ^ b * Y)‖ ≤
      (((p ^ b : ℕ) : ℝ) ^ (2 * r - 1)) *
        (((p ^ b : ℕ) : ℝ) ^ (2 * t - 1)) *
          normalizedVinogradovShiftedAllCenterMixedMomentSum
            p ((k - r + 1) * b) b b k r t Y :=
      norm_normalizedVinogradovMomentMod_le_shiftedAllCenterMixedMomentSum
        p ((k - r + 1) * b) b b k r t Y hr ht
    _ ≤ (((p ^ b : ℕ) : ℝ) ^ (2 * r - 1)) *
        (((p ^ b : ℕ) : ℝ) ^ (2 * t - 1)) *
          ((∑ gamma ∈ Finset.range b,
            (vinogradovCenterPairExactScaleSet p b b gamma).card *
              (‖normalizedVinogradovMomentMod
                (p ^ vinogradovFarScale k r b b gamma) r r
                  (p ^ vinogradovFarScale k r b b gamma)‖ *
                (Y ^ (2 * t) : ℝ))) +
            (p ^ b : ℕ) *
              (‖normalizedVinogradovMomentMod
                (p ^ vinogradovFarScale k r b b b) r r
                  (p ^ vinogradovFarScale k r b b b)‖ *
                (Y ^ (2 * t) : ℝ))) := by
      exact mul_le_mul_of_nonneg_left
        (normalizedVinogradovShiftedAllCenterMixedMomentSum_le_allScales_self
          p b k r t Y hrk hkp hb hbudget htail hscale)
        (by positivity)

end

end ZeroFreeRegion.VinogradovKorobov
