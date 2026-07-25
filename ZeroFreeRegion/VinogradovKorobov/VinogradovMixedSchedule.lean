import ZeroFreeRegion.VinogradovKorobov.VinogradovMixedRecurrence
import ZeroFreeRegion.VinogradovKorobov.VinogradovMixedTailMoment
import ZeroFreeRegion.VinogradovKorobov.VinogradovCompleteBlockMain

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- On a complete main residue block, the same mixed moment simultaneously
obeys the far-scale recurrence and the factorial-tail estimate.  Keeping the
minimum is the interface needed by a multiscale schedule: later steps may use
the lower-degree moment without discarding the independent tail saving. -/
theorem
    norm_normalizedVinogradovMixedModConditionedMoment_le_min_farScale_completeBlockFactorialTail
    (p a b k r t Y Z n q gamma : ℕ) [Fact p.Prime]
    (hrk : r ≤ k) (hkp : k < p) (hb : 0 < b)
    (hgammaa : gamma ≤ a)
    (hbudget : gamma * (k - r) + a * r ≤ (k - r + 1) * b)
    (htail : (k - r + 1) * b ≤ a * (r + 1))
    (hscale :
      p ^ a * Z ≤
        p ^ a * p ^ vinogradovFarScale k r a b gamma)
    (hqk : q ≤ k) (hsplit : n + q = 2 * t)
    (hnowrap :
      VinogradovResidualTailNoWrap
        p ((k - r + 1) * b) b q Y)
    (z : Fin (p ^ a)) (eta omega : ℤ)
    (hcenter :
      vinogradovCenterValue z - eta =
        omega * (p : ℤ) ^ gamma)
    (homega : IsCoprime (p : ℤ) omega) :
    ‖normalizedVinogradovMixedModConditionedMoment
        p ((k - r + 1) * b) a b k r t
          (p ^ a * Z) Y (vinogradovCenterValue z) eta‖ ≤
      min
        (‖normalizedVinogradovMomentMod
          (p ^ vinogradovFarScale k r a b gamma) r r
            (p ^ vinogradovFarScale k r a b gamma)‖ *
          (Y ^ (2 * t) : ℝ))
        (Real.sqrt
          ((Z : ℝ) ^ (4 * r) *
            ((q.factorial : ℝ) * (Y : ℝ) ^ (2 * n + q)))) := by
  letI : NeZero (p ^ a) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  letI : NeZero (p ^ ((k - r + 1) * b)) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  apply le_min
  · exact
      norm_normalizedVinogradovMixedModConditionedMoment_le_farScaleMoment
        p a b k r t (p ^ a * Z) Y gamma
          (vinogradovCenterValue z) eta omega
          hrk hkp hb hgammaa hbudget htail hcenter homega hscale
  · exact Real.le_sqrt_of_sq_le
      (norm_normalizedVinogradovMixedModConditionedMoment_sq_le_completeMainBlock_factorialTail
        p ((k - r + 1) * b) a b k r t Y Z n q
          (Fact.out : p.Prime).ne_zero hqk hsplit hnowrap z eta)

/-- The hybrid pointwise estimate aggregates over a shifted exact
center-difference layer.  The complete-block identity aligns the ordinary
moment decomposition length `p^b * Y` with the residue-block length
`p^a * Z`; the exact layer cardinality is the only aggregation cost. -/
theorem
    normalizedVinogradovShiftedExactScaleMixedMomentSum_le_card_mul_min_farScale_completeBlockFactorialTail
    (p a b k r t Y Z n q gamma : ℕ) [Fact p.Prime]
    (hrk : r ≤ k) (hkp : k < p) (hb : 0 < b)
    (hgb : gamma < b) (hgammaa : gamma ≤ a)
    (hbudget : gamma * (k - r) + a * r ≤ (k - r + 1) * b)
    (htail : (k - r + 1) * b ≤ a * (r + 1))
    (hcomplete : p ^ b * Y = p ^ a * Z)
    (hscale :
      p ^ a * Z ≤
        p ^ a * p ^ vinogradovFarScale k r a b gamma)
    (hqk : q ≤ k) (hsplit : n + q = 2 * t)
    (hnowrap :
      VinogradovResidualTailNoWrap
        p ((k - r + 1) * b) b q Y) :
    normalizedVinogradovShiftedExactScaleMixedMomentSum
        p a b k r t Y gamma ≤
      (vinogradovCenterPairExactScaleSet p a b gamma).card *
        min
          (‖normalizedVinogradovMomentMod
            (p ^ vinogradovFarScale k r a b gamma) r r
              (p ^ vinogradovFarScale k r a b gamma)‖ *
            (Y ^ (2 * t) : ℝ))
          (Real.sqrt
            ((Z : ℝ) ^ (4 * r) *
              ((q.factorial : ℝ) * (Y : ℝ) ^ (2 * n + q)))) := by
  letI : NeZero (p ^ ((k - r + 1) * b)) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  unfold normalizedVinogradovShiftedExactScaleMixedMomentSum
  rw [hcomplete]
  calc
    (∑ z ∈ vinogradovCenterPairExactScaleSet p a b gamma,
      ‖normalizedVinogradovMixedModConditionedMoment
        p ((k - r + 1) * b) a b k r t (p ^ a * Z) Y
          (vinogradovCenterValue z.1)
          (vinogradovCenterValue z.2 - (p : ℤ) ^ b)‖) ≤
        ∑ _z ∈ vinogradovCenterPairExactScaleSet p a b gamma,
          min
            (‖normalizedVinogradovMomentMod
              (p ^ vinogradovFarScale k r a b gamma) r r
                (p ^ vinogradovFarScale k r a b gamma)‖ *
              (Y ^ (2 * t) : ℝ))
            (Real.sqrt
              ((Z : ℝ) ^ (4 * r) *
                ((q.factorial : ℝ) * (Y : ℝ) ^ (2 * n + q)))) := by
      apply Finset.sum_le_sum
      intro z hz
      rcases exists_coprime_shifted_center_factor_of_exactScale
        p a b gamma hgb z hz with ⟨omega, hcenter, homega⟩
      exact
        norm_normalizedVinogradovMixedModConditionedMoment_le_min_farScale_completeBlockFactorialTail
          p a b k r t Y Z n q gamma hrk hkp hb hgammaa
            hbudget htail hscale hqk hsplit hnowrap z.1
            (vinogradovCenterValue z.2 - (p : ℤ) ^ b) omega
            hcenter homega
    _ = (vinogradovCenterPairExactScaleSet p a b gamma).card *
        min
          (‖normalizedVinogradovMomentMod
            (p ^ vinogradovFarScale k r a b gamma) r r
              (p ^ vinogradovFarScale k r a b gamma)‖ *
            (Y ^ (2 * t) : ℝ))
          (Real.sqrt
            ((Z : ℝ) ^ (4 * r) *
              ((q.factorial : ℝ) * (Y : ℝ) ^ (2 * n + q)))) := by
      simp

/-- Global shifted-center recurrence with both available savings retained on
every nonterminal exact scale.  Only the genuinely terminal center layer is
left at the ambient tuple bound. -/
theorem
    normalizedVinogradovShiftedAllCenterMixedMomentSum_le_hybridExactScales_add_terminal
    (p a b k r t Y Z n q : ℕ) [Fact p.Prime]
    (hrk : r ≤ k) (hkp : k < p) (hb : 0 < b)
    (hgammaa : ∀ gamma < b, gamma ≤ a)
    (hbudget : ∀ gamma < b,
      gamma * (k - r) + a * r ≤ (k - r + 1) * b)
    (htail : (k - r + 1) * b ≤ a * (r + 1))
    (hcomplete : p ^ b * Y = p ^ a * Z)
    (hscale : ∀ gamma < b,
      p ^ a * Z ≤
        p ^ a * p ^ vinogradovFarScale k r a b gamma)
    (hqk : q ≤ k) (hsplit : n + q = 2 * t)
    (hnowrap :
      VinogradovResidualTailNoWrap
        p ((k - r + 1) * b) b q Y) :
    normalizedVinogradovShiftedAllCenterMixedMomentSum
        p ((k - r + 1) * b) a b k r t Y ≤
      (∑ gamma ∈ Finset.range b,
        (vinogradovCenterPairExactScaleSet p a b gamma).card *
          min
            (‖normalizedVinogradovMomentMod
              (p ^ vinogradovFarScale k r a b gamma) r r
                (p ^ vinogradovFarScale k r a b gamma)‖ *
              (Y ^ (2 * t) : ℝ))
            (Real.sqrt
              ((Z : ℝ) ^ (4 * r) *
                ((q.factorial : ℝ) * (Y : ℝ) ^ (2 * n + q))))) +
        (p ^ a : ℕ) *
          ((((p ^ b * Y) ^ (2 * r) * Y ^ (2 * t) : ℕ)) : ℝ) := by
  rw [
    normalizedVinogradovShiftedAllCenterMixedMomentSum_eq_exactScales_add_terminal]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro gamma hgamma
    have hgb : gamma < b := Finset.mem_range.mp hgamma
    exact
      normalizedVinogradovShiftedExactScaleMixedMomentSum_le_card_mul_min_farScale_completeBlockFactorialTail
        p a b k r t Y Z n q gamma hrk hkp hb hgb
          (hgammaa gamma hgb) (hbudget gamma hgb) htail
          hcomplete (hscale gamma hgb) hqk hsplit hnowrap
  · exact normalizedVinogradovShiftedTerminalMixedMomentSum_le_trivial
      p a b k r t Y

/-- One complete hybrid recurrence for the ordinary Vinogradov moment.
Double conditioning is followed by the exact center-scale partition; each
nonterminal layer keeps the better of its lower-degree recurrence and its
factorial-tail estimate. -/
theorem norm_normalizedVinogradovMomentMod_le_hybridExactScales_add_terminal
    (p a b k r t Y Z n q : ℕ) [Fact p.Prime]
    (hr : 0 < r) (ht : 0 < t)
    (hrk : r ≤ k) (hkp : k < p) (hb : 0 < b)
    (hgammaa : ∀ gamma < b, gamma ≤ a)
    (hbudget : ∀ gamma < b,
      gamma * (k - r) + a * r ≤ (k - r + 1) * b)
    (htail : (k - r + 1) * b ≤ a * (r + 1))
    (hcomplete : p ^ b * Y = p ^ a * Z)
    (hscale : ∀ gamma < b,
      p ^ a * Z ≤
        p ^ a * p ^ vinogradovFarScale k r a b gamma)
    (hqk : q ≤ k) (hsplit : n + q = 2 * t)
    (hnowrap :
      VinogradovResidualTailNoWrap
        p ((k - r + 1) * b) b q Y) :
    ‖normalizedVinogradovMomentMod
        (p ^ ((k - r + 1) * b)) k (r + t) (p ^ b * Y)‖ ≤
      (((p ^ a : ℕ) : ℝ) ^ (2 * r - 1)) *
        (((p ^ b : ℕ) : ℝ) ^ (2 * t - 1)) *
          ((∑ gamma ∈ Finset.range b,
            (vinogradovCenterPairExactScaleSet p a b gamma).card *
              min
                (‖normalizedVinogradovMomentMod
                  (p ^ vinogradovFarScale k r a b gamma) r r
                    (p ^ vinogradovFarScale k r a b gamma)‖ *
                  (Y ^ (2 * t) : ℝ))
                (Real.sqrt
                  ((Z : ℝ) ^ (4 * r) *
                    ((q.factorial : ℝ) *
                      (Y : ℝ) ^ (2 * n + q))))) +
            (p ^ a : ℕ) *
              ((((p ^ b * Y) ^ (2 * r) *
                Y ^ (2 * t) : ℕ)) : ℝ)) := by
  letI : NeZero (p ^ a) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  letI : NeZero (p ^ b) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  letI : NeZero (p ^ ((k - r + 1) * b)) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  calc
    ‖normalizedVinogradovMomentMod
        (p ^ ((k - r + 1) * b)) k (r + t) (p ^ b * Y)‖ ≤
      (((p ^ a : ℕ) : ℝ) ^ (2 * r - 1)) *
        (((p ^ b : ℕ) : ℝ) ^ (2 * t - 1)) *
          normalizedVinogradovShiftedAllCenterMixedMomentSum
            p ((k - r + 1) * b) a b k r t Y :=
      norm_normalizedVinogradovMomentMod_le_shiftedAllCenterMixedMomentSum
        p ((k - r + 1) * b) a b k r t Y hr ht
    _ ≤ (((p ^ a : ℕ) : ℝ) ^ (2 * r - 1)) *
        (((p ^ b : ℕ) : ℝ) ^ (2 * t - 1)) *
          ((∑ gamma ∈ Finset.range b,
            (vinogradovCenterPairExactScaleSet p a b gamma).card *
              min
                (‖normalizedVinogradovMomentMod
                  (p ^ vinogradovFarScale k r a b gamma) r r
                    (p ^ vinogradovFarScale k r a b gamma)‖ *
                  (Y ^ (2 * t) : ℝ))
                (Real.sqrt
                  ((Z : ℝ) ^ (4 * r) *
                    ((q.factorial : ℝ) *
                      (Y : ℝ) ^ (2 * n + q))))) +
            (p ^ a : ℕ) *
              ((((p ^ b * Y) ^ (2 * r) *
                Y ^ (2 * t) : ℕ)) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (normalizedVinogradovShiftedAllCenterMixedMomentSum_le_hybridExactScales_add_terminal
          p a b k r t Y Z n q hrk hkp hb hgammaa hbudget
            htail hcomplete hscale hqk hsplit hnowrap)
        (by positivity)

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
