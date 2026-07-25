import ZeroFreeRegion.VinogradovKorobov.VinogradovWeightedBounds
import ZeroFreeRegion.VinogradovKorobov.VinogradovWeightedMoment
import ZeroFreeRegion.VinogradovKorobov.VinogradovPrimePowerMultiBlock

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- Every degree-weighted solution at scale `a` satisfies the ordinary
degree-`k` system modulo the weakest common modulus `p^a`. -/
theorem IsVinogradovWeightedSolutionMod.toCommonMod
    (p a k s X : ℕ) {x y : Fin s → Fin X}
    (h : IsVinogradovWeightedSolutionMod p a k s X x y) :
    IsVinogradovSolutionMod (p ^ a) k s X x y := by
  rw [isVinogradovWeightedSolutionMod_iff_powerSumNat_modEq] at h
  intro j
  rw [← natCast_vinogradovPowerSumNat,
    ← natCast_vinogradovPowerSumNat,
    ZMod.natCast_eq_natCast_iff]
  exact (h j).of_dvd (pow_dvd_pow p (by
    have hj : 1 ≤ j.val + 1 := Nat.succ_le_succ (Nat.zero_le _)
    exact Nat.le_mul_of_pos_left a (by omega)))

/-- The weighted solution set is a subset of the solution set for the weakest
common modulus. -/
theorem vinogradovWeightedSolutionCountMod_le_common
    (p a k s X : ℕ) :
    vinogradovWeightedSolutionCountMod p a k s X ≤
      vinogradovSolutionCountMod (p ^ a) k s X := by
  classical
  unfold vinogradovWeightedSolutionCountMod vinogradovSolutionCountMod
  apply Finset.sum_le_sum
  intro x hx
  apply Finset.card_le_card
  intro y hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  exact hy.toCommonMod p a k s X

/-- The existing ordinary-modulus multiblock estimate gives an unconditional
fallback bound for the weighted prime-power count.  It does not yet exploit
the stronger moduli of the higher-degree equations. -/
theorem vinogradovWeightedPrimePowerMultiBlockSolutionCount_le_strata
    (p k r b n : ℕ) [Fact p.Prime] (hk : 0 < k) (hkp : k < p) :
    vinogradovWeightedSolutionCountMod p (n + 1) k (b * k + r)
        (p ^ (n + 1)) ≤
      ((p ^ k - p.descFactorial k) ^ b * p ^ r *
          p ^ (b * k + r)) *
        (p ^ (2 * (b * k + r))) ^ n +
      ((p ^ k) ^ b - (p ^ k - p.descFactorial k) ^ b) *
        (p ^ r * p ^ (b * k + r) *
          (p ^ (k + 2 * ((b - 1) * k + r))) ^ n) := by
  exact (vinogradovWeightedSolutionCountMod_le_common
      p (n + 1) k (b * k + r) (p ^ (n + 1))).trans
    (vinogradovPrimePowerMultiBlockSolutionCount_le_strata
      p k r b n hk hkp)

/-- The common-modulus fallback also bounds the normalized weighted Weyl
moment. -/
theorem norm_normalizedVinogradovWeightedMomentMod_primePowerMultiBlock_le_strata
    (p k r b n : ℕ) [Fact p.Prime] (hk : 0 < k) (hkp : k < p) :
    ‖normalizedVinogradovWeightedMomentMod
        p (n + 1) k (b * k + r) (p ^ (n + 1))‖ ≤
      ((((p ^ k - p.descFactorial k) ^ b * p ^ r *
            p ^ (b * k + r)) *
          (p ^ (2 * (b * k + r))) ^ n +
        ((p ^ k) ^ b - (p ^ k - p.descFactorial k) ^ b) *
          (p ^ r * p ^ (b * k + r) *
            (p ^ (k + 2 * ((b - 1) * k + r))) ^ n) : ℕ) : ℝ) := by
  rw [normalizedVinogradovWeightedMomentMod_eq_solutionCount]
  norm_cast
  exact vinogradovWeightedPrimePowerMultiBlockSolutionCount_le_strata
    p k r b n hk hkp

end

end ZeroFreeRegion.VinogradovKorobov
