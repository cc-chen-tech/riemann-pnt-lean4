import ZeroFreeRegion.VinogradovKorobov.VinogradovPrimePowerMultiBlock
import ZeroFreeRegion.VinogradovKorobov.VinogradovPrimePowerTargetFiber

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- Cycling a first-nonsingular block to the head lets the uniform
fixed-target fiber bound replace the older iterated Hensel estimate. -/
theorem card_vinogradovPrimePowerFirstNonsingularSolutionSet_le_target_fibers
    (p k r q a n : ℕ) [Fact p.Prime] (hk : 0 < k) (hkp : k < p) :
    (vinogradovPrimePowerFirstNonsingularSolutionSet
      p k r q a n).card ≤
      (p ^ (n + 1)) ^ (k + 2 * (q * k + a * k + r)) *
        k.factorial := by
  exact (card_vinogradovPrimePowerFirstNonsingularSolutionSet_le_nonsingular
    p k r q a n hk).trans
      (card_vinogradovPrimePowerNonsingularSolutionSet_le_fixed_data
        p k (q * k + a * k + r) n hkp)

/-- Summing over the location of the first nonsingular block gives `b`
copies of the same fixed-target estimate. -/
theorem card_vinogradovPrimePowerSomeBlockNonsingularSolutionSet_le_target_fibers
    (p k r b n : ℕ) [Fact p.Prime] (hk : 0 < k) (hkp : k < p) :
    (vinogradovPrimePowerSomeBlockNonsingularSolutionSet
      p k r b n).card ≤
      b * ((p ^ (n + 1)) ^
        (k + 2 * ((b - 1) * k + r)) * k.factorial) := by
  calc
    (vinogradovPrimePowerSomeBlockNonsingularSolutionSet
        p k r b n).card ≤
        ∑ q : Fin b,
          (vinogradovPrimePowerFirstNonsingularSolutionSet
            p k r q.val (b - 1 - q.val) n).card :=
      card_vinogradovPrimePowerSomeBlockNonsingularSolutionSet_le_sum_first
        p k r b n hk
    _ ≤ ∑ q : Fin b,
        (p ^ (n + 1)) ^
            (k + 2 * (q.val * k + (b - 1 - q.val) * k + r)) *
          k.factorial := by
      apply Finset.sum_le_sum
      intro q _hq
      exact
        card_vinogradovPrimePowerFirstNonsingularSolutionSet_le_target_fibers
          p k r q.val (b - 1 - q.val) n hk hkp
    _ = ∑ _q : Fin b,
        (p ^ (n + 1)) ^ (k + 2 * ((b - 1) * k + r)) *
          k.factorial := by
      apply Finset.sum_congr rfl
      intro q _hq
      have hprefix : q.val + (b - 1 - q.val) = b - 1 := by
        omega
      have htail :
          q.val * k + (b - 1 - q.val) * k + r =
            (b - 1) * k + r := by
        rw [← Nat.add_mul, hprefix]
      rw [htail]
    _ = b * ((p ^ (n + 1)) ^
        (k + 2 * ((b - 1) * k + r)) * k.factorial) := by
      simp

/-- The all-singular branch and the sharper target-fiber nonsingular branch
combine into an improved complete multiblock solution-count estimate. -/
theorem vinogradovPrimePowerMultiBlockSolutionCount_le_target_fibers
    (p k r b n : ℕ) [Fact p.Prime] (hk : 0 < k) (hkp : k < p) :
    vinogradovSolutionCountMod (p ^ (n + 1)) k (b * k + r)
        (p ^ (n + 1)) ≤
      ((p ^ k - p.descFactorial k) ^ b * p ^ r *
          p ^ (b * k + r)) *
        (p ^ (2 * (b * k + r))) ^ n +
      b * ((p ^ (n + 1)) ^
        (k + 2 * ((b - 1) * k + r)) * k.factorial) := by
  rw [← card_primePowerMultiBlockSingular_add_someNonsingular]
  exact Nat.add_le_add
    (card_vinogradovPrimePowerMultiBlockSingularSolutionSet_le p k r b n)
    (card_vinogradovPrimePowerSomeBlockNonsingularSolutionSet_le_target_fibers
      p k r b n hk hkp)

/-- The sharper multiblock count transfers to the normalized complete
Vinogradov moment. -/
theorem norm_normalizedVinogradovMomentMod_primePowerMultiBlock_le_target_fibers
    (p k r b n : ℕ) [Fact p.Prime] (hk : 0 < k) (hkp : k < p) :
    ‖normalizedVinogradovMomentMod
        (p ^ (n + 1)) k (b * k + r) (p ^ (n + 1))‖ ≤
      ((((p ^ k - p.descFactorial k) ^ b * p ^ r *
            p ^ (b * k + r)) *
          (p ^ (2 * (b * k + r))) ^ n +
        b * ((p ^ (n + 1)) ^
          (k + 2 * ((b - 1) * k + r)) * k.factorial) : ℕ) : ℝ) := by
  letI : NeZero (p ^ (n + 1)) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [normalizedVinogradovMomentMod_eq_solutionCount]
  norm_cast
  exact vinogradovPrimePowerMultiBlockSolutionCount_le_target_fibers
    p k r b n hk hkp

end

end ZeroFreeRegion.VinogradovKorobov
