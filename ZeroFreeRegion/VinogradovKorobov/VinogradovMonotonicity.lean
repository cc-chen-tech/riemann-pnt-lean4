import ZeroFreeRegion.VinogradovKorobov.VinogradovQuadratic

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Reindexing a degree by `Fin.castLE` does not change the corresponding
natural-number power sum. -/
theorem vinogradovPowerSumNat_castLE {k l s X : ℕ} (hkl : k ≤ l)
    (x : Fin s → Fin X) (j : Fin k) :
    vinogradovPowerSumNat x (Fin.castLE hkl j) =
      vinogradovPowerSumNat x j := by
  rfl

/-- A solution of a higher-degree Vinogradov system is a solution of every
lower-degree subsystem. -/
theorem IsVinogradovSolutionNat.mono_degree {k l s X : ℕ} (hkl : k ≤ l)
    {x y : Fin s → Fin X}
    (h : IsVinogradovSolutionNat l s X x y) :
    IsVinogradovSolutionNat k s X x y := by
  intro j
  simpa only [vinogradovPowerSumNat_castLE] using h (Fin.castLE hkl j)

/-- Adding higher power-sum equations can only decrease the solution count. -/
theorem vinogradovSolutionCountNat_antitone_degree {k l s X : ℕ}
    (hkl : k ≤ l) :
    vinogradovSolutionCountNat l s X ≤
      vinogradovSolutionCountNat k s X := by
  classical
  unfold vinogradovSolutionCountNat
  apply Finset.sum_le_sum
  intro x hx
  apply Finset.card_le_card
  intro y hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  exact hy.mono_degree hkl

/-- The quadratic two-variable bound holds for every system of degree at
least two. -/
theorem vinogradovSolutionCountNat_two_le_of_two_le_degree
    {k X : ℕ} (hk : 2 ≤ k) :
    vinogradovSolutionCountNat k 2 X ≤ 2 * X ^ 2 :=
  (vinogradovSolutionCountNat_antitone_degree hk).trans
    (vinogradovSolutionCountNat_two_two_le X)

/-- Any verified integer solution-count estimate transfers to the normalized
finite Weyl moment once the modulus prevents wraparound. -/
theorem norm_normalizedVinogradovMomentMod_le_of_count
    (Q k s X B : ℕ) [NeZero Q] (hX : 1 ≤ X)
    (hQ : s * X ^ k < Q)
    (hcount : vinogradovSolutionCountNat k s X ≤ B) :
    ‖normalizedVinogradovMomentMod Q k s X‖ ≤ (B : ℝ) := by
  rw [normalizedVinogradovMomentMod_eq_natCount_of_topScale Q k s X hX hQ]
  exact_mod_cast hcount

/-- Hence every degree `k ≥ 2` has the same quadratic fourth-moment bound. -/
theorem norm_normalizedVinogradovMomentMod_two_le_of_two_le_degree
    (Q k X : ℕ) [NeZero Q] (hk : 2 ≤ k) (hX : 1 ≤ X)
    (hQ : 2 * X ^ k < Q) :
    ‖normalizedVinogradovMomentMod Q k 2 X‖ ≤
      2 * (X : ℝ) ^ 2 := by
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using
    norm_normalizedVinogradovMomentMod_le_of_count
      Q k 2 X (2 * X ^ 2) hX hQ
        (vinogradovSolutionCountNat_two_le_of_two_le_degree hk)

end

end ZeroFreeRegion.VinogradovKorobov
