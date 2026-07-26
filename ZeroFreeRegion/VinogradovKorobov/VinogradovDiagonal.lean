import ZeroFreeRegion.VinogradovKorobov.VinogradovNewton
import Mathlib.Data.List.Permutation

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- For a fixed left tuple, a Vinogradov system containing the first `s`
power-sum equations has at most `s!` right tuples: they are all reorderings of
the left tuple. -/
theorem fixed_left_solution_count_le_factorial (k s X : ℕ) (hsk : s ≤ k)
    (x : Fin s → Fin X) :
    (Finset.univ.filter fun y : Fin s → Fin X ↦
      IsVinogradovSolutionNat k s X x y).card ≤ s.factorial := by
  let solutions := Finset.univ.filter fun y : Fin s → Fin X ↦
    IsVinogradovSolutionNat k s X x y
  let toList : (Fin s → Fin X) ↪ List (Fin X) :=
    ⟨List.ofFn, fun _ _ hxy => List.ofFn_inj.mp hxy⟩
  calc
    solutions.card = (solutions.map toList).card := by
      rw [Finset.card_map]
    _ ≤ (List.ofFn x).permutations.toFinset.card := by
      apply Finset.card_le_card
      intro ys hys
      simp only [Finset.mem_map] at hys
      obtain ⟨y, hy, rfl⟩ := hys
      simp only [List.mem_toFinset, List.mem_permutations]
      apply Multiset.coe_eq_coe.mp
      have hsol : IsVinogradovSolutionNat k s X x y := by
        exact (Finset.mem_filter.mp hy).2
      simpa using (hsol.multiset_eq hsk).symm
    _ ≤ (List.ofFn x).permutations.length :=
      List.toFinset_card_le (List.ofFn x).permutations
    _ = s.factorial := by
      rw [List.length_permutations, List.length_ofFn]

/-- In the diagonal range `s ≤ k`, the integer Vinogradov mean value has the
uniform bound `J_{s,k}(X) ≤ s! X^s`. -/
theorem vinogradovSolutionCountNat_le_diagonal (k s X : ℕ) (hsk : s ≤ k) :
    vinogradovSolutionCountNat k s X ≤ s.factorial * X ^ s := by
  classical
  unfold vinogradovSolutionCountNat
  calc
    (∑ x : Fin s → Fin X,
      (Finset.univ.filter fun y : Fin s → Fin X ↦
        IsVinogradovSolutionNat k s X x y).card) ≤
        ∑ _x : Fin s → Fin X, s.factorial := by
      apply Finset.sum_le_sum
      intro x _
      exact fixed_left_solution_count_le_factorial k s X hsk x
    _ = X ^ s * s.factorial := by
      simp [Fintype.card_fin]
    _ = s.factorial * X ^ s := Nat.mul_comm _ _

/-- The diagonal solution bound transfers to the normalized finite Weyl
moment whenever the modulus is large enough to prevent wraparound. -/
theorem norm_normalizedVinogradovMomentMod_le_diagonal
    (Q k s X : ℕ) [NeZero Q] (hsk : s ≤ k) (hX : 1 ≤ X)
    (hQ : s * X ^ k < Q) :
    ‖normalizedVinogradovMomentMod Q k s X‖ ≤
      (s.factorial : ℝ) * (X : ℝ) ^ s := by
  simpa only [Nat.cast_mul, Nat.cast_factorial, Nat.cast_pow] using
    norm_normalizedVinogradovMomentMod_le_of_count
      Q k s X (s.factorial * X ^ s) hX hQ
        (vinogradovSolutionCountNat_le_diagonal k s X hsk)

end

end ZeroFreeRegion.VinogradovKorobov
