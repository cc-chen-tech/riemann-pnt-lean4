import ZeroFreeRegion.VinogradovKorobov.VinogradovMixedRecurrence

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- A complete degree-one residue solution with one variable on each side is
exactly a diagonal pair. -/
theorem isVinogradovResidueSolution_one_one_iff
    (Q : ℕ) [NeZero Q] (x y : Fin 1 → ZMod Q) :
    IsVinogradovResidueSolution Q 1 1 x y ↔ x = y := by
  constructor
  · intro h
    funext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    have hzero := h (0 : Fin 1)
    simpa [vinogradovResiduePowerSum] using hzero
  · rintro rfl
    intro j
    rfl

/-- At the complete residue scale there are exactly `Q` degree-one,
one-variable solution pairs. -/
theorem vinogradovSolutionCountMod_complete_one
    (Q : ℕ) [NeZero Q] :
    vinogradovSolutionCountMod Q 1 1 Q = Q := by
  classical
  have hset :
      vinogradovResidueSolutionPairSet Q 1 1 =
        Finset.univ.image
          (fun x : Fin 1 → ZMod Q ↦ (x, x)) := by
    ext xy
    simp only [vinogradovResidueSolutionPairSet, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_image]
    rw [isVinogradovResidueSolution_one_one_iff]
    constructor
    · intro hxy
      exact ⟨xy.1, Prod.ext rfl hxy⟩
    · rintro ⟨x, rfl⟩
      rfl
  rw [← card_vinogradovResidueSolutionPairSet Q 1 1, hset]
  rw [Finset.card_image_of_injective]
  · simp
  · intro x y hxy
    exact congrArg Prod.fst hxy

/-- Exact normalized degree-one moment at the complete residue scale. -/
theorem normalizedVinogradovMomentMod_complete_one
    (Q : ℕ) [NeZero Q] :
    normalizedVinogradovMomentMod Q 1 1 Q = (Q : ℂ) := by
  rw [normalizedVinogradovMomentMod_eq_solutionCount,
    vinogradovSolutionCountMod_complete_one]

/-- Real-norm form of the complete degree-one base moment. -/
theorem norm_normalizedVinogradovMomentMod_complete_one
    (Q : ℕ) [NeZero Q] :
    ‖normalizedVinogradovMomentMod Q 1 1 Q‖ = (Q : ℝ) := by
  rw [normalizedVinogradovMomentMod_complete_one]
  simp

end

end ZeroFreeRegion.VinogradovKorobov
