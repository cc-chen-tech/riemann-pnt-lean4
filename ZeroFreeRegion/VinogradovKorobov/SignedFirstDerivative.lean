import ZeroFreeRegion.VinogradovKorobov.FirstDerivative

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

/-- Negating a real phase conjugates its unit complex phase term. -/
lemma phaseTerm_neg (f : ℕ → ℝ) (n : ℕ) :
    phaseTerm (fun k ↦ -f k) n = star (phaseTerm f n) := by
  unfold phaseTerm
  change Complex.exp (Complex.I * ((-f n : ℝ) : ℂ)) =
    (starRingEnd ℂ) (Complex.exp (Complex.I * ((f n : ℝ) : ℂ)))
  rw [← Complex.exp_conj]
  congr 1
  simp

/-- A finite exponential sum and the sum for its negated phase have the same
norm. -/
lemma norm_phaseSum_neg_eq (f : ℕ → ℝ) (N : ℕ) :
    ‖∑ k ∈ Finset.range N, phaseTerm (fun n ↦ -f n) k‖ =
      ‖∑ k ∈ Finset.range N, phaseTerm f k‖ := by
  calc
    ‖∑ k ∈ Finset.range N, phaseTerm (fun n ↦ -f n) k‖ =
        ‖star (∑ k ∈ Finset.range N, phaseTerm f k)‖ := by
      congr 1
      rw [star_sum]
      apply Finset.sum_congr rfl
      intro k hk
      exact phaseTerm_neg f k
    _ = ‖∑ k ∈ Finset.range N, phaseTerm f k‖ := norm_star _

/-- Kusmin--Landau for a decreasing phase.  The positive decrements stay in
one nonresonant turn and decrease with the index. -/
theorem kusminLandau_negative_antitone_two_pi_div (f : ℕ → ℝ) (N : ℕ)
    {delta : ℝ} (hdelta : 0 < delta)
    (hlower : ∀ k ≤ N, delta ≤ f k - f (k + 1))
    (hupper : ∀ k ≤ N, f k - f (k + 1) ≤ 2 * Real.pi - delta)
    (hanti : ∀ k < N,
      f (k + 1) - f (k + 2) ≤ f k - f (k + 1)) :
    ‖∑ k ∈ Finset.range (N + 1), phaseTerm f k‖ ≤
      2 * Real.pi / delta := by
  let g : ℕ → ℝ := fun k ↦ -f k
  have hg := kusminLandau_antitone_two_pi_div g N hdelta
    (fun k hk ↦ by dsimp [g]; linarith [hlower k hk])
    (fun k hk ↦ by dsimp [g]; linarith [hupper k hk])
    (fun k hk ↦ by dsimp [g]; linarith [hanti k hk])
  rw [norm_phaseSum_neg_eq f (N + 1)] at hg
  exact hg

end ZeroFreeRegion.VinogradovKorobov
