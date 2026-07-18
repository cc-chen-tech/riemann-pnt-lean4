import ZeroFreeRegion.VinogradovKorobov.IteratedDifference

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

example (h : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  phaseDifference h f n

example (shifts : List ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  iteratedPhaseDifference shifts f n

noncomputable example (B : ℕ → ℝ) (N L : ℕ) : ℝ :=
  aProcessSquaredBound B N L

example (f : ℕ → ℝ) (n h : ℕ) :
    phaseTerm f n * (starRingEnd ℂ) (phaseTerm f (n + h)) =
      phaseTerm (phaseDifference h f) n :=
  phaseTerm_mul_conj_shift_eq_phaseTerm_difference f n h

example (f : ℕ → ℝ) (h k n : ℕ) :
    phaseDifference h (phaseDifference k f) n =
      phaseDifference k (phaseDifference h f) n :=
  phaseDifference_commute f h k n

example (f : ℕ → ℝ) (shifts : List ℕ) (ell N : ℕ) :
    (∑ n ∈ Finset.range (N - ell),
        phaseTerm (iteratedPhaseDifference shifts f) n *
          (starRingEnd ℂ)
            (phaseTerm (iteratedPhaseDifference shifts f) (n + ell))) =
      ∑ n ∈ Finset.range (N - ell),
        phaseTerm (iteratedPhaseDifference (ell :: shifts) f) n :=
  iteratedPhase_correlation_eq f shifts ell N

example (f : ℕ → ℝ) (shifts : List ℕ) (B : ℕ → ℝ) (N L : ℕ)
    (hL : 1 ≤ L) (hLN : L ≤ N)
    (hcor : ∀ ell ∈ Finset.Icc 1 (L - 1),
      ‖∑ n ∈ Finset.range (N - ell),
        phaseTerm (iteratedPhaseDifference (ell :: shifts) f) n‖ ≤ B ell) :
    (L : ℝ) ^ 2 *
        ‖∑ n ∈ Finset.range N,
          phaseTerm (iteratedPhaseDifference shifts f) n‖ ^ 2 ≤
      (L : ℝ) * ((N : ℝ) + ((L : ℝ) - 1)) * N +
        2 * ((N : ℝ) + ((L : ℝ) - 1)) *
          ∑ ell ∈ Finset.Icc 1 (L - 1),
            ((L : ℝ) - (ell : ℝ)) * B ell :=
  vanDerCorputIteratedPhaseOfDifferenceBounds
    f shifts B N L hL hLN hcor

example (f : ℕ → ℝ) (shifts : List ℕ) (B : ℕ → ℝ) (N L : ℕ)
    (hL : 1 ≤ L) (hLN : L ≤ N)
    (hcor : ∀ ell ∈ Finset.Icc 1 (L - 1),
      ‖∑ n ∈ Finset.range (N - ell),
        phaseTerm (iteratedPhaseDifference (ell :: shifts) f) n‖ ≤ B ell) :
    ‖∑ n ∈ Finset.range N,
        phaseTerm (iteratedPhaseDifference shifts f) n‖ ^ 2 ≤
      aProcessSquaredBound B N L :=
  norm_iteratedPhase_sum_sq_le_aProcess f shifts B N L hL hLN hcor

example (f : ℕ → ℝ) (shifts : List ℕ) (Q : ℕ → ℝ) (N L : ℕ)
    (hL : 1 ≤ L) (hLN : L ≤ N)
    (hcorSq : ∀ ell ∈ Finset.Icc 1 (L - 1),
      ‖∑ n ∈ Finset.range (N - ell),
        phaseTerm (iteratedPhaseDifference (ell :: shifts) f) n‖ ^ 2 ≤ Q ell) :
    ‖∑ n ∈ Finset.range N,
        phaseTerm (iteratedPhaseDifference shifts f) n‖ ^ 2 ≤
      aProcessSquaredBound (fun ell ↦ Real.sqrt (Q ell)) N L :=
  norm_iteratedPhase_sum_sq_le_aProcess_of_sq_bounds
    f shifts Q N L hL hLN hcorSq

example (f : ℕ → ℝ) (shifts : List ℕ)
    (C : ℕ → ℕ → ℝ) (L₂ : ℕ → ℕ) (N L₁ : ℕ)
    (hL₁ : 1 ≤ L₁) (hL₁N : L₁ ≤ N)
    (hL₂ : ∀ ell₁ ∈ Finset.Icc 1 (L₁ - 1), 1 ≤ L₂ ell₁)
    (hL₂N : ∀ ell₁ ∈ Finset.Icc 1 (L₁ - 1), L₂ ell₁ ≤ N - ell₁)
    (hsecond : ∀ ell₁ ∈ Finset.Icc 1 (L₁ - 1),
      ∀ ell₂ ∈ Finset.Icc 1 (L₂ ell₁ - 1),
        ‖∑ n ∈ Finset.range (N - ell₁ - ell₂),
          phaseTerm
            (iteratedPhaseDifference (ell₂ :: ell₁ :: shifts) f) n‖ ≤
          C ell₁ ell₂) :
    ‖∑ n ∈ Finset.range N,
        phaseTerm (iteratedPhaseDifference shifts f) n‖ ^ 2 ≤
      aProcessSquaredBound
        (fun ell₁ ↦ Real.sqrt
          (aProcessSquaredBound (C ell₁) (N - ell₁) (L₂ ell₁)))
        N L₁ :=
  norm_iteratedPhase_sum_sq_le_two_aProcess
    f shifts C L₂ N L₁ hL₁ hL₁N hL₂ hL₂N hsecond

end ZeroFreeRegion.VinogradovKorobov
