import ZeroFreeRegion.VinogradovKorobov.RecursiveAProcess

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

example (N : ℕ) (shifts : List ℕ) : ℕ :=
  remainingAProcessLength N shifts

noncomputable example (L : List ℕ → ℕ) (Q : List ℕ → ℝ)
    (N depth : ℕ) (shifts : List ℕ) : ℝ :=
  recursiveAProcessSquaredBound L Q N depth shifts

example (f : ℕ → ℝ) (L : List ℕ → ℕ) (Q : List ℕ → ℝ)
    (N depth : ℕ) (shifts : List ℕ)
    (hvalid : RecursiveAProcessValid f L Q N depth shifts) :
    ‖∑ n ∈ Finset.range (remainingAProcessLength N shifts),
        phaseTerm (iteratedPhaseDifference shifts f) n‖ ^ 2 ≤
      recursiveAProcessSquaredBound L Q N depth shifts :=
  norm_iteratedPhase_sum_sq_le_recursiveAProcess
    f L Q N depth shifts hvalid

example (f : ℕ → ℝ) (L : List ℕ → ℕ) (Q : List ℕ → ℝ)
    (N depth : ℕ)
    (hvalid : RecursiveAProcessValid f L Q N depth []) :
    ‖∑ n ∈ Finset.range N, phaseTerm f n‖ ^ 2 ≤
      recursiveAProcessSquaredBound L Q N depth [] :=
  norm_phaseSum_sq_le_recursiveAProcess f L Q N depth hvalid

end ZeroFreeRegion.VinogradovKorobov
