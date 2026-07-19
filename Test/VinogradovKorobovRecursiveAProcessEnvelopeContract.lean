import ZeroFreeRegion.VinogradovKorobov.RecursiveAProcessEnvelope

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable example (H : ℕ → ℕ) (N : ℕ) (C : ℝ)
    (depth level : ℕ) : ℝ :=
  coarseRecursiveAProcessSquaredBound H N C depth level

example (f : ℕ → ℝ) (H : ℕ → ℕ) (Q : List ℕ → ℝ)
    (N : ℕ) (C : ℝ) (depth : ℕ) (shifts : List ℕ)
    (hvalid : RecursiveAProcessValid f (fun s ↦ H s.length) Q N depth shifts)
    (hleaf : ∀ s, Q s ≤ C) :
    recursiveAProcessSquaredBound (fun s ↦ H s.length) Q N depth shifts ≤
      coarseRecursiveAProcessSquaredBound H N C depth shifts.length :=
  recursiveAProcessSquaredBound_le_coarse
    f H Q N C depth shifts hvalid hleaf

example (f : ℕ → ℝ) (H : ℕ → ℕ) (Q : List ℕ → ℝ)
    (N : ℕ) (C : ℝ) (depth : ℕ)
    (hvalid : RecursiveAProcessValid f (fun s ↦ H s.length) Q N depth [])
    (hleaf : ∀ s, Q s ≤ C) :
    ‖∑ n ∈ Finset.range N, phaseTerm f n‖ ^ 2 ≤
      coarseRecursiveAProcessSquaredBound H N C depth 0 :=
  norm_phaseSum_sq_le_coarseRecursiveAProcess
    f H Q N C depth hvalid hleaf

end ZeroFreeRegion.VinogradovKorobov
