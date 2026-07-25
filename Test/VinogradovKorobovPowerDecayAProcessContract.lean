import ZeroFreeRegion.VinogradovKorobov.PowerDecayAProcess

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable example (depth : ℕ) : ℝ := aProcessPowerDecayExponent depth

noncomputable example (H : ℕ → ℕ) (N : ℕ) (C : ℝ)
    (depth level : ℕ) : ℝ :=
  aProcessPowerDecayConstant H N C depth level

noncomputable example (H : ℕ → ℕ) (N : ℕ) (C : ℝ)
    (depth level : ℕ) : ℝ :=
  aProcessPowerDecayCoefficient H N C depth level

noncomputable example (H : ℕ → ℕ) (N : ℕ) (C : ℝ)
    (depth level : ℕ) (P : ℝ) : ℝ :=
  aProcessPowerDecayEnvelope H N C depth level P

example (depth : ℕ) : 0 < aProcessPowerDecayExponent depth :=
  aProcessPowerDecayExponent_pos depth

example (depth : ℕ) :
    aProcessPowerDecayExponent depth = 1 / (2 : ℝ) ^ depth :=
  aProcessPowerDecayExponent_eq depth

example (H : ℕ → ℕ) (N : ℕ) (C : ℝ) (depth level : ℕ)
    (hH : 2 ≤ H level) :
    aProcessPowerDecayCoefficient H N C (depth + 1) level ≤
      8 * (N : ℝ) * Real.sqrt
          (aProcessPowerDecayCoefficient H N C depth (level + 1)) /
        (1 - aProcessPowerDecayExponent depth / 2) *
          (H level : ℝ) ^ (-(aProcessPowerDecayExponent depth / 2)) :=
  aProcessPowerDecayCoefficient_succ_le_rpow H N C depth level hH

example (H : ℕ → ℕ) (N : ℕ) (C P : ℝ) (depth level : ℕ)
    (hC : 0 ≤ C) (hP : 0 < P)
    (hHlower : ∀ j, 2 ≤ H j) (hHupper : ∀ j, H j ≤ N) :
    hybridProductRecursiveAProcessSquaredBound H N C depth level P ≤
      aProcessPowerDecayEnvelope H N C depth level P :=
  hybridProductRecursiveAProcessSquaredBound_le_powerDecay
    H N C depth level P hC hP hHlower hHupper

example (t : ℝ) (m N depth : ℕ) (H : ℕ → ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hHlower : ∀ j, 2 ≤ H j) (hHupper : ∀ j, H j ≤ N)
    (hvalid : RecursiveZetaAProcessScaleValid
      t m (fun s ↦ H s.length) N depth []) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤
      aProcessPowerDecayEnvelope H N
        (zetaAProcessUniformLeafSquaredBound t m N depth) depth 0 1 :=
  norm_zetaPhase_sum_sq_le_powerDecayEnvelope_of_scale
    t m N depth H ht hm hHlower hHupper hvalid

end ZeroFreeRegion.VinogradovKorobov
