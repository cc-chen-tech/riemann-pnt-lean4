import ZeroFreeRegion.VinogradovKorobov.ConstantPowerDecayAProcess

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable example (h N : ℕ) (C : ℝ) (depth : ℕ) : ℝ :=
  constantPowerDecayCoefficientMajorant h N C depth

example (h N : ℕ) (C : ℝ) (depth : ℕ) :
    0 ≤ constantPowerDecayCoefficientMajorant h N C depth :=
  constantPowerDecayCoefficientMajorant_nonneg h N C depth

example (h N : ℕ) (C : ℝ) (depth level : ℕ) (hh : 2 ≤ h) :
    aProcessPowerDecayCoefficient (fun _ ↦ h) N C depth level ≤
      constantPowerDecayCoefficientMajorant h N C depth :=
  aProcessPowerDecayCoefficient_const_le_majorant h N C depth level hh

example (t : ℝ) (m N depth h : ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hh : 2 ≤ h) (hhN : h ≤ N)
    (hbudget : depth * (h - 1) < N)
    (hmajor : t * ((depth.factorial : ℝ) * (h : ℝ) ^ depth *
      ((m : ℝ) ^ (depth + 1))⁻¹) ≤ Real.pi) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤
      constantAProcessSquaredEnvelope h N 0 depth +
        constantPowerDecayCoefficientMajorant h N
          (zetaAProcessUniformLeafSquaredBound t m N depth) depth :=
  norm_zetaPhase_sum_sq_le_constantPowerDecayMajorant
    t m N depth h ht hm hh hhN hbudget hmajor

end ZeroFreeRegion.VinogradovKorobov
