import ZeroFreeRegion.VinogradovKorobov.RecursiveReciprocalEnvelope

namespace ZeroFreeRegion.VinogradovKorobov

example (Q : ℕ → ℝ) (C : ℝ) (N L : ℕ)
    (hL : 1 ≤ L) (hLN : L ≤ N) (hC : 0 ≤ C)
    (hQ : ∀ ell ∈ Finset.Icc 1 (L - 1),
      Q ell ≤ (C * (ell : ℝ)⁻¹) ^ 2) :
    aProcessSquaredBound (fun ell ↦ Real.sqrt (Q ell)) N L ≤
      2 * (N : ℝ) ^ 2 / L +
        4 * (N : ℝ) * C * (1 + Real.log L) / L :=
  aProcessSquaredBound_le_of_sq_reciprocal
    Q C N L hL hLN hC hQ

example (Q : ℕ → ℝ) (E P : ℝ) (N L : ℕ)
    (hL : 1 ≤ L) (hLN : L ≤ N) (hE : 0 ≤ E) (hP : 0 < P)
    (hQ : ∀ ell ∈ Finset.Icc 1 (L - 1),
      Q ell * ((ell : ℝ) * P) ^ 2 ≤ E) :
    aProcessSquaredBound (fun ell ↦ Real.sqrt (Q ell)) N L * P ^ 2 ≤
      2 * (N : ℝ) ^ 2 * P ^ 2 / L +
        4 * (N : ℝ) * Real.sqrt E * P * (1 + Real.log L) / L :=
  aProcessSquaredBound_mul_sq_le_of_scaled_children
    Q E P N L hL hLN hE hP hQ

example (H : ℕ → ℕ) (N depth level : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    0 ≤ refinedRecursiveAProcessSquaredBound H N C depth level :=
  refinedRecursiveAProcessSquaredBound_nonneg H N C depth level hC

example (f : ℕ → ℝ) (H : ℕ → ℕ) (Q : List ℕ → ℝ)
    (N depth : ℕ) (C : ℝ) (shifts : List ℕ)
    (hC : 0 ≤ C)
    (hvalid : RecursiveAProcessValid
      f (fun s ↦ H s.length) Q N depth shifts)
    (hleaf : ∀ s, (∀ h ∈ s, 0 < h) → Q s * (s.prod : ℝ) ^ 2 ≤ C)
    (hprod : shifts.prod ≤ aProcessScheduleProduct H shifts.length)
    (hshifts : ∀ h ∈ shifts, 0 < h) :
    recursiveAProcessSquaredBound
        (fun s ↦ H s.length) Q N depth shifts * (shifts.prod : ℝ) ^ 2 ≤
      refinedRecursiveAProcessSquaredBound H N C depth shifts.length :=
  recursiveAProcessSquaredBound_mul_prod_sq_le_refined
    f H Q N depth C shifts hC hvalid hleaf hprod hshifts

example (t : ℝ) (m N depth : ℕ) (shifts : List ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hshifts : ∀ h ∈ shifts, 0 < h) :
    zetaAProcessProductLeafSquaredBound t m N depth shifts *
        (shifts.prod : ℝ) ^ 2 =
      zetaAProcessUniformLeafSquaredBound t m N depth :=
  zetaAProcessProductLeafSquaredBound_mul_prod_sq
    t m N depth shifts ht hm hshifts

example (t : ℝ) (m N depth : ℕ) (H : ℕ → ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hvalid : RecursiveZetaAProcessScaleValid
      t m (fun s ↦ H s.length) N depth []) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤
      refinedRecursiveAProcessSquaredBound H N
        (zetaAProcessUniformLeafSquaredBound t m N depth) depth 0 :=
  norm_zetaPhase_sum_sq_le_refinedRecursiveAProcess_of_scale
    t m N depth H ht hm hvalid

example (t : ℝ) (m N depth : ℕ) (H : ℕ → ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hvalid : ZetaAProcessScheduleValid t m N depth H) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤
      refinedRecursiveAProcessSquaredBound H N
        (zetaAProcessUniformLeafSquaredBound t m N depth) depth 0 :=
  norm_zetaPhase_sum_sq_le_scheduledRefinedRecursiveAProcess
    t m N depth H ht hm hvalid

end ZeroFreeRegion.VinogradovKorobov
