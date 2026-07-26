import ZeroFreeRegion.VinogradovKorobov.SecondDifferenceSum

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

/-- The concrete second-level correlation bound used by the two-step
A-process for a logarithmic zeta phase. -/
noncomputable def twoAProcessLogCorrelationBound
    (t : ℝ) (m N ell₁ ell₂ : ℕ) : ℝ :=
  2 * Real.pi /
    (t * logSecondDifferenceDecrement ell₂ ell₁
      ((m + (N - ell₁ - ell₂ - 1) : ℕ) : ℝ))

/-- Two recursive A-process steps for a shifted logarithmic zeta sum, with
all second-level correlations discharged by the concrete third-difference
Kusmin--Landau estimate.  The remaining `hturn` assumptions are explicit
parameter constraints, not unproved analytic estimates. -/
theorem norm_zetaOscillation_sum_sq_le_two_aProcess
    (t : ℝ) (m N L₁ : ℕ) (L₂ : ℕ → ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hL₁ : 1 ≤ L₁) (hL₁N : L₁ ≤ N)
    (hL₂ : ∀ ell₁ ∈ Finset.Icc 1 (L₁ - 1), 1 ≤ L₂ ell₁)
    (hL₂N : ∀ ell₁ ∈ Finset.Icc 1 (L₁ - 1),
      L₂ ell₁ ≤ N - ell₁)
    (hturn : ∀ ell₁ ∈ Finset.Icc 1 (L₁ - 1),
      ∀ ell₂ ∈ Finset.Icc 1 (L₂ ell₁ - 1),
        t * logSecondDifferenceDecrement ell₂ ell₁ m ≤
          2 * Real.pi -
            t * logSecondDifferenceDecrement ell₂ ell₁
              ((m + (N - ell₁ - ell₂ - 1) : ℕ) : ℝ)) :
    ‖∑ n ∈ Finset.range N, zetaOscillation t (m + n)‖ ^ 2 ≤
      aProcessSquaredBound
        (fun ell₁ ↦ Real.sqrt
          (aProcessSquaredBound
            (twoAProcessLogCorrelationBound t m N ell₁)
            (N - ell₁) (L₂ ell₁)))
        N L₁ := by
  have hsecond : ∀ ell₁ ∈ Finset.Icc 1 (L₁ - 1),
      ∀ ell₂ ∈ Finset.Icc 1 (L₂ ell₁ - 1),
        ‖∑ n ∈ Finset.range (N - ell₁ - ell₂),
          phaseTerm
            (iteratedPhaseDifference
              (ell₂ :: ell₁ :: []) (shiftedZetaPhase t m)) n‖ ≤
          twoAProcessLogCorrelationBound t m N ell₁ ell₂ := by
    intro ell₁ hell₁ ell₂ hell₂
    have hell₁pos : 0 < ell₁ := (Finset.mem_Icc.mp hell₁).1
    have hell₂pos : 0 < ell₂ := (Finset.mem_Icc.mp hell₂).1
    have hell₂upper : ell₂ ≤ L₂ ell₁ - 1 :=
      (Finset.mem_Icc.mp hell₂).2
    have hlength : 1 ≤ N - ell₁ - ell₂ := by
      have hL₂bound := hL₂N ell₁ hell₁
      omega
    have hkl := iteratedShiftedZetaPhase_two_kusminLandau_range
      t ell₂ ell₁ m (N - ell₁ - ell₂)
      ht hell₂pos hell₁pos hm hlength
      (hturn ell₁ hell₁ ell₂ hell₂)
    simpa only [twoAProcessLogCorrelationBound] using hkl
  have hbase := norm_iteratedPhase_sum_sq_le_two_aProcess
    (shiftedZetaPhase t m) []
    (twoAProcessLogCorrelationBound t m N) L₂ N L₁
    hL₁ hL₁N hL₂ hL₂N hsecond
  simpa only [iteratedPhaseDifference_nil,
    phaseTerm_shiftedZetaPhase] using hbase

end ZeroFreeRegion.VinogradovKorobov
