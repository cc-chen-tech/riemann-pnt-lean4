import ZeroFreeRegion.VinogradovKorobov.ScaledSecondDifferenceSum

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

/-- Scale-explicit second-level correlation bound for the logarithmic
two-step A-process. -/
noncomputable def scaledTwoAProcessLogCorrelationBound
    (t : ℝ) (m N ell₁ ell₂ : ℕ) : ℝ :=
  162 * Real.pi * ((m + (N - ell₁ - ell₂ - 1) : ℕ) : ℝ) ^ 3 /
    (t * ell₂ * ell₁)

/-- Two A-process steps with every second-level logarithmic correlation
replaced by its explicit `x^3 / (t ell₁ ell₂)` bound. -/
theorem norm_zetaOscillation_sum_sq_le_scaled_two_aProcess
    (t : ℝ) (m N L₁ : ℕ) (L₂ : ℕ → ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hL₁ : 1 ≤ L₁) (hL₁N : L₁ ≤ N) (hL₁m : L₁ ≤ m)
    (hL₂ : ∀ ell₁ ∈ Finset.Icc 1 (L₁ - 1), 1 ≤ L₂ ell₁)
    (hL₂N : ∀ ell₁ ∈ Finset.Icc 1 (L₁ - 1),
      L₂ ell₁ ≤ N - ell₁)
    (hL₂m : ∀ ell₁ ∈ Finset.Icc 1 (L₁ - 1), L₂ ell₁ ≤ m)
    (hscale : ∀ ell₁ ∈ Finset.Icc 1 (L₁ - 1),
      ∀ ell₂ ∈ Finset.Icc 1 (L₂ ell₁ - 1),
        5 * t * (ell₂ : ℝ) * (ell₁ : ℝ) ≤
          Real.pi * (m : ℝ) ^ 3) :
    ‖∑ n ∈ Finset.range N, zetaOscillation t (m + n)‖ ^ 2 ≤
      aProcessSquaredBound
        (fun ell₁ ↦ Real.sqrt
          (aProcessSquaredBound
            (scaledTwoAProcessLogCorrelationBound t m N ell₁)
            (N - ell₁) (L₂ ell₁)))
        N L₁ := by
  have hsecond : ∀ ell₁ ∈ Finset.Icc 1 (L₁ - 1),
      ∀ ell₂ ∈ Finset.Icc 1 (L₂ ell₁ - 1),
        ‖∑ n ∈ Finset.range (N - ell₁ - ell₂),
          phaseTerm
            (iteratedPhaseDifference
              (ell₂ :: ell₁ :: []) (shiftedZetaPhase t m)) n‖ ≤
          scaledTwoAProcessLogCorrelationBound t m N ell₁ ell₂ := by
    intro ell₁ hell₁ ell₂ hell₂
    have hell₁pos : 0 < ell₁ := (Finset.mem_Icc.mp hell₁).1
    have hell₂pos : 0 < ell₂ := (Finset.mem_Icc.mp hell₂).1
    have hell₁upper : ell₁ ≤ L₁ - 1 := (Finset.mem_Icc.mp hell₁).2
    have hell₂upper : ell₂ ≤ L₂ ell₁ - 1 :=
      (Finset.mem_Icc.mp hell₂).2
    have hlength : 1 ≤ N - ell₁ - ell₂ := by
      have hL₂bound := hL₂N ell₁ hell₁
      omega
    have hell₁m : ell₁ ≤ m := by omega
    have hell₂m : ell₂ ≤ m := by
      have hL₂bound := hL₂m ell₁ hell₁
      omega
    have hcor :=
      iteratedShiftedZetaPhase_two_kusminLandau_scaled_range_of_start_scale
        t ell₂ ell₁ m (N - ell₁ - ell₂)
        ht hell₂pos hell₁pos hm hlength hell₂m hell₁m
        (hscale ell₁ hell₁ ell₂ hell₂)
    simpa only [scaledTwoAProcessLogCorrelationBound] using hcor
  have hbase := norm_iteratedPhase_sum_sq_le_two_aProcess
    (shiftedZetaPhase t m) []
    (scaledTwoAProcessLogCorrelationBound t m N) L₂ N L₁
    hL₁ hL₁N hL₂ hL₂N hsecond
  simpa only [iteratedPhaseDifference_nil,
    phaseTerm_shiftedZetaPhase] using hbase

/-- Constant-step specialization.  All pointwise A-process constraints are
reduced to the two endpoint conditions `L₁ + L₂ ≤ N` and
`5 t L₁ L₂ ≤ π m^3`. -/
theorem norm_zetaOscillation_sum_sq_le_scaled_two_aProcess_const
    (t : ℝ) (m N L₁ L₂ : ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hL₁ : 1 ≤ L₁) (hL₂ : 1 ≤ L₂)
    (hLN : L₁ + L₂ ≤ N) (hL₁m : L₁ ≤ m) (hL₂m : L₂ ≤ m)
    (hscale :
      5 * t * (L₂ : ℝ) * (L₁ : ℝ) ≤ Real.pi * (m : ℝ) ^ 3) :
    ‖∑ n ∈ Finset.range N, zetaOscillation t (m + n)‖ ^ 2 ≤
      aProcessSquaredBound
        (fun ell₁ ↦ Real.sqrt
          (aProcessSquaredBound
            (scaledTwoAProcessLogCorrelationBound t m N ell₁)
            (N - ell₁) L₂))
        N L₁ := by
  apply norm_zetaOscillation_sum_sq_le_scaled_two_aProcess
    t m N L₁ (fun _ ↦ L₂) ht hm hL₁ (by omega) hL₁m
  · intro ell₁ hell₁
    exact hL₂
  · intro ell₁ hell₁
    have hell₁upper := (Finset.mem_Icc.mp hell₁).2
    omega
  · intro ell₁ hell₁
    exact hL₂m
  · intro ell₁ hell₁ ell₂ hell₂
    have hell₁pos : 0 ≤ (ell₁ : ℝ) := Nat.cast_nonneg ell₁
    have hell₂pos : 0 ≤ (ell₂ : ℝ) := Nat.cast_nonneg ell₂
    have hell₁upper : ell₁ ≤ L₁ := by
      have h := (Finset.mem_Icc.mp hell₁).2
      omega
    have hell₂upper : ell₂ ≤ L₂ := by
      have h := (Finset.mem_Icc.mp hell₂).2
      omega
    have hprod :
        (ell₂ : ℝ) * (ell₁ : ℝ) ≤ (L₂ : ℝ) * (L₁ : ℝ) := by
      exact mul_le_mul (by exact_mod_cast hell₂upper)
        (by exact_mod_cast hell₁upper) hell₁pos (Nat.cast_nonneg L₂)
    calc
      5 * t * (ell₂ : ℝ) * (ell₁ : ℝ) =
          (5 * t) * ((ell₂ : ℝ) * (ell₁ : ℝ)) := by ring
      _ ≤ (5 * t) * ((L₂ : ℝ) * (L₁ : ℝ)) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = 5 * t * (L₂ : ℝ) * (L₁ : ℝ) := by ring
      _ ≤ Real.pi * (m : ℝ) ^ 3 := hscale

end ZeroFreeRegion.VinogradovKorobov
