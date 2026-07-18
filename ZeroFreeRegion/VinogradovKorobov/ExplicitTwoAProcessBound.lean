import ZeroFreeRegion.VinogradovKorobov.AProcessBounds
import ZeroFreeRegion.VinogradovKorobov.ScaledTwoAProcessLogSum

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

/-- A single uniform envelope for every second-level logarithmic
correlation in a block. -/
noncomputable def globalLogCorrelationBound (t : ℝ) (m N : ℕ) : ℝ :=
  162 * Real.pi * ((m + N : ℕ) : ℝ) ^ 3 / t

/-- The resulting uniform inner A-process bound. -/
noncomputable def explicitTwoAProcessInnerBound
    (t : ℝ) (m N L₂ : ℕ) : ℝ :=
  2 * (N : ℝ) ^ 2 / L₂ +
    4 * (N : ℝ) * globalLogCorrelationBound t m N

/-- Inner A-process envelope retaining the reciprocal first shift. -/
noncomputable def refinedTwoAProcessInnerBound
    (t : ℝ) (m N L₂ ell₁ : ℕ) : ℝ :=
  2 * (N : ℝ) ^ 2 / L₂ +
    4 * (N : ℝ) *
      (globalLogCorrelationBound t m N * (ell₁ : ℝ)⁻¹) *
      (1 + Real.log L₂) / L₂

/-- Constant part of the refined inner A-process estimate. -/
noncomputable def refinedTwoAProcessConstantPart (N L₂ : ℕ) : ℝ :=
  2 * (N : ℝ) ^ 2 / L₂

/-- Reciprocal-shift coefficient of the refined inner A-process estimate. -/
noncomputable def refinedTwoAProcessReciprocalPart
    (t : ℝ) (m N L₂ : ℕ) : ℝ :=
  4 * (N : ℝ) * globalLogCorrelationBound t m N *
    (1 + Real.log L₂) / L₂

lemma refinedTwoAProcessInnerBound_eq
    (t : ℝ) (m N L₂ ell₁ : ℕ) :
    refinedTwoAProcessInnerBound t m N L₂ ell₁ =
      refinedTwoAProcessConstantPart N L₂ +
        refinedTwoAProcessReciprocalPart t m N L₂ * (ell₁ : ℝ)⁻¹ := by
  unfold refinedTwoAProcessInnerBound refinedTwoAProcessConstantPart
    refinedTwoAProcessReciprocalPart
  ring

lemma scaledTwoAProcessLogCorrelationBound_le_global
    (t : ℝ) (m N ell₁ ell₂ : ℕ)
    (ht : 0 < t) (hell₁ : 0 < ell₁) (hell₂ : 0 < ell₂) :
    scaledTwoAProcessLogCorrelationBound t m N ell₁ ell₂ ≤
      globalLogCorrelationBound t m N := by
  have hxNat :
      m + (N - ell₁ - ell₂ - 1) ≤ m + N := by omega
  have hx :
      (((m + (N - ell₁ - ell₂ - 1) : ℕ) : ℝ)) ≤
        ((m + N : ℕ) : ℝ) := by exact_mod_cast hxNat
  have hpow :
      (((m + (N - ell₁ - ell₂ - 1) : ℕ) : ℝ)) ^ 3 ≤
        ((m + N : ℕ) : ℝ) ^ 3 := by gcongr
  have hnum :
      162 * Real.pi *
          (((m + (N - ell₁ - ell₂ - 1) : ℕ) : ℝ)) ^ 3 ≤
        162 * Real.pi * ((m + N : ℕ) : ℝ) ^ 3 := by
    gcongr
  have hell₁R : 1 ≤ (ell₁ : ℝ) := by exact_mod_cast hell₁
  have hell₂R : 1 ≤ (ell₂ : ℝ) := by exact_mod_cast hell₂
  have hden : t ≤ t * (ell₂ : ℝ) * (ell₁ : ℝ) := by
    calc
      t = t * 1 * 1 := by ring
      _ ≤ t * (ell₂ : ℝ) * (ell₁ : ℝ) := by gcongr
  unfold scaledTwoAProcessLogCorrelationBound globalLogCorrelationBound
  calc
    162 * Real.pi *
          (((m + (N - ell₁ - ell₂ - 1) : ℕ) : ℝ)) ^ 3 /
        (t * (ell₂ : ℝ) * (ell₁ : ℝ)) ≤
        162 * Real.pi * ((m + N : ℕ) : ℝ) ^ 3 /
          (t * (ell₂ : ℝ) * (ell₁ : ℝ)) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ 162 * Real.pi * ((m + N : ℕ) : ℝ) ^ 3 / t :=
      div_le_div_of_nonneg_left (by positivity) ht hden

lemma scaledTwoAProcessLogCorrelationBound_le_reciprocal
    (t : ℝ) (m N ell₁ ell₂ : ℕ)
    (ht : 0 < t) (hell₁ : 0 < ell₁) (hell₂ : 0 < ell₂) :
    scaledTwoAProcessLogCorrelationBound t m N ell₁ ell₂ ≤
      (globalLogCorrelationBound t m N * (ell₁ : ℝ)⁻¹) *
        (ell₂ : ℝ)⁻¹ := by
  have hxNat :
      m + (N - ell₁ - ell₂ - 1) ≤ m + N := by omega
  have hx :
      (((m + (N - ell₁ - ell₂ - 1) : ℕ) : ℝ)) ≤
        ((m + N : ℕ) : ℝ) := by exact_mod_cast hxNat
  have hnum :
      162 * Real.pi *
          (((m + (N - ell₁ - ell₂ - 1) : ℕ) : ℝ)) ^ 3 ≤
        162 * Real.pi * ((m + N : ℕ) : ℝ) ^ 3 := by
    gcongr
  have hell₁ne : (ell₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hell₁.ne'
  have hell₂ne : (ell₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hell₂.ne'
  unfold scaledTwoAProcessLogCorrelationBound globalLogCorrelationBound
  calc
    162 * Real.pi *
          (((m + (N - ell₁ - ell₂ - 1) : ℕ) : ℝ)) ^ 3 /
        (t * (ell₂ : ℝ) * (ell₁ : ℝ)) ≤
        162 * Real.pi * ((m + N : ℕ) : ℝ) ^ 3 /
          (t * (ell₂ : ℝ) * (ell₁ : ℝ)) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = (162 * Real.pi * ((m + N : ℕ) : ℝ) ^ 3 / t *
          (ell₁ : ℝ)⁻¹) * (ell₂ : ℝ)⁻¹ := by
      field_simp

lemma aProcess_scaledCorrelation_le_innerBound
    (t : ℝ) (m N ell₁ L₂ : ℕ)
    (ht : 0 < t) (hell₁ : 0 < ell₁)
    (hL₂ : 1 ≤ L₂) (hL₂N : L₂ ≤ N - ell₁) :
    aProcessSquaredBound
        (scaledTwoAProcessLogCorrelationBound t m N ell₁)
        (N - ell₁) L₂ ≤
      explicitTwoAProcessInnerBound t m N L₂ := by
  have hglobal0 : 0 ≤ globalLogCorrelationBound t m N := by
    unfold globalLogCorrelationBound
    positivity
  have hraw := aProcessSquaredBound_le
    (scaledTwoAProcessLogCorrelationBound t m N ell₁)
    (globalLogCorrelationBound t m N) (N - ell₁) L₂
    hL₂ hL₂N hglobal0
    (by
      intro ell₂ hell₂
      have hell₂pos : 0 < ell₂ := (Finset.mem_Icc.mp hell₂).1
      unfold scaledTwoAProcessLogCorrelationBound
      positivity)
    (by
      intro ell₂ hell₂
      have hell₂pos : 0 < ell₂ := (Finset.mem_Icc.mp hell₂).1
      exact scaledTwoAProcessLogCorrelationBound_le_global
        t m N ell₁ ell₂ ht hell₁ hell₂pos)
  have hlength : ((N - ell₁ : ℕ) : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.sub_le N ell₁
  unfold explicitTwoAProcessInnerBound
  calc
    aProcessSquaredBound
        (scaledTwoAProcessLogCorrelationBound t m N ell₁)
        (N - ell₁) L₂ ≤
        2 * ((N - ell₁ : ℕ) : ℝ) ^ 2 / L₂ +
          4 * ((N - ell₁ : ℕ) : ℝ) *
            globalLogCorrelationBound t m N := hraw
    _ ≤ 2 * (N : ℝ) ^ 2 / L₂ +
          4 * (N : ℝ) * globalLogCorrelationBound t m N := by
      apply add_le_add
      · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg L₂)
        gcongr
      · gcongr

lemma aProcess_scaledCorrelation_le_refinedInnerBound
    (t : ℝ) (m N ell₁ L₂ : ℕ)
    (ht : 0 < t) (hell₁ : 0 < ell₁)
    (hL₂ : 1 ≤ L₂) (hL₂N : L₂ ≤ N - ell₁) :
    aProcessSquaredBound
        (scaledTwoAProcessLogCorrelationBound t m N ell₁)
        (N - ell₁) L₂ ≤
      refinedTwoAProcessInnerBound t m N L₂ ell₁ := by
  have hglobal0 : 0 ≤ globalLogCorrelationBound t m N := by
    unfold globalLogCorrelationBound
    positivity
  have hell₁inv0 : 0 ≤ ((ell₁ : ℝ)⁻¹) := by positivity
  have hC0 :
      0 ≤ globalLogCorrelationBound t m N * (ell₁ : ℝ)⁻¹ :=
    mul_nonneg hglobal0 hell₁inv0
  have hraw := aProcessSquaredBound_le_reciprocal
    (scaledTwoAProcessLogCorrelationBound t m N ell₁)
    (globalLogCorrelationBound t m N * (ell₁ : ℝ)⁻¹)
    (N - ell₁) L₂ hL₂ hL₂N hC0
    (by
      intro ell₂ hell₂
      have hell₂pos : 0 < ell₂ := (Finset.mem_Icc.mp hell₂).1
      unfold scaledTwoAProcessLogCorrelationBound
      positivity)
    (by
      intro ell₂ hell₂
      have hell₂pos : 0 < ell₂ := (Finset.mem_Icc.mp hell₂).1
      exact scaledTwoAProcessLogCorrelationBound_le_reciprocal
        t m N ell₁ ell₂ ht hell₁ hell₂pos)
  have hlength : ((N - ell₁ : ℕ) : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.sub_le N ell₁
  unfold refinedTwoAProcessInnerBound
  calc
    aProcessSquaredBound
        (scaledTwoAProcessLogCorrelationBound t m N ell₁)
        (N - ell₁) L₂ ≤
        2 * ((N - ell₁ : ℕ) : ℝ) ^ 2 / L₂ +
          4 * ((N - ell₁ : ℕ) : ℝ) *
            (globalLogCorrelationBound t m N * (ell₁ : ℝ)⁻¹) *
            (1 + Real.log L₂) / L₂ := hraw
    _ ≤ 2 * (N : ℝ) ^ 2 / L₂ +
          4 * (N : ℝ) *
            (globalLogCorrelationBound t m N * (ell₁ : ℝ)⁻¹) *
            (1 + Real.log L₂) / L₂ := by
      apply add_le_add
      · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg L₂)
        gcongr
      · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg L₂)
        gcongr

/-- Fully explicit two-step A-process bound for a logarithmic zeta block. -/
theorem norm_zetaOscillation_sum_sq_le_explicit_two_aProcess
    (t : ℝ) (m N L₁ L₂ : ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hL₁ : 1 ≤ L₁) (hL₂ : 1 ≤ L₂)
    (hLN : L₁ + L₂ ≤ N) (hL₁m : L₁ ≤ m) (hL₂m : L₂ ≤ m)
    (hscale :
      5 * t * (L₂ : ℝ) * (L₁ : ℝ) ≤ Real.pi * (m : ℝ) ^ 3) :
    ‖∑ n ∈ Finset.range N, zetaOscillation t (m + n)‖ ^ 2 ≤
      2 * (N : ℝ) ^ 2 / L₁ +
        4 * (N : ℝ) * Real.sqrt
          (explicitTwoAProcessInnerBound t m N L₂) := by
  have hbase := norm_zetaOscillation_sum_sq_le_scaled_two_aProcess_const
    t m N L₁ L₂ ht hm hL₁ hL₂ hLN hL₁m hL₂m hscale
  apply hbase.trans
  apply aProcessSquaredBound_le
    (fun ell₁ ↦ Real.sqrt
      (aProcessSquaredBound
        (scaledTwoAProcessLogCorrelationBound t m N ell₁)
        (N - ell₁) L₂))
    (Real.sqrt (explicitTwoAProcessInnerBound t m N L₂))
    N L₁ hL₁ (by omega) (Real.sqrt_nonneg _)
  · intro ell₁ hell₁
    exact Real.sqrt_nonneg _
  · intro ell₁ hell₁
    have hell₁pos : 0 < ell₁ := (Finset.mem_Icc.mp hell₁).1
    have hell₁upper := (Finset.mem_Icc.mp hell₁).2
    apply Real.sqrt_le_sqrt
    apply aProcess_scaledCorrelation_le_innerBound
      t m N ell₁ L₂ ht hell₁pos hL₂
    omega

/-- Refined explicit two-step A-process bound retaining both reciprocal shift
gains and closing the outer weighted sum by Cauchy--Schwarz. -/
theorem norm_zetaOscillation_sum_sq_le_refined_two_aProcess
    (t : ℝ) (m N L₁ L₂ : ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hL₁ : 1 ≤ L₁) (hL₂ : 1 ≤ L₂)
    (hLN : L₁ + L₂ ≤ N) (hL₁m : L₁ ≤ m) (hL₂m : L₂ ≤ m)
    (hscale :
      5 * t * (L₂ : ℝ) * (L₁ : ℝ) ≤ Real.pi * (m : ℝ) ^ 3) :
    ‖∑ n ∈ Finset.range N, zetaOscillation t (m + n)‖ ^ 2 ≤
      2 * (N : ℝ) ^ 2 / L₁ +
        4 * (N : ℝ) *
          (Real.sqrt (refinedTwoAProcessConstantPart N L₂) *
              (L₁ : ℝ) ^ 2 +
            Real.sqrt (refinedTwoAProcessReciprocalPart t m N L₂) *
              Real.sqrt ((L₁ : ℝ) ^ 3 * (1 + Real.log L₁))) /
          (L₁ : ℝ) ^ 2 := by
  have hbase := norm_zetaOscillation_sum_sq_le_scaled_two_aProcess_const
    t m N L₁ L₂ ht hm hL₁ hL₂ hLN hL₁m hL₂m hscale
  apply hbase.trans
  have hlog₂ : 0 ≤ 1 + Real.log (L₂ : ℝ) := by
    have hcast : (1 : ℝ) ≤ (L₂ : ℝ) := by exact_mod_cast hL₂
    have := Real.log_nonneg hcast
    linarith
  have hA : 0 ≤ refinedTwoAProcessConstantPart N L₂ := by
    unfold refinedTwoAProcessConstantPart
    positivity
  have hD : 0 ≤ refinedTwoAProcessReciprocalPart t m N L₂ := by
    unfold refinedTwoAProcessReciprocalPart globalLogCorrelationBound
    positivity
  apply aProcessSquaredBound_le_sqrt_reciprocal
    (fun ell₁ ↦ Real.sqrt
      (aProcessSquaredBound
        (scaledTwoAProcessLogCorrelationBound t m N ell₁)
        (N - ell₁) L₂))
    (refinedTwoAProcessConstantPart N L₂)
    (refinedTwoAProcessReciprocalPart t m N L₂)
    N L₁ hL₁ (by omega) hA hD
  · intro ell₁ hell₁
    exact Real.sqrt_nonneg _
  · intro ell₁ hell₁
    have hell₁pos : 0 < ell₁ := (Finset.mem_Icc.mp hell₁).1
    have hell₁upper := (Finset.mem_Icc.mp hell₁).2
    apply Real.sqrt_le_sqrt
    calc
      aProcessSquaredBound
          (scaledTwoAProcessLogCorrelationBound t m N ell₁)
          (N - ell₁) L₂ ≤
          refinedTwoAProcessInnerBound t m N L₂ ell₁ :=
        aProcess_scaledCorrelation_le_refinedInnerBound
          t m N ell₁ L₂ ht hell₁pos hL₂ (by omega)
      _ = refinedTwoAProcessConstantPart N L₂ +
          refinedTwoAProcessReciprocalPart t m N L₂ * (ell₁ : ℝ)⁻¹ :=
        refinedTwoAProcessInnerBound_eq t m N L₂ ell₁

/-- Equal-step form of the refined two-step estimate, ready for an integer
choice of a single differencing length `L`. -/
theorem norm_zetaOscillation_sum_sq_le_refined_two_aProcess_equal
    (t : ℝ) (m N L : ℕ)
    (ht : 0 < t) (hm : 0 < m) (hL : 1 ≤ L)
    (hLN : 2 * L ≤ N) (hLm : L ≤ m)
    (hscale :
      5 * t * (L : ℝ) ^ 2 ≤ Real.pi * (m : ℝ) ^ 3) :
    ‖∑ n ∈ Finset.range N, zetaOscillation t (m + n)‖ ^ 2 ≤
      2 * (N : ℝ) ^ 2 / L +
        4 * (N : ℝ) *
          (Real.sqrt (refinedTwoAProcessConstantPart N L) *
              (L : ℝ) ^ 2 +
            Real.sqrt (refinedTwoAProcessReciprocalPart t m N L) *
              Real.sqrt ((L : ℝ) ^ 3 * (1 + Real.log L))) /
          (L : ℝ) ^ 2 := by
  apply norm_zetaOscillation_sum_sq_le_refined_two_aProcess
    t m N L L ht hm hL hL (by omega) hLm hLm
  nlinarith [hscale]

end ZeroFreeRegion.VinogradovKorobov
