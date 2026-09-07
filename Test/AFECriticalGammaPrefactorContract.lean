import HardyTheorem.AFECriticalGammaPrefactor

open Complex HardyTheorem.AFE

-- The raw coefficient is not a unit phase: its exact squared norm is required.
example (t : ℝ) :
    let s : ℂ := (1 / 2 : ℂ) + I * t
    ‖((2 * Real.pi : ℝ) : ℂ) ^ (s - 1) *
      (Complex.exp (I * ((Real.pi / 2 : ℝ) : ℂ) * (1 - s)) * Complex.Gamma (1 - s))‖ ^ 2 =
        1 / (1 + Real.exp (-2 * Real.pi * t)) :=
  norm_criticalGammaPrefactor_sq t

-- Nonvanishing and the uniform bound are proved, not normalization hypotheses.
example (t : ℝ) :
    let s : ℂ := (1 / 2 : ℂ) + I * t
    let P : ℂ := ((2 * Real.pi : ℝ) : ℂ) ^ (s - 1) *
      (Complex.exp (I * ((Real.pi / 2 : ℝ) : ℂ) * (1 - s)) * Complex.Gamma (1 - s))
    0 < ‖P‖ ∧ ‖P‖ ≤ 1 :=
  norm_criticalGammaPrefactor_pos_and_le_one t

-- The weak AFE permits any unit phase, with this actual exponential error.
example (t : ℝ) :
    let s : ℂ := (1 / 2 : ℂ) + I * t
    let P : ℂ := ((2 * Real.pi : ℝ) : ℂ) ^ (s - 1) *
      (Complex.exp (I * ((Real.pi / 2 : ℝ) : ℂ) * (1 - s)) * Complex.Gamma (1 - s))
    ∃ U : ℂ, ‖U‖ = 1 ∧ ‖P - U‖ ≤ Real.exp (-2 * Real.pi * t) :=
  exists_unitPhase_close_criticalGammaPrefactor t

-- A normalization sanity check: at zero height the raw squared norm is 1/2, not 1.
example : ‖criticalGammaPrefactor 0‖ ^ 2 = (1 / 2 : ℝ) := by
  have h := norm_criticalGammaPrefactor_sq 0
  norm_num at h
  exact h

#print axioms norm_criticalGammaPrefactor_sq
#print axioms norm_criticalGammaPrefactor_pos_and_le_one
#print axioms exists_unitPhase_close_criticalGammaPrefactor
