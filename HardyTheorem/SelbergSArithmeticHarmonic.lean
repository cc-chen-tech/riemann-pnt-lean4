import Mathlib.NumberTheory.Harmonic.Bounds

open scoped BigOperators

namespace HardyTheorem

/-! # The finite harmonic factor in the Selberg arithmetic sum. -/

theorem selberg_sum_Icc_inv_le_one_add_log (Y : ℕ) :
    (∑ m ∈ Finset.Icc 1 Y, (m : ℝ)⁻¹) ≤
      1 + Real.log (Y : ℝ) := by
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast] using harmonic_le_one_add_log Y

end HardyTheorem
