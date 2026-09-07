import Mathlib

/-! Exact natural-number cutoffs for the square-root Poisson decomposition. -/

namespace HardyTheorem.AFE

/-- The actual square-root floor lies in its height cell, with an explicit
threshold sufficient for all five nearest-endpoint modes. -/
theorem natFloor_sqrt_heightCell {t : ℝ} (ht : 72 * Real.pi ≤ t) :
    let K := Nat.floor (Real.sqrt (t / (2 * Real.pi)))
    6 ≤ K ∧ 2 * Real.pi * (K : ℝ) ^ 2 ≤ t ∧
      t < 2 * Real.pi * ((K : ℝ) + 1) ^ 2 := by
  let q : ℝ := t / (2 * Real.pi)
  let K := Nat.floor (Real.sqrt q)
  have hp : 0 < 2 * Real.pi := by positivity
  have ht0 : 0 ≤ t := (show 0 ≤ 72 * Real.pi by positivity).trans ht
  have hq : 0 ≤ q := div_nonneg ht0 hp.le
  have hq36 : 36 ≤ q := by
    apply (le_div_iff₀ hp).mpr
    nlinarith
  have hsqrt := Real.sq_sqrt hq
  have hsqrt0 := Real.sqrt_nonneg q
  have hsqrt6 : (6 : ℝ) ≤ Real.sqrt q := by nlinarith
  have hK6 : 6 ≤ K := Nat.le_floor (by exact_mod_cast hsqrt6)
  have hK0 : 0 ≤ (K : ℝ) := Nat.cast_nonneg K
  have hfloor : (K : ℝ) ≤ Real.sqrt q := Nat.floor_le hsqrt0
  have hfloorU : Real.sqrt q < (K : ℝ) + 1 := Nat.lt_floor_add_one _
  have hsqL : (K : ℝ) ^ 2 ≤ q := by nlinarith
  have hsqU : q < ((K : ℝ) + 1) ^ 2 := by nlinarith
  refine ⟨hK6, ?_, ?_⟩
  · have h := (le_div_iff₀ hp).mp hsqL
    nlinarith
  · have h := (div_lt_iff₀ hp).mp hsqU
    nlinarith

/-- The finite cutoff is linear in `K`, lies beyond the complete endpoint
band, and is already in the inverse-square far-tail range. -/
theorem sqrt_heightCell_frequency_cutoff {K : ℕ} {t : ℝ} (hK : 6 ≤ K)
    (htL : 2 * Real.pi * (K : ℝ) ^ 2 ≤ t)
    (htU : t ≤ 2 * Real.pi * ((K : ℝ) + 1) ^ 2) :
    let M := Nat.ceil (t / (Real.pi * K))
    2 * K ≤ M ∧ M ≤ 2 * K + 5 ∧
      Nat.floor (t / (2 * Real.pi * K)) ≤ K + 2 ∧
      ∀ m : ℕ, M ≤ m → t / (K : ℝ) ≤ Real.pi * m := by
  let M := Nat.ceil (t / (Real.pi * K))
  have hK6 : 6 ≤ (K : ℝ) := by exact_mod_cast hK
  have hK0 : 0 < (K : ℝ) := by linarith
  have hpK : 0 < Real.pi * (K : ℝ) := mul_pos Real.pi_pos hK0
  have hp2K : 0 < 2 * Real.pi * (K : ℝ) := by positivity
  have ht0 : 0 ≤ t := (show 0 ≤ 2 * Real.pi * (K : ℝ) ^ 2 by positivity).trans htL
  have hqL : 2 * (K : ℝ) ≤ t / (Real.pi * K) := by
    apply (le_div_iff₀ hpK).mpr
    nlinarith
  have hqU : t / (Real.pi * K) ≤ 2 * (K : ℝ) + 5 := by
    apply (div_le_iff₀ hpK).mpr
    nlinarith [mul_nonneg Real.pi_pos.le (show 0 ≤ (K : ℝ) - 2 by linarith)]
  have hML : 2 * K ≤ M := by
    have h := hqL.trans (Nat.le_ceil (t / (Real.pi * K)))
    exact_mod_cast h
  have hMU : M ≤ 2 * K + 5 := Nat.ceil_le.mpr (by exact_mod_cast hqU)
  have hbetaU : t / (2 * Real.pi * K) < (K : ℝ) + 3 := by
    apply (div_lt_iff₀ hp2K).mpr
    nlinarith [mul_pos (show 0 < 2 * Real.pi by positivity)
      (show 0 < (K : ℝ) - 1 by linarith)]
  have hfloor : Nat.floor (t / (2 * Real.pi * K)) ≤ K + 2 := by
    have h : Nat.floor (t / (2 * Real.pi * K)) < K + 3 :=
      (Nat.floor_lt (div_nonneg ht0 hp2K.le)).mpr (by exact_mod_cast hbetaU)
    omega
  refine ⟨hML, hMU, hfloor, ?_⟩
  intro m hm
  have hmR : (M : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hq := (Nat.le_ceil (t / (Real.pi * K))).trans hmR
  have h := (div_le_iff₀ hpK).mp hq
  apply (div_le_iff₀ hK0).mpr
  nlinarith

end HardyTheorem.AFE
