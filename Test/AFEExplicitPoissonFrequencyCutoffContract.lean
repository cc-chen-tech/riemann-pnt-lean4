import HardyTheorem.AFEExplicitPoissonFrequencyCutoff

open HardyTheorem AFE

-- The actual natural floor has the stated cell, including the lower boundary.
example {t : ℝ} (ht : 72 * Real.pi ≤ t) :
    let K := Nat.floor (Real.sqrt (t / (2 * Real.pi)))
    6 ≤ K ∧ 2 * Real.pi * (K : ℝ) ^ 2 ≤ t ∧
      t < 2 * Real.pi * ((K : ℝ) + 1) ^ 2 :=
  natFloor_sqrt_heightCell ht

-- Every integer at or beyond M meets the existing analytic far-tail condition.
example {K : ℕ} {t : ℝ} (hK : 6 ≤ K)
    (htL : 2 * Real.pi * (K : ℝ) ^ 2 ≤ t)
    (htU : t ≤ 2 * Real.pi * ((K : ℝ) + 1) ^ 2) :
    let M := Nat.ceil (t / (Real.pi * K))
    2 * K ≤ M ∧ M ≤ 2 * K + 5 ∧
      Nat.floor (t / (2 * Real.pi * K)) ≤ K + 2 ∧
      ∀ m : ℕ, M ≤ m → t / (K : ℝ) ≤ Real.pi * m :=
  sqrt_heightCell_frequency_cutoff hK htL htU

#print axioms natFloor_sqrt_heightCell
#print axioms sqrt_heightCell_frequency_cutoff
