import HardyTheorem.AFEExplicitPoissonHeightScale

open HardyTheorem AFE

-- The entire square-root cell, including both endpoints, has the AFE scale.
example {t : ℝ} {K : ℕ} (hK : 6 ≤ K)
    (htL : 2 * Real.pi * (K : ℝ) ^ 2 ≤ t)
    (htU : t ≤ 2 * Real.pi * ((K : ℝ) + 1) ^ 2) :
    let M := Nat.ceil (t / (Real.pi * K))
    1 ≤ t ∧
      (K : ℝ) ^ (-(1 / 2) : ℝ) ≤ 2 * t ^ (-1 / 4 : ℝ) ∧
      1 + Real.log M ≤ 1 + Real.log t ∧
      2 * Real.sqrt K * Real.exp (-2 * Real.pi * t) ≤ t ^ (-1 / 4 : ℝ) :=
  sqrt_heightCell_logAfe_scales hK htL htU

#print axioms sqrt_heightCell_logAfe_scales
