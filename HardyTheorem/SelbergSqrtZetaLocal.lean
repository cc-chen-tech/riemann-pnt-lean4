import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Data.Real.Basic

namespace HardyTheorem

/-!
# The local square-root zeta mollifier

Selberg's positive-proportion argument uses the Euler-factor coefficients of
`ζ(s)⁻¹ᐟ²`, rather than the Möbius coefficients of `ζ(s)⁻¹`.  The local
generating series is `(1 - X)^(1/2)`.  This file constructs that formal power
series and proves the square identity needed to globalize its coefficients.
-/

/-- The formal power series `(1 - X)^(1/2)`. -/
noncomputable def selbergSqrtZetaEulerFactor : PowerSeries ℝ :=
  PowerSeries.rescale (-1 : ℝ)
    (PowerSeries.binomialSeries ℝ (1 / 2 : ℝ))

/-- The coefficient of `X^k` in `(1 - X)^(1/2)`. -/
noncomputable def selbergSqrtZetaLocalCoeff (k : ℕ) : ℝ :=
  PowerSeries.coeff k selbergSqrtZetaEulerFactor

@[simp] theorem selbergSqrtZetaLocalCoeff_zero :
    selbergSqrtZetaLocalCoeff 0 = 1 := by
  simp [selbergSqrtZetaLocalCoeff, selbergSqrtZetaEulerFactor]

@[simp] theorem selbergSqrtZetaLocalCoeff_one :
    selbergSqrtZetaLocalCoeff 1 = -(1 / 2 : ℝ) := by
  simp [selbergSqrtZetaLocalCoeff, selbergSqrtZetaEulerFactor]

/-- Squaring the local Euler factor recovers the Möbius Euler factor. -/
theorem selbergSqrtZetaEulerFactor_sq :
    selbergSqrtZetaEulerFactor * selbergSqrtZetaEulerFactor =
      1 - PowerSeries.X := by
  rw [selbergSqrtZetaEulerFactor, ← map_mul,
    ← PowerSeries.binomialSeries_add]
  norm_num
  rw [show PowerSeries.binomialSeries ℝ (1 : ℝ) =
      (1 + PowerSeries.X) ^ (1 : ℕ) by
        simpa using (PowerSeries.binomialSeries_nat (A := ℝ) 1)]
  simp [sub_eq_add_neg]

/-- The self-convolution of the local coefficients is `1, -1, 0, ...`. -/
theorem sum_antidiagonal_selbergSqrtZetaLocalCoeff_mul
    (k : ℕ) :
    (∑ ij ∈ Finset.antidiagonal k,
        selbergSqrtZetaLocalCoeff ij.1 *
          selbergSqrtZetaLocalCoeff ij.2) =
      if k = 0 then 1 else if k = 1 then -1 else 0 := by
  unfold selbergSqrtZetaLocalCoeff
  rw [← PowerSeries.coeff_mul, selbergSqrtZetaEulerFactor_sq]
  by_cases hk0 : k = 0
  · subst k
    simp
  by_cases hk1 : k = 1
  · subst k
    simp
  simp [hk0, hk1, PowerSeries.coeff_X]

end HardyTheorem
