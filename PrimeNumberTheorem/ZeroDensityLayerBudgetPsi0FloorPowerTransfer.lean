import PrimeNumberTheorem.ZeroDensityLayerBudgetPsi0FloorRoundingDecay

open Filter Topology Asymptotics

namespace PrimeNumberTheorem

/--
An arbitrary positive fraction of the target power eventually absorbs the
full midpoint floor-rounding budget.
-/
theorem eventually_chebyshevPsi0FloorRoundingBudget_le_mul_targetPower
    {beta loss : ℝ} (hbeta : 0 < beta) (hloss : 0 < loss) :
    ∀ᶠ x : ℝ in atTop,
      chebyshevPsi0FloorRoundingBudget x ≤ loss * x ^ beta := by
  have hsmall :=
    (chebyshevPsi0FloorRoundingBudget_isLittleO_targetPower hbeta).def hloss
  filter_upwards [hsmall, eventually_ge_atTop (0 : ℝ)] with x hx hnonneg
  simpa [Real.norm_eq_abs,
    abs_of_nonneg (chebyshevPsi0FloorRoundingBudget_nonneg x),
    abs_of_nonneg (Real.rpow_nonneg hnonneg beta)] using hx

/--
Logarithmic form of the eventual absorption estimate.
-/
theorem eventually_chebyshevPsi0FloorRoundingBudget_exp_le
    {beta loss : ℝ} (hbeta : 0 < beta) (hloss : 0 < loss) :
    ∀ᶠ y : ℝ in atTop,
      chebyshevPsi0FloorRoundingBudget (Real.exp y) ≤
        loss * Real.exp (beta * y) := by
  have hpower :=
    Real.tendsto_exp_atTop.eventually
      (eventually_chebyshevPsi0FloorRoundingBudget_le_mul_targetPower
        hbeta hloss)
  filter_upwards [hpower] with y hy
  rw [Real.rpow_def_of_pos (Real.exp_pos y), Real.log_exp] at hy
  simpa [mul_comm] using hy

/--
Pointwise sharp-constant transfer: if the floor-rounding budget consumes at
most `loss` times the zero-forced power, a continuous coefficient `c`
survives at the natural floor with coefficient `c - loss`.
-/
theorem continuousExpPowerPsi0Witness_to_natFloor_of_roundingSmall
    {y beta c loss : ℝ}
    (hround :
      chebyshevPsi0FloorRoundingBudget (Real.exp y) ≤
        loss * Real.exp (beta * y))
    (hwitness :
      c * Real.exp (beta * y) ≤
        |chebyshevPsi0Error (Real.exp y)|) :
    (c - loss) * Real.exp (beta * y) ≤
      |chebyshevPsi0Error (Nat.floor (Real.exp y) : ℝ)| := by
  have hfloor :=
    continuousExpPsi0Witness_to_natFloor
      (y := y) (amplitude := c * Real.exp (beta * y)) hwitness
  calc
    (c - loss) * Real.exp (beta * y) =
        c * Real.exp (beta * y) - loss * Real.exp (beta * y) := by
      ring
    _ ≤
        c * Real.exp (beta * y) -
          chebyshevPsi0FloorRoundingBudget (Real.exp y) :=
      sub_le_sub_left hround _
    _ ≤ |chebyshevPsi0Error (Nat.floor (Real.exp y) : ℝ)| :=
      hfloor

/--
Eventually, every continuous `c * exp (beta*y)` witness transfers to the
natural floor with any prescribed positive coefficient loss.
-/
theorem eventually_continuousExpPowerPsi0Witness_to_natFloor
    {beta c loss : ℝ} (hbeta : 0 < beta) (hloss : 0 < loss) :
    ∀ᶠ y : ℝ in atTop,
      c * Real.exp (beta * y) ≤
          |chebyshevPsi0Error (Real.exp y)| →
        (c - loss) * Real.exp (beta * y) ≤
          |chebyshevPsi0Error (Nat.floor (Real.exp y) : ℝ)| := by
  filter_upwards [
    eventually_chebyshevPsi0FloorRoundingBudget_exp_le hbeta hloss
  ] with y hround
  exact
    continuousExpPowerPsi0Witness_to_natFloor_of_roundingSmall
      hround

end PrimeNumberTheorem
