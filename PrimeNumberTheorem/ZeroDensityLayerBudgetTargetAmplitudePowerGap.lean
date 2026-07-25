import PrimeNumberTheorem.ZeroDensityLayerBudgetTargetAmplitudeBarrier

open Filter Topology

namespace PrimeNumberTheorem

/-!
# Power-layer gap relative to a target zero

A zero layer with real part `sigma` contributes on the relative power scale
`x ^ (sigma - 1)`.  Against a target layer of real part `beta`, the exact
exponential-form ratio is `x ^ (sigma - beta)`.

The three cases below isolate the mathematical boundary:

* `sigma < beta`: the layer is target-amplitude negligible;
* `sigma = beta`: the ratio is identically one;
* `beta < sigma`: the ratio diverges.

Thus a zero-counting bound alone cannot remove same-real-part layers.  They
must be included in the main cluster or controlled by a separate
anti-cancellation argument.
-/

/-- Exponential form of the ratio between a `sigma` layer and a target
`beta` layer at natural points. -/
noncomputable def pntPowerLayerToTargetRatio
    (beta sigma : ℝ) (m : ℕ) : ℝ :=
  Real.exp ((sigma - beta) * Real.log (m : ℝ))

/-- The ratio is exactly the quotient of the two relative power factors in
exponential form. -/
theorem pntPowerLayerToTargetRatio_eq_exp_div_exp
    (beta sigma : ℝ) (m : ℕ) :
    pntPowerLayerToTargetRatio beta sigma m =
      Real.exp ((sigma - 1) * Real.log (m : ℝ)) /
        Real.exp ((beta - 1) * Real.log (m : ℝ)) := by
  unfold pntPowerLayerToTargetRatio
  rw [← Real.exp_sub]
  apply congrArg Real.exp
  ring

/-- Strict real-part separation below the target makes a power layer
negligible on the target-amplitude scale. -/
theorem pntPowerLayerToTargetRatio_tendsto_zero_of_lt
    {beta sigma : ℝ} (hgap : sigma < beta) :
    Tendsto
      (pntPowerLayerToTargetRatio beta sigma)
      atTop (𝓝 0) := by
  have hlog :
      Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hnegLog :
      Tendsto (fun m : ℕ => -Real.log (m : ℝ)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hlog
  have hscaled :
      Tendsto
        (fun m : ℕ => (beta - sigma) * (-Real.log (m : ℝ)))
        atTop atBot :=
    hnegLog.const_mul_atBot (sub_pos.mpr hgap)
  have hexp :
      Tendsto
        (fun m : ℕ =>
          Real.exp ((beta - sigma) * (-Real.log (m : ℝ))))
        atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hscaled
  refine hexp.congr' ?_
  filter_upwards with m
  unfold pntPowerLayerToTargetRatio
  apply congrArg Real.exp
  ring

/-- A same-real-part layer has exactly the same target power scale. -/
theorem pntPowerLayerToTargetRatio_self
    (beta : ℝ) :
    pntPowerLayerToTargetRatio beta beta = fun _ : ℕ => 1 := by
  funext m
  simp [pntPowerLayerToTargetRatio]

/-- A same-real-part layer is not target-amplitude negligible. -/
theorem not_tendsto_pntPowerLayerToTargetRatio_self_zero
    (beta : ℝ) :
    ¬ Tendsto
      (pntPowerLayerToTargetRatio beta beta)
      atTop (𝓝 0) := by
  rw [pntPowerLayerToTargetRatio_self]
  intro hzero
  have hone :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  exact zero_ne_one
    (tendsto_nhds_unique hzero hone)

/-- A layer strictly to the right of the target dominates the target power
scale. -/
theorem pntPowerLayerToTargetRatio_tendsto_atTop_of_lt
    {beta sigma : ℝ} (hgap : beta < sigma) :
    Tendsto
      (pntPowerLayerToTargetRatio beta sigma)
      atTop atTop := by
  have hlog :
      Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hscaled :
      Tendsto
        (fun m : ℕ => (sigma - beta) * Real.log (m : ℝ))
        atTop atTop :=
    hlog.const_mul_atTop (sub_pos.mpr hgap)
  exact Real.tendsto_exp_atTop.comp hscaled

/-- In particular, every fixed `1 / m`-scale residual is negligible against
a target zero with positive real part. -/
theorem pntInverseScaleToTargetRatio_tendsto_zero
    {beta : ℝ} (hbeta : 0 < beta) :
    Tendsto
      (pntPowerLayerToTargetRatio beta 0)
      atTop (𝓝 0) :=
  pntPowerLayerToTargetRatio_tendsto_zero_of_lt hbeta

end PrimeNumberTheorem
