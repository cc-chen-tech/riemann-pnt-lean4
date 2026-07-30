import PrimeNumberTheorem.ZeroDensityLayerBudgetTargetAmplitudeTransfer
import PrimeNumberTheorem.PNTAsymptotics

open Filter Topology

namespace PrimeNumberTheorem

/-!
# Target-amplitude barrier for subpolynomial contour heights

The fixed-rate Pintz height produces the contour-decay factor
`exp (-rate * sqrt (log m))`.  A target zero with real part `beta < 1`
has relative amplitude on the power scale `m ^ (beta - 1)`.

After normalization, the corresponding majorant factor is

`exp ((1 - beta) * log m - rate * sqrt (log m))`,

which tends to infinity.  Consequently the existing ordinary contour
majorant cannot, by itself, certify target-amplitude negligibility.  This is
a limitation of that upper majorant and is not a lower bound for the actual
contour remainder.
-/

/-- Quadratic-versus-linear exponent appearing after a power-scale target
amplitude normalization. -/
noncomputable def pntSubpolynomialContourToPowerRatio
    (delta rate : ℝ) (m : ℕ) : ℝ :=
  Real.exp
    (delta * Real.log (m : ℝ) - rate * pntSqrtLog m)

/-- Every positive power exponent dominates every fixed
square-root-logarithmic contour rate. -/
theorem pntSubpolynomialContourToPowerRatio_tendsto_atTop
    {delta : ℝ} (hdelta : 0 < delta) (rate : ℝ) :
    Tendsto
      (pntSubpolynomialContourToPowerRatio delta rate)
      atTop atTop := by
  have hlinear :
      Tendsto (fun u : ℝ => delta * u - rate) atTop atTop := by
    simpa [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-rate)
        ((tendsto_id :
            Tendsto (fun u : ℝ => u) atTop atTop).const_mul_atTop hdelta))
  have hquadratic :
      Tendsto
        (fun u : ℝ => (delta * u - rate) * u)
        atTop atTop :=
    hlinear.atTop_mul_atTop₀
      (tendsto_id : Tendsto (fun u : ℝ => u) atTop atTop)
  have hexponential :
      Tendsto
        (fun u : ℝ => Real.exp ((delta * u - rate) * u))
        atTop atTop :=
    Real.tendsto_exp_atTop.comp hquadratic
  have hmodel :
      Tendsto
        (fun m : ℕ =>
          Real.exp
            ((delta * pntSqrtLog m - rate) * pntSqrtLog m))
        atTop atTop :=
    hexponential.comp tendsto_pntSqrtLog_atTop
  refine hmodel.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  have hlog_nonneg : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hm)
  have hscale_sq :
      pntSqrtLog m ^ 2 = Real.log (m : ℝ) := by
    simpa only [pntSqrtLog] using Real.sq_sqrt hlog_nonneg
  unfold pntSubpolynomialContourToPowerRatio
  apply congrArg Real.exp
  rw [← hscale_sq]
  ring

/-- The normalized subpolynomial contour factor cannot tend to zero. -/
theorem not_tendsto_pntSubpolynomialContourToPowerRatio_zero
    {delta : ℝ} (hdelta : 0 < delta) (rate : ℝ) :
    ¬ Tendsto
      (pntSubpolynomialContourToPowerRatio delta rate)
      atTop (𝓝 0) := by
  intro hzero
  have hlarge :
      ∀ᶠ m in atTop,
        1 < pntSubpolynomialContourToPowerRatio delta rate m :=
    (pntSubpolynomialContourToPowerRatio_tendsto_atTop hdelta rate).eventually
      (eventually_gt_atTop 1)
  have hsmall :
      ∀ᶠ m in atTop,
        pntSubpolynomialContourToPowerRatio delta rate m < 1 :=
    (tendsto_order.mp hzero).2 1 zero_lt_one
  rcases (hlarge.and hsmall).exists with ⟨m, hlargeM, hsmallM⟩
  linarith

/-- Exact ratio between the Pintz contour-decay factor and the exponential
form of a target-zero relative power amplitude. -/
noncomputable def pntContourKernelToTargetAmplitudeRatio
    (beta rate : ℝ) (m : ℕ) : ℝ :=
  Real.exp (-rate * pntSqrtLog m) /
    Real.exp ((beta - 1) * Real.log (m : ℝ))

/-- For every fixed `beta < 1`, the contour majorant's exponential factor,
after target-amplitude normalization, diverges to infinity. -/
theorem pntContourKernelToTargetAmplitudeRatio_tendsto_atTop
    {beta : ℝ} (hbeta : beta < 1) (rate : ℝ) :
    Tendsto
      (pntContourKernelToTargetAmplitudeRatio beta rate)
      atTop atTop := by
  have hbase :=
    pntSubpolynomialContourToPowerRatio_tendsto_atTop
      (sub_pos.mpr hbeta) rate
  refine hbase.congr' ?_
  filter_upwards with m
  unfold pntContourKernelToTargetAmplitudeRatio
  unfold pntSubpolynomialContourToPowerRatio
  rw [← Real.exp_sub]
  apply congrArg Real.exp
  ring

/-- In particular, the currently available contour-decay factor is not a
target-amplitude-negligible certificate for any fixed `beta < 1`. -/
theorem not_tendsto_pntContourKernelToTargetAmplitudeRatio_zero
    {beta : ℝ} (hbeta : beta < 1) (rate : ℝ) :
    ¬ Tendsto
      (pntContourKernelToTargetAmplitudeRatio beta rate)
      atTop (𝓝 0) := by
  intro hzero
  have hlarge :
      ∀ᶠ m in atTop,
        1 < pntContourKernelToTargetAmplitudeRatio beta rate m :=
    (pntContourKernelToTargetAmplitudeRatio_tendsto_atTop hbeta rate).eventually
      (eventually_gt_atTop 1)
  have hsmall :
      ∀ᶠ m in atTop,
        pntContourKernelToTargetAmplitudeRatio beta rate m < 1 :=
    (tendsto_order.mp hzero).2 1 zero_lt_one
  rcases (hlarge.and hsmall).exists with ⟨m, hlargeM, hsmallM⟩
  linarith

end PrimeNumberTheorem
