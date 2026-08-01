import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTHybridCofinalOutsideClusterCap

/-!
# Moving real-part gaps and the density-height barrier

Suppose an outside-cluster layer lies below `beta - gap(m)`, while its
multiplicity mass grows like `exp (q * logHeight(m))`. After normalization
by the target `beta`-power, the logarithmic decay budget is

`gap(m) * log m - q * logHeight(m)`.

This module proves both the corresponding decay criterion and a no-go
theorem: if the contour height is target-amplitude admissible and `q > 0`,
then this budget forces `gap(m)` to have an eventual fixed positive lower
bound. A moving gap tending to zero cannot close the transfer when one first
aggregates by a positive-exponent density bound.
-/

open Filter Topology

namespace PrimeNumberTheorem

/-- Logarithmic decay budget after combining a moving real-part gap with a
`q`-power density cost in the truncation height. -/
noncomputable def pntMovingDensityLogMargin
    (q : ℝ) (logHeight : ℕ → ℝ) (gap : ℕ → ℝ) (m : ℕ) : ℝ :=
  gap m * Real.log (m : ℝ) - q * logHeight m

/-- The moving gap absorbs the density cost when its logarithmic margin
tends to infinity. -/
def IsMovingDensityGapAdmissible
    (q : ℝ) (logHeight : ℕ → ℝ) (gap : ℕ → ℝ) : Prop :=
  Tendsto (pntMovingDensityLogMargin q logHeight gap) atTop atTop

/-- Exponential normalized majorant corresponding to the moving density
margin. -/
noncomputable def pntMovingDensityNormalizedRatio
    (q : ℝ) (logHeight : ℕ → ℝ) (gap : ℕ → ℝ) (m : ℕ) : ℝ :=
  Real.exp
    (q * logHeight m - gap m * Real.log (m : ℝ))

/-- A moving density gap with divergent positive log margin makes the
normalized aggregate majorant tend to zero. -/
theorem tendsto_pntMovingDensityNormalizedRatio_zero
    {q : ℝ} {logHeight gap : ℕ → ℝ}
    (hadmissible :
      IsMovingDensityGapAdmissible q logHeight gap) :
    Tendsto
      (pntMovingDensityNormalizedRatio q logHeight gap)
      atTop (𝓝 0) := by
  have hnegative :
      Tendsto
        (fun m : ℕ =>
          -pntMovingDensityLogMargin q logHeight gap m)
        atTop atBot :=
    tendsto_neg_atTop_atBot.comp hadmissible
  have hexp :
      Tendsto
        (fun m : ℕ =>
          Real.exp
            (-pntMovingDensityLogMargin q logHeight gap m))
        atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hnegative
  refine hexp.congr' ?_
  filter_upwards with m
  unfold pntMovingDensityNormalizedRatio
    pntMovingDensityLogMargin
  apply congrArg Real.exp
  ring

/--
Combining an admissible target-amplitude contour height with a positive
density exponent forces an eventual fixed real-part gap:

`q * (1 - beta) < gap(m)`.

Hence the moving-gap formulation does not weaken the fixed-gap requirement
when the zero layer is estimated by `height^q` before normalization.
-/
theorem eventually_fixedGap_of_contour_and_movingDensity
    {beta q : ℝ} {logHeight gap : ℕ → ℝ}
    (hbeta : beta < 1)
    (hq : 0 < q)
    (hcontour :
      IsTargetAmplitudeAdmissibleHeight beta logHeight)
    (hdensity :
      IsMovingDensityGapAdmissible q logHeight gap) :
    ∀ᶠ m in atTop, q * (1 - beta) < gap m := by
  have hcontourPositive :
      ∀ᶠ m in atTop,
        0 < pntTargetAmplitudeContourLogGap beta logHeight m :=
    hcontour.eventually (eventually_gt_atTop 0)
  have hdensityPositive :
      ∀ᶠ m in atTop,
        0 < pntMovingDensityLogMargin q logHeight gap m :=
    hdensity.eventually (eventually_gt_atTop 0)
  filter_upwards
      [hcontourPositive, hdensityPositive,
        eventually_ge_atTop (2 : ℕ)] with
      m hcontourM hdensityM hm
  have hlog : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast hm)
  have hheight :
      (1 - beta) * Real.log (m : ℝ) < logHeight m := by
    unfold pntTargetAmplitudeContourLogGap at hcontourM
    linarith
  have haggregate :
      q * logHeight m < gap m * Real.log (m : ℝ) := by
    unfold pntMovingDensityLogMargin at hdensityM
    linarith
  have hscaled :
      q * ((1 - beta) * Real.log (m : ℝ)) <
        q * logHeight m :=
    mul_lt_mul_of_pos_left hheight hq
  have hmul :
      (q * (1 - beta)) * Real.log (m : ℝ) <
        gap m * Real.log (m : ℝ) := by
    calc
      (q * (1 - beta)) * Real.log (m : ℝ) =
          q * ((1 - beta) * Real.log (m : ℝ)) := by ring
      _ < q * logHeight m := hscaled
      _ < gap m * Real.log (m : ℝ) := haggregate
  exact lt_of_mul_lt_mul_right hmul hlog.le

/-- In particular, a moving real-part gap tending to zero is incompatible
with simultaneous contour admissibility and a positive-exponent density
aggregate. -/
theorem not_movingDensityGap_tendsto_zero_of_contour
    {beta q : ℝ} {logHeight gap : ℕ → ℝ}
    (hbeta : beta < 1)
    (hq : 0 < q)
    (hcontour :
      IsTargetAmplitudeAdmissibleHeight beta logHeight)
    (hdensity :
      IsMovingDensityGapAdmissible q logHeight gap) :
    ¬ Tendsto gap atTop (𝓝 0) := by
  intro hgap
  have hfixed :=
    eventually_fixedGap_of_contour_and_movingDensity
      hbeta hq hcontour hdensity
  have hconstant : 0 < q * (1 - beta) :=
    mul_pos hq (sub_pos.mpr hbeta)
  have hsmall :
      ∀ᶠ m in atTop, gap m < q * (1 - beta) :=
    (tendsto_order.mp hgap).2
      (q * (1 - beta)) hconstant
  rcases (hfixed.and hsmall).exists with ⟨m, hlargeM, hsmallM⟩
  exact lt_asymm hlargeM hsmallM

end PrimeNumberTheorem
