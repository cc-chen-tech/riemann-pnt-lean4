import PrimeNumberTheorem.ZeroDensityLayerBudgetTargetAmplitudePowerGap

open Filter Topology

namespace PrimeNumberTheorem

/-!
# Height criterion for target-amplitude contour decay

For a target zero of real part `beta`, write `logHeight m` for the logarithm
of the contour truncation height.  The normalized contour kernel has exponent

`(1 - beta) * log m - logHeight m`.

It therefore tends to zero whenever the opposite exponent

`logHeight m - (1 - beta) * log m`

tends to infinity.  Polynomial heights exhibit the sharp transition
`alpha > 1 - beta`.
-/

/-- Logarithmic excess of a contour height over the target-amplitude power
scale. -/
noncomputable def pntTargetAmplitudeContourLogGap
    (beta : ℝ) (logHeight : ℕ → ℝ) (m : ℕ) : ℝ :=
  logHeight m - (1 - beta) * Real.log (m : ℝ)

/-- A height is admissible for a target real part when its logarithmic excess
over `(1 - beta) * log m` tends to infinity. -/
def IsTargetAmplitudeAdmissibleHeight
    (beta : ℝ) (logHeight : ℕ → ℝ) : Prop :=
  Tendsto
    (pntTargetAmplitudeContourLogGap beta logHeight)
    atTop atTop

/-- Normalized contour-decay factor attached to an abstract logarithmic
height schedule. -/
noncomputable def pntTargetAmplitudeContourRatioAtLogHeight
    (beta : ℝ) (logHeight : ℕ → ℝ) (m : ℕ) : ℝ :=
  Real.exp
    ((1 - beta) * Real.log (m : ℝ) - logHeight m)

/-- The abstract ratio is exactly the quotient of the contour factor
`exp (-logHeight)` by the target relative power amplitude. -/
theorem pntTargetAmplitudeContourRatioAtLogHeight_eq
    (beta : ℝ) (logHeight : ℕ → ℝ) (m : ℕ) :
    pntTargetAmplitudeContourRatioAtLogHeight beta logHeight m =
      Real.exp (-logHeight m) /
        Real.exp ((beta - 1) * Real.log (m : ℝ)) := by
  unfold pntTargetAmplitudeContourRatioAtLogHeight
  rw [← Real.exp_sub]
  apply congrArg Real.exp
  ring

/-- Every admissible logarithmic height produces target-amplitude contour
decay. -/
theorem tendsto_pntTargetAmplitudeContourRatio_zero
    {beta : ℝ} {logHeight : ℕ → ℝ}
    (hadmissible :
      IsTargetAmplitudeAdmissibleHeight beta logHeight) :
    Tendsto
      (pntTargetAmplitudeContourRatioAtLogHeight beta logHeight)
      atTop (𝓝 0) := by
  have hnegative :
      Tendsto
        (fun m : ℕ =>
          -pntTargetAmplitudeContourLogGap beta logHeight m)
        atTop atBot :=
    tendsto_neg_atTop_atBot.comp hadmissible
  have hexp :
      Tendsto
        (fun m : ℕ =>
          Real.exp
            (-pntTargetAmplitudeContourLogGap beta logHeight m))
        atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hnegative
  refine hexp.congr' ?_
  filter_upwards with m
  unfold pntTargetAmplitudeContourRatioAtLogHeight
  unfold pntTargetAmplitudeContourLogGap
  apply congrArg Real.exp
  ring

/-- Logarithm of the polynomial height `T(m) = m ^ alpha`. -/
noncomputable def pntPolynomialLogHeight
    (alpha : ℝ) (m : ℕ) : ℝ :=
  alpha * Real.log (m : ℝ)

/-- A polynomial height is target-amplitude admissible above the critical
exponent `1 - beta`. -/
theorem isTargetAmplitudeAdmissibleHeight_pntPolynomial
    {beta alpha : ℝ} (hcritical : 1 - beta < alpha) :
    IsTargetAmplitudeAdmissibleHeight beta
      (pntPolynomialLogHeight alpha) := by
  have hlog :
      Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hscaled :
      Tendsto
        (fun m : ℕ =>
          (alpha - (1 - beta)) * Real.log (m : ℝ))
        atTop atTop :=
    hlog.const_mul_atTop (sub_pos.mpr hcritical)
  refine hscaled.congr' ?_
  filter_upwards with m
  unfold pntTargetAmplitudeContourLogGap
  unfold pntPolynomialLogHeight
  ring

/-- Above the critical exponent, the polynomial-height contour ratio tends
to zero. -/
theorem tendsto_pntPolynomialContourRatio_zero_of_critical_lt
    {beta alpha : ℝ} (hcritical : 1 - beta < alpha) :
    Tendsto
      (pntTargetAmplitudeContourRatioAtLogHeight beta
        (pntPolynomialLogHeight alpha))
      atTop (𝓝 0) :=
  tendsto_pntTargetAmplitudeContourRatio_zero
    (isTargetAmplitudeAdmissibleHeight_pntPolynomial hcritical)

/-- At the critical polynomial exponent, the normalized contour factor is
identically one. -/
theorem pntPolynomialContourRatio_critical
    (beta : ℝ) :
    pntTargetAmplitudeContourRatioAtLogHeight beta
        (pntPolynomialLogHeight (1 - beta)) =
      fun _ : ℕ => 1 := by
  funext m
  simp [pntTargetAmplitudeContourRatioAtLogHeight,
    pntPolynomialLogHeight]

/-- The critical polynomial height does not give target-amplitude decay. -/
theorem not_tendsto_pntPolynomialContourRatio_critical_zero
    (beta : ℝ) :
    ¬ Tendsto
      (pntTargetAmplitudeContourRatioAtLogHeight beta
        (pntPolynomialLogHeight (1 - beta)))
      atTop (𝓝 0) := by
  rw [pntPolynomialContourRatio_critical]
  intro hzero
  have hone :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  exact zero_ne_one (tendsto_nhds_unique hzero hone)

/-- Below the critical polynomial exponent, the normalized contour factor
diverges. -/
theorem tendsto_pntPolynomialContourRatio_atTop_of_lt_critical
    {beta alpha : ℝ} (hcritical : alpha < 1 - beta) :
    Tendsto
      (pntTargetAmplitudeContourRatioAtLogHeight beta
        (pntPolynomialLogHeight alpha))
      atTop atTop := by
  have hlog :
      Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hscaled :
      Tendsto
        (fun m : ℕ =>
          ((1 - beta) - alpha) * Real.log (m : ℝ))
        atTop atTop :=
    hlog.const_mul_atTop (sub_pos.mpr hcritical)
  have hexp :=
    Real.tendsto_exp_atTop.comp hscaled
  refine hexp.congr' ?_
  filter_upwards with m
  unfold pntTargetAmplitudeContourRatioAtLogHeight
  unfold pntPolynomialLogHeight
  apply congrArg Real.exp
  ring

/-- Exact polynomial-height transition: target-amplitude contour decay holds
if and only if `alpha > 1 - beta`. -/
theorem tendsto_pntPolynomialContourRatio_zero_iff
    (beta alpha : ℝ) :
    Tendsto
        (pntTargetAmplitudeContourRatioAtLogHeight beta
          (pntPolynomialLogHeight alpha))
        atTop (𝓝 0) ↔
      1 - beta < alpha := by
  constructor
  · intro hzero
    by_contra hnot
    have hle : alpha ≤ 1 - beta := le_of_not_gt hnot
    rcases hle.eq_or_lt with heq | hlt
    · subst alpha
      exact
        not_tendsto_pntPolynomialContourRatio_critical_zero beta hzero
    · have hinfty :=
        tendsto_pntPolynomialContourRatio_atTop_of_lt_critical hlt
      have hlarge :
          ∀ᶠ m in atTop,
            1 <
              pntTargetAmplitudeContourRatioAtLogHeight beta
                (pntPolynomialLogHeight alpha) m :=
        hinfty.eventually (eventually_gt_atTop 1)
      have hsmall :
          ∀ᶠ m in atTop,
            pntTargetAmplitudeContourRatioAtLogHeight beta
                (pntPolynomialLogHeight alpha) m < 1 :=
        (tendsto_order.mp hzero).2 1 zero_lt_one
      rcases (hlarge.and hsmall).exists with
        ⟨m, hlargeM, hsmallM⟩
      linarith
  · exact tendsto_pntPolynomialContourRatio_zero_of_critical_lt

end PrimeNumberTheorem
