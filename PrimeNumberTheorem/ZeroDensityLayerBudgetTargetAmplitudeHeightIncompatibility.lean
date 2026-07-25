import PrimeNumberTheorem.ZeroForcingUnifiedTransfer

open Filter Topology

namespace PrimeNumberTheorem

/-!
# Incompatibility of one subpolynomial height with target-amplitude decay

The current Pintz--Carlson upper transfer uses a subpolynomial hard truncation
height.  For a fixed target real part `beta < 1`, target-amplitude contour
decay requires logarithmic height exceeding `(1 - beta) * log m` by a
quantity tending to infinity.

These requirements are incompatible for one hard truncation height.  This
formalizes the need for a distinct lower-bound height, a two-height
decomposition, or a smoothed explicit formula.
-/

/-- An upper-bound logarithmic height is subpolynomial when it is eventually
bounded by `epsilon * log m` for every positive `epsilon`. -/
def IsPNTSubpolynomialLogHeight
    (logHeight : ℕ → ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∀ᶠ m in atTop,
      logHeight m ≤ epsilon * Real.log (m : ℝ)

/-- A subpolynomial logarithmic height falls below every fixed positive target
power scale by an amount tending to minus infinity. -/
theorem tendsto_targetAmplitudeContourLogGap_atBot_of_subpolynomial
    {beta : ℝ} (hbeta : beta < 1)
    {logHeight : ℕ → ℝ}
    (hsubpolynomial : IsPNTSubpolynomialLogHeight logHeight) :
    Tendsto
      (pntTargetAmplitudeContourLogGap beta logHeight)
      atTop atBot := by
  let delta : ℝ := 1 - beta
  have hdelta : 0 < delta := sub_pos.mpr hbeta
  have hhalfDelta : 0 < delta / 2 := half_pos hdelta
  have hheight :
      ∀ᶠ m in atTop,
        logHeight m ≤
          (delta / 2) * Real.log (m : ℝ) :=
    hsubpolynomial (delta / 2) hhalfDelta
  have hlog :
      Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hnegativeLog :
      Tendsto (fun m : ℕ => -Real.log (m : ℝ)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hlog
  have hmodel :
      Tendsto
        (fun m : ℕ =>
          (delta / 2) * (-Real.log (m : ℝ)))
        atTop atBot :=
    hnegativeLog.const_mul_atBot hhalfDelta
  rw [tendsto_atBot]
  intro b
  have hmodelBound :=
    hmodel.eventually (eventually_le_atBot b)
  filter_upwards [hheight, hmodelBound] with m hheightM hmodelM
  unfold pntTargetAmplitudeContourLogGap
  have hgapBound :
      logHeight m - (1 - beta) * Real.log (m : ℝ) ≤
        (delta / 2) * (-Real.log (m : ℝ)) := by
    dsimp [delta] at hheightM ⊢
    linarith
  exact hgapBound.trans hmodelM

/-- No subpolynomial upper-bound height is target-amplitude admissible for a
fixed `beta < 1`. -/
theorem not_isTargetAmplitudeAdmissibleHeight_of_subpolynomial
    {beta : ℝ} (hbeta : beta < 1)
    {logHeight : ℕ → ℝ}
    (hsubpolynomial : IsPNTSubpolynomialLogHeight logHeight) :
    ¬ IsTargetAmplitudeAdmissibleHeight beta logHeight := by
  intro hadmissible
  have hminus :=
    tendsto_targetAmplitudeContourLogGap_atBot_of_subpolynomial
      hbeta hsubpolynomial
  have hpositive :
      ∀ᶠ m in atTop,
        0 < pntTargetAmplitudeContourLogGap beta logHeight m :=
    hadmissible.eventually (eventually_gt_atTop 0)
  have hnonpositive :
      ∀ᶠ m in atTop,
        pntTargetAmplitudeContourLogGap beta logHeight m ≤ 0 :=
    hminus.eventually (eventually_le_atBot 0)
  rcases (hpositive.and hnonpositive).exists with
    ⟨m, hpositiveM, hnonpositiveM⟩
  linarith

/-- For a subpolynomial height, the normalized contour factor diverges for
every fixed target real part below one. -/
theorem tendsto_targetAmplitudeContourRatio_atTop_of_subpolynomial
    {beta : ℝ} (hbeta : beta < 1)
    {logHeight : ℕ → ℝ}
    (hsubpolynomial : IsPNTSubpolynomialLogHeight logHeight) :
    Tendsto
      (pntTargetAmplitudeContourRatioAtLogHeight beta logHeight)
      atTop atTop := by
  have hgap :=
    tendsto_targetAmplitudeContourLogGap_atBot_of_subpolynomial
      hbeta hsubpolynomial
  have hnegative :
      Tendsto
        (fun m : ℕ =>
          -pntTargetAmplitudeContourLogGap beta logHeight m)
        atTop atTop :=
    tendsto_neg_atBot_atTop.comp hgap
  have hexp :
      Tendsto
        (fun m : ℕ =>
          Real.exp
            (-pntTargetAmplitudeContourLogGap beta logHeight m))
        atTop atTop :=
    Real.tendsto_exp_atTop.comp hnegative
  refine hexp.congr' ?_
  filter_upwards with m
  unfold pntTargetAmplitudeContourRatioAtLogHeight
  unfold pntTargetAmplitudeContourLogGap
  apply congrArg Real.exp
  ring

/-- Logarithm of the current fixed-rate Pintz height. -/
noncomputable def pntSqrtLogHeight
    (rate : ℝ) (m : ℕ) : ℝ :=
  rate * pntSqrtLog m

/-- Every nonnegative fixed multiple of `sqrt (log m)` is subpolynomial. -/
theorem isPNTSubpolynomialLogHeight_pntSqrtLog
    {rate : ℝ} (hrate : 0 ≤ rate) :
    IsPNTSubpolynomialLogHeight (pntSqrtLogHeight rate) := by
  intro epsilon hepsilon
  have hscale :=
    tendsto_pntSqrtLog_atTop.eventually
      (eventually_ge_atTop (rate / epsilon))
  filter_upwards [hscale, eventually_ge_atTop (1 : ℕ)] with
      m hscaleM hm
  have hlog_nonneg : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hm)
  have hsqrt_nonneg : 0 ≤ pntSqrtLog m :=
    Real.sqrt_nonneg _
  have hscale_sq :
      pntSqrtLog m ^ 2 = Real.log (m : ℝ) := by
    simpa only [pntSqrtLog] using Real.sq_sqrt hlog_nonneg
  have hrate_le :
      rate ≤ epsilon * pntSqrtLog m := by
    have := (div_le_iff₀ hepsilon).mp hscaleM
    nlinarith
  unfold pntSqrtLogHeight
  nlinarith

/-- The current fixed-rate Pintz height is therefore incompatible with every
fixed target real part `beta < 1`. -/
theorem not_isTargetAmplitudeAdmissibleHeight_pntSqrtLog
    {beta rate : ℝ} (hbeta : beta < 1) (hrate : 0 ≤ rate) :
    ¬ IsTargetAmplitudeAdmissibleHeight beta
      (pntSqrtLogHeight rate) :=
  not_isTargetAmplitudeAdmissibleHeight_of_subpolynomial
    hbeta (isPNTSubpolynomialLogHeight_pntSqrtLog hrate)

end PrimeNumberTheorem
