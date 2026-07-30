import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicCarlsonGapFamily

/-!
# Domination of geometric Carlson gaps by the smallest gap

The exact balanced exponent need not be compared at two different gaps.
Instead, the established estimate

`balancedExponent(g) <= -g / 2`

gives a coarse ratio.  If `delta <= g`, both the quadratic coefficient
`g⁻²` and the exponential factor `m^(-g/2)` are bounded by their values at
`delta`.  This closes the heterogeneous-ratio comparison needed to sum a
dynamic geometric family of actual zeta strips.
-/

namespace PrimeNumberTheorem

open Filter Topology
open scoped BigOperators

noncomputable section

/-- Common one-layer majorant at the smallest real-part gap. -/
noncomputable def carlsonDynamicGapCoarseLogPowerRatio
    (C : ℝ) (delta : ℕ → ℝ) (m : ℕ) : ℝ :=
  Real.exp
    (Real.log C +
      2 * Real.log (delta m)⁻¹ +
      4 * Real.log (Real.log (m : ℝ)) -
      delta m / 2 * Real.log (m : ℝ))

/-- The common coarse ratio after paying for all dynamic layers. -/
noncomputable def carlsonDynamicGapLayeredCoarseLogPowerRatio
    (C : ℝ) (delta : ℕ → ℝ) (layers : ℕ → ℕ) (m : ℕ) : ℝ :=
  Real.exp
    (Real.log C +
      2 * Real.log (delta m)⁻¹ +
      4 * Real.log (Real.log (m : ℝ)) +
      carlsonDynamicLayerCountLogCost layers m -
      delta m / 2 * Real.log (m : ℝ))

theorem carlsonDynamicGapLayeredCoarseLogPowerRatio_eq
    (C : ℝ) (delta : ℕ → ℝ) (layers : ℕ → ℕ) (m : ℕ) :
    carlsonDynamicGapLayeredCoarseLogPowerRatio
        C delta layers m =
      ((layers m : ℝ) + 1) *
        carlsonDynamicGapCoarseLogPowerRatio C delta m := by
  have hlayersPos : 0 < (layers m : ℝ) + 1 := by positivity
  unfold carlsonDynamicGapLayeredCoarseLogPowerRatio
    carlsonDynamicGapCoarseLogPowerRatio
    carlsonDynamicLayerCountLogCost
  rw [show
      Real.log C + 2 * Real.log (delta m)⁻¹ +
            4 * Real.log (Real.log (m : ℝ)) +
            Real.log ((layers m : ℝ) + 1) -
            delta m / 2 * Real.log (m : ℝ) =
          Real.log ((layers m : ℝ) + 1) +
            (Real.log C + 2 * Real.log (delta m)⁻¹ +
              4 * Real.log (Real.log (m : ℝ)) -
              delta m / 2 * Real.log (m : ℝ)) by ring]
  rw [Real.exp_add, Real.exp_log hlayersPos]

/-- The complete layer-count margin is exactly what makes the common coarse
majorant vanish. -/
theorem tendsto_carlsonDynamicGapLayeredCoarseLogPowerRatio_zero
    {C : ℝ} {delta : ℕ → ℝ} {layers : ℕ → ℕ}
    (hgap :
      IsCarlsonMovingQuadraticLogPowerLayerCountGap delta layers) :
    Tendsto
      (carlsonDynamicGapLayeredCoarseLogPowerRatio C delta layers)
      atTop (nhds 0) := by
  have hnegative :
      Tendsto
        (fun m =>
          -(delta m / 2 * Real.log (m : ℝ) -
              2 * Real.log (delta m)⁻¹ -
              4 * Real.log (Real.log (m : ℝ)) -
              carlsonDynamicLayerCountLogCost layers m))
        atTop atBot :=
    tendsto_neg_atTop_atBot.comp hgap
  have hshift :
      Tendsto
        (fun m =>
          Real.log C +
            -(delta m / 2 * Real.log (m : ℝ) -
              2 * Real.log (delta m)⁻¹ -
              4 * Real.log (Real.log (m : ℝ)) -
              carlsonDynamicLayerCountLogCost layers m))
        atTop atBot :=
    tendsto_atBot_add_const_left atTop (Real.log C) hnegative
  have hexp :=
    Real.tendsto_exp_atBot.comp hshift
  apply hexp.congr'
  filter_upwards with m
  simp only [Function.comp_apply]
  unfold carlsonDynamicGapLayeredCoarseLogPowerRatio
  congr 1
  ring

/-- An exact balanced ratio at a larger gap is bounded by the coarse ratio at
the smaller gap. -/
theorem carlsonMovingBalancedLogPowerRatio_le_coarse_of_gap_le
    {alpha C : ℝ} {delta gap : ℕ → ℝ} {m : ℕ}
    (hm : 1 ≤ m)
    (hdelta : 0 < delta m)
    (hgapLower : delta m ≤ gap m)
    (hgapUpper : gap m ≤ 1 / 2)
    (halpha : 0 ≤ alpha)
    (hsmall : 128 * alpha * gap m ≤ 1) :
    carlsonMovingBalancedCoefficientRatio alpha gap
        (carlsonMovingQuadraticLogPowerEnvelope C gap) m ≤
      carlsonDynamicGapCoarseLogPowerRatio C delta m := by
  have hgapPos : 0 < gap m := hdelta.trans_le hgapLower
  have hinv :
      (gap m)⁻¹ ≤ (delta m)⁻¹ :=
    inv_anti₀ hdelta hgapLower
  have hlogInv :
      Real.log (gap m)⁻¹ ≤ Real.log (delta m)⁻¹ :=
    Real.log_le_log (inv_pos.mpr hgapPos) hinv
  have hlogm : 0 ≤ Real.log (m : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast hm
  have hexponent :=
    carlsonTwoHeightBalancedExponent_movingStrip_le_neg_half
      hgapPos hgapUpper halpha hsmall
  have hexponentScaled :=
    mul_le_mul_of_nonneg_right hexponent hlogm
  have hgapScaled :
      (-gap m / 2) * Real.log (m : ℝ) ≤
        (-delta m / 2) * Real.log (m : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) hlogm
  unfold carlsonMovingBalancedCoefficientRatio
    carlsonMovingQuadraticLogPowerEnvelope
    carlsonDynamicGapCoarseLogPowerRatio
  rw [Real.exp_le_exp]
  linarith

/-- Summing masses bounded by the common coarse ratio costs exactly the
dynamic layer factor. -/
theorem carlsonDynamicFiniteLayerMass_le_layeredCoarseLogPowerRatio
    {C : ℝ} {delta : ℕ → ℝ} {layers : ℕ → ℕ}
    {mass : (m : ℕ) → Fin (layers m) → ℝ} {m : ℕ}
    (hmass :
      ∀ i,
        mass m i ≤
          carlsonDynamicGapCoarseLogPowerRatio C delta m) :
    carlsonDynamicFiniteLayerMass layers mass m ≤
      carlsonDynamicGapLayeredCoarseLogPowerRatio
        C delta layers m := by
  let ratio := carlsonDynamicGapCoarseLogPowerRatio C delta m
  have hratio : 0 ≤ ratio := by
    dsimp [ratio, carlsonDynamicGapCoarseLogPowerRatio]
    exact (Real.exp_pos _).le
  calc
    carlsonDynamicFiniteLayerMass layers mass m
        ≤ ∑ _i : Fin (layers m), ratio := by
          unfold carlsonDynamicFiniteLayerMass
          exact Finset.sum_le_sum fun i _ => hmass i
    _ = (layers m : ℝ) * ratio := by simp
    _ ≤ ((layers m : ℝ) + 1) * ratio := by
      exact mul_le_mul_of_nonneg_right
        (by linarith : (layers m : ℝ) ≤ (layers m : ℝ) + 1) hratio
    _ = carlsonDynamicGapLayeredCoarseLogPowerRatio
          C delta layers m := by
      rw [carlsonDynamicGapLayeredCoarseLogPowerRatio_eq]

/-- Pointwise Carlson counts now imply decay of the complete actual dynamic
gap family without a separate ratio-domination hypothesis. -/
theorem tendsto_actualDynamicCarlsonGapFamilyMass_zero_of_minGap
    {A alpha : ℝ} {delta : ℕ → ℝ}
    {layers : ℕ → ℕ} {gap : ℕ → ℕ → ℝ}
    (hA : 0 ≤ A) (halpha : 0 < alpha)
    (hdelta : ∀ᶠ m : ℕ in atTop, 0 < delta m)
    (hlayerGap :
      ∀ᶠ m : ℕ in atTop, ∀ i : Fin (layers m),
        delta m ≤ gap m i.1 ∧
          gap m i.1 ≤ 1 / 8 ∧
          128 * alpha * gap m i.1 ≤ 1)
    (hmargin :
      IsCarlsonMovingQuadraticLogPowerLayerCountGap delta layers)
    (hcount :
      IsActualDynamicCarlsonGapFamilyCountCertificate
        A alpha layers gap) :
    Tendsto
      (actualDynamicCarlsonGapFamilyMass alpha layers gap)
      atTop (nhds 0) := by
  let C := actualMovingCarlsonBalancedPositiveConstant A alpha
  have hgapBasic :
      ∀ᶠ m : ℕ in atTop, ∀ i : Fin (layers m),
        0 < gap m i.1 ∧ gap m i.1 ≤ 1 / 8 := by
    filter_upwards [hdelta, hlayerGap] with m hdm hgm
    intro i
    exact ⟨hdm.trans_le (hgm i).1, (hgm i).2.1⟩
  have hown :=
    eventually_actualDynamicCarlsonGapLayerMass_le_ownRatio
      hA halpha hgapBasic hcount
  have hfamily :
      ∀ᶠ m : ℕ in atTop,
        actualDynamicCarlsonGapFamilyMass alpha layers gap m ≤
          carlsonDynamicGapLayeredCoarseLogPowerRatio
            C delta layers m := by
    filter_upwards
      [eventually_ge_atTop (1 : ℕ), hdelta, hlayerGap, hown] with
        m hm hdm hgm hmass
    apply carlsonDynamicFiniteLayerMass_le_layeredCoarseLogPowerRatio
    intro i
    exact (hmass i).trans
      (carlsonMovingBalancedLogPowerRatio_le_coarse_of_gap_le
        hm hdm (hgm i).1 ((hgm i).2.1.trans (by norm_num))
          halpha.le (hgm i).2.2)
  refine squeeze_zero' ?_ hfamily
    (tendsto_carlsonDynamicGapLayeredCoarseLogPowerRatio_zero hmargin)
  filter_upwards with m
  unfold actualDynamicCarlsonGapFamilyMass
    carlsonDynamicFiniteLayerMass
  exact Finset.sum_nonneg fun i _ =>
    actualMovingCarlsonStripMass_nonneg alpha
      (actualDynamicCarlsonGapSchedule gap i.1) m

/-- The same unconditional ratio comparison for the actual disjoint strip
union. -/
theorem tendsto_actualDynamicCarlsonGapStripUnion_mass_zero_of_minGap
    {A alpha : ℝ} {delta : ℕ → ℝ}
    {layers : ℕ → ℕ} {gap : ℕ → ℕ → ℝ}
    (hA : 0 ≤ A) (halpha : 0 < alpha)
    (hdelta : ∀ᶠ m : ℕ in atTop, 0 < delta m)
    (hlayerGap :
      ∀ᶠ m : ℕ in atTop, ∀ i : Fin (layers m),
        delta m ≤ gap m i.1 ∧
          gap m i.1 ≤ 1 / 8 ∧
          128 * alpha * gap m i.1 ≤ 1)
    (hmargin :
      IsCarlsonMovingQuadraticLogPowerLayerCountGap delta layers)
    (hcount :
      IsActualDynamicCarlsonGapFamilyCountCertificate
        A alpha layers gap)
    (hseparated : CarlsonDynamicGapFamilySeparated layers gap) :
    Tendsto
      (fun m =>
        ∑ rho ∈ actualDynamicCarlsonGapStripUnion
            alpha layers gap m,
          ‖pntRelativeZeroContribution (m : ℝ) rho‖)
      atTop (nhds 0) := by
  apply
    (tendsto_actualDynamicCarlsonGapFamilyMass_zero_of_minGap
      hA halpha hdelta hlayerGap hmargin hcount).congr'
  filter_upwards with m
  exact
    (actualDynamicCarlsonGapStripUnion_mass_eq_familyMass
      hseparated).symm

end

end PrimeNumberTheorem
