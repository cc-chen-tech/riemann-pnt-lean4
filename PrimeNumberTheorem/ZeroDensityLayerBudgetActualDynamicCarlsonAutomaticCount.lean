import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonDynamicGapDomination

/-!
# Uniform pointwise Carlson counts for a dynamic strip family

Carlson's public contour certificate chooses `A`, `C₁`, and `C₂` before
quantifying over `sigma` and `T`.  Consequently the same constants apply to
every member of a height-dependent finite real-part cover.  This is the
quantifier order that a dynamic geometric layering requires.
-/

namespace PrimeNumberTheorem

open Filter Topology

noncomputable section

/-- Explicit Carlson height conditions at the balanced intermediate height
and the common outer height, for every active dynamic layer. -/
def ActualDynamicCarlsonGapFamilyHeightConditions
    (C₁ C₂ alpha : ℝ) (layers : ℕ → ℕ)
    (gap : ℕ → ℕ → ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i : Fin (layers m),
    let delta := actualDynamicCarlsonGapSchedule gap i.1
    CarlsonPointwiseHeightConditions C₁ C₂ (1 - 2 * delta m)
        (carlsonPolynomialHeight
          (carlsonMovingBalancedCut alpha delta m) (m : ℝ)) ∧
      CarlsonPointwiseHeightConditions C₁ C₂ (1 - 2 * delta m)
        (carlsonPolynomialHeight alpha (m : ℝ))

/-- One set of Carlson constants supplies both actual counts in every active
dynamic layer. -/
theorem exists_actualDynamicCarlsonGapFamilyCountCertificate
    {alpha : ℝ} {layers : ℕ → ℕ} {gap : ℕ → ℕ → ℝ}
    (hgap :
      ∀ᶠ m : ℕ in atTop, ∀ i : Fin (layers m),
        0 < gap m i.1 ∧ gap m i.1 < 1 / 4) :
    ∃ A C₁ C₂ : ℝ,
      0 ≤ A ∧ 1 ≤ C₁ ∧ 1 ≤ C₂ ∧
        (ActualDynamicCarlsonGapFamilyHeightConditions
            C₁ C₂ alpha layers gap →
          IsActualDynamicCarlsonGapFamilyCountCertificate
            A alpha layers gap) := by
  obtain ⟨A, C₁, C₂, hA, hC₁, hC₂, hpointwise⟩ :=
    exists_carlson_moving_twoHeight_pointwise_count_certificate
  refine ⟨A, C₁, C₂, hA, hC₁, hC₂, ?_⟩
  intro hconditions
  filter_upwards [hgap, hconditions] with m hgm hTm
  intro i
  let delta := actualDynamicCarlsonGapSchedule gap i.1
  have hd : 0 < delta m ∧ delta m < 1 / 4 := by
    simpa [delta, actualDynamicCarlsonGapSchedule] using hgm i
  have hTi := hTm i
  exact hpointwise hd.1 hd.2 hTi.1 hTi.2

/-- Fully automatic actual dynamic-family decay from explicit height
conditions, minimum-gap control, and the complete logarithmic margin. -/
theorem exists_constants_tendsto_actualDynamicCarlsonGapFamilyMass_zero
    {alpha : ℝ} {delta : ℕ → ℝ}
    {layers : ℕ → ℕ} {gap : ℕ → ℕ → ℝ}
    (halpha : 0 < alpha)
    (hdelta : ∀ᶠ m : ℕ in atTop, 0 < delta m)
    (hlayerGap :
      ∀ᶠ m : ℕ in atTop, ∀ i : Fin (layers m),
        delta m ≤ gap m i.1 ∧
          gap m i.1 ≤ 1 / 8 ∧
          128 * alpha * gap m i.1 ≤ 1)
    (hmargin :
      IsCarlsonMovingQuadraticLogPowerLayerCountGap delta layers) :
    ∃ A C₁ C₂ : ℝ,
      0 ≤ A ∧ 1 ≤ C₁ ∧ 1 ≤ C₂ ∧
        (ActualDynamicCarlsonGapFamilyHeightConditions
            C₁ C₂ alpha layers gap →
          Tendsto
            (actualDynamicCarlsonGapFamilyMass alpha layers gap)
            atTop (nhds 0)) := by
  have hgapQuarter :
      ∀ᶠ m : ℕ in atTop, ∀ i : Fin (layers m),
        0 < gap m i.1 ∧ gap m i.1 < 1 / 4 := by
    filter_upwards [hdelta, hlayerGap] with m hdm hgm
    intro i
    exact
      ⟨hdm.trans_le (hgm i).1,
        (hgm i).2.1.trans_lt (by norm_num)⟩
  obtain ⟨A, C₁, C₂, hA, hC₁, hC₂, hcertificate⟩ :=
    exists_actualDynamicCarlsonGapFamilyCountCertificate hgapQuarter
  refine ⟨A, C₁, C₂, hA, hC₁, hC₂, ?_⟩
  intro hheight
  exact
    tendsto_actualDynamicCarlsonGapFamilyMass_zero_of_minGap
      hA halpha hdelta hlayerGap hmargin
        (hcertificate hheight)

/-- Union form of the automatic dynamic Carlson transfer. -/
theorem exists_constants_tendsto_actualDynamicCarlsonGapStripUnion_mass_zero
    {alpha : ℝ} {delta : ℕ → ℝ}
    {layers : ℕ → ℕ} {gap : ℕ → ℕ → ℝ}
    (halpha : 0 < alpha)
    (hdelta : ∀ᶠ m : ℕ in atTop, 0 < delta m)
    (hlayerGap :
      ∀ᶠ m : ℕ in atTop, ∀ i : Fin (layers m),
        delta m ≤ gap m i.1 ∧
          gap m i.1 ≤ 1 / 8 ∧
          128 * alpha * gap m i.1 ≤ 1)
    (hmargin :
      IsCarlsonMovingQuadraticLogPowerLayerCountGap delta layers)
    (hseparated : CarlsonDynamicGapFamilySeparated layers gap) :
    ∃ A C₁ C₂ : ℝ,
      0 ≤ A ∧ 1 ≤ C₁ ∧ 1 ≤ C₂ ∧
        (ActualDynamicCarlsonGapFamilyHeightConditions
            C₁ C₂ alpha layers gap →
          Tendsto
            (fun m =>
              ∑ rho ∈ actualDynamicCarlsonGapStripUnion
                  alpha layers gap m,
                ‖pntRelativeZeroContribution (m : ℝ) rho‖)
            atTop (nhds 0)) := by
  obtain ⟨A, C₁, C₂, hA, hC₁, hC₂, hfamily⟩ :=
    exists_constants_tendsto_actualDynamicCarlsonGapFamilyMass_zero
      halpha hdelta hlayerGap hmargin
  refine ⟨A, C₁, C₂, hA, hC₁, hC₂, ?_⟩
  intro hheight
  apply (hfamily hheight).congr'
  filter_upwards with m
  exact
    (actualDynamicCarlsonGapStripUnion_mass_eq_familyMass
      hseparated).symm

end

end PrimeNumberTheorem
