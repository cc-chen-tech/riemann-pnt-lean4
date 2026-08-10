import PrimeNumberTheorem.ZeroDensityLayerBudgetActualMovingCarlsonAutomaticDecay
import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonActualOrderedBalancedStrips
import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonDynamicLayerCount

/-!
# Dynamic families of actual moving Carlson strips

This module lifts the honest one-strip pointwise Carlson chain to a number of
real-part strips depending on the PNT scale.  Strip `j` has gap `g_j(m)` and
therefore covers

`1 - 2 g_j(m) < Re rho <= 1 - g_j(m)`.

The family is genuinely dependent: its index type is `Fin (layers m)`.
Pairwise factor-two separation makes these strips disjoint.  The actual zeta
kernel mass in every strip is bounded from the two pointwise Carlson counts,
and the dynamic layer-count theorem then sums the family.

The final transfer exposes, rather than hides, the remaining geometric
comparison: every individual gap ratio must be dominated by the common ratio
at the smallest boundary gap.
-/

namespace PrimeNumberTheorem

open Filter Topology
open scoped BigOperators

noncomputable section

def actualDynamicCarlsonGapSchedule
    (gap : ℕ → ℕ → ℝ) (j : ℕ) : ℕ → ℝ :=
  fun m => gap m j

/-- Actual multiplicity-weighted zeta mass in dynamic layer `i`. -/
noncomputable def actualDynamicCarlsonGapLayerMass
    (alpha : ℝ) (layers : ℕ → ℕ) (gap : ℕ → ℕ → ℝ)
    (m : ℕ) (i : Fin (layers m)) : ℝ :=
  actualMovingCarlsonStripMass alpha
    (actualDynamicCarlsonGapSchedule gap i.1) m

/-- Sum of all actual zeta layer masses at scale `m`. -/
noncomputable def actualDynamicCarlsonGapFamilyMass
    (alpha : ℝ) (layers : ℕ → ℕ) (gap : ℕ → ℕ → ℝ)
    (m : ℕ) : ℝ :=
  carlsonDynamicFiniteLayerMass layers
    (actualDynamicCarlsonGapLayerMass alpha layers gap) m

/-- Actual finite union represented by the dynamic gap family. -/
noncomputable def actualDynamicCarlsonGapStripUnion
    (alpha : ℝ) (layers : ℕ → ℕ) (gap : ℕ → ℕ → ℝ)
    (m : ℕ) : Finset ℂ :=
  actualPositiveCarlsonFiniteStripUnion
    (fun i : Fin (layers m) => 1 - 2 * gap m i.1)
    (fun i : Fin (layers m) => 1 - gap m i.1)
    (carlsonPolynomialHeight alpha (m : ℝ))

/-- Factor-two separation in gap coordinates is exactly endpoint separation
for strips `(1 - 2g, 1 - g]`. -/
def CarlsonDynamicGapFamilySeparated
    (layers : ℕ → ℕ) (gap : ℕ → ℕ → ℝ) : Prop :=
  ∀ m (i j : Fin (layers m)), i ≠ j →
    2 * gap m i.1 ≤ gap m j.1 ∨
      2 * gap m j.1 ≤ gap m i.1

theorem actualDynamicCarlsonGapStripUnion_mass_eq_familyMass
    {alpha : ℝ} {layers : ℕ → ℕ} {gap : ℕ → ℕ → ℝ} {m : ℕ}
    (hsep : CarlsonDynamicGapFamilySeparated layers gap) :
    (∑ rho ∈ actualDynamicCarlsonGapStripUnion alpha layers gap m,
        ‖pntRelativeZeroContribution (m : ℝ) rho‖) =
      actualDynamicCarlsonGapFamilyMass alpha layers gap m := by
  let sigma : Fin (layers m) → ℝ :=
    fun i => 1 - 2 * gap m i.1
  let tau : Fin (layers m) → ℝ :=
    fun i => 1 - gap m i.1
  have hendpoints :
      ∀ i j, i ≠ j →
        tau i ≤ sigma j ∨ tau j ≤ sigma i := by
    intro i j hij
    rcases hsep m i j hij with hijGap | hjiGap
    · right
      dsimp [sigma, tau]
      linarith
    · left
      dsimp [sigma, tau]
      linarith
  have hdisjoint :=
    actualPositiveCarlsonStrips_pairwiseDisjoint_of_endpoints
      sigma tau (carlsonPolynomialHeight alpha (m : ℝ)) hendpoints
  have heq :=
    actualPositiveCarlsonFiniteStripUnion_mass_eq
      sigma tau alpha (m : ℝ) hdisjoint
  simpa [actualDynamicCarlsonGapStripUnion,
    actualDynamicCarlsonGapFamilyMass,
    carlsonDynamicFiniteLayerMass,
    actualDynamicCarlsonGapLayerMass,
    actualMovingCarlsonStripMass,
    actualDynamicCarlsonGapSchedule,
    actualPositiveCarlsonFiniteStripMass,
    sigma, tau] using heq

/-- The two actual zero counts required in every dynamic layer. -/
def IsActualDynamicCarlsonGapFamilyCountCertificate
    (A alpha : ℝ) (layers : ℕ → ℕ) (gap : ℕ → ℕ → ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i : Fin (layers m),
    let delta := actualDynamicCarlsonGapSchedule gap i.1
    (ZeroDensity.zeroDensityCount (1 - 2 * delta m)
        (carlsonPolynomialHeight
          (carlsonMovingBalancedCut alpha delta m) (m : ℝ)) : ℝ) ≤
      carlsonPointwiseCountBudget A (1 - 2 * delta m)
        (carlsonPolynomialHeight
          (carlsonMovingBalancedCut alpha delta m) (m : ℝ)) ∧
    (ZeroDensity.zeroDensityCount (1 - 2 * delta m)
        (carlsonPolynomialHeight alpha (m : ℝ)) : ℝ) ≤
      carlsonPointwiseCountBudget A (1 - 2 * delta m)
        (carlsonPolynomialHeight alpha (m : ℝ))

/-- Pointwise version of the count-to-budget multiplication used by the
single-strip automatic theorem. -/
theorem actualDynamicCarlsonTwoHeightBudget_le_pointwiseMajorant
    {A alpha : ℝ} {delta gamma : ℕ → ℝ} {m : ℕ}
    (hm : 1 ≤ m) (hdelta : 0 < delta m)
    (hdeltaUpper : delta m ≤ 1 / 8)
    (hcount :
      (ZeroDensity.zeroDensityCount (1 - 2 * delta m)
          (carlsonPolynomialHeight (gamma m) (m : ℝ)) : ℝ) ≤
        carlsonPointwiseCountBudget A (1 - 2 * delta m)
          (carlsonPolynomialHeight (gamma m) (m : ℝ)) ∧
      (ZeroDensity.zeroDensityCount (1 - 2 * delta m)
          (carlsonPolynomialHeight alpha (m : ℝ)) : ℝ) ≤
        carlsonPointwiseCountBudget A (1 - 2 * delta m)
          (carlsonPolynomialHeight alpha (m : ℝ))) :
    actualCarlsonTwoHeightLowBudget
          (1 - 2 * delta m) (1 - delta m) (gamma m) (m : ℝ) +
        actualCarlsonTwoHeightHighBudget
          (1 - 2 * delta m) (1 - delta m) alpha (gamma m) (m : ℝ) ≤
      actualMovingCarlsonTwoHeightPointwiseMajorant
        A alpha delta gamma m := by
  have hmReal : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmNonneg : (0 : ℝ) ≤ (m : ℝ) := zero_le_one.trans hmReal
  have hsigma : 0 < 1 - 2 * delta m := by linarith
  have hlowFactor :
      0 ≤ (m : ℝ) ^ (-delta m) / (1 - 2 * delta m) := by
    exact div_nonneg (Real.rpow_nonneg hmNonneg _) hsigma.le
  have hhighFactor :
      0 ≤ polynomialOrdinateRectangleKernel
        (1 - delta m) (gamma m) (m : ℝ) := by
    unfold polynomialOrdinateRectangleKernel
    exact div_nonneg (Real.rpow_nonneg hmNonneg _)
      (Real.rpow_nonneg hmNonneg _)
  unfold actualMovingCarlsonTwoHeightPointwiseMajorant
    actualMovingCarlsonLowPointwiseMajorant
    actualMovingCarlsonHighPointwiseMajorant
    actualCarlsonTwoHeightLowBudget
    actualCarlsonTwoHeightHighBudget
  have hlow := mul_le_mul_of_nonneg_left hcount.1 hlowFactor
  have hhigh := mul_le_mul_of_nonneg_left hcount.2 hhighFactor
  have hexponent : 1 - delta m - 1 = -delta m := by ring
  rw [hexponent]
  exact add_le_add hlow hhigh

/-- Every actual dynamic layer is bounded by its own honest pointwise Carlson
ratio. -/
theorem eventually_actualDynamicCarlsonGapLayerMass_le_ownRatio
    {A alpha : ℝ} {layers : ℕ → ℕ} {gap : ℕ → ℕ → ℝ}
    (hA : 0 ≤ A) (halpha : 0 < alpha)
    (hgap :
      ∀ᶠ m : ℕ in atTop, ∀ i : Fin (layers m),
        0 < gap m i.1 ∧ gap m i.1 ≤ 1 / 8)
    (hcount :
      IsActualDynamicCarlsonGapFamilyCountCertificate
        A alpha layers gap) :
    ∀ᶠ m : ℕ in atTop, ∀ i : Fin (layers m),
      actualDynamicCarlsonGapLayerMass alpha layers gap m i ≤
        carlsonMovingBalancedCoefficientRatio alpha
          (actualDynamicCarlsonGapSchedule gap i.1)
          (carlsonMovingQuadraticLogPowerEnvelope
            (actualMovingCarlsonBalancedPositiveConstant A alpha)
            (actualDynamicCarlsonGapSchedule gap i.1)) m := by
  filter_upwards [eventually_ge_atTop (2 : ℕ), hgap, hcount] with
      m hm hgm hNm
  intro i
  let delta := actualDynamicCarlsonGapSchedule gap i.1
  have hdm : 0 < delta m ∧ delta m ≤ 1 / 8 := by
    simpa [delta, actualDynamicCarlsonGapSchedule] using hgm i
  have hcountm := hNm i
  have hmReal : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (le_trans (by norm_num) hm)
  have hsigma : 0 < 1 - 2 * delta m := by linarith
  have hquarter : delta m < 1 / 4 :=
    hdm.2.trans_lt (by norm_num)
  have hcutAlpha :
      carlsonMovingBalancedCut alpha delta m ≤ alpha :=
    (carlsonMovingBalancedCut_lt_alpha
      hdm.1 hquarter halpha).le
  have hbudget :=
    actualDynamicCarlsonTwoHeightBudget_le_pointwiseMajorant
      (le_trans (by norm_num) hm) hdm.1 hdm.2 hcountm
  have hratio :=
    actualMovingCarlsonTwoHeightPointwiseMajorant_le_logPowerRatio
      hA halpha hm hdm.1 hdm.2
  unfold actualDynamicCarlsonGapLayerMass actualMovingCarlsonStripMass
  exact
    (sum_norm_actualPositiveCarlsonStrip_le_twoHeightBudget
      hmReal hsigma hcutAlpha).trans (hbudget.trans hratio)

/-- Explicit remaining comparison between the heterogeneous gap ratios and
the common smallest-gap ratio used for summation. -/
def IsCarlsonDynamicGapFamilyRatioDominated
    (alpha C : ℝ) (delta : ℕ → ℝ)
    (layers : ℕ → ℕ) (gap : ℕ → ℕ → ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i : Fin (layers m),
    carlsonMovingBalancedCoefficientRatio alpha
        (actualDynamicCarlsonGapSchedule gap i.1)
        (carlsonMovingQuadraticLogPowerEnvelope C
          (actualDynamicCarlsonGapSchedule gap i.1)) m ≤
      carlsonMovingBalancedCoefficientRatio alpha delta
        (carlsonMovingQuadraticLogPowerEnvelope C delta) m

/-- Actual dynamic Carlson strip families decay after combining pointwise
counts, the common-ratio comparison, and the complete layer-count margin. -/
theorem tendsto_actualDynamicCarlsonGapFamilyMass_zero
    {A alpha : ℝ} {delta : ℕ → ℝ}
    {layers : ℕ → ℕ} {gap : ℕ → ℕ → ℝ}
    (hA : 0 ≤ A) (halpha : 0 < alpha)
    (hdelta :
      ∀ᶠ m : ℕ in atTop,
        0 < delta m ∧ delta m ≤ 1 / 2 ∧
          128 * alpha * delta m ≤ 1)
    (hlayerGap :
      ∀ᶠ m : ℕ in atTop, ∀ i : Fin (layers m),
        0 < gap m i.1 ∧ gap m i.1 ≤ 1 / 8)
    (hmargin :
      IsCarlsonMovingQuadraticLogPowerLayerCountGap delta layers)
    (hcount :
      IsActualDynamicCarlsonGapFamilyCountCertificate
        A alpha layers gap)
    (hdominated :
      IsCarlsonDynamicGapFamilyRatioDominated alpha
        (actualMovingCarlsonBalancedPositiveConstant A alpha)
        delta layers gap) :
    Tendsto
      (actualDynamicCarlsonGapFamilyMass alpha layers gap)
      atTop (nhds 0) := by
  apply tendsto_carlsonDynamicFiniteLayerMass_zero_logPower
    halpha.le hdelta hmargin
  · filter_upwards with m
    intro i
    exact actualMovingCarlsonStripMass_nonneg alpha
      (actualDynamicCarlsonGapSchedule gap i.1) m
  · have hown :=
      eventually_actualDynamicCarlsonGapLayerMass_le_ownRatio
        hA halpha hlayerGap hcount
    filter_upwards [hown, hdominated] with m hm hdom
    intro i
    exact (hm i).trans (hdom i)

/-- The corresponding actual zeta union mass tends to zero when the gap
strips are factor-two separated. -/
theorem tendsto_actualDynamicCarlsonGapStripUnion_mass_zero
    {A alpha : ℝ} {delta : ℕ → ℝ}
    {layers : ℕ → ℕ} {gap : ℕ → ℕ → ℝ}
    (hA : 0 ≤ A) (halpha : 0 < alpha)
    (hdelta :
      ∀ᶠ m : ℕ in atTop,
        0 < delta m ∧ delta m ≤ 1 / 2 ∧
          128 * alpha * delta m ≤ 1)
    (hlayerGap :
      ∀ᶠ m : ℕ in atTop, ∀ i : Fin (layers m),
        0 < gap m i.1 ∧ gap m i.1 ≤ 1 / 8)
    (hmargin :
      IsCarlsonMovingQuadraticLogPowerLayerCountGap delta layers)
    (hcount :
      IsActualDynamicCarlsonGapFamilyCountCertificate
        A alpha layers gap)
    (hdominated :
      IsCarlsonDynamicGapFamilyRatioDominated alpha
        (actualMovingCarlsonBalancedPositiveConstant A alpha)
        delta layers gap)
    (hseparated : CarlsonDynamicGapFamilySeparated layers gap) :
    Tendsto
      (fun m =>
        ∑ rho ∈ actualDynamicCarlsonGapStripUnion
            alpha layers gap m,
          ‖pntRelativeZeroContribution (m : ℝ) rho‖)
      atTop (nhds 0) := by
  apply
    (tendsto_actualDynamicCarlsonGapFamilyMass_zero
      hA halpha hdelta hlayerGap hmargin hcount hdominated).congr'
  filter_upwards with m
  exact
    (actualDynamicCarlsonGapStripUnion_mass_eq_familyMass
      hseparated).symm

end

end PrimeNumberTheorem
