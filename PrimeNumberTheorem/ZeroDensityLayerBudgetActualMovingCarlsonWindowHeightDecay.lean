import PrimeNumberTheorem.ZeroDensityLayerBudgetActualMovingCarlsonFullyAutomaticDecay

/-!
# Moving Carlson decay at a selected height in a unit window

Explicit-formula contour arguments select a good height in
`[x ^ innerAlpha, x ^ innerAlpha + 1]`, whereas the moving Carlson decay
theorem is stated at an exact polynomial height.  This module supplies the
missing height-stability bridge.
-/

namespace PrimeNumberTheorem

open Filter
open scoped BigOperators Topology

noncomputable section

/-- Multiplicity-weighted moving-strip mass at an arbitrary selected height. -/
def actualSelectedHeightMovingCarlsonStripMass
    (H : ℝ → ℝ) (delta : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ rho ∈ actualPositiveCarlsonStrip
      (1 - 2 * delta m) (1 - delta m) (H (m : ℝ)),
    ‖pntRelativeZeroContribution (m : ℝ) rho‖

theorem actualSelectedHeightMovingCarlsonStripMass_nonneg
    (H : ℝ → ℝ) (delta : ℕ → ℝ) (m : ℕ) :
    0 ≤ actualSelectedHeightMovingCarlsonStripMass H delta m := by
  unfold actualSelectedHeightMovingCarlsonStripMass
  positivity

/-- Increasing only the height preserves membership in an actual Carlson
strip. -/
theorem actualPositiveCarlsonStrip_mono_height
    {sigma tau T U : ℝ} (hTU : T ≤ U) :
    actualPositiveCarlsonStrip sigma tau T ⊆
      actualPositiveCarlsonStrip sigma tau U := by
  intro rho hrho
  rcases mem_actualPositiveCarlsonStrip.mp hrho with
    ⟨hzero, him, hheight, hlower, hupper⟩
  exact mem_actualPositiveCarlsonStrip.mpr
    ⟨hzero, him, hheight.trans hTU, hlower, hupper⟩

/-- A selected moving-strip mass is bounded by the exact polynomial-height
mass whenever the selected height is no larger. -/
theorem actualSelectedHeightMovingCarlsonStripMass_le_exact
    {H : ℝ → ℝ} {alpha : ℝ} {delta : ℕ → ℝ} {m : ℕ}
    (hheight :
      H (m : ℝ) ≤ carlsonPolynomialHeight alpha (m : ℝ)) :
    actualSelectedHeightMovingCarlsonStripMass H delta m ≤
      actualMovingCarlsonStripMass alpha delta m := by
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (actualPositiveCarlsonStrip_mono_height hheight)
    (fun rho _ _ => norm_nonneg _)

/-- A unit window above a smaller polynomial height is eventually contained
below every strictly larger polynomial height. -/
theorem eventually_selectedHeight_le_polynomialHeight_of_unitWindow
    {H : ℝ → ℝ} {innerAlpha outerAlpha : ℝ}
    (hinner : 0 ≤ innerAlpha)
    (hstrict : innerAlpha < outerAlpha)
    (hwindow : ∀ᶠ m : ℕ in atTop,
      H (m : ℝ) ∈ Set.Icc
        (carlsonPolynomialHeight innerAlpha (m : ℝ))
        (carlsonPolynomialHeight innerAlpha (m : ℝ) + 1)) :
    ∀ᶠ m : ℕ in atTop,
      H (m : ℝ) ≤ carlsonPolynomialHeight outerAlpha (m : ℝ) := by
  have hgap : 0 < outerAlpha - innerAlpha := sub_pos.mpr hstrict
  have hgapGrowth :
      Tendsto (fun x : ℝ => x ^ (outerAlpha - innerAlpha))
        atTop atTop :=
    tendsto_rpow_atTop hgap
  filter_upwards [
    hwindow,
    eventually_ge_atTop (1 : ℕ),
    (hgapGrowth.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (2 : ℝ))
  ] with m hm hmOne hgapTwo
  have hmReal : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hmOne
  have hmPos : (0 : ℝ) < (m : ℝ) := zero_lt_one.trans_le hmReal
  have hinnerOne :
      1 ≤ carlsonPolynomialHeight innerAlpha (m : ℝ) := by
    unfold carlsonPolynomialHeight
    exact Real.one_le_rpow hmReal hinner
  have hfactorNonneg :
      0 ≤ carlsonPolynomialHeight innerAlpha (m : ℝ) :=
    Real.rpow_nonneg (zero_le_one.trans hmReal) _
  calc
    H (m : ℝ) ≤
        carlsonPolynomialHeight innerAlpha (m : ℝ) + 1 :=
      hm.2
    _ ≤ 2 * carlsonPolynomialHeight innerAlpha (m : ℝ) := by
      linarith
    _ ≤ carlsonPolynomialHeight innerAlpha (m : ℝ) *
          ((m : ℝ) ^ (outerAlpha - innerAlpha)) := by
      simpa [mul_comm] using
        (mul_le_mul_of_nonneg_right hgapTwo hfactorNonneg)
    _ = carlsonPolynomialHeight outerAlpha (m : ℝ) := by
      unfold carlsonPolynomialHeight
      rw [← Real.rpow_add hmPos]
      congr 1
      ring

/-- Fully automatic Carlson decay remains valid at every selected height in a
unit window below a strictly larger polynomial exponent. -/
theorem tendsto_actualSelectedHeightMovingCarlsonStripMass_zero
    {H : ℝ → ℝ} {innerAlpha outerAlpha : ℝ}
    {delta : ℕ → ℝ}
    (hinner : 0 ≤ innerAlpha)
    (hstrict : innerAlpha < outerAlpha)
    (houter : 0 < outerAlpha)
    (hwindow : ∀ᶠ m : ℕ in atTop,
      H (m : ℝ) ∈ Set.Icc
        (carlsonPolynomialHeight innerAlpha (m : ℝ))
        (carlsonPolynomialHeight innerAlpha (m : ℝ) + 1))
    (hdelta : ∀ᶠ m : ℕ in atTop,
      0 < delta m ∧ delta m ≤ 1 / 8 ∧
        128 * outerAlpha * delta m ≤ 1)
    (hgap : IsCarlsonMovingQuadraticLogPowerGap delta) :
    Tendsto
      (actualSelectedHeightMovingCarlsonStripMass H delta)
      atTop (nhds 0) := by
  have hheight :=
    eventually_selectedHeight_le_polynomialHeight_of_unitWindow
      hinner hstrict hwindow
  have hexact :=
    tendsto_actualMovingCarlsonStripMass_zero_fullyAutomatic
      houter hdelta hgap
  refine squeeze_zero' ?_ ?_ hexact
  · filter_upwards with m
    exact actualSelectedHeightMovingCarlsonStripMass_nonneg H delta m
  · filter_upwards [hheight] with m hm
    exact actualSelectedHeightMovingCarlsonStripMass_le_exact hm

end

end PrimeNumberTheorem
