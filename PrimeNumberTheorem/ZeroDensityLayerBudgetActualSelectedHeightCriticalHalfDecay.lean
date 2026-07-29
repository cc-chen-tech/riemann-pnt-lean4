import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCriticalHalfDecay
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualMovingCarlsonWindowHeightDecay
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTHybridActualSelectedHeightLowLayer

/-!
# Critical-half decay at a selected height in a unit window

The existing selected-height low-layer theorem works for every cofinal height
bounded by a polynomial.  This module proves that a unit good-height window
automatically supplies both conditions after allowing an arbitrarily small
strict increase in the polynomial exponent.
-/

namespace PrimeNumberTheorem

open Filter
open scoped Topology

noncomputable section

/-- Canonical critical-half split at an arbitrary height schedule. -/
def actualSelectedHeightCriticalHalfCanonicalInput
    (H : ℝ → ℝ) (x : ℝ) :
    PositiveZeroOutsideClusterBucketInput (H x) ∅ 2 :=
  pntHybridCanonicalTwoStripOutsideClusterBucketInput
    (1 / 2) (H x) ∅

theorem actualSelectedHeightCriticalHalfCanonicalInput_low_re_le
    {H : ℝ → ℝ} {x : ℝ} {rho : ℂ}
    (hrho :
      rho ∈ (actualSelectedHeightCriticalHalfCanonicalInput H x).layer
        (0 : Fin 2)) :
    rho.re ≤ 1 / 2 :=
  pntHybridCanonicalTwoStripOutsideCluster_low_re_le hrho

/-- Real-variable version of unit-window absorption into every strictly
larger polynomial exponent. -/
theorem eventually_selectedHeight_le_polynomialHeight_of_unitWindow_real
    {H : ℝ → ℝ} {innerAlpha outerAlpha : ℝ}
    (hinner : 0 ≤ innerAlpha)
    (hstrict : innerAlpha < outerAlpha)
    (hwindow : ∀ᶠ x : ℝ in atTop,
      H x ∈ Set.Icc
        (carlsonPolynomialHeight innerAlpha x)
        (carlsonPolynomialHeight innerAlpha x + 1)) :
    ∀ᶠ x : ℝ in atTop,
      H x ≤ carlsonPolynomialHeight outerAlpha x := by
  have hgap : 0 < outerAlpha - innerAlpha := sub_pos.mpr hstrict
  have hgapGrowth :
      Tendsto (fun x : ℝ => x ^ (outerAlpha - innerAlpha))
        atTop atTop :=
    tendsto_rpow_atTop hgap
  filter_upwards [
    hwindow,
    eventually_ge_atTop (1 : ℝ),
    hgapGrowth.eventually (eventually_ge_atTop (2 : ℝ))
  ] with x hxWindow hx hgapTwo
  have hxPos : 0 < x := zero_lt_one.trans_le hx
  have hinnerOne :
      1 ≤ carlsonPolynomialHeight innerAlpha x := by
    unfold carlsonPolynomialHeight
    exact Real.one_le_rpow hx hinner
  have hfactorNonneg :
      0 ≤ carlsonPolynomialHeight innerAlpha x :=
    Real.rpow_nonneg (zero_le_one.trans hx) _
  calc
    H x ≤ carlsonPolynomialHeight innerAlpha x + 1 :=
      hxWindow.2
    _ ≤ 2 * carlsonPolynomialHeight innerAlpha x := by
      linarith
    _ ≤ carlsonPolynomialHeight innerAlpha x *
          x ^ (outerAlpha - innerAlpha) := by
      simpa [mul_comm] using
        (mul_le_mul_of_nonneg_right hgapTwo hfactorNonneg)
    _ = carlsonPolynomialHeight outerAlpha x := by
      unfold carlsonPolynomialHeight
      rw [← Real.rpow_add hxPos]
      congr 1
      ring

/-- A positive-exponent unit window is automatically cofinal. -/
theorem tendsto_selectedHeight_atTop_of_unitWindow
    {H : ℝ → ℝ} {alpha : ℝ}
    (halpha : 0 < alpha)
    (hwindow : ∀ᶠ x : ℝ in atTop,
      H x ∈ Set.Icc
        (carlsonPolynomialHeight alpha x)
        (carlsonPolynomialHeight alpha x + 1)) :
    Tendsto H atTop atTop := by
  have hbase :
      Tendsto (carlsonPolynomialHeight alpha) atTop atTop :=
    tendsto_rpow_atTop halpha
  refine tendsto_atTop.2 ?_
  intro b
  filter_upwards [
    hwindow,
    hbase.eventually (eventually_ge_atTop b)
  ] with x hx hbx
  exact hbx.trans hx.1

/-- The selected critical-half contribution tends to zero along natural
points when the selected height lies in a unit polynomial window and that
window is absorbed below an exponent strictly less than `1 / 2`. -/
theorem tendsto_actualSelectedHeightCriticalHalfPNTLayerNorm_zero
    {H : ℝ → ℝ} {innerAlpha outerAlpha epsilon : ℝ}
    (hinner : 0 < innerAlpha)
    (hstrict : innerAlpha < outerAlpha)
    (houter : 0 < outerAlpha)
    (hepsilon : 0 < epsilon)
    (hmargin : outerAlpha + epsilon < 1 / 2)
    (hwindow : ∀ᶠ x : ℝ in atTop,
      H x ∈ Set.Icc
        (carlsonPolynomialHeight innerAlpha x)
        (carlsonPolynomialHeight innerAlpha x + 1)) :
    Tendsto
      (fun m : ℕ =>
        dynamicPositiveOutsideClusterPNTLayerNorm H ∅
          (actualSelectedHeightCriticalHalfCanonicalInput H)
          (0 : Fin 2) (m : ℝ))
      atTop (nhds 0) := by
  rcases
      exists_canonicalTwoStripOutsideCluster_uniform_norm_lower_bound
        H (1 / 2) ∅ with
    ⟨kappa, hkappa, hnorm⟩
  have hreal :=
    tendsto_dynamicPositiveOutsideClusterPNTLayerNorm_div_targetAmplitude_zero_of_hybrid_selectedHeight
      (input := actualSelectedHeightCriticalHalfCanonicalInput H)
      (i := (0 : Fin 2))
      (beta := 1) (tau := (1 / 2 : ℝ))
      (alpha := outerAlpha) (kappa := kappa)
      (epsilon := epsilon)
      (eventually_selectedHeight_le_polynomialHeight_of_unitWindow_real
        hinner.le hstrict hwindow)
      (tendsto_selectedHeight_atTop_of_unitWindow hinner hwindow)
      hkappa
      (by
        intro x rho hrho
        exact hnorm x rho hrho)
      (by
        intro x rho hrho
        exact
          actualSelectedHeightCriticalHalfCanonicalInput_low_re_le hrho)
      houter hepsilon (by linarith)
  have hreal' :
      Tendsto
        (fun x : ℝ =>
          dynamicPositiveOutsideClusterPNTLayerNorm H ∅
            (actualSelectedHeightCriticalHalfCanonicalInput H)
            (0 : Fin 2) x)
        atTop (nhds 0) := by
    convert hreal using 1
    funext x
    simp [targetZeroPowerAmplitude,
      dynamicPositiveOutsideClusterPNTLayerNorm]
  exact hreal'.comp tendsto_natCast_atTop_atTop

end

end PrimeNumberTheorem
