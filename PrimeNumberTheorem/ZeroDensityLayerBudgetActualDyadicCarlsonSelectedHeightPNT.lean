import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDyadicCarlsonMinimalLayerHeights
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedUniformGoodHeightPNT

/-!
# Selected-height PNT transfer from the automatic dyadic Carlson cover

The selected-height middle strip `(1 / 2, 1 - 2 * delta]` is split at the
fixed anchor `7 / 8`.

* `(1 / 2, 7 / 8]` decays from the global multiplicity bound when the
  polynomial-height exponent is strictly below `1 / 8`.
* `(7 / 8, 1 - 2 * delta]` is contained in the automatically scheduled
  dyadic Carlson window.
* A selected-height dynamic zero-free region excludes zeros to the right of
  `1 - delta`.

The existing explicit-formula transfer then yields decay of the actual
relative Chebyshev `psi₀` error.
-/

namespace PrimeNumberTheorem

open Filter Topology
open scoped BigOperators

noncomputable section

/-- Selected-height PNT kernel mass in the fixed low strip
`(1 / 2, 7 / 8]`. -/
noncomputable def actualSelectedHeightSevenEighthsLowMass
    (H : ℝ → ℝ) (m : ℕ) : ℝ :=
  ∑ rho ∈ actualPositiveCarlsonStrip
      (1 / 2) (7 / 8) (H (m : ℝ)),
    ‖pntRelativeZeroContribution (m : ℝ) rho‖

theorem actualSelectedHeightSevenEighthsLowMass_nonneg
    (H : ℝ → ℝ) (m : ℕ) :
    0 ≤ actualSelectedHeightSevenEighthsLowMass H m := by
  unfold actualSelectedHeightSevenEighthsLowMass
  positivity

/-- A selected uniformly good height below `x ^ outerAlpha` gives decay of
the fixed low strip whenever `outerAlpha < 1 / 8`, with a strict logarithmic
margin recorded by `epsilon`. -/
theorem tendsto_actualSelectedHeightSevenEighthsLowMass_zero
    {innerAlpha outerAlpha epsilon : ℝ}
    (hinner : 0 < innerAlpha)
    (hstrict : innerAlpha < outerAlpha)
    (houter : 0 < outerAlpha)
    (hepsilon : 0 < epsilon)
    (hmargin : outerAlpha + epsilon < 1 / 8)
    (selection : UniformNaturalPointGoodHeightSelection) :
    Tendsto
      (actualSelectedHeightSevenEighthsLowMass
        (selectedUniformGoodHeight innerAlpha selection))
      atTop (nhds 0) := by
  let H := selectedUniformGoodHeight innerAlpha selection
  rcases
      exists_canonicalTwoStripOutsideCluster_uniform_norm_lower_bound
        H (7 / 8) ∅ with
    ⟨kappa, hkappa, hnorm⟩
  rcases ExplicitFormulaAux.exists_globalZeroMultiplicity_le_mul_log with
    ⟨C, hC, hglobalMultiplicity⟩
  have hHle :
      ∀ᶠ x : ℝ in atTop,
        H x ≤ carlsonPolynomialHeight outerAlpha x :=
    eventually_selectedUniformGoodHeight_le_polynomialHeight
      hinner hstrict selection
  have hHtop : Tendsto H atTop atTop := by
    simpa [H] using
      selectedUniformGoodHeight_tendsto_atTop hinner selection
  have hlogReal :=
    eventually_one_add_log_polynomialHeight_add_six_le_log_four houter
  have hlog :
      ∀ᶠ m : ℕ in atTop,
        1 + Real.log ((m : ℝ) ^ outerAlpha + 6) ≤
          (outerAlpha + 2) * Real.log (m : ℝ) ^ 4 :=
    tendsto_natCast_atTop_atTop.eventually hlogReal
  have hmajorReal :
      Tendsto
        (actualHybridLowNormalizedLogPowerMajorant
          C kappa 1 (7 / 8) outerAlpha)
        atTop (nhds 0) :=
    tendsto_actualHybridLowNormalizedLogPowerMajorant_zero
      hC hkappa houter hepsilon (by linarith)
  have hmajor :
      Tendsto
        (fun m : ℕ =>
          actualHybridLowNormalizedLogPowerMajorant
            C kappa 1 (7 / 8) outerAlpha (m : ℝ))
        atTop (nhds 0) :=
    hmajorReal.comp tendsto_natCast_atTop_atTop
  refine squeeze_zero' ?_ ?_ hmajor
  · exact Filter.Eventually.of_forall
      (actualSelectedHeightSevenEighthsLowMass_nonneg H)
  · filter_upwards [
      eventually_ge_atTop (1 : ℕ),
      hHtop.comp tendsto_natCast_atTop_atTop |>.eventually
        (eventually_ge_atTop (4 : ℝ)),
      tendsto_natCast_atTop_atTop.eventually hHle,
      hlog] with m hm hHfour hHupper hlogBound
    have hmPos : 0 < (m : ℝ) := by
      exact_mod_cast (Nat.zero_lt_of_lt hm)
    let layer :=
      actualPositiveCarlsonStrip
        (1 / 2) (7 / 8) (H (m : ℝ))
    have hnormLayer :
        ∀ rho ∈ layer, kappa ≤ ‖rho‖ := by
      intro rho hrho
      rcases mem_actualPositiveCarlsonStrip.mp hrho with
        ⟨hzero, him, himHeight, _, hreUpper⟩
      apply hnorm (m : ℝ) rho
      apply Finset.mem_filter.mpr
      constructor
      · exact mem_positiveNontrivialZerosOutsideClusterFinset.mpr
          ⟨hzero, him, himHeight, by simp⟩
      · exact
          pntHybridCanonicalTwoStripOutsideCluster_low_cover
            (mem_positiveNontrivialZerosOutsideClusterFinset.mpr
              ⟨hzero, him, himHeight, by simp⟩)
            hreUpper
    have hkernel :
        ∀ rho ∈ layer,
          ‖pntRelativeSimpleZeroKernel (m : ℝ) rho‖ ≤
            stripEndpointRelativeKernelBudget
              kappa (7 / 8) (m : ℝ) := by
      intro rho hrho
      rcases mem_actualPositiveCarlsonStrip.mp hrho with
        ⟨_, _, _, _, hreUpper⟩
      exact
        norm_pntRelativeSimpleZeroKernel_le_stripEndpoint
          (by exact_mod_cast hm) hkappa (hnormLayer rho hrho)
          hreUpper
    have hkernelNonneg :
        0 ≤ stripEndpointRelativeKernelBudget
          kappa (7 / 8) (m : ℝ) :=
      stripEndpointRelativeKernelBudget_nonneg
        (by exact_mod_cast (Nat.zero_le m)) hkappa.le
    have hmass :
        analyticMultiplicityMass layer ≤
          ExplicitFormulaAux.globalZeroMultiplicity (H (m : ℝ)) := by
      have hsubset :
          layer ⊆ nontrivialZerosFinset (H (m : ℝ)) := by
        intro rho hrho
        rcases mem_actualPositiveCarlsonStrip.mp hrho with
          ⟨hzero, him, himHeight, _, _⟩
        exact mem_nontrivialZerosFinset.mpr
          ⟨hzero, by simpa [abs_of_pos him] using himHeight⟩
      unfold analyticMultiplicityMass
        ExplicitFormulaAux.globalZeroMultiplicity
      exact
        Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun rho _ _ => Nat.cast_nonneg _)
    have hphysical :
        actualSelectedHeightSevenEighthsLowMass H m ≤
          actualHybridGlobalLowLayerMajorant
            C (H (m : ℝ)) kappa (7 / 8) (m : ℝ) := by
      calc
        actualSelectedHeightSevenEighthsLowMass H m =
            ∑ rho ∈ layer,
              ‖pntRelativeZeroContribution (m : ℝ) rho‖ := rfl
        _ ≤ stripEndpointRelativeKernelBudget
                kappa (7 / 8) (m : ℝ) *
              analyticMultiplicityMass layer :=
          sum_norm_pntRelativeZeroContribution_le_kernel_mul_multiplicityMass
            layer (m : ℝ)
            (stripEndpointRelativeKernelBudget
              kappa (7 / 8) (m : ℝ))
            hkernelNonneg hkernel
        _ ≤ stripEndpointRelativeKernelBudget
                kappa (7 / 8) (m : ℝ) *
              ExplicitFormulaAux.globalZeroMultiplicity (H (m : ℝ)) :=
          mul_le_mul_of_nonneg_left hmass hkernelNonneg
        _ ≤ stripEndpointRelativeKernelBudget
                kappa (7 / 8) (m : ℝ) *
              (C * H (m : ℝ) *
                (1 + Real.log (H (m : ℝ) + 6))) :=
          mul_le_mul_of_nonneg_left
            (hglobalMultiplicity (H (m : ℝ)) hHfour) hkernelNonneg
        _ = actualHybridGlobalLowLayerMajorant
              C (H (m : ℝ)) kappa (7 / 8) (m : ℝ) := by
          unfold actualHybridGlobalLowLayerMajorant
          ring
    have hselected :
        actualHybridGlobalLowLayerMajorant
            C (H (m : ℝ)) kappa (7 / 8) (m : ℝ) ≤
          actualHybridGlobalLowLayerMajorant
            C (carlsonPolynomialHeight outerAlpha (m : ℝ))
              kappa (7 / 8) (m : ℝ) :=
      actualHybridGlobalLowLayerMajorant_mono_height
        hC hkappa hmPos.le hHfour hHupper
    have hcoefficient :
        0 ≤ C * kappa⁻¹ *
          (m : ℝ) ^ ((7 / 8 : ℝ) - 1 + outerAlpha) := by
      positivity
    calc
      actualSelectedHeightSevenEighthsLowMass H m ≤
          actualHybridGlobalLowLayerMajorant
            C (carlsonPolynomialHeight outerAlpha (m : ℝ))
              kappa (7 / 8) (m : ℝ) :=
        hphysical.trans hselected
      _ =
          actualHybridGlobalLowLayerMajorant
              C (carlsonPolynomialHeight outerAlpha (m : ℝ))
                kappa (7 / 8) (m : ℝ) /
            targetZeroPowerAmplitude 1 (m : ℝ) := by
        rw [show targetZeroPowerAmplitude 1 (m : ℝ) = 1 by
          simp [targetZeroPowerAmplitude], div_one]
      _ =
          C * kappa⁻¹ *
              (m : ℝ) ^ ((7 / 8 : ℝ) - 1 + outerAlpha) *
            (1 + Real.log ((m : ℝ) ^ outerAlpha + 6)) := by
        exact
          actualHybridGlobalLowLayerMajorant_div_target_eq
            (C := C) (kappa := kappa) (beta := 1)
            (tau := 7 / 8) (alpha := outerAlpha) hmPos
      _ ≤
          C * kappa⁻¹ *
              (m : ℝ) ^ ((7 / 8 : ℝ) - 1 + outerAlpha) *
            ((outerAlpha + 2) * Real.log (m : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_left hlogBound hcoefficient
      _ =
          actualHybridLowNormalizedLogPowerMajorant
            C kappa 1 (7 / 8) outerAlpha (m : ℝ) := by
        unfold actualHybridLowNormalizedLogPowerMajorant
        ring

/-- At one selected height, the moving middle strip is covered by the fixed
low strip and the minimal dyadic fixed-anchor window. -/
theorem actualSelectedHeightMovingMiddle_le_low_add_dyadicAnchor
    {H : ℝ → ℝ} {outerAlpha : ℝ} {delta : ℕ → ℝ} {m : ℕ}
    (hdeltaNonneg : 0 ≤ delta m)
    (hdelta : 0 < delta m)
    (hheight :
      H (m : ℝ) ≤ carlsonPolynomialHeight outerAlpha (m : ℝ)) :
    actualSelectedHeightMovingCarlsonMiddleMass H delta m ≤
      actualSelectedHeightSevenEighthsLowMass H m +
        actualDyadicCarlsonFixedAnchorMass outerAlpha delta
          (dyadicCarlsonLayerSchedule delta) m := by
  let middle :=
    actualPositiveCarlsonStrip
      (1 / 2) (1 - 2 * delta m) (H (m : ℝ))
  let low :=
    actualPositiveCarlsonStrip
      (1 / 2) (7 / 8) (H (m : ℝ))
  let anchor :=
    actualDyadicCarlsonFixedAnchorWindow outerAlpha delta
      (dyadicCarlsonLayerSchedule delta) m
  have hsubset : middle ⊆ low ∪ anchor := by
    intro rho hrho
    rcases mem_actualPositiveCarlsonStrip.mp hrho with
      ⟨hzero, him, himHeight, hreLower, hreUpper⟩
    by_cases hreLow : rho.re ≤ 7 / 8
    · exact Finset.mem_union.mpr <| Or.inl <|
        mem_actualPositiveCarlsonStrip.mpr
          ⟨hzero, him, himHeight, hreLower, hreLow⟩
    · have hreAnchor : (7 / 8 : ℝ) < rho.re :=
        lt_of_not_ge hreLow
      have hreRight : rho.re ≤ 1 - delta m := by
        linarith
      exact Finset.mem_union.mpr <| Or.inr <|
        mem_actualDyadicCarlsonMinimalFixedAnchorWindow
          hzero him (himHeight.trans hheight) hdelta
            hreAnchor hreRight
  have hdisjoint : Disjoint low anchor := by
    refine Finset.disjoint_left.mpr ?_
    intro rho hrhoLow hrhoAnchor
    have hreLow :=
      (mem_actualPositiveCarlsonStrip.mp hrhoLow).2.2.2.2
    have hrhoAnchor' := hrhoAnchor
    unfold actualDyadicCarlsonFixedAnchorWindow at hrhoAnchor'
    have hreAnchor := (Finset.mem_filter.mp hrhoAnchor').2.1
    exact (not_lt_of_ge hreLow) hreAnchor
  calc
    actualSelectedHeightMovingCarlsonMiddleMass H delta m =
        ∑ rho ∈ middle,
          ‖pntRelativeZeroContribution (m : ℝ) rho‖ := rfl
    _ ≤ ∑ rho ∈ low ∪ anchor,
          ‖pntRelativeZeroContribution (m : ℝ) rho‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun rho _ _ => norm_nonneg _)
    _ =
        actualSelectedHeightSevenEighthsLowMass H m +
          actualDyadicCarlsonFixedAnchorMass outerAlpha delta
            (dyadicCarlsonLayerSchedule delta) m := by
      rw [Finset.sum_union hdisjoint]
      rfl

/-- Automatic decay of the selected-height middle strip from its fixed-low
and dyadic-anchor pieces. -/
theorem tendsto_actualSelectedHeightMovingMiddleMass_zero_of_dyadic
    {innerAlpha outerAlpha epsilon : ℝ} {delta : ℕ → ℝ}
    (hinner : 0 < innerAlpha)
    (hstrict : innerAlpha < outerAlpha)
    (houter : 0 < outerAlpha)
    (houterUpper : outerAlpha ≤ 1 / 16)
    (hepsilon : 0 < epsilon)
    (hmargin : outerAlpha + epsilon < 1 / 8)
    (selection : UniformNaturalPointGoodHeightSelection)
    (hdeltaNonneg : ∀ m, 0 ≤ delta m)
    (hdelta : ∀ᶠ m : ℕ in atTop, 0 < delta m)
    (hdeltaUpper : ∀ᶠ m : ℕ in atTop, delta m ≤ 1 / 8)
    (hgap : IsCarlsonMovingDyadicLogPowerGap delta) :
    Tendsto
      (actualSelectedHeightMovingCarlsonMiddleMass
        (selectedUniformGoodHeight innerAlpha selection) delta)
      atTop (nhds 0) := by
  let H := selectedUniformGoodHeight innerAlpha selection
  have hlow :
      Tendsto (actualSelectedHeightSevenEighthsLowMass H)
        atTop (nhds 0) :=
    tendsto_actualSelectedHeightSevenEighthsLowMass_zero
      hinner hstrict houter hepsilon hmargin selection
  obtain ⟨A, C₁, C₂, hA, hC₁, hC₂, hanchor⟩ :=
    exists_constants_tendsto_actualDyadicCarlsonMinimalFixedAnchorMass_zero_automatic
      houter houterUpper hdeltaNonneg hdelta hdeltaUpper hgap
  have hheightReal :
      ∀ᶠ x : ℝ in atTop,
        H x ≤ carlsonPolynomialHeight outerAlpha x :=
    eventually_selectedUniformGoodHeight_le_polynomialHeight
      hinner hstrict selection
  have hheight :
      ∀ᶠ m : ℕ in atTop,
        H (m : ℝ) ≤
          carlsonPolynomialHeight outerAlpha (m : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hheightReal
  have hmajor :
      Tendsto
        (fun m =>
          actualSelectedHeightSevenEighthsLowMass H m +
            actualDyadicCarlsonFixedAnchorMass outerAlpha delta
              (dyadicCarlsonLayerSchedule delta) m)
        atTop (nhds 0) :=
    by simpa using hlow.add hanchor
  refine squeeze_zero' ?_ ?_ hmajor
  · exact Filter.Eventually.of_forall fun m => by
      unfold actualSelectedHeightMovingCarlsonMiddleMass
      positivity
  · filter_upwards [hdelta, hheight] with m hm hmHeight
    exact actualSelectedHeightMovingMiddle_le_low_add_dyadicAnchor
      (hdeltaNonneg m) hm hmHeight

/-- A selected-height dynamic zero-free region, stated directly on the
actual zeta zeros visible to the explicit formula. -/
def IsSelectedHeightDynamicZeroFree
    (H : ℝ → ℝ) (delta : ℕ → ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ rho : ℂ,
    RiemannHypothesis.IsNontrivialZero rho →
    0 < rho.im →
    rho.im ≤ H (m : ℝ) →
    rho.re ≤ 1 - delta m

theorem eventually_actualSelectedHeightMovingPositiveRightEdgeCap_of_dynamicZeroFree
    {H : ℝ → ℝ} {delta : ℕ → ℝ}
    (hzeroFree : IsSelectedHeightDynamicZeroFree H delta) :
    ∀ᶠ m : ℕ in atTop,
      ActualSelectedHeightMovingPositiveRightEdgeCap H delta m := by
  filter_upwards [hzeroFree] with m hm
  intro rho hrho
  rcases mem_positiveNontrivialZerosFinset.mp hrho with
    ⟨hzero, him, himHeight⟩
  exact hm rho hzero him himHeight

/-- Complete selected-height PNT transfer from a dynamic zero-free region
and the automatic minimal dyadic Carlson cover. -/
theorem tendsto_relativeChebyshevPsi0Error_of_selectedUniformGoodHeightDyadicCarlson
    {innerAlpha outerAlpha epsilon : ℝ} {delta : ℕ → ℝ}
    (hinner : 0 < innerAlpha)
    (hstrict : innerAlpha < outerAlpha)
    (houter : 0 < outerAlpha)
    (houterUpper : outerAlpha ≤ 1 / 16)
    (hepsilon : 0 < epsilon)
    (hmargin : outerAlpha + epsilon < 1 / 8)
    (selection : UniformNaturalPointGoodHeightSelection)
    (hdeltaNonneg : ∀ m, 0 ≤ delta m)
    (hdelta : ∀ᶠ m : ℕ in atTop, 0 < delta m)
    (hdeltaUpper : ∀ᶠ m : ℕ in atTop, delta m ≤ 1 / 8)
    (hgap : IsCarlsonMovingDyadicLogPowerGap delta)
    (hzeroFree :
      IsSelectedHeightDynamicZeroFree
        (selectedUniformGoodHeight innerAlpha selection) delta) :
    Tendsto (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
      atTop (nhds 0) := by
  have hmiddle :=
    tendsto_actualSelectedHeightMovingMiddleMass_zero_of_dyadic
      hinner hstrict houter houterUpper hepsilon hmargin selection
      hdeltaNonneg hdelta hdeltaUpper hgap
  have hcap :=
    eventually_actualSelectedHeightMovingPositiveRightEdgeCap_of_dynamicZeroFree
      hzeroFree
  have hdeltaCarlson :
      ∀ᶠ m : ℕ in atTop,
        0 < delta m ∧ delta m ≤ 1 / 8 ∧
          128 * outerAlpha * delta m ≤ 1 := by
    filter_upwards [hdelta, hdeltaUpper] with m hm hmUpper
    have hproduct :
        outerAlpha * delta m ≤
          (1 / 16 : ℝ) * (1 / 8 : ℝ) :=
      mul_le_mul houterUpper hmUpper hm.le (by norm_num)
    exact ⟨hm, hmUpper, by nlinarith⟩
  exact
    tendsto_relativeChebyshevPsi0Error_of_selectedUniformGoodHeightMovingCarlson
      hinner hstrict houter hepsilon
      (hmargin.trans (by norm_num)) selection
      hdeltaCarlson
      (isCarlsonMovingQuadraticLogPowerGap_of_dyadic
        hdelta hdeltaUpper hgap)
      hcap hmiddle

end

end PrimeNumberTheorem
