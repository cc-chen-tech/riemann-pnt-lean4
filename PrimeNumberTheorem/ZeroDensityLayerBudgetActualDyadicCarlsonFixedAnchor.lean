import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDyadicCarlsonCover

/-!
# A fixed real-part anchor from the dyadic Carlson cover

If the outer dyadic scale satisfies

`1 / 8 <= 2 ^ L * delta <= 1 / 4`,

then the first `L` strips cover every actual positive zeta zero with real part
in `(7 / 8, 1 - delta]`.  The upper half of the same scale interval also
forces every active gap to be at most `1 / 8`.  For polynomial-height exponent
`alpha <= 1 / 16`, this automatically gives the small-parameter condition
`128 * alpha * gap <= 1` used by the moving Carlson transfer.
-/

namespace PrimeNumberTheorem

open Filter Topology
open scoped BigOperators

noncomputable section

/-- The part of the dyadic Carlson union lying in the fixed real-part window
`(7 / 8, 1 - delta]`. -/
noncomputable def actualDyadicCarlsonFixedAnchorWindow
    (alpha : ℝ) (delta : ℕ → ℝ) (layers : ℕ → ℕ) (m : ℕ) : Finset ℂ :=
  (actualDynamicCarlsonGapStripUnion alpha layers
      (dyadicCarlsonGap delta) m).filter
    (fun rho => (7 / 8 : ℝ) < rho.re ∧
      rho.re ≤ 1 - delta m)

/-- PNT relative-kernel mass in the fixed anchored window. -/
noncomputable def actualDyadicCarlsonFixedAnchorMass
    (alpha : ℝ) (delta : ℕ → ℝ) (layers : ℕ → ℕ) (m : ℕ) : ℝ :=
  ∑ rho ∈ actualDyadicCarlsonFixedAnchorWindow alpha delta layers m,
    ‖pntRelativeZeroContribution (m : ℝ) rho‖

theorem actualDyadicCarlsonFixedAnchorMass_nonneg
    (alpha : ℝ) (delta : ℕ → ℝ) (layers : ℕ → ℕ) (m : ℕ) :
    0 ≤ actualDyadicCarlsonFixedAnchorMass alpha delta layers m := by
  unfold actualDyadicCarlsonFixedAnchorMass
  positivity

/-- Controlling the outer dyadic scale controls every active gap. -/
theorem dyadicCarlsonGap_active_of_outer_le
    {alpha : ℝ} {delta : ℕ → ℝ} {m L : ℕ}
    (halphaNonneg : 0 ≤ alpha)
    (halphaUpper : alpha ≤ 1 / 16)
    (hdelta : 0 ≤ delta m)
    (houter : (2 : ℝ) ^ L * delta m ≤ 1 / 4) :
    ∀ i : Fin L,
      dyadicCarlsonGap delta m i.1 ≤ 1 / 8 ∧
      128 * alpha * dyadicCarlsonGap delta m i.1 ≤ 1 := by
  intro i
  have hpow :
      (2 : ℝ) ^ (i.1 + 1) ≤ (2 : ℝ) ^ L :=
    pow_le_pow_right₀ (by norm_num)
      (Nat.succ_le_iff.mpr i.isLt)
  have hscaled :
      (2 : ℝ) ^ (i.1 + 1) * delta m ≤
        (2 : ℝ) ^ L * delta m :=
    mul_le_mul_of_nonneg_right hpow hdelta
  have htwice :
      2 * dyadicCarlsonGap delta m i.1 ≤ 1 / 4 := by
    calc
      2 * dyadicCarlsonGap delta m i.1 =
          (2 : ℝ) ^ (i.1 + 1) * delta m := by
            unfold dyadicCarlsonGap
            rw [pow_succ]
            ring
      _ ≤ (2 : ℝ) ^ L * delta m := hscaled
      _ ≤ 1 / 4 := houter
  have hgapNonneg :
      0 ≤ dyadicCarlsonGap delta m i.1 := by
    unfold dyadicCarlsonGap
    positivity
  have hgap :
      dyadicCarlsonGap delta m i.1 ≤ 1 / 8 := by
    norm_num at htwice ⊢
    linarith
  refine ⟨hgap, ?_⟩
  have hproduct :
      alpha * dyadicCarlsonGap delta m i.1 ≤
        (1 / 16 : ℝ) * (1 / 8 : ℝ) :=
    mul_le_mul halphaUpper hgap hgapNonneg (by norm_num)
  nlinarith

/-- The lower outer-scale bound moves the dyadic cover past the fixed anchor
`7 / 8`. -/
theorem mem_actualDyadicCarlsonFixedAnchorWindow
    {alpha : ℝ} {delta : ℕ → ℝ} {layers : ℕ → ℕ} {m : ℕ} {rho : ℂ}
    (hzero : RiemannHypothesis.IsNontrivialZero rho)
    (him : 0 < rho.im)
    (himHeight : rho.im ≤ carlsonPolynomialHeight alpha (m : ℝ))
    (houterLower :
      (1 / 8 : ℝ) ≤
        (2 : ℝ) ^ (layers m) * delta m)
    (hreAnchor : (7 / 8 : ℝ) < rho.re)
    (hreUpper : rho.re ≤ 1 - delta m) :
    rho ∈ actualDyadicCarlsonFixedAnchorWindow
      alpha delta layers m := by
  have hreLower :
      1 - (2 : ℝ) ^ (layers m) * delta m < rho.re := by
    linarith
  have hunion :
      rho ∈ actualDynamicCarlsonGapStripUnion alpha layers
        (dyadicCarlsonGap delta) m :=
    mem_actualDynamicDyadicCarlsonGapStripUnion
      hzero him himHeight hreLower hreUpper
  simp [actualDyadicCarlsonFixedAnchorWindow, hunion,
    hreAnchor, hreUpper]

/-- Restricting the dyadic union to the fixed anchor window cannot increase
its nonnegative PNT kernel mass. -/
theorem actualDyadicCarlsonFixedAnchorMass_le_union
    (alpha : ℝ) (delta : ℕ → ℝ) (layers : ℕ → ℕ) (m : ℕ) :
    actualDyadicCarlsonFixedAnchorMass alpha delta layers m ≤
      ∑ rho ∈ actualDynamicCarlsonGapStripUnion alpha layers
          (dyadicCarlsonGap delta) m,
        ‖pntRelativeZeroContribution (m : ℝ) rho‖ := by
  unfold actualDyadicCarlsonFixedAnchorMass
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset _ _)
    (fun rho _ _ => norm_nonneg _)

/-- Decay of the full dyadic union implies decay in the fixed anchor
window. -/
theorem tendsto_actualDyadicCarlsonFixedAnchorMass_zero_of_union
    {alpha : ℝ} {delta : ℕ → ℝ} {layers : ℕ → ℕ}
    (hunion :
      Tendsto
        (fun m =>
          ∑ rho ∈ actualDynamicCarlsonGapStripUnion alpha layers
              (dyadicCarlsonGap delta) m,
            ‖pntRelativeZeroContribution (m : ℝ) rho‖)
        atTop (𝓝 0)) :
    Tendsto
      (actualDyadicCarlsonFixedAnchorMass alpha delta layers)
      atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ hunion
  · exact Filter.Eventually.of_forall
      (actualDyadicCarlsonFixedAnchorMass_nonneg alpha delta layers)
  · exact Filter.Eventually.of_forall
      (actualDyadicCarlsonFixedAnchorMass_le_union alpha delta layers)

/-- Concrete fixed-anchor Carlson transfer.  The dyadic scale sandwich
provides all active-gap hypotheses automatically. -/
theorem exists_constants_tendsto_actualDyadicCarlsonFixedAnchorMass_zero
    {alpha : ℝ} {delta : ℕ → ℝ} {layers : ℕ → ℕ}
    (halpha : 0 < alpha)
    (halphaUpper : alpha ≤ 1 / 16)
    (hdeltaNonneg : ∀ m, 0 ≤ delta m)
    (hdelta : ∀ᶠ m : ℕ in atTop, 0 < delta m)
    (hscale :
      ∀ᶠ m : ℕ in atTop,
        (1 / 8 : ℝ) ≤
            (2 : ℝ) ^ (layers m) * delta m ∧
          (2 : ℝ) ^ (layers m) * delta m ≤ 1 / 4)
    (hmargin :
      IsCarlsonMovingQuadraticLogPowerLayerCountGap
        delta layers) :
    ∃ A C₁ C₂ : ℝ,
      0 ≤ A ∧
      1 ≤ C₁ ∧
      1 ≤ C₂ ∧
      (ActualDynamicCarlsonGapFamilyHeightConditions C₁ C₂ alpha layers
          (dyadicCarlsonGap delta) →
        Tendsto
          (actualDyadicCarlsonFixedAnchorMass alpha delta layers)
          atTop (𝓝 0)) := by
  have hactive :
      ∀ᶠ m : ℕ in atTop,
        ∀ i : Fin (layers m),
          dyadicCarlsonGap delta m i.1 ≤ 1 / 8 ∧
          128 * alpha *
              dyadicCarlsonGap delta m i.1 ≤ 1 := by
    filter_upwards [hscale] with m hm
    exact dyadicCarlsonGap_active_of_outer_le
      halpha.le halphaUpper (hdeltaNonneg m) hm.2
  obtain ⟨A, C₁, C₂, hA, hC₁, hC₂, htransfer⟩ :=
    exists_constants_tendsto_actualDynamicDyadicCarlsonGapStripUnion_mass_zero
      halpha hdeltaNonneg hdelta hactive hmargin
  refine ⟨A, C₁, C₂, hA, hC₁, hC₂, ?_⟩
  intro hheight
  exact tendsto_actualDyadicCarlsonFixedAnchorMass_zero_of_union
    (htransfer hheight)

end

end PrimeNumberTheorem
