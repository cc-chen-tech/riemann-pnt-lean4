import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBoundaryMassAllocation
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonPositiveZeroIndexInjective
import PrimeNumberTheorem.ZeroDensityLayerBudgetVisibleClusterCoefficientMass

/-!
# Comparing captured Carlson mass with finite visible-cluster mass

Injectivity of the actual Carlson positive-zero indexing turns the indexed
captured boundary mass into a submass of the finite distinct-zero coefficient
mass.  Relative to a seed `S₀ ⊆ S`, the mass captured by the extension
`S \ S₀` plus the mass left outside `S` is exactly the mass that was outside
`S₀`.
-/

namespace PrimeNumberTheorem

open scoped BigOperators

noncomputable section

/-- Indexed positive-zero boundary mass captured by a finite complex cluster
is bounded by that cluster's full multiplicity-weighted coefficient mass. -/
theorem actualCarlsonCapturedBoundaryMass_le_finiteVisibleClusterCoefficientMass
    {sigma beta : ℝ} (S : Finset ℂ)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1) :
    actualCarlsonCapturedBoundaryMass
        (sigma := sigma) beta S ≤
      finiteVisibleClusterCoefficientMass S := by
  let weight : ℂ → ℝ :=
    fun rho => (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖
  let f : ℂ → ℝ :=
    fun rho => if rho ∈ S then weight rho else 0
  have hfSupport : ∀ rho ∉ S, f rho = 0 := by
    intro rho hrho
    simp [f, hrho]
  have hfSummable : Summable f :=
    summable_of_ne_finset_zero hfSupport
  have hfNonneg : ∀ rho, 0 ≤ f rho := by
    intro rho
    by_cases hrho : rho ∈ S
    · simp [f, hrho, weight]
      positivity
    · simp [f, hrho]
  have hfCompSummable :
      Summable
        (f ∘
          (@actualCarlsonPositiveZero sigma)) :=
    hfSummable.comp_injective
      actualCarlsonPositiveZero_injective
  have hterm :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonCapturedBoundaryTerm beta S index ≤
          (f ∘ actualCarlsonPositiveZero) index := by
    intro index
    by_cases hre : actualCarlsonPositiveZeroRealPart index = beta
    · by_cases hmem : actualCarlsonPositiveZero index ∈ S
      · simp [actualCarlsonCapturedBoundaryTerm, f, hre, hmem, weight,
          actualCarlsonPositiveZeroWeight_eq_coefficient]
      · simp [actualCarlsonCapturedBoundaryTerm, f, hre, hmem]
    · by_cases hmem : actualCarlsonPositiveZero index ∈ S
      · simp [actualCarlsonCapturedBoundaryTerm, f, hre, hmem, weight]
        positivity
      · simp [actualCarlsonCapturedBoundaryTerm, f, hre, hmem]
  calc
    actualCarlsonCapturedBoundaryMass
          (sigma := sigma) beta S =
        ∑' index : ActualCarlsonPositiveZeroIndex sigma,
          actualCarlsonCapturedBoundaryTerm beta S index := rfl
    _ ≤
        ∑' index : ActualCarlsonPositiveZeroIndex sigma,
          (f ∘ actualCarlsonPositiveZero) index :=
      (summable_actualCarlsonCapturedBoundaryTerm S hhalf hone).tsum_le_tsum
        hterm hfCompSummable
    _ ≤ ∑' rho : ℂ, f rho :=
      tsum_comp_le_tsum_of_inj
        hfSummable hfNonneg actualCarlsonPositiveZero_injective
    _ = ∑ rho ∈ S, f rho :=
      tsum_eq_sum hfSupport
    _ = finiteVisibleClusterCoefficientMass S := by
      unfold finiteVisibleClusterCoefficientMass
      simp [f, weight]

/-- Captured indexed mass splits over a finite seed and its extension. -/
theorem actualCarlsonCapturedBoundaryMass_eq_seed_add_extension
    {sigma beta : ℝ} {S₀ S : Finset ℂ}
    (hsub : S₀ ⊆ S)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1) :
    actualCarlsonCapturedBoundaryMass
        (sigma := sigma) beta S =
      actualCarlsonCapturedBoundaryMass
          (sigma := sigma) beta S₀ +
        actualCarlsonCapturedBoundaryMass
          (sigma := sigma) beta (S \ S₀) := by
  have hterm :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonCapturedBoundaryTerm beta S index =
          actualCarlsonCapturedBoundaryTerm beta S₀ index +
            actualCarlsonCapturedBoundaryTerm beta (S \ S₀) index := by
    intro index
    by_cases hre : actualCarlsonPositiveZeroRealPart index = beta
    · by_cases hseed : actualCarlsonPositiveZero index ∈ S₀
      · have hmem : actualCarlsonPositiveZero index ∈ S :=
          hsub hseed
        simp [actualCarlsonCapturedBoundaryTerm, hre, hseed, hmem]
      · by_cases hmem : actualCarlsonPositiveZero index ∈ S
        · have hdiff : actualCarlsonPositiveZero index ∈ S \ S₀ :=
            Finset.mem_sdiff.mpr ⟨hmem, hseed⟩
          simp [actualCarlsonCapturedBoundaryTerm, hre, hseed, hmem, hdiff]
        · have hdiff : actualCarlsonPositiveZero index ∉ S \ S₀ := by
            intro hin
            exact hmem (Finset.mem_sdiff.mp hin).1
          simp [actualCarlsonCapturedBoundaryTerm, hre, hseed, hmem, hdiff]
    · simp [actualCarlsonCapturedBoundaryTerm, hre]
  unfold actualCarlsonCapturedBoundaryMass
  rw [←
    (summable_actualCarlsonCapturedBoundaryTerm S₀ hhalf hone).tsum_add
      (summable_actualCarlsonCapturedBoundaryTerm (S \ S₀) hhalf hone)]
  exact tsum_congr hterm

/-- Relative to a seed, captured extension mass and final outside mass form an
exact partition of the seed's original outside boundary mass. -/
theorem
    actualCarlsonCapturedBoundaryMass_extension_add_outside_eq_seedOutside
    {sigma beta : ℝ} {S₀ S : Finset ℂ}
    (hsub : S₀ ⊆ S)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1) :
    actualCarlsonCapturedBoundaryMass
          (sigma := sigma) beta (S \ S₀) +
        actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S =
      actualCarlsonOutsideClusterBoundaryMass
        (sigma := sigma) beta S₀ := by
  have hseed :=
    actualCarlsonTotalBoundaryMass_eq_captured_add_outside
      (beta := beta) S₀ hhalf hone
  have hfinal :=
    actualCarlsonTotalBoundaryMass_eq_captured_add_outside
      (beta := beta) S hhalf hone
  have hsplit :=
    actualCarlsonCapturedBoundaryMass_eq_seed_add_extension
      (beta := beta) hsub hhalf hone
  rw [hsplit] at hfinal
  linarith

/-- Simultaneously small extension coefficient mass and final outside mass
are possible only if the seed's original outside boundary mass fits inside
their summed allowances. -/
theorem actualCarlsonSeedOutside_lt_add_of_extensionMass_lt_of_outside_lt
    {sigma beta addedAllowance outsideAllowance : ℝ}
    {S₀ S : Finset ℂ}
    (hsub : S₀ ⊆ S)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hadded :
      finiteVisibleClusterCoefficientMass (S \ S₀) <
        addedAllowance)
    (houtside :
      actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S < outsideAllowance) :
    actualCarlsonOutsideClusterBoundaryMass
        (sigma := sigma) beta S₀ <
      addedAllowance + outsideAllowance := by
  have hcaptured :
      actualCarlsonCapturedBoundaryMass
          (sigma := sigma) beta (S \ S₀) <
        addedAllowance :=
    lt_of_le_of_lt
      (actualCarlsonCapturedBoundaryMass_le_finiteVisibleClusterCoefficientMass
        (S \ S₀) hhalf hone)
      hadded
  rw [←
    actualCarlsonCapturedBoundaryMass_extension_add_outside_eq_seedOutside
      hsub hhalf hone]
  exact add_lt_add hcaptured houtside

end

end PrimeNumberTheorem
