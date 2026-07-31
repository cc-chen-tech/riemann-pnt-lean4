import PrimeNumberTheorem.ZeroDensityLayerBudgetActualPintzCertifiedGoodHeightUnifiedTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetPintzGrid

/-!
# Certified actual Pintz grids and admissible-height cost covers

The finite family of actual good-height selectors is placed in the original
Pintz envelope-grid interface.  The resulting dynamic grid is exactly the
Stack119 grid, so eventual zero-freeness and additive-slack global optimality
refer to the same height schedule used by the unified PNT transfer.

The analytic cost-cover estimate remains an explicit input.
-/

namespace PrimeNumberTheorem

open Filter Topology

/-- The actual certified candidate family as a Pintz envelope dynamic grid. -/
noncomputable def actualPintzCertifiedEnvelopeDynamicGridInput
    {ι : Type*} [Fintype ι] {zeroFree : ℝ → ℝ → Prop}
    (alpha : ℝ) (halpha : 0 < alpha)
    (family : ActualPintzGoodHeightCandidateFamily ι)
    (hzeroFree :
      ∀ᶠ x : ℝ in atTop, ∀ i,
        zeroFree x
          (actualPintzCandidateHeight alpha (family.selector i) x)) :
    PintzEnvelopeDynamicGridInput zeroFree where
  envelope := actualPintzCandidateLowerEnvelope alpha
  candidates := actualPintzCandidateFiniteGrid alpha family
  envelope_tendsto_atTop :=
    actualPintzCandidateLowerEnvelope_tendsto_atTop halpha
  envelope_le_candidates :=
    actualPintzCandidateLowerEnvelope_le alpha family
  eventually_candidate_zeroFree := by
    classical
    filter_upwards [hzeroFree] with x hx T hT
    rcases Finset.mem_image.mp hT with ⟨i, _hi, rfl⟩
    exact hx i

/-- Forgetting the Pintz zero-free certificate recovers definitionally the
same certified dynamic grid used by Stack119. -/
theorem actualPintzCertifiedEnvelopeDynamicGridInput_toDynamicFiniteHeightGrid
    {ι : Type*} [Fintype ι] {zeroFree : ℝ → ℝ → Prop}
    (alpha : ℝ) (halpha : 0 < alpha)
    (family : ActualPintzGoodHeightCandidateFamily ι)
    (hzeroFree :
      ∀ᶠ x : ℝ in atTop, ∀ i,
        zeroFree x
          (actualPintzCandidateHeight alpha (family.selector i) x)) :
    (actualPintzCertifiedEnvelopeDynamicGridInput
      alpha halpha family hzeroFree).toDynamicFiniteHeightGrid =
      actualPintzCertifiedDynamicGrid alpha halpha family :=
  rfl

/-- The original Pintz grid theorem now certifies eventual zero-freeness of
the exact actual-good-height optimizer. -/
theorem eventually_actualPintzCertifiedOptimalHeight_zeroFree
    {ι : Type*} [Fintype ι] {zeroFree : ℝ → ℝ → Prop}
    (cost : ℝ → ℝ → ℝ) (alpha : ℝ) (halpha : 0 < alpha)
    (family : ActualPintzGoodHeightCandidateFamily ι)
    (hzeroFree :
      ∀ᶠ x : ℝ in atTop, ∀ i,
        zeroFree x
          (actualPintzCandidateHeight alpha (family.selector i) x)) :
    ∀ᶠ x : ℝ in atTop,
      zeroFree x
        (actualPintzCertifiedOptimalHeight cost alpha halpha family x) := by
  have hselected :=
    (actualPintzCertifiedEnvelopeDynamicGridInput
      alpha halpha family hzeroFree).eventually_optimalHeight_zeroFree cost
  simpa [actualPintzCertifiedOptimalHeight,
    actualPintzCertifiedEnvelopeDynamicGridInput] using hselected

/-- An analytic additive-slack cost-cover certificate for the actual certified
candidate grid. -/
def ActualPintzCertifiedDynamicCostCover
    {ι : Type*} [Fintype ι]
    (cost : ℝ → ℝ → ℝ) (alpha : ℝ) (halpha : 0 < alpha)
    (family : ActualPintzGoodHeightCandidateFamily ι)
    (admissible : ℝ → ℝ → Prop) (slack : ℝ → ℝ) : Prop :=
  DynamicFiniteGridCostCover cost
    (actualPintzCertifiedDynamicGrid alpha halpha family)
    admissible slack

/-- A certified cost cover upgrades exact finite-family minimization to
additive-slack optimality against every admissible height. -/
theorem actualPintzCertifiedOptimalHeight_le_add_of_costCover
    {ι : Type*} [Fintype ι]
    (cost : ℝ → ℝ → ℝ) (alpha : ℝ) (halpha : 0 < alpha)
    (family : ActualPintzGoodHeightCandidateFamily ι)
    (admissible : ℝ → ℝ → Prop) (slack : ℝ → ℝ)
    (cover : ActualPintzCertifiedDynamicCostCover
      cost alpha halpha family admissible slack)
    {x T : ℝ} (hT : admissible x T) :
    cost x (actualPintzCertifiedOptimalHeight
      cost alpha halpha family x) ≤
      cost x T + slack x :=
  dynamicFiniteGridOptimalHeight_le_add cost
    (actualPintzCertifiedDynamicGrid alpha halpha family)
    admissible slack cover hT

end PrimeNumberTheorem
