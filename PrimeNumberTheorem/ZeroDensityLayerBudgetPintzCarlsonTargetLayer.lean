import PrimeNumberTheorem.ZeroDensityLayerBudgetTwoHeightComplementSplit

/-!
# Pintz--Carlson certificates for target-amplitude zero layers

For one dynamic real-part strip, Carlson controls the number of zeros while a
Pintz envelope controls the kernel attached to each zero.  Their product is a
majorant for the strip contribution.  This file packages the exact normalized
criterion that turns such a product majorant into target-amplitude
negligibility, and then aggregates finitely many certified strips.

No concrete zero-density estimate is asserted here.  A caller must provide the
actual count bound, kernel bound, strip-sum domination, and normalized decay.
-/

namespace PrimeNumberTheorem

/-- Auditable data showing that a zero layer is negligible relative to a target
amplitude by multiplying a Carlson-style count budget with a Pintz-style
pointwise kernel budget. -/
structure PintzCarlsonTargetLayerBudget
    (amplitude layer countBudget kernelBudget : ℝ → ℝ) : Prop where
  /-- The zero-count majorant is eventually nonnegative. -/
  count_eventually_nonneg :
    ∀ᶠ x in Filter.atTop, 0 ≤ countBudget x
  /-- The single-zero kernel majorant is eventually nonnegative. -/
  kernel_eventually_nonneg :
    ∀ᶠ x in Filter.atTop, 0 ≤ kernelBudget x
  /-- Count times pointwise kernel dominates the full multiplicity-weighted
  contribution of this strip. -/
  layer_abs_le_count_mul_kernel :
    ∀ᶠ x in Filter.atTop,
      |layer x| ≤ countBudget x * kernelBudget x
  /-- The Pintz--Carlson product is small after target-amplitude normalization. -/
  normalized_product_tendsto_zero :
    Filter.Tendsto
      (fun x => countBudget x * kernelBudget x / amplitude x)
      Filter.atTop (nhds 0)

/-- A certified Pintz--Carlson strip budget yields the normalized complementary
estimate required by the oscillation transfer layer. -/
theorem PintzCarlsonTargetLayerBudget.targetAmplitudeNegligible
    {amplitude layer countBudget kernelBudget : ℝ → ℝ}
    (hamplitude : ∀ᶠ x in Filter.atTop, 0 < amplitude x)
    (budget :
      PintzCarlsonTargetLayerBudget
        amplitude layer countBudget kernelBudget) :
    TargetAmplitudeNegligible amplitude layer := by
  unfold TargetAmplitudeNegligible
  refine squeeze_zero' ?_ ?_ budget.normalized_product_tendsto_zero
  · filter_upwards [hamplitude] with x hx
    exact div_nonneg (abs_nonneg _) (le_of_lt hx)
  · filter_upwards [hamplitude,
      budget.layer_abs_le_count_mul_kernel] with x hx hlayer
    exact div_le_div_of_nonneg_right hlayer (le_of_lt hx)

/-- Finitely many dynamically chosen real-part strips, each with its own
Carlson count and Pintz kernel budget, aggregate to a negligible complement. -/
theorem targetAmplitudeNegligible_finset_sum_of_pintzCarlsonBudgets
    {ι : Type*} {amplitude : ℝ → ℝ}
    (hamplitude : ∀ᶠ x in Filter.atTop, 0 < amplitude x)
    (layers : Finset ι)
    (term countBudget kernelBudget : ι → ℝ → ℝ)
    (hbudget :
      ∀ i ∈ layers,
        PintzCarlsonTargetLayerBudget amplitude (term i)
          (countBudget i) (kernelBudget i)) :
    TargetAmplitudeNegligible amplitude
      (fun x => layers.sum (fun i => term i x)) := by
  apply targetAmplitudeNegligible_finset_sum hamplitude
  intro i hi
  exact (hbudget i hi).targetAmplitudeNegligible hamplitude

/-- Construct a two-height complementary certificate from independently
certified Pintz--Carlson budgets for the inner and annular zero layers. -/
theorem twoHeightTargetComplementControl_of_pintzCarlsonBudgets
    {amplitude innerComplement heightAnnulus : ℝ → ℝ}
    {innerCount innerKernel annulusCount annulusKernel : ℝ → ℝ}
    (hamplitude : ∀ᶠ x in Filter.atTop, 0 < amplitude x)
    (hinner :
      PintzCarlsonTargetLayerBudget amplitude innerComplement
        innerCount innerKernel)
    (hannulus :
      PintzCarlsonTargetLayerBudget amplitude heightAnnulus
        annulusCount annulusKernel) :
    TwoHeightTargetComplementControl
      amplitude innerComplement heightAnnulus where
  amplitude_eventually_pos := hamplitude
  inner_negligible := hinner.targetAmplitudeNegligible hamplitude
  annulus_negligible := hannulus.targetAmplitudeNegligible hamplitude

end PrimeNumberTheorem
