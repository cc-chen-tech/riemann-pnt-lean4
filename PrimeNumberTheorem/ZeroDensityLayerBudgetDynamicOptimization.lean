import PrimeNumberTheorem.ZeroDensityLayerBudgetBidirectional

/-!
# Pointwise optimal dynamic truncation heights

Finite-grid optimization previously selected a height for one fixed cost
function.  Here both the cost and the candidate grid vary with the scale `x`.
The selected pointwise minimizer is therefore a genuine function `T = T(x)`.

Each grid carries a lower envelope tending to infinity.  Membership of the
selected minimizer then proves `T(x) → ∞` automatically, while finite-grid
cost covers retain exact or additive-slack optimality against all admissible
heights.
-/

namespace PrimeNumberTheorem

/--
A scale-dependent finite height grid whose every candidate lies above a lower
envelope tending to infinity.
-/
structure DynamicFiniteHeightGrid where
  grid : ℝ → FiniteHeightGrid
  lowerEnvelope : ℝ → ℝ
  lowerEnvelope_tendsto_atTop :
    Filter.Tendsto lowerEnvelope Filter.atTop Filter.atTop
  lowerEnvelope_le :
    ∀ x T, T ∈ (grid x).heights → lowerEnvelope x ≤ T

/-- Pointwise exact minimizer of `cost x` on the finite grid at scale `x`. -/
noncomputable def dynamicFiniteGridOptimalHeight
    (cost : ℝ → ℝ → ℝ) (grid : DynamicFiniteHeightGrid)
    (x : ℝ) : ℝ :=
  finiteGridOptimalHeight (cost x) (grid.grid x)

theorem dynamicFiniteGridOptimalHeight_mem
    (cost : ℝ → ℝ → ℝ) (grid : DynamicFiniteHeightGrid)
    (x : ℝ) :
    dynamicFiniteGridOptimalHeight cost grid x ∈
      (grid.grid x).heights :=
  finiteGridOptimalHeight_mem (cost x) (grid.grid x)

theorem dynamicFiniteGridOptimalHeight_pos
    (cost : ℝ → ℝ → ℝ) (grid : DynamicFiniteHeightGrid)
    (x : ℝ) :
    0 < dynamicFiniteGridOptimalHeight cost grid x :=
  finiteGridOptimalHeight_pos (cost x) (grid.grid x)

/-- The selected dynamic height minimizes cost exactly on each finite grid. -/
theorem dynamicFiniteGridOptimalHeight_le_of_mem
    (cost : ℝ → ℝ → ℝ) (grid : DynamicFiniteHeightGrid)
    {x T : ℝ} (hT : T ∈ (grid.grid x).heights) :
    cost x (dynamicFiniteGridOptimalHeight cost grid x) ≤ cost x T :=
  finiteGridOptimalHeight_le_of_mem (cost x) (grid.grid x) hT

/--
The pointwise minimizer tends to infinity because it always lies above the
grid's diverging lower envelope.
-/
theorem dynamicFiniteGridOptimalHeight_tendsto_atTop
    (cost : ℝ → ℝ → ℝ) (grid : DynamicFiniteHeightGrid) :
    Filter.Tendsto (dynamicFiniteGridOptimalHeight cost grid)
      Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro b
  have hlower :
      ∀ᶠ x in Filter.atTop, b ≤ grid.lowerEnvelope x :=
    (Filter.tendsto_atTop.1 grid.lowerEnvelope_tendsto_atTop) b
  filter_upwards [hlower] with x hbx
  exact hbx.trans
    (grid.lowerEnvelope_le x _
      (dynamicFiniteGridOptimalHeight_mem cost grid x))

/--
At every scale, the finite grid approximates every admissible height in cost.
-/
structure DynamicFiniteGridCostCover
    (cost : ℝ → ℝ → ℝ) (grid : DynamicFiniteHeightGrid)
    (admissible : ℝ → ℝ → Prop) (slack : ℝ → ℝ) : Prop where
  cover :
    ∀ x,
      FiniteGridCostCover (cost x) (grid.grid x)
        (admissible x) (slack x)

/-- Pointwise additive-slack optimality against every admissible height. -/
theorem dynamicFiniteGridOptimalHeight_le_add
    (cost : ℝ → ℝ → ℝ) (grid : DynamicFiniteHeightGrid)
    (admissible : ℝ → ℝ → Prop) (slack : ℝ → ℝ)
    (cover : DynamicFiniteGridCostCover cost grid admissible slack)
    {x T : ℝ} (hT : admissible x T) :
    cost x (dynamicFiniteGridOptimalHeight cost grid x) ≤
      cost x T + slack x :=
  finiteGridOptimalHeight_le_add
    (cost x) (grid.grid x) (admissible x) (slack x)
      (cover.cover x) hT

/--
An explicit-formula estimate valid at every positive height is automatically
valid at the selected dynamic optimizer.
-/
theorem dynamicExplicitFormula_upper_at_dynamicFiniteGridOptimalHeight
    (error : ℝ → ℝ) (cost : ℝ → ℝ → ℝ)
    (grid : DynamicFiniteHeightGrid)
    (hupper : ∀ x T, 0 < T → |error x| ≤ cost x T)
    (x : ℝ) :
    |error x| ≤
      cost x (dynamicFiniteGridOptimalHeight cost grid x) :=
  hupper x _ (dynamicFiniteGridOptimalHeight_pos cost grid x)

/--
Automatic construction of a positive, diverging, pointwise near-optimal
explicit-formula height schedule.
-/
theorem exists_dynamicFiniteGridOptimalHeight
    (error : ℝ → ℝ) (cost : ℝ → ℝ → ℝ)
    (grid : DynamicFiniteHeightGrid)
    (admissible : ℝ → ℝ → Prop) (slack : ℝ → ℝ)
    (hupper : ∀ x T, 0 < T → |error x| ≤ cost x T)
    (cover : DynamicFiniteGridCostCover cost grid admissible slack) :
    ∃ height : ℝ → ℝ,
      Filter.Tendsto height Filter.atTop Filter.atTop ∧
      (∀ x, 0 < height x ∧ |error x| ≤ cost x (height x)) ∧
      ∀ x T, admissible x T →
        cost x (height x) ≤ cost x T + slack x := by
  refine ⟨dynamicFiniteGridOptimalHeight cost grid,
    dynamicFiniteGridOptimalHeight_tendsto_atTop cost grid, ?_, ?_⟩
  · intro x
    exact
      ⟨dynamicFiniteGridOptimalHeight_pos cost grid x,
        dynamicExplicitFormula_upper_at_dynamicFiniteGridOptimalHeight
          error cost grid hupper x⟩
  · intro x T hT
    exact dynamicFiniteGridOptimalHeight_le_add
      cost grid admissible slack cover hT

end PrimeNumberTheorem
