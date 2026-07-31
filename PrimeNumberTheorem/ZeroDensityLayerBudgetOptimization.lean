import PrimeNumberTheorem.ZeroDensityLayerBudgetDynamic

/-!
# Constructive finite-grid optimization of explicit-formula heights

An analytic explicit formula normally leaves a truncation height to be chosen.
`IsOptimalHeight` records a choice that has already been proved optimal.  This
module supplies the complementary finite construction: on every nonempty
finite set of positive candidate heights, an optimizer exists and is selected
canonically by classical choice.

The resulting height is exact on the candidate grid.  If the grid has a
certified cost-cover property with slack `ε`, the same selected height is
automatically `ε`-optimal among all admissible heights.  Thus an analytic
discretization estimate can be separated cleanly from the finite optimization
step checked here.
-/

namespace PrimeNumberTheorem

/-- A finite, nonempty collection of positive explicit-formula heights. -/
structure FiniteHeightGrid where
  heights : Finset ℝ
  nonempty : heights.Nonempty
  positive : ∀ T ∈ heights, 0 < T

/-- `T` minimizes `cost` on the certified finite height grid. -/
structure IsFiniteGridOptimizer (cost : ℝ → ℝ) (grid : FiniteHeightGrid)
    (T : ℝ) : Prop where
  mem : T ∈ grid.heights
  minimal : ∀ U ∈ grid.heights, cost T ≤ cost U

/-- Every finite nonempty height grid has an exact cost minimizer. -/
theorem exists_finiteGridOptimizer (cost : ℝ → ℝ) (grid : FiniteHeightGrid) :
    ∃ T, IsFiniteGridOptimizer cost grid T := by
  classical
  obtain ⟨T, hT, hmin⟩ :=
    Finset.exists_min_image grid.heights cost grid.nonempty
  exact ⟨T, hT, hmin⟩

/-- The selected exact minimizer on a finite height grid. -/
noncomputable def finiteGridOptimalHeight (cost : ℝ → ℝ)
    (grid : FiniteHeightGrid) : ℝ :=
  Classical.choose (exists_finiteGridOptimizer cost grid)

theorem finiteGridOptimalHeight_spec (cost : ℝ → ℝ)
    (grid : FiniteHeightGrid) :
    IsFiniteGridOptimizer cost grid (finiteGridOptimalHeight cost grid) :=
  Classical.choose_spec (exists_finiteGridOptimizer cost grid)

theorem finiteGridOptimalHeight_mem (cost : ℝ → ℝ)
    (grid : FiniteHeightGrid) :
    finiteGridOptimalHeight cost grid ∈ grid.heights :=
  (finiteGridOptimalHeight_spec cost grid).mem

theorem finiteGridOptimalHeight_pos (cost : ℝ → ℝ)
    (grid : FiniteHeightGrid) :
    0 < finiteGridOptimalHeight cost grid :=
  grid.positive _ (finiteGridOptimalHeight_mem cost grid)

theorem finiteGridOptimalHeight_le_of_mem (cost : ℝ → ℝ)
    (grid : FiniteHeightGrid) {U : ℝ} (hU : U ∈ grid.heights) :
    cost (finiteGridOptimalHeight cost grid) ≤ cost U :=
  (finiteGridOptimalHeight_spec cost grid).minimal U hU

/--
The grid approximates every admissible height in cost, with additive slack
`slack`.  This is the sole analytic input needed to upgrade finite minimization
to a global near-optimality statement.
-/
structure FiniteGridCostCover (cost : ℝ → ℝ) (grid : FiniteHeightGrid)
    (admissible : ℝ → Prop) (slack : ℝ) : Prop where
  exists_candidate :
    ∀ T, admissible T →
      ∃ U ∈ grid.heights, cost U ≤ cost T + slack

/--
The finite-grid optimizer is globally near-optimal whenever the candidate grid
has a certified cost-cover property.
-/
theorem finiteGridOptimalHeight_le_add
    (cost : ℝ → ℝ) (grid : FiniteHeightGrid)
    (admissible : ℝ → Prop) (slack : ℝ)
    (cover : FiniteGridCostCover cost grid admissible slack)
    {T : ℝ} (hT : admissible T) :
    cost (finiteGridOptimalHeight cost grid) ≤ cost T + slack := by
  obtain ⟨U, hU, hcost⟩ := cover.exists_candidate T hT
  exact (finiteGridOptimalHeight_le_of_mem cost grid hU).trans hcost

/--
An explicit-formula estimate valid at every positive height can be evaluated
automatically at the selected finite-grid optimizer.
-/
theorem explicitFormula_upper_at_finiteGridOptimalHeight
    (error : ℝ) (cost : ℝ → ℝ) (grid : FiniteHeightGrid)
    (hupper : ∀ T, 0 < T → |error| ≤ cost T) :
    |error| ≤ cost (finiteGridOptimalHeight cost grid) :=
  hupper _ (finiteGridOptimalHeight_pos cost grid)

/--
Combined automatic transfer: choose the finite-grid optimizer, evaluate the
explicit formula there, and retain a comparison with every admissible height.
-/
theorem exists_explicitFormula_finiteGrid_optimal
    (error : ℝ) (cost : ℝ → ℝ) (grid : FiniteHeightGrid)
    (admissible : ℝ → Prop) (slack : ℝ)
    (hupper : ∀ T, 0 < T → |error| ≤ cost T)
    (cover : FiniteGridCostCover cost grid admissible slack) :
    ∃ T, 0 < T ∧ |error| ≤ cost T ∧
      ∀ U, admissible U → cost T ≤ cost U + slack := by
  refine ⟨finiteGridOptimalHeight cost grid,
    finiteGridOptimalHeight_pos cost grid,
    explicitFormula_upper_at_finiteGridOptimalHeight error cost grid hupper, ?_⟩
  intro U hU
  exact finiteGridOptimalHeight_le_add cost grid admissible slack cover hU

end PrimeNumberTheorem
