import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlson

open Filter

namespace PrimeNumberTheorem

/-- Minimal side conditions for evaluating a truncated formula at `(x,T)`. -/
def AdmissibleHeight (heightThreshold x T : ℝ) : Prop :=
  2 ≤ x ∧ heightThreshold ≤ T

/--
A truncation height selected as a function of the evaluation point.

The convergence field is what transports eventual zero-density estimates from
height space to the `x`-scale.
-/
structure DynamicHeightSchedule (x₀ heightThreshold : ℝ) where
  height : ℝ → ℝ
  admissible :
    ∀ x, x₀ ≤ x → AdmissibleHeight heightThreshold x (height x)
  tendsToAtTop : Tendsto height atTop atTop

/-- The three auditable components of a dynamic explicit-formula bound. -/
def explicitFormulaCost
    (layerCost truncationCost compactCost : ℝ → ℝ → ℝ)
    (x T : ℝ) : ℝ :=
  layerCost x T + truncationCost x T + compactCost x T

/--
Certificate that `T x` minimizes the supplied cost among all admissible
heights at `x`.
-/
def IsOptimalHeight
    (cost : ℝ → ℝ → ℝ)
    (admissible : ℝ → ℝ → Prop)
    (T : ℝ → ℝ) : Prop :=
  ∀ x, admissible x (T x) ∧
    ∀ U, admissible x U → cost x (T x) ≤ cost x U

/-- Specialize a fixed-height explicit-formula estimate at a dynamic height. -/
theorem dynamic_explicit_formula_upper
    {pntError : ℝ → ℂ}
    {layerCost truncationCost compactCost : ℝ → ℝ → ℝ}
    {x₀ heightThreshold : ℝ}
    (schedule : DynamicHeightSchedule x₀ heightThreshold)
    (hformula :
      ∀ x T, AdmissibleHeight heightThreshold x T →
        ‖pntError x‖ ≤
          explicitFormulaCost layerCost truncationCost compactCost x T) :
    ∀ x, x₀ ≤ x →
      ‖pntError x‖ ≤
        explicitFormulaCost layerCost truncationCost compactCost x
          (schedule.height x) := by
  intro x hx
  exact hformula x (schedule.height x) (schedule.admissible x hx)

/-- An optimal-height certificate improves every admissible fixed-height cost. -/
theorem optimal_height_upper
    {pntError : ℝ → ℂ}
    {cost : ℝ → ℝ → ℝ}
    {admissible : ℝ → ℝ → Prop}
    {T : ℝ → ℝ}
    (hoptimal : IsOptimalHeight cost admissible T)
    (hbound :
      ∀ x U, admissible x U → ‖pntError x‖ ≤ cost x U) :
    ∀ x U, admissible x U →
      ‖pntError x‖ ≤ cost x (T x) ∧
        cost x (T x) ≤ cost x U := by
  intro x U hU
  exact ⟨hbound x (T x) (hoptimal x).1, (hoptimal x).2 U hU⟩

/-- Pull Carlson's eventual height estimate back along a dynamic schedule. -/
theorem CarlsonEventualMajorant.along_schedule
    {sigma : ℝ}
    (M : CarlsonEventualMajorant sigma)
    {T : ℝ → ℝ}
    (hT : Tendsto T atTop atTop) :
    ∀ᶠ x in atTop,
      (ZeroDensity.zeroDensityCount sigma (T x) : ℝ) ≤
        M.C *
          ‖(T x) ^ (4 * sigma * (1 - sigma)) *
            (Real.log (T x)) ^ 4‖ :=
  hT.eventually M.bound

end PrimeNumberTheorem
