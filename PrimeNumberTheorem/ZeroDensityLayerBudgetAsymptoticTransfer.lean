import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlson
import PrimeNumberTheorem.ZeroDensityLayerBudgetOmegaTransfer

/-!
# Asymptotic dynamic-layer budgets and Omega transfer

This module is the interface between Carlson-style dynamic zero-layer bounds
and the perturbative Omega theorems.  The analytic side supplies a bound for
the complementary-zero remainder along a height `T = T(x)`.  If that bound
tends to zero, every fixed positive main-cluster amplitude eventually dominates
it, and the recurrent finite-cluster witness survives in the full error term.

No implementation detail of the separately owned complementary-bound module is
used here.
-/

namespace PrimeNumberTheorem

/-- Evaluate a two-parameter layer budget along a dynamic height schedule. -/
def dynamicLayerBudgetAlong (height : ℝ → ℝ)
    (layerBudget : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  layerBudget x (height x)

/--
A dynamic layer budget eventually dominates the complementary-zero remainder
along the selected height schedule.
-/
structure DynamicLayerRemainderCertificate
    (remainder height : ℝ → ℝ)
    (layerBudget : ℝ → ℝ → ℝ) : Prop where
  eventually_bound :
    ∀ᶠ x in Filter.atTop,
      |remainder x| ≤ dynamicLayerBudgetAlong height layerBudget x

/--
If the dynamic layer budget is eventually below half the main amplitude, its
remainder satisfies the perturbative Omega interface.
-/
theorem isEventuallyHalfSmall_of_dynamicLayerBudget
    {remainder height : ℝ → ℝ} {layerBudget : ℝ → ℝ → ℝ}
    {amplitude : ℝ}
    (certificate :
      DynamicLayerRemainderCertificate remainder height layerBudget)
    (hbudget :
      ∀ᶠ x in Filter.atTop,
        dynamicLayerBudgetAlong height layerBudget x ≤ amplitude / 2) :
    IsEventuallyHalfSmall remainder amplitude := by
  filter_upwards [certificate.eventually_bound, hbudget] with x hrem hbudgetx
  exact hrem.trans hbudgetx

/--
A real-valued dynamic layer budget converging to zero is eventually below half
of every fixed positive amplitude.
-/
theorem eventually_dynamicLayerBudget_le_half_of_tendsto_zero
    {height : ℝ → ℝ} {layerBudget : ℝ → ℝ → ℝ}
    {amplitude : ℝ} (hamplitude : 0 < amplitude)
    (hzero :
      Filter.Tendsto (dynamicLayerBudgetAlong height layerBudget)
        Filter.atTop (nhds 0)) :
    ∀ᶠ x in Filter.atTop,
      dynamicLayerBudgetAlong height layerBudget x ≤ amplitude / 2 := by
  have hhalf : (0 : ℝ) < amplitude / 2 := by linarith
  have heventually :
      ∀ᶠ x in Filter.atTop,
        dynamicLayerBudgetAlong height layerBudget x ∈ Set.Iio (amplitude / 2) :=
    hzero.eventually (Iio_mem_nhds hhalf)
  filter_upwards [heventually] with x hx
  exact hx.le

/--
Convergence of the dynamic layer budget to zero automatically supplies the
eventual-half-small remainder certificate.
-/
theorem isEventuallyHalfSmall_of_dynamicLayerBudget_tendsto_zero
    {remainder height : ℝ → ℝ} {layerBudget : ℝ → ℝ → ℝ}
    {amplitude : ℝ} (hamplitude : 0 < amplitude)
    (certificate :
      DynamicLayerRemainderCertificate remainder height layerBudget)
    (hzero :
      Filter.Tendsto (dynamicLayerBudgetAlong height layerBudget)
        Filter.atTop (nhds 0)) :
    IsEventuallyHalfSmall remainder amplitude :=
  isEventuallyHalfSmall_of_dynamicLayerBudget certificate
    (eventually_dynamicLayerBudget_le_half_of_tendsto_zero hamplitude hzero)

/--
Dynamic Carlson-layer-to-Omega transfer.  Once the complementary budget along
`T(x)` tends to zero, a recurrent main cluster forces an absolute Omega bound
for the complete explicit-formula error.
-/
theorem hasFarNormWitness_add_of_dynamicLayerBudget_tendsto_zero
    {error main remainder height : ℝ → ℝ}
    {layerBudget : ℝ → ℝ → ℝ} {amplitude : ℝ}
    (hamplitude : 0 < amplitude)
    (hmain : HasFarNormWitness main amplitude)
    (certificate :
      DynamicLayerRemainderCertificate remainder height layerBudget)
    (hzero :
      Filter.Tendsto (dynamicLayerBudgetAlong height layerBudget)
        Filter.atTop (nhds 0))
    (hdecomp : ∀ x, error x = main x + remainder x) :
    HasFarNormWitness error (amplitude / 2) :=
  hasFarNormWitness_add_of_eventuallyHalfSmall hmain
    (isEventuallyHalfSmall_of_dynamicLayerBudget_tendsto_zero
      hamplitude certificate hzero)
    hdecomp

/--
Dynamic Carlson-layer-to-Omega-plus/minus transfer.  Positive and negative
main-cluster recurrence both survive the same vanishing complementary budget.
-/
theorem hasFarSignedWitnesses_add_of_dynamicLayerBudget_tendsto_zero
    {error main remainder height : ℝ → ℝ}
    {layerBudget : ℝ → ℝ → ℝ} {amplitude : ℝ}
    (hamplitude : 0 < amplitude)
    (hmain : HasFarSignedWitnesses main amplitude)
    (certificate :
      DynamicLayerRemainderCertificate remainder height layerBudget)
    (hzero :
      Filter.Tendsto (dynamicLayerBudgetAlong height layerBudget)
        Filter.atTop (nhds 0))
    (hdecomp : ∀ x, error x = main x + remainder x) :
    HasFarSignedWitnesses error (amplitude / 2) :=
  hasFarSignedWitnesses_add_of_eventuallyHalfSmall hmain
    (isEventuallyHalfSmall_of_dynamicLayerBudget_tendsto_zero
      hamplitude certificate hzero)
    hdecomp

end PrimeNumberTheorem
