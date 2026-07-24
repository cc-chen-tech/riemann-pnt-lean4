import PrimeNumberTheorem.ZeroDensityLayerBudgetAsymptoticTransfer

/-!
# Finite real-part layer decay

Carlson estimates are applied strip by strip.  This module proves the finite
aggregation step needed by a dynamic explicit formula: if every real-part
layer budget tends to zero along `T = T(x)`, then their total finite budget
tends to zero.  The result plugs directly into the asymptotic Omega transfer.
-/

namespace PrimeNumberTheorem

/-- Sum the contributions of finitely many real-part layers. -/
def finiteLayerBudget {ι : Type*} [DecidableEq ι]
    (layers : Finset ι) (layerTerm : ι → ℝ → ℝ → ℝ)
    (x T : ℝ) : ℝ :=
  ∑ i in layers, layerTerm i x T

/-- Evaluate the finite real-part layer sum along a dynamic height schedule. -/
def finiteLayerBudgetAlong {ι : Type*} [DecidableEq ι]
    (layers : Finset ι) (height : ℝ → ℝ)
    (layerTerm : ι → ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  finiteLayerBudget layers layerTerm x (height x)

/-- Every individual layer contribution vanishes along the dynamic height. -/
structure FiniteDynamicLayerDecay {ι : Type*} [DecidableEq ι]
    (layers : Finset ι) (height : ℝ → ℝ)
    (layerTerm : ι → ℝ → ℝ → ℝ) : Prop where
  layer_tendsto_zero :
    ∀ i ∈ layers,
      Filter.Tendsto (fun x => layerTerm i x (height x))
        Filter.atTop (nhds 0)

/--
Finite-layer closure: stripwise convergence to zero implies convergence of the
total dynamic layer budget to zero.
-/
theorem finiteLayerBudgetAlong_tendsto_zero
    {ι : Type*} [DecidableEq ι]
    (layers : Finset ι) (height : ℝ → ℝ)
    (layerTerm : ι → ℝ → ℝ → ℝ) :
    (∀ i ∈ layers,
      Filter.Tendsto (fun x => layerTerm i x (height x))
        Filter.atTop (nhds 0)) →
    Filter.Tendsto (finiteLayerBudgetAlong layers height layerTerm)
      Filter.atTop (nhds 0) := by
  classical
  induction layers using Finset.induction_on with
  | empty =>
      intro h
      simp [finiteLayerBudgetAlong, finiteLayerBudget]
  | @insert a s ha ih =>
      intro h
      have haZero :
          Filter.Tendsto (fun x => layerTerm a x (height x))
            Filter.atTop (nhds 0) :=
        h a (by simp)
      have hsZero :
          Filter.Tendsto (finiteLayerBudgetAlong s height layerTerm)
            Filter.atTop (nhds 0) :=
        ih (by
          intro i hi
          exact h i (by simp [hi]))
      simpa [finiteLayerBudgetAlong, finiteLayerBudget, ha] using
        haZero.add hsZero

theorem FiniteDynamicLayerDecay.total_tendsto_zero
    {ι : Type*} [DecidableEq ι]
    {layers : Finset ι} {height : ℝ → ℝ}
    {layerTerm : ι → ℝ → ℝ → ℝ}
    (decay : FiniteDynamicLayerDecay layers height layerTerm) :
    Filter.Tendsto (finiteLayerBudgetAlong layers height layerTerm)
      Filter.atTop (nhds 0) :=
  finiteLayerBudgetAlong_tendsto_zero layers height layerTerm
    decay.layer_tendsto_zero

/--
The generic two-parameter dynamic budget evaluator agrees with the finite
real-part layer sum.
-/
theorem dynamicLayerBudgetAlong_finiteLayerBudget
    {ι : Type*} [DecidableEq ι]
    (layers : Finset ι) (height : ℝ → ℝ)
    (layerTerm : ι → ℝ → ℝ → ℝ) :
    dynamicLayerBudgetAlong height (finiteLayerBudget layers layerTerm) =
      finiteLayerBudgetAlong layers height layerTerm :=
  rfl

/--
Finite Carlson-layer decay plus a remainder domination certificate forces an
absolute Omega bound for the complete error.
-/
theorem hasFarNormWitness_add_of_finiteLayerDecay
    {ι : Type*} [DecidableEq ι]
    {layers : Finset ι}
    {error main remainder height : ℝ → ℝ}
    {layerTerm : ι → ℝ → ℝ → ℝ} {amplitude : ℝ}
    (hamplitude : 0 < amplitude)
    (hmain : HasFarNormWitness main amplitude)
    (remainderCertificate :
      DynamicLayerRemainderCertificate remainder height
        (finiteLayerBudget layers layerTerm))
    (decay : FiniteDynamicLayerDecay layers height layerTerm)
    (hdecomp : ∀ x, error x = main x + remainder x) :
    HasFarNormWitness error (amplitude / 2) := by
  apply hasFarNormWitness_add_of_dynamicLayerBudget_tendsto_zero
    hamplitude hmain remainderCertificate
  · simpa [dynamicLayerBudgetAlong_finiteLayerBudget] using
      decay.total_tendsto_zero
  · exact hdecomp

/--
The same finite Carlson-layer certificate transfers recurrent values of both
signs, yielding an Omega-plus/minus conclusion.
-/
theorem hasFarSignedWitnesses_add_of_finiteLayerDecay
    {ι : Type*} [DecidableEq ι]
    {layers : Finset ι}
    {error main remainder height : ℝ → ℝ}
    {layerTerm : ι → ℝ → ℝ → ℝ} {amplitude : ℝ}
    (hamplitude : 0 < amplitude)
    (hmain : HasFarSignedWitnesses main amplitude)
    (remainderCertificate :
      DynamicLayerRemainderCertificate remainder height
        (finiteLayerBudget layers layerTerm))
    (decay : FiniteDynamicLayerDecay layers height layerTerm)
    (hdecomp : ∀ x, error x = main x + remainder x) :
    HasFarSignedWitnesses error (amplitude / 2) := by
  apply hasFarSignedWitnesses_add_of_dynamicLayerBudget_tendsto_zero
    hamplitude hmain remainderCertificate
  · simpa [dynamicLayerBudgetAlong_finiteLayerBudget] using
      decay.total_tendsto_zero
  · exact hdecomp

end PrimeNumberTheorem
