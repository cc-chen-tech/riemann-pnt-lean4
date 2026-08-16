import Mathlib.Data.Finsupp.Basic
import Mathlib.Topology.Basic

/-!
# From all finite sections to a continuous infinite quadratic form

This module isolates the exact topological bridge needed after finite Weil
matrix certification.

There are two logically separate steps:

1. positivity of every finite section implies positivity on finitely
   supported coordinate vectors;
2. if those vectors embed densely into the target space and the infinite
   quadratic form is continuous, positivity extends to the whole space.

A certificate for one cutoff, such as `N = 200`, does not satisfy the first
hypothesis.  No RH statement is made here.
-/

namespace WeilExtremalKernels

open Set
open scoped BigOperators

/-- Quadratic form of an ambient kernel restricted to a finite index set. -/
def finiteSectionForm
    (Q : Nat -> Nat -> Real)
    (indices : Finset Nat)
    (x : Nat ->₀ Real) : Real :=
  ∑ i in indices, ∑ j in indices, x i * Q i j * x j

/-- The kernel quadratic form on a finitely supported vector. -/
def finitelySupportedKernelForm
    (Q : Nat -> Nat -> Real)
    (x : Nat ->₀ Real) : Real :=
  finiteSectionForm Q x.support x

/-- Positivity of every finite section implies positivity for every finitely
supported coordinate vector. -/
theorem finitelySupportedKernelForm_nonneg_of_all_finite_sections
    (Q : Nat -> Nat -> Real)
    (hsections :
      forall (indices : Finset Nat) (x : Nat ->₀ Real),
        x.support ⊆ indices ->
        0 <= finiteSectionForm Q indices x) :
    forall x : Nat ->₀ Real,
      0 <= finitelySupportedKernelForm Q x := by
  intro x
  exact hsections x.support x (by rfl)

/-- A continuous real-valued function that is nonnegative on a dense set is
nonnegative everywhere. -/
theorem nonneg_of_dense_continuous
    {X : Type*} [TopologicalSpace X]
    (q : X -> Real) (S : Set X)
    (hdense : Dense S)
    (hcontinuous : Continuous q)
    (hS : forall x, x ∈ S -> 0 <= q x) :
    forall x, 0 <= q x := by
  have hclosed : IsClosed (q ⁻¹' Ici 0) :=
    isClosed_Ici.preimage hcontinuous
  have hsubset : S ⊆ q ⁻¹' Ici 0 := by
    intro x hx
    exact hS x hx
  have hclosure : closure S ⊆ q ⁻¹' Ici 0 :=
    closure_minimal hsubset hclosed
  intro x
  apply hclosure
  rw [hdense.closure_eq]
  exact mem_univ x

/-- Complete finite-to-infinite transfer interface.

To use this theorem for a Weil space, one must supply:

* all finite-section inequalities, not one selected cutoff;
* a dense coordinate embedding;
* continuity of the target quadratic form;
* exact agreement between the target form and the finite kernel formula on
  embedded finitely supported vectors. -/
theorem infinite_nonneg_of_all_finite_sections
    {X : Type*} [TopologicalSpace X]
    (Q : Nat -> Nat -> Real)
    (q : X -> Real)
    (embed : (Nat ->₀ Real) -> X)
    (hsections :
      forall (indices : Finset Nat) (x : Nat ->₀ Real),
        x.support ⊆ indices ->
        0 <= finiteSectionForm Q indices x)
    (hdense : Dense (Set.range embed))
    (hcontinuous : Continuous q)
    (hagrees :
      forall x : Nat ->₀ Real,
        q (embed x) = finitelySupportedKernelForm Q x) :
    forall y : X, 0 <= q y := by
  apply nonneg_of_dense_continuous q (Set.range embed) hdense hcontinuous
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  rw [hagrees]
  exact finitelySupportedKernelForm_nonneg_of_all_finite_sections
    Q hsections x

end WeilExtremalKernels
