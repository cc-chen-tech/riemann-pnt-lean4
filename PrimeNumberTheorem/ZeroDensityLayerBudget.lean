import Mathlib

open scoped BigOperators

namespace PrimeNumberTheorem

variable {ρ E : Type*}

/-- The half-open real-part strip `(lo, hi]` inside a finite zero set. -/
noncomputable def realPartLayer [DecidableEq ρ]
    (zeros : Finset ρ) (re : ρ → ℝ) (lo hi : ℝ) : Finset ρ :=
  zeros.filter fun z => lo < re z ∧ re z ≤ hi

/--
A finite partition certificate for a zero tail.

The decomposition field is deliberately extensional in the summand.  Concrete
strip constructions prove it once; analytic users only need the resulting
finite-sum identity.
-/
structure LayerCertificate
    (ρ E : Type*) [DecidableEq ρ] [NormedAddCommGroup E] where
  tail : Finset ρ
  layerCount : ℕ
  layer : Fin layerCount → Finset ρ
  pairwise_disjoint :
    ∀ ⦃i j⦄, i ≠ j → Disjoint (layer i) (layer j)
  sum_decomposition :
    ∀ term : ρ → E,
      ∑ z ∈ tail, term z = ∑ i, ∑ z ∈ layer i, term z

/--
A finite family of explicit half-open real-part strips whose sums decompose a
chosen zero tail.

The certificate keeps the analytic cutoff data visible.  Its decomposition
field is the proof obligation that the chosen strips cover the tail exactly;
after that proof, every kernel summand can reuse the same partition.
-/
structure RealPartLayering
    (ρ E : Type*) [DecidableEq ρ] [NormedAddCommGroup E] where
  tail : Finset ρ
  re : ρ → ℝ
  layerCount : ℕ
  lower : Fin layerCount → ℝ
  upper : Fin layerCount → ℝ
  strict_strip : ∀ i, lower i < upper i
  pairwise_disjoint :
    ∀ ⦃i j⦄, i ≠ j →
      Disjoint
        (realPartLayer tail re (lower i) (upper i))
        (realPartLayer tail re (lower j) (upper j))
  sum_decomposition :
    ∀ term : ρ → E,
      ∑ z ∈ tail, term z =
        ∑ i, ∑ z ∈ realPartLayer tail re (lower i) (upper i), term z

/-- Forget the cutoff geometry while retaining its exact finite partition. -/
noncomputable def RealPartLayering.certificate
    [DecidableEq ρ] [NormedAddCommGroup E]
    (L : RealPartLayering ρ E) : LayerCertificate ρ E where
  tail := L.tail
  layerCount := L.layerCount
  layer := fun i => realPartLayer L.tail L.re (L.lower i) (L.upper i)
  pairwise_disjoint := L.pairwise_disjoint
  sum_decomposition := L.sum_decomposition

/-- Sum of the occupancy majorant times the kernel majorant on every layer. -/
def layeredTailBudget
    [DecidableEq ρ] [NormedAddCommGroup E]
    (C : LayerCertificate ρ E)
    (occupancy kernelWeight : Fin C.layerCount → ℝ) : ℝ :=
  ∑ i, occupancy i * kernelWeight i

/--
The abstract density-to-kernel transfer inequality.

No zeta-specific fact occurs here: a zero-density theorem supplies
`hoccupancy`, while an explicit-formula kernel estimate supplies `hkernel`.
-/
theorem norm_tail_sum_le_layeredTailBudget
    [DecidableEq ρ] [NormedAddCommGroup E]
    (C : LayerCertificate ρ E)
    (term : ρ → E)
    (occupancy kernelWeight : Fin C.layerCount → ℝ)
    (hoccupancy :
      ∀ i, ((C.layer i).card : ℝ) ≤ occupancy i)
    (hkernel :
      ∀ i z, z ∈ C.layer i → ‖term z‖ ≤ kernelWeight i)
    (hkernel_nonneg : ∀ i, 0 ≤ kernelWeight i) :
    ‖∑ z ∈ C.tail, term z‖ ≤
      layeredTailBudget C occupancy kernelWeight := by
  have hLayer :
      ∀ i, ‖∑ z ∈ C.layer i, term z‖ ≤
        occupancy i * kernelWeight i := by
    intro i
    calc
      ‖∑ z ∈ C.layer i, term z‖
          ≤ ∑ z ∈ C.layer i, ‖term z‖ := norm_sum_le _ _
      _ ≤ ∑ _z ∈ C.layer i, kernelWeight i := by
        exact Finset.sum_le_sum fun z hz => hkernel i z hz
      _ = ((C.layer i).card : ℝ) * kernelWeight i := by simp
      _ ≤ occupancy i * kernelWeight i :=
        mul_le_mul_of_nonneg_right (hoccupancy i) (hkernel_nonneg i)
  rw [C.sum_decomposition term]
  calc
    ‖∑ i, ∑ z ∈ C.layer i, term z‖
        ≤ ∑ i, ‖∑ z ∈ C.layer i, term z‖ := norm_sum_le _ _
    _ ≤ ∑ i, occupancy i * kernelWeight i :=
      Finset.sum_le_sum fun i _ => hLayer i
    _ = layeredTailBudget C occupancy kernelWeight := rfl

end PrimeNumberTheorem
