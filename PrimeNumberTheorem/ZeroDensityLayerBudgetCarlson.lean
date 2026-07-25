import PrimeNumberTheorem.ZeroDensityLayerBudget
import PrimeNumberTheorem.CarlsonAsymptotic

open Filter
open scoped BigOperators

namespace PrimeNumberTheorem

variable {ρ E : Type*}

/-- A real-valued majorant for a two-parameter zero-counting function. -/
def ZeroDensityMajorant
    (count : ℝ → ℝ → ℕ) (majorant : ℝ → ℝ → ℝ) : Prop :=
  ∀ σ T, (count σ T : ℝ) ≤ majorant σ T

/-- Per-layer occupancies certified by a zero-density input. -/
structure LayerDensityCertificate
    [DecidableEq ρ] [NormedAddCommGroup E]
    (C : LayerCertificate ρ E) where
  occupancy : Fin C.layerCount → ℝ
  occupancy_nonneg : ∀ i, 0 ≤ occupancy i
  occupancy_bound :
    ∀ i, ((C.layer i).card : ℝ) ≤ occupancy i

/--
Turn a global density majorant into layer occupancies at chosen strip
thresholds.  The separate `hcount` premise is the geometric fact that a strip
is contained in the corresponding cumulative zero set.
-/
noncomputable def LayerDensityCertificate.ofMajorant
    [DecidableEq ρ] [NormedAddCommGroup E]
    (C : LayerCertificate ρ E)
    (count : ℝ → ℝ → ℕ)
    (majorant : ℝ → ℝ → ℝ)
    (sigma : Fin C.layerCount → ℝ)
    (T : ℝ)
    (hmajorant : ZeroDensityMajorant count majorant)
    (hcount :
      ∀ i, ((C.layer i).card : ℝ) ≤ (count (sigma i) T : ℝ)) :
    LayerDensityCertificate C where
  occupancy := fun i => majorant (sigma i) T
  occupancy_nonneg := by
    intro i
    exact le_trans (Nat.cast_nonneg (count (sigma i) T))
      (hmajorant (sigma i) T)
  occupancy_bound := by
    intro i
    exact le_trans (hcount i) (hmajorant (sigma i) T)

/-- Apply a certified density occupancy bound to the abstract kernel budget. -/
theorem norm_tail_sum_le_of_layerDensity
    [DecidableEq ρ] [NormedAddCommGroup E]
    (C : LayerCertificate ρ E)
    (density : LayerDensityCertificate C)
    (term : ρ → E)
    (kernelWeight : Fin C.layerCount → ℝ)
    (hkernel :
      ∀ i z, z ∈ C.layer i → ‖term z‖ ≤ kernelWeight i)
    (hkernel_nonneg : ∀ i, 0 ≤ kernelWeight i) :
    ‖∑ z ∈ C.tail, term z‖ ≤
      layeredTailBudget C density.occupancy kernelWeight :=
  norm_tail_sum_le_layeredTailBudget C term density.occupancy kernelWeight
    density.occupancy_bound hkernel hkernel_nonneg

/--
Direct zero-density-majorant form of the layered tail estimate.

Carlson's theorem enters only through `hmajorant`; the remaining input
`hcount` records containment of each real-part strip in the cumulative count.
-/
theorem norm_tail_sum_le_of_zeroDensityMajorant
    [DecidableEq ρ] [NormedAddCommGroup E]
    (C : LayerCertificate ρ E)
    (count : ℝ → ℝ → ℕ)
    (majorant : ℝ → ℝ → ℝ)
    (sigma : Fin C.layerCount → ℝ)
    (T : ℝ)
    (term : ρ → E)
    (kernelWeight : Fin C.layerCount → ℝ)
    (hmajorant : ZeroDensityMajorant count majorant)
    (hcount :
      ∀ i, ((C.layer i).card : ℝ) ≤ (count (sigma i) T : ℝ))
    (hkernel :
      ∀ i z, z ∈ C.layer i → ‖term z‖ ≤ kernelWeight i)
    (hkernel_nonneg : ∀ i, 0 ≤ kernelWeight i) :
    ‖∑ z ∈ C.tail, term z‖ ≤
      layeredTailBudget C (fun i => majorant (sigma i) T) kernelWeight := by
  let density :=
    LayerDensityCertificate.ofMajorant C count majorant sigma T
      hmajorant hcount
  exact norm_tail_sum_le_of_layerDensity C density term kernelWeight
    hkernel hkernel_nonneg

/--
The eventual pointwise majorant extracted from Carlson's fixed-real-part
`IsBigO` theorem.

The norm on the model term avoids adding artificial positivity hypotheses at
small heights.  Applications normally combine `bound` with an admissible
height schedule tending to infinity.
-/
structure CarlsonEventualMajorant (sigma : ℝ) where
  C : ℝ
  C_nonneg : 0 ≤ C
  bound :
    ∀ᶠ T in atTop,
      (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
        C * ‖T ^ (4 * sigma * (1 - sigma)) * (Real.log T) ^ 4‖

/-- Carlson's theorem supplies an eventual density certificate at each fixed
real-part threshold strictly between `1/2` and `1`. -/
theorem exists_carlsonEventualMajorant
    {sigma : ℝ} (hσ : 1 / 2 < sigma) (hσ1 : sigma < 1) :
    Nonempty (CarlsonEventualMajorant sigma) := by
  rcases
      (CarlsonZeroDensity.carlson_zeroDensity_isBigO hσ hσ1).exists_nonneg with
    ⟨C, hC, hbigO⟩
  refine ⟨⟨C, hC, ?_⟩⟩
  filter_upwards [hbigO.bound] with T hT
  have hcount_nonneg :
      0 ≤ (ZeroDensity.zeroDensityCount sigma T : ℝ) :=
    Nat.cast_nonneg _
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg hcount_nonneg] using hT

end PrimeNumberTheorem
