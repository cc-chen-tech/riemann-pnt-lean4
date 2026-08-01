import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTHybridLowLayerOptimizer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZetaStripExcludingClusterTransfer
import PrimeNumberTheorem.GlobalZeroCount

/-!
# Actual zeta-kernel majorant for a hybrid low-real-part layer

Carlson cannot be applied to a bucket whose lower threshold is at or left of
the critical line.  For such a layer this file instead uses the global
analytic-multiplicity bound `O(T log T)`.

The result is pointwise and applies to the genuine multiplicity-weighted
relative PNT kernel outside a finite main cluster.  Combined with a
real-part endpoint `rho.re <= tau` and denominator guard
`kappa <= ‖rho‖`, it produces the explicit majorant

`C * T * (1 + log (T + 6)) * kappa⁻¹ * x^(tau - 1)`.

No lower-threshold hypothesis is needed.  Thus this is the actual-kernel
replacement for the low half of a hybrid global/Carlson bucket profile.
-/

open scoped BigOperators

namespace PrimeNumberTheorem

/-- Explicit global-count majorant for one actual low-real-part PNT layer. -/
noncomputable def actualHybridGlobalLowLayerMajorant
    (C T kappa tau x : ℝ) : ℝ :=
  (C * T * (1 + Real.log (T + 6))) *
    stripEndpointRelativeKernelBudget kappa tau x

/--
Every outside-cluster bucket layer has analytic multiplicity mass at most the
global multiplicity of all nontrivial zeros up to the same height.
-/
theorem
    PositiveZeroOutsideClusterBucketInput.layer_multiplicityMass_le_globalZeroMultiplicity
    {T : ℝ} {S : Finset ℂ} {n : ℕ}
    (input : PositiveZeroOutsideClusterBucketInput T S n)
    (i : Fin n) :
    analyticMultiplicityMass (input.layer i) ≤
      ExplicitFormulaAux.globalZeroMultiplicity T := by
  have hsubset :
      input.layer i ⊆ nontrivialZerosFinset T := by
    intro rho hrho
    have hOutside :=
      mem_positiveNontrivialZerosOutsideClusterFinset.mp
        (Finset.mem_filter.mp hrho).1
    apply mem_nontrivialZerosFinset.mpr
    refine ⟨hOutside.1, ?_⟩
    rw [abs_of_pos hOutside.2.1]
    exact hOutside.2.2.1
  unfold analyticMultiplicityMass
    ExplicitFormulaAux.globalZeroMultiplicity
  exact
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun _ _ _ => Nat.cast_nonneg _)

/--
Pointwise actual-kernel bound for one outside-cluster layer using global
multiplicity rather than a Carlson strip count.
-/
theorem
    dynamicPositiveOutsideClusterPNTLayerNorm_le_globalMultiplicity_mul_stripEndpoint
    {n : ℕ} {T : ℝ → ℝ} {S : Finset ℂ}
    (input :
      (x : ℝ) → PositiveZeroOutsideClusterBucketInput (T x) S n)
    (i : Fin n) (tau kappa : ℝ)
    (hkappa : 0 < kappa)
    (hnorm :
      ∀ x, ∀ rho ∈ (input x).layer i, kappa ≤ ‖rho‖)
    (hre :
      ∀ x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau)
    {x : ℝ} (hx : 1 ≤ x) :
    |dynamicPositiveOutsideClusterPNTLayerNorm T S input i x| ≤
      ExplicitFormulaAux.globalZeroMultiplicity (T x) *
        stripEndpointRelativeKernelBudget kappa tau x := by
  have hkernel :
      ∀ rho ∈ (input x).layer i,
        ‖pntRelativeSimpleZeroKernel x rho‖ ≤
          stripEndpointRelativeKernelBudget kappa tau x := by
    intro rho hrho
    exact
      norm_pntRelativeSimpleZeroKernel_le_stripEndpoint
        hx hkappa (hnorm x rho hrho) (hre x rho hrho)
  have hkernelNonneg :
      0 ≤ stripEndpointRelativeKernelBudget kappa tau x :=
    stripEndpointRelativeKernelBudget_nonneg
      (zero_le_one.trans hx) hkappa.le
  calc
    |dynamicPositiveOutsideClusterPNTLayerNorm T S input i x| =
        dynamicPositiveOutsideClusterPNTLayerNorm T S input i x := by
      exact abs_of_nonneg (norm_nonneg _)
    _ ≤ ∑ rho ∈ (input x).layer i,
          ‖pntRelativeZeroContribution x rho‖ := by
      exact norm_sum_le _ _
    _ ≤ stripEndpointRelativeKernelBudget kappa tau x *
          analyticMultiplicityMass ((input x).layer i) :=
      sum_norm_pntRelativeZeroContribution_le_kernel_mul_multiplicityMass
        ((input x).layer i) x
        (stripEndpointRelativeKernelBudget kappa tau x)
        hkernelNonneg hkernel
    _ ≤ stripEndpointRelativeKernelBudget kappa tau x *
          ExplicitFormulaAux.globalZeroMultiplicity (T x) :=
      mul_le_mul_of_nonneg_left
        ((input x).layer_multiplicityMass_le_globalZeroMultiplicity i)
        hkernelNonneg
    _ = ExplicitFormulaAux.globalZeroMultiplicity (T x) *
          stripEndpointRelativeKernelBudget kappa tau x := by
      ring

/--
The global `O(T log T)` theorem supplies one nonnegative coefficient
controlling the genuine low-layer zeta kernel at every height `T >= 4`.
-/
theorem
    exists_globalCoefficient_dynamicPositiveOutsideClusterPNTLayerNorm_le_actualHybridMajorant
    {n : ℕ} {T : ℝ → ℝ} {S : Finset ℂ}
    (input :
      (x : ℝ) → PositiveZeroOutsideClusterBucketInput (T x) S n)
    (i : Fin n) (tau kappa : ℝ)
    (hkappa : 0 < kappa)
    (hnorm :
      ∀ x, ∀ rho ∈ (input x).layer i, kappa ≤ ‖rho‖)
    (hre :
      ∀ x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : ℝ, 1 ≤ x → 4 ≤ T x →
        |dynamicPositiveOutsideClusterPNTLayerNorm T S input i x| ≤
          actualHybridGlobalLowLayerMajorant
            C (T x) kappa tau x := by
  rcases ExplicitFormulaAux.exists_globalZeroMultiplicity_le_mul_log with
    ⟨C, hC, hglobal⟩
  refine ⟨C, hC, ?_⟩
  intro x hx hT
  have hkernelNonneg :
      0 ≤ stripEndpointRelativeKernelBudget kappa tau x :=
    stripEndpointRelativeKernelBudget_nonneg
      (zero_le_one.trans hx) hkappa.le
  calc
    |dynamicPositiveOutsideClusterPNTLayerNorm T S input i x| ≤
        ExplicitFormulaAux.globalZeroMultiplicity (T x) *
          stripEndpointRelativeKernelBudget kappa tau x :=
      dynamicPositiveOutsideClusterPNTLayerNorm_le_globalMultiplicity_mul_stripEndpoint
        input i tau kappa hkappa hnorm hre hx
    _ ≤ (C * T x * (1 + Real.log (T x + 6))) *
          stripEndpointRelativeKernelBudget kappa tau x :=
      mul_le_mul_of_nonneg_right (hglobal (T x) hT) hkernelNonneg
    _ = actualHybridGlobalLowLayerMajorant
          C (T x) kappa tau x := by
      rfl

end PrimeNumberTheorem
