import PrimeNumberTheorem.ZeroDensityLayerBudgetExplicitFormulaKernel

/-!
# Multiplicity-weighted explicit-formula kernels

Carlson's zero count is weighted by analytic multiplicity.  The PNT zero term
must therefore be split into multiplicity times a simple kernel before applying
the density estimate; counting zeros and retaining multiplicity inside a
pointwise majorant would account for multiplicity incorrectly.
-/

open Complex
open scoped BigOperators ComplexConjugate

namespace PrimeNumberTheorem

/-- The relative PNT kernel for one copy of a zero, without analytic
multiplicity. -/
noncomputable def pntRelativeSimpleZeroKernel (x : ℝ) (ρ : ℂ) : ℂ :=
  ((x : ℂ)⁻¹) * (-((x : ℂ) ^ ρ / ρ))

/-- Real-valued analytic multiplicity mass of a finite zero set. -/
noncomputable def analyticMultiplicityMass (s : Finset ℂ) : ℝ :=
  ∑ ρ ∈ s, (analyticOrderNatAt riemannZeta ρ : ℝ)

theorem pntRelativeZeroContribution_eq_multiplicity_mul_simpleKernel
    (x : ℝ) (ρ : ℂ) :
    pntRelativeZeroContribution x ρ =
      (analyticOrderNatAt riemannZeta ρ : ℂ) *
        pntRelativeSimpleZeroKernel x ρ := by
  simp only [pntRelativeZeroContribution, pntFiniteZeroContribution,
    pntExplicitFormulaZeroTerm, pntRelativeSimpleZeroKernel]
  ring

theorem norm_pntRelativeZeroContribution_eq_multiplicity_mul_norm
    (x : ℝ) (ρ : ℂ) :
    ‖pntRelativeZeroContribution x ρ‖ =
      (analyticOrderNatAt riemannZeta ρ : ℝ) *
        ‖pntRelativeSimpleZeroKernel x ρ‖ := by
  rw [pntRelativeZeroContribution_eq_multiplicity_mul_simpleKernel, norm_mul]
  simp

theorem sum_norm_pntRelativeZeroContribution_eq_weightedKernel
    (s : Finset ℂ) (x : ℝ) :
    (∑ ρ ∈ s, ‖pntRelativeZeroContribution x ρ‖) =
      ∑ ρ ∈ s, (analyticOrderNatAt riemannZeta ρ : ℝ) *
        ‖pntRelativeSimpleZeroKernel x ρ‖ := by
  apply Finset.sum_congr rfl
  intro ρ hρ
  exact norm_pntRelativeZeroContribution_eq_multiplicity_mul_norm x ρ

/-- A pointwise bound for the simple kernel is multiplied by analytic
multiplicity mass exactly once. -/
theorem sum_norm_pntRelativeZeroContribution_le_kernel_mul_multiplicityMass
    (s : Finset ℂ) (x K : ℝ) (hK : 0 ≤ K)
    (hkernel : ∀ ρ ∈ s, ‖pntRelativeSimpleZeroKernel x ρ‖ ≤ K) :
    (∑ ρ ∈ s, ‖pntRelativeZeroContribution x ρ‖) ≤
      K * analyticMultiplicityMass s := by
  rw [sum_norm_pntRelativeZeroContribution_eq_weightedKernel]
  calc
    (∑ ρ ∈ s, (analyticOrderNatAt riemannZeta ρ : ℝ) *
        ‖pntRelativeSimpleZeroKernel x ρ‖) ≤
        ∑ ρ ∈ s, (analyticOrderNatAt riemannZeta ρ : ℝ) * K := by
      apply Finset.sum_le_sum
      intro ρ hρ
      exact mul_le_mul_of_nonneg_left (hkernel ρ hρ) (by positivity)
    _ = K * analyticMultiplicityMass s := by
      rw [analyticMultiplicityMass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ρ hρ
      ring

theorem sum_norm_pntRelativeZeroContribution_le_kernel_mul_of_mass_le
    (s : Finset ℂ) (x K D : ℝ) (hK : 0 ≤ K)
    (hkernel : ∀ ρ ∈ s, ‖pntRelativeSimpleZeroKernel x ρ‖ ≤ K)
    (hmass : analyticMultiplicityMass s ≤ D) :
    (∑ ρ ∈ s, ‖pntRelativeZeroContribution x ρ‖) ≤ K * D :=
  (sum_norm_pntRelativeZeroContribution_le_kernel_mul_multiplicityMass
    s x K hK hkernel).trans (mul_le_mul_of_nonneg_left hmass hK)

/-- Layer-level interface matching Carlson's multiplicity-weighted zero count.
The remaining structural task is to derive `hmass` automatically from the
bucket inclusion. -/
theorem PositiveZeroBucketInput.sum_norm_pntRelativeZeroContribution_layer_le_count
    {T x : ℝ} {n : ℕ} (input : PositiveZeroBucketInput T n) (i : Fin n)
    (hkernel : ∀ ρ ∈ input.layer i,
      ‖pntRelativeSimpleZeroKernel x ρ‖ ≤
        Real.exp (-Pintz.pintzZeroEnvelope x))
    (hmass : analyticMultiplicityMass (input.layer i) ≤
      (ZeroDensity.zeroDensityCount (input.sigma i) T : ℝ)) :
    (∑ ρ ∈ input.layer i, ‖pntRelativeZeroContribution x ρ‖) ≤
      Real.exp (-Pintz.pintzZeroEnvelope x) *
        (ZeroDensity.zeroDensityCount (input.sigma i) T : ℝ) := by
  apply sum_norm_pntRelativeZeroContribution_le_kernel_mul_of_mass_le
  · positivity
  · exact hkernel
  · exact hmass

/-- The multiplicity mass of a bucket is automatically bounded by the Carlson
count because the bucket is a subset of the corresponding zero-density
finset. -/
theorem PositiveZeroBucketInput.layer_multiplicityMass_le_zeroDensityCount
    {T : ℝ} {n : ℕ} (input : PositiveZeroBucketInput T n) (i : Fin n) :
    analyticMultiplicityMass (input.layer i) ≤
      (ZeroDensity.zeroDensityCount (input.sigma i) T : ℝ) := by
  have hnat :
      (∑ ρ ∈ input.layer i, analyticOrderNatAt riemannZeta ρ) ≤
        ∑ ρ ∈ ZeroDensity.zeroDensityZerosFinset (input.sigma i) T,
          analyticOrderNatAt riemannZeta ρ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (input.layer_subset_zeroDensityZerosFinset i)
    intro ρ hρ hnot
    exact Nat.zero_le _
  unfold analyticMultiplicityMass ZeroDensity.zeroDensityCount
  exact_mod_cast hnat

/-- Fully automatic multiplicity accounting for one positive-height bucket. -/
theorem PositiveZeroBucketInput.sum_norm_pntRelativeZeroContribution_layer_le_count'
    {T x : ℝ} {n : ℕ} (input : PositiveZeroBucketInput T n) (i : Fin n)
    (hkernel : ∀ ρ ∈ input.layer i,
      ‖pntRelativeSimpleZeroKernel x ρ‖ ≤
        Real.exp (-Pintz.pintzZeroEnvelope x)) :
    (∑ ρ ∈ input.layer i, ‖pntRelativeZeroContribution x ρ‖) ≤
      Real.exp (-Pintz.pintzZeroEnvelope x) *
        (ZeroDensity.zeroDensityCount (input.sigma i) T : ℝ) :=
  input.sum_norm_pntRelativeZeroContribution_layer_le_count i hkernel
    (input.layer_multiplicityMass_le_zeroDensityCount i)

end PrimeNumberTheorem
