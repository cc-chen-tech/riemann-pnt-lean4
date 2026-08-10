import PrimeNumberTheorem.ZeroDensityLayerBudgetActualClusterSignedComplement
import PrimeNumberTheorem.ZeroDensityLayerBudgetSharpConstantTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTSharpSignedOmega

/-!
# Visible-cluster transfer from a finite seed

For a finite inclusion `S₀ ⊆ S`, the actual visible PNT main term splits
exactly into the seed contribution and the contribution of `S \ S₀`.
Consequently, a far-point witness for the seed survives in the expanded
cluster after subtracting any eventual target-scale budget for the newly
adjoined finite terms.

This is a finite-sum stability statement.  It does not construct a seed
oscillation witness and does not invoke a zero-reproduction argument.
-/

open scoped BigOperators Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- Exact complex finite-sum decomposition of a visible cluster into a seed
and the newly adjoined members. -/
theorem dynamicVisibleClusterPNTZeroSum_eq_seed_add_extension
    (T : ℝ → ℝ) {S₀ S : Finset ℂ}
    (hsub : ∀ rho ∈ S₀, rho ∈ S) (x : ℝ) :
    dynamicVisibleClusterPNTZeroSum T S x =
      dynamicVisibleClusterPNTZeroSum T S₀ x +
        dynamicVisibleClusterPNTZeroSum T (S \ S₀) x := by
  classical
  unfold dynamicVisibleClusterPNTZeroSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho _
  by_cases hseed : rho ∈ S₀
  · have hfinal : rho ∈ S := hsub rho hseed
    simp [hseed, hfinal]
  · by_cases hfinal : rho ∈ S
    · have hextension : rho ∈ S \ S₀ :=
        Finset.mem_sdiff.mpr ⟨hfinal, hseed⟩
      simp [hseed, hfinal, hextension]
    · have hextension : rho ∉ S \ S₀ := by
        intro hrho
        exact hfinal (Finset.mem_sdiff.mp hrho).1
      simp [hseed, hfinal, hextension]

/-- Real visible-main version of the finite seed decomposition. -/
theorem dynamicVisibleClusterPNTMain_eq_seed_add_extension
    (T : ℝ → ℝ) {S₀ S : Finset ℂ}
    (hsub : ∀ rho ∈ S₀, rho ∈ S) (x : ℝ) :
    dynamicVisibleClusterPNTMain T S x =
      dynamicVisibleClusterPNTMain T S₀ x +
        dynamicVisibleClusterPNTMain T (S \ S₀) x := by
  have h :=
    congrArg Complex.re
      (dynamicVisibleClusterPNTZeroSum_eq_seed_add_extension
        T hsub x)
  simpa [dynamicVisibleClusterPNTMain] using h

/-- The perturbation from the seed main to the expanded main is exactly the
visible contribution of the newly adjoined finite members. -/
theorem dynamicVisibleClusterPNTMain_sub_seed_eq_extension
    (T : ℝ → ℝ) {S₀ S : Finset ℂ}
    (hsub : ∀ rho ∈ S₀, rho ∈ S) (x : ℝ) :
    dynamicVisibleClusterPNTMain T S x -
        dynamicVisibleClusterPNTMain T S₀ x =
      dynamicVisibleClusterPNTMain T (S \ S₀) x := by
  rw [dynamicVisibleClusterPNTMain_eq_seed_add_extension T hsub x]
  ring

/-- An unsigned seed-cluster witness survives finite extension with the exact
coefficient loss assigned to the newly adjoined visible terms. -/
theorem hasFarNaturalPointTargetAmplitudeWitness_visibleCluster_of_seed
    (T : ℝ → ℝ) {S₀ S : Finset ℂ}
    (hsub : ∀ rho ∈ S₀, rho ∈ S)
    {amplitude : ℕ → ℝ} {c loss : ℝ}
    (hseed :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m => dynamicVisibleClusterPNTMain T S₀ (m : ℝ))
        (fun m => c * amplitude m))
    (hnew :
      ∀ᶠ m : ℕ in atTop,
        |dynamicVisibleClusterPNTMain T (S \ S₀) (m : ℝ)| <
          loss * amplitude m) :
    HasFarNaturalPointTargetAmplitudeWitness
      (fun m => dynamicVisibleClusterPNTMain T S (m : ℝ))
      (fun m => (c - loss) * amplitude m) := by
  apply hseed.transfer_eventually_sub_lt
  filter_upwards [hnew] with m hm
  rw [dynamicVisibleClusterPNTMain_sub_seed_eq_extension T hsub (m : ℝ)]
  exact hm

/-- Positive signed seed witnesses obey the same finite-extension loss. -/
theorem hasFarNaturalPointPositiveTargetAmplitudeWitness_visibleCluster_of_seed
    (T : ℝ → ℝ) {S₀ S : Finset ℂ}
    (hsub : ∀ rho ∈ S₀, rho ∈ S)
    {amplitude : ℕ → ℝ} {c loss : ℝ}
    (hseed :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
        (fun m => dynamicVisibleClusterPNTMain T S₀ (m : ℝ))
        (fun m => c * amplitude m))
    (hnew :
      ∀ᶠ m : ℕ in atTop,
        |dynamicVisibleClusterPNTMain T (S \ S₀) (m : ℝ)| <
          loss * amplitude m) :
    HasFarNaturalPointPositiveTargetAmplitudeWitness
      (fun m => dynamicVisibleClusterPNTMain T S (m : ℝ))
      (fun m => (c - loss) * amplitude m) := by
  apply hseed.transfer_eventually_sub_lt
  filter_upwards [hnew] with m hm
  rw [dynamicVisibleClusterPNTMain_sub_seed_eq_extension T hsub (m : ℝ)]
  exact hm

/-- Negative signed seed witnesses obey the same finite-extension loss. -/
theorem hasFarNaturalPointNegativeTargetAmplitudeWitness_visibleCluster_of_seed
    (T : ℝ → ℝ) {S₀ S : Finset ℂ}
    (hsub : ∀ rho ∈ S₀, rho ∈ S)
    {amplitude : ℕ → ℝ} {c loss : ℝ}
    (hseed :
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (fun m => dynamicVisibleClusterPNTMain T S₀ (m : ℝ))
        (fun m => c * amplitude m))
    (hnew :
      ∀ᶠ m : ℕ in atTop,
        |dynamicVisibleClusterPNTMain T (S \ S₀) (m : ℝ)| <
          loss * amplitude m) :
    HasFarNaturalPointNegativeTargetAmplitudeWitness
      (fun m => dynamicVisibleClusterPNTMain T S (m : ℝ))
      (fun m => (c - loss) * amplitude m) := by
  apply hseed.transfer_eventually_sub_lt
  filter_upwards [hnew] with m hm
  rw [dynamicVisibleClusterPNTMain_sub_seed_eq_extension T hsub (m : ℝ)]
  exact hm

end PrimeNumberTheorem
