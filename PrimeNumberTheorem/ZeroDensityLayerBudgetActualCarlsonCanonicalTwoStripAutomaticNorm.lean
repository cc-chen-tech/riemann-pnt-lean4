import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonCanonicalTwoStripPNTTransfer

/-!
# Automatic norm lower bound for canonical positive-zero layers

Positive-ordinate zeros of height at most one form a finite set, so their
nonzero norms have a positive finite minimum.  Above height one, the elementary
bound `|rho.im| ≤ ‖rho‖` gives a uniform lower bound directly.

This removes the last manually supplied kernel-denominator lower bound from the
canonical two-strip PNT transfer.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- A finite set of nonzero complex numbers has a positive norm lower bound
which may be chosen at most one. -/
theorem exists_pos_le_one_le_norm_on_finset
    (A : Finset ℂ) (hnonzero : ∀ z ∈ A, z ≠ 0) :
    ∃ kappa : ℝ,
      0 < kappa ∧ kappa ≤ 1 ∧ ∀ z ∈ A, kappa ≤ ‖z‖ := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      exact ⟨1, one_pos, le_rfl, by simp⟩
  | @insert a s ha ih =>
      have haNonzero : a ≠ 0 :=
        hnonzero a (Finset.mem_insert_self a s)
      have hsNonzero : ∀ z ∈ s, z ≠ 0 := by
        intro z hz
        exact hnonzero z (Finset.mem_insert_of_mem hz)
      rcases ih hsNonzero with ⟨kappa, hkappa, hkappaOne, hkappaS⟩
      refine
        ⟨min kappa ‖a‖, lt_min hkappa (norm_pos_iff.mpr haNonzero),
          (min_le_left _ _).trans hkappaOne, ?_⟩
      intro z hz
      rw [Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hkappaS z hz)

/-- Every dynamic canonical positive-zero layer admits one uniform positive
norm lower bound.  The bound depends only on the finite height-one base set,
not on the dynamic height or strip threshold. -/
theorem exists_canonicalTwoStripOutsideCluster_uniform_norm_lower_bound
    (H : ℝ → ℝ) (threshold : ℝ) (S : Finset ℂ) :
    ∃ kappa : ℝ,
      0 < kappa ∧
        ∀ (x : ℝ),
          ∀ rho ∈
              (pntHybridCanonicalTwoStripOutsideClusterBucketInput
                threshold (H x) S).layer (0 : Fin 2),
            kappa ≤ ‖rho‖ := by
  let base := positiveNontrivialZerosOutsideClusterFinset 1 S
  have hbaseNonzero : ∀ rho ∈ base, rho ≠ 0 := by
    intro rho hrho hzero
    have hmem :=
      (mem_positiveNontrivialZerosOutsideClusterFinset.mp hrho).2.1
    subst rho
    simpa using hmem
  rcases exists_pos_le_one_le_norm_on_finset base hbaseNonzero with
    ⟨kappa, hkappa, hkappaOne, hkappaBase⟩
  refine ⟨kappa, hkappa, ?_⟩
  intro x rho hrho
  have hpositive :
      rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) S :=
    (Finset.mem_filter.mp hrho).1
  rcases mem_positiveNontrivialZerosOutsideClusterFinset.mp hpositive with
    ⟨hzero, himPos, himHeight, houtside⟩
  by_cases himOne : rho.im ≤ 1
  · apply hkappaBase rho
    exact
      mem_positiveNontrivialZerosOutsideClusterFinset.mpr
        ⟨hzero, himPos, himOne, houtside⟩
  · have honeIm : 1 < rho.im := lt_of_not_ge himOne
    have himNorm : rho.im ≤ ‖rho‖ := by
      simpa [abs_of_pos himPos] using Complex.abs_im_le_norm rho
    exact hkappaOne.trans (honeIm.le.trans himNorm)

/-- Canonical pointwise-gap Carlson transfer to the actual PNT error with the
zero-kernel denominator bound constructed automatically. -/
theorem selectedUniformGoodHeightActualCarlsonCanonicalTwoStripPNTClusterResidual_automatic
    {S : Finset ℂ} {sigma beta alpha epsilon : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hS : ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S)
    (hbeta : 0 < beta)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (halpha : 0 < alpha)
    (halphaOne : alpha ≤ 1)
    (hcontourMargin : 1 - beta < alpha)
    (hepsilon : 0 < epsilon)
    (hlowMargin : sigma - beta + alpha + epsilon < 0)
    (hreHigh :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index < beta)
    (hreReal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) :
    NaturalPointTargetAmplitudeNegligible
      (fun m => targetZeroPowerAmplitude beta (m : ℝ))
      (fun m =>
        relativeChebyshevPsi0Error (m : ℝ) -
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight alpha selection) S (m : ℝ)) := by
  rcases
      exists_canonicalTwoStripOutsideCluster_uniform_norm_lower_bound
        (selectedUniformGoodHeight alpha selection) sigma S with
    ⟨kappa, hkappa, hnorm⟩
  exact
    selectedUniformGoodHeightActualCarlsonCanonicalTwoStripPNTClusterResidual_targetNegligible
      selection hS hbeta hhalf hone hkappa hnorm halpha halphaOne
      hcontourMargin hepsilon hlowMargin hreHigh hreReal

end PrimeNumberTheorem
