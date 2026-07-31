import PrimeNumberTheorem.ZeroDensityLayerBudgetVariableBoundaryZeroFreeUpperDecay

/-!
# Zero-free envelopes for the canonical running boundary

A monotone zero-free envelope bounds every pointwise visible-zero bottleneck
and hence the recursive running maximum.  The fixed anchor competes with the
analytic gap, producing the exact effective gap `min (1-beta0) gap`.
-/

namespace PrimeNumberTheorem

open Filter Topology

noncomputable section

/-- Every positive nontrivial zero visible at natural sample `m` lies below
the zero-free envelope `1 - gap(m)`. -/
def IsNaturalPositiveZeroFreeEnvelope
    (H : ℝ → ℝ) (gap : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, ∀ rho ∈ positiveNontrivialZerosFinset (H (m : ℝ)),
    rho.re ≤ 1 - gap m

/-- Honest gap after accounting for the fixed anchor in the running maximum. -/
noncomputable def naturalRunningBoundaryEffectiveGap
    (beta0 : ℝ) (gap : ℕ → ℝ) (m : ℕ) : ℝ :=
  min (1 - beta0) (gap m)

/-- A pointwise visible-zero bottleneck is bounded by the larger of the fixed
anchor and the current zero-free envelope. -/
theorem visiblePositiveZeroRealPartBottleneck_le_anchor_max_envelope
    {H : ℝ → ℝ} {beta0 : ℝ} {gap : ℕ → ℝ}
    (hbeta0 : 0 < beta0)
    (henvelope : IsNaturalPositiveZeroFreeEnvelope H gap)
    (m : ℕ) :
    visiblePositiveZeroRealPartBottleneck H m ≤
      max beta0 (1 - gap m) := by
  let values :=
    insert 0
      ((positiveNontrivialZerosFinset (H (m : ℝ))).image fun rho => rho.re)
  change values.max' (Finset.insert_nonempty 0 _) ≤
    max beta0 (1 - gap m)
  rw [Finset.max'_le_iff]
  intro value hvalue
  rcases Finset.mem_insert.mp hvalue with hzero | hzero
  · rw [hzero]
    exact hbeta0.le.trans (le_max_left _ _)
  · obtain ⟨rho, hrho, rfl⟩ := Finset.mem_image.mp hzero
    exact (henvelope m rho hrho).trans (le_max_right _ _)

/-- An antitone analytic gap makes `1-gap(m)` monotone, so the recursive
running maximum stays below the anchor-envelope maximum. -/
theorem naturalRunningVisibleZeroBoundary_le_anchor_max_envelope
    {H : ℝ → ℝ} {beta0 : ℝ} {gap : ℕ → ℝ}
    (hbeta0 : 0 < beta0)
    (hgapAnti : Antitone gap)
    (henvelope : IsNaturalPositiveZeroFreeEnvelope H gap) :
    ∀ m : ℕ,
      naturalRunningVisibleZeroBoundary H beta0 m ≤
        max beta0 (1 - gap m) := by
  intro m
  induction m with
  | zero =>
      exact max_le (le_max_left _ _)
        (visiblePositiveZeroRealPartBottleneck_le_anchor_max_envelope
          hbeta0 henvelope 0)
  | succ m ih =>
      have hupper : 1 - gap m ≤ 1 - gap (m + 1) := by
        have := hgapAnti (Nat.le_succ m)
        linarith
      rw [naturalRunningVisibleZeroBoundary]
      apply max_le
      · exact ih.trans (max_le_max le_rfl hupper)
      · exact
          visiblePositiveZeroRealPartBottleneck_le_anchor_max_envelope
            hbeta0 henvelope (m + 1)

/-- The effective gap is bounded by the actual distance of the canonical
running boundary from one. -/
theorem naturalRunningBoundaryEffectiveGap_le_one_sub_runningBoundary
    {H : ℝ → ℝ} {beta0 : ℝ} {gap : ℕ → ℝ}
    (hbeta0 : 0 < beta0)
    (hgapAnti : Antitone gap)
    (henvelope : IsNaturalPositiveZeroFreeEnvelope H gap)
    (m : ℕ) :
    naturalRunningBoundaryEffectiveGap beta0 gap m ≤
      1 - naturalRunningVisibleZeroBoundary H beta0 m := by
  have hrunning :=
    naturalRunningVisibleZeroBoundary_le_anchor_max_envelope
      hbeta0 hgapAnti henvelope m
  have heq :
      naturalRunningBoundaryEffectiveGap beta0 gap m =
        1 - max beta0 (1 - gap m) := by
    unfold naturalRunningBoundaryEffectiveGap
    by_cases h : beta0 ≤ 1 - gap m
    · rw [max_eq_right h]
      have hgap : gap m ≤ 1 - beta0 := by linarith
      rw [min_eq_right hgap]
      ring
    · have hreverse : 1 - gap m ≤ beta0 := le_of_not_ge h
      rw [max_eq_left hreverse]
      have hgap : 1 - beta0 ≤ gap m := by linarith
      rw [min_eq_left hgap]
  rw [heq]
  linarith

/-- Effective-gap logarithmic divergence implies the exact Stack 117
zero-free decay condition for the floor-extended running boundary. -/
theorem isNaturalVariableBoundaryZeroFreeDecay_of_envelope
    {H : ℝ → ℝ} {beta0 : ℝ} {gap : ℕ → ℝ}
    (hbeta0 : 0 < beta0)
    (hgapAnti : Antitone gap)
    (henvelope : IsNaturalPositiveZeroFreeEnvelope H gap)
    (heffective :
      Tendsto
        (fun m : ℕ =>
          naturalRunningBoundaryEffectiveGap beta0 gap m *
            Real.log (m : ℝ))
        atTop atTop) :
    IsNaturalVariableBoundaryZeroFreeDecay
      (naturalRunningVisibleZeroBoundaryReal H beta0) := by
  unfold IsNaturalVariableBoundaryZeroFreeDecay
  apply tendsto_atTop_mono' atTop ?_ heffective
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  have hlog : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hm)
  have hgap :=
    naturalRunningBoundaryEffectiveGap_le_one_sub_runningBoundary
      hbeta0 hgapAnti henvelope m
  rw [naturalRunningVisibleZeroBoundaryReal_natCast]
  exact mul_le_mul_of_nonneg_right hgap hlog

/-- A concrete monotone zero-free envelope closes the sigma-only actual PNT
upper direction while retaining the conditional signed-Omega conclusion. -/
theorem actualSigmaOnlyZeroFreeEnvelopeUpperDecaySignedOmega
    {sigma eta c loss : ℝ} {gap : ℕ → ℝ}
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (heta : 0 < eta)
    (hloss : 0 < loss)
    (hlossC : loss < c)
    (hgapAnti : Antitone gap)
    (henvelope :
      IsNaturalPositiveZeroFreeEnvelope
        (sigmaOnlyNaturalRunningBoundaryHeight sigma) gap)
    (heffective :
      Tendsto
        (fun m : ℕ =>
          naturalRunningBoundaryEffectiveGap
              (sigmaOnlyRunningBoundaryBeta0 sigma) gap m *
            Real.log (m : ℝ))
        atTop atTop)
    (hmainPos :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
            (sigmaOnlyNaturalRunningBoundaryHeight sigma)
            (variableBoundaryZeroPackage
              (sigmaOnlyNaturalRunningBoundaryHeight sigma)
              (sigmaOnlyNaturalRunningBoundary sigma) (m : ℝ))
            (m : ℝ))
        (fun m : ℕ =>
          c * variableBoundaryTargetAmplitude
            (sigmaOnlyNaturalRunningBoundary sigma) (m : ℝ)))
    (hmainNeg :
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
            (sigmaOnlyNaturalRunningBoundaryHeight sigma)
            (variableBoundaryZeroPackage
              (sigmaOnlyNaturalRunningBoundaryHeight sigma)
              (sigmaOnlyNaturalRunningBoundary sigma) (m : ℝ))
            (m : ℝ))
        (fun m : ℕ =>
          c * variableBoundaryTargetAmplitude
            (sigmaOnlyNaturalRunningBoundary sigma) (m : ℝ))) :
    Tendsto
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        atTop (nhds 0) ∧
      0 < c - loss ∧
      HasFarSignedTargetAmplitudeWitnesses chebyshevPsi0Error
        (fun x : ℝ =>
          (c - loss) * x ^ sigmaOnlyNaturalRunningBoundary sigma x) := by
  have hbeta0 : 0 < sigmaOnlyRunningBoundaryBeta0 sigma :=
    (sigmaOnlyRunningBoundaryParameters_spec hhalf hone).2.2.2.1
  have hzeroFree :
      IsNaturalVariableBoundaryZeroFreeDecay
        (sigmaOnlyNaturalRunningBoundary sigma) := by
    simpa [sigmaOnlyNaturalRunningBoundary,
      sigmaOnlyNaturalRunningBoundaryHeight] using
      isNaturalVariableBoundaryZeroFreeDecay_of_envelope
        hbeta0 hgapAnti henvelope heffective
  exact
    actualSigmaOnlyRunningBoundaryZeroFreeUpperDecaySignedOmega
      hhalf hone heta hloss hlossC hzeroFree hmainPos hmainNeg

end

end PrimeNumberTheorem
