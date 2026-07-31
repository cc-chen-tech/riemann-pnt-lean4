import PrimeNumberTheorem.ZeroDensityLayerBudgetVariableBoundarySigmaOnlyUnifiedUpperSignedOmega

/-!
# Zero-free moving gaps and actual PNT decay

A zero-free region controls the constructed moving boundary through the exact
logarithmic condition `(1 - beta(m)) * log m -> infinity`.  This makes the
moving target amplitude decay, closing the actual relative PNT upper direction
of the unified transfer.
-/

namespace PrimeNumberTheorem

open Filter Topology

noncomputable section

/-- Canonical selected good-height schedule determined by one Carlson
threshold. -/
noncomputable def sigmaOnlyNaturalRunningBoundaryHeight
    (sigma : ℝ) : ℝ → ℝ :=
  actualDynamicBoundaryCanonicalSelectedGoodHeight
    (actualDynamicBoundaryBalancedGoodHeightExponent sigma)

/-- Canonical running visible-zero boundary determined by one Carlson
threshold. -/
noncomputable def sigmaOnlyNaturalRunningBoundary
    (sigma : ℝ) : ℝ → ℝ :=
  naturalRunningVisibleZeroBoundaryReal
    (sigmaOnlyNaturalRunningBoundaryHeight sigma)
    (sigmaOnlyRunningBoundaryBeta0 sigma)

/-- Exact logarithmic zero-free condition needed for decay of a moving target
power amplitude. -/
def IsNaturalVariableBoundaryZeroFreeDecay
    (beta : ℝ → ℝ) : Prop :=
  Tendsto
    (fun m : ℕ =>
      (1 - beta (m : ℝ)) * Real.log (m : ℝ))
    atTop atTop

/-- A divergent zero-free logarithmic gap makes the exact moving relative
power amplitude tend to zero. -/
theorem variableBoundaryTargetAmplitude_tendsto_zero_of_zeroFreeDecay
    {beta : ℝ → ℝ}
    (hzeroFree : IsNaturalVariableBoundaryZeroFreeDecay beta) :
    Tendsto
      (fun m : ℕ =>
        variableBoundaryTargetAmplitude beta (m : ℝ))
      atTop (nhds 0) := by
  have hnegative :
      Tendsto
        (fun m : ℕ =>
          -((1 - beta (m : ℝ)) * Real.log (m : ℝ)))
        atTop atBot :=
    tendsto_neg_atTop_atBot.comp hzeroFree
  have hexp :
      Tendsto
        (fun m : ℕ =>
          Real.exp
            (-((1 - beta (m : ℝ)) * Real.log (m : ℝ))))
        atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp hnegative
  refine hexp.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  have hmPos : 0 < (m : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hm)
  unfold variableBoundaryTargetAmplitude targetZeroPowerAmplitude
  rw [Real.rpow_def_of_pos hmPos]
  apply congrArg Real.exp
  ring

/-- Sigma-only actual PNT decay and conditional signed-Omega transfer.

The zero-free input closes the upper direction for the canonical running
boundary.  The lower signed conclusion retains the independent positive and
negative main-package witnesses. -/
theorem actualSigmaOnlyRunningBoundaryZeroFreeUpperDecaySignedOmega
    {sigma eta c loss : ℝ}
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (heta : 0 < eta)
    (hloss : 0 < loss)
    (hlossC : loss < c)
    (hzeroFree :
      IsNaturalVariableBoundaryZeroFreeDecay
        (sigmaOnlyNaturalRunningBoundary sigma))
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
  rcases
      actualSigmaOnlyNaturalRunningMaximumBoundaryUnifiedUpperSignedOmega
        hhalf hone heta hloss hlossC
          (by
            simpa [sigmaOnlyNaturalRunningBoundaryHeight,
              sigmaOnlyNaturalRunningBoundary] using hmainPos)
          (by
            simpa [sigmaOnlyNaturalRunningBoundaryHeight,
              sigmaOnlyNaturalRunningBoundary] using hmainNeg) with
    ⟨hupper, hcoefficient, hsigned⟩
  have htarget :
      Tendsto
        (fun m : ℕ =>
          variableBoundaryTargetAmplitude
            (sigmaOnlyNaturalRunningBoundary sigma) (m : ℝ))
        atTop (nhds 0) :=
    variableBoundaryTargetAmplitude_tendsto_zero_of_zeroFreeDecay hzeroFree
  have hmajorant :
      Tendsto
        (fun m : ℕ =>
          (actualCarlsonDynamicBoundaryCoefficientCapConstant sigma + eta) *
            variableBoundaryTargetAmplitude
              (sigmaOnlyNaturalRunningBoundary sigma) (m : ℝ))
        atTop (nhds 0) := by
    simpa only [mul_zero] using
      htarget.const_mul
        (actualCarlsonDynamicBoundaryCoefficientCapConstant sigma + eta)
  have habs :
      Tendsto
        (fun m : ℕ => |relativeChebyshevPsi0Error (m : ℝ)|)
        atTop (nhds 0) := by
    apply squeeze_zero'
    · filter_upwards with m
      exact abs_nonneg _
    · filter_upwards [hupper] with m hm
      exact hm.le
    · simpa [sigmaOnlyNaturalRunningBoundary] using hmajorant
  have hdecay :
      Tendsto
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa [Real.norm_eq_abs] using habs
  exact
    ⟨hdecay, hcoefficient,
      by simpa [sigmaOnlyNaturalRunningBoundary] using hsigned⟩

end

end PrimeNumberTheorem
