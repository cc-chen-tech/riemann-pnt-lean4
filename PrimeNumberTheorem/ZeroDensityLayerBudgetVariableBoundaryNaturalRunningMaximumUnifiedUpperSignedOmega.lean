import PrimeNumberTheorem.ZeroDensityLayerBudgetVariableBoundaryCanonicalGoodHeightUnifiedUpperSignedOmega

/-!
# Natural running-maximum moving zero boundary

The canonical good-height schedule need not be monotone.  We therefore take
the real-part maximum of the zeros visible at each natural sample and then a
recursive running maximum.  This constructs a sampled-monotone moving boundary
with an automatic fixed lower anchor and visible right-edge property.
-/

namespace PrimeNumberTheorem

open Filter

noncomputable section

/-- Largest real part among positive nontrivial zeros visible at one natural
sample, with zero inserted for the empty-set case. -/
noncomputable def visiblePositiveZeroRealPartBottleneck
    (H : ℝ → ℝ) (m : ℕ) : ℝ :=
  let values :=
    insert 0
      ((positiveNontrivialZerosFinset (H (m : ℝ))).image fun rho => rho.re)
  values.max' (Finset.insert_nonempty 0 _)

/-- Every positive zero visible at the current natural sample lies below its
finite real-part bottleneck. -/
theorem visiblePositiveZero_re_le_bottleneck
    {H : ℝ → ℝ} {m : ℕ} {rho : ℂ}
    (hrho : rho ∈ positiveNontrivialZerosFinset (H (m : ℝ))) :
    rho.re ≤ visiblePositiveZeroRealPartBottleneck H m := by
  let values :=
    insert 0
      ((positiveNontrivialZerosFinset (H (m : ℝ))).image fun z => z.re)
  apply values.le_max'
  exact Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨rho, hrho, rfl⟩)

/-- Running maximum of all pointwise visible-zero bottlenecks through the
current natural sample, initialized above the fixed lower anchor. -/
noncomputable def naturalRunningVisibleZeroBoundary
    (H : ℝ → ℝ) (beta0 : ℝ) : ℕ → ℝ
  | 0 => max beta0 (visiblePositiveZeroRealPartBottleneck H 0)
  | m + 1 =>
      max (naturalRunningVisibleZeroBoundary H beta0 m)
        (visiblePositiveZeroRealPartBottleneck H (m + 1))

/-- The fixed anchor lies below every value of the running boundary. -/
theorem beta0_le_naturalRunningVisibleZeroBoundary
    (H : ℝ → ℝ) (beta0 : ℝ) (m : ℕ) :
    beta0 ≤ naturalRunningVisibleZeroBoundary H beta0 m := by
  induction m with
  | zero =>
      exact le_max_left _ _
  | succ m ih =>
      exact ih.trans (le_max_left _ _)

/-- The current visible-zero bottleneck lies below the running boundary. -/
theorem visiblePositiveZeroRealPartBottleneck_le_runningBoundary
    (H : ℝ → ℝ) (beta0 : ℝ) (m : ℕ) :
    visiblePositiveZeroRealPartBottleneck H m ≤
      naturalRunningVisibleZeroBoundary H beta0 m := by
  cases m with
  | zero =>
      exact le_max_right _ _
  | succ m =>
      exact le_max_right _ _

/-- Each successor step can only increase the running boundary. -/
theorem naturalRunningVisibleZeroBoundary_le_succ
    (H : ℝ → ℝ) (beta0 : ℝ) (m : ℕ) :
    naturalRunningVisibleZeroBoundary H beta0 m ≤
      naturalRunningVisibleZeroBoundary H beta0 (m + 1) :=
  le_max_left _ _

/-- The natural running boundary is monotone. -/
theorem naturalRunningVisibleZeroBoundary_monotone
    (H : ℝ → ℝ) (beta0 : ℝ) :
    Monotone (naturalRunningVisibleZeroBoundary H beta0) :=
  monotone_nat_of_le_succ
    (naturalRunningVisibleZeroBoundary_le_succ H beta0)

/-- Real-valued floor extension of the natural running boundary. -/
noncomputable def naturalRunningVisibleZeroBoundaryReal
    (H : ℝ → ℝ) (beta0 x : ℝ) : ℝ :=
  naturalRunningVisibleZeroBoundary H beta0 (Nat.floor x)

@[simp] theorem naturalRunningVisibleZeroBoundaryReal_natCast
    (H : ℝ → ℝ) (beta0 : ℝ) (m : ℕ) :
    naturalRunningVisibleZeroBoundaryReal H beta0 (m : ℝ) =
      naturalRunningVisibleZeroBoundary H beta0 m := by
  simp [naturalRunningVisibleZeroBoundaryReal]

/-- The floor-extended boundary has the fixed lower anchor at every natural
sample. -/
theorem beta0_le_naturalRunningVisibleZeroBoundaryReal_natCast
    (H : ℝ → ℝ) (beta0 : ℝ) (m : ℕ) :
    beta0 ≤ naturalRunningVisibleZeroBoundaryReal H beta0 (m : ℝ) := by
  simpa using beta0_le_naturalRunningVisibleZeroBoundary H beta0 m

/-- The floor-extended boundary is monotone on the natural samples used by the
explicit-formula transfer. -/
theorem naturalRunningVisibleZeroBoundaryReal_sampled_monotone
    (H : ℝ → ℝ) (beta0 : ℝ) :
    Monotone
      (fun m : ℕ =>
        naturalRunningVisibleZeroBoundaryReal H beta0 (m : ℝ)) := by
  simpa using naturalRunningVisibleZeroBoundary_monotone H beta0

/-- The constructed running boundary automatically bounds every currently
visible Carlson-indexed positive zero. -/
theorem naturalRunningVisibleZeroBoundaryReal_indexedVisibleRightEdge
    {sigma : ℝ} (H : ℝ → ℝ) (beta0 : ℝ) :
    IsIndexedVariableBoundaryVisibleRightEdge (sigma := sigma) H
      (naturalRunningVisibleZeroBoundaryReal H beta0) := by
  intro m index hvisible
  rcases actualCarlsonPositiveZero_spec index with ⟨hzero, him, _⟩
  have hmem :
      actualCarlsonPositiveZero index ∈
        positiveNontrivialZerosFinset (H (m : ℝ)) := by
    apply mem_positiveNontrivialZerosFinset.mpr
    exact ⟨hzero, him, by simpa [abs_of_pos him] using hvisible⟩
  rw [naturalRunningVisibleZeroBoundaryReal_natCast]
  exact
    (visiblePositiveZero_re_le_bottleneck hmem).trans
      (visiblePositiveZeroRealPartBottleneck_le_runningBoundary H beta0 m)

/-- Canonical-good-height unified transfer with the moving boundary itself
constructed as the natural running maximum of visible zero real parts. -/
theorem
    actualNaturalRunningMaximumBoundaryCanonicalGoodHeightUnifiedUpperSignedOmega
    {sigma beta0 alpha epsilon eta c loss : ℝ}
    (heta : 0 < eta)
    (hloss : 0 < loss)
    (hlossC : loss < c)
    (hbeta0 : 0 < beta0)
    (halpha : 0 < alpha)
    (halphaOne : alpha ≤ 1)
    (hcontourMargin : 1 - beta0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta0 + alpha + epsilon < 0)
    (hrightReal :
      ∀ rho ∈ realOrdinateNontrivialZerosFinset 0, rho.re < beta0)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hmainPos :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
            (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha)
            (variableBoundaryZeroPackage
              (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha)
              (naturalRunningVisibleZeroBoundaryReal
                (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha)
                beta0)
              (m : ℝ))
            (m : ℝ))
        (fun m : ℕ =>
          c * variableBoundaryTargetAmplitude
            (naturalRunningVisibleZeroBoundaryReal
              (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha)
              beta0)
            (m : ℝ)))
    (hmainNeg :
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
            (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha)
            (variableBoundaryZeroPackage
              (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha)
              (naturalRunningVisibleZeroBoundaryReal
                (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha)
                beta0)
              (m : ℝ))
            (m : ℝ))
        (fun m : ℕ =>
          c * variableBoundaryTargetAmplitude
            (naturalRunningVisibleZeroBoundaryReal
              (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha)
              beta0)
            (m : ℝ))) :
    (∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ)| <
          (actualCarlsonDynamicBoundaryCoefficientCapConstant sigma + eta) *
            variableBoundaryTargetAmplitude
              (naturalRunningVisibleZeroBoundaryReal
                (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha)
                beta0)
              (m : ℝ)) ∧
      0 < c - loss ∧
      HasFarSignedTargetAmplitudeWitnesses chebyshevPsi0Error
        (fun x : ℝ =>
          (c - loss) * x ^
            naturalRunningVisibleZeroBoundaryReal
              (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha)
              beta0 x) := by
  let H := actualDynamicBoundaryCanonicalSelectedGoodHeight alpha
  let beta := naturalRunningVisibleZeroBoundaryReal H beta0
  have hbetaLower : ∀ᶠ m : ℕ in atTop, beta0 ≤ beta (m : ℝ) := by
    filter_upwards with m
    exact beta0_le_naturalRunningVisibleZeroBoundaryReal_natCast H beta0 m
  have hbetaMono : Monotone (fun m : ℕ => beta (m : ℝ)) :=
    naturalRunningVisibleZeroBoundaryReal_sampled_monotone H beta0
  have hright :
      IsIndexedVariableBoundaryVisibleRightEdge (sigma := sigma) H beta :=
    naturalRunningVisibleZeroBoundaryReal_indexedVisibleRightEdge H beta0
  exact
    actualMonotoneVariableBoundaryCanonicalGoodHeightUnifiedUpperSignedOmega
      heta hloss hlossC hbeta0 hbetaLower hbetaMono halpha halphaOne
        hcontourMargin hepsilon hmargin hrightReal hhalf hone hright
          (by simpa [H, beta] using hmainPos)
          (by simpa [H, beta] using hmainNeg)

end

end PrimeNumberTheorem
