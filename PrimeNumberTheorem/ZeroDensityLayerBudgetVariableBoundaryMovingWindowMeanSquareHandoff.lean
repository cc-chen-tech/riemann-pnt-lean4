import PrimeNumberTheorem.ZeroDensityLayerBudgetVariableBoundaryNaturalRunningMaximumReciprocalSignAlternative

/-!
# Moving-window mean-square handoff for a variable zero boundary

This module isolates the exact local analytic input still missing from the
natural running-boundary transfer.  A strict square-sum lower bound on every
far normalized window forces one threshold-large natural point.  Positivity
of the moving target amplitude then removes the normalization and supplies
the unsigned moving-package witness consumed by the reciprocal upper/lower
transfer.

No mean-square estimate for the actual zeta-zero package is asserted here.
-/

open scoped BigOperators Topology

namespace PrimeNumberTheorem

open Filter

noncomputable section

/-- Every far tail contains a finite window whose square energy is strictly
larger than the constant threshold energy on that window. -/
def HasFarWindowStrictMeanSquareLowerBound
    (f : ℕ → ℝ) (threshold : ℝ) : Prop :=
  ∀ M : ℕ, ∃ G : Finset ℕ,
    (∀ m ∈ G, M ≤ m) ∧
      (G.card : ℝ) * threshold ^ 2 < ∑ m ∈ G, (f m) ^ 2

/-- A strict lower mean-square budget forces a threshold-large point in every
far tail.  This is the finite arithmetic core of the handoff. -/
theorem HasFarWindowStrictMeanSquareLowerBound.toNaturalPointWitness
    {f : ℕ → ℝ} {threshold : ℝ}
    (hthreshold : 0 ≤ threshold)
    (henergy : HasFarWindowStrictMeanSquareLowerBound f threshold) :
    HasFarNaturalPointTargetAmplitudeWitness f (fun _ => threshold) := by
  intro M
  rcases henergy M with ⟨G, hfar, henergyG⟩
  have hexists : ∃ m ∈ G, threshold ≤ |f m| := by
    by_contra hlarge
    push_neg at hlarge
    have hupper :
        (∑ m ∈ G, (f m) ^ 2) ≤
          (G.card : ℝ) * threshold ^ 2 := by
      calc
        (∑ m ∈ G, (f m) ^ 2) ≤ ∑ _m ∈ G, threshold ^ 2 :=
          Finset.sum_le_sum fun m hm => by
            have hsquare :=
              (sq_lt_sq₀ (abs_nonneg (f m)) hthreshold).2 (hlarge m hm)
            simpa only [sq_abs] using hsquare.le
        _ = (G.card : ℝ) * threshold ^ 2 := by simp
    exact (not_lt_of_ge hupper) henergyG
  rcases hexists with ⟨m, hmG, hm⟩
  exact ⟨m, hfar m hmG, hm⟩

/-- A normalized strict mean-square lower bound becomes a witness at the
moving unnormalized amplitude whenever that amplitude is eventually
positive. -/
theorem HasFarWindowStrictMeanSquareLowerBound.normalized_to_mul_amplitude
    {f amplitude : ℕ → ℝ} {threshold : ℝ}
    (hthreshold : 0 ≤ threshold)
    (hamplitude : ∀ᶠ m : ℕ in atTop, 0 < amplitude m)
    (henergy :
      HasFarWindowStrictMeanSquareLowerBound
        (fun m => f m / amplitude m) threshold) :
    HasFarNaturalPointTargetAmplitudeWitness
      f (fun m => threshold * amplitude m) := by
  have hnormalized := henergy.toNaturalPointWitness hthreshold
  rcases eventually_atTop.1 hamplitude with ⟨M₀, hM₀⟩
  intro M
  rcases hnormalized (max M M₀) with ⟨m, hmFar, hm⟩
  have hmM : M ≤ m := (le_max_left M M₀).trans hmFar
  have hm₀ : M₀ ≤ m := (le_max_right M M₀).trans hmFar
  have hamp : 0 < amplitude m := hM₀ m hm₀
  have hdiv : threshold ≤ |f m| / amplitude m := by
    simpa [abs_div, abs_of_pos hamp] using hm
  exact ⟨m, hmM, (le_div_iff₀ hamp).mp hdiv⟩

/-- Exact handoff from a repeatable normalized moving-window square-energy
lower bound to the unsigned actual moving-package witness required by the
natural running boundary. -/
theorem
    actualNaturalRunningMaximumMovingPackageWitness_of_windowMeanSquare
    {alpha beta0 c : ℝ}
    (hc : 0 ≤ c)
    (henergy :
      HasFarWindowStrictMeanSquareLowerBound
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
              (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha)
              (variableBoundaryZeroPackage
                (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha)
                (naturalRunningVisibleZeroBoundaryReal
                  (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha)
                  beta0)
                (m : ℝ))
              (m : ℝ) /
            variableBoundaryTargetAmplitude
              (naturalRunningVisibleZeroBoundaryReal
                (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha)
                beta0)
              (m : ℝ))
        c) :
    HasFarNaturalPointTargetAmplitudeWitness
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
          (m : ℝ)) := by
  apply henergy.normalized_to_mul_amplitude hc
  exact eventually_variableBoundaryTargetAmplitude_pos _

/-- The running-boundary reciprocal upper bound and one-sign Omega
alternative can consume a repeatable local square-energy lower bound directly,
without a separate pointwise moving-package witness assumption. -/
theorem
    actualNaturalRunningMaximumBoundaryCanonicalGoodHeightUnifiedUpperSignAlternative_of_windowMeanSquare_reciprocal
    {sigma beta0 alpha epsilon eta c loss : ℝ}
    (heta : 0 < eta)
    (hloss : 0 < loss) (hlossC : loss < c)
    (hc : 0 ≤ c)
    (hbeta0 : 0 < beta0)
    (halpha : 0 < alpha)
    (halphaOne : alpha ≤ 1)
    (hcontourMargin : 1 - beta0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta0 + epsilon < 0)
    (hrightReal :
      ∀ rho ∈ realOrdinateNontrivialZerosFinset 0, rho.re < beta0)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (henergy :
      HasFarWindowStrictMeanSquareLowerBound
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
              (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha)
              (variableBoundaryZeroPackage
                (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha)
                (naturalRunningVisibleZeroBoundaryReal
                  (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha)
                  beta0)
                (m : ℝ))
              (m : ℝ) /
            variableBoundaryTargetAmplitude
              (naturalRunningVisibleZeroBoundaryReal
                (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha)
                beta0)
              (m : ℝ))
        c) :
    (∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ)| <
          (actualCarlsonDynamicBoundaryCoefficientCapConstant sigma + eta) *
            variableBoundaryTargetAmplitude
              (naturalRunningVisibleZeroBoundaryReal
                (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha)
                beta0)
              (m : ℝ)) ∧
      0 < c - loss ∧
      (HasFarPositiveTargetAmplitudeWitness chebyshevPsi0Error
          (fun x : ℝ =>
            (c - loss) * x ^
              naturalRunningVisibleZeroBoundaryReal
                (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha)
                beta0 x) ∨
        HasFarNegativeTargetAmplitudeWitness chebyshevPsi0Error
          (fun x : ℝ =>
            (c - loss) * x ^
              naturalRunningVisibleZeroBoundaryReal
                (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha)
                beta0 x)) := by
  apply
    actualNaturalRunningMaximumBoundaryCanonicalGoodHeightUnifiedUpperSignAlternative_reciprocal
      heta hloss hlossC hbeta0 halpha halphaOne hcontourMargin hepsilon
      hmargin hrightReal hhalf hone
  exact
    actualNaturalRunningMaximumMovingPackageWitness_of_windowMeanSquare
      hc henergy

end
end PrimeNumberTheorem
