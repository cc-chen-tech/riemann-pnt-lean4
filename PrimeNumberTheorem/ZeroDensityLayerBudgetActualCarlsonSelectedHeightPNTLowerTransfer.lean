import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonSelectedHeightPNTTransfer
import PrimeNumberTheorem.ZeroForcingUnifiedTransfer

/-!
# Conditional lower transfer for the pointwise-gap Carlson chain

The Carlson-explicit-formula chain now controls the actual PNT residual outside
the visible finite zero cluster.  This module records the final conditional
assembly step: a far natural-point witness for that visible cluster survives
the negligible residual with half the target amplitude.

No cluster oscillation theorem is asserted here.  The `hmain` witness remains
an explicit input supplied by the separate sharp-oscillation development.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- A target-negligible difference from a main term transfers every far
natural-point main witness to the full error with half the amplitude. -/
theorem hasFarNaturalPointTargetAmplitudeWitness_of_difference_negligible
    {amplitude main error : ℕ → ℝ}
    (hamplitude : ∀ᶠ m : ℕ in atTop, 0 < amplitude m)
    (hnegligible :
      NaturalPointTargetAmplitudeNegligible amplitude
        (fun m => error m - main m))
    (hmain : HasFarNaturalPointTargetAmplitudeWitness main amplitude) :
    HasFarNaturalPointTargetAmplitudeWitness error
      (fun m => amplitude m / 2) := by
  have hsmall :=
    eventually_abs_lt_mul_of_naturalPointTargetAmplitudeNegligible
      hamplitude hnegligible (epsilon := (1 / 2 : ℝ)) (by norm_num)
  rw [eventually_atTop] at hsmall
  rcases hsmall with ⟨M₀, hM₀⟩
  intro M
  rcases hmain (max M M₀) with ⟨m, hm, hmainM⟩
  have hmM : M ≤ m := le_trans (le_max_left M M₀) hm
  have hmM₀ : M₀ ≤ m := le_trans (le_max_right M M₀) hm
  refine ⟨m, hmM, ?_⟩
  apply half_targetAmplitude_le_abs_error
    (remainder := error m - main m) hmainM
  · have hsmallM := (hM₀ m hmM₀).le
    calc
      |error m - main m| ≤ (1 / 2 : ℝ) * amplitude m := hsmallM
      _ = amplitude m / 2 := by ring
  · ring

/-- Conditional unsigned lower transfer from a selected-height visible zeta
cluster to the actual relative Chebyshev error.  The high Carlson strip uses
only the pointwise gap outside `S`. -/
theorem selectedUniformGoodHeightActualCarlsonPNTLowerTransfer
    {n : ℕ} {S : Finset ℂ}
    {sigma beta alpha kappa epsilon : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (selectedUniformGoodHeight alpha selection x) S n)
    (i : Fin n)
    (hS : ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S)
    (hbeta : 0 < beta)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hkappa : 0 < kappa)
    (hnorm : ∀ (x : ℝ), ∀ rho ∈ (input x).layer i, kappa ≤ ‖rho‖)
    (hreLow : ∀ (x : ℝ), ∀ rho ∈ (input x).layer i, rho.re ≤ sigma)
    (hlowCover :
      ∀ (x : ℝ),
        ∀ rho ∈
            positiveNontrivialZerosOutsideClusterFinset
              (selectedUniformGoodHeight alpha selection x) S,
          rho.re ≤ sigma → (input x).bucket rho = i)
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
        rho.re < beta)
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m =>
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight alpha selection) S (m : ℝ))
        (fun m => targetZeroPowerAmplitude beta (m : ℝ))) :
    HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
      (fun x => targetZeroPowerAmplitude beta x / 2) := by
  have hresidual :=
    selectedUniformGoodHeightActualCarlsonPNTClusterResidual_targetNegligible
      selection input i hS hbeta hhalf hone hkappa hnorm hreLow
      hlowCover halpha halphaOne hcontourMargin hepsilon hlowMargin
      hreHigh hreReal
  have hnatural :=
    hasFarNaturalPointTargetAmplitudeWitness_of_difference_negligible
      (eventually_naturalPoint_pos_of_eventually_pos
        (targetZeroPowerAmplitude_eventually_pos beta))
      hresidual hmain
  exact HasFarNaturalPointTargetAmplitudeWitness.toReal hnatural

end PrimeNumberTheorem
