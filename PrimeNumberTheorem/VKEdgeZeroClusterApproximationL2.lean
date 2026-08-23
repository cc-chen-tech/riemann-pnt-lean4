import PrimeNumberTheorem.ExplicitFormulaNormalizedWindowRemainder
import PrimeNumberTheorem.VKEdgeZeroClusterClosedTermsL2

open Complex Filter MeasureTheory Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# Local L2 decay of the finite-height approximation error

The normalized-window explicit-formula theorem supplies one good truncation
height whose approximation error is uniformly small on a fixed logarithmic
window.  This module turns that pointwise estimate into a local second-moment
estimate.  The complementary-zero contribution is deliberately not included.
-/

/-- Local second moment of the normalized finite-height approximation error. -/
noncomputable def normalizedFiniteZeroClusterApproximationErrorSecondMoment
    (T beta a L : ℝ) : ℝ :=
  ∫ y in a..(a + L),
    ‖normalizedFiniteZeroClusterApproximationError T beta y‖ ^ 2

private theorem
    normalizedFiniteZeroClusterApproximationError_ae_eq_rightContinuous
    (T beta : ℝ) :
    (fun y =>
      normalizedFiniteZeroClusterApproximationError T beta y) =ᵐ[volume]
    (fun y =>
      (Real.exp (-beta * y) : ℂ) *
        (explicitFormulaApproxWithMultiplicity (Real.exp y) T -
          (chebyshevPsi (Real.exp y) : ℂ))) := by
  filter_upwards [jumpVonMangoldt_exp_ae_eq_zero] with y hy
  have hy0 : jumpVonMangoldt (Real.exp y) = 0 := by
    simpa using hy
  unfold normalizedFiniteZeroClusterApproximationError chebyshevPsi0
  rw [hy0]
  push_cast
  ring

private theorem
    measurable_normalizedFiniteZeroClusterApproximationError_rightContinuous
    (T beta : ℝ) :
    Measurable
      (fun y =>
        (Real.exp (-beta * y) : ℂ) *
          (explicitFormulaApproxWithMultiplicity (Real.exp y) T -
            (chebyshevPsi (Real.exp y) : ℂ))) := by
  have hpsi : Measurable chebyshevPsi := by
    change Measurable (Chebyshev.psi : ℝ → ℝ)
    simpa only [chebyshevPsi_eq_mathlib] using
      Chebyshev.psi_mono.measurable
  unfold explicitFormulaApproxWithMultiplicity
  unfold finiteNontrivialZeroSumWithMultiplicity
  fun_prop

private theorem
    aeStronglyMeasurable_normSq_normalizedFiniteZeroClusterApproximationError
    (T beta : ℝ) :
    AEStronglyMeasurable
      (fun y =>
        ‖normalizedFiniteZeroClusterApproximationError T beta y‖ ^ 2)
      volume := by
  have hmeas :
      AEStronglyMeasurable
        (fun y =>
          (Real.exp (-beta * y) : ℂ) *
            (explicitFormulaApproxWithMultiplicity (Real.exp y) T -
              (chebyshevPsi (Real.exp y) : ℂ)))
        volume :=
    (measurable_normalizedFiniteZeroClusterApproximationError_rightContinuous
      T beta).aestronglyMeasurable
  have hae :=
    normalizedFiniteZeroClusterApproximationError_ae_eq_rightContinuous
      T beta
  have hnorm :=
    (hmeas.congr hae.symm).norm
  convert hnorm.mul hnorm using 1 <;> (try rfl)
  · funext y
    simp [pow_two]

/-- On every fixed logarithmic window, one good truncation height makes the
normalized finite-height approximation-error second moment arbitrarily small.

This controls only the finite-height approximation component of the actual
zero-cluster remainder.  It does not control the complementary zero package. -/
theorem
    eventually_exists_goodHeight_normalizedApproximationErrorSecondMoment_lt
    {beta L eta : ℝ}
    (hbeta : 1 / 2 < beta) (hbeta1 : beta < 1)
    (hL : 0 ≤ L) (heta : 0 < eta) :
    ∀ᶠ a in atTop,
      ∃ T ∈ Set.Icc (Real.exp (a / 2)) (Real.exp (a / 2) + 1),
        ExplicitFormulaAux.goodHeight T ∧
          normalizedFiniteZeroClusterApproximationErrorSecondMoment
              T beta a L <
            eta := by
  let delta : ℝ := Real.sqrt (eta / (L + 1))
  have hL1 : 0 < L + 1 := by linarith
  have hratio : 0 < eta / (L + 1) := div_pos heta hL1
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact Real.sqrt_pos.2 hratio
  have hselect :=
    ExplicitFormulaResidues.eventually_exists_uniform_goodHeight_normalized_window_remainder_lt
        hbeta hbeta1 hL hdelta
  filter_upwards [hselect] with a ha
  rcases ha with ⟨T, hT, hgood, hpoint⟩
  refine ⟨T, hT, hgood, ?_⟩
  have hab : a ≤ a + L := by linarith
  have hleft :
      IntervalIntegrable
        (fun y =>
          ‖normalizedFiniteZeroClusterApproximationError T beta y‖ ^ 2)
        volume a (a + L) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    refine
      IntegrableOn.of_bound isCompact_Icc.measure_lt_top
        (aeStronglyMeasurable_normSq_normalizedFiniteZeroClusterApproximationError
          T beta).restrict
        (delta ^ 2) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    have hnorm :
        ‖normalizedFiniteZeroClusterApproximationError T beta y‖ <
          delta := by
      rw [normalizedFiniteZeroClusterApproximationError, norm_mul]
      have hscalar :
          ‖((Real.exp (-beta * y) : ℝ) : ℂ)‖ =
            Real.exp (-beta * y) := by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
      rw [hscalar]
      exact hpoint y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg
      (normalizedFiniteZeroClusterApproximationError T beta y)]
  have hright :
      IntervalIntegrable (fun _ : ℝ => delta ^ 2)
        volume a (a + L) :=
    intervalIntegrable_const
  have hpointSq :
      ∀ y ∈ Icc a (a + L),
        ‖normalizedFiniteZeroClusterApproximationError T beta y‖ ^ 2 ≤
          delta ^ 2 := by
    intro y hy
    have hnorm :
        ‖normalizedFiniteZeroClusterApproximationError T beta y‖ <
          delta := by
      rw [normalizedFiniteZeroClusterApproximationError, norm_mul]
      have hscalar :
          ‖((Real.exp (-beta * y) : ℝ) : ℂ)‖ =
            Real.exp (-beta * y) := by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
      rw [hscalar]
      exact hpoint y hy
    nlinarith [norm_nonneg
      (normalizedFiniteZeroClusterApproximationError T beta y)]
  have hmono :=
    intervalIntegral.integral_mono_on hab hleft hright hpointSq
  have hdeltaSq : delta ^ 2 = eta / (L + 1) := by
    dsimp [delta]
    exact Real.sq_sqrt hratio.le
  have hbudget : L * delta ^ 2 < eta := by
    rw [hdeltaSq]
    have hfrac : L / (L + 1) < 1 :=
      (div_lt_one hL1).2 (by linarith)
    calc
      L * (eta / (L + 1)) = eta * (L / (L + 1)) := by ring
      _ < eta * 1 := mul_lt_mul_of_pos_left hfrac heta
      _ = eta := mul_one eta
  unfold normalizedFiniteZeroClusterApproximationErrorSecondMoment
  calc
    (∫ y in a..(a + L),
        ‖normalizedFiniteZeroClusterApproximationError T beta y‖ ^ 2) ≤
        ∫ _y in a..(a + L), delta ^ 2 :=
      hmono
    _ = L * delta ^ 2 := by simp
    _ < eta := hbudget

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
