import HardyTheorem.AFEExplicitPoissonQuotient
import MathlibAux.IntervalOscillatorySecondIntegrationByParts

/-!
# Explicit twice-integrated nonstationary Poisson modes

This module closes the analytic bookkeeping needed to apply the generic
second integration-by-parts identity to the explicit compact Mellin
amplitude.  On a positive nonstationary support interval, continuity gives
all three interval-integrability hypotheses, while the fixed plateau makes
both quotient boundary terms vanish.
-/

noncomputable section

open Complex MeasureTheory Set

namespace HardyTheorem
namespace AFE

/-- A nonstationary Fourier--Mellin mode is bounded by the `L1` norm of its
explicit twice-integrated remainder.  In particular, no integrability or
endpoint hypothesis remains for the caller to supply. -/
theorem norm_explicitPoissonIntegral_le_secondRemainder
    (sigma x N t : ℝ) (k : ℤ)
    (hx : 1 < x) (hxN : x ≤ N)
    (hnonstationary : ∀ u ∈ Icc (x - 1) (N + 1),
      weightedPoissonVelocity t k u ≠ 0) :
    ‖∫ u in (x - 1)..(N + 1),
        explicitComplexMellinAmplitude sigma x N u *
          Complex.exp (I * weightedPoissonPhase t k u)‖ ≤
      ∫ u in (x - 1)..(N + 1),
        ‖explicitPoissonSecondQuotientDerivative sigma x N t k u‖ := by
  have hab : x - 1 ≤ N + 1 := by linarith
  have hmem {u : ℝ} (hu : u ∈ uIcc (x - 1) (N + 1)) :
      u ∈ Icc (x - 1) (N + 1) := by
    simpa [uIcc_of_le hab] using hu
  have hne {u : ℝ} (hu : u ∈ uIcc (x - 1) (N + 1)) : u ≠ 0 := by
    have hu' := hmem hu
    have hu_pos : 0 < u := by linarith [hu'.1]
    exact hu_pos.ne'
  have hvel {u : ℝ} (hu : u ∈ uIcc (x - 1) (N + 1)) :
      weightedPoissonVelocity t k u ≠ 0 :=
    hnonstationary u (hmem hu)
  have hQ'int : IntervalIntegrable
      (explicitPoissonFirstQuotientDerivative sigma x N t k)
      volume (x - 1) (N + 1) := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    exact (explicitPoissonFirstQuotientDerivative_continuousAt
      sigma x N t k (hne hu) (hvel hu)).continuousWithinAt
  have hR'int : IntervalIntegrable
      (explicitPoissonSecondQuotientDerivative sigma x N t k)
      volume (x - 1) (N + 1) := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    exact (explicitPoissonSecondQuotientDerivative_continuousAt
      sigma x N t k (hne hu) (hvel hu)).continuousWithinAt
  have hE'int : IntervalIntegrable
      (fun u => Complex.exp (I * weightedPoissonPhase t k u) *
        (I * (weightedPoissonVelocity t k u : ℂ)))
      volume (x - 1) (N + 1) := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    have hphase : ContinuousAt (weightedPoissonPhase t k) u :=
      (weightedPoissonPhase_hasDerivAt_velocity t k (hne hu)).continuousAt
    have hvelocity : ContinuousAt (weightedPoissonVelocity t k) u :=
      (weightedPoissonVelocity_hasDerivAt t k (hne hu)).continuousAt
    have hphaseC : ContinuousAt
        (fun y => (weightedPoissonPhase t k y : ℂ)) u := by
      change ContinuousAt (Complex.ofReal ∘ weightedPoissonPhase t k) u
      exact Complex.continuous_ofReal.continuousAt.comp hphase
    have hvelocityC : ContinuousAt
        (fun y => (weightedPoissonVelocity t k y : ℂ)) u := by
      change ContinuousAt (Complex.ofReal ∘ weightedPoissonVelocity t k) u
      exact Complex.continuous_ofReal.continuousAt.comp hvelocity
    exact (((continuousAt_const.mul hphaseC).cexp).mul
      (continuousAt_const.mul hvelocityC)).continuousWithinAt
  apply MathlibAux.norm_intervalIntegral_mul_cexp_phase_le_secondRemainder
    hab
    (A := explicitComplexMellinAmplitude sigma x N)
    (Q := explicitPoissonFirstQuotient sigma x N t k)
    (Q' := explicitPoissonFirstQuotientDerivative sigma x N t k)
    (R := explicitPoissonSecondQuotient sigma x N t k)
    (R' := explicitPoissonSecondQuotientDerivative sigma x N t k)
    (F := weightedPoissonPhase t k)
    (F' := weightedPoissonVelocity t k)
  · intro u hu
    exact weightedPoissonPhase_hasDerivAt_velocity t k (hne hu)
  · intro u hu
    exact explicitPoissonFirstQuotient_hasDerivAt
      sigma x N t k (hne hu) (hvel hu)
  · intro u hu
    exact explicitPoissonSecondQuotient_hasDerivAt
      sigma x N t k (hne hu) (hvel hu)
  · exact hQ'int
  · exact hR'int
  · exact hE'int
  · intro u hu
    exact (explicitPoissonFirstQuotient_mul_velocity (hvel hu)).symm
  · intro u hu
    exact (explicitPoissonSecondQuotient_mul_velocity_eq_firstDerivative
      (hvel hu)).symm
  · constructor
    · exact explicitPoissonFirstQuotient_eq_zero_of_le le_rfl
    · exact explicitPoissonFirstQuotient_eq_zero_of_ge le_rfl
  · constructor
    · exact explicitPoissonSecondQuotient_eq_zero_of_le le_rfl
    · exact explicitPoissonSecondQuotient_eq_zero_of_ge le_rfl

end AFE
end HardyTheorem
