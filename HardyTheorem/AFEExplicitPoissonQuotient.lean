import HardyTheorem.AFEExplicitMellinAmplitude
import HardyTheorem.AFEWeightedPoissonVelocity
import MathlibAux.OscillatoryPhaseQuotient

/-!
# The explicit second integration-by-parts quotients for the Poisson AFE

This module instantiates the generic nonlinear phase quotients with the
explicit Mellin amplitude and the weighted Poisson phase velocity.
-/

noncomputable section

open Complex

namespace HardyTheorem
namespace AFE

noncomputable def explicitPoissonFirstQuotient
    (sigma x N t : ℝ) (k : ℤ) (u : ℝ) : ℂ :=
  MathlibAux.oscillatoryPhaseQuotient
    (explicitComplexMellinAmplitude sigma x N)
    (weightedPoissonVelocity t k) u

noncomputable def explicitPoissonFirstQuotientDerivative
    (sigma x N t : ℝ) (k : ℤ) (u : ℝ) : ℂ :=
  MathlibAux.oscillatoryPhaseQuotientDerivative
    (explicitComplexMellinAmplitude sigma x N)
    (explicitComplexMellinAmplitudeDeriv sigma x N)
    (weightedPoissonVelocity t k)
    (weightedPoissonVelocityDeriv t) u

noncomputable def explicitPoissonSecondQuotient
    (sigma x N t : ℝ) (k : ℤ) (u : ℝ) : ℂ :=
  MathlibAux.oscillatorySecondPhaseQuotient
    (explicitComplexMellinAmplitude sigma x N)
    (explicitComplexMellinAmplitudeDeriv sigma x N)
    (weightedPoissonVelocity t k)
    (weightedPoissonVelocityDeriv t) u

noncomputable def explicitPoissonSecondQuotientDerivative
    (sigma x N t : ℝ) (k : ℤ) (u : ℝ) : ℂ :=
  MathlibAux.oscillatorySecondPhaseQuotientDerivative
    (explicitComplexMellinAmplitude sigma x N)
    (explicitComplexMellinAmplitudeDeriv sigma x N)
    (explicitComplexMellinAmplitudeSecondDeriv sigma x N)
    (weightedPoissonVelocity t k)
    (weightedPoissonVelocityDeriv t)
    (weightedPoissonVelocitySecondDeriv t) u

theorem explicitPoissonFirstQuotient_mul_velocity
    {sigma x N t u : ℝ} {k : ℤ}
    (hv0 : weightedPoissonVelocity t k u ≠ 0) :
    explicitPoissonFirstQuotient sigma x N t k u *
        (I * (weightedPoissonVelocity t k u : ℂ)) =
      explicitComplexMellinAmplitude sigma x N u := by
  exact MathlibAux.oscillatoryPhaseQuotient_mul_phaseVelocity hv0

theorem explicitPoissonFirstQuotient_hasDerivAt
    (sigma x N t : ℝ) (k : ℤ) {u : ℝ}
    (hu : u ≠ 0) (hv0 : weightedPoissonVelocity t k u ≠ 0) :
    HasDerivAt (explicitPoissonFirstQuotient sigma x N t k)
      (explicitPoissonFirstQuotientDerivative sigma x N t k u) u := by
  exact MathlibAux.oscillatoryPhaseQuotient_hasDerivAt
    (explicitComplexMellinAmplitude_hasDerivAt sigma x N hu)
    (weightedPoissonVelocity_hasDerivAt t k hu) hv0

theorem explicitPoissonSecondQuotient_mul_velocity
    {sigma x N t u : ℝ} {k : ℤ}
    (hv0 : weightedPoissonVelocity t k u ≠ 0) :
    explicitPoissonSecondQuotient sigma x N t k u *
        (I * (weightedPoissonVelocity t k u : ℂ)) =
      MathlibAux.oscillatoryPhaseQuotientDerivative
        (explicitComplexMellinAmplitude sigma x N)
        (explicitComplexMellinAmplitudeDeriv sigma x N)
        (weightedPoissonVelocity t k)
        (weightedPoissonVelocityDeriv t) u := by
  exact MathlibAux.oscillatorySecondPhaseQuotient_mul_phaseVelocity hv0

theorem explicitPoissonSecondQuotient_mul_velocity_eq_firstDerivative
    {sigma x N t u : ℝ} {k : ℤ}
    (hv0 : weightedPoissonVelocity t k u ≠ 0) :
    explicitPoissonSecondQuotient sigma x N t k u *
        (I * (weightedPoissonVelocity t k u : ℂ)) =
      explicitPoissonFirstQuotientDerivative sigma x N t k u := by
  exact explicitPoissonSecondQuotient_mul_velocity hv0

theorem explicitPoissonSecondQuotient_hasDerivAt
    (sigma x N t : ℝ) (k : ℤ) {u : ℝ}
    (hu : u ≠ 0) (hv0 : weightedPoissonVelocity t k u ≠ 0) :
    HasDerivAt (explicitPoissonSecondQuotient sigma x N t k)
      (explicitPoissonSecondQuotientDerivative sigma x N t k u) u := by
  exact MathlibAux.oscillatorySecondPhaseQuotient_hasDerivAt
    (explicitComplexMellinAmplitude_hasDerivAt sigma x N hu)
    (explicitComplexMellinAmplitudeDeriv_hasDerivAt sigma x N hu)
    (weightedPoissonVelocity_hasDerivAt t k hu)
    (weightedPoissonVelocityDeriv_hasDerivAt t hu) hv0

theorem explicitPoissonFirstQuotientDerivative_continuousAt
    (sigma x N t : ℝ) (k : ℤ) {u : ℝ}
    (hu : u ≠ 0) (hv0 : weightedPoissonVelocity t k u ≠ 0) :
    ContinuousAt (explicitPoissonFirstQuotientDerivative sigma x N t k) u := by
  exact MathlibAux.oscillatoryPhaseQuotientDerivative_continuousAt
    (explicitComplexMellinAmplitude_hasDerivAt sigma x N hu).continuousAt
    (explicitComplexMellinAmplitudeDeriv_hasDerivAt sigma x N hu).continuousAt
    (weightedPoissonVelocity_hasDerivAt t k hu).continuousAt
    (weightedPoissonVelocityDeriv_hasDerivAt t hu).continuousAt hv0

theorem explicitPoissonSecondQuotientDerivative_continuousAt
    (sigma x N t : ℝ) (k : ℤ) {u : ℝ}
    (hu : u ≠ 0) (hv0 : weightedPoissonVelocity t k u ≠ 0) :
    ContinuousAt (explicitPoissonSecondQuotientDerivative sigma x N t k) u := by
  exact MathlibAux.oscillatorySecondPhaseQuotientDerivative_continuousAt
    (explicitComplexMellinAmplitude_hasDerivAt sigma x N hu).continuousAt
    (explicitComplexMellinAmplitudeDeriv_hasDerivAt sigma x N hu).continuousAt
    (explicitComplexMellinAmplitudeSecondDeriv_continuousAt sigma x N hu)
    (weightedPoissonVelocity_hasDerivAt t k hu).continuousAt
    (weightedPoissonVelocityDeriv_hasDerivAt t hu).continuousAt
    (weightedPoissonVelocitySecondDeriv_continuousAt t hu) hv0

theorem norm_explicitPoissonSecondQuotientDerivative_le
    {sigma x N t u : ℝ} {k : ℤ}
    (hv0 : weightedPoissonVelocity t k u ≠ 0) :
    ‖explicitPoissonSecondQuotientDerivative sigma x N t k u‖ ≤
      |1 / (weightedPoissonVelocity t k u) ^ 2| *
          ‖explicitComplexMellinAmplitudeSecondDeriv sigma x N u‖ +
      |3 * weightedPoissonVelocityDeriv t u /
          (weightedPoissonVelocity t k u) ^ 3| *
          ‖explicitComplexMellinAmplitudeDeriv sigma x N u‖ +
      |weightedPoissonVelocitySecondDeriv t u /
          (weightedPoissonVelocity t k u) ^ 3| *
          ‖explicitComplexMellinAmplitude sigma x N u‖ +
      |3 * (weightedPoissonVelocityDeriv t u) ^ 2 /
          (weightedPoissonVelocity t k u) ^ 4| *
          ‖explicitComplexMellinAmplitude sigma x N u‖ := by
  exact MathlibAux.norm_oscillatorySecondPhaseQuotientDerivative_le hv0

theorem explicitPoissonFirstQuotient_eq_zero_of_le
    {sigma x N t u : ℝ} {k : ℤ} (hu : u ≤ x - 1) :
    explicitPoissonFirstQuotient sigma x N t k u = 0 := by
  apply MathlibAux.oscillatoryPhaseQuotient_eq_zero
  exact explicitComplexMellinAmplitude_eq_zero_of_le hu

theorem explicitPoissonFirstQuotient_eq_zero_of_ge
    {sigma x N t u : ℝ} {k : ℤ} (hu : N + 1 ≤ u) :
    explicitPoissonFirstQuotient sigma x N t k u = 0 := by
  apply MathlibAux.oscillatoryPhaseQuotient_eq_zero
  exact explicitComplexMellinAmplitude_eq_zero_of_ge hu

theorem explicitPoissonSecondQuotient_eq_zero_of_le
    {sigma x N t u : ℝ} {k : ℤ} (hu : u ≤ x - 1) :
    explicitPoissonSecondQuotient sigma x N t k u = 0 := by
  apply MathlibAux.oscillatorySecondPhaseQuotient_eq_zero
  · exact explicitComplexMellinAmplitude_eq_zero_of_le hu
  · exact explicitComplexMellinAmplitudeDeriv_eq_zero_of_le hu

theorem explicitPoissonSecondQuotient_eq_zero_of_ge
    {sigma x N t u : ℝ} {k : ℤ} (hu : N + 1 ≤ u) :
    explicitPoissonSecondQuotient sigma x N t k u = 0 := by
  apply MathlibAux.oscillatorySecondPhaseQuotient_eq_zero
  · exact explicitComplexMellinAmplitude_eq_zero_of_ge hu
  · exact explicitComplexMellinAmplitudeDeriv_eq_zero_of_ge hu

end AFE
end HardyTheorem
