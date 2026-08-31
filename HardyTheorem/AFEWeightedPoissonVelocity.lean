import HardyTheorem.AFEWeightedPoissonCutoff

/-!
# Velocity derivatives for the weighted Poisson phase

The three functions here are `F'`, `F''`, and `F'''` for the Fourier--Mellin
phase used in the smoothed critical AFE.
-/

noncomputable section

namespace HardyTheorem
namespace AFE

noncomputable def weightedPoissonVelocity (t : ℝ) (k : ℤ) (u : ℝ) : ℝ :=
  -t / u - 2 * Real.pi * (k : ℝ)

noncomputable def weightedPoissonVelocityDeriv (t u : ℝ) : ℝ :=
  t / u ^ 2

noncomputable def weightedPoissonVelocitySecondDeriv (t u : ℝ) : ℝ :=
  -2 * t / u ^ 3

theorem weightedPoissonPhase_hasDerivAt_velocity
    (t : ℝ) (k : ℤ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (weightedPoissonPhase t k)
      (weightedPoissonVelocity t k u) u := by
  simpa only [weightedPoissonVelocity] using
    weightedPoissonPhase_hasDerivAt t k hu

theorem weightedPoissonVelocity_hasDerivAt
    (t : ℝ) (k : ℤ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (weightedPoissonVelocity t k)
      (weightedPoissonVelocityDeriv t u) u := by
  have hquot := (hasDerivAt_const u (-t)).div (hasDerivAt_id u) hu
  have hconst : HasDerivAt (fun _y : ℝ => 2 * Real.pi * (k : ℝ)) 0 u :=
    hasDerivAt_const u _
  convert! hquot.sub hconst using 1
  simp [weightedPoissonVelocityDeriv]

theorem weightedPoissonVelocityDeriv_hasDerivAt
    (t : ℝ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (weightedPoissonVelocityDeriv t)
      (weightedPoissonVelocitySecondDeriv t u) u := by
  have hquot := (hasDerivAt_const u t).div ((hasDerivAt_id u).pow 2)
    (pow_ne_zero 2 hu)
  convert! hquot using 1
  simp [weightedPoissonVelocitySecondDeriv]
  field_simp [hu]

theorem weightedPoissonVelocitySecondDeriv_continuousAt
    (t : ℝ) {u : ℝ} (hu : u ≠ 0) :
    ContinuousAt (weightedPoissonVelocitySecondDeriv t) u := by
  unfold weightedPoissonVelocitySecondDeriv
  exact continuousAt_const.div₀ (continuousAt_id.pow 3) (pow_ne_zero 3 hu)

end AFE
end HardyTheorem
