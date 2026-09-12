import PrimeNumberTheorem.MWKFCubicZetaPoleFactorization
import Mathlib.Topology.UniformSpace.UniformApproximation

open Filter Topology

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Joint continuity of the cubic Euler pole unit

The locally uniform Euler product from `MWKFCubicEulerLocalUniform` is a
jointly continuous function of all three complex variables on its open strip.
Combining this with the analytic pole unit at `1` proves that the full pole
unit core is continuous at the central point.  In particular, the leading
value `U(s,t,0)` occurring after the third-variable derivative tends jointly
to `U(0,0,0) = 1`.

This is the local limiting input identified by the review of the pole
factorization.  It does not exchange this limit with a contour integral or a
residue, and it makes no off-diagonal estimate.
-/

/-- The locally uniformly convergent Euler correction is jointly continuous
on every open strip of width `eta < 1/4`. -/
theorem continuousOn_mwkfEulerCorrection_openStrip
    {eta : ℝ} (hetaQuarter : eta < 1 / 4) :
    ContinuousOn
      (fun z : ℂ × ℂ × ℂ ↦
        mwkfEulerCorrection z.1 z.2.1 z.2.2)
      (mwkfEulerOpenStrip eta) := by
  have hprod :=
    hasProdLocallyUniformlyOn_mwkfPrimeCorrectionFactor hetaQuarter
  apply hprod.continuousOn
  apply Filter.Eventually.frequently
  filter_upwards [] with S
  apply continuousOn_finsetProd S
  intro p hp
  exact continuousOn_mwkfPrimeCorrectionFactor_openStrip p
    (by linarith : eta < 1 / 2)

/-- The three-variable pole-unit core is jointly continuous at the central
point.  This uses the joint local-uniform convergence of the Euler correction,
not merely separate holomorphy. -/
theorem continuousAt_mwkfEulerPoleUnitCore_zero :
    ContinuousAt
      (fun z : ℂ × ℂ × ℂ ↦
        mwkfEulerPoleUnitCore z.1 z.2.1 z.2.2)
      (0, 0, 0) := by
  let Q : ℂ → ℂ := ZeroFreeRegion.riemannZetaPoleUnitAtOne
  have hQ : ContinuousAt Q 1 := by
    exact ZeroFreeRegion.analyticAt_riemannZetaPoleUnitAtOne.continuousAt
  have hQst : ContinuousAt
      (fun z : ℂ × ℂ × ℂ ↦ Q (1 + z.1 + z.2.1)) (0, 0, 0) := by
    have hmap : ContinuousAt
        (fun z : ℂ × ℂ × ℂ ↦ 1 + z.1 + z.2.1) (0, 0, 0) := by
      fun_prop
    simpa [Function.comp_def] using hQ.comp_of_eq hmap (by norm_num)
  have hQsw : ContinuousAt
      (fun z : ℂ × ℂ × ℂ ↦ Q (1 + z.1 + z.2.2)) (0, 0, 0) := by
    have hmap : ContinuousAt
        (fun z : ℂ × ℂ × ℂ ↦ 1 + z.1 + z.2.2) (0, 0, 0) := by
      fun_prop
    simpa [Function.comp_def] using hQ.comp_of_eq hmap (by norm_num)
  have hQtw : ContinuousAt
      (fun z : ℂ × ℂ × ℂ ↦ Q (1 + z.2.1 + z.2.2)) (0, 0, 0) := by
    have hmap : ContinuousAt
        (fun z : ℂ × ℂ × ℂ ↦ 1 + z.2.1 + z.2.2) (0, 0, 0) := by
      fun_prop
    simpa [Function.comp_def] using hQ.comp_of_eq hmap (by norm_num)
  have hzero : (0, 0, 0) ∈ mwkfEulerOpenStrip (1 / 8 : ℝ) := by
    norm_num [mwkfEulerOpenStrip]
  have hH : ContinuousAt
      (fun z : ℂ × ℂ × ℂ ↦
        mwkfEulerCorrection z.1 z.2.1 z.2.2) (0, 0, 0) :=
    (continuousOn_mwkfEulerCorrection_openStrip
      (by norm_num : (1 / 8 : ℝ) < 1 / 4)).continuousAt
      ((isOpen_mwkfEulerOpenStrip (1 / 8 : ℝ)).mem_nhds hzero)
  have hden :
      (fun z : ℂ × ℂ × ℂ ↦
        Q (1 + z.1 + z.2.2) * Q (1 + z.2.1 + z.2.2)) (0, 0, 0) ≠ 0 := by
    simp [Q, ZeroFreeRegion.riemannZetaPoleUnitAtOne_one]
  unfold mwkfEulerPoleUnitCore
  change ContinuousAt
    (fun z : ℂ × ℂ × ℂ ↦
      Q (1 + z.1 + z.2.1) /
          (Q (1 + z.1 + z.2.2) * Q (1 + z.2.1 + z.2.2)) *
        mwkfEulerCorrection z.1 z.2.1 z.2.2) (0, 0, 0)
  exact (hQst.div (hQsw.mul hQtw) hden).mul hH

/-- On the `w = 0` slice, the leading pole-unit value tends jointly to one
as `(s,t)` tends to the central pair. -/
theorem tendsto_mwkfEulerPoleUnitCore_in_third_zero_at_pair_zero :
    Tendsto
      (fun z : ℂ × ℂ ↦ mwkfEulerPoleUnitCore z.1 z.2 0)
      (𝓝 (0, 0)) (𝓝 1) := by
  have hslice : ContinuousAt
      (fun z : ℂ × ℂ ↦ (z.1, z.2, (0 : ℂ))) (0, 0) := by
    fun_prop
  have hcont := continuousAt_mwkfEulerPoleUnitCore_zero.comp_of_eq hslice (by rfl)
  change Tendsto
    (fun z : ℂ × ℂ ↦ mwkfEulerPoleUnitCore z.1 z.2 0)
    (𝓝 (0, 0)) (𝓝 (mwkfEulerPoleUnitCore 0 0 0)) at hcont
  simpa only [mwkfEulerPoleUnitCore_zero] using hcont

end PrimeNumberTheorem.MWKFCubic
