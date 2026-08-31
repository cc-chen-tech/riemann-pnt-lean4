import Mathlib.MeasureTheory.Integral.DominatedConvergence
import HardyTheorem.OscillatoryDampedGammaTail

open Real Complex Set MeasureTheory Filter Topology

namespace HardyTheorem.OscillatoryGammaCompactLimit

/-!
# Compact part of the Abel boundary passage

On a fixed interval bounded away from zero, exponential damping converges to
one under the oscillatory Gamma integral.  The tail is deliberately absent
from this statement; it is controlled uniformly in
`OscillatoryDampedGammaTail`.
-/

/-- On every fixed positive interval, the damped oscillatory Gamma integral
converges to the undamped one as the nonnegative damping tends to zero. -/
theorem tendsto_intervalIntegral_dampedGamma_nhdsWithin_zero
    {z : ℂ} {c a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto
      (fun r : ℝ => ∫ u in a..b,
        (u : ℂ) ^ (z - 1) * Complex.exp (-(r * u)) *
          Complex.exp (-I * (c * u)))
      (nhdsWithin 0 (Ici 0))
      (nhds (∫ u in a..b,
        (u : ℂ) ^ (z - 1) * Complex.exp (-I * (c * u)))) := by
  let F : ℝ → ℝ → ℂ := fun r u =>
    (u : ℂ) ^ (z - 1) * Complex.exp (-(r * u)) *
      Complex.exp (-I * (c * u))
  let f : ℝ → ℂ := fun u =>
    (u : ℂ) ^ (z - 1) * Complex.exp (-I * (c * u))
  let bound : ℝ → ℝ := fun u => u ^ (z.re - 1)
  have hF_cont (r : ℝ) : ContinuousOn (F r) (Icc a b) := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (ha.trans_le hu.1)
    have hpow : ContinuousAt (fun v : ℝ => (v : ℂ) ^ (z - 1)) u :=
      Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hu0)
    have hdamp : ContinuousAt (fun v : ℝ => Complex.exp (-(r * v))) u := by
      fun_prop
    have hphase : ContinuousAt (fun v : ℝ => Complex.exp (-I * (c * v))) u := by
      fun_prop
    exact ((hpow.mul hdamp).mul hphase).continuousWithinAt
  have hbound_cont : ContinuousOn bound (Icc a b) := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (ha.trans_le hu.1)
    exact (Real.continuousAt_rpow_const u (z.re - 1) (Or.inl hu0)).continuousWithinAt
  have hbound_int : IntervalIntegrable bound volume a b :=
    hbound_cont.intervalIntegrable_of_Icc hab
  have hmeas : ∀ᶠ r in nhdsWithin 0 (Ici 0),
      AEStronglyMeasurable (F r) (volume.restrict (uIoc a b)) := by
    exact Eventually.of_forall fun r =>
      ((hF_cont r).mono (by
        simpa [uIcc_of_le hab] using
          (uIoc_subset_uIcc (a := a) (b := b)))).aestronglyMeasurable
        measurableSet_uIoc
  have hmajor : ∀ᶠ r in nhdsWithin 0 (Ici 0),
      ∀ᵐ u ∂volume, u ∈ uIoc a b → ‖F r u‖ ≤ bound u := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    filter_upwards with u hu
    have huIcc : u ∈ Icc a b := by
      simpa [uIcc_of_le hab] using
        (uIoc_subset_uIcc (a := a) (b := b) hu)
    have hupos : 0 < u := ha.trans_le huIcc.1
    have hru : 0 ≤ r * u := mul_nonneg hr hupos.le
    have hdamp : Real.exp (-(r * u)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr hru
    dsimp only [F, bound]
    rw [norm_mul, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hupos]
    have hdampNorm : ‖Complex.exp (-(r * u))‖ = Real.exp (-(r * u)) := by
      rw [Complex.norm_exp]
      simp
    have hphaseNorm : ‖Complex.exp (-I * (c * u))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    rw [hdampNorm, hphaseNorm, mul_one]
    exact mul_le_of_le_one_right (Real.rpow_nonneg hupos.le _) hdamp
  have hpoint : ∀ᵐ u ∂volume, u ∈ uIoc a b →
      Tendsto (fun r => F r u) (nhdsWithin 0 (Ici 0)) (nhds (f u)) := by
    filter_upwards with u hu
    have hdamp : Tendsto (fun r : ℝ => Complex.exp (-(r * u)))
        (nhdsWithin 0 (Ici 0)) (nhds 1) := by
      have hcont : ContinuousAt (fun r : ℝ => Complex.exp (-(r * u))) 0 := by
        fun_prop
      have hval : Complex.exp (-((0 : ℝ) * u)) = 1 := by simp
      rw [← hval]
      exact hcont.continuousWithinAt
    have hpow : Tendsto (fun _ : ℝ => (u : ℂ) ^ (z - 1))
        (nhdsWithin 0 (Ici 0)) (nhds ((u : ℂ) ^ (z - 1))) :=
      tendsto_const_nhds
    have hphase : Tendsto (fun _ : ℝ => Complex.exp (-I * (c * u)))
        (nhdsWithin 0 (Ici 0)) (nhds (Complex.exp (-I * (c * u)))) :=
      tendsto_const_nhds
    dsimp only [F, f]
    simpa using ((hpow.mul hdamp).mul hphase)
  simpa [F, f] using
    intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      bound hmeas hmajor hbound_int hpoint

/-- The same Abel limit on `(0,b]`.  Continuity at the endpoint `0` is not
claimed; `0 < Re z` is exactly the local integrability condition for the
dominating power. -/
theorem tendsto_intervalIntegral_dampedGamma_zero_right_nhdsWithin_zero
    {z : ℂ} {c b : ℝ} (hz0 : 0 < z.re) (hb : 0 ≤ b) :
    Tendsto
      (fun r : ℝ => ∫ u in (0 : ℝ)..b,
        (u : ℂ) ^ (z - 1) * Complex.exp (-(r * u)) *
          Complex.exp (-I * (c * u)))
      (nhdsWithin 0 (Ici 0))
      (nhds (∫ u in (0 : ℝ)..b,
        (u : ℂ) ^ (z - 1) * Complex.exp (-I * (c * u)))) := by
  let F : ℝ → ℝ → ℂ := fun r u =>
    (u : ℂ) ^ (z - 1) * Complex.exp (-(r * u)) *
      Complex.exp (-I * (c * u))
  let f : ℝ → ℂ := fun u =>
    (u : ℂ) ^ (z - 1) * Complex.exp (-I * (c * u))
  let bound : ℝ → ℝ := fun u => u ^ (z.re - 1)
  have hF_cont (r : ℝ) : ContinuousOn (F r) (uIoc (0 : ℝ) b) := by
    intro u hu
    have huIoc : u ∈ Ioc (0 : ℝ) b := by
      simpa [uIoc_of_le hb] using hu
    have hupos : 0 < u := huIoc.1
    have hu0 : u ≠ 0 := hupos.ne'
    have hpow : ContinuousAt (fun v : ℝ => (v : ℂ) ^ (z - 1)) u :=
      Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hu0)
    have hdamp : ContinuousAt (fun v : ℝ => Complex.exp (-(r * v))) u := by
      fun_prop
    have hphase : ContinuousAt (fun v : ℝ => Complex.exp (-I * (c * v))) u := by
      fun_prop
    exact ((hpow.mul hdamp).mul hphase).continuousWithinAt
  have hbound_int : IntervalIntegrable bound volume 0 b := by
    dsimp only [bound]
    exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hmeas : ∀ᶠ r in nhdsWithin 0 (Ici 0),
      AEStronglyMeasurable (F r) (volume.restrict (uIoc 0 b)) := by
    exact Eventually.of_forall fun r =>
      (hF_cont r).aestronglyMeasurable measurableSet_uIoc
  have hmajor : ∀ᶠ r in nhdsWithin 0 (Ici 0),
      ∀ᵐ u ∂volume, u ∈ uIoc (0 : ℝ) b → ‖F r u‖ ≤ bound u := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    filter_upwards with u hu
    have huIoc : u ∈ Ioc (0 : ℝ) b := by
      simpa [uIoc_of_le hb] using hu
    have hupos : 0 < u := huIoc.1
    have hru : 0 ≤ r * u := mul_nonneg hr hupos.le
    have hdamp : Real.exp (-(r * u)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr hru
    dsimp only [F, bound]
    rw [norm_mul, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hupos]
    have hdampNorm : ‖Complex.exp (-(r * u))‖ = Real.exp (-(r * u)) := by
      rw [Complex.norm_exp]
      simp
    have hphaseNorm : ‖Complex.exp (-I * (c * u))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    rw [hdampNorm, hphaseNorm, mul_one]
    exact mul_le_of_le_one_right (Real.rpow_nonneg hupos.le _) hdamp
  have hpoint : ∀ᵐ u ∂volume, u ∈ uIoc (0 : ℝ) b →
      Tendsto (fun r => F r u) (nhdsWithin 0 (Ici 0)) (nhds (f u)) := by
    filter_upwards with u hu
    have hdamp : Tendsto (fun r : ℝ => Complex.exp (-(r * u)))
        (nhdsWithin 0 (Ici 0)) (nhds 1) := by
      have hcont : ContinuousAt (fun r : ℝ => Complex.exp (-(r * u))) 0 := by
        fun_prop
      have hval : Complex.exp (-((0 : ℝ) * u)) = 1 := by simp
      rw [← hval]
      exact hcont.continuousWithinAt
    have hpow : Tendsto (fun _ : ℝ => (u : ℂ) ^ (z - 1))
        (nhdsWithin 0 (Ici 0)) (nhds ((u : ℂ) ^ (z - 1))) :=
      tendsto_const_nhds
    have hphase : Tendsto (fun _ : ℝ => Complex.exp (-I * (c * u)))
        (nhdsWithin 0 (Ici 0)) (nhds (Complex.exp (-I * (c * u)))) :=
      tendsto_const_nhds
    dsimp only [F, f]
    simpa using ((hpow.mul hdamp).mul hphase)
  simpa [F, f] using
    intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      bound hmeas hmajor hbound_int hpoint

/-- The unit-interval specialization used by the first version of the Abel
boundary argument. -/
theorem tendsto_intervalIntegral_dampedGamma_zero_one_nhdsWithin_zero
    {z : ℂ} {c : ℝ} (hz0 : 0 < z.re) :
    Tendsto
      (fun r : ℝ => ∫ u in (0 : ℝ)..1,
        (u : ℂ) ^ (z - 1) * Complex.exp (-(r * u)) *
          Complex.exp (-I * (c * u)))
      (nhdsWithin 0 (Ici 0))
      (nhds (∫ u in (0 : ℝ)..1,
        (u : ℂ) ^ (z - 1) * Complex.exp (-I * (c * u)))) := by
  exact tendsto_intervalIntegral_dampedGamma_zero_right_nhdsWithin_zero
    hz0 (by norm_num)

end HardyTheorem.OscillatoryGammaCompactLimit
