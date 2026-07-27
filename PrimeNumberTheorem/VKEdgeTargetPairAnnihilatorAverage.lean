import PrimeNumberTheorem.VKEdgeTargetPairAnnihilator
import PrimeNumberTheorem.ZeroForcedOscillation

open Complex Filter MeasureTheory Set Topology
open scoped Interval

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- The scalar by which the target-pair annihilator multiplies a cosine of
frequency `lambda`. -/
def frequencyAnnihilatorMultiplier
    (gamma lambda h : ℝ) : ℝ :=
  2 * (Real.cos (lambda * h) - Real.cos (gamma * h))

/-- The selected frequency is annihilated for every step. -/
theorem frequencyAnnihilatorMultiplier_target
    (gamma h : ℝ) :
    frequencyAnnihilatorMultiplier gamma gamma h = 0 := by
  simp [frequencyAnnihilatorMultiplier]

/-- Exact finite-interval mean square of the annihilator multiplier. -/
theorem intervalIntegral_frequencyAnnihilatorMultiplier_sq
    {gamma lambda H : ℝ}
    (hgamma : gamma ≠ 0) (hlambda : lambda ≠ 0)
    (hne : lambda ≠ gamma) (hneg : lambda ≠ -gamma) :
    (∫ h in (0 : ℝ)..H,
        frequencyAnnihilatorMultiplier gamma lambda h ^ 2) =
      4 * H +
        Real.sin (2 * lambda * H) / lambda +
        Real.sin (2 * gamma * H) / gamma -
        4 * Real.sin ((lambda - gamma) * H) / (lambda - gamma) -
        4 * Real.sin ((lambda + gamma) * H) / (lambda + gamma) := by
  let primitive : ℝ → ℝ := fun h =>
    4 * h +
      Real.sin (2 * lambda * h) / lambda +
      Real.sin (2 * gamma * h) / gamma -
      4 * Real.sin ((lambda - gamma) * h) / (lambda - gamma) -
      4 * Real.sin ((lambda + gamma) * h) / (lambda + gamma)
  have hsub : lambda - gamma ≠ 0 := sub_ne_zero.mpr hne
  have hadd : lambda + gamma ≠ 0 := by
    intro hzero
    apply hneg
    linarith
  have hderiv (h : ℝ) :
      HasDerivAt primitive
        (frequencyAnnihilatorMultiplier gamma lambda h ^ 2) h := by
    have hmain : HasDerivAt (fun x : ℝ => 4 * x) 4 h := by
      convert (hasDerivAt_id h).const_mul 4 using 1 <;> ring
    have hlambdaDeriv :
        HasDerivAt
          (fun x : ℝ => Real.sin (2 * lambda * x) / lambda)
          (2 * Real.cos (2 * lambda * h)) h := by
      convert
        (((Real.hasDerivAt_sin (2 * lambda * h)).comp h
          ((hasDerivAt_const h (2 * lambda)).mul
            (hasDerivAt_id h))).div_const lambda) using 1 <;>
        field_simp [hlambda] <;>
        ring
    have hgammaDeriv :
        HasDerivAt
          (fun x : ℝ => Real.sin (2 * gamma * x) / gamma)
          (2 * Real.cos (2 * gamma * h)) h := by
      convert
        (((Real.hasDerivAt_sin (2 * gamma * h)).comp h
          ((hasDerivAt_const h (2 * gamma)).mul
            (hasDerivAt_id h))).div_const gamma) using 1 <;>
        field_simp [hgamma] <;>
        ring
    have hsubDeriv :
        HasDerivAt
          (fun x : ℝ =>
            4 * Real.sin ((lambda - gamma) * x) / (lambda - gamma))
          (4 * Real.cos ((lambda - gamma) * h)) h := by
      convert
        ((((Real.hasDerivAt_sin ((lambda - gamma) * h)).comp h
          ((hasDerivAt_const h (lambda - gamma)).mul
            (hasDerivAt_id h))).const_mul 4).div_const
              (lambda - gamma)) using 1 <;>
        field_simp [hsub] <;>
        ring
    have haddDeriv :
        HasDerivAt
          (fun x : ℝ =>
            4 * Real.sin ((lambda + gamma) * x) / (lambda + gamma))
          (4 * Real.cos ((lambda + gamma) * h)) h := by
      convert
        ((((Real.hasDerivAt_sin ((lambda + gamma) * h)).comp h
          ((hasDerivAt_const h (lambda + gamma)).mul
            (hasDerivAt_id h))).const_mul 4).div_const
              (lambda + gamma)) using 1 <;>
        field_simp [hadd] <;>
        ring
    have hcombined :=
      (((hmain.add hlambdaDeriv).add hgammaDeriv).sub hsubDeriv).sub
        haddDeriv
    convert hcombined using 1
    · unfold frequencyAnnihilatorMultiplier
      rw [show
          (2 *
              (Real.cos (lambda * h) -
                Real.cos (gamma * h))) ^ 2 =
            4 * Real.cos (lambda * h) ^ 2 +
              4 * Real.cos (gamma * h) ^ 2 -
              8 * Real.cos (lambda * h) *
                Real.cos (gamma * h) by ring]
      rw [Real.cos_sq, Real.cos_sq]
      have hproduct :=
        Real.two_mul_cos_mul_cos (lambda * h) (gamma * h)
      rw [show
          8 * Real.cos (lambda * h) *
              Real.cos (gamma * h) =
            4 *
              (Real.cos (lambda * h - gamma * h) +
                Real.cos (lambda * h + gamma * h)) by
          nlinarith]
      ring_nf
  have hint :
      IntervalIntegrable
        (fun h => frequencyAnnihilatorMultiplier gamma lambda h ^ 2)
        volume 0 H := by
    apply Continuous.intervalIntegrable
    unfold frequencyAnnihilatorMultiplier
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun h _hh => hderiv h) hint]
  dsimp [primitive]
  simp

/-- The multiplier energy per unit step length. -/
def normalizedStepMultiplierEnergy
    (gamma lambda H : ℝ) : ℝ :=
  H⁻¹ * ∫ h in (0 : ℝ)..H,
    frequencyAnnihilatorMultiplier gamma lambda h ^ 2

private theorem tendsto_sin_mul_div_atTop
    {c d : ℝ} (hd : d ≠ 0) :
    Tendsto (fun H : ℝ => Real.sin (c * H) / (d * H))
      atTop (𝓝 0) := by
  have hsinBound :
      IsBoundedUnder (· ≤ ·) atTop
        (norm ∘ fun H : ℝ => Real.sin (c * H)) := by
    apply isBoundedUnder_of_eventually_le
      (a := (1 : ℝ))
    exact Eventually.of_forall fun H => by
      simpa [Function.comp_apply, Real.norm_eq_abs] using
        Real.abs_sin_le_one (c * H)
  have hzero :
      Tendsto
        (fun H : ℝ => Real.sin (c * H) * H⁻¹)
        atTop (𝓝 0) :=
    Filter.isBoundedUnder_le_mul_tendsto_zero
      hsinBound tendsto_inv_atTop_zero
  convert hzero.const_mul d⁻¹ using 1
  · funext H
    field_simp [hd]
  · simp

/-- Averaging over the step removes every collision with a fixed distinct
positive frequency. -/
theorem tendsto_normalizedStepMultiplierEnergy
    {gamma lambda : ℝ}
    (hgamma : 0 < gamma) (hlambda : 0 < lambda)
    (hne : lambda ≠ gamma) :
    Tendsto (normalizedStepMultiplierEnergy gamma lambda)
      atTop (𝓝 4) := by
  have hsub : lambda - gamma ≠ 0 := sub_ne_zero.mpr hne
  have hadd : lambda + gamma ≠ 0 := by positivity
  have hlambdaTerm :
      Tendsto
        (fun H : ℝ => Real.sin (2 * lambda * H) / (lambda * H))
        atTop (𝓝 0) :=
    tendsto_sin_mul_div_atTop hlambda.ne'
  have hgammaTerm :
      Tendsto
        (fun H : ℝ => Real.sin (2 * gamma * H) / (gamma * H))
        atTop (𝓝 0) :=
    tendsto_sin_mul_div_atTop hgamma.ne'
  have hsubTerm :
      Tendsto
        (fun H : ℝ =>
          Real.sin ((lambda - gamma) * H) /
            ((lambda - gamma) * H))
        atTop (𝓝 0) :=
    tendsto_sin_mul_div_atTop hsub
  have haddTerm :
      Tendsto
        (fun H : ℝ =>
          Real.sin ((lambda + gamma) * H) /
            ((lambda + gamma) * H))
        atTop (𝓝 0) :=
    tendsto_sin_mul_div_atTop hadd
  have hformula :
      ∀ᶠ H : ℝ in atTop,
        normalizedStepMultiplierEnergy gamma lambda H =
          4 +
            Real.sin (2 * lambda * H) / (lambda * H) +
            Real.sin (2 * gamma * H) / (gamma * H) -
            4 *
              (Real.sin ((lambda - gamma) * H) /
                ((lambda - gamma) * H)) -
            4 *
              (Real.sin ((lambda + gamma) * H) /
                ((lambda + gamma) * H)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
    rw [normalizedStepMultiplierEnergy,
      intervalIntegral_frequencyAnnihilatorMultiplier_sq
        hgamma.ne' hlambda.ne' hne (by
          intro heq
          nlinarith)]
    field_simp [hH.ne', hgamma.ne', hlambda.ne', hsub, hadd]
  have hlimit :
      Tendsto
        (fun H : ℝ =>
          4 +
            Real.sin (2 * lambda * H) / (lambda * H) +
            Real.sin (2 * gamma * H) / (gamma * H) -
            4 *
              (Real.sin ((lambda - gamma) * H) /
                ((lambda - gamma) * H)) -
            4 *
              (Real.sin ((lambda + gamma) * H) /
                ((lambda + gamma) * H)))
        atTop (𝓝 4) := by
    convert
      (((tendsto_const_nhds.add hlambdaTerm).add hgammaTerm).sub
        (tendsto_const_nhds.mul hsubTerm)).sub
          (tendsto_const_nhds.mul haddTerm) using 1 <;>
      norm_num
  exact hlimit.congr'
    (hformula.mono fun _H hH => hH.symm)

/-- Every fixed non-target positive frequency eventually contributes at least
`2` units of normalized step energy. -/
theorem eventually_two_le_normalizedStepMultiplierEnergy
    {gamma lambda : ℝ}
    (hgamma : 0 < gamma) (hlambda : 0 < lambda)
    (hne : lambda ≠ gamma) :
    ∀ᶠ H in atTop,
      2 ≤ normalizedStepMultiplierEnergy gamma lambda H := by
  have hmem : Set.Ioi (2 : ℝ) ∈ 𝓝 4 :=
    Ioi_mem_nhds (by norm_num)
  filter_upwards [
    (tendsto_normalizedStepMultiplierEnergy hgamma hlambda hne)
      hmem] with H hH
  exact hH.le

/-- A single sufficiently long step interval separates every frequency in a
fixed finite collected package. -/
theorem eventually_two_le_normalizedStepMultiplierEnergy_finset
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (omega : ι → ℝ) {gamma : ℝ}
    (hgamma : 0 < gamma)
    (homega : ∀ i ∈ S, 0 < omega i)
    (hne : ∀ i ∈ S, omega i ≠ gamma) :
    ∀ᶠ H in atTop, ∀ i ∈ S,
      2 ≤ normalizedStepMultiplierEnergy gamma (omega i) H := by
  exact S.eventually_all.mpr fun i hi =>
    eventually_two_le_normalizedStepMultiplierEnergy
      hgamma (homega i hi) (hne i hi)

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
