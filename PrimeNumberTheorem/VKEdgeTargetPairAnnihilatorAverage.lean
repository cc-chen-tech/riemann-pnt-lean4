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

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
