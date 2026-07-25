import PrimeNumberTheorem.VKEdgePiOverTwoGaussianMean

open MeasureTheory Set

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- The part of the Gaussian line lying at least `12m` from its center. -/
def gaussianTail (m : ℝ) : Set ℝ :=
  {t | 12 * m ≤ |t|}

theorem normalizedGaussian_le_doubled_scaledGaussian
    {m t : ℝ} (hm : 0 < m) (ht : t ∈ gaussianTail m) :
    normalizedGaussian m t ≤
      2 * Real.exp (-18 * m) * normalizedGaussian (2 * m) t := by
  have htAbs : 12 * m ≤ |t| := ht
  have htSq : 144 * m ^ 2 ≤ t ^ 2 := by
    nlinarith [sq_nonneg (|t| - 12 * m), sq_abs t]
  have hexponent :
      -t ^ 2 / (4 * m) ≤
        -18 * m - t ^ 2 / (8 * m) := by
    have hdiff :
        (-t ^ 2 / (4 * m)) -
            (-18 * m - t ^ 2 / (8 * m)) =
          (144 * m ^ 2 - t ^ 2) / (8 * m) := by
      field_simp
      ring
    have hquotient :
        (144 * m ^ 2 - t ^ 2) / (8 * m) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr htSq) (by positivity)
    linarith
  have hexp :
      Real.exp (-t ^ 2 / (4 * m)) ≤
        Real.exp (-18 * m) *
          Real.exp (-t ^ 2 / (8 * m)) := by
    calc
      Real.exp (-t ^ 2 / (4 * m)) ≤
          Real.exp (-18 * m - t ^ 2 / (8 * m)) :=
        Real.exp_le_exp.mpr hexponent
      _ = Real.exp (-18 * m) *
          Real.exp (-t ^ 2 / (8 * m)) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hpim : 0 < Real.pi * m := mul_pos Real.pi_pos hm
  have hpiTwoM : 0 < Real.pi * (2 * m) := by positivity
  have hroot :
      Real.sqrt (Real.pi * (2 * m)) ≤
        2 * Real.sqrt (Real.pi * m) := by
    have hsqrtM := Real.sq_sqrt hpim.le
    have hsqrtTwoM := Real.sq_sqrt hpiTwoM.le
    have hleft := Real.sqrt_nonneg (Real.pi * (2 * m))
    have hright := Real.sqrt_nonneg (Real.pi * m)
    nlinarith
  have hreciprocal :
      1 / (2 * Real.sqrt (Real.pi * m)) ≤
        2 / (2 * Real.sqrt (Real.pi * (2 * m))) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  unfold normalizedGaussian
  calc
    Real.exp (-t ^ 2 / (4 * m)) /
          (2 * Real.sqrt (Real.pi * m)) =
        Real.exp (-t ^ 2 / (4 * m)) *
          (1 / (2 * Real.sqrt (Real.pi * m))) := by ring
    _ ≤
        (Real.exp (-18 * m) *
            Real.exp (-t ^ 2 / (8 * m))) *
          (2 / (2 * Real.sqrt (Real.pi * (2 * m)))) :=
      mul_le_mul hexp hreciprocal (by positivity) (by positivity)
    _ =
        2 * Real.exp (-18 * m) *
          (Real.exp (-t ^ 2 / (4 * (2 * m))) /
            (2 * Real.sqrt (Real.pi * (2 * m)))) := by
      have hexponentTwo :
          -t ^ 2 / (8 * m) = -t ^ 2 / (4 * (2 * m)) := by
        ring
      rw [hexponentTwo]
      ring

/--
The normalized Gaussian mass outside distance `12m` is exponentially small.
The loose constant `2` avoids introducing a separate `sqrt 2` factor.
-/
theorem integral_normalizedGaussian_gaussianTail_le
    {m : ℝ} (hm : 0 < m) :
    (∫ t : ℝ in gaussianTail m, normalizedGaussian m t) ≤
      2 * Real.exp (-18 * m) := by
  have htwoM : 0 < 2 * m := by positivity
  have htailMeasurable : MeasurableSet (gaussianTail m) := by
    exact measurableSet_le measurable_const continuous_abs.measurable
  have hleftInt :
      IntegrableOn (normalizedGaussian m) (gaussianTail m) :=
    (integrable_normalizedGaussian hm).integrableOn
  have hmajorInt :
      Integrable
        (fun t : ℝ =>
          2 * Real.exp (-18 * m) * normalizedGaussian (2 * m) t) :=
    (integrable_normalizedGaussian htwoM).const_mul _
  calc
    (∫ t : ℝ in gaussianTail m, normalizedGaussian m t) ≤
        ∫ t : ℝ in gaussianTail m,
          2 * Real.exp (-18 * m) *
            normalizedGaussian (2 * m) t := by
      apply setIntegral_mono_on hleftInt hmajorInt.integrableOn htailMeasurable
      intro t ht
      exact normalizedGaussian_le_doubled_scaledGaussian hm ht
    _ ≤
        ∫ t : ℝ,
          2 * Real.exp (-18 * m) *
            normalizedGaussian (2 * m) t :=
      setIntegral_le_integral hmajorInt
        (Filter.Eventually.of_forall fun t =>
          mul_nonneg (by positivity)
            (normalizedGaussian_pos htwoM t).le)
    _ = 2 * Real.exp (-18 * m) := by
      rw [integral_const_mul, integral_normalizedGaussian htwoM, mul_one]

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
