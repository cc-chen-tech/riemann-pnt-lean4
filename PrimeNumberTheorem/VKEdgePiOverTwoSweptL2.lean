import PrimeNumberTheorem.VKEdgePiOverTwoOrdinaryL2

open Complex Filter MeasureTheory Polynomial Set Topology

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/--
An integrable fixed-variance envelope for the Gaussian kernels obtained while
the scale `m` sweeps through `[M, R * M]`.
-/
def sweptGaussianEnvelope (q M R m y : ℝ) : ℝ :=
  Real.exp 2 * Real.sqrt (2 * R) *
    normalizedGaussian (2 * R * M) (q * m - y)

private theorem scaledGaussian_completion_square
    {m t : ℝ} (hm : 0 < m) :
    Real.exp |(Real.sqrt m)⁻¹ * t| *
        normalizedGaussian m t ≤
      Real.exp 2 *
        (Real.exp (-t ^ 2 / (8 * m)) /
          (2 * Real.sqrt (Real.pi * m))) := by
  have hsqrtPos : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  let u : ℝ := (Real.sqrt m)⁻¹ * t
  have huSq : u ^ 2 = t ^ 2 / m := by
    dsimp [u]
    rw [inv_mul_eq_div, div_pow, Real.sq_sqrt hm.le]
  have hquad : |u| - u ^ 2 / 4 ≤ 2 - u ^ 2 / 8 := by
    nlinarith [sq_nonneg (|u| - 4), sq_abs u]
  have hexp :
      Real.exp (|u| - u ^ 2 / 4) ≤
        Real.exp (2 - u ^ 2 / 8) :=
    Real.exp_le_exp.mpr hquad
  have hdenomPos : 0 < 2 * Real.sqrt (Real.pi * m) := by
    positivity
  unfold normalizedGaussian
  calc
    Real.exp |(Real.sqrt m)⁻¹ * t| *
          (Real.exp (-t ^ 2 / (4 * m)) /
            (2 * Real.sqrt (Real.pi * m))) =
        Real.exp (|u| - u ^ 2 / 4) /
          (2 * Real.sqrt (Real.pi * m)) := by
      rw [← mul_div_assoc, ← Real.exp_add]
      congr 2
      rw [huSq]
      ring
    _ ≤ Real.exp (2 - u ^ 2 / 8) /
          (2 * Real.sqrt (Real.pi * m)) :=
      div_le_div_of_nonneg_right hexp hdenomPos.le
    _ = Real.exp 2 *
          (Real.exp (-t ^ 2 / (8 * m)) /
            (2 * Real.sqrt (Real.pi * m))) := by
      rw [← mul_div_assoc, ← Real.exp_add]
      congr 2
      rw [huSq]
      field_simp
      ring

theorem exp_scaled_abs_mul_normalizedGaussian_le_sweptEnvelope
    {q M R m y : ℝ}
    (hM : 1 ≤ M) (hR : 1 ≤ R)
    (hmLower : M ≤ m) (hmUpper : m ≤ R * M) :
    Real.exp |(Real.sqrt m)⁻¹ * (q * m - y)| *
        normalizedGaussian m (q * m - y) ≤
      sweptGaussianEnvelope q M R m y := by
  have hMPos : 0 < M := zero_lt_one.trans_le hM
  have hmPos : 0 < m := hMPos.trans_le hmLower
  have hRPos : 0 < R := zero_lt_one.trans_le hR
  have hRMPos : 0 < R * M := mul_pos hRPos hMPos
  have hscalePos : 0 < 2 * R * M := by positivity
  have hbase :=
    scaledGaussian_completion_square
      (m := m) (t := q * m - y) hmPos
  rw [sweptGaussianEnvelope]
  calc
    Real.exp |(Real.sqrt m)⁻¹ * (q * m - y)| *
          normalizedGaussian m (q * m - y) ≤
        Real.exp 2 *
          (Real.exp (-(q * m - y) ^ 2 / (8 * m)) /
            (2 * Real.sqrt (Real.pi * m))) := hbase
    _ ≤ Real.exp 2 * Real.sqrt (2 * R) *
          normalizedGaussian (2 * R * M) (q * m - y) := by
      unfold normalizedGaussian
      have hexponent :
          Real.exp (-(q * m - y) ^ 2 / (8 * m)) ≤
            Real.exp (-(q * m - y) ^ 2 /
              (4 * (2 * R * M))) := by
        apply Real.exp_le_exp.mpr
        have hsquare : 0 ≤ (q * m - y) ^ 2 := sq_nonneg _
        have hdenom : m ≤ R * M := hmUpper
        apply (div_le_div_iff₀ (by positivity : 0 < 8 * m)
          (by positivity : 0 < 4 * (2 * R * M))).2
        nlinarith
      have hsqrtM :
          Real.sqrt (Real.pi * M) ≤
            Real.sqrt (Real.pi * m) := by
        exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hmLower Real.pi_pos.le)
      have hsqrtIdentity :
          Real.sqrt (2 * R) * Real.sqrt (Real.pi * M) =
            Real.sqrt (Real.pi * (2 * R * M)) := by
        rw [← Real.sqrt_mul (by positivity : 0 ≤ 2 * R)]
        congr 1
        ring
      have hprefactor :
          1 / (2 * Real.sqrt (Real.pi * m)) ≤
            Real.sqrt (2 * R) /
              (2 * Real.sqrt (Real.pi * (2 * R * M))) := by
        rw [← hsqrtIdentity]
        have hsqrtRPos : 0 < Real.sqrt (2 * R) := by positivity
        field_simp
        nlinarith
      have hexpNonneg :
          0 ≤ Real.exp (-(q * m - y) ^ 2 / (8 * m)) :=
        (Real.exp_pos _).le
      have hrightNonneg :
          0 ≤ Real.sqrt (2 * R) /
            (2 * Real.sqrt (Real.pi * (2 * R * M))) := by
        positivity
      calc
        Real.exp 2 *
              (Real.exp (-(q * m - y) ^ 2 / (8 * m)) /
                (2 * Real.sqrt (Real.pi * m))) =
            Real.exp 2 *
              (Real.exp (-(q * m - y) ^ 2 / (8 * m)) *
                (1 / (2 * Real.sqrt (Real.pi * m)))) := by ring
        _ ≤ Real.exp 2 *
              (Real.exp (-(q * m - y) ^ 2 / (8 * m)) *
                (Real.sqrt (2 * R) /
                  (2 * Real.sqrt (Real.pi * (2 * R * M))))) := by
          gcongr
        _ ≤ Real.exp 2 *
              (Real.exp (-(q * m - y) ^ 2 /
                  (4 * (2 * R * M))) *
                (Real.sqrt (2 * R) /
                  (2 * Real.sqrt (Real.pi * (2 * R * M))))) := by
          gcongr
        _ = Real.exp 2 * Real.sqrt (2 * R) *
              (Real.exp (-(q * m - y) ^ 2 /
                  (4 * (2 * R * M))) /
                (2 * Real.sqrt (Real.pi * (2 * R * M)))) := by ring

private theorem integral_normalizedGaussian_affine
    {q v y : ℝ} (hq : 0 < q) (hv : 0 < v) :
    (∫ m : ℝ, normalizedGaussian v (q * m - y)) = 1 / q := by
  have hshift :
      (∫ u : ℝ, normalizedGaussian v (u - y)) =
        ∫ u : ℝ, normalizedGaussian v u := by
    simpa [sub_eq_add_neg] using
      (integral_add_right_eq_self (normalizedGaussian v) (-y))
  have hscale :=
    Measure.integral_comp_mul_left
      (fun u : ℝ => normalizedGaussian v (u - y)) q
  rw [hshift, integral_normalizedGaussian hv] at hscale
  simpa [abs_of_pos (inv_pos.mpr hq), one_div] using hscale

theorem integral_sweptGaussianEnvelope_le
    {q M R y : ℝ}
    (hq : 0 < q) (hM : 0 < M) (hR : 0 < R) :
    (∫ m in Set.Icc M (R * M),
        sweptGaussianEnvelope q M R m y) ≤
      Real.exp 2 * Real.sqrt (2 * R) / q := by
  have hscalePos : 0 < 2 * R * M := by positivity
  have hbaseInt :
      Integrable
        (fun m : ℝ => normalizedGaussian (2 * R * M) (q * m - y)) := by
    have hshift :=
      (integrable_normalizedGaussian hscalePos).comp_add_right (-y)
    simpa [sub_eq_add_neg] using hshift.comp_mul_left' hq.ne'
  have henvelopeInt :
      Integrable (fun m : ℝ => sweptGaussianEnvelope q M R m y) := by
    simpa only [sweptGaussianEnvelope] using
      hbaseInt.const_mul (Real.exp 2 * Real.sqrt (2 * R))
  have hnonneg :
      ∀ᶠ m : ℝ in ae (volume.restrict Set.univ),
        0 ≤ sweptGaussianEnvelope q M R m y := by
    filter_upwards with m
    unfold sweptGaussianEnvelope
    exact mul_nonneg (by positivity)
      (normalizedGaussian_pos hscalePos (q * m - y)).le
  calc
    (∫ m in Set.Icc M (R * M),
        sweptGaussianEnvelope q M R m y) ≤
        ∫ m in Set.univ, sweptGaussianEnvelope q M R m y := by
      apply setIntegral_mono_set henvelopeInt.integrableOn hnonneg
      filter_upwards with m
      intro _hm
      exact Set.mem_univ m
    _ = ∫ m : ℝ, sweptGaussianEnvelope q M R m y := by simp
    _ = Real.exp 2 * Real.sqrt (2 * R) / q := by
      rw [show
          (fun m : ℝ => sweptGaussianEnvelope q M R m y) =
            fun m : ℝ =>
              (Real.exp 2 * Real.sqrt (2 * R)) *
                normalizedGaussian (2 * R * M) (q * m - y) by
        funext m
        rfl]
      rw [integral_const_mul, integral_normalizedGaussian_affine hq hscalePos]
      ring

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
