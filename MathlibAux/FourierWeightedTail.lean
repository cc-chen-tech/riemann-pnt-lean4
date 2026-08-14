import MathlibAux.SlidingWindowParseval

/-!
# A weighted high-frequency Fourier tail bound

On the region `|y| > 1 / H`, the reciprocal-square weight is at most `H ^ 2`.
Combining this pointwise estimate with Plancherel gives a reusable bound for
the high-frequency term in sliding-window Fourier arguments.
-/

open Complex FourierTransform MeasureTheory Set
open scoped FourierTransform

namespace MathlibAux

/-- The reciprocal-square weighted Fourier energy above frequency `1 / H`
is at most `H ^ 2` times the original `L2` energy. -/
theorem integral_normSq_fourier_weightedTail_le
    {F : ℝ → ℂ} (hF2 : MemLp F 2) {H : ℝ} (hH : 0 < H) :
    (∫ y : ℝ in {y | 1 / H < |y|},
      ‖(𝓕 (hF2.toLp F) :
        Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) y‖ ^ 2 / y ^ 2) ≤
      H ^ 2 * ∫ y : ℝ, ‖F y‖ ^ 2 := by
  let f : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ) := hF2.toLp F
  let fhat : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ) := 𝓕 f
  let tail : Set ℝ := {y | 1 / H < |y|}
  let weighted : ℝ → ℝ := fun y => ‖fhat y‖ ^ 2 / y ^ 2
  have hfhatMem : MemLp (fun y : ℝ => fhat y) 2 :=
    MeasureTheory.Lp.memLp fhat
  have hfhatSq : Integrable (fun y : ℝ => ‖fhat y‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hfhatMem.1).mp hfhatMem
  have htailMeas : MeasurableSet tail := by
    exact measurableSet_lt measurable_const continuous_abs.measurable
  have hweightedMeas :
      AEStronglyMeasurable weighted (volume.restrict tail) := by
    have hinv : AEStronglyMeasurable (fun y : ℝ => (y ^ 2)⁻¹)
        (volume.restrict tail) := by
      exact ((measurable_id.pow_const 2).inv.aestronglyMeasurable).mono_measure
        Measure.restrict_le_self
    have hnum : AEStronglyMeasurable (fun y : ℝ => ‖fhat y‖ ^ 2)
        (volume.restrict tail) :=
      hfhatSq.aestronglyMeasurable.mono_measure Measure.restrict_le_self
    simpa only [weighted, div_eq_mul_inv, Pi.mul_def] using hnum.mul hinv
  have hpoint (y : ℝ) (hy : y ∈ tail) :
      weighted y ≤ H ^ 2 * ‖fhat y‖ ^ 2 := by
    have hyAbs : 1 / H < |y| := by simpa only [tail, mem_setOf_eq] using hy
    have hyPos : 0 < |y| := lt_of_le_of_lt (by positivity) hyAbs
    have hyNe : y ≠ 0 := abs_pos.mp hyPos
    have hmul : 1 ≤ H * |y| := by
      exact le_of_lt (by
        simpa only [mul_comm] using (div_lt_iff₀ hH).mp hyAbs)
    have hsq : 1 ≤ H ^ 2 * y ^ 2 := by
      have hmulSq :=
        (sq_le_sq₀ (by positivity) (mul_nonneg hH.le (abs_nonneg y))).2 hmul
      simpa only [one_pow, mul_pow, sq_abs] using hmulSq
    have hinv : 1 / y ^ 2 ≤ H ^ 2 :=
      (div_le_iff₀ (sq_pos_of_ne_zero hyNe)).2
        (by simpa only [one_mul, mul_comm] using hsq)
    calc
      weighted y = ‖fhat y‖ ^ 2 * (1 / y ^ 2) := by
        simp only [weighted]
        ring
      _ ≤ ‖fhat y‖ ^ 2 * H ^ 2 :=
        mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
      _ = H ^ 2 * ‖fhat y‖ ^ 2 := mul_comm _ _
  have hweighted : IntegrableOn weighted tail := by
    apply Integrable.mono'
      ((hfhatSq.const_mul (H ^ 2)).integrableOn) hweightedMeas
    filter_upwards [ae_restrict_mem htailMeas] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      simp only [weighted]
      positivity)]
    exact hpoint y hy
  have hrestricted :
      (∫ y in tail, weighted y) ≤
        ∫ y in tail, H ^ 2 * ‖fhat y‖ ^ 2 := by
    apply setIntegral_mono_on hweighted
      ((hfhatSq.const_mul (H ^ 2)).integrableOn) htailMeas
    exact hpoint
  have hcoe : (fun y : ℝ => f y) =ᵐ[volume] F := by
    simpa only [f] using hF2.coeFn_toLp
  calc
    (∫ y : ℝ in {y | 1 / H < |y|},
        ‖(𝓕 (hF2.toLp F) :
          Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) y‖ ^ 2 / y ^ 2) =
        ∫ y in tail, weighted y := rfl
    _ ≤ ∫ y in tail, H ^ 2 * ‖fhat y‖ ^ 2 := hrestricted
    _ ≤ ∫ y : ℝ, H ^ 2 * ‖fhat y‖ ^ 2 :=
      setIntegral_le_integral (hfhatSq.const_mul (H ^ 2))
        (Filter.Eventually.of_forall fun y =>
          mul_nonneg (sq_nonneg H) (sq_nonneg ‖fhat y‖))
    _ = H ^ 2 * ∫ y : ℝ, ‖fhat y‖ ^ 2 := by
      rw [integral_const_mul]
    _ = H ^ 2 * ∫ y : ℝ, ‖f y‖ ^ 2 := by
      congr 1
      rw [integral_norm_sq_coeFn_eq_norm_sq,
        integral_norm_sq_coeFn_eq_norm_sq]
      exact congrArg (fun r : ℝ => r ^ 2)
        (MeasureTheory.Lp.norm_fourier_eq f)
    _ = H ^ 2 * ∫ y : ℝ, ‖F y‖ ^ 2 := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hcoe] with y hy
      rw [hy]

end MathlibAux
