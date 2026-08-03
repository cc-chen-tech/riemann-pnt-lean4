import MathlibAux.SlidingIntegralFourierCompatibility

/-!
# Fourier energy bound for genuine sliding integrals

The abstract inverse `L2` rectangular multiplier agrees almost everywhere
with the genuine sliding integral of an `L1 ∩ L2` function.  Restricting its
nonnegative square energy to a finite interval and applying the whole-line
Plancherel estimate gives the low/high-frequency bound below.  No continuity
assumption on the original function is needed.
-/

open Complex FourierTransform MeasureTheory Set
open scoped FourierTransform

namespace MathlibAux

/-- The square energy of a genuine sliding integral on any ordered finite
interval is bounded by the low/high-frequency rectangular-multiplier energy.
The only hypotheses on `F` are `L1` integrability and membership in `L2`. -/
theorem integral_normSq_slidingIntegral_le_fourier_low_high
    {F : ℝ → ℂ} (hF1 : Integrable F) (hF2 : MemLp F 2)
    {H a b : ℝ} (hH : 0 < H) (hab : a ≤ b) :
    (∫ t in a..b,
      Complex.normSq (∫ u in t..t + H, F u)) ≤
      H ^ 2 * (∫ y : ℝ in {y | |y| ≤ 1 / H},
        ‖(𝓕 (hF2.toLp F) :
          Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) y‖ ^ 2) +
      4 * (∫ y : ℝ in {y | 1 / H < |y|},
        ‖(𝓕 (hF2.toLp F) :
          Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) y‖ ^ 2 / y ^ 2) := by
  let P : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ) :=
    𝓕⁻ (rectangularMultiplierLp (hF2.toLp F) H hH.le)
  have hPmem : MemLp (fun t : ℝ => P t) 2 :=
    MeasureTheory.Lp.memLp P
  have hPenergy : Integrable (fun t : ℝ => ‖P t‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hPmem.1).mp hPmem
  have hrecover :
      (fun t : ℝ => P t) =ᵐ[volume]
        fun t => ∫ u in t..t + H, F u := by
    simpa only [P] using
      fourierInv_rectangularMultiplierLp_ae_eq_slidingIntegral
        hF1 hF2 hH.le
  have henergy :
      (fun t : ℝ =>
        Complex.normSq (∫ u in t..t + H, F u)) =ᵐ[volume]
        fun t => ‖P t‖ ^ 2 := by
    filter_upwards [hrecover] with t ht
    rw [← ht, Complex.normSq_eq_norm_sq]
  have henergy_restrict :
      (fun t : ℝ =>
        Complex.normSq (∫ u in t..t + H, F u)) =ᵐ[
          volume.restrict (Ioc a b)]
        fun t => ‖P t‖ ^ 2 :=
    (ae_restrict_le : ae (volume.restrict (Ioc a b)) ≤ ae volume) henergy
  calc
    (∫ t in a..b,
        Complex.normSq (∫ u in t..t + H, F u)) =
        ∫ t in Ioc a b, ‖P t‖ ^ 2 := by
      rw [intervalIntegral.integral_of_le hab]
      exact integral_congr_ae henergy_restrict
    _ ≤ ∫ t : ℝ, ‖P t‖ ^ 2 :=
      setIntegral_le_integral hPenergy
        (Filter.Eventually.of_forall fun t => sq_nonneg ‖P t‖)
    _ ≤
        H ^ 2 * (∫ y : ℝ in {y | |y| ≤ 1 / H},
          ‖(𝓕 (hF2.toLp F) :
            Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) y‖ ^ 2) +
        4 * (∫ y : ℝ in {y | 1 / H < |y|},
          ‖(𝓕 (hF2.toLp F) :
            Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) y‖ ^ 2 / y ^ 2) := by
      simpa only [P] using
        rectangularMultiplier_plancherel_le (hF2.toLp F) H hH

end MathlibAux
