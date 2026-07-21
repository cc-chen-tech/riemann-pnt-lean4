import Mathlib.Analysis.Fourier.LpSpace
import MathlibAux.RectangularFourierEnvelope

/-!
# Plancherel for a rectangular sliding-window multiplier

Mathlib normalizes the Fourier transform by
`exp (-2 * pi * I * x * y)`.  Consequently the backward rectangular kernel
`1_[-H, 0]` has multiplier

`integral v in 0..H, exp (I * (2 * pi * y * v))`.

The theorem below is the exact `L2` Plancherel statement for this multiplier.
It deliberately does not identify the inverse `L2` transform with a pointwise
convolution: that compatibility is not part of Mathlib's current `L1`/`L2`
Fourier API.
-/

open Complex FourierTransform MeasureTheory Set
open scoped FourierTransform

namespace MathlibAux

/-- The exact Fourier multiplier of the backward rectangular kernel
`1_[-H, 0]`, with Mathlib's `2 * pi` Fourier normalization. -/
noncomputable def rectangularFourierMultiplier (H y : ℝ) : ℂ :=
  ∫ v in (0 : ℝ)..H,
    Complex.exp (I * ((((2 * Real.pi * y) * v : ℝ)) : ℂ))

theorem rectangularFourierMultiplier_eq (H y : ℝ) :
    rectangularFourierMultiplier H y =
      if y = 0 then (H : ℂ) else
        (Complex.exp (I * (((2 * Real.pi * y * H : ℝ)) : ℂ)) - 1) /
          (I * (((2 * Real.pi * y : ℝ)) : ℂ)) := by
  by_cases hy : y = 0
  · subst y
    simp [rectangularFourierMultiplier]
    apply Complex.ext
    · change (((H : ℂ) * 1).re) = (H : ℂ).re
      simp
    · change (((H : ℂ) * 1).im) = (H : ℂ).im
      simp
  · rw [if_neg hy]
    have hc : I * (((2 * Real.pi * y : ℝ)) : ℂ) ≠ 0 := by
      exact mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr
        (mul_ne_zero (mul_ne_zero (by positivity) Real.pi_ne_zero) hy))
    unfold rectangularFourierMultiplier
    convert integral_exp_mul_complex (a := (0 : ℝ)) (b := H) hc using 1 <;>
      push_cast <;> ring_nf
    all_goals simp

theorem measurable_rectangularFourierMultiplier (H : ℝ) :
    Measurable (rectangularFourierMultiplier H) := by
  rw [show rectangularFourierMultiplier H = fun y : ℝ =>
      if y = 0 then (H : ℂ) else
        (Complex.exp (I * (((2 * Real.pi * y * H : ℝ)) : ℂ)) - 1) /
          (I * (((2 * Real.pi * y : ℝ)) : ℂ)) by
    funext y
    exact rectangularFourierMultiplier_eq H y]
  apply Measurable.ite (measurableSet_singleton 0) measurable_const
  measurability

theorem norm_rectangularFourierMultiplier_le_length {H y : ℝ} (hH : 0 ≤ H) :
    ‖rectangularFourierMultiplier H y‖ ≤ H := by
  unfold rectangularFourierMultiplier
  convert
    (norm_integral_cexp_linear_le_length (delta := H) (omega := 2 * Real.pi * y) hH)
      using 1
  all_goals push_cast
  all_goals rfl

theorem norm_rectangularFourierMultiplier_le_frequency {H y : ℝ}
    (hH : 0 ≤ H) (hy : y ≠ 0) :
    ‖rectangularFourierMultiplier H y‖ ≤ 2 / |2 * Real.pi * y| := by
  unfold rectangularFourierMultiplier
  convert
    ((norm_integral_cexp_linear_le_min (delta := H) (omega := 2 * Real.pi * y) hH
      (mul_ne_zero (mul_ne_zero (by positivity) Real.pi_ne_zero) hy)).trans
        (min_le_right _ _)) using 1
  all_goals push_cast
  all_goals rfl

theorem norm_rectangularFourierMultiplier_le_two_div_abs {H y : ℝ}
    (hH : 0 ≤ H) (hy : y ≠ 0) :
    ‖rectangularFourierMultiplier H y‖ ≤ 2 / |y| := by
  refine (norm_rectangularFourierMultiplier_le_frequency hH hy).trans ?_
  apply div_le_div_of_nonneg_left (by positivity) (abs_pos.mpr hy)
  rw [abs_mul]
  have htwoPi : 1 ≤ |2 * Real.pi| := by
    rw [abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    nlinarith [Real.two_le_pi]
  exact le_mul_of_one_le_left (abs_nonneg y) htwoPi

theorem normSq_rectangularFourierMultiplier_mul_le_length
    {H y : ℝ} (hH : 0 ≤ H) (z : ℂ) :
    ‖rectangularFourierMultiplier H y * z‖ ^ 2 ≤ H ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right
    ((sq_le_sq₀ (norm_nonneg _) hH).2
      (norm_rectangularFourierMultiplier_le_length hH)) (sq_nonneg _)

theorem normSq_rectangularFourierMultiplier_mul_le_frequency
    {H y : ℝ} (hH : 0 ≤ H) (hy : y ≠ 0) (z : ℂ) :
    ‖rectangularFourierMultiplier H y * z‖ ^ 2 ≤ 4 * (‖z‖ ^ 2 / y ^ 2) := by
  rw [norm_mul, mul_pow]
  have hsq : ‖rectangularFourierMultiplier H y‖ ^ 2 ≤ (2 / |y|) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).2
      (norm_rectangularFourierMultiplier_le_two_div_abs hH hy)
  calc
    ‖rectangularFourierMultiplier H y‖ ^ 2 * ‖z‖ ^ 2 ≤
        (2 / |y|) ^ 2 * ‖z‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    _ = 4 * (‖z‖ ^ 2 / y ^ 2) := by
      rw [div_pow, sq_abs]
      ring

theorem memLp_rectangularFourierMultiplier_mul_fourier
    (F : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) (H : ℝ) (hH : 0 ≤ H) :
    MemLp
      (fun y : ℝ => rectangularFourierMultiplier H y *
        (𝓕 F : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) y) 2 := by
  apply (MeasureTheory.Lp.memLp
    (𝓕 F : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ))).of_le_mul
  · exact (measurable_rectangularFourierMultiplier H).aestronglyMeasurable.mul
      (MeasureTheory.Lp.aestronglyMeasurable
        (𝓕 F : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)))
  · filter_upwards with y
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_rectangularFourierMultiplier_le_length hH) (norm_nonneg _)

/-- The integral of the squared pointwise norm of an `L2` representative is
the square of its `L2` norm. -/
theorem integral_norm_sq_coeFn_eq_norm_sq
    (f : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) :
    (∫ x : ℝ, ‖f x‖ ^ 2) = ‖f‖ ^ 2 := by
  calc
    (∫ x : ℝ, ‖f x‖ ^ 2) = ∫ x : ℝ, Complex.re (inner ℂ (f x) (f x)) := by
      congr with x
      exact (inner_self_eq_norm_sq (𝕜 := ℂ) (f x)).symm
    _ = Complex.re (∫ x : ℝ, inner ℂ (f x) (f x)) :=
      integral_re (𝕜 := ℂ) (MeasureTheory.L2.integrable_inner f f)
    _ = Complex.re (inner ℂ f f) := by
      exact congrArg Complex.re (MeasureTheory.L2.inner_def f f).symm
    _ = ‖f‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) f

/-- Integral form of Plancherel for Mathlib's inverse `L2` Fourier transform.
The proof uses `MeasureTheory.Lp.norm_fourier_eq`, rather than assuming an
equality of energies. -/
theorem integral_norm_sq_fourierInv_eq
    (f : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) :
    (∫ x : ℝ, ‖(𝓕⁻ f : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) x‖ ^ 2) =
      ∫ y : ℝ, ‖f y‖ ^ 2 := by
  rw [integral_norm_sq_coeFn_eq_norm_sq, integral_norm_sq_coeFn_eq_norm_sq]
  have h := MeasureTheory.Lp.norm_fourier_eq
    (𝓕⁻ f : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ))
  rw [fourier_fourierInv_eq] at h
  exact congrArg (fun r : ℝ => r ^ 2) h.symm

/-- The frequency-side rectangular multiplier packaged as an `L2` function. -/
noncomputable def rectangularMultiplierLp
    (F : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) (H : ℝ)
    (hH : 0 ≤ H) :
    Lp (α := ℝ) ℂ 2 (volume : Measure ℝ) :=
  (memLp_rectangularFourierMultiplier_mul_fourier F H hH).toLp
    (fun y : ℝ => rectangularFourierMultiplier H y *
      (𝓕 F : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) y)

/-- Exact Plancherel identity for the rectangular-window Fourier multiplier.
This is the `L2` Fourier-theoretic content of Titchmarsh (10.7.1), with
Mathlib's `exp (-2 * pi * I * x * y)` normalization. -/
theorem rectangularMultiplier_plancherel_eq
    (F : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) (H : ℝ) (hH : 0 ≤ H) :
    (∫ t : ℝ, ‖(𝓕⁻ (rectangularMultiplierLp F H hH) :
        Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) t‖ ^ 2) =
      ∫ y : ℝ, ‖rectangularFourierMultiplier H y *
        (𝓕 F : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) y‖ ^ 2 := by
  rw [integral_norm_sq_fourierInv_eq]
  let hHF := memLp_rectangularFourierMultiplier_mul_fourier F H hH
  apply integral_congr_ae
  filter_upwards [hHF.coeFn_toLp] with y hy
  rw [rectangularMultiplierLp, hy]

/-- The low/high-frequency Titchmarsh bound for the exact rectangular
multiplier.  Because Mathlib uses the `2 * pi` Fourier normalization, its
native high-frequency estimate is sharper; the constant `4` here is the
normalization-independent weakening used in (10.7.1). -/
theorem rectangularMultiplier_plancherel_le
    (F : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) (H : ℝ) (hH : 0 < H) :
    (∫ t : ℝ, ‖(𝓕⁻ (rectangularMultiplierLp F H hH.le) :
        Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) t‖ ^ 2) ≤
      H ^ 2 * (∫ y : ℝ in {y | |y| ≤ 1 / H},
        ‖(𝓕 F : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) y‖ ^ 2) +
      4 * (∫ y : ℝ in {y | 1 / H < |y|},
        ‖(𝓕 F : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) y‖ ^ 2 / y ^ 2) := by
  rw [rectangularMultiplier_plancherel_eq F H hH.le]
  let fhat : ℝ → ℂ := fun y =>
    (𝓕 F : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) y
  let energy : ℝ → ℝ := fun y => ‖rectangularFourierMultiplier H y * fhat y‖ ^ 2
  let low : Set ℝ := {y | |y| ≤ 1 / H}
  let tail : ℝ → ℝ := fun y => (4 * ‖fhat y‖ ^ 2) / y ^ 2
  let hHF := memLp_rectangularFourierMultiplier_mul_fourier F H hH.le
  have hfourier : MemLp fhat 2 := by
    exact MeasureTheory.Lp.memLp
      (𝓕 F : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ))
  have hfhatSq : Integrable (fun y => ‖fhat y‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hfourier.1).mp hfourier
  have henergy : Integrable energy := by
    exact (memLp_two_iff_integrable_sq_norm hHF.1).mp hHF
  have hlow : MeasurableSet low := by
    exact measurableSet_le continuous_abs.measurable measurable_const
  have htailMeas : AEStronglyMeasurable tail (volume.restrict lowᶜ) := by
    have hinv : AEStronglyMeasurable (fun y : ℝ => (y ^ 2)⁻¹)
        (volume.restrict lowᶜ) := by
      exact ((measurable_id.pow_const 2).inv.aestronglyMeasurable).mono_measure
        Measure.restrict_le_self
    have hnum : AEStronglyMeasurable (fun y => 4 * ‖fhat y‖ ^ 2)
        (volume.restrict lowᶜ) :=
      (hfhatSq.aestronglyMeasurable.const_mul 4).mono_measure
        (Measure.restrict_le_self : volume.restrict lowᶜ ≤ volume)
    simpa only [tail, div_eq_mul_inv, Pi.mul_apply] using hnum.mul hinv
  have htail : IntegrableOn tail lowᶜ := by
    apply Integrable.mono'
      ((hfhatSq.const_mul (4 * H ^ 2)).integrableOn) htailMeas
    filter_upwards [ae_restrict_mem hlow.compl] with y hyLow
    have hyAbs : 1 / H < |y| := by simpa [low] using hyLow
    have hyPos : 0 < |y| := lt_of_le_of_lt (by positivity) hyAbs
    have hy : y ≠ 0 := abs_pos.mp hyPos
    have hmul : 1 ≤ H * |y| := by
      have := le_of_lt ((div_lt_iff₀ hH).mp hyAbs)
      nlinarith
    have hsq : 1 ≤ H ^ 2 * y ^ 2 := by
      have := (sq_le_sq₀ (by positivity) (mul_nonneg hH.le (abs_nonneg y))).2 hmul
      simpa only [one_pow, mul_pow, sq_abs] using this
    have hinv : 1 / y ^ 2 ≤ H ^ 2 :=
      (div_le_iff₀ (sq_pos_of_ne_zero hy)).2 (by simpa [mul_comm] using hsq)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ tail y)]
    dsimp only [tail]
    calc
      (4 * ‖fhat y‖ ^ 2) / y ^ 2 =
          (4 * ‖fhat y‖ ^ 2) * (1 / y ^ 2) := by ring
      _ ≤ (4 * ‖fhat y‖ ^ 2) * H ^ 2 :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 4 * H ^ 2 * ‖fhat y‖ ^ 2 := by ring
  have hlowBound :
      (∫ y in low, energy y) ≤ ∫ y in low, H ^ 2 * ‖fhat y‖ ^ 2 := by
    apply setIntegral_mono_on henergy.integrableOn
      ((hfhatSq.const_mul (H ^ 2)).integrableOn) hlow
    intro y _hy
    exact normSq_rectangularFourierMultiplier_mul_le_length hH.le (fhat y)
  have htailBound : (∫ y in lowᶜ, energy y) ≤ ∫ y in lowᶜ, tail y := by
    apply setIntegral_mono_on henergy.integrableOn htail hlow.compl
    intro y hyLow
    have hyAbs : 1 / H < |y| := by simpa [low] using hyLow
    have hy : y ≠ 0 := by
      exact abs_pos.mp (lt_of_le_of_lt (by positivity) hyAbs)
    convert normSq_rectangularFourierMultiplier_mul_le_frequency hH.le hy (fhat y) using 1
    all_goals simp only [tail]
    all_goals ring
  calc
    (∫ y : ℝ, energy y) = (∫ y in low, energy y) + ∫ y in lowᶜ, energy y :=
      (integral_add_compl hlow henergy).symm
    _ ≤ (∫ y in low, H ^ 2 * ‖fhat y‖ ^ 2) + ∫ y in lowᶜ, tail y :=
      add_le_add hlowBound htailBound
    _ = H ^ 2 * (∫ y in low, ‖fhat y‖ ^ 2) +
        4 * (∫ y in lowᶜ, ‖fhat y‖ ^ 2 / y ^ 2) := by
      rw [integral_const_mul]
      simp only [tail]
      have htailForm :
          (fun y : ℝ => 4 * ‖fhat y‖ ^ 2 / y ^ 2) =
            fun y : ℝ => 4 * (‖fhat y‖ ^ 2 / y ^ 2) := by
        funext y
        ring
      rw [htailForm]
      rw [integral_const_mul]
    _ = H ^ 2 * (∫ y : ℝ in {y | |y| ≤ 1 / H}, ‖fhat y‖ ^ 2) +
        4 * (∫ y : ℝ in {y | 1 / H < |y|}, ‖fhat y‖ ^ 2 / y ^ 2) := by
      have hcomp : lowᶜ = {y : ℝ | 1 / H < |y|} := by
        ext y
        simp only [low, mem_compl_iff, mem_setOf_eq]
        exact not_le
      rw [hcomp]
    _ = _ := rfl

end MathlibAux
