import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

open Complex FourierTransform MeasureTheory Set
open scoped ComplexConjugate FourierTransform

namespace MathlibAux

/-! # Reflection identities for Fourier energy of real-valued functions -/

theorem fourier_neg_eq_conj_of_conj_eq_self
    {F : ℝ → ℂ} (hreal : ∀ t, conj (F t) = F t) (w : ℝ) :
    𝓕 F (-w) = conj (𝓕 F w) := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with t
  simp only [smul_eq_mul, map_mul, ← Complex.exp_conj, hreal]
  congr 1
  apply congrArg Complex.exp
  simp only [Complex.conj_ofReal, conj_I]
  push_cast
  ring

theorem normSq_fourier_even_of_conj_eq_self
    {F : ℝ → ℂ} (hreal : ∀ t, conj (F t) = F t) :
    Function.Even (fun w => Complex.normSq (𝓕 F w)) := by
  intro w
  change Complex.normSq (𝓕 F (-w)) = Complex.normSq (𝓕 F w)
  rw [fourier_neg_eq_conj_of_conj_eq_self hreal]
  exact Complex.normSq_conj _

private theorem value_eq_value_abs_of_even
    {g : ℝ → ℝ} (hg : Function.Even g) (x : ℝ) : g x = g |x| := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, hg x]

theorem integral_abs_sublevel_eq_two_mul_Ioc_of_even
    (g : ℝ → ℝ) (hg : Function.Even g) {A : ℝ} (_hA : 0 ≤ A) :
    (∫ x in {x : ℝ | |x| ≤ A}, g x) =
      2 * ∫ x in Ioc 0 A, g x := by
  let f : ℝ → ℝ := fun r => (Iic A).indicator g r
  calc
    (∫ x in {x : ℝ | |x| ≤ A}, g x) = ∫ x : ℝ, f |x| := by
      rw [← integral_indicator
        (measurableSet_le continuous_abs.measurable measurable_const)]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : |x| ≤ A <;>
        simp [f, hx, value_eq_value_abs_of_even hg x]
    _ = 2 * ∫ x in Ioi (0 : ℝ), f x := integral_comp_abs
    _ = 2 * ∫ x in Ioc 0 A, g x := by
      congr 1
      rw [← integral_indicator measurableSet_Ioi,
        ← integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      filter_upwards with x
      simp only [f, indicator_apply]
      by_cases hx0 : 0 < x <;> by_cases hxA : x ≤ A <;>
        simp [hx0, hxA]

theorem integral_abs_superlevel_eq_two_mul_Ioi_of_even
    (g : ℝ → ℝ) (hg : Function.Even g) {A : ℝ} (hA : 0 ≤ A) :
    (∫ x in {x : ℝ | A < |x|}, g x) =
      2 * ∫ x in Ioi A, g x := by
  let f : ℝ → ℝ := fun r => (Ioi A).indicator g r
  calc
    (∫ x in {x : ℝ | A < |x|}, g x) = ∫ x : ℝ, f |x| := by
      rw [← integral_indicator
        (measurableSet_lt measurable_const continuous_abs.measurable)]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : A < |x| <;>
        simp [f, hx, value_eq_value_abs_of_even hg x]
    _ = 2 * ∫ x in Ioi (0 : ℝ), f x := integral_comp_abs
    _ = 2 * ∫ x in Ioi A, g x := by
      congr 1
      rw [← integral_indicator measurableSet_Ioi,
        ← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards with x
      simp only [f, indicator_apply]
      by_cases hx0 : 0 < x
      · by_cases hxA : A < x <;> simp [hx0, hxA]
      · have hxA : ¬ A < x := fun hx => hx0 (hA.trans_lt hx)
        simp [hx0, hxA]

end MathlibAux
