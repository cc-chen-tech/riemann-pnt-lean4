import PrimeNumberTheorem.FourierL1L2
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Asymptotics

open Asymptotics Filter FourierTransform MeasureTheory Set

namespace PrimeNumberTheorem
namespace SincSquareIntegral

/-- The complex-valued indicator of the centered interval of length one. -/
noncomputable def centeredUnitIntervalIndicator (x : ℝ) : ℂ :=
  (Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)).indicator (fun _ => 1) x

/-- With Mathlib's `exp (-2*pi*i*x*xi)` convention, the Fourier transform of
the centered interval of length one is the normalized sinc `sinc (pi*xi)`. -/
theorem fourier_centeredUnitIntervalIndicator (xi : ℝ) :
    𝓕 centeredUnitIntervalIndicator xi =
      (Real.sinc (Real.pi * xi) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hindicator :
      (fun x : ℝ =>
        Complex.exp (↑(-2 * Real.pi * x * xi) * Complex.I) •
          centeredUnitIntervalIndicator x) =
      (Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)).indicator
        (fun x => Complex.exp (↑(-2 * Real.pi * x * xi) * Complex.I)) := by
    funext x
    simp [centeredUnitIntervalIndicator, Set.indicator]
  rw [hindicator, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)]
  by_cases hxi : xi = 0
  · subst xi
    norm_num
  let c : ℝ := -2 * Real.pi * xi
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hxi
  have hintegrand :
      (fun x : ℝ => Complex.exp (↑(-2 * Real.pi * x * xi) * Complex.I)) =
        fun x => Complex.exp (↑(c * x) * Complex.I) := by
    funext x
    rw [show -2 * Real.pi * x * xi = c * x by
      dsimp [c]
      ring]
  rw [hintegrand]
  have hscale := intervalIntegral.integral_comp_mul_left
    (a := -(1 / 2 : ℝ)) (b := 1 / 2)
    (fun t : ℝ => Complex.exp (t * Complex.I)) hc
  have hca : c * (-(1 / 2 : ℝ)) = Real.pi * xi := by
    dsimp [c]
    ring
  have hcb : c * (1 / 2 : ℝ) = -(Real.pi * xi) := by
    dsimp [c]
    ring
  rw [hca, hcb] at hscale
  have hright :
      (∫ t in Real.pi * xi..-(Real.pi * xi),
        Complex.exp (t * Complex.I)) =
        -(2 * (Real.pi * xi) * Real.sinc (Real.pi * xi) : ℝ) := by
    rw [intervalIntegral.integral_symm, integral_exp_mul_I_eq_sinc]
    norm_cast
  rw [hscale, hright]
  change ((c⁻¹ : ℝ) : ℂ) *
      (-((2 * (Real.pi * xi) * Real.sinc (Real.pi * xi) : ℝ) : ℂ)) = _
  dsimp [c]
  push_cast
  field_simp [Real.pi_ne_zero, hxi]

private theorem sinc_sq_norm_le_two_inv_one_add_sq
    {x : ℝ} (hx : 1 ≤ |x|) :
    ‖Real.sinc x ^ 2‖ ≤ 2 * ‖(1 + x ^ 2)⁻¹‖ := by
  have hxne : x ≠ 0 := by
    intro hx0
    subst x
    norm_num at hx
  have habspos : 0 < |x| := abs_pos.mpr hxne
  have hsinc : |Real.sinc x| ≤ |x|⁻¹ := by
    rw [Real.sinc_of_ne_zero hxne, abs_div]
    simpa [one_div] using
      (div_le_div_iff_of_pos_right habspos).2 (Real.abs_sin_le_one x)
  have hsincSq : Real.sinc x ^ 2 ≤ (x ^ 2)⁻¹ := by
    calc
      Real.sinc x ^ 2 = |Real.sinc x| ^ 2 := (sq_abs _).symm
      _ ≤ |x|⁻¹ ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) (inv_nonneg.mpr (abs_nonneg _))).2 hsinc
      _ = (x ^ 2)⁻¹ := by rw [inv_pow, sq_abs]
  have hxsq : 1 ≤ x ^ 2 := by
    have := (sq_le_sq₀ zero_le_one (abs_nonneg x)).2 hx
    simpa using this
  have hx2pos : 0 < x ^ 2 := sq_pos_of_ne_zero hxne
  have honepos : 0 < 1 + x ^ 2 := by positivity
  have hinv : (x ^ 2)⁻¹ ≤ 2 * (1 + x ^ 2)⁻¹ := by
    have hfrac : 1 / x ^ 2 ≤ 2 / (1 + x ^ 2) := by
      apply (div_le_div_iff₀ hx2pos honepos).2
      nlinarith
    simpa [one_div, div_eq_mul_inv] using hfrac
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr honepos)]
  exact hsincSq.trans hinv

private theorem sinc_sq_isBigO_atTop :
    (fun x : ℝ => Real.sinc x ^ 2) =O[atTop]
      (fun x : ℝ => (1 + x ^ 2)⁻¹) := by
  apply IsBigO.of_bound 2
  filter_upwards [Ici_mem_atTop (1 : ℝ)] with x hx
  change 1 ≤ x at hx
  exact sinc_sq_norm_le_two_inv_one_add_sq (by
    rw [abs_of_nonneg (by linarith)]
    exact hx)

private theorem sinc_sq_isBigO_atBot :
    (fun x : ℝ => Real.sinc x ^ 2) =O[atBot]
      (fun x : ℝ => (1 + x ^ 2)⁻¹) := by
  apply IsBigO.of_bound 2
  filter_upwards [Iic_mem_atBot (-1 : ℝ)] with x hx
  change x ≤ -1 at hx
  exact sinc_sq_norm_le_two_inv_one_add_sq (by
    rw [abs_of_nonpos (by linarith)]
    linarith)

theorem integrable_sinc_sq :
    Integrable (fun x : ℝ => Real.sinc x ^ 2) :=
  (Real.continuous_sinc.pow 2).locallyIntegrable.integrable_of_isBigO_atBot_atTop
    sinc_sq_isBigO_atBot
    (integrable_inv_one_add_sq.integrableAtFilter atBot)
    sinc_sq_isBigO_atTop
    (integrable_inv_one_add_sq.integrableAtFilter atTop)

theorem centeredUnitIntervalIndicator_memLp_one :
    MemLp centeredUnitIntervalIndicator 1 := by
  simpa [centeredUnitIntervalIndicator] using
    memLp_indicator_const 1 measurableSet_Icc (1 : ℂ)
      (Or.inr isCompact_Icc.measure_lt_top.ne)

theorem centeredUnitIntervalIndicator_memLp_two :
    MemLp centeredUnitIntervalIndicator 2 := by
  simpa [centeredUnitIntervalIndicator] using
    memLp_indicator_const 2 measurableSet_Icc (1 : ℂ)
      (Or.inr isCompact_Icc.measure_lt_top.ne)

theorem memLp_two_complex_sinc_pi :
    MemLp (fun x : ℝ => (Real.sinc (Real.pi * x) : ℂ)) 2 := by
  have hscaled : Integrable (fun x : ℝ => Real.sinc (Real.pi * x) ^ 2) :=
    (integrable_comp_mul_left_iff
      (fun x : ℝ => Real.sinc x ^ 2) Real.pi_ne_zero).2 integrable_sinc_sq
  rw [memLp_two_iff_integrable_sq_norm (by fun_prop)]
  convert hscaled using 1
  funext x
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Plancherel applied to the centered interval of length one. -/
theorem integral_sinc_pi_mul_sq :
    ∫ x : ℝ, Real.sinc (Real.pi * x) ^ 2 = 1 := by
  let g : ℝ → ℂ := fun x => Real.sinc (Real.pi * x)
  have hf1 := centeredUnitIntervalIndicator_memLp_one
  have hf2 := centeredUnitIntervalIndicator_memLp_two
  have hg2 : MemLp g 2 := memLp_two_complex_sinc_pi
  have hfourierEq : 𝓕 centeredUnitIntervalIndicator = g :=
    funext fourier_centeredUnitIntervalIndicator
  have hfourier2 : MemLp (𝓕 centeredUnitIntervalIndicator) 2 := by
    rw [hfourierEq]
    exact hg2
  have hfourierToLp :
      hfourier2.toLp = hg2.toLp :=
    MemLp.toLp_congr hfourier2 hg2 <|
      Filter.Eventually.of_forall fourier_centeredUnitIntervalIndicator
  have hcompat : 𝓕 hf2.toLp = hg2.toLp := calc
    _ = hfourier2.toLp :=
      FourierL1L2.fourier_toLp_two_eq_toLp_fourier hf1 hf2 hfourier2
    _ = _ := hfourierToLp
  have hleft :
      inner ℂ hg2.toLp hg2.toLp =
        Complex.ofReal (∫ x : ℝ, Real.sinc (Real.pi * x) ^ 2) := by
    change (∫ x : ℝ, inner ℂ
      ((hg2.toLp : ℝ → ℂ) x) ((hg2.toLp : ℝ → ℂ) x)) = _
    calc
      _ = ∫ x : ℝ, Complex.ofReal (Real.sinc (Real.pi * x) ^ 2) := by
        apply integral_congr_ae
        filter_upwards [hg2.coeFn_toLp] with x hx
        rw [hx]
        simp only [g, inner_self_eq_norm_sq_to_K, Complex.norm_real]
        rw [Real.norm_eq_abs]
        change Complex.ofReal |Real.sinc (Real.pi * x)| ^ 2 =
          Complex.ofReal (Real.sinc (Real.pi * x) ^ 2)
        calc
          _ = Complex.ofReal (|Real.sinc (Real.pi * x)| ^ 2) :=
            (Complex.ofReal_pow _ 2).symm
          _ = _ := congrArg Complex.ofReal (sq_abs _)
      _ = Complex.ofReal (∫ x : ℝ, Real.sinc (Real.pi * x) ^ 2) :=
        integral_ofReal
  have hright : inner ℂ hf2.toLp hf2.toLp = 1 := by
    change (∫ x : ℝ, inner ℂ
      ((hf2.toLp : ℝ → ℂ) x) ((hf2.toLp : ℝ → ℂ) x)) = 1
    calc
      _ = ∫ x : ℝ, (Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)).indicator
            (fun _ => (1 : ℂ)) x := by
        apply integral_congr_ae
        filter_upwards [hf2.coeFn_toLp] with x hx
        rw [hx]
        by_cases hmem : -(2 : ℝ)⁻¹ ≤ x ∧ x ≤ (2 : ℝ)⁻¹ <;>
          simp [centeredUnitIntervalIndicator, Set.indicator, hmem,
            inner_self_eq_norm_sq_to_K]
      _ = ∫ _x in Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ), (1 : ℂ) :=
        integral_indicator measurableSet_Icc
      _ = 1 := by
        norm_num
  have hplancherel := Lp.inner_fourier_eq hf2.toLp hf2.toLp
  rw [hcompat, hleft, hright] at hplancherel
  exact_mod_cast hplancherel

/-- The classical full-line sinc-square integral. -/
theorem integral_sinc_sq :
    ∫ x : ℝ, Real.sinc x ^ 2 = Real.pi := by
  have hscale := Measure.integral_comp_mul_left
    (fun x : ℝ => Real.sinc x ^ 2) Real.pi
  rw [integral_sinc_pi_mul_sq,
    abs_of_pos (inv_pos.mpr Real.pi_pos)] at hscale
  change 1 = Real.pi⁻¹ * (∫ y : ℝ, Real.sinc y ^ 2) at hscale
  field_simp [Real.pi_ne_zero] at hscale
  exact hscale.symm

end SincSquareIntegral
end PrimeNumberTheorem
