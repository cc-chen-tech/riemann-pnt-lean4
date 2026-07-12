import Mathlib
import PrimeNumberTheorem

/-!
# Second-order Perron inversion

This module proves an absolutely convergent, second-order Perron formula and its
finite-sum form.  The squared denominator is the first point at which Mathlib's
Fourier inversion theorem applies directly; the ordinary `1 / s` Perron kernel
is only conditionally integrable.
-/

open Complex MeasureTheory Set Filter Topology
open scoped FourierTransform

namespace PrimeNumberTheorem

/-- The Laplace transform of the first moment on the positive half-line. -/
theorem integral_mul_cexp_Ioi (a : ℂ) (ha : a.re < 0) :
    (∫ u : ℝ in Set.Ioi 0, (u : ℂ) * Complex.exp (a * u)) = 1 / a ^ 2 := by
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  have hint : IntegrableOn (fun u : ℝ => (u : ℂ) * Complex.exp (a * u)) (Ioi 0) := by
    apply Integrable.mono'
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1)
        (b := -a.re) (by norm_num) (by norm_num) (by linarith))
    · fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [norm_mul, norm_real, Complex.norm_exp, mul_re, ofReal_re, ofReal_im,
        mul_zero, sub_zero, Real.norm_eq_abs, abs_of_pos hu]
      simp [Real.rpow_one, Real.rpow_one, mul_comm]
  let F : ℝ → ℂ := fun u => Complex.exp (a * u) * (a * u - 1) / a ^ 2
  have hF : ∀ u : ℝ, HasDerivAt F ((u : ℂ) * Complex.exp (a * u)) u := by
    intro u
    let H : ℂ → ℂ := fun z => Complex.exp (a * z) * (a * z - 1) / a ^ 2
    have hH : HasDerivAt H ((u : ℂ) * Complex.exp (a * u)) (u : ℂ) := by
      dsimp [H]
      convert ((((Complex.hasDerivAt_exp (a * u)).comp (u : ℂ)
        ((hasDerivAt_id (u : ℂ)).const_mul a)).mul
          ((((hasDerivAt_id (u : ℂ)).const_mul a).sub_const 1))).div_const (a ^ 2)) using 1 <;>
        simp only [Function.comp_apply, id_eq] <;> field_simp <;> ring
    simpa [F, H] using hH.comp_ofReal
  have hlim : Filter.Tendsto F Filter.atTop (𝓝 0) := by
    have hexp : Tendsto (fun u : ℝ => Complex.exp (a * u)) atTop (𝓝 0) := by
      simpa [Complex.tendsto_exp_nhds_zero_iff] using
        tendsto_const_nhds.neg_mul_atTop ha tendsto_id
    have hmul : Tendsto (fun u : ℝ => (u : ℂ) * Complex.exp (a * u)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (-a.re) (by linarith)).congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
      rw [norm_mul, norm_real, Complex.norm_exp, mul_re, ofReal_re, ofReal_im,
        mul_zero, sub_zero, Real.norm_eq_abs, abs_of_pos hu]
      simp [Real.rpow_one]
    have hdiff :
        Tendsto (fun u : ℝ => (u : ℂ) * Complex.exp (a * u) / a -
          Complex.exp (a * u) / a ^ 2) atTop (𝓝 0) := by
      simpa using ((hmul.div_const a).sub (hexp.div_const (a ^ 2)))
    refine hdiff.congr' ?_
    filter_upwards with u
    dsimp [F]
    field_simp
  have hzero : F 0 = -(1 / a ^ 2) := by
    simp [F]
    field_simp
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    (f := F) (f' := fun u : ℝ => (u : ℂ) * Complex.exp (a * u))
    (a := 0) (m := 0) (by simpa [F] using (hF 0).continuousAt.continuousWithinAt)
    (fun u _ => hF u) hint hlim]
  rw [hzero]
  ring

/-- Continuous one-sided exponential ramp used in the second-order Perron formula. -/
noncomputable def smoothPerronStep (c : ℝ) : ℝ → ℂ :=
  fun u : ℝ => ((max u 0 : ℝ) : ℂ) * Complex.exp (-c * max u 0)

theorem fourier_smoothPerronStep (c : ℝ) (hc : 0 < c) (w : ℝ) :
    𝓕 (smoothPerronStep c) w =
      1 / ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2 := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  rw [show (fun u : ℝ =>
      Complex.exp (↑(-2 * Real.pi * u * w) * Complex.I) • smoothPerronStep c u) =
      Set.indicator (Set.Ioi 0) (fun u : ℝ =>
        (u : ℂ) * Complex.exp ((-(c : ℂ) - 2 * Real.pi * w * Complex.I) * u)) by
    funext u
    by_cases hu : u ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hu]
      have hu' : 0 < u := Set.mem_Ioi.mp hu
      simp only [smoothPerronStep, smul_eq_mul, max_eq_left hu'.le]
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    · have hu0 : u ≤ 0 := le_of_not_gt hu
      simp [smoothPerronStep, hu, max_eq_right hu0]]
  rw [MeasureTheory.integral_indicator measurableSet_Ioi]
  rw [integral_mul_cexp_Ioi (-(c : ℂ) - 2 * Real.pi * w * Complex.I) (by simp [hc])]
  congr 1
  ring_nf

theorem integrable_smoothPerronStep (c : ℝ) (hc : 0 < c) :
    Integrable (smoothPerronStep c) := by
  have hbase : IntegrableOn
      (fun u : ℝ => (u : ℂ) * Complex.exp (-c * u)) (Set.Ioi 0) := by
    apply Integrable.mono'
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1)
        (b := c) (by norm_num) (by norm_num) hc)
    · fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [norm_mul, norm_real, Complex.norm_exp, mul_re, ofReal_re, ofReal_im,
        mul_zero, sub_zero, Real.norm_eq_abs, abs_of_pos hu]
      simp [Real.rpow_one, mul_comm]
  apply (hbase.integrable_indicator measurableSet_Ioi).congr
  filter_upwards with u
  by_cases hu : 0 < u
  · simp [smoothPerronStep, hu, max_eq_left hu.le]
  · have hu0 : u ≤ 0 := le_of_not_gt hu
    simp [smoothPerronStep, hu, max_eq_right hu0]

theorem integrable_fourier_smoothPerronStep (c : ℝ) (hc : 0 < c) :
    Integrable (𝓕 (smoothPerronStep c)) := by
  rw [integrable_congr (Filter.Eventually.of_forall (fourier_smoothPerronStep c hc))]
  have hne (w : ℝ) : (c : ℂ) + 2 * Real.pi * w * Complex.I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hmeas : AEStronglyMeasurable
      (fun w : ℝ => 1 / ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) := by
    exact (continuous_const.div₀ (by fun_prop) (fun w => pow_ne_zero 2 (hne w))).aestronglyMeasurable
  apply (integrable_norm_iff hmeas).mp
  have hk : 2 * Real.pi / c ≠ 0 := by positivity
  have h := (integrable_inv_one_add_sq.comp_mul_left' hk).const_mul (c ^ (-2 : ℤ))
  convert h using 1
  funext w
  rw [show (c : ℂ) + 2 * Real.pi * w * Complex.I =
      (c : ℂ) + ((2 * Real.pi * w : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [norm_div, norm_one, norm_pow, Complex.sq_norm, Complex.normSq_add_mul_I]
  field_simp

theorem fourierInv_secondOrderPerronKernel (c : ℝ) (hc : 0 < c) (u : ℝ) :
    𝓕⁻ (fun w : ℝ => (1 / ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2 : ℂ)) u =
      smoothPerronStep c u := by
  have hcont : Continuous (smoothPerronStep c) := by
    unfold smoothPerronStep
    fun_prop
  have hinv : 𝓕⁻ (𝓕 (smoothPerronStep c)) u = smoothPerronStep c u :=
    (integrable_smoothPerronStep c hc).fourierInv_fourier_eq
      (integrable_fourier_smoothPerronStep c hc) (v := u) hcont.continuousAt
  rw [show 𝓕 (smoothPerronStep c) =
      (fun w : ℝ => (1 / ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2 : ℂ)) by
        funext w
        exact fourier_smoothPerronStep c hc w] at hinv
  exact hinv

/-- Exact second-order Perron inversion in the Fourier-normalized vertical variable. -/
theorem integral_secondOrderPerronKernel_eq (c : ℝ) (hc : 0 < c) (u : ℝ) :
    (∫ w : ℝ, Complex.exp (2 * Real.pi * (w * u) * Complex.I) /
      ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) = smoothPerronStep c u := by
  rw [← fourierInv_secondOrderPerronKernel c hc u, Real.fourierInv_eq']
  congr 1
  funext w
  simp only [smul_eq_mul, one_div]
  rw [div_eq_mul_inv]
  rw [show inner ℝ w u = w * u by change u * w = w * u; ring]
  push_cast
  ring

/-- Exact second-order Perron formula. The Fourier variable is normalized so that
`s = c + 2πiw`; equivalently this is `(2πi)⁻¹ ∫ y^s / s² ds`. -/
theorem secondOrderPerron_eq_max (c : ℝ) (hc : 0 < c) (u : ℝ) :
    (∫ w : ℝ, Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
      ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) = ((max u 0 : ℝ) : ℂ) := by
  rw [show (fun w : ℝ =>
      (Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
        ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2 : ℂ)) =
      (fun w : ℝ => (Complex.exp (c * u) *
        (Complex.exp (2 * Real.pi * (w * u) * Complex.I) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) : ℂ)) by
    funext w
    rw [show (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) =
        (c * u : ℝ) + 2 * Real.pi * (w * u) * Complex.I by push_cast; ring,
      Complex.exp_add]
    rw [show c * u = u * c by ring]
    push_cast
    ring]
  calc
    _ = Complex.exp (c * u) *
        (∫ w : ℝ, Complex.exp (2 * Real.pi * (w * u) * Complex.I) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) :=
      integral_const_mul _ _
    _ = Complex.exp (c * u) * smoothPerronStep c u := by
      rw [integral_secondOrderPerronKernel_eq c hc u]
    _ = ((max u 0 : ℝ) : ℂ) := by
      by_cases hu : 0 < u
      · simp only [smoothPerronStep, max_eq_left hu.le]
        rw [mul_left_comm, ← Complex.exp_add]
        simp
      · have hu0 : u ≤ 0 := le_of_not_gt hu
        simp [smoothPerronStep, max_eq_right hu0]

theorem integrable_secondOrderPerronKernel (c : ℝ) (hc : 0 < c) (u : ℝ) :
    Integrable (fun w : ℝ =>
      Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
        ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) := by
  have hbase : Integrable (fun w : ℝ =>
      (1 / ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2 : ℂ)) := by
    exact (integrable_fourier_smoothPerronStep c hc).congr
      (Filter.Eventually.of_forall fun w => fourier_smoothPerronStep c hc w)
  have hne (w : ℝ) : (c : ℂ) + 2 * Real.pi * w * Complex.I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  apply Integrable.mono' (hbase.norm.const_mul ‖Complex.exp (c * u)‖)
  · exact ((by fun_prop : Continuous fun w : ℝ =>
        Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u)).div₀
          (by fun_prop) (fun w => pow_ne_zero 2 (hne w))).aestronglyMeasurable
  · filter_upwards with w
    simp only [norm_div, norm_one, Complex.norm_exp]
    apply le_of_eq
    congr 2
    simp
    ring

/-- Finite-sum Perron inversion, the form needed before inserting von Mangoldt coefficients. -/
theorem integral_finset_secondOrderPerron_eq
    {ι : Type*} (S : Finset ι) (a : ι → ℂ) (u : ι → ℝ)
    (c : ℝ) (hc : 0 < c) :
    (∫ w : ℝ, ∑ i ∈ S, a i *
      (Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u i) /
        ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2)) =
      ∑ i ∈ S, a i * ((max (u i) 0 : ℝ) : ℂ) := by
  rw [MeasureTheory.integral_finset_sum S]
  · apply Finset.sum_congr rfl
    intro i hi
    calc
      (∫ w : ℝ, a i *
          (Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u i) /
            ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2)) =
        a i * (∫ w : ℝ,
          Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u i) /
            ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) :=
        integral_const_mul _ _
      _ = a i * ((max (u i) 0 : ℝ) : ℂ) := by
        rw [secondOrderPerron_eq_max c hc (u i)]
  · intro i hi
    exact (integrable_secondOrderPerronKernel c hc (u i)).const_mul (a i)

/-- First Riesz mean of the von Mangoldt coefficients. -/
noncomputable def smoothedChebyshevPsi (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ico 1 (Nat.floor x + 1),
    vonMangoldt n * Real.log (x / n)

/-- The exact second-order Perron formula for the finite von Mangoldt sum. -/
theorem integral_vonMangoldt_secondOrderPerron_eq
    (x c : ℝ) (hx : 0 < x) (hc : 0 < c) :
    (∫ w : ℝ, ∑ n ∈ Finset.Ico 1 (Nat.floor x + 1), (vonMangoldt n : ℂ) *
      (Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) *
        Real.log (x / n)) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2)) =
      (smoothedChebyshevPsi x : ℂ) := by
  rw [integral_finset_secondOrderPerron_eq
    (Finset.Ico 1 (Nat.floor x + 1)) (fun n => (vonMangoldt n : ℂ))
      (fun n => Real.log (x / n)) c hc]
  rw [smoothedChebyshevPsi, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rcases Finset.mem_Ico.mp hn with ⟨hn_one, hn_upper⟩
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn_one)
  have hn_floor : n ≤ Nat.floor x := by omega
  have hn_x : (n : ℝ) ≤ x := by
    exact le_trans (by exact_mod_cast hn_floor) (Nat.floor_le hx.le)
  have hratio : 1 ≤ x / (n : ℝ) := (le_div_iff₀ hn_pos).2 (by simpa using hn_x)
  rw [max_eq_left (Real.log_nonneg hratio)]
  exact (Complex.ofReal_mul _ _).symm

end PrimeNumberTheorem
