import HardyTheorem.SelbergExplicitFourierMass
import HardyTheorem.SelbergFourierL2Compatibility
import MathlibAux.RealFourierEnergySymmetry

open Complex FourierTransform MeasureTheory Set
open scoped ComplexConjugate FourierTransform

namespace HardyTheorem

set_option maxHeartbeats 800000

/-! # Exact `2*pi` transport of Selberg's Fourier energy -/

theorem normSq_fourier_selbergCompletedMollifiedF_eq
    {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (X : ℕ) (w : ℝ) :
    Complex.normSq (𝓕 (selbergCompletedMollifiedFComplex delta X) w) =
      (2 * Real.pi) * Complex.normSq
        (selbergExplicitInverseFourierKernel delta X (2 * Real.pi * w)) := by
  rw [fourier_selbergCompletedMollifiedF_eq_explicitKernel
    hdelta hdeltaPi X w, Complex.normSq_mul, Complex.normSq_ofReal]
  have hnonneg : 0 ≤ 2 * Real.pi := mul_nonneg (by norm_num) Real.pi_pos.le
  rw [Real.mul_self_sqrt hnonneg]

theorem integral_normSq_fourier_selberg_Ioc_eq
    {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (X : ℕ)
    {A : ℝ} (hA : 0 ≤ A) :
    (∫ w in Ioc 0 A,
      Complex.normSq (𝓕 (selbergCompletedMollifiedFComplex delta X) w)) =
      ∫ y in Ioc 0 ((2 * Real.pi) * A),
        Complex.normSq
          (selbergExplicitInverseFourierKernel delta X y) := by
  let g : ℝ → ℝ := fun y => Complex.normSq
    (selbergExplicitInverseFourierKernel delta X y)
  rw [setIntegral_congr_fun measurableSet_Ioc (fun w _ =>
    normSq_fourier_selbergCompletedMollifiedF_eq hdelta hdeltaPi X w)]
  rw [integral_const_mul]
  rw [← intervalIntegral.integral_of_le hA]
  have hscale := intervalIntegral.smul_integral_comp_mul_left
    (f := g) (a := 0) (b := A) (2 * Real.pi)
  change (2 * Real.pi) * (∫ w in 0..A, g ((2 * Real.pi) * w)) = _
  rw [← intervalIntegral.integral_of_le
    (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hA)]
  simpa only [smul_eq_mul, mul_zero] using hscale

theorem integral_normSq_fourier_selberg_div_sq_Ioi_eq
    {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (X : ℕ)
    {A : ℝ} (_hA : 0 ≤ A) :
    (∫ w in Ioi A,
      Complex.normSq (𝓕 (selbergCompletedMollifiedFComplex delta X) w) /
        w ^ 2) =
      (4 * Real.pi ^ 2) *
        ∫ y in Ioi ((2 * Real.pi) * A),
          Complex.normSq
            (selbergExplicitInverseFourierKernel delta X y) / y ^ 2 := by
  let p : ℝ := 2 * Real.pi
  let m : ℝ → ℝ := fun y => Complex.normSq
    (selbergExplicitInverseFourierKernel delta X y)
  let q : ℝ → ℝ := fun y => m y / (y / p) ^ 2
  have hp : 0 < p := by dsimp [p]; positivity
  rw [setIntegral_congr_fun measurableSet_Ioi (fun w _ => by
    rw [normSq_fourier_selbergCompletedMollifiedF_eq hdelta hdeltaPi X w])]
  have hreshape : ∀ w : ℝ,
      (2 * Real.pi) * Complex.normSq
          (selbergExplicitInverseFourierKernel delta X
            (2 * Real.pi * w)) / w ^ 2 =
        p * (m (p * w) / w ^ 2) := by
    intro w
    dsimp [p, m]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun w _ => hreshape w)]
  rw [integral_const_mul]
  have hqcomp : ∀ w : ℝ, m (p * w) / w ^ 2 = q (p * w) := by
    intro w
    dsimp [q]
    rw [mul_div_cancel_left₀ w hp.ne']
  rw [setIntegral_congr_fun measurableSet_Ioi (fun w _ => hqcomp w)]
  have hscale := integral_comp_mul_left_Ioi q A hp
  change p * (∫ w in Ioi A, q (p * w)) = _
  rw [hscale]
  simp only [smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  dsimp [q, m, p]
  by_cases hy : y = 0
  · simp [hy]
  · field_simp
    ring

private theorem conj_selbergCompletedMollifiedFComplex_eq_self
    (delta : ℝ) (X : ℕ) (t : ℝ) :
    conj (selbergCompletedMollifiedFComplex delta X t) =
      selbergCompletedMollifiedFComplex delta X t := by
  simp [selbergCompletedMollifiedFComplex]

theorem integral_normSq_selbergFourierLp_abs_le_eq
    {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (X : ℕ)
    {A : ℝ} (hA : 0 ≤ A) :
    (∫ w : ℝ in {w | |w| ≤ A},
      ‖(𝓕 ((memLp_two_selbergCompletedMollifiedF_complex
          hdelta hdeltaPi X).toLp
            (selbergCompletedMollifiedFComplex delta X)) :
          Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) w‖ ^ 2) =
      2 * ∫ y in Ioc 0 ((2 * Real.pi) * A),
        Complex.normSq
          (selbergExplicitInverseFourierKernel delta X y) := by
  let F : ℝ → ℂ := selbergCompletedMollifiedFComplex delta X
  let hF2 : MemLp F 2 :=
    memLp_two_selbergCompletedMollifiedF_complex hdelta hdeltaPi X
  let Q : ℝ → ℝ := fun w => Complex.normSq (𝓕 F w)
  have hcompat := MathlibAux.coe_fourier_toLp_two_ae_eq_of_integrable
    (integrable_selbergCompletedMollifiedF_complex hdelta hdeltaPi X) hF2
  have heven : Function.Even Q := by
    exact MathlibAux.normSq_fourier_even_of_conj_eq_self
      (conj_selbergCompletedMollifiedFComplex_eq_self delta X)
  calc
    (∫ w : ℝ in {w | |w| ≤ A},
        ‖(𝓕 (hF2.toLp F) :
          Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) w‖ ^ 2) =
      ∫ w : ℝ in {w | |w| ≤ A}, Q w := by
        apply integral_congr_ae
        filter_upwards [hcompat.filter_mono ae_restrict_le] with w hw
        rw [hw]
        dsimp [Q]
        rw [Complex.normSq_eq_norm_sq]
    _ = 2 * ∫ w in Ioc 0 A, Q w :=
      MathlibAux.integral_abs_sublevel_eq_two_mul_Ioc_of_even Q heven hA
    _ = 2 * ∫ y in Ioc 0 ((2 * Real.pi) * A),
        Complex.normSq
          (selbergExplicitInverseFourierKernel delta X y) := by
      rw [integral_normSq_fourier_selberg_Ioc_eq hdelta hdeltaPi X hA]

theorem integral_normSq_selbergFourierLp_abs_gt_eq
    {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (X : ℕ)
    {A : ℝ} (hA : 0 ≤ A) :
    (∫ w : ℝ in {w | A < |w|},
      ‖(𝓕 ((memLp_two_selbergCompletedMollifiedF_complex
          hdelta hdeltaPi X).toLp
            (selbergCompletedMollifiedFComplex delta X)) :
          Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) w‖ ^ 2 / w ^ 2) =
      (8 * Real.pi ^ 2) *
        ∫ y in Ioi ((2 * Real.pi) * A),
          Complex.normSq
            (selbergExplicitInverseFourierKernel delta X y) / y ^ 2 := by
  let F : ℝ → ℂ := selbergCompletedMollifiedFComplex delta X
  let hF2 : MemLp F 2 :=
    memLp_two_selbergCompletedMollifiedF_complex hdelta hdeltaPi X
  let Q : ℝ → ℝ := fun w => Complex.normSq (𝓕 F w) / w ^ 2
  have hcompat := MathlibAux.coe_fourier_toLp_two_ae_eq_of_integrable
    (integrable_selbergCompletedMollifiedF_complex hdelta hdeltaPi X) hF2
  have hbaseEven : Function.Even (fun w => Complex.normSq (𝓕 F w)) :=
    MathlibAux.normSq_fourier_even_of_conj_eq_self
      (conj_selbergCompletedMollifiedFComplex_eq_self delta X)
  have heven : Function.Even Q := by
    intro w
    dsimp [Q]
    rw [show Complex.normSq (𝓕 F (-w)) = Complex.normSq (𝓕 F w) from
      hbaseEven w]
    ring
  calc
    (∫ w : ℝ in {w | A < |w|},
        ‖(𝓕 (hF2.toLp F) :
          Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) w‖ ^ 2 / w ^ 2) =
      ∫ w : ℝ in {w | A < |w|}, Q w := by
        apply integral_congr_ae
        filter_upwards [hcompat.filter_mono ae_restrict_le] with w hw
        rw [hw]
        dsimp [Q]
        rw [Complex.normSq_eq_norm_sq]
    _ = 2 * ∫ w in Ioi A, Q w :=
      MathlibAux.integral_abs_superlevel_eq_two_mul_Ioi_of_even Q heven hA
    _ = (8 * Real.pi ^ 2) *
        ∫ y in Ioi ((2 * Real.pi) * A),
          Complex.normSq
            (selbergExplicitInverseFourierKernel delta X y) / y ^ 2 := by
      rw [integral_normSq_fourier_selberg_div_sq_Ioi_eq
        hdelta hdeltaPi X hA]
      ring

end HardyTheorem
