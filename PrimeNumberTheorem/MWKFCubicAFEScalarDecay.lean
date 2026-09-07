import MathlibAux.GammaVerticalStripBound
import PrimeNumberTheorem.MWKFCubicAFETermwise

open Complex MeasureTheory

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Actual Gaussian decay of the gamma-only Mellin scalar

Unlike the completed-zeta numerator, this is the scalar defining each
real-product AFE weight. Its vertical integral is absolutely convergent
on every nonzero line X > -1/2. Constants below depend on fixed t and X;
this is not a T-uniform asymptotic estimate.
-/

theorem norm_cubicAFEKernelG_le (t : ℝ) (z : ℂ) :
    ‖cubicAFEKernelG t z‖ ≤ ‖Complex.exp (z^2)‖ * (1 + 4 * ‖z‖^2)^3 := by
  have hs : (1 / 2 : ℝ) ≤ ‖cubicCriticalPoint t‖ := by
    simpa [cubicCriticalPoint] using re_le_norm (cubicCriticalPoint t)
  have hu : (1 / 2 : ℝ) ≤ ‖1 - cubicCriticalPoint t‖ := by
    convert re_le_norm (1 - cubicCriticalPoint t) using 1
    norm_num [cubicCriticalPoint]
  have hfactor (w : ℂ) (hw : (1 / 2 : ℝ) ≤ ‖w‖) :
      ‖1 - z^2 / w^2‖ ≤ 1 + 4 * ‖z‖^2 := by
    have hwpos : 0 < ‖w‖^2 := by positivity
    have hdiv : ‖z‖^2 / ‖w‖^2 ≤ 4 * ‖z‖^2 := by
      apply (div_le_iff₀ hwpos).mpr
      have hsq : 1 ≤ 4 * ‖w‖^2 := by nlinarith
      nlinarith [sq_nonneg ‖z‖]
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖z^2 / w^2‖ := norm_sub_le _ _
      _ = 1 + ‖z‖^2 / ‖w‖^2 := by rw [norm_one, norm_div, norm_pow, norm_pow]
      _ ≤ _ := add_le_add le_rfl hdiv
  have hfixed : ‖1 - 4 * z^2‖ ≤ 1 + 4 * ‖z‖^2 := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖4 * z^2‖ := norm_sub_le _ _
      _ = _ := by norm_num [norm_mul, norm_pow]
  unfold cubicAFEKernelG cubicAFEPoleCanceller
  simp only [norm_mul]
  calc
    _ ≤ ‖Complex.exp (z^2)‖ *
        (((1 + 4 * ‖z‖^2) * (1 + 4 * ‖z‖^2)) * (1 + 4 * ‖z‖^2)) := by
      gcongr
      · exact hfactor _ hs
      · exact hfactor _ hu
    _ = _ := by ring

noncomputable def cubicAFEVerticalGaussianMajorant (X y : ℝ) : ℝ :=
  (1 + |X| + |y|)^6 * Real.exp (-y^2)

theorem cubicAFEVerticalGaussianMajorant_nonneg (X y : ℝ) :
    0 ≤ cubicAFEVerticalGaussianMajorant X y := by
  unfold cubicAFEVerticalGaussianMajorant
  positivity

theorem norm_cubicAFEKernelG_vertical_le (t X y : ℝ) :
    ‖cubicAFEKernelG t (cubicAFEVerticalPoint X y)‖ ≤
      (125 * Real.exp (X^2)) * cubicAFEVerticalGaussianMajorant X y := by
  let z := cubicAFEVerticalPoint X y
  let Y := 1 + |X| + |y|
  have hY : 1 ≤ Y := by dsimp [Y]; linarith [abs_nonneg X, abs_nonneg y]
  have hz : ‖z‖ ≤ Y := by
    calc
      _ ≤ ‖(X : ℂ)‖ + ‖(y : ℂ) * I‖ := norm_add_le _ _
      _ = |X| + |y| := by simp
      _ ≤ _ := by dsimp [Y]; linarith
  have hzsq : ‖z‖^2 ≤ Y^2 := by gcongr
  have hb : 1 + 4 * ‖z‖^2 ≤ 5 * Y^2 := by nlinarith
  have hzre : (z^2).re = X^2 - y^2 := by
    rw [pow_two, Complex.mul_re]
    simp [z, cubicAFEVerticalPoint]
    ring
  calc
    _ ≤ ‖Complex.exp (z^2)‖ * (1 + 4 * ‖z‖^2)^3 := norm_cubicAFEKernelG_le t z
    _ ≤ ‖Complex.exp (z^2)‖ * (5 * Y^2)^3 := by gcongr
    _ = _ := by
      rw [Complex.norm_exp, hzre, Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg]
      unfold cubicAFEVerticalGaussianMajorant
      dsimp only [Y]
      ring

theorem integrable_cubicAFEVerticalGaussianMajorant (X : ℝ) :
    Integrable (cubicAFEVerticalGaussianMajorant X) := by
  have h0 : Integrable (fun y : ℝ ↦ Real.exp (-y^2)) := by
    simpa only [neg_mul, one_mul] using (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1))
  have h6 : Integrable (fun y : ℝ ↦ |y|^6 * Real.exp (-y^2)) := by
    have hh : Integrable (fun y : ℝ ↦ y^6 * Real.exp (-y^2)) := by
      simpa only [Real.rpow_natCast, neg_mul, one_mul] using
        (integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
          (by norm_num : (-1 : ℝ) < (6 : ℕ)))
    simpa only [Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_pos (Real.exp_pos _)] using hh.norm
  have hb : Integrable (fun y : ℝ ↦
      32 * (((1 + |X|)^6 + |y|^6) * Real.exp (-y^2))) := by
    simpa only [add_mul, Pi.add_apply] using ((h0.const_mul ((1 + |X|)^6)).add h6).const_mul 32
  apply hb.mono' (by unfold cubicAFEVerticalGaussianMajorant; fun_prop)
  filter_upwards [] with y
  rw [Real.norm_of_nonneg (cubicAFEVerticalGaussianMajorant_nonneg X y)]
  have hh := add_pow_le (by positivity : (0 : ℝ) ≤ 1 + |X|) (abs_nonneg y) 6
  norm_num at hh
  exact (mul_le_mul_of_nonneg_right hh (Real.exp_pos (-y^2)).le).trans_eq (by ring)

theorem continuous_cubicAFEScalar_vertical_of_halfPlane (t : ℝ) {X : ℝ}
    (hX : -1 / 2 < X) (hne : X ≠ 0) :
    Continuous (fun y : ℝ ↦ cubicAFEScalar t (cubicAFEVerticalPoint X y)) := by
  have hc (w : ℂ) (hw : w.re = 1 / 2) :
      Continuous (fun y : ℝ ↦ Gammaℝ (w + cubicAFEVerticalPoint X y)) := by
    have harg : Continuous (fun y : ℝ ↦ w + cubicAFEVerticalPoint X y) := by
      unfold cubicAFEVerticalPoint
      fun_prop
    have hi := differentiable_Gammaℝ_inv.continuous.comp harg
    have hn (y : ℝ) : (Gammaℝ (w + cubicAFEVerticalPoint X y))⁻¹ ≠ 0 := by
      apply inv_ne_zero
      apply Gammaℝ_ne_zero_of_re_pos
      simp only [Complex.add_re, cubicAFEVerticalPoint, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
        zero_mul, sub_self, add_zero, hw]
      linarith
    have hii : Continuous (fun y : ℝ ↦ ((Gammaℝ (w + cubicAFEVerticalPoint X y))⁻¹)⁻¹) :=
      hi.inv₀ hn
    simpa only [inv_inv] using hii
  have hs := hc (cubicCriticalPoint t) (by simp [cubicCriticalPoint])
  have hu := hc (1 - cubicCriticalPoint t) (by norm_num [cubicCriticalPoint])
  have hk : Continuous (fun y : ℝ ↦ cubicAFEKernelG t (cubicAFEVerticalPoint X y)) := by
    unfold cubicAFEKernelG cubicAFEPoleCanceller cubicAFEVerticalPoint
    fun_prop
  have hv : Continuous (cubicAFEVerticalPoint X) := by unfold cubicAFEVerticalPoint; fun_prop
  have hz (y : ℝ) : cubicAFEVerticalPoint X y ≠ 0 := by
    intro hz
    exact hne (by simpa [cubicAFEVerticalPoint] using congrArg Complex.re hz)
  exact ((hk.mul (hs.mul hu)).div_const _).div₀ hv hz

theorem exists_norm_cubicAFEScalar_vertical_le (t : ℝ) {X : ℝ}
    (hX : -1 / 2 < X) (hne : X ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ,
      ‖cubicAFEScalar t (cubicAFEVerticalPoint X y)‖ ≤ C * cubicAFEVerticalGaussianMajorant X y := by
  obtain ⟨C, hC, hgamma⟩ := MathlibAux.exists_norm_Gammaℝ_le_on_positive_reIcc
    (show 0 < 1 / 2 + X by linarith) (show 0 < 1 / 2 + X by linarith)
  refine ⟨125 * Real.exp (X^2) * C^2 / ‖cubicAFEGammaProduct t 0‖ / |X|, by positivity, ?_⟩
  intro y
  have hgp : ‖cubicAFEGammaProduct t (cubicAFEVerticalPoint X y)‖ ≤ C^2 := by
    unfold cubicAFEGammaProduct
    rw [norm_mul, pow_two]
    apply mul_le_mul (hgamma _ ?_ ?_) (hgamma _ ?_ ?_) (norm_nonneg _) hC <;>
      norm_num [cubicCriticalPoint, cubicAFEVerticalPoint]
  have hz : |X| ≤ ‖cubicAFEVerticalPoint X y‖ := by
    simpa [cubicAFEVerticalPoint] using abs_re_le_norm (cubicAFEVerticalPoint X y)
  have hXpos : 0 < |X| := abs_pos.mpr hne
  have hM := cubicAFEVerticalGaussianMajorant_nonneg X y
  unfold cubicAFEScalar
  rw [norm_div, norm_div, norm_mul]
  calc
    _ ≤ ((125 * Real.exp (X^2) * cubicAFEVerticalGaussianMajorant X y) * C^2) /
        ‖cubicAFEGammaProduct t 0‖ / |X| := by
      gcongr
      exact norm_cubicAFEKernelG_vertical_le t X y
    _ = _ := by ring

theorem integrable_cubicAFEScalar_vertical (t : ℝ) {X : ℝ}
    (hX : -1 / 2 < X) (hne : X ≠ 0) :
    Integrable (fun y : ℝ ↦ cubicAFEScalar t (cubicAFEVerticalPoint X y)) := by
  obtain ⟨C, _, hC⟩ := exists_norm_cubicAFEScalar_vertical_le t hX hne
  exact ((integrable_cubicAFEVerticalGaussianMajorant X).const_mul C).mono'
    (continuous_cubicAFEScalar_vertical_of_halfPlane t hX hne).aestronglyMeasurable
    (Filter.Eventually.of_forall hC)

end PrimeNumberTheorem.MWKFCubic
