import HardyTheorem.SelbergComplexGaussianMellin

open Real Complex Set MeasureTheory

namespace HardyTheorem

/-! # Absolute convergence of the complex Gaussian Mellin line -/

/-- The absolute value of the complex-radius Mellin kernel is a fixed
`r⁻¹` multiple of the rotated Gamma Mellin transform. -/
theorem norm_Gamma_half_vertical_polar_cpow
    {phi r : ℝ} (hphi0 : 0 ≤ phi)
    (hphiPi : phi < Real.pi / 2) (hr : 0 < r) (t : ℝ) :
    ‖Complex.Gamma (((2 : ℂ) + I * t) / 2) *
        (((r : ℂ) * Complex.exp ((phi : ℂ) * I)) ^
          (-(((2 : ℂ) + I * t) / 2)))‖ =
      r⁻¹ * ‖mellin (selbergRotatedExponential phi)
        ((1 : ℂ) + I * (t / 2))‖ := by
  let q : ℂ := (1 : ℂ) + I * (t / 2)
  have hq : (((2 : ℂ) + I * t) / 2) = q := by
    dsimp [q]
    push_cast
    ring
  have hphiLow : -Real.pi < phi := by linarith [Real.pi_pos]
  have hphiHigh : phi ≤ Real.pi := by linarith [Real.pi_pos]
  rw [hq, polar_cpow_neg hr hphiLow hphiHigh]
  rw [mellin_selbergRotatedExponential hphi0 hphiPi
    (show 0 < q.re by simp [q])]
  simp only [norm_mul]
  have hradial : ‖(r : ℂ) ^ (-q)‖ = r⁻¹ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
    simp [q, Real.rpow_neg_one]
  rw [hradial]
  ring

/-- The complex Gaussian kernel is absolutely integrable on Selberg's
right line. -/
theorem integrable_Gamma_half_vertical_polar_cpow
    {phi r : ℝ} (hphi0 : 0 ≤ phi)
    (hphiPi : phi < Real.pi / 2) (hr : 0 < r) :
    Integrable (fun t : ℝ =>
      Complex.Gamma (((2 : ℂ) + I * t) / 2) *
        (((r : ℂ) * Complex.exp ((phi : ℂ) * I)) ^
          (-(((2 : ℂ) + I * t) / 2)))) := by
  let g : ℝ → ℂ := fun u =>
    mellin (selbergRotatedExponential phi) ((1 : ℂ) + I * u)
  have hg : Integrable g := by
    simpa [Complex.VerticalIntegrable, g, mul_comm] using
      verticalIntegrable_mellin_selbergRotatedExponential hphi0 hphiPi
  have hgHalf : Integrable (fun t : ℝ => g ((1 / 2 : ℝ) * t)) :=
    hg.comp_mul_left' (by norm_num)
  have hcontinuousFactor : Continuous (fun t : ℝ =>
      (r : ℂ) ^ (-((1 : ℂ) + I * (t / 2)))) := by
    have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    exact (by fun_prop : Continuous (fun t : ℝ =>
      -((1 : ℂ) + I * (t / 2)))).const_cpow (Or.inl hr0)
  have hfactorNorm : ∀ t : ℝ,
      ‖(r : ℂ) ^ (-((1 : ℂ) + I * (t / 2)))‖ ≤ r⁻¹ := by
    intro t
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
    simp [Real.rpow_neg_one]
  have hproduct : Integrable (fun t : ℝ =>
      (r : ℂ) ^ (-((1 : ℂ) + I * (t / 2))) *
        g ((1 / 2 : ℝ) * t)) := by
    exact hgHalf.bdd_mul hcontinuousFactor.aestronglyMeasurable
      (Filter.Eventually.of_forall hfactorNorm)
  apply hproduct.congr
  filter_upwards with t
  let q : ℂ := (1 : ℂ) + I * (t / 2)
  have hq : (((2 : ℂ) + I * t) / 2) = q := by
    dsimp [q]
    push_cast
    ring
  have hphiLow : -Real.pi < phi := by linarith [Real.pi_pos]
  have hphiHigh : phi ≤ Real.pi := by linarith [Real.pi_pos]
  rw [hq, polar_cpow_neg hr hphiLow hphiHigh]
  dsimp [g]
  have hhalf : (1 : ℂ) + I * (((1 / 2 : ℝ) * t : ℝ) : ℂ) = q := by
    dsimp [q]
    push_cast
    ring
  rw [hhalf, mellin_selbergRotatedExponential hphi0 hphiPi
      (show 0 < q.re by simp [q])]
  ring

/-- The `L¹` norm scales exactly as `2 / r`; this exact dependence is the
summable `n⁻²` majorant needed for the Dirichlet/integral interchange. -/
theorem integral_norm_Gamma_half_vertical_polar_cpow
    {phi r : ℝ} (hphi0 : 0 ≤ phi)
    (hphiPi : phi < Real.pi / 2) (hr : 0 < r) :
    (∫ t : ℝ, ‖Complex.Gamma (((2 : ℂ) + I * t) / 2) *
        (((r : ℂ) * Complex.exp ((phi : ℂ) * I)) ^
          (-(((2 : ℂ) + I * t) / 2)))‖) =
      2 * r⁻¹ * (∫ u : ℝ, ‖mellin (selbergRotatedExponential phi)
        ((1 : ℂ) + I * u)‖) := by
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall
    (norm_Gamma_half_vertical_polar_cpow hphi0 hphiPi hr))]
  rw [MeasureTheory.integral_const_mul]
  let h : ℝ → ℝ := fun u => ‖mellin (selbergRotatedExponential phi)
    ((1 : ℂ) + I * u)‖
  have hscale := MeasureTheory.Measure.integral_comp_mul_left h (1 / 2 : ℝ)
  have hh : ∀ t : ℝ,
      ‖mellin (selbergRotatedExponential phi)
        ((1 : ℂ) + I * (t / 2))‖ = h (t / 2) := by
    intro t
    dsimp [h]
    push_cast
    rfl
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hh)]
  change r⁻¹ * (∫ t : ℝ, h (t / 2)) = 2 * r⁻¹ * (∫ u : ℝ, h u)
  have hscale' : (∫ t : ℝ, h (t / 2)) = 2 * (∫ u : ℝ, h u) := by
    calc
      (∫ t : ℝ, h (t / 2)) = ∫ t : ℝ, h ((1 / 2 : ℝ) * t) := by
        congr 1
        funext t
        congr 1
        ring
      _ = 2 * (∫ u : ℝ, h u) := by
        norm_num at hscale ⊢
        exact hscale
  rw [hscale']
  ring

end HardyTheorem
