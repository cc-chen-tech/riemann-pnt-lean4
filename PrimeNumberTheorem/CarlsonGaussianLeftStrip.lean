import PrimeNumberTheorem.CarlsonGaussianDetectorCovering

/-! The ordinary-error Gaussian and interval estimates on the entire closed
strip `1/2 ≤ Re(s) ≤ 2/3`.  The left-shifted Littlewood line needs this
uniform version, not only the old endpoint specialization. -/

open Complex MeasureTheory Set

namespace PrimeNumberTheorem.CarlsonZeroDensity

/-- Pole removal costs at most five throughout the closed left strip. -/
theorem norm_add_one_div_sub_one_le_five_on_leftStrip
    {s : ℂ} (hs : s.re ∈ Icc (1 / 2 : ℝ) (2 / 3)) :
    ‖(s + 1) / (s - 1)‖ ≤ 5 := by
  have hden : s - 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hre
    linarith [hs.2]
  rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hden)]
  have hprod : 0 ≤ (3 * s.re - 2) * (2 * s.re - 3) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith [hs.2]) (by linarith [hs.2])
  have hsq : ‖s + 1‖ ^ 2 ≤ (5 * ‖s - 1‖) ^ 2 := by
    rw [Complex.sq_norm,
      show (5 * ‖s - 1‖) ^ 2 = 25 * ‖s - 1‖ ^ 2 by ring, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    nlinarith [sq_nonneg s.im]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

private theorem error_le_five_poleFree {x : ℝ}
    (hx : x ∈ Icc (1 / 2 : ℝ) (2 / 3)) (Y0 Y1 : ℕ) (t : ℝ) :
    ‖twoScaleMollifiedZetaError Y0 Y1 ((x : ℂ) + I * (t : ℂ))‖ ≤
      5 * ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1 ((x : ℂ) + I * (t : ℂ))‖ := by
  let s : ℂ := (x : ℂ) + I * (t : ℂ)
  have hsre : s.re = x := by simp [s]
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [hsre] at hre
    simp only [Complex.zero_re] at hre
    linarith [hx.1]
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [hsre] at hre
    simp only [Complex.one_re] at hre
    linarith [hx.2]
  have hsn1 : s ≠ -1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [hsre] at hre
    simp only [Complex.neg_re, Complex.one_re] at hre
    linarith [hx.1]
  have hplus : s + 1 ≠ 0 := by intro h; apply hsn1; linear_combination h
  have hminus : s - 1 ≠ 0 := by intro h; apply hs1; linear_combination h
  have hrecover : twoScaleMollifiedZetaError Y0 Y1 s =
      (s + 1) / (s - 1) * poleFreeTwoScaleMollifiedZetaError Y0 Y1 s := by
    rw [poleFreeTwoScaleMollifiedZetaError_eq_mul hs0 hs1 hsn1]
    field_simp [hminus, hplus]
  change ‖twoScaleMollifiedZetaError Y0 Y1 s‖ ≤
    5 * ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1 s‖
  rw [hrecover, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (norm_add_one_div_sub_one_le_five_on_leftStrip (by simpa [hsre] using hx))
    (norm_nonneg _)

private theorem continuous_error_vertical {x : ℝ}
    (hx : x ∈ Icc (1 / 2 : ℝ) (2 / 3)) (Y0 Y1 : ℕ) :
    Continuous fun t : ℝ => twoScaleMollifiedZetaError Y0 Y1
      ((x : ℂ) + I * (t : ℂ)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hs1 : (x : ℂ) + I * (t : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero,
      sub_self, add_zero, Complex.one_re] at hre
    linarith [hx.2]
  have hpoint : ContinuousAt (fun u : ℝ => (x : ℂ) + I * (u : ℂ)) t := by fun_prop
  simpa only [Function.comp_def] using
    (analyticAt_twoScaleMollifiedZetaError_of_ne_one Y0 Y1 hs1).continuousAt.comp
      (f := fun u : ℝ => (x : ℂ) + I * (u : ℂ)) hpoint

/-- The comparison proves genuine integrability and the quantitative bound
together, so neither result relies on a default value of the integral. -/
theorem gaussian_twoScaleError_leftStrip_integrable_and_le
    {Delta w x : ℝ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    (hx : x ∈ Icc (1 / 2 : ℝ) (2 / 3)) :
    Integrable (fun t : ℝ => carlsonGaussianWeight Delta w t *
      ‖twoScaleMollifiedZetaError Y0 Y1 ((x : ℂ) + I * (t : ℂ))‖ ^ 2) ∧
    (∫ t : ℝ, carlsonGaussianWeight Delta w t *
      ‖twoScaleMollifiedZetaError Y0 Y1 ((x : ℂ) + I * (t : ℂ))‖ ^ 2) ≤
      25 * ‖carlsonGaussianPoleFreeLpValueTotal Delta w Y0 Y1
        hDelta hY0 hY01 (x : ℂ)‖ ^ 2 := by
  have hx4 : (x : ℂ).re ∈ Icc (1 / 2 : ℝ) 4 := by
    change x ∈ Icc (1 / 2 : ℝ) 4
    exact ⟨hx.1, by linarith [hx.2]⟩
  let H := poleFreeTwoScaleMollifiedZetaError Y0 Y1
  let phi := carlsonGaussianHilbertSection Delta w H (x : ℂ)
  let g : ℝ → ℝ := fun t => carlsonGaussianWeight Delta w t *
    ‖twoScaleMollifiedZetaError Y0 Y1 ((x : ℂ) + I * (t : ℂ))‖ ^ 2
  have hmem : MemLp phi 2 volume :=
    memLp_carlsonGaussian_poleFreeTwoScaleMollifiedZetaError_on_half_four
      hDelta hY0 hY01 hx4
  have hphiInt : Integrable fun t => ‖phi t‖ ^ 2 :=
    (memLp_two_iff_integrable_sq_norm hmem.1).mp hmem
  have hgcont : Continuous g := by
    exact (by unfold carlsonGaussianWeight; fun_prop :
      Continuous (carlsonGaussianWeight Delta w)).mul
      ((continuous_error_vertical hx Y0 Y1).norm.pow 2)
  have hmajorInt : Integrable fun t => 25 * ‖phi t‖ ^ 2 := hphiInt.const_mul 25
  have hpoint (t : ℝ) : g t ≤ 25 * ‖phi t‖ ^ 2 := by
    have hsquared := (sq_le_sq₀ (norm_nonneg _)
      (show 0 ≤ 5 * ‖H ((x : ℂ) + I * (t : ℂ))‖ by positivity)).2
        (error_le_five_poleFree hx Y0 Y1 t)
    have hsq : ‖twoScaleMollifiedZetaError Y0 Y1 ((x : ℂ) + I * (t : ℂ))‖ ^ 2 ≤
        25 * ‖H ((x : ℂ) + I * (t : ℂ))‖ ^ 2 := by nlinarith [hsquared]
    have hweight : 0 ≤ carlsonGaussianWeight Delta w t := (Real.exp_pos _).le
    have hinflate := le_mul_of_one_le_left
      (mul_nonneg hweight (sq_nonneg ‖H ((x : ℂ) + I * (t : ℂ))‖))
      (Real.one_le_exp (show 0 ≤ x ^ 2 / Delta ^ 2 by positivity))
    calc
      g t ≤ 25 * (carlsonGaussianWeight Delta w t *
          ‖H ((x : ℂ) + I * (t : ℂ))‖ ^ 2) := by
        simpa only [g, mul_left_comm] using mul_le_mul_of_nonneg_left hsq hweight
      _ ≤ 25 * (Real.exp (x ^ 2 / Delta ^ 2) *
          (carlsonGaussianWeight Delta w t * ‖H ((x : ℂ) + I * (t : ℂ))‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hinflate (by norm_num)
      _ = 25 * ‖phi t‖ ^ 2 := by
        dsimp only [phi]
        rw [norm_sq_carlsonGaussianHilbertSection_real hDelta.ne' H x t]
        ring
  have hgInt : Integrable g := by
    apply Integrable.mono_nonneg hmajorInt hgcont.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun t => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
    · exact Filter.Eventually.of_forall hpoint
  refine ⟨hgInt, ?_⟩
  calc
    (∫ t : ℝ, g t) ≤ ∫ t : ℝ, 25 * ‖phi t‖ ^ 2 := integral_mono hgInt hmajorInt hpoint
    _ = 25 * ∫ t : ℝ, ‖phi t‖ ^ 2 := by rw [integral_const_mul]
    _ = _ := by
      rw [carlsonGaussianPoleFreeLpValueTotal_eq hDelta hY0 hY01 hx4,
        norm_sq_carlsonGaussianPoleFreeLpValue hDelta hY0 hY01 hx4]

/-- Uniform local bounds imply an interval bound on any line in the closed
left strip, including the auxiliary Littlewood line. -/
theorem integral_indicator_Icc_twoScaleError_leftStrip_le
    {Delta U V x L : ℝ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    (hx : x ∈ Icc (1 / 2 : ℝ) (2 / 3)) (hL : 0 ≤ L)
    (hLocal : ∀ w ∈ carlsonGaussianCoverCenters Delta U V,
      ‖carlsonGaussianPoleFreeLpValueTotal Delta w Y0 Y1
        hDelta hY0 hY01 (x : ℂ)‖ ^ 2 ≤ L) :
    (∫ t : ℝ, (Icc U V).indicator (fun t =>
      ‖twoScaleMollifiedZetaError Y0 Y1 ((x : ℂ) + I * (t : ℂ))‖ ^ 2) t) ≤
      Real.exp (1 / 4 : ℝ) *
        (((Nat.floor ((V - U) / Delta) + 1 : ℕ) : ℝ) * (25 * L)) := by
  let g : ℝ → ℝ := fun t =>
    ‖twoScaleMollifiedZetaError Y0 Y1 ((x : ℂ) + I * (t : ℂ))‖ ^ 2
  have hgcont : Continuous g := (continuous_error_vertical hx Y0 Y1).norm.pow 2
  have hTargetInt : Integrable ((Icc U V).indicator g) :=
    (hgcont.continuousOn.integrableOn_compact isCompact_Icc).integrable_indicator measurableSet_Icc
  have hpair (w : ℝ) := gaussian_twoScaleError_leftStrip_integrable_and_le
    (w := w) hDelta hY0 hY01 hx
  apply integral_indicator_Icc_le_floor_add_one_mul_of_local_gaussian_bound
    hDelta (show 0 ≤ 25 * L by positivity) (fun t => sq_nonneg _) hTargetInt
    (fun w _ => (hpair w).1)
  intro w hw
  exact (hpair w).2.trans (mul_le_mul_of_nonneg_left (hLocal w hw) (by norm_num))

end PrimeNumberTheorem.CarlsonZeroDensity
