import PrimeNumberTheorem.CarlsonGaussianFiniteCovering
import PrimeNumberTheorem.CarlsonGaussianPoleFreeBoundaryContinuity

/-!
# From the pole-free Gaussian norm to the ordinary Carlson detector

On the line `Re(s)=2/3`, removal of the harmless pole factor costs at most
`5` pointwise, hence `25` in the second moment.  Combining this fact with the
finite Gaussian covering theorem gives the exact local-to-interval adapter
needed after the Hilbert-valued three-lines argument.
-/

open Complex Set MeasureTheory

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- The inverse pole-removal factor costs at most `5` on `Re(s)=2/3`. -/
theorem norm_add_one_div_sub_one_le_five_of_re_eq_two_thirds
    {s : ℂ} (hs : s.re = 2 / 3) :
    ‖(s + 1) / (s - 1)‖ ≤ 5 := by
  have hden : s - 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hre
    rw [hs] at hre
    norm_num at hre
  rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hden)]
  have hsq : ‖s + 1‖ ^ 2 ≤ (5 * ‖s - 1‖) ^ 2 := by
    rw [Complex.sq_norm]
    rw [show (5 * ‖s - 1‖) ^ 2 = 25 * ‖s - 1‖ ^ 2 by ring]
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    rw [hs]
    nlinarith [sq_nonneg s.im]
  exact (sq_le_sq₀ (norm_nonneg (s + 1))
    (mul_nonneg (by norm_num) (norm_nonneg (s - 1)))).mp hsq

/-- On `Re(s)=2/3`, the ordinary mollified zeta error is at most five times
the pole-free error. -/
theorem norm_twoScaleMollifiedZetaError_le_five_mul_poleFree_two_thirds
    (Y0 Y1 : ℕ) (t : ℝ) :
    ‖twoScaleMollifiedZetaError Y0 Y1
        (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ))‖ ≤
      5 * ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1
        (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ))‖ := by
  let s : ℂ := ((2 / 3 : ℝ) : ℂ) + I * (t : ℂ)
  have hsre : s.re = 2 / 3 := by simp [s]
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [s] at hre
  have hsneg1 : s ≠ -1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [s] at hre
  have hplus : s + 1 ≠ 0 := by
    intro h
    apply hsneg1
    linear_combination h
  have hminus : s - 1 ≠ 0 := by
    intro h
    apply hs1
    linear_combination h
  have hfactor := poleFreeTwoScaleMollifiedZetaError_eq_mul
    (Y0 := Y0) (Y1 := Y1) hs0 hs1 hsneg1
  have hrecover :
      twoScaleMollifiedZetaError Y0 Y1 s =
        (s + 1) / (s - 1) * poleFreeTwoScaleMollifiedZetaError Y0 Y1 s := by
    rw [hfactor]
    field_simp [hminus, hplus]
  change ‖twoScaleMollifiedZetaError Y0 Y1 s‖ ≤
    5 * ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1 s‖
  rw [hrecover, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (norm_add_one_div_sub_one_le_five_of_re_eq_two_thirds hsre)
    (norm_nonneg _)

/-- The ordinary two-scale error is continuous on the `2/3` vertical line. -/
theorem continuous_twoScaleMollifiedZetaError_vertical_two_thirds
    (Y0 Y1 : ℕ) :
    Continuous fun t : ℝ => twoScaleMollifiedZetaError Y0 Y1
      (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ)) := by
  rw [continuous_iff_continuousAt]
  intro t
  let point : ℝ → ℂ := fun u => ((2 / 3 : ℝ) : ℂ) + I * (u : ℂ)
  have hpoint : ContinuousAt point t := by
    dsimp [point]
    fun_prop
  have hs1 : point t ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [point] at hre
  have hanalytic := analyticAt_twoScaleMollifiedZetaError_of_ne_one
    Y0 Y1 hs1
  simpa [point, Function.comp_def] using hanalytic.continuousAt.comp hpoint

/-- A local Gaussian second moment of the ordinary error on `Re(s)=2/3`
is at most `25` times the squared norm of the pole-free Gaussian `L²` value.
-/
theorem integral_gaussian_norm_sq_twoScaleMollifiedZetaError_two_thirds_le
    {Delta w : ℝ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1) :
    (∫ t : ℝ, carlsonGaussianWeight Delta w t *
        ‖twoScaleMollifiedZetaError Y0 Y1
          (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2) ≤
      25 * ‖carlsonGaussianPoleFreeLpValue Delta w Y0 Y1
        hDelta hY0 hY01 ((2 / 3 : ℝ) : ℂ)
          (by norm_num : (((2 / 3 : ℝ) : ℂ).re) ∈ Icc (1 / 2 : ℝ) 4)‖ ^ 2 := by
  let H : ℂ → ℂ := poleFreeTwoScaleMollifiedZetaError Y0 Y1
  let phi : ℝ → ℂ := carlsonGaussianHilbertSection Delta w H
    ((2 / 3 : ℝ) : ℂ)
  let g : ℝ → ℝ := fun t => carlsonGaussianWeight Delta w t *
    ‖twoScaleMollifiedZetaError Y0 Y1
      (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2
  have hmem : MemLp phi 2 volume := by
    exact memLp_carlsonGaussian_poleFreeTwoScaleMollifiedZetaError_on_half_four
      (Delta := Delta) (w := w) (z := ((2 / 3 : ℝ) : ℂ))
      hDelta hY0 hY01
        (by norm_num : (((2 / 3 : ℝ) : ℂ).re) ∈ Icc (1 / 2 : ℝ) 4)
  have hsectionInt : Integrable (fun t => ‖phi t‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hmem.1).mp hmem
  have hgcont : Continuous g := by
    dsimp [g]
    exact (by
      unfold carlsonGaussianWeight
      fun_prop : Continuous (carlsonGaussianWeight Delta w)).mul
      ((continuous_twoScaleMollifiedZetaError_vertical_two_thirds Y0 Y1).norm.pow 2)
  have hmajorInt : Integrable (fun t => 25 * ‖phi t‖ ^ 2) :=
    hsectionInt.const_mul 25
  have hpoint (t : ℝ) : g t ≤ 25 * ‖phi t‖ ^ 2 := by
    have hnorm :=
      norm_twoScaleMollifiedZetaError_le_five_mul_poleFree_two_thirds Y0 Y1 t
    have hsq :
        ‖twoScaleMollifiedZetaError Y0 Y1
          (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2 ≤
          25 * ‖H (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2 := by
      have := (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (by norm_num) (norm_nonneg _))).2 hnorm
      change ‖twoScaleMollifiedZetaError Y0 Y1
          (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2 ≤
        25 * ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1
          (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2
      calc
        _ ≤ (5 * ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1
            (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ))‖) ^ 2 := this
        _ = _ := by ring
    have hweight : 0 ≤ carlsonGaussianWeight Delta w t :=
      (Real.exp_pos _).le
    have hexp : 1 ≤ Real.exp ((2 / 3 : ℝ) ^ 2 / Delta ^ 2) :=
      Real.one_le_exp (by positivity)
    dsimp [g, phi]
    rw [norm_sq_carlsonGaussianHilbertSection_real hDelta.ne' H
      (2 / 3 : ℝ) t]
    calc
      carlsonGaussianWeight Delta w t *
            ‖twoScaleMollifiedZetaError Y0 Y1
              (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2
          ≤ carlsonGaussianWeight Delta w t *
              (25 * ‖H (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hweight
      _ = 25 * (carlsonGaussianWeight Delta w t *
            ‖H (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2) := by ring
      _ ≤ 25 * (Real.exp ((2 / 3 : ℝ) ^ 2 / Delta ^ 2) *
            carlsonGaussianWeight Delta w t *
            ‖H (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        calc
          carlsonGaussianWeight Delta w t *
                ‖H (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2
              ≤ Real.exp ((2 / 3 : ℝ) ^ 2 / Delta ^ 2) *
                  (carlsonGaussianWeight Delta w t *
                    ‖H (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2) :=
            le_mul_of_one_le_left
              (mul_nonneg hweight (sq_nonneg _)) hexp
          _ = Real.exp ((2 / 3 : ℝ) ^ 2 / Delta ^ 2) *
                carlsonGaussianWeight Delta w t *
                ‖H (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2 := by ring
  have hgInt : Integrable g := by
    apply Integrable.mono_nonneg hmajorInt hgcont.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun t =>
        mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
    · exact Filter.Eventually.of_forall hpoint
  calc
    (∫ t : ℝ, g t) ≤ ∫ t : ℝ, 25 * ‖phi t‖ ^ 2 :=
      integral_mono hgInt hmajorInt hpoint
    _ = 25 * ∫ t : ℝ, ‖phi t‖ ^ 2 := by rw [integral_const_mul]
    _ = 25 * ‖carlsonGaussianPoleFreeLpValue Delta w Y0 Y1
        hDelta hY0 hY01 ((2 / 3 : ℝ) : ℂ)
          (by norm_num : (((2 / 3 : ℝ) : ℂ).re) ∈ Icc (1 / 2 : ℝ) 4)‖ ^ 2 := by
      rw [norm_sq_carlsonGaussianPoleFreeLpValue hDelta hY0 hY01]

/-- Uniform local pole-free Gaussian norm bounds imply an unweighted
interval second-moment bound for the ordinary Carlson error. -/
theorem integral_indicator_Icc_norm_sq_twoScaleMollifiedZetaError_two_thirds_le
    {Delta U V L : ℝ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    (hL : 0 ≤ L)
    (hLocal : ∀ w ∈ carlsonGaussianCoverCenters Delta U V,
      ‖carlsonGaussianPoleFreeLpValue Delta w Y0 Y1
        hDelta hY0 hY01 ((2 / 3 : ℝ) : ℂ)
          (by norm_num : (((2 / 3 : ℝ) : ℂ).re) ∈ Icc (1 / 2 : ℝ) 4)‖ ^ 2 ≤ L) :
    (∫ t : ℝ, (Icc U V).indicator (fun t =>
        ‖twoScaleMollifiedZetaError Y0 Y1
          (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2) t) ≤
      Real.exp (1 / 4 : ℝ) *
        (((Nat.floor ((V - U) / Delta) + 1 : ℕ) : ℝ) * (25 * L)) := by
  let g : ℝ → ℝ := fun t =>
    ‖twoScaleMollifiedZetaError Y0 Y1
      (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2
  have hgcont : Continuous g :=
    (continuous_twoScaleMollifiedZetaError_vertical_two_thirds Y0 Y1).norm.pow 2
  have hTargetInt : Integrable ((Icc U V).indicator g) :=
    (hgcont.continuousOn.integrableOn_compact isCompact_Icc).integrable_indicator
      measurableSet_Icc
  have hLocalInt : ∀ w ∈ carlsonGaussianCoverCenters Delta U V,
      Integrable (fun t => carlsonGaussianWeight Delta w t * g t) := by
    intro w _hw
    dsimp [g]
    have hcont : Continuous fun t => carlsonGaussianWeight Delta w t *
        ‖twoScaleMollifiedZetaError Y0 Y1
          (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2 := by
      exact (by
        unfold carlsonGaussianWeight
        fun_prop : Continuous (carlsonGaussianWeight Delta w)).mul hgcont
    have hbound :=
      integral_gaussian_norm_sq_twoScaleMollifiedZetaError_two_thirds_le
        (Delta := Delta) (w := w) (Y0 := Y0) (Y1 := Y1)
        hDelta hY0 hY01
    let H : ℂ → ℂ := poleFreeTwoScaleMollifiedZetaError Y0 Y1
    let phi : ℝ → ℂ := carlsonGaussianHilbertSection Delta w H
      ((2 / 3 : ℝ) : ℂ)
    have hmem : MemLp phi 2 volume := by
      exact memLp_carlsonGaussian_poleFreeTwoScaleMollifiedZetaError_on_half_four
        (Delta := Delta) (w := w) (z := ((2 / 3 : ℝ) : ℂ))
        hDelta hY0 hY01
          (by norm_num : (((2 / 3 : ℝ) : ℂ).re) ∈ Icc (1 / 2 : ℝ) 4)
    have hsectionInt : Integrable (fun t => ‖phi t‖ ^ 2) :=
      (memLp_two_iff_integrable_sq_norm hmem.1).mp hmem
    have hmajorInt : Integrable (fun t => 25 * ‖phi t‖ ^ 2) :=
      hsectionInt.const_mul 25
    apply Integrable.mono_nonneg hmajorInt hcont.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun t =>
        mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
    · exact Filter.Eventually.of_forall fun t => by
        have hnorm :=
          norm_twoScaleMollifiedZetaError_le_five_mul_poleFree_two_thirds
            Y0 Y1 t
        have hsq :
            ‖twoScaleMollifiedZetaError Y0 Y1
              (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2 ≤
              25 * ‖H (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2 := by
          have := (sq_le_sq₀ (norm_nonneg _)
            (mul_nonneg (by norm_num) (norm_nonneg _))).2 hnorm
          change ‖twoScaleMollifiedZetaError Y0 Y1
              (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2 ≤
            25 * ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1
              (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2
          calc
            _ ≤ (5 * ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1
                (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ))‖) ^ 2 := this
            _ = _ := by ring
        have hweight : 0 ≤ carlsonGaussianWeight Delta w t :=
          (Real.exp_pos _).le
        have hexp : 1 ≤ Real.exp ((2 / 3 : ℝ) ^ 2 / Delta ^ 2) :=
          Real.one_le_exp (by positivity)
        dsimp [phi]
        rw [norm_sq_carlsonGaussianHilbertSection_real hDelta.ne' H
          (2 / 3 : ℝ) t]
        calc
          carlsonGaussianWeight Delta w t *
                ‖twoScaleMollifiedZetaError Y0 Y1
                  (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2
              ≤ carlsonGaussianWeight Delta w t *
                  (25 * ‖H (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hsq hweight
          _ = 25 * (carlsonGaussianWeight Delta w t *
                ‖H (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2) := by ring
          _ ≤ 25 * (Real.exp ((2 / 3 : ℝ) ^ 2 / Delta ^ 2) *
                carlsonGaussianWeight Delta w t *
                ‖H (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            calc
              carlsonGaussianWeight Delta w t *
                    ‖H (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2
                  ≤ Real.exp ((2 / 3 : ℝ) ^ 2 / Delta ^ 2) *
                      (carlsonGaussianWeight Delta w t *
                        ‖H (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2) :=
                le_mul_of_one_le_left
                  (mul_nonneg hweight (sq_nonneg _)) hexp
              _ = Real.exp ((2 / 3 : ℝ) ^ 2 / Delta ^ 2) *
                    carlsonGaussianWeight Delta w t *
                    ‖H (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2 := by ring
  apply integral_indicator_Icc_le_floor_add_one_mul_of_local_gaussian_bound
    hDelta (mul_nonneg (by norm_num) hL) (fun t => sq_nonneg _)
    hTargetInt hLocalInt
  intro w hw
  calc
    (∫ t : ℝ, carlsonGaussianWeight Delta w t * g t) ≤
        25 * ‖carlsonGaussianPoleFreeLpValue Delta w Y0 Y1
          hDelta hY0 hY01 ((2 / 3 : ℝ) : ℂ)
            (by norm_num : (((2 / 3 : ℝ) : ℂ).re) ∈ Icc (1 / 2 : ℝ) 4)‖ ^ 2 :=
      integral_gaussian_norm_sq_twoScaleMollifiedZetaError_two_thirds_le
        hDelta hY0 hY01
    _ ≤ 25 * L := mul_le_mul_of_nonneg_left (hLocal w hw) (by norm_num)

end CarlsonZeroDensity
end PrimeNumberTheorem
