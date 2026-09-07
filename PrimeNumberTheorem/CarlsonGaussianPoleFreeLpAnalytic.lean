import PrimeNumberTheorem.CarlsonGaussianPoleFreeTotalSection
import MathlibAux.LpPointwiseDerivBridge

/-!
# Local `L²` analyticity of the concrete Carlson Gaussian map

The neighborhood-uniform derivative majorant is combined here with the
pointwise mean-value estimate and dominated convergence.  The result is an
actual `Lp ℂ 2 volume` derivative theorem on the central strip needed for the
shifted Carlson contour.
-/

open Complex Set MeasureTheory Filter
open scoped ENNReal MeasureTheory

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- A positive local radius at every point of the open Carlson strip.  The
factor four leaves room both for the derivative Cauchy circle and for the
subsequent slope ball. -/
noncomputable def carlsonGaussianOpenStripRadius (z : ℂ) : ℝ :=
  min (1 / 48 : ℝ)
    (min ((z.re - 1 / 2) / 4) ((4 - z.re) / 4))

theorem carlsonGaussianOpenStripRadius_pos {z : ℂ}
    (hzleft : 1 / 2 < z.re) (hzright : z.re < 4) :
    0 < carlsonGaussianOpenStripRadius z := by
  unfold carlsonGaussianOpenStripRadius
  exact lt_min (by norm_num) (lt_min (by linarith) (by linarith))

theorem carlsonGaussianOpenStripRadius_le_one_div_forty_eight (z : ℂ) :
    carlsonGaussianOpenStripRadius z ≤ (1 / 48 : ℝ) := by
  exact min_le_left _ _

theorem carlsonGaussianOpenStripRadius_left {z : ℂ}
    (hzleft : 1 / 2 < z.re) :
    1 / 2 + 2 * carlsonGaussianOpenStripRadius z ≤ z.re := by
  have hle : carlsonGaussianOpenStripRadius z ≤ (z.re - 1 / 2) / 4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  linarith

theorem carlsonGaussianOpenStripRadius_right {z : ℂ}
    (hzright : z.re < 4) :
    z.re + 2 * carlsonGaussianOpenStripRadius z ≤ 4 := by
  have hle : carlsonGaussianOpenStripRadius z ≤ (4 - z.re) / 4 :=
    (min_le_right _ _).trans (min_le_right _ _)
  linarith

/-- The exact concrete Gaussian derivative section is continuous in the
height variable at every point of the open strip. -/
theorem continuous_carlsonGaussianHilbertSectionDeriv_poleFree_on_open_strip
    {Delta w : ℝ} {Y0 Y1 : ℕ} {z : ℂ}
    (hzleft : 1 / 2 < z.re) :
    Continuous fun t : ℝ =>
      carlsonGaussianHilbertSectionDeriv Delta w
        (poleFreeTwoScaleMollifiedZetaError Y0 Y1) z t := by
  let point : ℝ → ℂ := fun t => z + I * (t : ℂ)
  have hpoint : Continuous point := by
    dsimp [point]
    fun_prop
  have hH : Continuous fun t : ℝ =>
      poleFreeTwoScaleMollifiedZetaError Y0 Y1 (point t) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hre : 0 < (point t).re := by
      dsimp [point]
      simp only [mul_re, I_re, ofReal_re, I_im, ofReal_im,
        zero_mul, one_mul, sub_self, add_zero]
      linarith
    have ha := analyticOnNhd_poleFreeTwoScaleMollifiedZetaError_re_gt
      (theta := 0) le_rfl Y0 Y1 (point t) hre
    exact ha.continuousAt.comp hpoint.continuousAt
  have hH' : Continuous fun t : ℝ =>
      deriv (poleFreeTwoScaleMollifiedZetaError Y0 Y1) (point t) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hre : 0 < (point t).re := by
      dsimp [point]
      simp only [mul_re, I_re, ofReal_re, I_im, ofReal_im,
        zero_mul, one_mul, sub_self, add_zero]
      linarith
    have ha := analyticOnNhd_poleFreeTwoScaleMollifiedZetaError_re_gt
      (theta := 0) le_rfl Y0 Y1 (point t) hre
    exact ha.deriv.continuousAt.comp hpoint.continuousAt
  let qfun : ℝ → ℂ := fun t => point t - I * (w : ℂ)
  have hq : Continuous qfun := by
    dsimp [qfun]
    fun_prop
  have hgauss : Continuous fun t =>
      Complex.exp (qfun t ^ 2 / (2 * (Delta : ℂ) ^ 2)) := by
    fun_prop
  have hlinear : Continuous fun t =>
      qfun t / (Delta : ℂ) ^ 2 *
        poleFreeTwoScaleMollifiedZetaError Y0 Y1 (point t) := by
    exact (hq.div_const _).mul hH
  change Continuous fun t : ℝ =>
    Complex.exp (qfun t ^ 2 / (2 * (Delta : ℂ) ^ 2)) *
      (qfun t / (Delta : ℂ) ^ 2 *
          poleFreeTwoScaleMollifiedZetaError Y0 Y1 (point t) +
        deriv (poleFreeTwoScaleMollifiedZetaError Y0 Y1) (point t))
  exact hgauss.mul (hlinear.add hH')

/-- The exact derivative section belongs to `L²(ℝ)` at every point of the
full open Carlson strip. -/
theorem memLp_carlsonGaussianHilbertSectionDeriv_poleFree_on_open_strip
    {Delta w : ℝ} {z : ℂ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    (hzleft : 1 / 2 < z.re) (hzright : z.re < 4) :
    MemLp
      (carlsonGaussianHilbertSectionDeriv Delta w
        (poleFreeTwoScaleMollifiedZetaError Y0 Y1) z) 2 volume := by
  let rho := carlsonGaussianOpenStripRadius z
  have hrho : 0 < rho := carlsonGaussianOpenStripRadius_pos hzleft hzright
  have hrhoSmall : rho ≤ (1 / 48 : ℝ) :=
    carlsonGaussianOpenStripRadius_le_one_div_forty_eight z
  rcases
      exists_carlsonGaussianDerivativeMajorant_bound_on_closedBall_of_radius
        hDelta hY0 hY01 hrho hrhoSmall
          (carlsonGaussianOpenStripRadius_left hzleft)
          (carlsonGaussianOpenStripRadius_right hzright) with
    ⟨K, hK, hmajor⟩
  have hcont :=
    continuous_carlsonGaussianHilbertSectionDeriv_poleFree_on_open_strip
      (Delta := Delta) (w := w) (Y0 := Y0) (Y1 := Y1) hzleft
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  apply Integrable.mono_nonneg
    (integrable_carlsonGaussianDerivativeMajorant hDelta K)
  · exact hcont.norm.pow 2 |>.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun _ => sq_nonneg _
  · exact Filter.Eventually.of_forall fun t => by
      apply hmajor z
      exact Metric.mem_closedBall_self hrho.le

/-- The totalized Carlson section as an actual `L²(ℝ)` value. -/
noncomputable def carlsonGaussianPoleFreeLpValueTotal
    (Delta w : ℝ) (Y0 Y1 : ℕ)
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1) (z : ℂ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_carlsonGaussianPoleFreeSectionTotal hDelta hY0 hY01 z).toLp
    (carlsonGaussianPoleFreeSectionTotal Delta w Y0 Y1 z)

private theorem closedBall_re_mem_wide_inner_strip
    {z v : ℂ} (hzre : z.re ∈ Icc (29 / 48 : ℝ) (187 / 48))
    (hv : v ∈ Metric.closedBall z (1 / 48 : ℝ)) :
    v.re ∈ Icc (7 / 12 : ℝ) (47 / 12) := by
  have hdist : dist v z ≤ (1 / 48 : ℝ) := Metric.mem_closedBall.mp hv
  have hreDiff : |v.re - z.re| ≤ (1 / 48 : ℝ) := by
    calc
      |v.re - z.re| = |(v - z).re| := by simp
      _ ≤ ‖v - z‖ := Complex.abs_re_le_norm (v - z)
      _ = dist v z := by rw [dist_eq_norm]
      _ ≤ 1 / 48 := hdist
  rw [abs_le] at hreDiff
  constructor <;> linarith [hzre.1, hzre.2]

set_option maxHeartbeats 600000 in
/-- The totalized concrete Carlson Gaussian map is complex differentiable on
the central strip, with derivative represented by the exact pointwise
Gaussian derivative section. -/
theorem hasDerivAt_carlsonGaussianPoleFreeLpValueTotal
    {Delta w : ℝ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    {z : ℂ} (hzre : z.re ∈ Icc (29 / 48 : ℝ) (187 / 48)) :
    HasDerivAt
      (carlsonGaussianPoleFreeLpValueTotal Delta w Y0 Y1 hDelta hY0 hY01)
      ((memLp_carlsonGaussianHilbertSectionDeriv_poleFree_on_wide_inner_strip
        hDelta hY0 hY01 (by constructor <;> linarith [hzre.1, hzre.2])).toLp
        (carlsonGaussianHilbertSectionDeriv Delta w
          (poleFreeTwoScaleMollifiedZetaError Y0 Y1) z)) z := by
  let f : ℂ → ℝ → ℂ := fun u =>
    carlsonGaussianPoleFreeSectionTotal Delta w Y0 Y1 u
  let f' : ℝ → ℂ :=
    carlsonGaussianHilbertSectionDeriv Delta w
      (poleFreeTwoScaleMollifiedZetaError Y0 Y1) z
  let hf : ∀ u, MemLp (f u) 2 volume := fun u =>
    memLp_carlsonGaussianPoleFreeSectionTotal hDelta hY0 hY01 u
  have hzWide : z.re ∈ Icc (7 / 12 : ℝ) (47 / 12) := by
    constructor <;> linarith [hzre.1, hzre.2]
  have hf' : MemLp f' 2 volume :=
    memLp_carlsonGaussianHilbertSectionDeriv_poleFree_on_wide_inner_strip
      hDelta hY0 hY01 hzWide
  rcases
      exists_carlsonGaussianDerivativeMajorant_bound_on_closedBall
        hDelta hY0 hY01 hzre with ⟨K, hK, hmajor⟩
  let B : ℝ → ℝ :=
    carlsonGaussianDerivativeMajorant Delta w z.im K
  have hBnonneg : ∀ t, 0 ≤ B t := by
    intro t
    dsimp [B, carlsonGaussianDerivativeMajorant]
    positivity
  have hBint : Integrable (fun t => 4 * B t) volume := by
    exact (integrable_carlsonGaussianDerivativeMajorant hDelta K).const_mul 4
  have hpointDeriv : ∀ v ∈ Metric.closedBall z (1 / 48 : ℝ), ∀ t,
      HasDerivAt (fun u => f u t)
        (carlsonGaussianHilbertSectionDeriv Delta w
          (poleFreeTwoScaleMollifiedZetaError Y0 Y1) v t) v := by
    intro v hv t
    exact
      hasDerivAt_carlsonGaussianPoleFreeSectionTotal_on_wide_inner_strip
        hDelta hY0 hY01 (closedBall_re_mem_wide_inner_strip hzre hv) t
  have hpointSq : ∀ v ∈ Metric.closedBall z (1 / 48 : ℝ), ∀ t,
      ‖carlsonGaussianHilbertSectionDeriv Delta w
          (poleFreeTwoScaleMollifiedZetaError Y0 Y1) v t‖ ^ 2 ≤ B t := by
    intro v hv t
    exact hmajor v hv t
  have hslopeBound :=
    pointwiseSlope_error_sq_le_four_mul_of_deriv_sq_le
      f (fun v => carlsonGaussianHilbertSectionDeriv Delta w
        (poleFreeTwoScaleMollifiedZetaError Y0 Y1) v)
      (z := z) (r := (1 / 48 : ℝ)) (B := B) (by norm_num)
      hpointDeriv hBnonneg hpointSq
  have hslopeMem (u : ℂ) : MemLp (pointwiseComplexSlope f z u) 2 volume := by
    change MemLp ((u - z)⁻¹ • (f u - f z)) 2 volume
    exact ((hf u).sub (hf z)).const_smul ((u - z)⁻¹)
  have hMeas : ∀ᶠ u in nhdsWithin z {z}ᶜ,
      AEStronglyMeasurable
        (fun t => ‖pointwiseComplexSlope f z u t - f' t‖ ^ 2) volume :=
    Filter.Eventually.of_forall fun u =>
      ((hslopeMem u).sub hf').aestronglyMeasurable.norm.pow 2
  have hzBall : z ∈ Metric.closedBall z (1 / 48 : ℝ) :=
    Metric.mem_closedBall_self (by norm_num)
  have hballNhd : ∀ᶠ u in nhds z,
      u ∈ Metric.closedBall z (1 / 48 : ℝ) :=
    mem_of_superset
      (Metric.ball_mem_nhds z (by norm_num : (0 : ℝ) < 1 / 48))
      Metric.ball_subset_closedBall
  have hballPunctured : ∀ᶠ u in nhdsWithin z {z}ᶜ,
      u ∈ Metric.closedBall z (1 / 48 : ℝ) :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hballNhd
  have hBound : ∀ᶠ u in nhdsWithin z {z}ᶜ, ∀ᵐ t ∂volume,
      ‖(‖pointwiseComplexSlope f z u t - f' t‖ ^ 2 : ℝ)‖ ≤ 4 * B t := by
    filter_upwards [hballPunctured] with u hu
    exact Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      by_cases huz : u = z
      · subst u
        simp only [pointwiseComplexSlope, sub_self, inv_zero, sub_self,
          mul_zero, zero_sub, norm_neg]
        have hcenter := hpointSq z hzBall t
        nlinarith [hBnonneg t]
      · exact hslopeBound u hu huz t
  have hDerivAE : ∀ᵐ t ∂volume,
      HasDerivAt (fun u => f u t) (f' t) z :=
    Filter.Eventually.of_forall fun t => hpointDeriv z hzBall t
  have hlim := tendsto_integral_pointwiseSlope_sq_of_dominated
    f hMeas hBound hBint hDerivAE
  have hresult :=
    hasDerivAt_memLpToLp_of_tendsto_integral_pointwiseSlope_sq
      f hf hf' hlim
  change HasDerivAt (fun u => (hf u).toLp (f u)) (hf'.toLp f') z
  exact hresult

private theorem closedBall_re_mem_open_strip
    {z v : ℂ} {rho : ℝ} (hrho : 0 < rho)
    (hleft : 1 / 2 + 2 * rho ≤ z.re)
    (hright : z.re + 2 * rho ≤ 4)
    (hv : v ∈ Metric.closedBall z rho) :
    1 / 2 < v.re ∧ v.re < 4 := by
  have hdist : dist v z ≤ rho := Metric.mem_closedBall.mp hv
  have hreDiff : |v.re - z.re| ≤ rho := by
    calc
      |v.re - z.re| = |(v - z).re| := by simp
      _ ≤ ‖v - z‖ := Complex.abs_re_le_norm (v - z)
      _ = dist v z := by rw [dist_eq_norm]
      _ ≤ rho := hdist
  rw [abs_le] at hreDiff
  constructor <;> linarith

set_option maxHeartbeats 600000 in
/-- Full open-strip `L²` analyticity of the concrete Carlson Gaussian map. -/
theorem hasDerivAt_carlsonGaussianPoleFreeLpValueTotal_on_open_strip
    {Delta w : ℝ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    {z : ℂ} (hzleft : 1 / 2 < z.re) (hzright : z.re < 4) :
    HasDerivAt
      (carlsonGaussianPoleFreeLpValueTotal Delta w Y0 Y1 hDelta hY0 hY01)
      ((memLp_carlsonGaussianHilbertSectionDeriv_poleFree_on_open_strip
        hDelta hY0 hY01 hzleft hzright).toLp
        (carlsonGaussianHilbertSectionDeriv Delta w
          (poleFreeTwoScaleMollifiedZetaError Y0 Y1) z)) z := by
  let rho := carlsonGaussianOpenStripRadius z
  have hrho : 0 < rho := carlsonGaussianOpenStripRadius_pos hzleft hzright
  have hrhoSmall : rho ≤ (1 / 48 : ℝ) :=
    carlsonGaussianOpenStripRadius_le_one_div_forty_eight z
  have hleft := carlsonGaussianOpenStripRadius_left hzleft
  have hright := carlsonGaussianOpenStripRadius_right hzright
  let f : ℂ → ℝ → ℂ := fun u =>
    carlsonGaussianPoleFreeSectionTotal Delta w Y0 Y1 u
  let f' : ℝ → ℂ :=
    carlsonGaussianHilbertSectionDeriv Delta w
      (poleFreeTwoScaleMollifiedZetaError Y0 Y1) z
  let hf : ∀ u, MemLp (f u) 2 volume := fun u =>
    memLp_carlsonGaussianPoleFreeSectionTotal hDelta hY0 hY01 u
  have hf' : MemLp f' 2 volume :=
    memLp_carlsonGaussianHilbertSectionDeriv_poleFree_on_open_strip
      hDelta hY0 hY01 hzleft hzright
  rcases
      exists_carlsonGaussianDerivativeMajorant_bound_on_closedBall_of_radius
        hDelta hY0 hY01 hrho hrhoSmall hleft hright with ⟨K, hK, hmajor⟩
  let B : ℝ → ℝ :=
    carlsonGaussianDerivativeMajorant Delta w z.im K
  have hBnonneg : ∀ t, 0 ≤ B t := by
    intro t
    dsimp [B, carlsonGaussianDerivativeMajorant]
    positivity
  have hBint : Integrable (fun t => 4 * B t) volume :=
    (integrable_carlsonGaussianDerivativeMajorant hDelta K).const_mul 4
  have hpointDeriv : ∀ v ∈ Metric.closedBall z rho, ∀ t,
      HasDerivAt (fun u => f u t)
        (carlsonGaussianHilbertSectionDeriv Delta w
          (poleFreeTwoScaleMollifiedZetaError Y0 Y1) v t) v := by
    intro v hv t
    have hvstrip := closedBall_re_mem_open_strip hrho hleft hright hv
    exact hasDerivAt_carlsonGaussianPoleFreeSectionTotal_on_open_strip
      hDelta hY0 hY01 hvstrip.1 hvstrip.2 t
  have hpointSq : ∀ v ∈ Metric.closedBall z rho, ∀ t,
      ‖carlsonGaussianHilbertSectionDeriv Delta w
          (poleFreeTwoScaleMollifiedZetaError Y0 Y1) v t‖ ^ 2 ≤ B t := by
    intro v hv t
    exact hmajor v hv t
  have hslopeBound :=
    pointwiseSlope_error_sq_le_four_mul_of_deriv_sq_le
      f (fun v => carlsonGaussianHilbertSectionDeriv Delta w
        (poleFreeTwoScaleMollifiedZetaError Y0 Y1) v)
      (z := z) (r := rho) (B := B) hrho.le
      hpointDeriv hBnonneg hpointSq
  have hslopeMem (u : ℂ) : MemLp (pointwiseComplexSlope f z u) 2 volume := by
    change MemLp ((u - z)⁻¹ • (f u - f z)) 2 volume
    exact ((hf u).sub (hf z)).const_smul ((u - z)⁻¹)
  have hMeas : ∀ᶠ u in nhdsWithin z {z}ᶜ,
      AEStronglyMeasurable
        (fun t => ‖pointwiseComplexSlope f z u t - f' t‖ ^ 2) volume :=
    Filter.Eventually.of_forall fun u =>
      ((hslopeMem u).sub hf').aestronglyMeasurable.norm.pow 2
  have hzBall : z ∈ Metric.closedBall z rho :=
    Metric.mem_closedBall_self hrho.le
  have hballNhd : ∀ᶠ u in nhds z, u ∈ Metric.closedBall z rho :=
    mem_of_superset (Metric.ball_mem_nhds z hrho) Metric.ball_subset_closedBall
  have hballPunctured : ∀ᶠ u in nhdsWithin z {z}ᶜ,
      u ∈ Metric.closedBall z rho :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hballNhd
  have hBound : ∀ᶠ u in nhdsWithin z {z}ᶜ, ∀ᵐ t ∂volume,
      ‖(‖pointwiseComplexSlope f z u t - f' t‖ ^ 2 : ℝ)‖ ≤ 4 * B t := by
    filter_upwards [hballPunctured] with u hu
    exact Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      by_cases huz : u = z
      · subst u
        simp only [pointwiseComplexSlope, sub_self, inv_zero, mul_zero,
          zero_sub, norm_neg]
        have hcenter := hpointSq z hzBall t
        nlinarith [hBnonneg t]
      · exact hslopeBound u hu huz t
  have hDerivAE : ∀ᵐ t ∂volume,
      HasDerivAt (fun u => f u t) (f' t) z :=
    Filter.Eventually.of_forall fun t => hpointDeriv z hzBall t
  have hlim := tendsto_integral_pointwiseSlope_sq_of_dominated
    f hMeas hBound hBint hDerivAE
  have hresult :=
    hasDerivAt_memLpToLp_of_tendsto_integral_pointwiseSlope_sq
      f hf hf' hlim
  change HasDerivAt (fun u => (hf u).toLp (f u)) (hf'.toLp f') z
  exact hresult

end CarlsonZeroDensity
end PrimeNumberTheorem
