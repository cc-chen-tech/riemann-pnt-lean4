import PrimeNumberTheorem.CarlsonGaussianPoleFreeLpAnalytic
import PrimeNumberTheorem.CarlsonGaussianPoleFreeLpValue

/-!
# Hadamard prerequisites for the concrete Carlson Gaussian map

This file proves the structural facts needed before applying the Banach-valued
three-lines theorem.  Imaginary translation of the strip parameter only
translates the height variable, so the `L²` norm depends on the real part.
Consequently boundedness on an unbounded vertical strip reduces to boundedness
of a continuous function on a compact real interval.
-/

open Complex Set MeasureTheory Function
open scoped ENNReal MeasureTheory

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- Moving the imaginary part of the strip parameter into the height variable
does not change the pointwise Carlson Gaussian section. -/
theorem carlsonGaussianHilbertSection_eq_real_shift
    (Delta w : ℝ) (H : ℂ → ℂ) (z : ℂ) (t : ℝ) :
    carlsonGaussianHilbertSection Delta w H z t =
      carlsonGaussianHilbertSection Delta w H (z.re : ℂ) (z.im + t) := by
  have hpoint :
      z + I * (t : ℂ) = (z.re : ℂ) + I * ((z.im + t : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  unfold carlsonGaussianHilbertSection
  rw [hpoint]

/-- On the controlled strip the totalized `Lp` value is the original
Gaussian section packaged in `L²`. -/
theorem carlsonGaussianPoleFreeLpValueTotal_eq
    {Delta w : ℝ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    {z : ℂ} (hzre : z.re ∈ Icc (1 / 2 : ℝ) 4) :
    carlsonGaussianPoleFreeLpValueTotal Delta w Y0 Y1
        hDelta hY0 hY01 z =
      carlsonGaussianPoleFreeLpValue Delta w Y0 Y1
        hDelta hY0 hY01 z hzre := by
  unfold carlsonGaussianPoleFreeLpValueTotal
  unfold carlsonGaussianPoleFreeLpValue
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall fun t => by
    rw [carlsonGaussianPoleFreeSectionTotal, if_pos hzre]

/-- Before totalization, the squared `L²` norm of the Gaussian section only
depends on the real part of the strip parameter. -/
theorem norm_sq_carlsonGaussianPoleFreeLpValue_eq_real_part
    {Delta w : ℝ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    {z : ℂ} (hzre : z.re ∈ Icc (1 / 2 : ℝ) 4) :
    ‖carlsonGaussianPoleFreeLpValue Delta w Y0 Y1
        hDelta hY0 hY01 z hzre‖ ^ 2 =
      ‖carlsonGaussianPoleFreeLpValue Delta w Y0 Y1
        hDelta hY0 hY01 (z.re : ℂ) (by simpa using hzre)‖ ^ 2 := by
  rw [norm_sq_carlsonGaussianPoleFreeLpValue hDelta hY0 hY01 hzre]
  rw [norm_sq_carlsonGaussianPoleFreeLpValue hDelta hY0 hY01
    (by simpa using hzre : ((z.re : ℝ) : ℂ).re ∈ Icc (1 / 2 : ℝ) 4)]
  calc
    (∫ t : ℝ,
        ‖carlsonGaussianHilbertSection Delta w
          (poleFreeTwoScaleMollifiedZetaError Y0 Y1) z t‖ ^ 2) =
        ∫ t : ℝ,
          ‖carlsonGaussianHilbertSection Delta w
            (poleFreeTwoScaleMollifiedZetaError Y0 Y1)
              (z.re : ℂ) (z.im + t)‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards with t
      rw [carlsonGaussianHilbertSection_eq_real_shift]
    _ = ∫ t : ℝ,
          ‖carlsonGaussianHilbertSection Delta w
            (poleFreeTwoScaleMollifiedZetaError Y0 Y1)
              (z.re : ℂ) t‖ ^ 2 := by
      simpa [add_comm] using
        integral_add_right_eq_self
          (fun t : ℝ =>
            ‖carlsonGaussianHilbertSection Delta w
              (poleFreeTwoScaleMollifiedZetaError Y0 Y1)
                (z.re : ℂ) t‖ ^ 2) z.im

/-- Imaginary translation is an exact isometry for the totalized Carlson
Gaussian `L²` map throughout its controlled strip. -/
theorem norm_carlsonGaussianPoleFreeLpValueTotal_eq_real_part
    {Delta w : ℝ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    {z : ℂ} (hzre : z.re ∈ Icc (1 / 2 : ℝ) 4) :
    ‖carlsonGaussianPoleFreeLpValueTotal Delta w Y0 Y1
        hDelta hY0 hY01 z‖ =
      ‖carlsonGaussianPoleFreeLpValueTotal Delta w Y0 Y1
        hDelta hY0 hY01 (z.re : ℂ)‖ := by
  rw [carlsonGaussianPoleFreeLpValueTotal_eq hDelta hY0 hY01 hzre]
  rw [carlsonGaussianPoleFreeLpValueTotal_eq hDelta hY0 hY01
    (by simpa using hzre : ((z.re : ℝ) : ℂ).re ∈ Icc (1 / 2 : ℝ) 4)]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact norm_sq_carlsonGaussianPoleFreeLpValue_eq_real_part
    hDelta hY0 hY01 hzre

/-- On every strip whose closed edges stay strictly inside `1/2 < Re z < 4`,
the concrete `L²` map is differentiable on the open strip and continuous on
its closure.  Keeping the Hadamard edges interior avoids any appeal to the
zero extension at its discontinuity candidates. -/
theorem diffContOnCl_carlsonGaussianPoleFreeLpValueTotal_on_inner_strip
    {Delta w l u : ℝ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    (hl : 1 / 2 < l) (hu : u < 4) (hlu : l < u) :
    DiffContOnCl ℂ
      (carlsonGaussianPoleFreeLpValueTotal Delta w Y0 Y1
        hDelta hY0 hY01)
      (HadamardThreeLines.verticalStrip l u) := by
  have hdiff : DifferentiableOn ℂ
      (carlsonGaussianPoleFreeLpValueTotal Delta w Y0 Y1
        hDelta hY0 hY01)
      (HadamardThreeLines.verticalClosedStrip l u) := by
    intro z hz
    change z.re ∈ Icc l u at hz
    exact
      (hasDerivAt_carlsonGaussianPoleFreeLpValueTotal_on_open_strip
        hDelta hY0 hY01 (hl.trans_le hz.1) (hz.2.trans_lt hu)).differentiableAt
        |>.differentiableWithinAt
  apply DifferentiableOn.diffContOnCl
  have hclosure :
      closure (HadamardThreeLines.verticalStrip l u) =
      HadamardThreeLines.verticalClosedStrip l u := by
    rw [HadamardThreeLines.verticalStrip,
      HadamardThreeLines.verticalClosedStrip, closure_preimage_re,
      closure_Ioo hlu.ne]
  rwa [hclosure]

/-- Although a vertical strip is unbounded, the norm image of the concrete
Gaussian map is bounded there: imaginary translation is an isometry, and the
remaining real parameter ranges over a compact interval. -/
theorem bddAbove_norm_carlsonGaussianPoleFreeLpValueTotal_on_inner_closed_strip
    {Delta w l u : ℝ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    (hl : 1 / 2 < l) (hu : u < 4) :
    BddAbove
      ((norm ∘ carlsonGaussianPoleFreeLpValueTotal Delta w Y0 Y1
        hDelta hY0 hY01) ''
          HadamardThreeLines.verticalClosedStrip l u) := by
  let F : ℂ → Lp ℂ 2 (volume : Measure ℝ) :=
    carlsonGaussianPoleFreeLpValueTotal Delta w Y0 Y1
      hDelta hY0 hY01
  have hcont : ContinuousOn (fun x : ℝ => ‖F (x : ℂ)‖) (Icc l u) := by
    intro x hx
    have hderiv : HasDerivAt F
        ((memLp_carlsonGaussianHilbertSectionDeriv_poleFree_on_open_strip
          hDelta hY0 hY01 (hl.trans_le hx.1) (hx.2.trans_lt hu)).toLp
          (carlsonGaussianHilbertSectionDeriv Delta w
            (poleFreeTwoScaleMollifiedZetaError Y0 Y1) (x : ℂ))) (x : ℂ) :=
      hasDerivAt_carlsonGaussianPoleFreeLpValueTotal_on_open_strip
        hDelta hY0 hY01 (hl.trans_le hx.1) (hx.2.trans_lt hu)
    have hofReal : ContinuousAt (fun y : ℝ => (y : ℂ)) x := by fun_prop
    exact hderiv.continuousAt.norm.comp hofReal |>.continuousWithinAt
  rcases isCompact_Icc.bddAbove_image hcont with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  change z.re ∈ Icc l u at hz
  change ‖F z‖ ≤ C
  rw [norm_carlsonGaussianPoleFreeLpValueTotal_eq_real_part
    hDelta hY0 hY01 (by constructor <;> linarith [hz.1, hz.2])]
  exact hC (mem_image_of_mem (fun x : ℝ => ‖F (x : ℂ)‖) hz)

/-- Concrete squared-norm Hadamard interpolation on any interior Carlson
strip.  The hypotheses `A` and `B` are exactly the two endpoint second-moment
bounds; no square-root loss is introduced when passing through the `L²` norm. -/
theorem norm_sq_carlsonGaussianPoleFreeLpValueTotal_le_interp_on_inner_strip
    {Delta w l u x A B : ℝ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    (hl : 1 / 2 < l) (hu : u < 4) (hlu : l < u)
    (hx : x ∈ Icc l u) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : ‖carlsonGaussianPoleFreeLpValueTotal Delta w Y0 Y1
        hDelta hY0 hY01 (l : ℂ)‖ ^ 2 ≤ A)
    (hB : ‖carlsonGaussianPoleFreeLpValueTotal Delta w Y0 Y1
        hDelta hY0 hY01 (u : ℂ)‖ ^ 2 ≤ B) :
    ‖carlsonGaussianPoleFreeLpValueTotal Delta w Y0 Y1
        hDelta hY0 hY01 (x : ℂ)‖ ^ 2 ≤
      A ^ (1 - (x - l) / (u - l)) * B ^ ((x - l) / (u - l)) := by
  let F : ℂ → Lp ℂ 2 (volume : Measure ℝ) :=
    carlsonGaussianPoleFreeLpValueTotal Delta w Y0 Y1
      hDelta hY0 hY01
  have hleft : ∀ z ∈ re ⁻¹' {l}, ‖F z‖ ≤ Real.sqrt A := by
    intro z hz
    change z.re ∈ ({l} : Set ℝ) at hz
    simp only [mem_singleton_iff] at hz
    have hzControlled : z.re ∈ Icc (1 / 2 : ℝ) 4 := by
      constructor <;> linarith
    rw [norm_carlsonGaussianPoleFreeLpValueTotal_eq_real_part
      hDelta hY0 hY01 hzControlled, hz]
    exact Real.le_sqrt_of_sq_le hA
  have hright : ∀ z ∈ re ⁻¹' {u}, ‖F z‖ ≤ Real.sqrt B := by
    intro z hz
    change z.re ∈ ({u} : Set ℝ) at hz
    simp only [mem_singleton_iff] at hz
    have hzControlled : z.re ∈ Icc (1 / 2 : ℝ) 4 := by
      constructor <;> linarith
    rw [norm_carlsonGaussianPoleFreeLpValueTotal_eq_real_part
      hDelta hY0 hY01 hzControlled, hz]
    exact Real.le_sqrt_of_sq_le hB
  have hinterp := MathlibAux.norm_sq_le_interp_of_mem_verticalClosedStrip'
    (f := F) (z := (x : ℂ)) (a := Real.sqrt A) (b := Real.sqrt B)
    hlu (by simpa [HadamardThreeLines.verticalClosedStrip] using hx)
    (diffContOnCl_carlsonGaussianPoleFreeLpValueTotal_on_inner_strip
      hDelta hY0 hY01 hl hu hlu)
    (bddAbove_norm_carlsonGaussianPoleFreeLpValueTotal_on_inner_closed_strip
      hDelta hY0 hY01 hl hu)
    (Real.sqrt_nonneg A) (Real.sqrt_nonneg B) hleft hright
  simpa [F, Real.sq_sqrt hA0, Real.sq_sqrt hB0] using hinterp

end CarlsonZeroDensity
end PrimeNumberTheorem
