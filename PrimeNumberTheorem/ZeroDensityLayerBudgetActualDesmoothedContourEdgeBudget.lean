import PrimeNumberTheorem.ZeroDensityLayerBudgetNormalizedDesmoothedExplicitFormula

open Complex MeasureTheory Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

/-- The natural radius bound for either horizontal edge of the cubic contour. -/
noncomputable def cubicHorizontalEdgeRadius (c W : ℝ) : ℝ :=
  c + 2 * Real.pi * W

/-- The natural radius bound for the left edge of the cubic contour. -/
noncomputable def cubicLeftEdgeRadius (a W : ℝ) : ℝ :=
  a + 2 * Real.pi * W

/-- Pointwise budget after separating the logarithmic derivative, Mellin
weight, denominator, and cubic de-smoothing multiplier. -/
noncomputable def desmoothedCubicPointwiseBudget
    (x h c nu L R : ℝ) : ℝ :=
  L * (x ^ c / nu) * (1 + 3 * (h * R))

/-- The actual de-smoothed zeta integrand has an exact four-factor norm
decomposition.  This is the point where the contour analysis is reduced to a
logarithmic-derivative estimate and elementary geometry. -/
theorem norm_desmoothedCubicContourIntegrand_eq
    {x h : ℝ} {s : ℂ} (hx : 0 < x) :
    ‖desmoothedCubicContourIntegrand x h s‖ =
      ‖logDeriv riemannZeta s‖ * (x ^ s.re / ‖s‖) *
        ‖cubicKernelMultiplier s h‖ := by
  rw [desmoothedCubicContourIntegrand, norm_mul,
    explicitFormulaIntegrand, norm_div, norm_mul, norm_neg,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  ring

/-- A reusable pointwise estimate for the actual de-smoothed zeta integrand.
No global logarithmic-derivative hypothesis is hidden: `hlog` is exactly the
local analytic input that later zero-free or zero-distance estimates must
supply. -/
theorem norm_desmoothedCubicContourIntegrand_le
    {x h c nu L R : ℝ} {s : ℂ}
    (hx : 0 < x) (hx1 : 1 ≤ x) (hnu : 0 < nu)
    (hsigma : s.re ≤ c) (hden : nu ≤ ‖s‖) (hradius : ‖s‖ ≤ R)
    (hL : 0 ≤ L) (hlog : ‖logDeriv riemannZeta s‖ ≤ L)
    (hh : 0 < h) (hs : s ≠ 0) (hsmall : h * R ≤ 1) :
    ‖desmoothedCubicContourIntegrand x h s‖ ≤
      desmoothedCubicPointwiseBudget x h c nu L R := by
  have hpow : x ^ s.re ≤ x ^ c :=
    Real.rpow_le_rpow_of_exponent_le hx1 hsigma
  have hquot : x ^ s.re / ‖s‖ ≤ x ^ c / nu :=
    div_le_div₀ (Real.rpow_nonneg hx.le c) hpow hnu hden
  have hsmall' : h * ‖s‖ ≤ 1 :=
    (mul_le_mul_of_nonneg_left hradius hh.le).trans hsmall
  have hnear := norm_cubicKernelMultiplier_sub_one_le_three_mul hh hs hsmall'
  have hmult0 : ‖cubicKernelMultiplier s h‖ ≤ 1 + 3 * (h * ‖s‖) :=
    (norm_multiplier_bounds_of_sub_one_le hnear).2
  have hmult : ‖cubicKernelMultiplier s h‖ ≤ 1 + 3 * (h * R) := by
    apply hmult0.trans
    gcongr
  rw [norm_desmoothedCubicContourIntegrand_eq hx]
  unfold desmoothedCubicPointwiseBudget
  gcongr

theorem two_pi_mul_pos {W : ℝ} (hW : 0 < W) :
    0 < 2 * Real.pi * W := by positivity

theorem two_pi_mul_le_norm_cubicBottomContourPoint
    {W sigma : ℝ} (hW : 0 < W) :
    2 * Real.pi * W ≤ ‖cubicBottomContourPoint W sigma‖ := by
  have hT := two_pi_mul_pos hW
  calc
    2 * Real.pi * W = |(cubicBottomContourPoint W sigma).im| := by
      simp [cubicBottomContourPoint, abs_of_pos hT]
    _ ≤ ‖cubicBottomContourPoint W sigma‖ := Complex.abs_im_le_norm _

theorem two_pi_mul_le_norm_cubicTopContourPoint
    {W sigma : ℝ} (hW : 0 < W) :
    2 * Real.pi * W ≤ ‖cubicTopContourPoint W sigma‖ := by
  have hT := two_pi_mul_pos hW
  calc
    2 * Real.pi * W = |(cubicTopContourPoint W sigma).im| := by
      simp [cubicTopContourPoint, abs_of_pos hT]
    _ ≤ ‖cubicTopContourPoint W sigma‖ := Complex.abs_im_le_norm _

theorem norm_cubicBottomContourPoint_le_radius
    {a c W sigma : ℝ} (ha : 0 < a) (hac : a ≤ c) (hW : 0 < W)
    (hsigma : sigma ∈ Ι a c) :
    ‖cubicBottomContourPoint W sigma‖ ≤ cubicHorizontalEdgeRadius c W := by
  have hsigma' : a < sigma ∧ sigma ≤ c := by
    simpa [Set.uIoc_of_le hac] using hsigma
  have hsigma0 : 0 ≤ sigma := (ha.trans hsigma'.1).le
  calc
    ‖cubicBottomContourPoint W sigma‖ ≤
        |(cubicBottomContourPoint W sigma).re| +
          |(cubicBottomContourPoint W sigma).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = sigma + 2 * Real.pi * W := by
      simp [cubicBottomContourPoint, abs_of_nonneg hsigma0,
        abs_of_pos Real.pi_pos, abs_of_pos hW]
    _ ≤ cubicHorizontalEdgeRadius c W := by
      unfold cubicHorizontalEdgeRadius
      linarith

theorem norm_cubicTopContourPoint_le_radius
    {a c W sigma : ℝ} (ha : 0 < a) (hac : a ≤ c) (hW : 0 < W)
    (hsigma : sigma ∈ Ι a c) :
    ‖cubicTopContourPoint W sigma‖ ≤ cubicHorizontalEdgeRadius c W := by
  have hsigma' : a < sigma ∧ sigma ≤ c := by
    simpa [Set.uIoc_of_le hac] using hsigma
  have hsigma0 : 0 ≤ sigma := (ha.trans hsigma'.1).le
  calc
    ‖cubicTopContourPoint W sigma‖ ≤
        |(cubicTopContourPoint W sigma).re| +
          |(cubicTopContourPoint W sigma).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = sigma + 2 * Real.pi * W := by
      simp [cubicTopContourPoint, abs_of_nonneg hsigma0,
        abs_of_pos Real.pi_pos, abs_of_pos hW]
    _ ≤ cubicHorizontalEdgeRadius c W := by
      unfold cubicHorizontalEdgeRadius
      linarith

theorem a_le_norm_cubicLeftContourPoint
    {a t : ℝ} (ha : 0 < a) :
    a ≤ ‖cubicLeftContourPoint a t‖ := by
  calc
    a = |(cubicLeftContourPoint a t).re| := by
      simp [cubicLeftContourPoint, abs_of_pos ha]
    _ ≤ ‖cubicLeftContourPoint a t‖ := Complex.abs_re_le_norm _

theorem norm_cubicLeftContourPoint_le_radius
    {a W t : ℝ} (ha : 0 < a) (hW : 0 < W)
    (ht : t ∈ Ι (-(2 * Real.pi * W)) (2 * Real.pi * W)) :
    ‖cubicLeftContourPoint a t‖ ≤ cubicLeftEdgeRadius a W := by
  have hT := two_pi_mul_pos hW
  have hinterval : -(2 * Real.pi * W) < t ∧ t ≤ 2 * Real.pi * W := by
    have horder : -(2 * Real.pi * W) ≤ 2 * Real.pi * W := by linarith
    rw [Set.uIoc_of_le horder] at ht
    exact ht
  have habs : |t| ≤ 2 * Real.pi * W :=
    abs_le.mpr ⟨hinterval.1.le, hinterval.2⟩
  calc
    ‖cubicLeftContourPoint a t‖ ≤
        |(cubicLeftContourPoint a t).re| +
          |(cubicLeftContourPoint a t).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = a + |t| := by simp [cubicLeftContourPoint, abs_of_pos ha]
    _ ≤ cubicLeftEdgeRadius a W := by
      unfold cubicLeftEdgeRadius
      linarith

/-- Concrete bottom-edge pointwise budget. -/
theorem norm_desmoothedCubicBottomContourIntegrand_le
    {x h a c W L sigma : ℝ}
    (hx : 0 < x) (hx1 : 1 ≤ x) (ha : 0 < a) (hac : a ≤ c)
    (hW : 0 < W) (hL : 0 ≤ L)
    (hlog : ‖logDeriv riemannZeta (cubicBottomContourPoint W sigma)‖ ≤ L)
    (hh : 0 < h)
    (hsmall : h * cubicHorizontalEdgeRadius c W ≤ 1)
    (hsigma : sigma ∈ Ι a c) :
    ‖desmoothedCubicContourIntegrand x h
        (cubicBottomContourPoint W sigma)‖ ≤
      desmoothedCubicPointwiseBudget x h c (2 * Real.pi * W) L
        (cubicHorizontalEdgeRadius c W) := by
  apply norm_desmoothedCubicContourIntegrand_le hx hx1 (two_pi_mul_pos hW)
  · simpa [cubicBottomContourPoint] using (by
      have := (show sigma ∈ Ι a c from hsigma)
      have hsigma' : a < sigma ∧ sigma ≤ c := by
        simpa [Set.uIoc_of_le hac] using this
      exact hsigma'.2)
  · exact two_pi_mul_le_norm_cubicBottomContourPoint hW
  · exact norm_cubicBottomContourPoint_le_radius ha hac hW hsigma
  · exact hL
  · exact hlog
  · exact hh
  · intro hs
    have := two_pi_mul_le_norm_cubicBottomContourPoint (sigma := sigma) hW
    rw [hs, norm_zero] at this
    linarith [two_pi_mul_pos hW]
  · exact hsmall

/-- Concrete top-edge pointwise budget. -/
theorem norm_desmoothedCubicTopContourIntegrand_le
    {x h a c W L sigma : ℝ}
    (hx : 0 < x) (hx1 : 1 ≤ x) (ha : 0 < a) (hac : a ≤ c)
    (hW : 0 < W) (hL : 0 ≤ L)
    (hlog : ‖logDeriv riemannZeta (cubicTopContourPoint W sigma)‖ ≤ L)
    (hh : 0 < h)
    (hsmall : h * cubicHorizontalEdgeRadius c W ≤ 1)
    (hsigma : sigma ∈ Ι a c) :
    ‖desmoothedCubicContourIntegrand x h
        (cubicTopContourPoint W sigma)‖ ≤
      desmoothedCubicPointwiseBudget x h c (2 * Real.pi * W) L
        (cubicHorizontalEdgeRadius c W) := by
  apply norm_desmoothedCubicContourIntegrand_le hx hx1 (two_pi_mul_pos hW)
  · simpa [cubicTopContourPoint] using (by
      have hsigma' : a < sigma ∧ sigma ≤ c := by
        simpa [Set.uIoc_of_le hac] using hsigma
      exact hsigma'.2)
  · exact two_pi_mul_le_norm_cubicTopContourPoint hW
  · exact norm_cubicTopContourPoint_le_radius ha hac hW hsigma
  · exact hL
  · exact hlog
  · exact hh
  · intro hs
    have := two_pi_mul_le_norm_cubicTopContourPoint (sigma := sigma) hW
    rw [hs, norm_zero] at this
    linarith [two_pi_mul_pos hW]
  · exact hsmall

/-- Concrete left-edge pointwise budget. -/
theorem norm_desmoothedCubicLeftContourIntegrand_le
    {x h a W L t : ℝ}
    (hx : 0 < x) (hx1 : 1 ≤ x) (ha : 0 < a) (hW : 0 < W)
    (hL : 0 ≤ L)
    (hlog : ‖logDeriv riemannZeta (cubicLeftContourPoint a t)‖ ≤ L)
    (hh : 0 < h) (hsmall : h * cubicLeftEdgeRadius a W ≤ 1)
    (ht : t ∈ Ι (-(2 * Real.pi * W)) (2 * Real.pi * W)) :
    ‖desmoothedCubicContourIntegrand x h (cubicLeftContourPoint a t)‖ ≤
      desmoothedCubicPointwiseBudget x h a a L
        (cubicLeftEdgeRadius a W) := by
  apply norm_desmoothedCubicContourIntegrand_le hx hx1 ha
  · simp [cubicLeftContourPoint]
  · exact a_le_norm_cubicLeftContourPoint ha
  · exact norm_cubicLeftContourPoint_le_radius ha hW ht
  · exact hL
  · exact hlog
  · exact hh
  · intro hs
    have := a_le_norm_cubicLeftContourPoint (t := t) ha
    rw [hs, norm_zero] at this
    linarith
  · exact hsmall

/-- Bottom-edge integral budget with the actual edge length. -/
theorem norm_desmoothedCubicBottomContourIntegral_le
    {x h a c W L : ℝ}
    (hx : 0 < x) (hx1 : 1 ≤ x) (ha : 0 < a) (hac : a ≤ c)
    (hW : 0 < W) (hL : 0 ≤ L)
    (hlog : ∀ sigma ∈ Ι a c,
      ‖logDeriv riemannZeta (cubicBottomContourPoint W sigma)‖ ≤ L)
    (hh : 0 < h) (hsmall : h * cubicHorizontalEdgeRadius c W ≤ 1) :
    ‖desmoothedCubicBottomContourIntegral x h a c W‖ ≤
      desmoothedCubicPointwiseBudget x h c (2 * Real.pi * W) L
          (cubicHorizontalEdgeRadius c W) * |c - a| := by
  unfold desmoothedCubicBottomContourIntegral
  exact intervalIntegral.norm_integral_le_of_norm_le_const
    (fun sigma hsigma => norm_desmoothedCubicBottomContourIntegrand_le
      hx hx1 ha hac hW hL (hlog sigma hsigma) hh hsmall hsigma)

/-- Top-edge integral budget with the actual edge length. -/
theorem norm_desmoothedCubicTopContourIntegral_le
    {x h a c W L : ℝ}
    (hx : 0 < x) (hx1 : 1 ≤ x) (ha : 0 < a) (hac : a ≤ c)
    (hW : 0 < W) (hL : 0 ≤ L)
    (hlog : ∀ sigma ∈ Ι a c,
      ‖logDeriv riemannZeta (cubicTopContourPoint W sigma)‖ ≤ L)
    (hh : 0 < h) (hsmall : h * cubicHorizontalEdgeRadius c W ≤ 1) :
    ‖desmoothedCubicTopContourIntegral x h a c W‖ ≤
      desmoothedCubicPointwiseBudget x h c (2 * Real.pi * W) L
          (cubicHorizontalEdgeRadius c W) * |c - a| := by
  unfold desmoothedCubicTopContourIntegral
  exact intervalIntegral.norm_integral_le_of_norm_le_const
    (fun sigma hsigma => norm_desmoothedCubicTopContourIntegrand_le
      hx hx1 ha hac hW hL (hlog sigma hsigma) hh hsmall hsigma)

/-- Left-edge integral budget with the actual vertical length `4*pi*W`. -/
theorem norm_desmoothedCubicLeftContourIntegral_le
    {x h a c W L : ℝ}
    (hx : 0 < x) (hx1 : 1 ≤ x) (ha : 0 < a) (hW : 0 < W)
    (hL : 0 ≤ L)
    (hlog : ∀ t ∈ Ι (-(2 * Real.pi * W)) (2 * Real.pi * W),
      ‖logDeriv riemannZeta (cubicLeftContourPoint a t)‖ ≤ L)
    (hh : 0 < h) (hsmall : h * cubicLeftEdgeRadius a W ≤ 1) :
    ‖desmoothedCubicLeftContourIntegral x h a c W‖ ≤
      desmoothedCubicPointwiseBudget x h a a L
          (cubicLeftEdgeRadius a W) * (4 * Real.pi * W) := by
  unfold desmoothedCubicLeftContourIntegral
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun t ht => norm_desmoothedCubicLeftContourIntegrand_le
      hx hx1 ha hW hL (hlog t ht) hh hsmall ht)
  convert hbound using 1
  have hlength :
      |2 * Real.pi * W - -(2 * Real.pi * W)| = 4 * Real.pi * W := by
    rw [abs_of_pos]
    · ring
    · nlinarith [two_pi_mul_pos hW]
  rw [hlength]

/-- The three concrete edge budgets assemble directly into the actual
de-smoothed contour remainder from Stack196. -/
theorem norm_desmoothedCubicContourRemainder_le_edgeBudgets
    {x h a c W Lbottom Ltop Lleft : ℝ}
    (hx : 0 < x) (hx1 : 1 ≤ x) (ha : 0 < a) (hac : a ≤ c)
    (hW : 0 < W) (hLb : 0 ≤ Lbottom) (hLt : 0 ≤ Ltop)
    (hLl : 0 ≤ Lleft)
    (hbottom : ∀ sigma ∈ Ι a c,
      ‖logDeriv riemannZeta (cubicBottomContourPoint W sigma)‖ ≤ Lbottom)
    (htop : ∀ sigma ∈ Ι a c,
      ‖logDeriv riemannZeta (cubicTopContourPoint W sigma)‖ ≤ Ltop)
    (hleft : ∀ t ∈ Ι (-(2 * Real.pi * W)) (2 * Real.pi * W),
      ‖logDeriv riemannZeta (cubicLeftContourPoint a t)‖ ≤ Lleft)
    (hh : 0 < h)
    (hsmallH : h * cubicHorizontalEdgeRadius c W ≤ 1)
    (hsmallL : h * cubicLeftEdgeRadius a W ≤ 1) :
    ‖desmoothedCubicContourRemainder x h a c W‖ ≤
      (desmoothedCubicPointwiseBudget x h c (2 * Real.pi * W) Lbottom
            (cubicHorizontalEdgeRadius c W) * |c - a| +
        desmoothedCubicPointwiseBudget x h c (2 * Real.pi * W) Ltop
            (cubicHorizontalEdgeRadius c W) * |c - a| +
        desmoothedCubicPointwiseBudget x h a a Lleft
            (cubicLeftEdgeRadius a W) * (4 * Real.pi * W)) /
        (2 * Real.pi) := by
  apply (norm_desmoothedCubicContourRemainder_le x h a c W).trans
  apply div_le_div_of_nonneg_right _ (by nlinarith [Real.pi_pos] : 0 ≤ 2 * Real.pi)
  exact add_le_add
    (add_le_add
      (norm_desmoothedCubicBottomContourIntegral_le hx hx1 ha hac hW hLb
        hbottom hh hsmallH)
      (norm_desmoothedCubicTopContourIntegral_le hx hx1 ha hac hW hLt
        htop hh hsmallH))
    (norm_desmoothedCubicLeftContourIntegral_le hx hx1 ha hW hLl
      hleft hh hsmallL)

end ExplicitFormulaResidues
end PrimeNumberTheorem
