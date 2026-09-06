import HardyTheorem.ConreyHorizontalJensenRegular
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import PrimeNumberTheorem.LittlewoodRectangle

/-!
# Principal-part integrals on Conrey's selected horizontal edges

The imaginary part of one logarithmic principal part is a translated Poisson
kernel.  Its complete interval integral costs at most `pi`, independently of
the zero's distance from the chosen horizontal line.  This prevents the
spurious quadratic divisor-mass loss produced by a pointwise reciprocal bound.
-/

open Complex Set MeasureTheory MeromorphicOn
open PrimeNumberTheorem.CarlsonZeroDensity

namespace HardyTheorem

/-- Exact Poisson-kernel formula for the imaginary part of one horizontal
principal part. -/
theorem abs_im_inv_horizontal_sub_eq_poissonKernel
    {x t : ℝ} {rho : ℂ} :
    |((((x : ℂ) + I * (t : ℂ) - rho)⁻¹).im)| =
      |t - rho.im| / ((t - rho.im) ^ 2 + (x - rho.re) ^ 2) := by
  rw [Complex.inv_im]
  have hden : 0 ≤
      (x - rho.re) * (x - rho.re) +
        (t - rho.im) * (t - rho.im) := by
    nlinarith [sq_nonneg (x - rho.re), sq_nonneg (t - rho.im)]
  simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_add, zero_mul,
    one_mul, Complex.normSq_apply, Complex.sub_re, Complex.add_re,
    Complex.mul_re, Complex.I_re, Complex.ofReal_re, Complex.ofReal_im,
    add_zero, sub_zero]
  rw [abs_div, abs_neg, abs_of_nonneg hden]
  ring

/-- The absolute imaginary Poisson kernel from one zero has interval integral
at most `pi`. -/
theorem integral_abs_im_inv_horizontal_sub_le_pi
    {a b t : ℝ} {rho : ℂ} (ht : t ≠ rho.im) :
    (∫ x in a..b, |((((x : ℂ) + I * (t : ℂ) - rho)⁻¹).im)|) ≤
      Real.pi := by
  let c : ℝ := |t - rho.im|
  have hc : c ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr ht)
  have hpoint : ∀ x : ℝ,
      |((((x : ℂ) + I * (t : ℂ) - rho)⁻¹).im)| =
        c / (c ^ 2 + (x - rho.re) ^ 2) := by
    intro x
    rw [abs_im_inv_horizontal_sub_eq_poissonKernel]
    dsimp [c]
    rw [sq_abs]
  rw [intervalIntegral.integral_congr (fun x _ => hpoint x)]
  change (∫ x in a..b,
    (fun u : ℝ => c / (c ^ 2 + u ^ 2)) (x - rho.re)) ≤ Real.pi
  have hshift :
      (∫ x in a..b,
        (fun u : ℝ => c / (c ^ 2 + u ^ 2)) (x - rho.re)) =
      ∫ x in a - rho.re..b - rho.re, c / (c ^ 2 + x ^ 2) := by
    simpa using
      (intervalIntegral.integral_comp_sub_right
        (fun u : ℝ => c / (c ^ 2 + u ^ 2)) rho.re (a := a) (b := b))
  rw [hshift, integral_div_sq_add_sq]
  nlinarith [Real.neg_pi_div_two_lt_arctan ((b - rho.re) / c),
    Real.arctan_lt_pi_div_two ((b - rho.re) / c),
    Real.neg_pi_div_two_lt_arctan ((a - rho.re) / c),
    Real.arctan_lt_pi_div_two ((a - rho.re) / c)]

/-- With the Littlewood weight `x-a`, one zero costs at most
`(b-a) * pi`; no reciprocal separation is spent. -/
theorem abs_integral_weighted_im_inv_horizontal_sub_le
    {a b t : ℝ} {rho : ℂ} (hab : a ≤ b) (ht : t ≠ rho.im) :
    |∫ x in a..b, (x - a) *
        ((((x : ℂ) + I * (t : ℂ) - rho)⁻¹).im)| ≤
      (b - a) * Real.pi := by
  let c : ℝ := |t - rho.im|
  let p : ℝ → ℝ := fun x => c / (c ^ 2 + (x - rho.re) ^ 2)
  have hc : 0 < c := abs_pos.mpr (sub_ne_zero.mpr ht)
  have hp : ∀ x : ℝ,
      |((((x : ℂ) + I * (t : ℂ) - rho)⁻¹).im)| = p x := by
    intro x
    rw [abs_im_inv_horizontal_sub_eq_poissonKernel]
    dsimp [p, c]
    rw [sq_abs]
  have hpcont : Continuous p := by
    dsimp [p]
    apply Continuous.div continuous_const
      ((continuous_const.pow 2).add
        ((continuous_id.sub continuous_const).pow 2))
    intro x
    have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
    change c ^ 2 + (x - rho.re) ^ 2 ≠ 0
    nlinarith [sq_nonneg (x - rho.re)]
  have hfi : IntervalIntegrable (fun x => (x - a) * p x)
      MeasureTheory.volume a b :=
    ((continuous_id.sub continuous_const).mul hpcont).intervalIntegrable _ _
  have hgi : IntervalIntegrable (fun x => (b - a) * p x)
      MeasureTheory.volume a b :=
    (continuous_const.mul hpcont).intervalIntegrable _ _
  calc
    |∫ x in a..b, (x - a) *
        ((((x : ℂ) + I * (t : ℂ) - rho)⁻¹).im)| ≤
        ∫ x in a..b, |(x - a) *
          ((((x : ℂ) + I * (t : ℂ) - rho)⁻¹).im)| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    _ = ∫ x in a..b, (x - a) * p x := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hxIcc : x ∈ Set.Icc a b := by
        simpa [Set.uIcc_of_le hab] using hx
      dsimp only
      rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hxIcc.1), hp]
    _ ≤ ∫ x in a..b, (b - a) * p x := by
      apply intervalIntegral.integral_mono_on hab hfi hgi
      intro x hx
      have hp0 : 0 ≤ p x := by
        rw [← hp x]
        positivity
      exact mul_le_mul_of_nonneg_right (by linarith [hx.2]) hp0
    _ = (b - a) * ∫ x in a..b, p x := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ (b - a) * Real.pi := by
      apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hab)
      simpa only [← hp] using
        integral_abs_im_inv_horizontal_sub_le_pi (a := a) (b := b) ht

/-- Integrating a uniform complex norm bound against the Littlewood weight
costs exactly the first moment `(b-a)^2/2` of that weight. -/
theorem abs_integral_weighted_im_le_of_norm_le
    (h : ℝ → ℂ) {a b K : ℝ} (hab : a ≤ b)
    (hbound : ∀ x ∈ Set.Icc a b, ‖h x‖ ≤ K) :
    |∫ x in a..b, (x - a) * (h x).im| ≤
      ((b - a) ^ 2 / 2) * K := by
  have hmajorInt : IntervalIntegrable (fun x : ℝ => (x - a) * K)
      MeasureTheory.volume a b :=
    ((continuous_id.sub continuous_const).mul continuous_const)
      |>.intervalIntegrable _ _
  have hpoint : ∀ᵐ x ∂MeasureTheory.volume,
      x ∈ Set.Ioc a b →
        ‖(x - a) * (h x).im‖ ≤ (x - a) * K := by
    filter_upwards [] with x hx
    have hxIcc : x ∈ Set.Icc a b := ⟨hx.1.le, hx.2⟩
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.mpr hxIcc.1)]
    exact mul_le_mul_of_nonneg_left
      ((Complex.abs_im_le_norm (h x)).trans (hbound x hxIcc))
      (sub_nonneg.mpr hxIcc.1)
  have hraw := intervalIntegral.norm_integral_le_of_norm_le
    (f := fun x : ℝ => (x - a) * (h x).im)
    hab hpoint hmajorInt
  have hmajorEval :
      (∫ x in a..b, (x - a) * K) = ((b - a) ^ 2 / 2) * K := by
    rw [intervalIntegral.integral_mul_const]
    let F : ℝ → ℝ := fun y =>
      (((fun u : ℝ => u ^ 2) ∘ fun u : ℝ => _root_.id u - a) y) / 2
    have hderiv : ∀ x : ℝ,
        HasDerivAt F ((2 : ℝ) * (x - a) ^ (2 - 1) * 1 / 2) x := by
      intro x
      exact (hasDerivAt_pow 2 (x - a)).comp x
        ((hasDerivAt_id x).sub_const a) |>.div_const (2 : ℝ)
    have hweightInt : IntervalIntegrable
        (fun x : ℝ => (2 : ℝ) * (x - a) ^ (2 - 1) * 1 / 2)
        MeasureTheory.volume a b :=
      (by fun_prop : Continuous
        (fun x : ℝ => (2 : ℝ) * (x - a) ^ (2 - 1) * 1 / 2))
        |>.intervalIntegrable _ _
    have hweightEval := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _hx => hderiv x) hweightInt
    have hweightEq : (∫ x in a..b, x - a) = (b - a) ^ 2 / 2 := by
      simpa [F] using hweightEval
    rw [hweightEq]
  rw [Real.norm_eq_abs, hmajorEval] at hraw
  exact hraw

/-- The explicit regular-factor norm bound integrates over every selected
horizontal segment with the exact first moment of the Littlewood weight. -/
theorem abs_integral_conreyHorizontalJensenRegularFactor_le
    (g : ℂ → ℂ) {R L U t K : ℝ} (hR0 : 0 ≤ R)
    (hL : 40000 ≤ L) (ht : t ∈ Set.Icc U (U + 1))
    (hregular : ∀ z ∈ Metric.closedBall
      (conreyHorizontalJensenCenter L U)
      (conreyHorizontalJensenInnerRadius R L), ‖logDeriv g z‖ ≤ K) :
    |∫ x in conreyHorizontalLeftEdge R L..conreyHorizontalRightEdge L,
        (x - conreyHorizontalLeftEdge R L) *
          (logDeriv g ((x : ℂ) + I * (t : ℂ))).im| ≤
      ((conreyHorizontalRightEdge L -
          conreyHorizontalLeftEdge R L) ^ 2 / 2) * K := by
  let a := conreyHorizontalLeftEdge R L
  let b := conreyHorizontalRightEdge L
  have hLpos : 0 < L := by linarith
  have hlogL := two_le_log_of_forty_thousand_le hL
  have haUpper : a ≤ 1 / 2 := by
    dsimp [a, conreyHorizontalLeftEdge]
    exact sub_le_self _ (div_nonneg hR0 hLpos.le)
  have hab : a ≤ b := by
    dsimp [b, conreyHorizontalRightEdge]
    linarith
  apply abs_integral_weighted_im_le_of_norm_le
    (h := fun x : ℝ => logDeriv g ((x : ℂ) + I * (t : ℂ))) hab
  intro x hx
  apply hregular
  apply conreyHorizontalJensenRectangle_subset_innerClosedBall R L U
  change ((x : ℂ) + I * (t : ℂ)).re ∈
      Set.Icc (conreyHorizontalLeftEdge R L)
        (conreyHorizontalRightEdge L) ∧
    ((x : ℂ) + I * (t : ℂ)).im ∈ Set.Icc U (U + 1)
  constructor
  · simpa [a, b] using hx
  · simpa using ht

/-- Multiplicity-weighted finite principal parts cost only the total
multiplicity times the one-zero Poisson bound. -/
theorem abs_integral_weighted_finset_principalParts_le
    (P : Finset ℂ) (m : ℂ → ℝ) {a b t : ℝ} (hab : a ≤ b)
    (hm : ∀ rho ∈ P, 0 ≤ m rho) (ht : ∀ rho ∈ P, t ≠ rho.im) :
    |∫ x in a..b, (x - a) *
        (∑ rho ∈ P, m rho *
          ((((x : ℂ) + I * (t : ℂ) - rho)⁻¹).im))| ≤
      (b - a) * Real.pi * ∑ rho ∈ P, m rho := by
  have hne : ∀ rho ∈ P, ∀ x : ℝ,
      (x : ℂ) + I * (t : ℂ) - rho ≠ 0 := by
    intro rho hrho x hzero
    have him := congrArg Complex.im hzero
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      zero_add, zero_mul, one_mul, sub_eq_zero, Complex.zero_im] at him
    exact ht rho hrho him
  have hinterm : ∀ rho ∈ P, IntervalIntegrable
      (fun x : ℝ => (x - a) * m rho *
        ((((x : ℂ) + I * (t : ℂ) - rho)⁻¹).im))
      MeasureTheory.volume a b := by
    intro rho hrho
    have hinv : Continuous fun x : ℝ =>
        (((x : ℂ) + I * (t : ℂ) - rho)⁻¹) := by
      exact (by fun_prop : Continuous fun x : ℝ =>
        (x : ℂ) + I * (t : ℂ) - rho).inv₀ (hne rho hrho)
    have himCont : Continuous fun x : ℝ =>
        ((((x : ℂ) + I * (t : ℂ) - rho)⁻¹).im) := by
      change Continuous (Complex.im ∘ fun x : ℝ =>
        ((x : ℂ) + I * (t : ℂ) - rho)⁻¹)
      exact Complex.continuous_im.comp hinv
    exact (((continuous_id.sub continuous_const).mul continuous_const).mul
      himCont).intervalIntegrable _ _
  have hsplit :
      (∫ x in a..b, (x - a) *
        (∑ rho ∈ P, m rho *
          ((((x : ℂ) + I * (t : ℂ) - rho)⁻¹).im))) =
      ∑ rho ∈ P, ∫ x in a..b, (x - a) * m rho *
        ((((x : ℂ) + I * (t : ℂ) - rho)⁻¹).im) := by
    rw [show (fun x : ℝ => (x - a) *
        (∑ rho ∈ P, m rho *
          ((((x : ℂ) + I * (t : ℂ) - rho)⁻¹).im))) =
        (fun x : ℝ => ∑ rho ∈ P, (x - a) * m rho *
          ((((x : ℂ) + I * (t : ℂ) - rho)⁻¹).im)) by
      funext x
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rho hrho
      ring]
    exact intervalIntegral.integral_finsetSum hinterm
  rw [hsplit]
  calc
    |∑ rho ∈ P, ∫ x in a..b, (x - a) * m rho *
        ((((x : ℂ) + I * (t : ℂ) - rho)⁻¹).im)| ≤
        ∑ rho ∈ P, |∫ x in a..b, (x - a) * m rho *
          ((((x : ℂ) + I * (t : ℂ) - rho)⁻¹).im)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ rho ∈ P, m rho * ((b - a) * Real.pi) := by
      apply Finset.sum_le_sum
      intro rho hrho
      rw [show (fun x : ℝ => (x - a) * m rho *
          ((((x : ℂ) + I * (t : ℂ) - rho)⁻¹).im)) =
          (fun x : ℝ => m rho * ((x - a) *
            ((((x : ℂ) + I * (t : ℂ) - rho)⁻¹).im))) by
        funext x; ring,
        intervalIntegral.integral_const_mul, abs_mul,
        abs_of_nonneg (hm rho hrho)]
      exact mul_le_mul_of_nonneg_left
        (abs_integral_weighted_im_inv_horizontal_sub_le hab (ht rho hrho))
        (hm rho hrho)
    _ = (b - a) * Real.pi * ∑ rho ∈ P, m rho := by
      rw [← Finset.sum_mul]
      ring

/-- Imaginary parts of all distinct zeros in the factorization disk. -/
noncomputable def conreyHorizontalJensenFactorZeroHeights
    (Y : ℕ) (R L U : ℝ) : Finset ℝ :=
  (conreyHorizontalJensenFactorZeroSupport Y R L U).image Complex.im

/-- Pigeonhole separation for a horizontal line selected against the complete
factor-disk zero support. -/
noncomputable def conreyHorizontalJensenFactorHorizontalSeparation
    (Y : ℕ) (R L U : ℝ) : ℝ :=
  1 / (4 * (((conreyHorizontalJensenFactorZeroHeights Y R L U).card : ℝ) + 1))

/-- A divisor-mass majorant also controls the factor-support height
separation. -/
theorem conreyHorizontalJensenFactorHorizontalSeparation_lower_of_mass_le
    {Y : ℕ} {R L U J : ℝ} (hR0 : 0 ≤ R) (hRmax : R ≤ 6 / 5)
    (hL : 40000 ≤ L) (hU : conreyHorizontalRightEdge L + 1 ≤ U)
    (hmass : conreyHorizontalJensenFactorZeroMass Y R L U ≤ J) :
    0 < 1 / (4 * (J + 1)) ∧
      1 / (4 * (J + 1)) ≤
        conreyHorizontalJensenFactorHorizontalSeparation Y R L U := by
  classical
  let zeros := conreyHorizontalJensenFactorZeroSupport Y R L U
  let heights := conreyHorizontalJensenFactorZeroHeights Y R L U
  have hmassNonneg : 0 ≤ conreyHorizontalJensenFactorZeroMass Y R L U := by
    let c : ℂ := conreyHorizontalJensenCenter L U
    let b : ℝ := conreyHorizontalJensenFactorRadius R L
    let D := MeromorphicOn.divisor (conreyHorizontalJensenProduct Y R L)
      (Metric.closedBall c b)
    have hbuffer := conreyHorizontalJensenBufferGeometry hR0 hRmax hL
    have hanalyticOuter :=
      analyticOnNhd_conreyExplicitMollifiedV1_horizontalJensenOuterClosedBall
        Y (conreyHorizontalLeftEdge R L) L U hL hU
    have hanalyticFactor : AnalyticOnNhd ℂ
        (conreyHorizontalJensenProduct Y R L) (Metric.closedBall c b) := by
      simpa [c, b, conreyHorizontalJensenProduct] using
        hanalyticOuter.mono
          (Metric.closedBall_subset_closedBall hbuffer.2.2.2.le)
    have hDnonneg : 0 ≤ D := hanalyticFactor.divisor_nonneg
    change 0 ≤ ∑ᶠ u, (D u : ℝ)
    apply finsum_nonneg
    intro u
    exact_mod_cast hDnonneg u
  have hJnonneg : 0 ≤ J := hmassNonneg.trans hmass
  have hsupportMass : (zeros.card : ℝ) ≤
      conreyHorizontalJensenFactorZeroMass Y R L U := by
    simpa [zeros] using
      card_conreyHorizontalJensenFactorZeroSupport_le_mass
        (Y := Y) (U := U) hR0 hRmax hL hU
  have hheightNat : heights.card ≤ zeros.card := by
    dsimp [heights, conreyHorizontalJensenFactorZeroHeights]
    exact Finset.card_image_le
  have hheightMass : (heights.card : ℝ) ≤
      conreyHorizontalJensenFactorZeroMass Y R L U := by
    have hheightReal : (heights.card : ℝ) ≤ (zeros.card : ℝ) := by
      exact_mod_cast hheightNat
    exact hheightReal.trans hsupportMass
  have hheightJ : (heights.card : ℝ) ≤ J := hheightMass.trans hmass
  have hsmallDenPos : 0 < 4 * ((heights.card : ℝ) + 1) := by positivity
  have hlargeDenPos : 0 < 4 * (J + 1) := by positivity
  have hdenLe : 4 * ((heights.card : ℝ) + 1) ≤ 4 * (J + 1) := by
    nlinarith
  have hrecip : 1 / (4 * (J + 1)) ≤
      1 / (4 * ((heights.card : ℝ) + 1)) :=
    one_div_le_one_div_of_le hsmallDenPos hdenLe
  refine ⟨one_div_pos.mpr hlargeDenPos, ?_⟩
  simpa [conreyHorizontalJensenFactorHorizontalSeparation, heights] using hrecip

/-- Every unit window contains a height separated from every factor-disk zero
ordinate; in particular the actual product is nonzero on the whole horizontal
segment. -/
theorem exists_conreyHorizontalJensenFactorAdmissibleHeight
    {Y : ℕ} {R L U : ℝ} (hY : 2 ≤ Y) (hR0 : 0 ≤ R)
    (hRmax : R ≤ 6 / 5) (hL : 40000 ≤ L)
    (hU : conreyHorizontalRightEdge L + 1 ≤ U) :
    ∃ t ∈ Set.Icc U (U + 1),
      (∀ z ∈ conreyHorizontalJensenFactorZeroSupport Y R L U,
        conreyHorizontalJensenFactorHorizontalSeparation Y R L U ≤
          |t - z.im|) ∧
      ∀ x ∈ Set.Icc (conreyHorizontalLeftEdge R L)
          (conreyHorizontalRightEdge L),
        conreyHorizontalJensenProduct Y R L
          ((x : ℂ) + I * (t : ℂ)) ≠ 0 := by
  classical
  let P := conreyHorizontalJensenFactorZeroSupport Y R L U
  let H := conreyHorizontalJensenFactorZeroHeights Y R L U
  rcases ZeroFreeRegion.exists_radius_separated_from_finset H
      (show U < U + 1 by linarith) with ⟨t, ht, hsep⟩
  have hdelta : 0 < 1 / ((4 : ℝ) * ((H.card : ℝ) + 1)) := by
    positivity
  refine ⟨t, ht, ?_, ?_⟩
  · intro z hz
    have hzim : z.im ∈ H := by
      dsimp [H, conreyHorizontalJensenFactorZeroHeights]
      exact Finset.mem_image.mpr ⟨z, by simpa [P] using hz, rfl⟩
    simpa [H, conreyHorizontalJensenFactorHorizontalSeparation] using
      hsep z.im hzim
  · intro x hx hzero
    let z : ℂ := (x : ℂ) + I * (t : ℂ)
    have hzRect : z ∈ conreyHorizontalJensenRectangle R L U := by
      change z.re ∈ Set.Icc (conreyHorizontalLeftEdge R L)
          (conreyHorizontalRightEdge L) ∧ z.im ∈ Set.Icc U (U + 1)
      constructor
      · simpa [z] using hx
      · simpa [z] using ht
    have hzInner : z ∈ Metric.closedBall (conreyHorizontalJensenCenter L U)
        (conreyHorizontalJensenInnerRadius R L) :=
      conreyHorizontalJensenRectangle_subset_innerClosedBall R L U hzRect
    have hbuffer := conreyHorizontalJensenBufferGeometry hR0 hRmax hL
    have hzFactor : z ∈ Metric.closedBall (conreyHorizontalJensenCenter L U)
        (conreyHorizontalJensenFactorRadius R L) :=
      Metric.closedBall_subset_closedBall
        (hbuffer.1.trans (hbuffer.2.1.trans hbuffer.2.2.1)).le hzInner
    have hzP : z ∈ P := by
      dsimp [P]
      exact (mem_conreyHorizontalJensenFactorZeroSupport_iff_zero
        hY hR0 hRmax hL hU hzFactor).mpr (by simpa [z] using hzero)
    have hzim : z.im ∈ H := by
      dsimp [H, conreyHorizontalJensenFactorZeroHeights]
      exact Finset.mem_image.mpr ⟨z, by simpa [P] using hzP, rfl⟩
    have hzeroDistance :
        1 / ((4 : ℝ) * ((H.card : ℝ) + 1)) ≤ 0 := by
      simpa [z] using hsep z.im hzim
    exact (not_lt_of_ge hzeroDistance) hdelta

/-- The complete multiplicity-weighted factor-disk principal part satisfies
the sharp linear-in-mass weighted horizontal integral bound. -/
theorem abs_integral_conreyHorizontalJensenFactorPrincipalPart_le
    {Y : ℕ} {R L U t : ℝ} (hR0 : 0 ≤ R) (hRmax : R ≤ 6 / 5)
    (hL : 40000 ≤ L) (hU : conreyHorizontalRightEdge L + 1 ≤ U)
    (ht : ∀ rho ∈ conreyHorizontalJensenFactorZeroSupport Y R L U,
      t ≠ rho.im) :
    |∫ x in conreyHorizontalLeftEdge R L..conreyHorizontalRightEdge L,
        (x - conreyHorizontalLeftEdge R L) *
          ((∑ᶠ rho,
            (MeromorphicOn.divisor (conreyHorizontalJensenProduct Y R L)
              (Metric.closedBall (conreyHorizontalJensenCenter L U)
                (conreyHorizontalJensenFactorRadius R L)) rho : ℂ) *
              (((x : ℂ) + I * (t : ℂ) - rho)⁻¹)).im)| ≤
      (conreyHorizontalRightEdge L - conreyHorizontalLeftEdge R L) *
        Real.pi * conreyHorizontalJensenFactorZeroMass Y R L U := by
  classical
  let a : ℝ := conreyHorizontalLeftEdge R L
  let bRight : ℝ := conreyHorizontalRightEdge L
  let c : ℂ := conreyHorizontalJensenCenter L U
  let b : ℝ := conreyHorizontalJensenFactorRadius R L
  let f : ℂ → ℂ := conreyHorizontalJensenProduct Y R L
  let D := MeromorphicOn.divisor f (Metric.closedBall c b)
  let P := conreyHorizontalJensenFactorZeroSupport Y R L U
  have hLpos : 0 < L := by linarith
  have hlogL := two_le_log_of_forty_thousand_le hL
  have haUpper : a ≤ 1 / 2 := by
    dsimp [a, conreyHorizontalLeftEdge]
    exact sub_le_self _ (div_nonneg hR0 hLpos.le)
  have hab : a ≤ bRight := by
    dsimp [bRight, conreyHorizontalRightEdge]
    linarith
  have hbuffer := conreyHorizontalJensenBufferGeometry hR0 hRmax hL
  have hanalyticOuter :=
    analyticOnNhd_conreyExplicitMollifiedV1_horizontalJensenOuterClosedBall
      Y (conreyHorizontalLeftEdge R L) L U hL hU
  have hanalyticFactor : AnalyticOnNhd ℂ f (Metric.closedBall c b) := by
    simpa [f, c, b, conreyHorizontalJensenProduct] using
      hanalyticOuter.mono
        (Metric.closedBall_subset_closedBall hbuffer.2.2.2.le)
  have hDfinite : D.support.Finite :=
    D.finiteSupport (isCompact_closedBall c b)
  have hDnonneg : 0 ≤ D := hanalyticFactor.divisor_nonneg
  have hPdef : P = hDfinite.toFinset := by
    simp [P, D, f, c, b, conreyHorizontalJensenFactorZeroSupport]
  have hprincipal : ∀ x : ℝ,
      (∑ᶠ rho, (D rho : ℂ) *
          (((x : ℂ) + I * (t : ℂ) - rho)⁻¹)) =
        ∑ rho ∈ P, (D rho : ℂ) *
          (((x : ℂ) + I * (t : ℂ) - rho)⁻¹) := by
    intro x
    apply finsum_eq_sum_of_support_subset
    intro rho hrho
    change rho ∈ P
    rw [hPdef, hDfinite.mem_toFinset]
    by_contra hrhoD
    have hDrho : D rho = 0 := by
      simpa [Function.mem_support] using hrhoD
    simp [hDrho] at hrho
  have himag : ∀ x : ℝ,
      ((∑ᶠ rho, (D rho : ℂ) *
          (((x : ℂ) + I * (t : ℂ) - rho)⁻¹))).im =
        ∑ rho ∈ P, (D rho : ℝ) *
          ((((x : ℂ) + I * (t : ℂ) - rho)⁻¹).im) := by
    intro x
    rw [hprincipal x]
    simp
  have hmassSupport : (fun rho : ℂ => (D rho : ℝ)).support ⊆ P := by
    intro rho hrho
    change rho ∈ P
    rw [hPdef, hDfinite.mem_toFinset]
    by_contra hrhoD
    have hDrho : D rho = 0 := by
      simpa [Function.mem_support] using hrhoD
    simp [hDrho] at hrho
  have hmassEq : (∑ rho ∈ P, (D rho : ℝ)) =
      conreyHorizontalJensenFactorZeroMass Y R L U := by
    have hsum := finsum_eq_sum_of_support_subset
      (fun rho : ℂ => (D rho : ℝ)) hmassSupport
    simpa [D, f, c, b, P, conreyHorizontalJensenFactorZeroMass] using hsum.symm
  rw [show (fun x : ℝ =>
      (x - conreyHorizontalLeftEdge R L) *
        ((∑ᶠ rho,
          (MeromorphicOn.divisor (conreyHorizontalJensenProduct Y R L)
            (Metric.closedBall (conreyHorizontalJensenCenter L U)
              (conreyHorizontalJensenFactorRadius R L)) rho : ℂ) *
            (((x : ℂ) + I * (t : ℂ) - rho)⁻¹)).im)) =
      (fun x : ℝ => (x - a) *
        (∑ rho ∈ P, (D rho : ℝ) *
          ((((x : ℂ) + I * (t : ℂ) - rho)⁻¹).im))) by
    funext x
    simpa [a, D, f, c, b] using congrArg (fun y : ℝ => (x - a) * y) (himag x)]
  have hbound := abs_integral_weighted_finset_principalParts_le
    P (fun rho => (D rho : ℝ)) hab
    (fun rho hrho => by exact_mod_cast hDnonneg rho)
    (fun rho hrho => ht rho (by simpa [P] using hrho))
  calc
    |∫ x in a..bRight, (x - a) *
        (∑ rho ∈ P, (D rho : ℝ) *
          ((((x : ℂ) + I * (t : ℂ) - rho)⁻¹).im))| ≤
        (bRight - a) * Real.pi * ∑ rho ∈ P, (D rho : ℝ) := hbound
    _ = (conreyHorizontalRightEdge L - conreyHorizontalLeftEdge R L) *
        Real.pi * conreyHorizontalJensenFactorZeroMass Y R L U := by
      rw [hmassEq]

/-- A factor-support admissible height simultaneously keeps the actual
product nonzero and gives the complete linear-in-mass principal-part bound. -/
theorem exists_conreyHorizontalJensenFactorHeight_principalPart_le
    {Y : ℕ} {R L U : ℝ} (hY : 2 ≤ Y) (hR0 : 0 ≤ R)
    (hRmax : R ≤ 6 / 5) (hL : 40000 ≤ L)
    (hU : conreyHorizontalRightEdge L + 1 ≤ U) :
    ∃ t ∈ Set.Icc U (U + 1),
      (∀ rho ∈ conreyHorizontalJensenFactorZeroSupport Y R L U,
        conreyHorizontalJensenFactorHorizontalSeparation Y R L U ≤
          |t - rho.im|) ∧
      (∀ x ∈ Set.Icc (conreyHorizontalLeftEdge R L)
          (conreyHorizontalRightEdge L),
        conreyHorizontalJensenProduct Y R L
          ((x : ℂ) + I * (t : ℂ)) ≠ 0) ∧
      |∫ x in conreyHorizontalLeftEdge R L..conreyHorizontalRightEdge L,
          (x - conreyHorizontalLeftEdge R L) *
            ((∑ᶠ rho,
              (MeromorphicOn.divisor (conreyHorizontalJensenProduct Y R L)
                (Metric.closedBall (conreyHorizontalJensenCenter L U)
                  (conreyHorizontalJensenFactorRadius R L)) rho : ℂ) *
                (((x : ℂ) + I * (t : ℂ) - rho)⁻¹)).im)| ≤
        (conreyHorizontalRightEdge L - conreyHorizontalLeftEdge R L) *
          Real.pi * conreyHorizontalJensenFactorZeroMass Y R L U := by
  rcases exists_conreyHorizontalJensenFactorAdmissibleHeight
      hY hR0 hRmax hL hU with ⟨t, htWindow, hsep, hnonzero⟩
  have hsepPos : 0 < conreyHorizontalJensenFactorHorizontalSeparation
      Y R L U := by
    dsimp [conreyHorizontalJensenFactorHorizontalSeparation]
    positivity
  have htZero : ∀ rho ∈ conreyHorizontalJensenFactorZeroSupport Y R L U,
      t ≠ rho.im := by
    intro rho hrho hteq
    have h := hsep rho hrho
    rw [hteq, sub_self, abs_zero] at h
    exact (not_lt_of_ge h) hsepPos
  refine ⟨t, htWindow, hsep, hnonzero, ?_⟩
  exact abs_integral_conreyHorizontalJensenFactorPrincipalPart_le
    hR0 hRmax hL hU htZero

/-- At one and the same selected height, the actual logarithmic derivative
splits into the complete factor-disk principal part and the extracted regular
factor.  Their weighted integrals satisfy the explicit linear-in-mass bound. -/
theorem exists_conreyHorizontalJensenHeight_weightedLogDeriv_le :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Y : ℕ} {R L U J : ℝ}, 2 ≤ Y →
      (Y : ℝ) ≤ Real.exp L → 0 ≤ R → R ≤ 6 / 5 → 40000 ≤ L →
      conreyHorizontalRightEdge L + 1 ≤ U → U + 1 ≤ Real.exp L →
      conreyHorizontalJensenFactorZeroMass Y R L U ≤ J →
      ∃ t ∈ Set.Icc U (U + 1),
        (∀ x ∈ Set.Icc (conreyHorizontalLeftEdge R L)
            (conreyHorizontalRightEdge L),
          conreyHorizontalJensenProduct Y R L
            ((x : ℂ) + I * (t : ℂ)) ≠ 0) ∧
        |∫ x in conreyHorizontalLeftEdge R L..conreyHorizontalRightEdge L,
            (x - conreyHorizontalLeftEdge R L) *
              (logDeriv (conreyHorizontalJensenProduct Y R L)
                ((x : ℂ) + I * (t : ℂ))).im| ≤
          ((conreyHorizontalRightEdge L -
              conreyHorizontalLeftEdge R L) ^ 2 / 2) *
              (128 * max
                (conreyHorizontalJensenFactorLogVariationMajorant
                  C Y R L U J) 1 *
                conreyHorizontalJensenOuterRadius L /
                conreyHorizontalJensenRadiusGap R L ^ 2) +
            (conreyHorizontalRightEdge L -
                conreyHorizontalLeftEdge R L) * Real.pi * J := by
  rcases exists_conreyHorizontalJensenGoodFactor_logDeriv_le_explicit with
    ⟨C, hC, hfactor⟩
  refine ⟨C, hC, ?_⟩
  intro Y R L U J hY hYtop hR0 hRmax hL hU hUtop hmass
  rcases hfactor hY hYtop hR0 hRmax hL hU hUtop hmass with
    ⟨q, g, hq, hg, hgne, hdecomp, hregular⟩
  rcases exists_conreyHorizontalJensenFactorHeight_principalPart_le
      hY hR0 hRmax hL hU with
    ⟨t, htWindow, hsep, hproductNe, hprincipalBound⟩
  refine ⟨t, htWindow, hproductNe, ?_⟩
  let a : ℝ := conreyHorizontalLeftEdge R L
  let bRight : ℝ := conreyHorizontalRightEdge L
  let c : ℂ := conreyHorizontalJensenCenter L U
  let bFactor : ℝ := conreyHorizontalJensenFactorRadius R L
  let f : ℂ → ℂ := conreyHorizontalJensenProduct Y R L
  let D := MeromorphicOn.divisor f (Metric.closedBall c bFactor)
  let z : ℝ → ℂ := fun x => (x : ℂ) + I * (t : ℂ)
  let principal : ℝ → ℂ := fun x =>
    ∑ᶠ rho, (D rho : ℂ) * (z x - rho)⁻¹
  let regular : ℝ → ℂ := fun x => logDeriv g (z x)
  let total : ℝ → ℂ := fun x => logDeriv f (z x)
  let K : ℝ :=
    128 * max
        (conreyHorizontalJensenFactorLogVariationMajorant C Y R L U J) 1 *
      conreyHorizontalJensenOuterRadius L /
      conreyHorizontalJensenRadiusGap R L ^ 2
  have hLpos : 0 < L := by linarith
  have hlogL := two_le_log_of_forty_thousand_le hL
  have haUpper : a ≤ 1 / 2 := by
    dsimp [a, conreyHorizontalLeftEdge]
    exact sub_le_self _ (div_nonneg hR0 hLpos.le)
  have hab : a ≤ bRight := by
    dsimp [bRight, conreyHorizontalRightEdge]
    linarith
  have hbuffer := conreyHorizontalJensenBufferGeometry hR0 hRmax hL
  have hzInner : ∀ x ∈ Set.Icc a bRight,
      z x ∈ Metric.closedBall c
        (conreyHorizontalJensenInnerRadius R L) := by
    intro x hx
    apply conreyHorizontalJensenRectangle_subset_innerClosedBall R L U
    change (z x).re ∈ Set.Icc (conreyHorizontalLeftEdge R L)
        (conreyHorizontalRightEdge L) ∧
      (z x).im ∈ Set.Icc U (U + 1)
    constructor
    · simpa [z, a, bRight] using hx
    · simpa [z] using htWindow
  have hzFactorClosed : ∀ x ∈ Set.Icc a bRight,
      z x ∈ Metric.closedBall c bFactor := by
    intro x hx
    exact Metric.closedBall_subset_closedBall
      (hbuffer.1.trans (hbuffer.2.1.trans hbuffer.2.2.1)).le
      (hzInner x hx)
  have hzFactorBall : ∀ x ∈ Set.Icc a bRight,
      z x ∈ Metric.ball c bFactor := by
    intro x hx
    exact Metric.closedBall_subset_ball
      (hbuffer.1.trans (hbuffer.2.1.trans hbuffer.2.2.1))
      (hzInner x hx)
  have hsplitPoint : ∀ x ∈ Set.Icc a bRight,
      total x = principal x + regular x := by
    intro x hx
    have hne : f (z x) ≠ 0 := by
      have hxSegment : x ∈ Set.Icc
          (conreyHorizontalLeftEdge R L)
          (conreyHorizontalRightEdge L) := by
        simpa [a, bRight] using hx
      simpa [f, z] using (hproductNe x hxSegment)
    have h := hdecomp (z x)
      (by simpa [c, bFactor] using hzFactorBall x hx)
      (by simpa [f] using hne)
    simpa [total, principal, regular, D, f, c, bFactor, z] using h
  have hanalyticOuter :=
    analyticOnNhd_conreyExplicitMollifiedV1_horizontalJensenOuterClosedBall
      Y (conreyHorizontalLeftEdge R L) L U hL hU
  have hFanalytic : ∀ x ∈ Set.uIcc a bRight,
      AnalyticAt ℂ f ((x : ℂ) + (t : ℂ) * I) := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hzOut : z x ∈ Metric.closedBall c
        (conreyHorizontalJensenOuterRadius L) :=
      Metric.closedBall_subset_closedBall
        (conreyHorizontalJensenInnerRadius_lt_outerRadius hR0 hRmax hL).le
        (hzInner x hx)
    simpa [f, z, c, mul_comm, conreyHorizontalJensenProduct] using
      hanalyticOuter (z x) hzOut
  have hFne : ∀ x ∈ Set.uIcc a bRight,
      f ((x : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    simpa [f, z, mul_comm] using hproductNe x
      (by simpa [a, bRight] using hx)
  have hganalytic : ∀ x ∈ Set.uIcc a bRight,
      AnalyticAt ℂ g ((x : ℂ) + (t : ℂ) * I) := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    simpa [z, c, bFactor, mul_comm] using
      hg (z x) (by simpa [c, bFactor] using hzFactorClosed x hx)
  have hgneLine : ∀ x ∈ Set.uIcc a bRight,
      g ((x : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    simpa [z, c, bFactor, mul_comm] using
      hgne ⟨z x, by simpa [c, bFactor] using hzFactorClosed x hx⟩
  have htotalCont : ContinuousOn total (Set.uIcc a bRight) := by
    simpa [total, f, z, mul_comm] using
      PrimeNumberTheorem.CarlsonZeroDensity.continuousOn_logDeriv_horizontal
        hFanalytic hFne
  have hregularCont : ContinuousOn regular (Set.uIcc a bRight) := by
    simpa [regular, z, mul_comm] using
      PrimeNumberTheorem.CarlsonZeroDensity.continuousOn_logDeriv_horizontal
        hganalytic hgneLine
  have htotalWeightedInt : IntervalIntegrable
      (fun x : ℝ => (x - a) * (total x).im)
      MeasureTheory.volume a bRight :=
    ((continuousOn_id.sub continuousOn_const).mul
      (Complex.continuous_im.comp_continuousOn htotalCont)).intervalIntegrable
  have hregularWeightedInt : IntervalIntegrable
      (fun x : ℝ => (x - a) * (regular x).im)
      MeasureTheory.volume a bRight :=
    ((continuousOn_id.sub continuousOn_const).mul
      (Complex.continuous_im.comp_continuousOn hregularCont)).intervalIntegrable
  have hprincipalWeightedInt : IntervalIntegrable
      (fun x : ℝ => (x - a) * (principal x).im)
      MeasureTheory.volume a bRight := by
    apply IntervalIntegrable.congr
      (f := fun x : ℝ =>
        (x - a) * (total x).im - (x - a) * (regular x).im)
    · intro x hx
      have hxIcc : x ∈ Set.Icc a bRight := by
        rw [Set.uIoc_of_le hab] at hx
        exact ⟨hx.1.le, hx.2⟩
      have hs := congrArg Complex.im (hsplitPoint x hxIcc)
      dsimp only
      simp only [Complex.add_im] at hs
      rw [hs]
      ring
    · exact htotalWeightedInt.sub hregularWeightedInt
  have hsplitIntegral :
      (∫ x in a..bRight, (x - a) * (total x).im) =
        (∫ x in a..bRight, (x - a) * (principal x).im) +
          ∫ x in a..bRight, (x - a) * (regular x).im := by
    calc
      (∫ x in a..bRight, (x - a) * (total x).im) =
          ∫ x in a..bRight,
            (x - a) * (principal x).im +
              (x - a) * (regular x).im := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hxIcc : x ∈ Set.Icc a bRight := by
          simpa [Set.uIcc_of_le hab] using hx
        have hs := congrArg Complex.im (hsplitPoint x hxIcc)
        simp only [Complex.add_im] at hs
        dsimp only
        rw [hs]
        ring
      _ = (∫ x in a..bRight, (x - a) * (principal x).im) +
          ∫ x in a..bRight, (x - a) * (regular x).im :=
        intervalIntegral.integral_add
          hprincipalWeightedInt hregularWeightedInt
  have hregularIntegral :
      |∫ x in a..bRight, (x - a) * (regular x).im| ≤
        ((bRight - a) ^ 2 / 2) * K := by
    have h := abs_integral_conreyHorizontalJensenRegularFactor_le
      g hR0 hL htWindow hregular
    simpa [a, bRight, regular, z, K] using h
  have hwidthNonneg : 0 ≤ bRight - a := sub_nonneg.mpr hab
  have hprincipalIntegral :
      |∫ x in a..bRight, (x - a) * (principal x).im| ≤
        (bRight - a) * Real.pi * J := by
    have hactual :
        |∫ x in a..bRight, (x - a) * (principal x).im| ≤
          (bRight - a) * Real.pi *
            conreyHorizontalJensenFactorZeroMass Y R L U := by
      simpa [a, bRight, principal, z, D, f, c, bFactor] using
        hprincipalBound
    exact hactual.trans (mul_le_mul_of_nonneg_left hmass
      (mul_nonneg hwidthNonneg Real.pi_pos.le))
  change |∫ x in a..bRight, (x - a) * (total x).im| ≤
    ((bRight - a) ^ 2 / 2) * K + (bRight - a) * Real.pi * J
  rw [hsplitIntegral]
  exact (abs_add_le _ _).trans
    ((add_le_add hprincipalIntegral hregularIntegral).trans_eq (by ring))

end HardyTheorem
