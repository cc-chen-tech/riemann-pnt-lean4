import HardyTheorem.ConreyExplicitRightVerticalLow

/-!
# Moving Jensen geometry for Conrey's horizontal edges

This file fixes an explicit Jensen disk around one unit-height horizontal
window.  The outer disk remains in `Re s >= 1/4` and, once the window starts
above the moving right edge, avoids the pole at `s = 1`.  Consequently the
actual product `V₁ B`, rather than an abstract regularization, is analytic on
the whole disk.
-/

open Complex Set

namespace HardyTheorem

/-- The corrected moving right edge used in the Conrey contour. -/
noncomputable def conreyHorizontalRightEdge (L : ℝ) : ℝ :=
  2 * Real.log L

/-- The Littlewood left edge `1/2 - R/L`. -/
noncomputable def conreyHorizontalLeftEdge (R L : ℝ) : ℝ :=
  1 / 2 - R / L

/-- Center of the Jensen disk for the unit height window `[U,U+1]`. -/
noncomputable def conreyHorizontalJensenCenter (L U : ℝ) : ℂ :=
  (conreyHorizontalRightEdge L : ℂ) + I * (U + 1 / 2)

/-- Radius of the smallest centered disk used here to cover the rectangle. -/
noncomputable def conreyHorizontalJensenInnerRadius (R L : ℝ) : ℝ :=
  Real.sqrt
    ((conreyHorizontalRightEdge L - conreyHorizontalLeftEdge R L) ^ 2 +
      1 / 4)

/-- The outer radius leaves the entire disk in `Re s >= 1/4`. -/
noncomputable def conreyHorizontalJensenOuterRadius (L : ℝ) : ℝ :=
  conreyHorizontalRightEdge L - 1 / 4

/-- The unit-height rectangle covered by the inner Jensen disk. -/
def conreyHorizontalJensenRectangle (R L U : ℝ) : Set ℂ :=
  Set.Icc (conreyHorizontalLeftEdge R L) (conreyHorizontalRightEdge L) ×ℂ
    Set.Icc U (U + 1)

/-- The exact inner radius covers the whole unit-height rectangle. -/
theorem conreyHorizontalJensenRectangle_subset_innerClosedBall
    (R L U : ℝ) :
    conreyHorizontalJensenRectangle R L U ⊆
      Metric.closedBall (conreyHorizontalJensenCenter L U)
        (conreyHorizontalJensenInnerRadius R L) := by
  intro z hz
  rw [Metric.mem_closedBall, Complex.dist_eq]
  have hreLower : conreyHorizontalLeftEdge R L ≤ z.re := hz.1.1
  have hreUpper : z.re ≤ conreyHorizontalRightEdge L := hz.1.2
  have himLower : U ≤ z.im := hz.2.1
  have himUpper : z.im ≤ U + 1 := hz.2.2
  have hreSq :
      (z.re - conreyHorizontalRightEdge L) ^ 2 ≤
        (conreyHorizontalRightEdge L - conreyHorizontalLeftEdge R L) ^ 2 := by
    nlinarith [mul_nonneg
      (sub_nonneg.mpr hreLower)
      (sub_nonneg.mpr (by linarith :
        z.re - conreyHorizontalLeftEdge R L ≤
          2 * (conreyHorizontalRightEdge L -
            conreyHorizontalLeftEdge R L)))]
  have himSq : (z.im - (U + 1 / 2)) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg
      (by linarith : 0 ≤ z.im - U)
      (by linarith : 0 ≤ U + 1 - z.im)]
  have hradicand :
      0 ≤ (conreyHorizontalRightEdge L -
          conreyHorizontalLeftEdge R L) ^ 2 + 1 / 4 := by
    positivity
  have hsquare :
      ‖z - conreyHorizontalJensenCenter L U‖ ^ 2 ≤
        (conreyHorizontalRightEdge L -
            conreyHorizontalLeftEdge R L) ^ 2 + 1 / 4 := by
    rw [Complex.sq_norm]
    simp [conreyHorizontalJensenCenter, Complex.normSq_apply]
    nlinarith
  rw [conreyHorizontalJensenInnerRadius]
  have hsqrt := Real.sq_sqrt hradicand
  nlinarith [norm_nonneg (z - conreyHorizontalJensenCenter L U),
    Real.sqrt_nonneg
      ((conreyHorizontalRightEdge L -
          conreyHorizontalLeftEdge R L) ^ 2 + 1 / 4)]

/-- The inner radius is strictly positive. -/
theorem conreyHorizontalJensenInnerRadius_pos (R L : ℝ) :
    0 < conreyHorizontalJensenInnerRadius R L := by
  rw [conreyHorizontalJensenInnerRadius, Real.sqrt_pos]
  nlinarith [sq_nonneg
    (conreyHorizontalRightEdge L - conreyHorizontalLeftEdge R L)]

private theorem two_le_log_of_forty_thousand_le
    {L : ℝ} (hL : 40000 ≤ L) :
    2 ≤ Real.log L := by
  have hLpos : 0 < L := by linarith
  have he2lt : Real.exp 2 < 9 := by
    have he := Real.exp_one_lt_three
    have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [he2]
    nlinarith [Real.exp_pos 1]
  have hLexp2 : Real.exp 2 ≤ L := he2lt.le.trans (by linarith)
  have hmono := Real.strictMonoOn_log.monotoneOn
    (Set.mem_Ioi.mpr (Real.exp_pos 2)) (Set.mem_Ioi.mpr hLpos) hLexp2
  simpa only [Real.log_exp] using hmono

/-- The inner disk has a genuine gap to the outer disk. -/
theorem conreyHorizontalJensenInnerRadius_lt_outerRadius
    {R L : ℝ} (hR0 : 0 ≤ R) (hRmax : R ≤ 6 / 5)
    (hL : 40000 ≤ L) :
    conreyHorizontalJensenInnerRadius R L <
      conreyHorizontalJensenOuterRadius L := by
  have hLpos : 0 < L := by linarith
  have hlogL := two_le_log_of_forty_thousand_le hL
  let A : ℝ := conreyHorizontalRightEdge L
  let sigma0 : ℝ := conreyHorizontalLeftEdge R L
  have hA : 4 ≤ A := by
    dsimp [A, conreyHorizontalRightEdge]
    linarith
  have hquot0 : 0 ≤ R / L := div_nonneg hR0 hLpos.le
  have hquotLe : R / L ≤ 3 / 100000 := by
    rw [div_le_iff₀ hLpos]
    nlinarith
  have hsigmaUpper : sigma0 ≤ 1 / 2 := by
    dsimp [sigma0, conreyHorizontalLeftEdge]
    linarith
  have hsigmaLower : 49 / 100 ≤ sigma0 := by
    dsimp [sigma0, conreyHorizontalLeftEdge]
    norm_num at hquotLe ⊢
    linarith
  have hsigmaSq : sigma0 ^ 2 ≤ 1 / 4 := by
    nlinarith [sq_nonneg sigma0, sq_nonneg (1 / 2 - sigma0)]
  have houterPos : 0 < A - 1 / 4 := by linarith
  have hradicand : 0 ≤ (A - sigma0) ^ 2 + 1 / 4 := by positivity
  have hsq : (A - sigma0) ^ 2 + 1 / 4 < (A - 1 / 4) ^ 2 := by
    nlinarith
  calc
    conreyHorizontalJensenInnerRadius R L =
        Real.sqrt ((A - sigma0) ^ 2 + 1 / 4) := by
      rfl
    _ < Real.sqrt ((A - 1 / 4) ^ 2) :=
      Real.sqrt_lt_sqrt hradicand hsq
    _ = A - 1 / 4 := Real.sqrt_sq houterPos.le
    _ = conreyHorizontalJensenOuterRadius L := by rfl

/-- Every point of the outer Jensen disk has real part at least `1/4`. -/
theorem quarter_le_re_of_mem_conreyHorizontalJensenOuterClosedBall
    {L U : ℝ} (_hL : 40000 ≤ L) {z : ℂ}
    (hz : z ∈ Metric.closedBall (conreyHorizontalJensenCenter L U)
      (conreyHorizontalJensenOuterRadius L)) :
    (1 / 4 : ℝ) ≤ z.re := by
  have hdist :
      ‖z - conreyHorizontalJensenCenter L U‖ ≤
        conreyHorizontalJensenOuterRadius L := by
    simpa [Metric.mem_closedBall, Complex.dist_eq] using hz
  have hre := Complex.abs_re_le_norm
    (z - conreyHorizontalJensenCenter L U)
  have hreAbs :
      |z.re - conreyHorizontalRightEdge L| ≤
        conreyHorizontalJensenOuterRadius L := by
    simpa [conreyHorizontalJensenCenter] using hre.trans hdist
  rw [abs_le] at hreAbs
  dsimp [conreyHorizontalJensenOuterRadius] at hreAbs
  linarith

/-- Starting the unit window above the moving edge keeps the disk away from
the pole `s=1`. -/
theorem ne_one_of_mem_conreyHorizontalJensenOuterClosedBall
    {L U : ℝ} (hL : 40000 ≤ L)
    (hU : conreyHorizontalRightEdge L + 1 ≤ U) {z : ℂ}
    (hz : z ∈ Metric.closedBall (conreyHorizontalJensenCenter L U)
      (conreyHorizontalJensenOuterRadius L)) :
    z ≠ 1 := by
  have hdist :
      ‖z - conreyHorizontalJensenCenter L U‖ ≤
        conreyHorizontalJensenOuterRadius L := by
    simpa [Metric.mem_closedBall, Complex.dist_eq] using hz
  have him := Complex.abs_im_le_norm
    (z - conreyHorizontalJensenCenter L U)
  have himAbs :
      |z.im - (U + 1 / 2)| ≤ conreyHorizontalJensenOuterRadius L := by
    simpa [conreyHorizontalJensenCenter] using him.trans hdist
  intro hzOne
  subst z
  simp only [one_im, zero_sub, abs_neg] at himAbs
  have hUpos : 0 ≤ U + 1 / 2 := by
    have hlogL := two_le_log_of_forty_thousand_le hL
    dsimp [conreyHorizontalRightEdge] at hU
    linarith
  rw [abs_of_nonneg hUpos] at himAbs
  dsimp [conreyHorizontalJensenOuterRadius] at himAbs
  linarith

/-- The actual explicit product `V₁ B` is analytic on the moving outer disk. -/
theorem analyticOnNhd_conreyExplicitMollifiedV1_horizontalJensenOuterClosedBall
    (Y : ℕ) (sigma0 L U : ℝ) (hL : 40000 ≤ L)
    (hU : conreyHorizontalRightEdge L + 1 ≤ U) :
    AnalyticOnNhd ℂ
      (conreyMollifiedDegreeOneV1
        (49 / 100) 0 (51 / 50) L Y sigma0 conreyExplicitP)
      (Metric.closedBall (conreyHorizontalJensenCenter L U)
        (conreyHorizontalJensenOuterRadius L)) := by
  intro z hz
  have hzre :=
    quarter_le_re_of_mem_conreyHorizontalJensenOuterClosedBall hL hz
  have hzne :=
    ne_one_of_mem_conreyHorizontalJensenOuterClosedBall hL hU hz
  unfold conreyMollifiedDegreeOneV1
  exact
    (analyticAt_conreyDegreeOneV1_of_re_pos_of_ne_one
      (g := (49 / 100 : ℝ)) (g0 := 0) (g1 := (51 / 50 : ℝ))
      (L := L) (by linarith) hzne).mul
    (analyticOnNhd_conreyMollifier Y sigma0 conreyExplicitP z (by simp))

end HardyTheorem
