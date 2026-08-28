import HardyTheorem.ConreyHorizontalJensenCount
import PrimeNumberTheorem.AnalyticBorel

/-!
# Buffered zero factorization for Conrey's horizontal edges

This module inserts a factorization disk strictly between the rectangle disk
and the growth disk.  The quantitative radius gap and the Jensen mass on that
larger factorization disk are the inputs for the later zero-removed Borel--
Caratheodory estimate.
-/

open Complex Set
open PrimeNumberTheorem.CarlsonZeroDensity

namespace HardyTheorem

/-- The absolute gap between the outer growth disk and the rectangle disk. -/
noncomputable def conreyHorizontalJensenRadiusGap (R L : ℝ) : ℝ :=
  conreyHorizontalJensenOuterRadius L -
    conreyHorizontalJensenInnerRadius R L

/-- Radius on which all zeros are extracted.  It retains one quarter of the
available gap outside the factorization disk. -/
noncomputable def conreyHorizontalJensenFactorRadius (R L : ℝ) : ℝ :=
  conreyHorizontalJensenInnerRadius R L +
    3 * conreyHorizontalJensenRadiusGap R L / 4

/-- Lower endpoint of the interval from which the zero-avoiding Borel circle
will be selected. -/
noncomputable def conreyHorizontalJensenGoodRadiusLower (R L : ℝ) : ℝ :=
  conreyHorizontalJensenInnerRadius R L +
    conreyHorizontalJensenRadiusGap R L / 4

/-- Upper endpoint of the interval from which the zero-avoiding Borel circle
will be selected. -/
noncomputable def conreyHorizontalJensenGoodRadiusUpper (R L : ℝ) : ℝ :=
  conreyHorizontalJensenInnerRadius R L +
    conreyHorizontalJensenRadiusGap R L / 2

/-- The moving Jensen disks have a uniform gap larger than `1/5`. -/
theorem one_fifth_lt_conreyHorizontalJensenRadiusGap
    {R L : ℝ} (hR0 : 0 ≤ R) (hRmax : R ≤ 6 / 5)
    (hL : 40000 ≤ L) :
    (1 / 5 : ℝ) < conreyHorizontalJensenRadiusGap R L := by
  have hLpos : 0 < L := by linarith
  have hlogL := two_le_log_of_forty_thousand_le hL
  let A : ℝ := conreyHorizontalRightEdge L
  let sigma0 : ℝ := conreyHorizontalLeftEdge R L
  let Q : ℝ := (A - sigma0) ^ 2 + 1 / 4
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
  have hx0 : 0 ≤ A - sigma0 := by linarith
  have hxLe : A - sigma0 ≤ A - 49 / 100 := by linarith
  have hxSq : (A - sigma0) ^ 2 ≤ (A - 49 / 100) ^ 2 :=
    (sq_le_sq₀ hx0 (by linarith)).2 hxLe
  have hQ0 : 0 ≤ Q := by
    dsimp [Q]
    positivity
  have htargetPos : 0 < A - 9 / 20 := by linarith
  have hQlt : Q < (A - 9 / 20) ^ 2 := by
    dsimp [Q]
    nlinarith
  have hsqrtSq : (Real.sqrt Q) ^ 2 = Q := Real.sq_sqrt hQ0
  have hsqrtLt : Real.sqrt Q < A - 9 / 20 := by
    nlinarith [Real.sqrt_nonneg Q]
  dsimp [conreyHorizontalJensenRadiusGap,
    conreyHorizontalJensenOuterRadius,
    conreyHorizontalJensenInnerRadius]
  change (1 / 5 : ℝ) < A - 1 / 4 - Real.sqrt Q
  linarith

/-- The same radius gap is strictly smaller than `1/4`. -/
theorem conreyHorizontalJensenRadiusGap_lt_one_fourth
    {R L : ℝ} (hR0 : 0 ≤ R) (_hRmax : R ≤ 6 / 5)
    (hL : 40000 ≤ L) :
    conreyHorizontalJensenRadiusGap R L < (1 / 4 : ℝ) := by
  have hLpos : 0 < L := by linarith
  have hlogL := two_le_log_of_forty_thousand_le hL
  let A : ℝ := conreyHorizontalRightEdge L
  let sigma0 : ℝ := conreyHorizontalLeftEdge R L
  let Q : ℝ := (A - sigma0) ^ 2 + 1 / 4
  have hA : 4 ≤ A := by
    dsimp [A, conreyHorizontalRightEdge]
    linarith
  have hquot0 : 0 ≤ R / L := div_nonneg hR0 hLpos.le
  have hsigmaUpper : sigma0 ≤ 1 / 2 := by
    dsimp [sigma0, conreyHorizontalLeftEdge]
    linarith
  have hx0 : 0 ≤ A - sigma0 := by linarith
  have hleft0 : 0 ≤ A - 1 / 2 := by linarith
  have hleftLe : A - 1 / 2 ≤ A - sigma0 := by linarith
  have hleftSq : (A - 1 / 2) ^ 2 ≤ (A - sigma0) ^ 2 :=
    (sq_le_sq₀ hleft0 hx0).2 hleftLe
  have hQ0 : 0 ≤ Q := by
    dsimp [Q]
    positivity
  have hltQ : (A - 1 / 2) ^ 2 < Q := by
    dsimp [Q]
    linarith
  have hsqrtSq : (Real.sqrt Q) ^ 2 = Q := Real.sq_sqrt hQ0
  have hleftLt : A - 1 / 2 < Real.sqrt Q := by
    nlinarith [Real.sqrt_nonneg Q]
  dsimp [conreyHorizontalJensenRadiusGap,
    conreyHorizontalJensenOuterRadius,
    conreyHorizontalJensenInnerRadius]
  change A - 1 / 4 - Real.sqrt Q < (1 / 4 : ℝ)
  linarith

/-- Strict nesting of the target disk, good-circle interval, factorization
disk, and outer growth disk. -/
theorem conreyHorizontalJensenBufferGeometry
    {R L : ℝ} (hR0 : 0 ≤ R) (hRmax : R ≤ 6 / 5)
    (hL : 40000 ≤ L) :
    conreyHorizontalJensenInnerRadius R L <
        conreyHorizontalJensenGoodRadiusLower R L ∧
      conreyHorizontalJensenGoodRadiusLower R L <
        conreyHorizontalJensenGoodRadiusUpper R L ∧
      conreyHorizontalJensenGoodRadiusUpper R L <
        conreyHorizontalJensenFactorRadius R L ∧
      conreyHorizontalJensenFactorRadius R L <
        conreyHorizontalJensenOuterRadius L := by
  have hgap := one_fifth_lt_conreyHorizontalJensenRadiusGap hR0 hRmax hL
  dsimp [conreyHorizontalJensenGoodRadiusLower,
    conreyHorizontalJensenGoodRadiusUpper,
    conreyHorizontalJensenFactorRadius,
    conreyHorizontalJensenRadiusGap] at *
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- Total analytic zero multiplicity on the buffered factorization disk. -/
noncomputable def conreyHorizontalJensenFactorZeroMass
    (Y : ℕ) (R L U : ℝ) : ℝ :=
  ∑ᶠ u,
    (MeromorphicOn.divisor (conreyHorizontalJensenProduct Y R L)
      (Metric.closedBall (conreyHorizontalJensenCenter L U)
        (conreyHorizontalJensenFactorRadius R L)) u : ℝ)

/-- Exact Jensen mass bound on the larger factorization disk. -/
theorem exists_conreyHorizontalJensenFactorZeroMass_le :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Y : ℕ} {R L U : ℝ}, 2 ≤ Y →
      (Y : ℝ) ≤ Real.exp L → 0 ≤ R → R ≤ 6 / 5 → 40000 ≤ L →
      conreyHorizontalRightEdge L + 1 ≤ U → U + 1 ≤ Real.exp L →
      conreyHorizontalJensenFactorZeroMass Y R L U ≤
        (Real.log (C * (Y : ℝ) *
            (conreyHorizontalJensenHeightBase L U) ^ 6 * (L + 2) ^ 2) +
          Real.log 6) /
            Real.log (conreyHorizontalJensenOuterRadius L /
              conreyHorizontalJensenFactorRadius R L) := by
  rcases
      exists_norm_conreyExplicitMollifiedV1_le_conreyHorizontalJensenOuterClosedBall with
    ⟨C, hC, hgrowth⟩
  refine ⟨C, hC, ?_⟩
  intro Y R L U hY hYtop hR0 hRmax hL hU hUtop
  let f : ℂ → ℂ := conreyHorizontalJensenProduct Y R L
  let c : ℂ := conreyHorizontalJensenCenter L U
  let b : ℝ := conreyHorizontalJensenFactorRadius R L
  let R₀ : ℝ := conreyHorizontalJensenOuterRadius L
  let H : ℝ := conreyHorizontalJensenHeightBase L U
  let M : ℝ := C * (Y : ℝ) * H ^ 6 * (L + 2) ^ 2
  have hLpos : 0 < L := by linarith
  have hsigma0 : conreyHorizontalLeftEdge R L ≤ 1 / 2 := by
    dsimp [conreyHorizontalLeftEdge]
    exact sub_le_self _ (div_nonneg hR0 hLpos.le)
  have hbuffer := conreyHorizontalJensenBufferGeometry hR0 hRmax hL
  have hb : 0 < b := by
    have hr := conreyHorizontalJensenInnerRadius_pos R L
    dsimp only [b]
    exact hr.trans (hbuffer.1.trans (hbuffer.2.1.trans hbuffer.2.2.1))
  have hbR : b < R₀ := by
    simpa only [b, R₀] using hbuffer.2.2.2
  have hR₀ : 0 < R₀ := hb.trans hbR
  have hanalytic : AnalyticOnNhd ℂ f (Metric.closedBall c R₀) := by
    simpa only [f, c, R₀, conreyHorizontalJensenProduct] using
      analyticOnNhd_conreyExplicitMollifiedV1_horizontalJensenOuterClosedBall
        Y (conreyHorizontalLeftEdge R L) L U hL hU
  have hH : 1 ≤ H := by
    simpa only [H] using one_le_conreyHorizontalJensenHeightBase hL hU
  have hYreal : 1 ≤ (Y : ℝ) := by exact_mod_cast (show 1 ≤ Y by omega)
  have hHpow : 1 ≤ H ^ 6 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hH 6
  have hLsq : 1 ≤ (L + 2) ^ 2 := by nlinarith [sq_nonneg (L + 2)]
  have hCY : 1 ≤ C * (Y : ℝ) := by
    simpa using mul_le_mul hC hYreal (by norm_num : (0 : ℝ) ≤ 1) (by linarith)
  have hCYH : 1 ≤ C * (Y : ℝ) * H ^ 6 := by
    simpa using mul_le_mul hCY hHpow (by norm_num : (0 : ℝ) ≤ 1)
      (mul_nonneg (by linarith) (by positivity))
  have hM : 1 ≤ M := by
    dsimp only [M]
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (C * (Y : ℝ) * H ^ 6) * (L + 2) ^ 2 :=
        mul_le_mul hCYH hLsq (by norm_num)
          (mul_nonneg (mul_nonneg (by linarith) (by positivity)) (by positivity))
  have hsphere : ∀ z ∈ Metric.sphere c R₀, ‖f z‖ ≤ M := by
    intro z hz
    have hzclosed : z ∈ Metric.closedBall c R₀ :=
      Metric.mem_closedBall.mpr (Metric.mem_sphere.mp hz).le
    simpa only [f, c, R₀, H, M, conreyHorizontalJensenProduct] using
      hgrowth hY hYtop hsigma0 hL hU hzclosed
  have htLower : 1 ≤ U + 1 / 2 := by
    have hlog : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
    dsimp [conreyHorizontalRightEdge] at hU
    linarith
  have htUpper : U + 1 / 2 ≤ Real.exp L := by linarith
  have hcenter : (1 / 6 : ℝ) ≤ ‖f c‖ := by
    have hraw := one_sixth_le_norm_conreyExplicitRightVerticalProduct
      hY hsigma0 hL htLower htUpper
    simpa [f, c, conreyHorizontalJensenProduct,
      conreyHorizontalJensenCenter, conreyHorizontalRightEdge,
      conreyExplicitRightVerticalProduct,
      conreyMollifiedDegreeOneV1] using hraw
  have hcircle :
      Real.circleAverage (Real.log ‖f ·‖) c R₀ ≤ Real.log M :=
    circleAverage_log_norm_le_log_of_norm_le hR₀ hanalytic.meromorphicOn hM hsphere
  have hjensen := jensen_inner_zero_multiplicity_le_log_div
    hb hbR hanalytic (by norm_num : (0 : ℝ) < 1 / 6) hcenter hcircle
  have hlocal := finsum_divisor_closedBall_eq_finsum_mem_of_le
    (f := f) (c := c) (b := b) (R := R₀) hbR.le hanalytic.meromorphicOn
  rw [← hlocal] at hjensen
  have hlogSix : Real.log (1 / 6 : ℝ) = -Real.log 6 := by
    rw [show (1 / 6 : ℝ) = (6 : ℝ)⁻¹ by ring, Real.log_inv]
  rw [hlogSix] at hjensen
  simpa [conreyHorizontalJensenFactorZeroMass, f, c, b, R₀, H, M,
    sub_neg_eq_add] using hjensen

end HardyTheorem
