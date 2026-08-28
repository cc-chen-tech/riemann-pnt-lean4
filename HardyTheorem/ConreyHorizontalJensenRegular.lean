import HardyTheorem.ConreyHorizontalJensenCount
import PrimeNumberTheorem.AnalyticBorel
import PrimeNumberTheorem.FiniteZeroGoodRadius

/-!
# Buffered zero factorization for Conrey's horizontal edges

This module inserts a factorization disk strictly between the rectangle disk
and the growth disk.  The quantitative radius gap and the Jensen mass on that
larger factorization disk are the inputs for the later zero-removed Borel--
Caratheodory estimate.
-/

open Complex Set MeromorphicOn
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

/-- The buffered factorization radius is large enough for the center divisor
estimate using `log b`. -/
theorem one_le_conreyHorizontalJensenFactorRadius
    {R L : ℝ} (hR0 : 0 ≤ R) (hRmax : R ≤ 6 / 5)
    (hL : 40000 ≤ L) :
    1 ≤ conreyHorizontalJensenFactorRadius R L := by
  have hlogL := two_le_log_of_forty_thousand_le hL
  have hgapUpper :=
    conreyHorizontalJensenRadiusGap_lt_one_fourth hR0 hRmax hL
  have hA : 4 ≤ conreyHorizontalRightEdge L := by
    dsimp [conreyHorizontalRightEdge]
    linarith
  dsimp [conreyHorizontalJensenFactorRadius,
    conreyHorizontalJensenRadiusGap,
    conreyHorizontalJensenOuterRadius] at *
  linarith

/-- The Borel geometry factor on every selected good circle has the explicit
`32 * outerRadius / gap^2` bound.  The leading `4` in the analytic Borel
theorem therefore produces the documented constant `128`. -/
theorem conreyHorizontalJensenFactorGeometry_le
    {R L q : ℝ} (hR0 : 0 ≤ R) (hRmax : R ≤ 6 / 5)
    (hL : 40000 ≤ L)
    (hq : q ∈ Set.Icc (conreyHorizontalJensenGoodRadiusLower R L)
      (conreyHorizontalJensenGoodRadiusUpper R L)) :
    (q + conreyHorizontalJensenInnerRadius R L) /
        (q - conreyHorizontalJensenInnerRadius R L) ^ 2 ≤
      32 * conreyHorizontalJensenOuterRadius L /
        conreyHorizontalJensenRadiusGap R L ^ 2 := by
  let r := conreyHorizontalJensenInnerRadius R L
  let R₀ := conreyHorizontalJensenOuterRadius L
  let gap := conreyHorizontalJensenRadiusGap R L
  have hbuffer := conreyHorizontalJensenBufferGeometry hR0 hRmax hL
  have hgapLower := one_fifth_lt_conreyHorizontalJensenRadiusGap hR0 hRmax hL
  have hgapPos : 0 < gap := by simpa [gap] using hgapLower.trans' (by norm_num)
  have hrPos : 0 < r := by
    simpa [r] using conreyHorizontalJensenInnerRadius_pos R L
  have hrR : r < R₀ := by
    simpa [r, R₀] using
      conreyHorizontalJensenInnerRadius_lt_outerRadius hR0 hRmax hL
  have hqLower : r + gap / 4 ≤ q := by
    simpa [r, gap, conreyHorizontalJensenGoodRadiusLower] using hq.1
  have hqUpper : q ≤ r + gap / 2 := by
    simpa [r, gap, conreyHorizontalJensenGoodRadiusUpper] using hq.2
  have hgapDef : gap = R₀ - r := by
    rfl
  have hqR : q ≤ R₀ := by linarith
  have hnum : q + r ≤ 2 * R₀ := by linarith
  have hqdiff : gap / 4 ≤ q - r := by linarith
  have hqdiffPos : 0 < q - r := by
    have : 0 < gap / 4 := by positivity
    linarith
  have hdenLower : gap ^ 2 / 16 ≤ (q - r) ^ 2 := by
    have hsquare := (sq_le_sq₀ (by positivity : 0 ≤ gap / 4)
      hqdiffPos.le).2 hqdiff
    nlinarith
  have hgapSqPos : 0 < gap ^ 2 := sq_pos_of_pos hgapPos
  have hR₀Pos : 0 < R₀ := hrPos.trans hrR
  have hcoefNonneg : 0 ≤ 32 * R₀ / gap ^ 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hdenLower hcoefNonneg
  have hnormalize :
      (32 * R₀ / gap ^ 2) * (gap ^ 2 / 16) = 2 * R₀ := by
    field_simp
    ring
  change (q + r) / (q - r) ^ 2 ≤ 32 * R₀ / gap ^ 2
  apply (div_le_iff₀ (sq_pos_of_pos hqdiffPos)).2
  calc
    q + r ≤ 2 * R₀ := hnum
    _ = (32 * R₀ / gap ^ 2) * (gap ^ 2 / 16) := hnormalize.symm
    _ ≤ (32 * R₀ / gap ^ 2) * (q - r) ^ 2 := hscaled

/-- Total analytic zero multiplicity on the buffered factorization disk. -/
noncomputable def conreyHorizontalJensenFactorZeroMass
    (Y : ℕ) (R L U : ℝ) : ℝ :=
  ∑ᶠ u,
    (MeromorphicOn.divisor (conreyHorizontalJensenProduct Y R L)
      (Metric.closedBall (conreyHorizontalJensenCenter L U)
        (conreyHorizontalJensenFactorRadius R L)) u : ℝ)

/-- Distinct zeros in the buffered factorization disk. -/
noncomputable def conreyHorizontalJensenFactorZeroSupport
    (Y : ℕ) (R L U : ℝ) : Finset ℂ :=
  ((MeromorphicOn.divisor (conreyHorizontalJensenProduct Y R L)
      (Metric.closedBall (conreyHorizontalJensenCenter L U)
        (conreyHorizontalJensenFactorRadius R L))).finiteSupport
    (isCompact_closedBall (conreyHorizontalJensenCenter L U)
      (conreyHorizontalJensenFactorRadius R L))).toFinset

/-- Quantitative separation furnished by the good-circle interval. -/
noncomputable def conreyHorizontalJensenFactorDiskSeparation
    (Y : ℕ) (R L U : ℝ) : ℝ :=
  (conreyHorizontalJensenGoodRadiusUpper R L -
      conreyHorizontalJensenGoodRadiusLower R L) /
    (4 * ((((conreyHorizontalJensenFactorZeroSupport Y R L U).image
      (dist (conreyHorizontalJensenCenter L U))).card : ℝ) + 1))

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

/-- The number of distinct factor-disk zeros is no larger than their total
analytic multiplicity. -/
theorem card_conreyHorizontalJensenFactorZeroSupport_le_mass
    {Y : ℕ} {R L U : ℝ} (hR0 : 0 ≤ R) (hRmax : R ≤ 6 / 5)
    (hL : 40000 ≤ L) (hU : conreyHorizontalRightEdge L + 1 ≤ U) :
    ((conreyHorizontalJensenFactorZeroSupport Y R L U).card : ℝ) ≤
      conreyHorizontalJensenFactorZeroMass Y R L U := by
  have hbuffer := conreyHorizontalJensenBufferGeometry hR0 hRmax hL
  have hanalyticOuter :=
    analyticOnNhd_conreyExplicitMollifiedV1_horizontalJensenOuterClosedBall
      Y (conreyHorizontalLeftEdge R L) L U hL hU
  have hanalyticFactor := hanalyticOuter.mono
    (Metric.closedBall_subset_closedBall hbuffer.2.2.2.le)
  simpa [conreyHorizontalJensenFactorZeroSupport,
    conreyHorizontalJensenFactorZeroMass,
    conreyHorizontalJensenProduct] using
      card_divisor_support_le_finsum_mass hanalyticFactor

/-- Any majorant for the factor-disk divisor mass gives a concrete lower
bound for the radial good-circle separation. -/
theorem conreyHorizontalJensenFactorDiskSeparation_lower_of_mass_le
    {Y : ℕ} {R L U J : ℝ} (hR0 : 0 ≤ R) (hRmax : R ≤ 6 / 5)
    (hL : 40000 ≤ L) (hU : conreyHorizontalRightEdge L + 1 ≤ U)
    (hmass : conreyHorizontalJensenFactorZeroMass Y R L U ≤ J) :
    0 < conreyHorizontalJensenRadiusGap R L / (16 * (J + 1)) ∧
      conreyHorizontalJensenRadiusGap R L / (16 * (J + 1)) ≤
        conreyHorizontalJensenFactorDiskSeparation Y R L U := by
  classical
  let c : ℂ := conreyHorizontalJensenCenter L U
  let b : ℝ := conreyHorizontalJensenFactorRadius R L
  let D := MeromorphicOn.divisor (conreyHorizontalJensenProduct Y R L)
    (Metric.closedBall c b)
  let zeros := conreyHorizontalJensenFactorZeroSupport Y R L U
  let radialCard : ℝ := (((zeros.image (dist c)).card : ℕ) : ℝ)
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
  have hmassNonneg : 0 ≤ conreyHorizontalJensenFactorZeroMass Y R L U := by
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
  have hradialNat : (zeros.image (dist c)).card ≤ zeros.card :=
    Finset.card_image_le
  have hradialSupport : radialCard ≤ (zeros.card : ℝ) := by
    dsimp [radialCard]
    exact_mod_cast hradialNat
  have hradialJ : radialCard ≤ J :=
    hradialSupport.trans (hsupportMass.trans hmass)
  have hgapPos := one_fifth_lt_conreyHorizontalJensenRadiusGap hR0 hRmax hL
  have hgap0 : 0 < conreyHorizontalJensenRadiusGap R L := by linarith
  have hsmallDenPos : 0 < 16 * (radialCard + 1) := by positivity
  have hlargeDenPos : 0 < 16 * (J + 1) := by positivity
  have hdenLe : 16 * (radialCard + 1) ≤ 16 * (J + 1) := by
    nlinarith
  have hrecip : 1 / (16 * (J + 1)) ≤
      1 / (16 * (radialCard + 1)) :=
    one_div_le_one_div_of_le hsmallDenPos hdenLe
  have hsepEq : conreyHorizontalJensenFactorDiskSeparation Y R L U =
      conreyHorizontalJensenRadiusGap R L /
        (16 * (radialCard + 1)) := by
    dsimp only [conreyHorizontalJensenFactorDiskSeparation, zeros, c,
      conreyHorizontalJensenGoodRadiusUpper,
      conreyHorizontalJensenGoodRadiusLower]
    have hk : radialCard + 1 ≠ 0 := ne_of_gt (by positivity)
    field_simp [hk]
    ring
  refine ⟨div_pos hgap0 (by positivity), ?_⟩
  rw [hsepEq]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have hrecip' : (16 * (J + 1))⁻¹ ≤
      (16 * (radialCard + 1))⁻¹ := by
    simpa [one_div] using hrecip
  exact mul_le_mul_of_nonneg_left hrecip' hgap0.le

private theorem analyticOrderAt_conreyHorizontalJensenProduct_factor_ne_top
    {Y : ℕ} {R L U : ℝ} (hY : 2 ≤ Y) (hR0 : 0 ≤ R)
    (hRmax : R ≤ 6 / 5) (hL : 40000 ≤ L)
    (hU : conreyHorizontalRightEdge L + 1 ≤ U) {z : ℂ}
    (hz : z ∈ Metric.closedBall (conreyHorizontalJensenCenter L U)
      (conreyHorizontalJensenFactorRadius R L)) :
    analyticOrderAt (conreyHorizontalJensenProduct Y R L) z ≠ ⊤ := by
  have hbuffer := conreyHorizontalJensenBufferGeometry hR0 hRmax hL
  have hzOuter : z ∈ Metric.closedBall (conreyHorizontalJensenCenter L U)
      (conreyHorizontalJensenOuterRadius L) :=
    Metric.closedBall_subset_closedBall hbuffer.2.2.2.le hz
  have hzre :=
    quarter_le_re_of_mem_conreyHorizontalJensenOuterClosedBall hL hzOuter
  have hzne :=
    ne_one_of_mem_conreyHorizontalJensenOuterClosedBall hL hU hzOuter
  have hV := analyticAt_conreyDegreeOneV1_of_re_pos_of_ne_one
    (g := (49 / 100 : ℝ)) (g0 := 0) (g1 := (51 / 50 : ℝ))
    (L := L) (by linarith) hzne
  have hB := analyticOnNhd_conreyMollifier Y
    (conreyHorizontalLeftEdge R L) conreyExplicitP z (by simp)
  have hVfinite := analyticOrderAt_conreyDegreeOneV1_ne_top_of_g_ne_zero
    (g0 := (0 : ℝ)) (g1 := (51 / 50 : ℝ)) (L := L)
    (by norm_num : (49 / 100 : ℝ) ≠ 0) (by linarith) hzne
  have hP1 : conreyExplicitP 1 = 1 := by
    norm_num [conreyExplicitP]
  have hBfinite := analyticOrderAt_conreyMollifier_ne_top
    hY hP1 (conreyHorizontalLeftEdge R L) z
  unfold conreyHorizontalJensenProduct conreyMollifiedDegreeOneV1
  change analyticOrderAt
    (conreyDegreeOneV1 (49 / 100) 0 (51 / 50) L *
      conreyMollifier Y (conreyHorizontalLeftEdge R L) conreyExplicitP) z ≠ ⊤
  rw [analyticOrderAt_mul hV hB]
  intro htop
  rw [ENat.add_eq_top] at htop
  exact htop.elim hVfinite hBfinite

/-- On the factorization disk, finite divisor support is exactly the zero set
of the actual Conrey product. -/
theorem mem_conreyHorizontalJensenFactorZeroSupport_iff_zero
    {Y : ℕ} {R L U : ℝ} (hY : 2 ≤ Y) (hR0 : 0 ≤ R)
    (hRmax : R ≤ 6 / 5) (hL : 40000 ≤ L)
    (hU : conreyHorizontalRightEdge L + 1 ≤ U) {z : ℂ}
    (hz : z ∈ Metric.closedBall (conreyHorizontalJensenCenter L U)
      (conreyHorizontalJensenFactorRadius R L)) :
    z ∈ conreyHorizontalJensenFactorZeroSupport Y R L U ↔
      conreyHorizontalJensenProduct Y R L z = 0 := by
  classical
  let c : ℂ := conreyHorizontalJensenCenter L U
  let b : ℝ := conreyHorizontalJensenFactorRadius R L
  let D := MeromorphicOn.divisor (conreyHorizontalJensenProduct Y R L)
    (Metric.closedBall c b)
  have hbuffer := conreyHorizontalJensenBufferGeometry hR0 hRmax hL
  have hanalyticOuter :=
    analyticOnNhd_conreyExplicitMollifiedV1_horizontalJensenOuterClosedBall
      Y (conreyHorizontalLeftEdge R L) L U hL hU
  have hanalytic : AnalyticOnNhd ℂ (conreyHorizontalJensenProduct Y R L)
      (Metric.closedBall c b) := by
    simpa [c, b, conreyHorizontalJensenProduct] using
      hanalyticOuter.mono
        (Metric.closedBall_subset_closedBall hbuffer.2.2.2.le)
  have horder := analyticOrderAt_conreyHorizontalJensenProduct_factor_ne_top
    hY hR0 hRmax hL hU (by simpa [c, b] using hz)
  have hdivisor : D z =
      (analyticOrderNatAt (conreyHorizontalJensenProduct Y R L) z : ℤ) := by
    rw [MeromorphicOn.divisor_apply hanalytic.meromorphicOn
      (by simpa [c, b] using hz),
      (hanalytic z (by simpa [c, b] using hz)).meromorphicOrderAt_eq]
    have hcast := Nat.cast_analyticOrderNatAt horder
    rw [← hcast]
    simp
  have hzAnalytic : AnalyticAt ℂ (conreyHorizontalJensenProduct Y R L) z :=
    hanalytic z (by simpa [c, b] using hz)
  have hnatCast := Nat.cast_analyticOrderNatAt horder
  rw [conreyHorizontalJensenFactorZeroSupport]
  rw [(D.finiteSupport (isCompact_closedBall c b)).mem_toFinset]
  simp only [Function.mem_support]
  rw [show MeromorphicOn.divisor (conreyHorizontalJensenProduct Y R L)
      (Metric.closedBall (conreyHorizontalJensenCenter L U)
        (conreyHorizontalJensenFactorRadius R L)) z = D z by rfl,
    hdivisor, Int.ofNat_ne_zero]
  constructor
  · intro hnat
    apply hzAnalytic.analyticOrderAt_ne_zero.mp
    intro hzero
    have hcastZero :
        (analyticOrderNatAt (conreyHorizontalJensenProduct Y R L) z : ℕ∞) = 0 :=
      hnatCast.trans hzero
    exact hnat (by simpa using hcastZero)
  · intro hzero hnatZero
    have horderZero :
        analyticOrderAt (conreyHorizontalJensenProduct Y R L) z = 0 := by
      rw [← hnatCast, hnatZero]
      rfl
    exact (hzAnalytic.analyticOrderAt_eq_zero.mp horderZero) hzero

/-- A circle in the buffered interval avoids every factor-disk zero with the
exact finite-set separation used later in the Borel estimate. -/
theorem exists_conreyHorizontalJensenGoodFactorCircle
    {Y : ℕ} {R L U : ℝ} (hY : 2 ≤ Y) (hR0 : 0 ≤ R)
    (hRmax : R ≤ 6 / 5) (hL : 40000 ≤ L)
    (hU : conreyHorizontalRightEdge L + 1 ≤ U) :
    ∃ q : ℝ,
      0 < q ∧ q ∈ Set.Icc
        (conreyHorizontalJensenGoodRadiusLower R L)
        (conreyHorizontalJensenGoodRadiusUpper R L) ∧
      (∀ z ∈ Metric.sphere (conreyHorizontalJensenCenter L U) q,
        ∀ rho ∈ conreyHorizontalJensenFactorZeroSupport Y R L U,
          conreyHorizontalJensenFactorDiskSeparation Y R L U ≤ dist z rho) ∧
      (∀ z ∈ Metric.sphere (conreyHorizontalJensenCenter L U) q,
        z ∈ Metric.closedBall (conreyHorizontalJensenCenter L U)
          (conreyHorizontalJensenFactorRadius R L)) ∧
      ∀ z ∈ Metric.sphere (conreyHorizontalJensenCenter L U) q,
        conreyHorizontalJensenProduct Y R L z ≠ 0 := by
  let c : ℂ := conreyHorizontalJensenCenter L U
  let zeros := conreyHorizontalJensenFactorZeroSupport Y R L U
  have hbuffer := conreyHorizontalJensenBufferGeometry hR0 hRmax hL
  have hcover : ∀ z ∈ Metric.closedBall c
      (conreyHorizontalJensenFactorRadius R L),
      conreyHorizontalJensenProduct Y R L z = 0 → z ∈ zeros := by
    intro z hz hzero
    exact (mem_conreyHorizontalJensenFactorZeroSupport_iff_zero
      hY hR0 hRmax hL hU (by simpa [c] using hz)).2 hzero
  simpa [c, zeros, conreyHorizontalJensenFactorDiskSeparation] using
    (PrimeNumberTheorem.exists_good_radius_avoiding_covered_finset_zeros
      (f := conreyHorizontalJensenProduct Y R L) zeros c
      (conreyHorizontalJensenInnerRadius_pos R L |>.trans hbuffer.1)
      hbuffer.2.1 hbuffer.2.2.1 hcover)

/-- Logarithmic norm majorant for the extracted nonzero factor on its selected
good circle. -/
noncomputable def conreyHorizontalJensenFactorCircleLogUpper
    (C : ℝ) (Y : ℕ) (R L U : ℝ) : ℝ :=
  Real.log (C * (Y : ℝ) *
      (conreyHorizontalJensenHeightBase L U) ^ 6 * (L + 2) ^ 2) -
    Real.log (conreyHorizontalJensenFactorDiskSeparation Y R L U) *
      conreyHorizontalJensenFactorZeroMass Y R L U

/-- Center lower bound for the extracted nonzero factor. -/
noncomputable def conreyHorizontalJensenFactorCenterLogLower
    (Y : ℕ) (R L U : ℝ) : ℝ :=
  -Real.log 6 -
    Real.log (conreyHorizontalJensenFactorRadius R L) *
      conreyHorizontalJensenFactorZeroMass Y R L U

/-- Explicit logarithmic-variation majorant after replacing the actual zero
mass by `J` and the actual good-circle separation by `gap/(16*(J+1))`. -/
noncomputable def conreyHorizontalJensenFactorLogVariationMajorant
    (C : ℝ) (Y : ℕ) (R L U J : ℝ) : ℝ :=
  Real.log (C * (Y : ℝ) *
      (conreyHorizontalJensenHeightBase L U) ^ 6 * (L + 2) ^ 2) +
    Real.log 6 +
    (Real.log (conreyHorizontalJensenFactorRadius R L) -
      Real.log (conreyHorizontalJensenRadiusGap R L / (16 * (J + 1)))) * J

/-- The actual center-to-circle logarithmic variation is controlled by the
explicit mass/separation majorant.  All sign conditions needed when replacing
the mass and the logarithm of the separation are kept visible. -/
theorem conreyHorizontalJensenFactorLogVariation_le_of_mass_le
    {C J : ℝ} {Y : ℕ} {R L U : ℝ}
    (hR0 : 0 ≤ R) (hRmax : R ≤ 6 / 5) (hL : 40000 ≤ L)
    (hU : conreyHorizontalRightEdge L + 1 ≤ U)
    (hmass : conreyHorizontalJensenFactorZeroMass Y R L U ≤ J) :
    conreyHorizontalJensenFactorCircleLogUpper C Y R L U -
        conreyHorizontalJensenFactorCenterLogLower Y R L U ≤
      conreyHorizontalJensenFactorLogVariationMajorant C Y R L U J := by
  let m := conreyHorizontalJensenFactorZeroMass Y R L U
  let sep := conreyHorizontalJensenFactorDiskSeparation Y R L U
  let delta := conreyHorizontalJensenRadiusGap R L / (16 * (J + 1))
  let b := conreyHorizontalJensenFactorRadius R L
  have hbuffer := conreyHorizontalJensenBufferGeometry hR0 hRmax hL
  have hanalyticOuter :=
    analyticOnNhd_conreyExplicitMollifiedV1_horizontalJensenOuterClosedBall
      Y (conreyHorizontalLeftEdge R L) L U hL hU
  have hanalyticFactor := hanalyticOuter.mono
    (Metric.closedBall_subset_closedBall hbuffer.2.2.2.le)
  have hDnonneg := hanalyticFactor.divisor_nonneg
  have hmNonneg : 0 ≤ m := by
    change 0 ≤ ∑ᶠ u,
      (MeromorphicOn.divisor (conreyHorizontalJensenProduct Y R L)
        (Metric.closedBall (conreyHorizontalJensenCenter L U)
          (conreyHorizontalJensenFactorRadius R L)) u : ℝ)
    apply finsum_nonneg
    intro u
    exact_mod_cast hDnonneg u
  have hJNonneg : 0 ≤ J := hmNonneg.trans hmass
  have hsepMajor := conreyHorizontalJensenFactorDiskSeparation_lower_of_mass_le
    (Y := Y) (U := U) hR0 hRmax hL hU hmass
  have hdeltaPos : 0 < delta := by simpa [delta] using hsepMajor.1
  have hdeltaSep : delta ≤ sep := by simpa [delta, sep] using hsepMajor.2
  have hlogDeltaSep : Real.log delta ≤ Real.log sep :=
    Real.log_le_log hdeltaPos hdeltaSep
  have hgapUpper :=
    conreyHorizontalJensenRadiusGap_lt_one_fourth hR0 hRmax hL
  have hdenPos : 0 < 16 * (J + 1) := by positivity
  have hdeltaLeOne : delta ≤ 1 := by
    dsimp [delta]
    apply (div_le_iff₀ hdenPos).2
    nlinarith
  have hlogDeltaNonpos : Real.log delta ≤ 0 :=
    Real.log_nonpos hdeltaPos.le hdeltaLeOne
  have hbOne : 1 ≤ b := by
    simpa [b] using one_le_conreyHorizontalJensenFactorRadius hR0 hRmax hL
  have hlogBNonneg : 0 ≤ Real.log b := Real.log_nonneg hbOne
  have hcoeffLe :
      -Real.log sep + Real.log b ≤ -Real.log delta + Real.log b := by
    linarith
  have hcoeffNonneg : 0 ≤ -Real.log delta + Real.log b := by
    linarith
  have hweighted :
      (-Real.log sep + Real.log b) * m ≤
        (-Real.log delta + Real.log b) * J := by
    exact (mul_le_mul_of_nonneg_right hcoeffLe hmNonneg).trans
      (mul_le_mul_of_nonneg_left hmass hcoeffNonneg)
  dsimp [conreyHorizontalJensenFactorCircleLogUpper,
    conreyHorizontalJensenFactorCenterLogLower,
    conreyHorizontalJensenFactorLogVariationMajorant,
    m, sep, delta, b]
  linarith

/-- One good circle and one extracted factor simultaneously give the center
lower bound, circle upper bound, logarithmic-derivative decomposition, and the
Borel--Caratheodory estimate throughout the rectangle disk. -/
theorem exists_conreyHorizontalJensenGoodFactor_logDeriv_le :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Y : ℕ} {R L U : ℝ}, 2 ≤ Y →
      (Y : ℝ) ≤ Real.exp L → 0 ≤ R → R ≤ 6 / 5 → 40000 ≤ L →
      conreyHorizontalRightEdge L + 1 ≤ U → U + 1 ≤ Real.exp L →
      ∃ q : ℝ, ∃ g : ℂ → ℂ,
        q ∈ Set.Icc (conreyHorizontalJensenGoodRadiusLower R L)
          (conreyHorizontalJensenGoodRadiusUpper R L) ∧
        AnalyticOnNhd ℂ g
          (Metric.closedBall (conreyHorizontalJensenCenter L U)
            (conreyHorizontalJensenFactorRadius R L)) ∧
        (∀ u : (Metric.closedBall (conreyHorizontalJensenCenter L U)
            (conreyHorizontalJensenFactorRadius R L) : Set ℂ), g u ≠ 0) ∧
        conreyHorizontalJensenFactorCenterLogLower Y R L U ≤
          Real.log ‖g (conreyHorizontalJensenCenter L U)‖ ∧
        (∀ z ∈ Metric.sphere (conreyHorizontalJensenCenter L U) q,
          Real.log ‖g z‖ ≤
            conreyHorizontalJensenFactorCircleLogUpper C Y R L U) ∧
        (∀ z ∈ Metric.ball (conreyHorizontalJensenCenter L U)
            (conreyHorizontalJensenFactorRadius R L),
          conreyHorizontalJensenProduct Y R L z ≠ 0 →
            logDeriv (conreyHorizontalJensenProduct Y R L) z =
              (∑ᶠ u,
                (MeromorphicOn.divisor
                  (conreyHorizontalJensenProduct Y R L)
                  (Metric.closedBall (conreyHorizontalJensenCenter L U)
                    (conreyHorizontalJensenFactorRadius R L)) u : ℂ) *
                  (z - u)⁻¹) + logDeriv g z) ∧
        ∀ z ∈ Metric.closedBall (conreyHorizontalJensenCenter L U)
            (conreyHorizontalJensenInnerRadius R L),
          ‖logDeriv g z‖ ≤
            4 * max
                (conreyHorizontalJensenFactorCircleLogUpper C Y R L U -
                  conreyHorizontalJensenFactorCenterLogLower Y R L U) 1 *
              (q + conreyHorizontalJensenInnerRadius R L) /
              (q - conreyHorizontalJensenInnerRadius R L) ^ 2 := by
  rcases
      exists_norm_conreyExplicitMollifiedV1_le_conreyHorizontalJensenOuterClosedBall with
    ⟨C, hC, hgrowth⟩
  refine ⟨C, hC, ?_⟩
  intro Y R L U hY hYtop hR0 hRmax hL hU hUtop
  let f : ℂ → ℂ := conreyHorizontalJensenProduct Y R L
  let c : ℂ := conreyHorizontalJensenCenter L U
  let d : ℝ := conreyHorizontalJensenInnerRadius R L
  let b : ℝ := conreyHorizontalJensenFactorRadius R L
  let H : ℝ := conreyHorizontalJensenHeightBase L U
  let M : ℝ := C * (Y : ℝ) * H ^ 6 * (L + 2) ^ 2
  let D := MeromorphicOn.divisor f (Metric.closedBall c b)
  let zeros := conreyHorizontalJensenFactorZeroSupport Y R L U
  let delta := conreyHorizontalJensenFactorDiskSeparation Y R L U
  have hLpos : 0 < L := by linarith
  have hsigma0 : conreyHorizontalLeftEdge R L ≤ 1 / 2 := by
    dsimp [conreyHorizontalLeftEdge]
    exact sub_le_self _ (div_nonneg hR0 hLpos.le)
  have hbuffer := conreyHorizontalJensenBufferGeometry hR0 hRmax hL
  have hdb : d < b := by
    dsimp only [d, b]
    exact hbuffer.1.trans (hbuffer.2.1.trans hbuffer.2.2.1)
  have hbOuter : b < conreyHorizontalJensenOuterRadius L := by
    simpa only [b] using hbuffer.2.2.2
  have hanalyticOuter :=
    analyticOnNhd_conreyExplicitMollifiedV1_horizontalJensenOuterClosedBall
      Y (conreyHorizontalLeftEdge R L) L U hL hU
  have hanalyticFactor : AnalyticOnNhd ℂ f (Metric.closedBall c b) := by
    simpa [f, c, b, conreyHorizontalJensenProduct] using
      hanalyticOuter.mono
        (Metric.closedBall_subset_closedBall hbOuter.le)
  have hnotop : ∀ u : (Metric.closedBall c b : Set ℂ),
      meromorphicOrderAt f u ≠ ⊤ := by
    intro u
    rw [(hanalyticFactor u u.property).meromorphicOrderAt_eq]
    intro htop
    have hu : (u : ℂ) ∈ Metric.closedBall
        (conreyHorizontalJensenCenter L U)
          (conreyHorizontalJensenFactorRadius R L) := by
      simpa only [c, b] using u.property
    apply analyticOrderAt_conreyHorizontalJensenProduct_factor_ne_top
      hY hR0 hRmax hL hU hu
    exact ENat.map_eq_top_iff.mp htop
  rcases exists_conreyHorizontalJensenGoodFactorCircle
      hY hR0 hRmax hL hU with
    ⟨q, hqpos, hqrange, hsep, hsphereFactor, hsphereNe⟩
  have hqb : q < b := hqrange.2.trans_lt hbuffer.2.2.1
  rcases
      exists_analytic_nonzero_factor_log_norm_logDeriv_pointwise_of_ne_zero
      (f := f) (c := c) (r := q) (R := b) hqb hanalyticFactor hnotop with
    ⟨g, hg, hgne, hfactor, hld⟩
  have hDfinite : D.support.Finite :=
    D.finiteSupport (isCompact_closedBall c b)
  have hDnonneg : 0 ≤ D := hanalyticFactor.divisor_nonneg
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
  have hclosedNorm : ∀ z ∈ Metric.closedBall c
      (conreyHorizontalJensenOuterRadius L), ‖f z‖ ≤ M := by
    intro z hz
    simpa [f, c, H, M, conreyHorizontalJensenProduct] using
      hgrowth hY hYtop hsigma0 hL hU hz
  have htLower : 1 ≤ U + 1 / 2 := by
    have hlog : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
    dsimp [conreyHorizontalRightEdge] at hU
    linarith
  have htUpper : U + 1 / 2 ≤ Real.exp L := by linarith
  have hcenterNorm : (1 / 6 : ℝ) ≤ ‖f c‖ := by
    have hraw := one_sixth_le_norm_conreyExplicitRightVerticalProduct
      hY hsigma0 hL htLower htUpper
    simpa [f, c, conreyHorizontalJensenProduct,
      conreyHorizontalJensenCenter, conreyHorizontalRightEdge,
      conreyExplicitRightVerticalProduct,
      conreyMollifiedDegreeOneV1] using hraw
  have hcenterNe : f c ≠ 0 :=
    norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1 / 6).trans_le hcenterNorm)
  have hcenterEq := hfactor c (by simp [hqpos.le]) hcenterNe
  have hsum := finsum_divisor_mul_log_norm_center_sub_le_log_mul_mass
    (f := f) (c := c) (b := b)
    (by
      simpa only [b] using
        (one_le_conreyHorizontalJensenFactorRadius hR0 hRmax hL))
    hanalyticFactor hcenterNe
  have hcenterF : -Real.log 6 ≤ Real.log ‖f c‖ := by
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 6) hcenterNorm
    rw [show Real.log (1 / 6 : ℝ) = -Real.log 6 by
      rw [show (1 / 6 : ℝ) = (6 : ℝ)⁻¹ by ring, Real.log_inv]] at hlog
    exact hlog
  have hcenterG : conreyHorizontalJensenFactorCenterLogLower Y R L U ≤
      Real.log ‖g c‖ := by
    change -Real.log 6 - Real.log b * (∑ᶠ u, (D u : ℝ)) ≤
      Real.log ‖g c‖
    simpa [D, f, c, b, conreyHorizontalJensenFactorCenterLogLower,
      conreyHorizontalJensenFactorZeroMass] using (show
        -Real.log 6 - Real.log b * (∑ᶠ u, (D u : ℝ)) ≤
          Real.log ‖g c‖ by linarith)
  have hdelta : 0 < delta := by
    dsimp [delta, conreyHorizontalJensenFactorDiskSeparation, zeros, c]
    have hwidth : 0 < conreyHorizontalJensenGoodRadiusUpper R L -
        conreyHorizontalJensenGoodRadiusLower R L := sub_pos.mpr hbuffer.2.1
    positivity
  have hsphereG : ∀ z ∈ Metric.sphere c q,
      Real.log ‖g z‖ ≤
        conreyHorizontalJensenFactorCircleLogUpper C Y R L U := by
    intro z hz
    have hzFactor : z ∈ Metric.closedBall c b :=
      hsphereFactor z (by simpa [c] using hz)
    have hzOuter : z ∈ Metric.closedBall c
        (conreyHorizontalJensenOuterRadius L) :=
      Metric.closedBall_subset_closedBall hbOuter.le hzFactor
    have hfz : f z ≠ 0 := hsphereNe z (by simpa [f, c] using hz)
    have hfactorZ := hfactor z
      (Metric.sphere_subset_closedBall (by simpa [c] using hz)) hfz
    have hsepSupport : ∀ u ∈ D.support, delta ≤ ‖z - u‖ := by
      intro u hu
      have huZeros : u ∈ zeros := by
        dsimp [zeros, conreyHorizontalJensenFactorZeroSupport]
        exact hDfinite.mem_toFinset.mpr hu
      have h := hsep z (by simpa [c] using hz) u
        (by simpa [zeros] using huZeros)
      simpa [delta, c, Complex.dist_eq] using h
    have hsumLower :=
      ZeroFreeRegion.log_mul_finsum_le_finsum_mul_log_norm_sub_of_finiteSupport
        hDfinite (fun u => hDnonneg u) hdelta hsepSupport
    have hlogF : Real.log ‖f z‖ ≤ Real.log M :=
      Real.log_le_log (norm_pos_iff.mpr hfz) (hclosedNorm z hzOuter)
    change Real.log ‖g z‖ ≤
      Real.log M - Real.log delta * (∑ᶠ u, (D u : ℝ))
    simpa [D, f, c, H, M, delta,
      conreyHorizontalJensenFactorCircleLogUpper,
      conreyHorizontalJensenFactorZeroMass] using (show
        Real.log ‖g z‖ ≤
          Real.log M - Real.log delta * (∑ᶠ u, (D u : ℝ)) by
      linarith)
  have hgCircle : AnalyticOnNhd ℂ g (Metric.closedBall c q) :=
    hg.mono (Metric.closedBall_subset_closedBall hqb.le)
  have hgneCircle : ∀ z ∈ Metric.closedBall c q, g z ≠ 0 := by
    intro z hz
    exact hgne ⟨z, Metric.closedBall_subset_closedBall hqb.le hz⟩
  have hdq : d < q := by
    dsimp only [d]
    exact hbuffer.1.trans_le hqrange.1
  have hregular : ∀ z ∈ Metric.closedBall c d,
      ‖logDeriv g z‖ ≤
        4 * max
            (conreyHorizontalJensenFactorCircleLogUpper C Y R L U -
              conreyHorizontalJensenFactorCenterLogLower Y R L U) 1 *
          (q + d) / (q - d) ^ 2 := by
    intro z hz
    exact
      ZeroFreeRegion.norm_logDeriv_le_four_mul_max_sub_mul_add_div_sq_of_sphere_log_norm_le_of_center_lower
        hqpos (conreyHorizontalJensenInnerRadius_pos R L).le hdq
        hgCircle hgneCircle hcenterG hsphereG hz
  refine ⟨q, g, hqrange, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [c, b] using hg
  · simpa [c, b] using hgne
  · simpa [c] using hcenterG
  · intro z hz
    exact hsphereG z (by simpa [c] using hz)
  · intro z hz hfz
    exact hld z (by simpa [f, c, b] using hz) hfz
  · intro z hz
    exact hregular z (by simpa [c, d] using hz)

/-- The same extracted factor admits a Borel bound with every explicit
majorant `J` for the complete factor-disk zero mass. -/
theorem exists_conreyHorizontalJensenGoodFactor_logDeriv_le_majorant :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Y : ℕ} {R L U J : ℝ}, 2 ≤ Y →
      (Y : ℝ) ≤ Real.exp L → 0 ≤ R → R ≤ 6 / 5 → 40000 ≤ L →
      conreyHorizontalRightEdge L + 1 ≤ U → U + 1 ≤ Real.exp L →
      conreyHorizontalJensenFactorZeroMass Y R L U ≤ J →
      ∃ q : ℝ, ∃ g : ℂ → ℂ,
        q ∈ Set.Icc (conreyHorizontalJensenGoodRadiusLower R L)
          (conreyHorizontalJensenGoodRadiusUpper R L) ∧
        AnalyticOnNhd ℂ g
          (Metric.closedBall (conreyHorizontalJensenCenter L U)
            (conreyHorizontalJensenFactorRadius R L)) ∧
        (∀ u : (Metric.closedBall (conreyHorizontalJensenCenter L U)
            (conreyHorizontalJensenFactorRadius R L) : Set ℂ), g u ≠ 0) ∧
        (∀ z ∈ Metric.ball (conreyHorizontalJensenCenter L U)
            (conreyHorizontalJensenFactorRadius R L),
          conreyHorizontalJensenProduct Y R L z ≠ 0 →
            logDeriv (conreyHorizontalJensenProduct Y R L) z =
              (∑ᶠ u,
                (MeromorphicOn.divisor
                  (conreyHorizontalJensenProduct Y R L)
                  (Metric.closedBall (conreyHorizontalJensenCenter L U)
                    (conreyHorizontalJensenFactorRadius R L)) u : ℂ) *
                  (z - u)⁻¹) + logDeriv g z) ∧
        ∀ z ∈ Metric.closedBall (conreyHorizontalJensenCenter L U)
            (conreyHorizontalJensenInnerRadius R L),
          ‖logDeriv g z‖ ≤
            4 * max
                (conreyHorizontalJensenFactorLogVariationMajorant
                  C Y R L U J) 1 *
              (q + conreyHorizontalJensenInnerRadius R L) /
              (q - conreyHorizontalJensenInnerRadius R L) ^ 2 := by
  rcases exists_conreyHorizontalJensenGoodFactor_logDeriv_le with
    ⟨C, hC, hfactor⟩
  refine ⟨C, hC, ?_⟩
  intro Y R L U J hY hYtop hR0 hRmax hL hU hUtop hmass
  rcases hfactor hY hYtop hR0 hRmax hL hU hUtop with
    ⟨q, g, hq, hg, hgne, hcenter, hsphere, hdecomp, hregular⟩
  have hvariation :=
    conreyHorizontalJensenFactorLogVariation_le_of_mass_le
      (C := C) hR0 hRmax hL hU hmass
  have hmax :
      max (conreyHorizontalJensenFactorCircleLogUpper C Y R L U -
          conreyHorizontalJensenFactorCenterLogLower Y R L U) 1 ≤
        max (conreyHorizontalJensenFactorLogVariationMajorant
          C Y R L U J) 1 := by
    exact max_le
      (hvariation.trans (le_max_left _ _)) (le_max_right _ _)
  have hbuffer := conreyHorizontalJensenBufferGeometry hR0 hRmax hL
  have hqpos : 0 < q :=
    (conreyHorizontalJensenInnerRadius_pos R L).trans
      (hbuffer.1.trans_le hq.1)
  have hdq : conreyHorizontalJensenInnerRadius R L < q :=
    hbuffer.1.trans_le hq.1
  have hnumNonneg : 0 ≤ q + conreyHorizontalJensenInnerRadius R L := by
    have hdpos := conreyHorizontalJensenInnerRadius_pos R L
    linarith
  have hdenSqPos : 0 <
      (q - conreyHorizontalJensenInnerRadius R L) ^ 2 :=
    sq_pos_of_pos (sub_pos.mpr hdq)
  refine ⟨q, g, hq, hg, hgne, hdecomp, ?_⟩
  intro z hz
  have hraw := hregular z hz
  apply hraw.trans
  apply (div_le_div_iff_of_pos_right hdenSqPos).2
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmax (by norm_num : (0 : ℝ) ≤ 4))
    hnumNonneg

/-- Fully explicit Borel bound for the same extracted nonvanishing factor.
The buffered-circle geometry absorbs the selected radius `q` and leaves the
documented constant `128`. -/
theorem exists_conreyHorizontalJensenGoodFactor_logDeriv_le_explicit :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Y : ℕ} {R L U J : ℝ}, 2 ≤ Y →
      (Y : ℝ) ≤ Real.exp L → 0 ≤ R → R ≤ 6 / 5 → 40000 ≤ L →
      conreyHorizontalRightEdge L + 1 ≤ U → U + 1 ≤ Real.exp L →
      conreyHorizontalJensenFactorZeroMass Y R L U ≤ J →
      ∃ q : ℝ, ∃ g : ℂ → ℂ,
        q ∈ Set.Icc (conreyHorizontalJensenGoodRadiusLower R L)
          (conreyHorizontalJensenGoodRadiusUpper R L) ∧
        AnalyticOnNhd ℂ g
          (Metric.closedBall (conreyHorizontalJensenCenter L U)
            (conreyHorizontalJensenFactorRadius R L)) ∧
        (∀ u : (Metric.closedBall (conreyHorizontalJensenCenter L U)
            (conreyHorizontalJensenFactorRadius R L) : Set ℂ), g u ≠ 0) ∧
        (∀ z ∈ Metric.ball (conreyHorizontalJensenCenter L U)
            (conreyHorizontalJensenFactorRadius R L),
          conreyHorizontalJensenProduct Y R L z ≠ 0 →
            logDeriv (conreyHorizontalJensenProduct Y R L) z =
              (∑ᶠ u,
                (MeromorphicOn.divisor
                  (conreyHorizontalJensenProduct Y R L)
                  (Metric.closedBall (conreyHorizontalJensenCenter L U)
                    (conreyHorizontalJensenFactorRadius R L)) u : ℂ) *
                  (z - u)⁻¹) + logDeriv g z) ∧
        ∀ z ∈ Metric.closedBall (conreyHorizontalJensenCenter L U)
            (conreyHorizontalJensenInnerRadius R L),
          ‖logDeriv g z‖ ≤
            128 * max
                (conreyHorizontalJensenFactorLogVariationMajorant
                  C Y R L U J) 1 *
              conreyHorizontalJensenOuterRadius L /
              conreyHorizontalJensenRadiusGap R L ^ 2 := by
  rcases exists_conreyHorizontalJensenGoodFactor_logDeriv_le_majorant with
    ⟨C, hC, hfactor⟩
  refine ⟨C, hC, ?_⟩
  intro Y R L U J hY hYtop hR0 hRmax hL hU hUtop hmass
  rcases hfactor hY hYtop hR0 hRmax hL hU hUtop hmass with
    ⟨q, g, hq, hg, hgne, hdecomp, hregular⟩
  refine ⟨q, g, hq, hg, hgne, hdecomp, ?_⟩
  intro z hz
  have hraw := hregular z hz
  have hgeometry :=
    conreyHorizontalJensenFactorGeometry_le hR0 hRmax hL hq
  have hmaxNonneg :
      0 ≤ max
        (conreyHorizontalJensenFactorLogVariationMajorant
          C Y R L U J) 1 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_right _ _)
  have hscaled := mul_le_mul_of_nonneg_left hgeometry
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hmaxNonneg)
  exact hraw.trans (by
    calc
      4 * max
          (conreyHorizontalJensenFactorLogVariationMajorant
            C Y R L U J) 1 *
          (q + conreyHorizontalJensenInnerRadius R L) /
          (q - conreyHorizontalJensenInnerRadius R L) ^ 2 =
          (4 * max
            (conreyHorizontalJensenFactorLogVariationMajorant
              C Y R L U J) 1) *
            ((q + conreyHorizontalJensenInnerRadius R L) /
              (q - conreyHorizontalJensenInnerRadius R L) ^ 2) := by ring
      _ ≤ (4 * max
            (conreyHorizontalJensenFactorLogVariationMajorant
              C Y R L U J) 1) *
            (32 * conreyHorizontalJensenOuterRadius L /
              conreyHorizontalJensenRadiusGap R L ^ 2) := hscaled
      _ = 128 * max
            (conreyHorizontalJensenFactorLogVariationMajorant
              C Y R L U J) 1 *
            conreyHorizontalJensenOuterRadius L /
            conreyHorizontalJensenRadiusGap R L ^ 2 := by ring)

end HardyTheorem
