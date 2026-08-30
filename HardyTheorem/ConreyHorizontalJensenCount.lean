import HardyTheorem.ConreyHorizontalJensenCenter
import HardyTheorem.ConreyHorizontalJensenGrowth
import PrimeNumberTheorem.AnalyticJensen

/-!
# Jensen mass and admissible heights for Conrey's actual product

This module applies the generic analytic Jensen theorem to the actual
degree-one Conrey product.  The divisor on the inner disk is local-equivalent
to the outer divisor restricted to that disk; its finite support is the only
zero set used in the subsequent height selection.
-/

open Complex Set
open PrimeNumberTheorem.CarlsonZeroDensity

namespace HardyTheorem

/-- The actual explicit product with the Littlewood left edge substituted. -/
noncomputable def conreyHorizontalJensenProduct
    (Y : ℕ) (R L : ℝ) : ℂ → ℂ :=
  conreyMollifiedDegreeOneV1 (49 / 100) 0 (51 / 50) L Y
    (conreyHorizontalLeftEdge R L) conreyExplicitP

/-- Total analytic zero multiplicity on the inner Jensen disk. -/
noncomputable def conreyHorizontalJensenInnerZeroMass
    (Y : ℕ) (R L U : ℝ) : ℝ :=
  ∑ᶠ u,
    (MeromorphicOn.divisor (conreyHorizontalJensenProduct Y R L)
      (Metric.closedBall (conreyHorizontalJensenCenter L U)
        (conreyHorizontalJensenInnerRadius R L)) u : ℝ)

/-- Distinct zeros on the inner disk, with multiplicity retained separately
by the divisor mass. -/
noncomputable def conreyHorizontalJensenInnerZeroSupport
    (Y : ℕ) (R L U : ℝ) : Finset ℂ :=
  ((MeromorphicOn.divisor (conreyHorizontalJensenProduct Y R L)
      (Metric.closedBall (conreyHorizontalJensenCenter L U)
        (conreyHorizontalJensenInnerRadius R L))).finiteSupport
    (isCompact_closedBall (conreyHorizontalJensenCenter L U)
      (conreyHorizontalJensenInnerRadius R L))).toFinset

/-- Imaginary parts of the distinct inner-disk zeros. -/
noncomputable def conreyHorizontalJensenInnerZeroHeights
    (Y : ℕ) (R L U : ℝ) : Finset ℝ :=
  (conreyHorizontalJensenInnerZeroSupport Y R L U).image Complex.im

/-- Exact Jensen divisor-mass bound for the actual product.  The denominator
keeps the moving radius ratio visible. -/
theorem exists_conreyHorizontalJensenInnerZeroMass_le :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Y : ℕ} {R L U : ℝ}, 2 ≤ Y →
      (Y : ℝ) ≤ Real.exp L → 0 ≤ R → R ≤ 6 / 5 → 40000 ≤ L →
      conreyHorizontalRightEdge L + 1 ≤ U → U + 1 ≤ Real.exp L →
      conreyHorizontalJensenInnerZeroMass Y R L U ≤
        (Real.log (C * (Y : ℝ) *
            (conreyHorizontalJensenHeightBase L U) ^ 6 * (L + 2) ^ 2) +
          Real.log 6) /
            Real.log (conreyHorizontalJensenOuterRadius L /
              conreyHorizontalJensenInnerRadius R L) := by
  rcases
      exists_norm_conreyExplicitMollifiedV1_le_conreyHorizontalJensenOuterClosedBall with
    ⟨C, hC, hgrowth⟩
  refine ⟨C, hC, ?_⟩
  intro Y R L U hY hYtop hR0 hRmax hL hU hUtop
  let f : ℂ → ℂ := conreyHorizontalJensenProduct Y R L
  let c : ℂ := conreyHorizontalJensenCenter L U
  let r : ℝ := conreyHorizontalJensenInnerRadius R L
  let R₀ : ℝ := conreyHorizontalJensenOuterRadius L
  let H : ℝ := conreyHorizontalJensenHeightBase L U
  let M : ℝ := C * (Y : ℝ) * H ^ 6 * (L + 2) ^ 2
  have hLpos : 0 < L := by linarith
  have hsigma0 : conreyHorizontalLeftEdge R L ≤ 1 / 2 := by
    dsimp [conreyHorizontalLeftEdge]
    exact sub_le_self _ (div_nonneg hR0 hLpos.le)
  have hr : 0 < r := by
    simpa only [r] using conreyHorizontalJensenInnerRadius_pos R L
  have hrR : r < R₀ := by
    simpa only [r, R₀] using
      conreyHorizontalJensenInnerRadius_lt_outerRadius hR0 hRmax hL
  have hR₀ : 0 < R₀ := hr.trans hrR
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
    hr hrR hanalytic (by norm_num : (0 : ℝ) < 1 / 6) hcenter hcircle
  have hlocal := finsum_divisor_closedBall_eq_finsum_mem_of_le
    (f := f) (c := c) (b := r) (R := R₀) hrR.le hanalytic.meromorphicOn
  rw [← hlocal] at hjensen
  have hlogSix : Real.log (1 / 6 : ℝ) = -Real.log 6 := by
    rw [show (1 / 6 : ℝ) = (6 : ℝ)⁻¹ by ring, Real.log_inv]
  rw [hlogSix] at hjensen
  simpa [conreyHorizontalJensenInnerZeroMass, f, c, r, R₀, H, M,
    sub_neg_eq_add] using hjensen

/-- The number of distinct inner-disk zeros is bounded by their total
analytic multiplicity. -/
theorem card_conreyHorizontalJensenInnerZeroSupport_le_mass
    {Y : ℕ} {R L U : ℝ} (hR0 : 0 ≤ R) (hRmax : R ≤ 6 / 5)
    (hL : 40000 ≤ L) (hU : conreyHorizontalRightEdge L + 1 ≤ U) :
    ((conreyHorizontalJensenInnerZeroSupport Y R L U).card : ℝ) ≤
      conreyHorizontalJensenInnerZeroMass Y R L U := by
  have hrR := conreyHorizontalJensenInnerRadius_lt_outerRadius hR0 hRmax hL
  have hanalyticOuter :=
    analyticOnNhd_conreyExplicitMollifiedV1_horizontalJensenOuterClosedBall
      Y (conreyHorizontalLeftEdge R L) L U hL hU
  have hanalyticInner := hanalyticOuter.mono
    (Metric.closedBall_subset_closedBall hrR.le)
  simpa [conreyHorizontalJensenInnerZeroSupport,
    conreyHorizontalJensenInnerZeroMass, conreyHorizontalJensenProduct] using
      card_divisor_support_le_finsum_mass hanalyticInner

private theorem analyticOrderAt_conreyHorizontalJensenProduct_ne_top
    {Y : ℕ} {R L U : ℝ} (hY : 2 ≤ Y) (hR0 : 0 ≤ R)
    (hRmax : R ≤ 6 / 5) (hL : 40000 ≤ L)
    (hU : conreyHorizontalRightEdge L + 1 ≤ U) {z : ℂ}
    (hz : z ∈ Metric.closedBall (conreyHorizontalJensenCenter L U)
      (conreyHorizontalJensenInnerRadius R L)) :
    analyticOrderAt (conreyHorizontalJensenProduct Y R L) z ≠ ⊤ := by
  have hrR := conreyHorizontalJensenInnerRadius_lt_outerRadius hR0 hRmax hL
  have hzOuter : z ∈ Metric.closedBall (conreyHorizontalJensenCenter L U)
      (conreyHorizontalJensenOuterRadius L) :=
    Metric.closedBall_subset_closedBall hrR.le hz
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

private theorem divisor_conreyHorizontalJensenProduct_eq_analyticOrderNatAt
    {Y : ℕ} {R L U : ℝ} (hY : 2 ≤ Y) (hR0 : 0 ≤ R)
    (hRmax : R ≤ 6 / 5) (hL : 40000 ≤ L)
    (hU : conreyHorizontalRightEdge L + 1 ≤ U) {z : ℂ}
    (hz : z ∈ Metric.closedBall (conreyHorizontalJensenCenter L U)
      (conreyHorizontalJensenInnerRadius R L)) :
    MeromorphicOn.divisor (conreyHorizontalJensenProduct Y R L)
        (Metric.closedBall (conreyHorizontalJensenCenter L U)
          (conreyHorizontalJensenInnerRadius R L)) z =
      (analyticOrderNatAt (conreyHorizontalJensenProduct Y R L) z : ℤ) := by
  have hrR := conreyHorizontalJensenInnerRadius_lt_outerRadius hR0 hRmax hL
  have hanalyticOuter :=
    analyticOnNhd_conreyExplicitMollifiedV1_horizontalJensenOuterClosedBall
      Y (conreyHorizontalLeftEdge R L) L U hL hU
  have hanalyticInner := hanalyticOuter.mono
    (Metric.closedBall_subset_closedBall hrR.le)
  have hanalyticInner' :
      AnalyticOnNhd ℂ (conreyHorizontalJensenProduct Y R L)
        (Metric.closedBall (conreyHorizontalJensenCenter L U)
          (conreyHorizontalJensenInnerRadius R L)) := by
    simpa [conreyHorizontalJensenProduct] using hanalyticInner
  have hanalyticAt := hanalyticInner' z hz
  have horder := analyticOrderAt_conreyHorizontalJensenProduct_ne_top
    hY hR0 hRmax hL hU hz
  rw [MeromorphicOn.divisor_apply hanalyticInner'.meromorphicOn hz,
    hanalyticAt.meromorphicOrderAt_eq]
  have hcast := Nat.cast_analyticOrderNatAt horder
  rw [← hcast]
  simp

private theorem mem_conreyHorizontalJensenInnerZeroSupport_iff_zero
    {Y : ℕ} {R L U : ℝ} (hY : 2 ≤ Y) (hR0 : 0 ≤ R)
    (hRmax : R ≤ 6 / 5) (hL : 40000 ≤ L)
    (hU : conreyHorizontalRightEdge L + 1 ≤ U) {z : ℂ}
    (hz : z ∈ Metric.closedBall (conreyHorizontalJensenCenter L U)
      (conreyHorizontalJensenInnerRadius R L)) :
    z ∈ conreyHorizontalJensenInnerZeroSupport Y R L U ↔
      conreyHorizontalJensenProduct Y R L z = 0 := by
  classical
  let D := MeromorphicOn.divisor (conreyHorizontalJensenProduct Y R L)
    (Metric.closedBall (conreyHorizontalJensenCenter L U)
      (conreyHorizontalJensenInnerRadius R L))
  have hdivisor : D z =
      (analyticOrderNatAt (conreyHorizontalJensenProduct Y R L) z : ℤ) := by
    dsimp [D]
    exact divisor_conreyHorizontalJensenProduct_eq_analyticOrderNatAt
      hY hR0 hRmax hL hU hz
  have hrR := conreyHorizontalJensenInnerRadius_lt_outerRadius hR0 hRmax hL
  have hanalyticOuter :=
    analyticOnNhd_conreyExplicitMollifiedV1_horizontalJensenOuterClosedBall
      Y (conreyHorizontalLeftEdge R L) L U hL hU
  have hanalytic : AnalyticAt ℂ (conreyHorizontalJensenProduct Y R L) z := by
    simpa [conreyHorizontalJensenProduct] using
      (hanalyticOuter.mono
        (Metric.closedBall_subset_closedBall hrR.le) z hz)
  have horder := analyticOrderAt_conreyHorizontalJensenProduct_ne_top
    hY hR0 hRmax hL hU hz
  have hnatCast := Nat.cast_analyticOrderNatAt horder
  rw [conreyHorizontalJensenInnerZeroSupport]
  rw [(D.finiteSupport
    (isCompact_closedBall (conreyHorizontalJensenCenter L U)
      (conreyHorizontalJensenInnerRadius R L))).mem_toFinset]
  simp only [Function.mem_support]
  rw [hdivisor, Int.ofNat_ne_zero]
  constructor
  · intro hnat
    apply hanalytic.analyticOrderAt_ne_zero.mp
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
    exact (hanalytic.analyticOrderAt_eq_zero.mp horderZero) hzero

/-- Every admissible unit window contains a quantitatively separated height
on which the actual product is nonzero across the complete horizontal
segment. -/
theorem exists_conreyHorizontalJensenAdmissibleHeight
    {Y : ℕ} {R L U : ℝ} (hY : 2 ≤ Y) (hR0 : 0 ≤ R)
    (hRmax : R ≤ 6 / 5) (hL : 40000 ≤ L)
    (hU : conreyHorizontalRightEdge L + 1 ≤ U) :
    ∃ t ∈ Set.Icc U (U + 1),
      (∀ z ∈ conreyHorizontalJensenInnerZeroSupport Y R L U,
        1 / ((4 : ℝ) *
            ((conreyHorizontalJensenInnerZeroHeights Y R L U).card + 1)) ≤
          |t - z.im|) ∧
      ∀ x ∈ Set.Icc (conreyHorizontalLeftEdge R L)
          (conreyHorizontalRightEdge L),
        conreyHorizontalJensenProduct Y R L
          ((x : ℂ) + I * (t : ℂ)) ≠ 0 := by
  classical
  let P := conreyHorizontalJensenInnerZeroSupport Y R L U
  let H := conreyHorizontalJensenInnerZeroHeights Y R L U
  rcases ZeroFreeRegion.exists_radius_separated_from_finset H
      (show U < U + 1 by linarith) with ⟨t, ht, hsep⟩
  have hdelta : 0 < 1 / ((4 : ℝ) * ((H.card : ℝ) + 1)) := by
    positivity
  refine ⟨t, ht, ?_, ?_⟩
  · intro z hz
    have hzim : z.im ∈ H := by
      dsimp [H, conreyHorizontalJensenInnerZeroHeights]
      exact Finset.mem_image.mpr ⟨z, by simpa [P] using hz, rfl⟩
    simpa [H] using hsep z.im hzim
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
    have hzP : z ∈ P := by
      dsimp [P]
      exact (mem_conreyHorizontalJensenInnerZeroSupport_iff_zero
        hY hR0 hRmax hL hU hzInner).mpr (by simpa [z] using hzero)
    have hzim : z.im ∈ H := by
      dsimp [H, conreyHorizontalJensenInnerZeroHeights]
      exact Finset.mem_image.mpr ⟨z, by simpa [P] using hzP, rfl⟩
    have hzeroDistance :
        1 / ((4 : ℝ) * ((H.card : ℝ) + 1)) ≤ 0 := by
      simpa [z] using hsep z.im hzim
    exact (not_lt_of_ge hzeroDistance) hdelta

end HardyTheorem
