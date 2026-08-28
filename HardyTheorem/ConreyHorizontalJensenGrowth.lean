import HardyTheorem.ConreyHorizontalJensenGeometry
import HardyTheorem.ConreyMollifierRightEdge
import ZeroFreeRegion.PhragmenLindelofZeta

/-!
# Actual growth inputs on Conrey's moving Jensen disk

This module derives the height geometry and the polynomial bounds for zeta
and its derivative on the actual moving outer disk.  No abstract growth
predicate is introduced.
-/

open Complex Set

namespace HardyTheorem

/-- A positive height base which absorbs both the moving center and the disk
radius. -/
noncomputable def conreyHorizontalJensenHeightBase (L U : ℝ) : ℝ :=
  U + conreyHorizontalRightEdge L + 10

theorem one_le_conreyHorizontalJensenHeightBase
    {L U : ℝ} (hL : 40000 ≤ L)
    (hU : conreyHorizontalRightEdge L + 1 ≤ U) :
    1 ≤ conreyHorizontalJensenHeightBase L U := by
  have hlog : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  dsimp [conreyHorizontalJensenHeightBase, conreyHorizontalRightEdge] at hU ⊢
  linarith

/-- The usual strip-growth height factor is absorbed by the moving height
base on the whole outer disk. -/
theorem abs_im_add_three_le_conreyHorizontalJensenHeightBase
    {L U : ℝ} (hU : conreyHorizontalRightEdge L + 1 ≤ U) {z : ℂ}
    (hz : z ∈ Metric.closedBall (conreyHorizontalJensenCenter L U)
      (conreyHorizontalJensenOuterRadius L)) :
    |z.im| + 3 ≤ conreyHorizontalJensenHeightBase L U := by
  have hdist :
      ‖z - conreyHorizontalJensenCenter L U‖ ≤
        conreyHorizontalJensenOuterRadius L := by
    simpa [Metric.mem_closedBall, Complex.dist_eq] using hz
  have him := Complex.abs_im_le_norm
    (z - conreyHorizontalJensenCenter L U)
  have himAbs :
      |z.im - (U + 1 / 2)| ≤ conreyHorizontalJensenOuterRadius L := by
    simpa [conreyHorizontalJensenCenter] using him.trans hdist
  rw [abs_le] at himAbs
  have himLower :=
    seven_fourths_le_im_of_mem_conreyHorizontalJensenOuterClosedBall hU hz
  rw [abs_of_pos (by linarith : 0 < z.im)]
  dsimp [conreyHorizontalJensenHeightBase,
    conreyHorizontalJensenOuterRadius] at himAbs ⊢
  linarith

/-- The Euclidean size of a point on the outer disk is absorbed by twice the
height base.  This is the bridge from the geometric disk to logarithmic
archimedean estimates. -/
theorem norm_le_two_mul_conreyHorizontalJensenHeightBase
    {L U : ℝ} (hL : 40000 ≤ L)
    (hU : conreyHorizontalRightEdge L + 1 ≤ U) {z : ℂ}
    (hz : z ∈ Metric.closedBall (conreyHorizontalJensenCenter L U)
      (conreyHorizontalJensenOuterRadius L)) :
    ‖z‖ ≤ 2 * conreyHorizontalJensenHeightBase L U := by
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
  have hzreLower : (1 / 4 : ℝ) ≤ z.re :=
    quarter_le_re_of_mem_conreyHorizontalJensenOuterClosedBall hL hz
  have hzim :=
    abs_im_add_three_le_conreyHorizontalJensenHeightBase hU hz
  have hreUpper : z.re ≤ conreyHorizontalJensenHeightBase L U := by
    dsimp [conreyHorizontalJensenHeightBase,
      conreyHorizontalJensenOuterRadius] at hreAbs ⊢
    linarith
  calc
    ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ = z.re + |z.im| := by rw [abs_of_nonneg (by linarith)]
    _ ≤ 2 * conreyHorizontalJensenHeightBase L U := by linarith

private theorem im_le_conreyHorizontalJensenCenter_add_outerRadius
    {L U : ℝ} {z : ℂ}
    (hz : z ∈ Metric.closedBall (conreyHorizontalJensenCenter L U)
      (conreyHorizontalJensenOuterRadius L)) :
    z.im ≤ U + 1 / 2 + conreyHorizontalJensenOuterRadius L := by
  have hdist :
      ‖z - conreyHorizontalJensenCenter L U‖ ≤
        conreyHorizontalJensenOuterRadius L := by
    simpa [Metric.mem_closedBall, Complex.dist_eq] using hz
  have him := Complex.abs_im_le_norm
    (z - conreyHorizontalJensenCenter L U)
  have himAbs :
      |z.im - (U + 1 / 2)| ≤ conreyHorizontalJensenOuterRadius L := by
    simpa [conreyHorizontalJensenCenter] using him.trans hdist
  rw [abs_le] at himAbs
  linarith

private theorem cauchySphere_re_mem_Icc_zero_four
    {z w : ℂ} (hzreLower : (1 / 4 : ℝ) ≤ z.re)
    (hzreUpper : z.re ≤ 63 / 16)
    (hw : w ∈ Metric.sphere z (1 / 16 : ℝ)) :
    w.re ∈ Set.Icc (0 : ℝ) 4 := by
  have hdist : ‖w - z‖ = (1 / 16 : ℝ) := by
    simpa [Metric.mem_sphere, Complex.dist_eq] using hw
  have hre := Complex.abs_re_le_norm (w - z)
  have hreAbs : |w.re - z.re| ≤ (1 / 16 : ℝ) := by
    simpa using hre.trans_eq hdist
  rw [abs_le] at hreAbs
  constructor <;> linarith

private theorem one_le_abs_im_of_mem_cauchySphere
    {L U : ℝ} (hU : conreyHorizontalRightEdge L + 1 ≤ U)
    {z w : ℂ}
    (hz : z ∈ Metric.closedBall (conreyHorizontalJensenCenter L U)
      (conreyHorizontalJensenOuterRadius L))
    (hw : w ∈ Metric.sphere z (1 / 16 : ℝ)) :
    1 ≤ |w.im| := by
  have hzim :=
    seven_fourths_le_im_of_mem_conreyHorizontalJensenOuterClosedBall hU hz
  have hdist : ‖w - z‖ = (1 / 16 : ℝ) := by
    simpa [Metric.mem_sphere, Complex.dist_eq] using hw
  have him := Complex.abs_im_le_norm (w - z)
  have himAbs : |w.im - z.im| ≤ (1 / 16 : ℝ) := by
    simpa using him.trans_eq hdist
  rw [abs_le] at himAbs
  rw [abs_of_pos (by linarith : 0 < w.im)]
  linarith

private theorem abs_im_add_three_le_heightBase_of_mem_cauchySphere
    {L U : ℝ} (hU : conreyHorizontalRightEdge L + 1 ≤ U)
    {z w : ℂ}
    (hz : z ∈ Metric.closedBall (conreyHorizontalJensenCenter L U)
      (conreyHorizontalJensenOuterRadius L))
    (hw : w ∈ Metric.sphere z (1 / 16 : ℝ)) :
    |w.im| + 3 ≤ conreyHorizontalJensenHeightBase L U := by
  have hzim :=
    seven_fourths_le_im_of_mem_conreyHorizontalJensenOuterClosedBall hU hz
  have hzUpper := im_le_conreyHorizontalJensenCenter_add_outerRadius hz
  have hdist : ‖w - z‖ = (1 / 16 : ℝ) := by
    simpa [Metric.mem_sphere, Complex.dist_eq] using hw
  have him := Complex.abs_im_le_norm (w - z)
  have himAbs : |w.im - z.im| ≤ (1 / 16 : ℝ) := by
    simpa using him.trans_eq hdist
  rw [abs_le] at himAbs
  rw [abs_of_pos (by linarith : 0 < w.im)]
  dsimp [conreyHorizontalJensenHeightBase,
    conreyHorizontalJensenOuterRadius] at hzUpper ⊢
  linarith

/-- Zeta and its derivative have uniform fourth-degree height growth on every
actual outer Jensen disk.  The proof uses a radius-`1/16` Cauchy circle and
splits at `Re z = 63/16`. -/
theorem exists_norm_riemannZeta_add_deriv_le_conreyHorizontalJensenOuterClosedBall :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {L U : ℝ}, 40000 ≤ L →
      conreyHorizontalRightEdge L + 1 ≤ U → ∀ {z : ℂ},
      z ∈ Metric.closedBall (conreyHorizontalJensenCenter L U)
        (conreyHorizontalJensenOuterRadius L) →
      ‖riemannZeta z‖ + ‖deriv riemannZeta z‖ ≤
        C * (conreyHorizontalJensenHeightBase L U) ^ 4 := by
  rcases ZeroFreeRegion.exists_norm_riemannZeta_le_polynomial_on_zero_four with
    ⟨C₀, hC₀, hstrip⟩
  let C₁ : ℝ := max C₀ 2
  refine ⟨17 * C₁, by dsimp [C₁]; nlinarith [le_max_right C₀ 2], ?_⟩
  intro L U hL hU z hz
  let H : ℝ := conreyHorizontalJensenHeightBase L U
  have hH : 1 ≤ H := by
    simpa only [H] using one_le_conreyHorizontalJensenHeightBase hL hU
  have hHpow : 1 ≤ H ^ 4 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hH 4
  have hC₁ : 2 ≤ C₁ := le_max_right C₀ 2
  have hC₁nonneg : 0 ≤ C₁ := by linarith
  have hzreLower : (1 / 4 : ℝ) ≤ z.re :=
    quarter_le_re_of_mem_conreyHorizontalJensenOuterClosedBall hL hz
  have hzimLower :=
    seven_fourths_le_im_of_mem_conreyHorizontalJensenOuterClosedBall hU hz
  have hzheight : |z.im| + 3 ≤ H := by
    simpa only [H] using
      abs_im_add_three_le_conreyHorizontalJensenHeightBase hU hz
  have hzheightPow : (|z.im| + 3) ^ 4 ≤ H ^ 4 :=
    pow_le_pow_left₀ (by positivity) hzheight 4
  have hzeta : ‖riemannZeta z‖ ≤ C₁ * H ^ 4 := by
    by_cases hz4 : z.re ≤ 4
    · have hraw := hstrip z ⟨by linarith, hz4⟩
          (by rw [abs_of_pos (by linarith : 0 < z.im)]; linarith)
      exact hraw.trans <| calc
        C₀ * (|z.im| + 3) ^ 4 ≤ C₁ * (|z.im| + 3) ^ 4 :=
          mul_le_mul_of_nonneg_right (le_max_left C₀ 2) (by positivity)
        _ ≤ C₁ * H ^ 4 :=
          mul_le_mul_of_nonneg_left hzheightPow hC₁nonneg
    · have hright :=
        (ZeroFreeRegion.norm_riemannZeta_le_re_zeta_two_of_two_le_re z
          (by linarith)).trans ZeroFreeRegion.riemannZeta_two_re_le_five_thirds
      exact hright.trans <| calc
        (5 / 3 : ℝ) ≤ 2 * 1 := by norm_num
        _ ≤ C₁ * H ^ 4 :=
          mul_le_mul hC₁ hHpow (by norm_num) (by linarith)
  have hderiv : ‖deriv riemannZeta z‖ ≤ 16 * C₁ * H ^ 4 := by
    by_cases hzsplit : z.re ≤ 63 / 16
    · have hsphere : ∀ w : ℂ, w ∈ Metric.sphere z (1 / 16 : ℝ) →
          ‖riemannZeta w‖ ≤ C₁ * H ^ 4 := by
        intro w hw
        have hwre := cauchySphere_re_mem_Icc_zero_four
          hzreLower hzsplit hw
        have hwim := one_le_abs_im_of_mem_cauchySphere hU hz hw
        have hwheight :=
          abs_im_add_three_le_heightBase_of_mem_cauchySphere hU hz hw
        have hwheightPow : (|w.im| + 3) ^ 4 ≤ H ^ 4 :=
          pow_le_pow_left₀ (by positivity) hwheight 4
        exact (hstrip w hwre hwim).trans <| calc
          C₀ * (|w.im| + 3) ^ 4 ≤ C₁ * (|w.im| + 3) ^ 4 :=
            mul_le_mul_of_nonneg_right (le_max_left C₀ 2) (by positivity)
          _ ≤ C₁ * H ^ 4 :=
            mul_le_mul_of_nonneg_left hwheightPow hC₁nonneg
      have hcauchy :=
        ZeroFreeRegion.norm_deriv_riemannZeta_le_of_sphere_norm_bound_avoid_one
          (c := z) (R := (1 / 16 : ℝ)) (M := C₁ * H ^ 4)
          (by norm_num) (by
            intro w hw hwone
            subst w
            have hnorm : ‖(1 : ℂ) - z‖ ≤ (1 / 16 : ℝ) := by
              simpa [Metric.mem_closedBall, Complex.dist_eq] using hw
            have him : |z.im| ≤ ‖(1 : ℂ) - z‖ := by
              simpa using Complex.abs_im_le_norm ((1 : ℂ) - z)
            rw [abs_of_pos (by linarith : 0 < z.im)] at him
            linarith) hsphere
      calc
        ‖deriv riemannZeta z‖ ≤ C₁ * H ^ 4 / (1 / 16 : ℝ) := hcauchy
        _ = 16 * C₁ * H ^ 4 := by ring
    · have hright :=
        ZeroFreeRegion.norm_deriv_riemannZeta_le_re_zeta_two_div_radius_of_closedBall_two_le_re
          (c := z) (R := (1 / 16 : ℝ)) (by norm_num) (by
            intro w hw
            have hre := ZeroFreeRegion.closedBall_re_bounds
              (z := w) (c := z) (R := (1 / 16 : ℝ)) hw
            linarith)
      have hright' : ‖deriv riemannZeta z‖ ≤ 80 / 3 := by
        calc
          ‖deriv riemannZeta z‖ ≤
              (riemannZeta (2 : ℂ)).re / (1 / 16 : ℝ) := hright
          _ ≤ (5 / 3 : ℝ) / (1 / 16 : ℝ) := by
            gcongr
            exact ZeroFreeRegion.riemannZeta_two_re_le_five_thirds
          _ = 80 / 3 := by norm_num
      exact hright'.trans <| calc
        (80 / 3 : ℝ) ≤ 16 * 2 * 1 := by norm_num
        _ ≤ 16 * C₁ * H ^ 4 := by
          nlinarith [mul_le_mul hC₁ hHpow (by norm_num : (0 : ℝ) ≤ 1)
            (by linarith : 0 ≤ C₁)]
  calc
    ‖riemannZeta z‖ + ‖deriv riemannZeta z‖ ≤
        C₁ * H ^ 4 + 16 * C₁ * H ^ 4 := add_le_add hzeta hderiv
    _ = (17 * C₁) * H ^ 4 := by ring

/-- A fixed coarse constant for the archimedean logarithmic derivative on
the moving Jensen disk. -/
noncomputable def conreyHorizontalJensenArchimedeanConstant : ℝ := 10

theorem one_le_conreyHorizontalJensenArchimedeanConstant :
    1 ≤ conreyHorizontalJensenArchimedeanConstant := by
  norm_num [conreyHorizontalJensenArchimedeanConstant]

/-- The exact logarithmic derivative `H'/H` has logarithmic growth on the
actual outer disk.  The proof shifts `digamma (z/2)` once to the half-plane
`Re >= 1`; the disk height controls the recurrence term. -/
theorem norm_logDeriv_conreyH_le_conreyHorizontalJensenOuterClosedBall
    {L U : ℝ} (hL : 40000 ≤ L)
    (hU : conreyHorizontalRightEdge L + 1 ≤ U) {z : ℂ}
    (hz : z ∈ Metric.closedBall (conreyHorizontalJensenCenter L U)
      (conreyHorizontalJensenOuterRadius L)) :
    ‖deriv conreyH z / conreyH z‖ ≤
      conreyHorizontalJensenArchimedeanConstant *
        (1 + Real.log (conreyHorizontalJensenHeightBase L U + 2)) := by
  let H : ℝ := conreyHorizontalJensenHeightBase L U
  let q : ℂ := z / 2
  have hH : 1 ≤ H := by
    simpa only [H] using one_le_conreyHorizontalJensenHeightBase hL hU
  have hzim : 7 / 4 ≤ z.im :=
    seven_fourths_le_im_of_mem_conreyHorizontalJensenOuterClosedBall hU hz
  have hzre : (1 / 4 : ℝ) ≤ z.re :=
    quarter_le_re_of_mem_conreyHorizontalJensenOuterClosedBall hL hz
  have hznormUpper : ‖z‖ ≤ 2 * H := by
    simpa only [H] using
      norm_le_two_mul_conreyHorizontalJensenHeightBase hL hU hz
  have hznormLower : 1 ≤ ‖z‖ := by
    calc
      1 ≤ z.im := by linarith
      _ ≤ |z.im| := le_abs_self _
      _ ≤ ‖z‖ := Complex.abs_im_le_norm z
  have hzOneNormLower : 1 ≤ ‖z - 1‖ := by
    calc
      1 ≤ (z - 1).im := by simp only [Complex.sub_im, Complex.one_im]; linarith
      _ ≤ |(z - 1).im| := le_abs_self _
      _ ≤ ‖z - 1‖ := Complex.abs_im_le_norm (z - 1)
  have hInv : ‖1 / z‖ ≤ 1 := by
    rw [norm_div, norm_one]
    simpa only [div_one] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hznormLower
  have hInvOne : ‖1 / (z - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    simpa only [div_one] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hzOneNormLower
  have hqnormLower : (7 / 8 : ℝ) ≤ ‖q‖ := by
    dsimp only [q]
    rw [norm_div]
    norm_num only [norm_ofNat]
    have himNorm : (7 / 4 : ℝ) ≤ ‖z‖ :=
      hzim.trans (le_abs_self z.im |>.trans (Complex.abs_im_le_norm z))
    linarith
  have hqInv : ‖q⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    calc
      ‖q‖⁻¹ ≤ (7 / 8 : ℝ)⁻¹ :=
        by simpa only [one_div] using
          one_div_le_one_div_of_le (by norm_num) hqnormLower
      _ ≤ 2 := by norm_num
  have hqimne : q.im ≠ 0 := by
    intro hzero
    have hqim : q.im = z.im / 2 := by simp [q]
    rw [hqim] at hzero
    linarith
  have hregular : ∀ m : ℕ, q ≠ -(m : ℂ) := by
    intro m hm
    apply hqimne
    have himEq := congrArg Complex.im hm
    simpa using himEq
  have hqshiftRe : (1 : ℝ) ≤ (q + 1).re := by
    have hqre : q.re = z.re / 2 := by simp [q]
    rw [Complex.add_re, hqre, Complex.one_re]
    linarith
  have hqnormUpper : ‖q‖ ≤ H := by
    dsimp only [q]
    rw [norm_div]
    norm_num only [norm_ofNat]
    linarith
  have hqshiftArg : ‖q + 1‖ + 1 ≤ H + 2 := by
    have hadd := norm_add_le q (1 : ℂ)
    norm_num only [norm_one] at hadd
    linarith
  have hlogShift : Real.log (‖q + 1‖ + 1) ≤ Real.log (H + 2) :=
    Real.log_le_log (by positivity) hqshiftArg
  have hEuler : ‖(Real.eulerMascheroniConstant : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.one_half_lt_eulerMascheroniConstant.trans' (by norm_num))]
    exact Real.eulerMascheroniConstant_lt_two_thirds.le.trans (by norm_num)
  have hDigShift := PrimeNumberTheorem.norm_digamma_le_log hqshiftRe
  have hrec := Complex.digamma_apply_add_one q hregular
  have hDigEq : Complex.digamma q = Complex.digamma (q + 1) - q⁻¹ := by
    linear_combination -hrec
  have hDig : ‖Complex.digamma q‖ ≤ 6 + Real.log (H + 2) := by
    rw [hDigEq]
    exact (norm_sub_le _ _).trans (by linarith)
  have hlogPi : ‖Complex.log (Real.pi : ℂ) / 2‖ ≤ 1 := by
    have hpiExp : Real.pi ≤ Real.exp 2 := by
      have hpi := Real.pi_lt_d2
      have he := Real.exp_one_gt_d9
      have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]
        norm_num
      rw [he2]
      nlinarith
    have hlogPiLe : Real.log Real.pi ≤ 2 := by
      calc
        Real.log Real.pi ≤ Real.log (Real.exp 2) :=
          Real.log_le_log Real.pi_pos hpiExp
        _ = 2 := Real.log_exp 2
    have hlogPiEq : Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) :=
      (Complex.ofReal_log Real.pi_pos.le).symm
    rw [hlogPiEq, norm_div]
    norm_num only [norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
    linarith
  have hsone : z ≠ 1 :=
    ne_one_of_mem_conreyHorizontalJensenOuterClosedBall hL hU hz
  rw [logDeriv_conreyH_eq_of_re_pos_of_ne_one (by linarith) hsone]
  have htriangle :
      ‖1 / z + 1 / (z - 1) - Complex.log ↑Real.pi / 2 +
          Complex.digamma (z / 2) / 2‖ ≤
        ‖1 / z‖ + ‖1 / (z - 1)‖ + ‖Complex.log ↑Real.pi / 2‖ +
          ‖Complex.digamma (z / 2) / 2‖ := by
    calc
      _ ≤ ‖1 / z + 1 / (z - 1) - Complex.log ↑Real.pi / 2‖ +
          ‖Complex.digamma (z / 2) / 2‖ := norm_add_le _ _
      _ ≤ (‖1 / z + 1 / (z - 1)‖ + ‖Complex.log ↑Real.pi / 2‖) +
          ‖Complex.digamma (z / 2) / 2‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ ((‖1 / z‖ + ‖1 / (z - 1)‖) + ‖Complex.log ↑Real.pi / 2‖) +
          ‖Complex.digamma (z / 2) / 2‖ :=
        add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
      _ = _ := by ring
  have hDigHalf : ‖Complex.digamma (z / 2) / 2‖ ≤
      (6 + Real.log (H + 2)) / 2 := by
    have hqeq : z / 2 = q := by rfl
    rw [hqeq, norm_div]
    norm_num only [norm_ofNat]
    exact div_le_div_of_nonneg_right hDig (by norm_num)
  have hlogNonneg : 0 ≤ Real.log (H + 2) :=
    Real.log_nonneg (by linarith)
  dsimp only [conreyHorizontalJensenArchimedeanConstant]
  simpa only [H] using htriangle.trans (by nlinarith)

/-- Conrey's actual degree-one factor has fifth-degree height growth on the
outer disk.  This theorem assembles the proved zeta, derivative, and
archimedean estimates; it has no abstract growth premise. -/
theorem exists_norm_conreyExplicitDegreeOneV1_le_conreyHorizontalJensenOuterClosedBall :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {L U : ℝ}, 40000 ≤ L →
      conreyHorizontalRightEdge L + 1 ≤ U → ∀ {z : ℂ},
      z ∈ Metric.closedBall (conreyHorizontalJensenCenter L U)
        (conreyHorizontalJensenOuterRadius L) →
      ‖conreyDegreeOneV1 (49 / 100) 0 (51 / 50) L z‖ ≤
        C * (conreyHorizontalJensenHeightBase L U) ^ 5 := by
  rcases exists_norm_riemannZeta_add_deriv_le_conreyHorizontalJensenOuterClosedBall with
    ⟨Cz, hCz, hzeta⟩
  refine ⟨32 * Cz, by nlinarith, ?_⟩
  intro L U hL hU z hz
  let H : ℝ := conreyHorizontalJensenHeightBase L U
  have hH : 1 ≤ H := by
    simpa only [H] using one_le_conreyHorizontalJensenHeightBase hL hU
  have hCz0 : 0 ≤ Cz := by linarith
  have hH4nonneg : 0 ≤ H ^ 4 := by positivity
  have hH5nonneg : 0 ≤ H ^ 5 := by positivity
  have hH4leH5 : H ^ 4 ≤ H ^ 5 := by
    calc
      H ^ 4 = H ^ 4 * 1 := by ring
      _ ≤ H ^ 4 * H := mul_le_mul_of_nonneg_left hH hH4nonneg
      _ = H ^ 5 := by ring
  have hzsum : ‖riemannZeta z‖ + ‖deriv riemannZeta z‖ ≤ Cz * H ^ 4 := by
    simpa only [H] using hzeta hL hU hz
  have hzetaOnly : ‖riemannZeta z‖ ≤ Cz * H ^ 4 :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans hzsum
  have hderivOnly : ‖deriv riemannZeta z‖ ≤ Cz * H ^ 4 :=
    (le_add_of_nonneg_left (norm_nonneg _)).trans hzsum
  have hlogUpper : Real.log (H + 2) ≤ H + 1 := by
    calc
      Real.log (H + 2) ≤ H + 2 - 1 :=
        Real.log_le_sub_one_of_pos (by linarith : 0 < H + 2)
      _ = H + 1 := by ring
  have harchRaw :=
    norm_logDeriv_conreyH_le_conreyHorizontalJensenOuterClosedBall hL hU hz
  have harch : ‖deriv conreyH z / conreyH z‖ ≤ 30 * H := by
    dsimp only [conreyHorizontalJensenArchimedeanConstant] at harchRaw
    simpa only [H] using harchRaw.trans (by nlinarith)
  have hg : ‖((49 / 100 : ℂ) + I * (0 : ℂ))‖ ≤ 1 := by norm_num
  have hLpos : 0 < L := by linarith
  have hg1 : ‖(((51 / 50) / L : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (by norm_num) hLpos.le)]
    exact (div_le_one hLpos).2 (by norm_num; linarith)
  have hfirst :
      ‖((49 / 100 : ℂ) + I * (0 : ℂ)) * riemannZeta z‖ ≤
        Cz * H ^ 4 := by
    rw [norm_mul]
    calc
      ‖(49 / 100 : ℂ) + I * (0 : ℂ)‖ * ‖riemannZeta z‖ ≤
          1 * ‖riemannZeta z‖ :=
        mul_le_mul_of_nonneg_right hg (norm_nonneg _)
      _ ≤ Cz * H ^ 4 := by simpa using hzetaOnly
  have hinner :
      ‖deriv riemannZeta z +
          (deriv conreyH z / conreyH z) * riemannZeta z‖ ≤
        Cz * H ^ 4 + (30 * H) * (Cz * H ^ 4) := by
    calc
      _ ≤ ‖deriv riemannZeta z‖ +
          ‖(deriv conreyH z / conreyH z) * riemannZeta z‖ :=
        norm_add_le _ _
      _ = ‖deriv riemannZeta z‖ +
          ‖deriv conreyH z / conreyH z‖ * ‖riemannZeta z‖ := by
        rw [norm_mul]
      _ ≤ Cz * H ^ 4 + (30 * H) * (Cz * H ^ 4) := by
        gcongr
  have hsecond :
      ‖((((51 / 50) / L : ℝ) : ℂ) *
          (deriv riemannZeta z +
            (deriv conreyH z / conreyH z) * riemannZeta z))‖ ≤
        Cz * H ^ 4 + (30 * H) * (Cz * H ^ 4) := by
    rw [norm_mul]
    calc
      ‖(((51 / 50) / L : ℝ) : ℂ)‖ *
          ‖deriv riemannZeta z +
            (deriv conreyH z / conreyH z) * riemannZeta z‖ ≤
        1 * ‖deriv riemannZeta z +
            (deriv conreyH z / conreyH z) * riemannZeta z‖ :=
          mul_le_mul_of_nonneg_right hg1 (norm_nonneg _)
      _ ≤ Cz * H ^ 4 + (30 * H) * (Cz * H ^ 4) := by
        simpa using hinner
  unfold conreyDegreeOneV1
  have hraw := (norm_add_le
    (((49 / 100 : ℂ) + I * (0 : ℂ)) * riemannZeta z)
    (((((51 / 50) / L : ℝ) : ℂ)) *
      (deriv riemannZeta z +
        (deriv conreyH z / conreyH z) * riemannZeta z))).trans
      (add_le_add hfirst hsecond)
  have hlead :
      (((49 / 100 : ℝ) : ℂ) + I * ((0 : ℝ) : ℂ)) =
        (49 / 100 : ℂ) + I * (0 : ℂ) := by norm_num
  calc
    _ ≤
      Cz * H ^ 4 +
        (Cz * H ^ 4 + (30 * H) * (Cz * H ^ 4)) := by
      rw [hlead]
      exact hraw
    _ ≤ (32 * Cz) * H ^ 5 := by
      have hscale : Cz * H ^ 4 ≤ Cz * H ^ 5 :=
        mul_le_mul_of_nonneg_left hH4leH5 hCz0
      nlinarith [mul_nonneg hCz0 hH5nonneg]

/-- The actual product `V1 * B` obeys the polynomial outer-circle bound used
by the Jensen argument.  The upper cutoff hypothesis is retained in the
public interface for the later logarithmic simplification, although the
pointwise finite-sum estimate itself is stronger. -/
theorem exists_norm_conreyExplicitMollifiedV1_le_conreyHorizontalJensenOuterClosedBall :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Y : ℕ} {sigma0 L U : ℝ}, 2 ≤ Y →
      (Y : ℝ) ≤ Real.exp L → sigma0 ≤ 1 / 2 → 40000 ≤ L →
      conreyHorizontalRightEdge L + 1 ≤ U → ∀ {z : ℂ},
      z ∈ Metric.closedBall (conreyHorizontalJensenCenter L U)
        (conreyHorizontalJensenOuterRadius L) →
      ‖conreyMollifiedDegreeOneV1
          (49 / 100) 0 (51 / 50) L Y sigma0 conreyExplicitP z‖ ≤
        C * (Y : ℝ) * (conreyHorizontalJensenHeightBase L U) ^ 6 *
          (L + 2) ^ 2 := by
  rcases exists_norm_conreyExplicitDegreeOneV1_le_conreyHorizontalJensenOuterClosedBall with
    ⟨C, hC, hV⟩
  refine ⟨C, hC, ?_⟩
  intro Y sigma0 L U hY _hYtop hsigma0 hL hU z hz
  let H : ℝ := conreyHorizontalJensenHeightBase L U
  have hH : 1 ≤ H := by
    simpa only [H] using one_le_conreyHorizontalJensenHeightBase hL hU
  have hV' :
      ‖conreyDegreeOneV1 (49 / 100) 0 (51 / 50) L z‖ ≤ C * H ^ 5 := by
    simpa only [H] using hV hL hU hz
  have hzre : (0 : ℝ) ≤ z.re := by
    have := quarter_le_re_of_mem_conreyHorizontalJensenOuterClosedBall hL hz
    linarith
  have hB := norm_conreyExplicitMollifier_le_natCast_of_re_nonneg
    hY hsigma0 hzre
  have hC0 : 0 ≤ C := by linarith
  have hY0 : (0 : ℝ) ≤ Y := by positivity
  have hH5nonneg : 0 ≤ H ^ 5 := by positivity
  have hH6nonneg : 0 ≤ H ^ 6 := by positivity
  have hH5leH6 : H ^ 5 ≤ H ^ 6 := by
    calc
      H ^ 5 = H ^ 5 * 1 := by ring
      _ ≤ H ^ 5 * H := mul_le_mul_of_nonneg_left hH hH5nonneg
      _ = H ^ 6 := by ring
  have hLplus : 1 ≤ (L + 2) ^ 2 := by nlinarith [sq_nonneg (L + 2)]
  have hshape : H ^ 5 ≤ H ^ 6 * (L + 2) ^ 2 := by
    calc
      H ^ 5 ≤ H ^ 6 := hH5leH6
      _ = H ^ 6 * 1 := by ring
      _ ≤ H ^ 6 * (L + 2) ^ 2 :=
        mul_le_mul_of_nonneg_left hLplus hH6nonneg
  rw [conreyMollifiedDegreeOneV1, norm_mul]
  calc
    ‖conreyDegreeOneV1 (49 / 100) 0 (51 / 50) L z‖ *
        ‖conreyMollifier Y sigma0 conreyExplicitP z‖ ≤
      (C * H ^ 5) * (Y : ℝ) :=
        mul_le_mul hV' hB (norm_nonneg _) (mul_nonneg hC0 hH5nonneg)
    _ = (C * (Y : ℝ)) * H ^ 5 := by ring
    _ ≤ (C * (Y : ℝ)) * (H ^ 6 * (L + 2) ^ 2) :=
      mul_le_mul_of_nonneg_left hshape (mul_nonneg hC0 hY0)
    _ = C * (Y : ℝ) * H ^ 6 * (L + 2) ^ 2 := by ring

end HardyTheorem
