import HardyTheorem.ConreyMollifierRightEdge
import HardyTheorem.ConreyV1RightEdge
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Conrey's explicit height main term on the global right vertical

This file specializes the reusable height-dependent `V1` main term to
Conrey's degree-one certificate

`g = 49/100`, `g0 = 0`, `g1 = 51/50`.

The first layer is deliberately elementary: it records the exact real main
term, its interval bounds, and the height-compensation identity.  Product and
integral estimates are built on top of these facts rather than replacing the
height variation by a constant normalization.
-/

open Complex

namespace HardyTheorem

/-- The height-dependent main term for Conrey's explicit degree-one choice. -/
noncomputable def conreyExplicitDegreeOneHeightMain (L t : ℝ) : ℂ :=
  conreyDegreeOneHeightMain (49 / 100) 0 (51 / 50) L t

/-- Exact real formula for the explicit height main term. -/
theorem conreyExplicitDegreeOneHeightMain_eq (L t : ℝ) :
    conreyExplicitDegreeOneHeightMain L t =
      (((49 / 100 + 51 / (100 * L) * Real.log (t / (2 * Real.pi))) : ℝ) : ℂ) := by
  unfold conreyExplicitDegreeOneHeightMain conreyDegreeOneHeightMain
  push_cast
  ring

@[simp] theorem conreyExplicitDegreeOneHeightMain_re (L t : ℝ) :
    (conreyExplicitDegreeOneHeightMain L t).re =
      49 / 100 + 51 / (100 * L) * Real.log (t / (2 * Real.pi)) := by
  rw [conreyExplicitDegreeOneHeightMain_eq]
  simp only [Complex.ofReal_re]

@[simp] theorem conreyExplicitDegreeOneHeightMain_im (L t : ℝ) :
    (conreyExplicitDegreeOneHeightMain L t).im = 0 := by
  rw [conreyExplicitDegreeOneHeightMain_eq]
  simp only [Complex.ofReal_im]

private theorem log_two_mul_pi_le_two : Real.log (2 * Real.pi) ≤ 2 := by
  have h1 : 2 * Real.pi ≤ Real.exp 2 := by
    have hpi := Real.pi_lt_d2
    have he := Real.exp_one_gt_d9
    have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [he2]
    nlinarith
  calc
    Real.log (2 * Real.pi) ≤ Real.log (Real.exp 2) :=
      Real.log_le_log (by positivity) h1
    _ = 2 := Real.log_exp 2

/-- On the full global range `t >= 1`, the explicit height main term is
uniformly bounded below by `1/3` once `L >= exp 2`. -/
theorem one_third_le_conreyExplicitDegreeOneHeightMain_re
    {L t : ℝ} (hL : Real.exp 2 ≤ L) (ht : 1 ≤ t) :
    (1 / 3 : ℝ) ≤ (conreyExplicitDegreeOneHeightMain L t).re := by
  have hLpos : 0 < L := (Real.exp_pos 2).trans_le hL
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht
  have hlogratio : -2 ≤ Real.log (t / (2 * Real.pi)) := by
    rw [Real.log_div (by positivity) (by positivity)]
    linarith [log_two_mul_pi_le_two]
  have he : 7 < Real.exp 2 := by
    have he1 := Real.exp_one_gt_d9
    have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [he2]
    nlinarith
  have hL7 : 7 < L := he.trans_le hL
  rw [conreyExplicitDegreeOneHeightMain_re]
  calc
    (1 / 3 : ℝ) ≤ 49 / 100 + 51 / (100 * L) * (-2) := by
      field_simp [hLpos.ne']
      nlinarith
    _ ≤ 49 / 100 + 51 / (100 * L) * Real.log (t / (2 * Real.pi)) := by
      gcongr

/-- If `t <= exp L`, the explicit height main term is at most one. -/
theorem conreyExplicitDegreeOneHeightMain_re_le_one
    {L t : ℝ} (hL : 0 < L) (ht : 0 < t) (htop : t ≤ Real.exp L) :
    (conreyExplicitDegreeOneHeightMain L t).re ≤ 1 := by
  have htwoPi : 1 ≤ 2 * Real.pi := by
    have hpi := Real.pi_gt_three
    nlinarith
  have hratioPos : 0 < t / (2 * Real.pi) := by positivity
  have hratioLe : t / (2 * Real.pi) ≤ Real.exp L := by
    calc
      t / (2 * Real.pi) ≤ t := div_le_self (le_of_lt ht) htwoPi
      _ ≤ Real.exp L := htop
  have hlog : Real.log (t / (2 * Real.pi)) ≤ L := by
    calc
      Real.log (t / (2 * Real.pi)) ≤ Real.log (Real.exp L) :=
        Real.log_le_log hratioPos hratioLe
      _ = L := Real.log_exp L
  rw [conreyExplicitDegreeOneHeightMain_re]
  have hc : 0 ≤ 51 / (100 * L) := by positivity
  calc
    49 / 100 + 51 / (100 * L) * Real.log (t / (2 * Real.pi)) ≤
        49 / 100 + 51 / (100 * L) * L := by gcongr
    _ = 1 := by field_simp [hL.ne']; ring

/-- Exact global height-compensation identity when the top height is `exp L`. -/
theorem one_sub_conreyExplicitDegreeOneHeightMain_re_eq
    {L t : ℝ} (hL : L ≠ 0) (ht : 0 < t) :
    1 - (conreyExplicitDegreeOneHeightMain L t).re =
      51 / (100 * L) * Real.log ((2 * Real.pi * Real.exp L) / t) := by
  rw [conreyExplicitDegreeOneHeightMain_re,
    Real.log_div (by positivity : t ≠ 0) (by positivity : 2 * Real.pi ≠ 0),
    Real.log_div (by positivity : 2 * Real.pi * Real.exp L ≠ 0) ht.ne',
    Real.log_mul (by positivity : 2 * Real.pi ≠ 0) (Real.exp_ne_zero L),
    Real.log_exp]
  field_simp [hL]
  ring

/-- The complex norm of the explicit main term equals its real part on the
global range where the latter is positive. -/
theorem norm_conreyExplicitDegreeOneHeightMain_eq_re
    {L t : ℝ} (hL : Real.exp 2 ≤ L) (ht : 1 ≤ t) :
    ‖conreyExplicitDegreeOneHeightMain L t‖ =
      (conreyExplicitDegreeOneHeightMain L t).re := by
  have hnonneg : 0 ≤ (conreyExplicitDegreeOneHeightMain L t).re :=
    (by norm_num : (0 : ℝ) ≤ 1 / 3).trans
      (one_third_le_conreyExplicitDegreeOneHeightMain_re hL ht)
  rw [conreyExplicitDegreeOneHeightMain_eq, Complex.norm_real, Real.norm_eq_abs]
  simp only [Complex.ofReal_re]
  rw [abs_of_nonneg]
  simpa only [conreyExplicitDegreeOneHeightMain_re] using hnonneg

/-- The concrete product appearing on Conrey's moving global right edge. -/
noncomputable def conreyExplicitRightVerticalProduct
    (Y : ℕ) (sigma0 L t : ℝ) : ℂ :=
  let s : ℂ := ((2 * Real.log L : ℝ) : ℂ) + I * t
  conreyDegreeOneV1 (49 / 100) 0 (51 / 50) L s *
    conreyMollifier Y sigma0 conreyExplicitP s

/-- On the high part of the global right vertical, the concrete `V1 B`
product is within `79/L` of the height-dependent real main term. -/
theorem norm_conreyExplicitRightVerticalProduct_sub_heightMain_le
    {Y : ℕ} {sigma0 L t : ℝ}
    (hY : 2 ≤ Y) (hsigma0 : sigma0 ≤ 1 / 2)
    (hL : 600 ≤ L) (ht : 2 * Real.log L ≤ t)
    (htop : t ≤ Real.exp L) :
    ‖conreyExplicitRightVerticalProduct Y sigma0 L t -
        conreyExplicitDegreeOneHeightMain L t‖ ≤ 79 / L := by
  have hLpos : 0 < L := by linarith
  have he2lt : Real.exp 2 < 9 := by
    have he := Real.exp_one_lt_three
    have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [he2]
    nlinarith [Real.exp_pos 1]
  have hLexp2 : Real.exp 2 ≤ L := he2lt.le.trans (by linarith)
  have hlogL : 2 ≤ Real.log L := by
    have hmono := Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (Real.exp_pos 2)) (Set.mem_Ioi.mpr hLpos) hLexp2
    simpa only [Real.log_exp] using hmono
  have ht2 : 2 ≤ t := by linarith
  have ht1 : 1 ≤ t := by linarith
  let s : ℂ := ((2 * Real.log L : ℝ) : ℂ) + I * t
  let V : ℂ := conreyDegreeOneV1 (49 / 100) 0 (51 / 50) L s
  let M : ℂ := conreyMollifier Y sigma0 conreyExplicitP s
  let A : ℂ := conreyExplicitDegreeOneHeightMain L t
  have hre : s.re = 2 * Real.log L := by simp [s]
  have him : s.im = t := by simp [s]
  have hVraw :
      ‖V - A‖ ≤ (3 * ‖A‖ + 34 * |(51 / 50 : ℝ)|) / L := by
    simpa only [V, A, conreyExplicitDegreeOneHeightMain] using
      norm_conreyDegreeOneV1_sub_heightMain_movingRight_le
        (g := (49 / 100 : ℝ)) (g0 := 0) (g1 := (51 / 50 : ℝ))
        (s := s) hLexp2 hre him ht2 (by simpa only [hre] using ht)
  have hAnorm : ‖A‖ ≤ 1 := by
    rw [show A = conreyExplicitDegreeOneHeightMain L t by rfl,
      norm_conreyExplicitDegreeOneHeightMain_eq_re hLexp2 ht1]
    exact conreyExplicitDegreeOneHeightMain_re_le_one hLpos (by linarith) htop
  have hV : ‖V - A‖ ≤ 38 / L := hVraw.trans (by
    apply div_le_div_of_nonneg_right _ hLpos.le
    norm_num at hAnorm ⊢
    nlinarith)
  have hLexp1 : Real.exp 1 ≤ L :=
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)).trans hLexp2
  have hM : ‖M - 1‖ ≤ 3 / L := by
    dsimp [M, s]
    convert norm_conreyExplicitMollifier_movingRight_sub_one_le
      hY hsigma0 hLexp1 t using 1
    · push_cast
      rfl
  have hMnorm : ‖M‖ ≤ 2 := by
    calc
      ‖M‖ = ‖(M - 1) + 1‖ := by ring_nf
      _ ≤ ‖M - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 3 / L + 1 := by
        simpa only [norm_one, add_comm] using add_le_add_right hM 1
      _ ≤ 2 := by
        have hL3 : 3 ≤ L := by linarith
        have h3div : 3 / L ≤ 1 := (div_le_one hLpos).mpr hL3
        linarith
  change ‖V * M - A‖ ≤ 79 / L
  rw [show V * M - A = (V - A) * M + A * (M - 1) by ring]
  calc
    ‖(V - A) * M + A * (M - 1)‖ ≤
        ‖V - A‖ * ‖M‖ + ‖A‖ * ‖M - 1‖ := by
      simpa only [norm_mul] using norm_add_le ((V - A) * M) (A * (M - 1))
    _ ≤ (38 / L) * 2 + 1 * (3 / L) := by
      exact add_le_add
        (mul_le_mul hV hMnorm (norm_nonneg _) (by positivity))
        (mul_le_mul hAnorm hM (norm_nonneg _) (by positivity))
    _ = 79 / L := by ring

/-- The high-part right-vertical product is nonzero by its explicit distance
from the positive main term; no abstract nonvanishing assumption is used. -/
theorem conreyExplicitRightVerticalProduct_ne_zero
    {Y : ℕ} {sigma0 L t : ℝ}
    (hY : 2 ≤ Y) (hsigma0 : sigma0 ≤ 1 / 2)
    (hL : 600 ≤ L) (ht : 2 * Real.log L ≤ t)
    (htop : t ≤ Real.exp L) :
    conreyExplicitRightVerticalProduct Y sigma0 L t ≠ 0 := by
  have hLpos : 0 < L := by linarith
  have he2lt : Real.exp 2 < 9 := by
    have he := Real.exp_one_lt_three
    have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [he2]
    nlinarith [Real.exp_pos 1]
  have hLexp2 : Real.exp 2 ≤ L := he2lt.le.trans (by linarith)
  have hlogL : 2 ≤ Real.log L := by
    have hmono := Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (Real.exp_pos 2)) (Set.mem_Ioi.mpr hLpos) hLexp2
    simpa only [Real.log_exp] using hmono
  have ht1 : 1 ≤ t := by linarith
  have hmain : (1 / 3 : ℝ) ≤ ‖conreyExplicitDegreeOneHeightMain L t‖ := by
    rw [norm_conreyExplicitDegreeOneHeightMain_eq_re hLexp2 ht1]
    exact one_third_le_conreyExplicitDegreeOneHeightMain_re hLexp2 ht1
  have herr := norm_conreyExplicitRightVerticalProduct_sub_heightMain_le
    hY hsigma0 hL ht htop
  intro hzero
  rw [hzero, zero_sub, norm_neg] at herr
  have hsmall : (79 / L : ℝ) ≤ 79 / 600 := by
    gcongr
  have : (1 / 3 : ℝ) ≤ 79 / 600 := hmain.trans (herr.trans hsmall)
  norm_num at this

/-- A quantitative logarithm stability estimate on the positive half-line.
The asymmetric lower bounds are the ones needed for the explicit Conrey
product and its height-dependent main term. -/
theorem abs_log_sub_log_le_six_mul_abs_sub
    {x a : ℝ} (hx : 1 / 6 ≤ x) (ha : 1 / 3 ≤ a) :
    |Real.log x - Real.log a| ≤ 6 * |x - a| := by
  have hxpos : 0 < x := by linarith
  have hapos : 0 < a := by linarith
  by_cases hax : a ≤ x
  · have hlog : 0 ≤ Real.log x - Real.log a := by
      exact sub_nonneg.mpr (Real.log_le_log hapos hax)
    rw [abs_of_nonneg hlog, ← Real.log_div hxpos.ne' hapos.ne']
    calc
      Real.log (x / a) ≤ x / a - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hxpos hapos)
      _ = (x - a) / a := by field_simp [hapos.ne']
      _ ≤ 3 * (x - a) := by
        have hinv : a⁻¹ ≤ 3 := by
          rw [inv_le_iff_one_le_mul₀ hapos]
          linarith
        rw [div_eq_mul_inv]
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left hinv (sub_nonneg.mpr hax)
      _ ≤ 6 * |x - a| := by
        rw [abs_of_nonneg (sub_nonneg.mpr hax)]
        linarith
  · have hxa : x ≤ a := le_of_not_ge hax
    have hlog : Real.log x - Real.log a ≤ 0 := by
      exact sub_nonpos.mpr (Real.log_le_log hxpos hxa)
    rw [abs_of_nonpos hlog]
    rw [show -(Real.log x - Real.log a) = Real.log a - Real.log x by ring,
      ← Real.log_div hapos.ne' hxpos.ne']
    calc
      Real.log (a / x) ≤ a / x - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hapos hxpos)
      _ = (a - x) / x := by field_simp [hxpos.ne']
      _ ≤ 6 * (a - x) := by
        have hinv : x⁻¹ ≤ 6 := by
          rw [inv_le_iff_one_le_mul₀ hxpos]
          linarith
        rw [div_eq_mul_inv]
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left hinv (sub_nonneg.mpr hxa)
      _ = 6 * |x - a| := by
        rw [abs_of_nonpos (sub_nonpos.mpr hxa)]
        ring

/-- On `[1/3,1]`, the logarithm is controlled by the distance from one. -/
theorem abs_log_le_three_mul_one_sub
    {a : ℝ} (ha : 1 / 3 ≤ a) (ha1 : a ≤ 1) :
    |Real.log a| ≤ 3 * (1 - a) := by
  have hapos : 0 < a := by linarith
  have hlog : Real.log a ≤ 0 := Real.log_nonpos hapos.le ha1
  rw [abs_of_nonpos hlog, ← Real.log_inv]
  calc
    Real.log a⁻¹ ≤ a⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hapos)
    _ = (1 - a) / a := by field_simp [hapos.ne']
    _ ≤ 3 * (1 - a) := by
      have hinv : a⁻¹ ≤ 3 := by
        rw [inv_le_iff_one_le_mul₀ hapos]
        linarith
      rw [div_eq_mul_inv]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left hinv (sub_nonneg.mpr ha1)

/-- The height-compensation logarithm has only linear total mass.  This is
the elementary integral which recovers the factor `1/L` on the global right
vertical. -/
theorem integral_log_conrey_height_compensation_one_exp_le
    {L : ℝ} (hL : 0 ≤ L) :
    (∫ t in (1 : ℝ)..Real.exp L,
      Real.log ((2 * Real.pi * Real.exp L) / t)) ≤ 3 * Real.exp L := by
  have honeexp : (1 : ℝ) ≤ Real.exp L := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hL
  have hCpos : 0 < 2 * Real.pi * Real.exp L := by positivity
  have heq :
      (∫ t in (1 : ℝ)..Real.exp L,
        Real.log ((2 * Real.pi * Real.exp L) / t)) =
      ∫ t in (1 : ℝ)..Real.exp L,
        (Real.log (2 * Real.pi * Real.exp L) - Real.log t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le honeexp] at ht
    exact Real.log_div hCpos.ne' (by linarith [ht.1])
  rw [heq, intervalIntegral.integral_sub
      (intervalIntegrable_const : IntervalIntegrable
        (fun _t : ℝ => Real.log (2 * Real.pi * Real.exp L))
          MeasureTheory.volume 1 (Real.exp L))
      intervalIntegral.intervalIntegrable_log',
    intervalIntegral.integral_const, integral_log]
  simp only [smul_eq_mul]
  have hlogC : Real.log (2 * Real.pi * Real.exp L) =
      Real.log (2 * Real.pi) + L := by
    rw [Real.log_mul (by positivity : 2 * Real.pi ≠ 0) (Real.exp_ne_zero L),
      Real.log_exp]
  rw [hlogC, Real.log_exp, Real.log_one]
  have hlogTwoPi : Real.log (2 * Real.pi) ≤ 2 := by
    exact log_two_mul_pi_le_two
  have hlogCnonneg : 0 ≤ Real.log (2 * Real.pi) + L := by
    have : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by
      have hpi := Real.pi_gt_three
      nlinarith)
    linarith
  nlinarith [Real.exp_pos L]

/-- The explicit `V1 B` product is continuous along the moving right
vertical.  Analyticity supplies continuity of `V1`, while the finite
mollifier is entire. -/
theorem continuous_conreyExplicitRightVerticalProduct
    {Y : ℕ} {sigma0 L : ℝ} (hL : Real.exp 2 ≤ L) :
    Continuous (fun t : ℝ =>
      conreyExplicitRightVerticalProduct Y sigma0 L t) := by
  have hLpos : 0 < L := (Real.exp_pos 2).trans_le hL
  have hlogL : 2 ≤ Real.log L := by
    have hmono := Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (Real.exp_pos 2)) (Set.mem_Ioi.mpr hLpos) hL
    simpa only [Real.log_exp] using hmono
  rw [continuous_iff_continuousAt]
  intro t
  have hsre :
      0 < (((2 * Real.log L : ℝ) : ℂ) + I * t).re := by
    simp
    linarith
  have hsne : (((2 * Real.log L : ℝ) : ℂ) + I * t) ≠ 1 := by
    intro heq
    have hre := congrArg Complex.re heq
    simp at hre
    linarith
  have hline : ContinuousAt
      (fun u : ℝ => ((2 * Real.log L : ℝ) : ℂ) + I * u) t := by
    fun_prop
  have hVbase :=
    (analyticAt_conreyDegreeOneV1_of_re_pos_of_ne_one
      (g := (49 / 100 : ℝ)) (g0 := 0) (g1 := (51 / 50 : ℝ))
      (L := L) hsre hsne).continuousAt
  have hV : ContinuousAt (fun u : ℝ =>
      conreyDegreeOneV1 (49 / 100) 0 (51 / 50) L
        (((2 * Real.log L : ℝ) : ℂ) + I * u)) t :=
    ContinuousAt.comp'
      (f := fun u : ℝ => ((2 * Real.log L : ℝ) : ℂ) + I * u)
      (g := conreyDegreeOneV1 (49 / 100) 0 (51 / 50) L)
      (x := t) hVbase hline
  have hMbase :=
    ((analyticOnNhd_conreyMollifier Y sigma0 conreyExplicitP)
      (((2 * Real.log L : ℝ) : ℂ) + I * t) (by simp)).continuousAt
  have hM : ContinuousAt (fun u : ℝ =>
      conreyMollifier Y sigma0 conreyExplicitP
        (((2 * Real.log L : ℝ) : ℂ) + I * u)) t :=
    ContinuousAt.comp'
      (f := fun u : ℝ => ((2 * Real.log L : ℝ) : ℂ) + I * u)
      (g := conreyMollifier Y sigma0 conreyExplicitP)
      (x := t) hMbase hline
  unfold conreyExplicitRightVerticalProduct
  change ContinuousAt
    ((fun u : ℝ => conreyDegreeOneV1 (49 / 100) 0 (51 / 50) L
        (((2 * Real.log L : ℝ) : ℂ) + I * u)) *
      (fun u : ℝ => conreyMollifier Y sigma0 conreyExplicitP
        (((2 * Real.log L : ℝ) : ℂ) + I * u))) t
  exact hV.mul hM

/-- Pointwise `O(1/L)` control of the logarithm on the high part of Conrey's
global right vertical.  The second term retains the exact height compensation
which is integrable without losing a factor of `L`. -/
theorem abs_log_norm_conreyExplicitRightVerticalProduct_le
    {Y : ℕ} {sigma0 L t : ℝ}
    (hY : 2 ≤ Y) (hsigma0 : sigma0 ≤ 1 / 2)
    (hL : 600 ≤ L) (ht : 2 * Real.log L ≤ t)
    (htop : t ≤ Real.exp L) :
    |Real.log ‖conreyExplicitRightVerticalProduct Y sigma0 L t‖| ≤
      500 / L + (2 / L) * Real.log ((2 * Real.pi * Real.exp L) / t) := by
  have hLpos : 0 < L := by linarith
  have he2lt : Real.exp 2 < 9 := by
    have he := Real.exp_one_lt_three
    have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [he2]
    nlinarith [Real.exp_pos 1]
  have hLexp2 : Real.exp 2 ≤ L := he2lt.le.trans (by linarith)
  have hlogL : 2 ≤ Real.log L := by
    have hmono := Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (Real.exp_pos 2)) (Set.mem_Ioi.mpr hLpos) hLexp2
    simpa only [Real.log_exp] using hmono
  have ht1 : 1 ≤ t := by linarith
  have htpos : 0 < t := by linarith
  let P : ℂ := conreyExplicitRightVerticalProduct Y sigma0 L t
  let A : ℂ := conreyExplicitDegreeOneHeightMain L t
  have hAeq : ‖A‖ = A.re := by
    simpa only [A] using norm_conreyExplicitDegreeOneHeightMain_eq_re hLexp2 ht1
  have hAlower : (1 / 3 : ℝ) ≤ ‖A‖ := by
    rw [hAeq]
    simpa only [A] using one_third_le_conreyExplicitDegreeOneHeightMain_re hLexp2 ht1
  have hAupper : ‖A‖ ≤ 1 := by
    rw [hAeq]
    simpa only [A] using
      conreyExplicitDegreeOneHeightMain_re_le_one hLpos htpos htop
  have herr : ‖P - A‖ ≤ 79 / L := by
    simpa only [P, A] using
      norm_conreyExplicitRightVerticalProduct_sub_heightMain_le
        hY hsigma0 hL ht htop
  have hnormdiff : |‖P‖ - ‖A‖| ≤ 79 / L :=
    (abs_norm_sub_norm_le P A).trans herr
  have hP_lower : (1 / 6 : ℝ) ≤ ‖P‖ := by
    have hsmall : (79 / L : ℝ) ≤ 79 / 600 := by gcongr
    have hleft : ‖A‖ - ‖P‖ ≤ 79 / L := by
      have := (le_abs_self (‖A‖ - ‖P‖)).trans
        (by simpa only [abs_sub_comm] using hnormdiff)
      exact this
    nlinarith [hAlower, hleft, hsmall]
  have hperturb :
      |Real.log ‖P‖ - Real.log ‖A‖| ≤ 474 / L := by
    calc
      |Real.log ‖P‖ - Real.log ‖A‖| ≤ 6 * |‖P‖ - ‖A‖| :=
        abs_log_sub_log_le_six_mul_abs_sub hP_lower hAlower
      _ ≤ 6 * (79 / L) := by gcongr
      _ = 474 / L := by ring
  have hmainlog : |Real.log ‖A‖| ≤ 3 * (1 - ‖A‖) :=
    abs_log_le_three_mul_one_sub hAlower hAupper
  have hgap :
      1 - ‖A‖ = 51 / (100 * L) *
        Real.log ((2 * Real.pi * Real.exp L) / t) := by
    rw [hAeq]
    simpa only [A] using
      one_sub_conreyExplicitDegreeOneHeightMain_re_eq hLpos.ne' htpos
  have htwoPi : 1 ≤ 2 * Real.pi := by
    have hpi := Real.pi_gt_three
    nlinarith
  have hratio : 1 ≤ (2 * Real.pi * Real.exp L) / t := by
    rw [le_div_iff₀ htpos]
    simpa only [one_mul] using
      htop.trans (le_mul_of_one_le_left (Real.exp_nonneg L) htwoPi)
  have hlogratio : 0 ≤ Real.log ((2 * Real.pi * Real.exp L) / t) :=
    Real.log_nonneg hratio
  have hmainlog' :
      |Real.log ‖A‖| ≤ (2 / L) *
        Real.log ((2 * Real.pi * Real.exp L) / t) := by
    rw [hgap] at hmainlog
    calc
      |Real.log ‖A‖| ≤ 3 *
          (51 / (100 * L) * Real.log ((2 * Real.pi * Real.exp L) / t)) :=
        hmainlog
      _ = (3 * (51 / (100 * L))) *
          Real.log ((2 * Real.pi * Real.exp L) / t) := by ring
      _ ≤ (2 / L) * Real.log ((2 * Real.pi * Real.exp L) / t) := by
        have hcoeff : 3 * (51 / (100 * L)) ≤ 2 / L := by
          field_simp [hLpos.ne']
          norm_num
        exact mul_le_mul_of_nonneg_right hcoeff hlogratio
  calc
    |Real.log ‖conreyExplicitRightVerticalProduct Y sigma0 L t‖| =
        |Real.log ‖P‖| := by rfl
    _ = |(Real.log ‖P‖ - Real.log ‖A‖) + Real.log ‖A‖| := by ring_nf
    _ ≤ |Real.log ‖P‖ - Real.log ‖A‖| + |Real.log ‖A‖| := abs_add_le _ _
    _ ≤ 474 / L + (2 / L) *
        Real.log ((2 * Real.pi * Real.exp L) / t) :=
      add_le_add hperturb hmainlog'
    _ ≤ 500 / L + (2 / L) *
        Real.log ((2 * Real.pi * Real.exp L) / t) := by
      exact add_le_add
        (div_le_div_of_nonneg_right (by norm_num) hLpos.le) le_rfl

/-- The complete high part of the explicit right-vertical absolute logarithm
has the required `exp L / L` scale. -/
theorem integral_abs_log_norm_conreyExplicitRightVerticalProduct_high_le
    {Y : ℕ} {sigma0 L : ℝ}
    (hY : 2 ≤ Y) (hsigma0 : sigma0 ≤ 1 / 2) (hL : 600 ≤ L) :
    (∫ t in 2 * Real.log L..Real.exp L,
      |Real.log ‖conreyExplicitRightVerticalProduct Y sigma0 L t‖|) ≤
        506 * Real.exp L / L := by
  have hLpos : 0 < L := by linarith
  have he2lt : Real.exp 2 < 9 := by
    have he := Real.exp_one_lt_three
    have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [he2]
    nlinarith [Real.exp_pos 1]
  have hLexp2 : Real.exp 2 ≤ L := he2lt.le.trans (by linarith)
  have hlogL : 2 ≤ Real.log L := by
    have hmono := Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (Real.exp_pos 2)) (Set.mem_Ioi.mpr hLpos) hLexp2
    simpa only [Real.log_exp] using hmono
  have ha1 : (1 : ℝ) ≤ 2 * Real.log L := by linarith
  have hab : 2 * Real.log L ≤ Real.exp L := by
    have hlogLleL : Real.log L ≤ L := by
      have := Real.add_one_le_exp (Real.log L)
      rw [Real.exp_log hLpos] at this
      linarith
    have hehalf := Real.add_one_le_exp (L / 2)
    have hexpLarge : 2 * L ≤ Real.exp L := by
      rw [show L = L / 2 + L / 2 by ring, Real.exp_add]
      nlinarith [sq_nonneg (L / 2 - 1)]
    linarith
  let P : ℝ → ℂ := fun t => conreyExplicitRightVerticalProduct Y sigma0 L t
  let q : ℝ → ℝ := fun t => Real.log ((2 * Real.pi * Real.exp L) / t)
  let f : ℝ → ℝ := fun t => |Real.log ‖P t‖|
  let g : ℝ → ℝ := fun t => 500 / L + (2 / L) * q t
  have hPcont : Continuous P := by
    simpa only [P] using
      continuous_conreyExplicitRightVerticalProduct
        (Y := Y) (sigma0 := sigma0) hLexp2
  have hfcont : ContinuousOn f (Set.Icc (2 * Real.log L) (Real.exp L)) := by
    intro t htmem
    have hPne : P t ≠ 0 := by
      simpa only [P] using
        conreyExplicitRightVerticalProduct_ne_zero hY hsigma0 hL htmem.1 htmem.2
    have hnorm : ContinuousAt (fun u => ‖P u‖) t :=
      (continuous_norm.comp hPcont).continuousAt
    have hlog : ContinuousAt (fun u => Real.log ‖P u‖) t :=
      (Real.continuousAt_log (by simpa using hPne)).comp' hnorm
    exact (continuous_abs.continuousAt.comp' hlog).continuousWithinAt
  have hfint : IntervalIntegrable f MeasureTheory.volume
      (2 * Real.log L) (Real.exp L) := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le hab] using hfcont
  have hqcontFull : ContinuousOn q (Set.Icc 1 (Real.exp L)) := by
    intro t htmem
    have htpos : 0 < t := lt_of_lt_of_le (by norm_num) htmem.1
    have hratioAt : ContinuousAt
        (fun u : ℝ => (2 * Real.pi * Real.exp L) / u) t := by
      exact continuousAt_const.div₀ continuousAt_id htpos.ne'
    exact ((Real.continuousAt_log (by positivity)).comp' hratioAt).continuousWithinAt
  have hqintFull : IntervalIntegrable q MeasureTheory.volume 1 (Real.exp L) :=
    (by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le]
      · exact hqcontFull
      · simpa only [Real.exp_zero] using
          Real.exp_le_exp.mpr (show (0 : ℝ) ≤ L by linarith))
  have hqintHigh : IntervalIntegrable q MeasureTheory.volume
      (2 * Real.log L) (Real.exp L) :=
    hqintFull.mono_set (by
      rw [Set.uIcc_of_le hab, Set.uIcc_of_le (by
        simpa only [Real.exp_zero] using
          Real.exp_le_exp.mpr (show (0 : ℝ) ≤ L by linarith))]
      exact Set.Icc_subset_Icc ha1 le_rfl)
  have hgint : IntervalIntegrable g MeasureTheory.volume
      (2 * Real.log L) (Real.exp L) := by
    exact intervalIntegrable_const.add (hqintHigh.const_mul (2 / L))
  have hfg : ∀ t ∈ Set.Icc (2 * Real.log L) (Real.exp L), f t ≤ g t := by
    intro t htmem
    simpa only [f, g, P, q] using
      abs_log_norm_conreyExplicitRightVerticalProduct_le
        hY hsigma0 hL htmem.1 htmem.2
  have hmono : (∫ t in 2 * Real.log L..Real.exp L, f t) ≤
      ∫ t in 2 * Real.log L..Real.exp L, g t :=
    intervalIntegral.integral_mono_on hab hfint hgint hfg
  have hqnonneg : ∀ t ∈ Set.Ioc 1 (Real.exp L), 0 ≤ q t := by
    intro t htmem
    have htpos : 0 < t := lt_trans (by norm_num) htmem.1
    have htwoPi : 1 ≤ 2 * Real.pi := by
      have hpi := Real.pi_gt_three
      nlinarith
    apply Real.log_nonneg
    rw [le_div_iff₀ htpos]
    simpa only [one_mul] using htmem.2.trans
      (le_mul_of_one_le_left (Real.exp_nonneg L) htwoPi)
  have hqae : 0 ≤ᵐ[MeasureTheory.volume.restrict
      (Set.Ioc 1 (Real.exp L))] q :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
      (MeasureTheory.ae_of_all _ hqnonneg)
  have hqmono : (∫ t in 2 * Real.log L..Real.exp L, q t) ≤
      ∫ t in 1..Real.exp L, q t :=
    intervalIntegral.integral_mono_interval ha1 hab le_rfl hqae hqintFull
  have hqfull : (∫ t in 1..Real.exp L, q t) ≤ 3 * Real.exp L := by
    simpa only [q] using integral_log_conrey_height_compensation_one_exp_le
      (show (0 : ℝ) ≤ L by linarith)
  have hqhigh : (∫ t in 2 * Real.log L..Real.exp L, q t) ≤
      3 * Real.exp L := hqmono.trans hqfull
  have hconst :
      (Real.exp L - 2 * Real.log L) * (500 / L) ≤
        500 * Real.exp L / L := by
    field_simp [hLpos.ne']
    have : 0 ≤ Real.log L := by linarith
    nlinarith
  have hqscaled : (2 / L) *
      (∫ t in 2 * Real.log L..Real.exp L, q t) ≤
        6 * Real.exp L / L := by
    have := mul_le_mul_of_nonneg_left hqhigh (by positivity : 0 ≤ 2 / L)
    calc
      (2 / L) * (∫ t in 2 * Real.log L..Real.exp L, q t) ≤
          (2 / L) * (3 * Real.exp L) := this
      _ = 6 * Real.exp L / L := by ring
  calc
    (∫ t in 2 * Real.log L..Real.exp L,
      |Real.log ‖conreyExplicitRightVerticalProduct Y sigma0 L t‖|) =
        ∫ t in 2 * Real.log L..Real.exp L, f t := by rfl
    _ ≤ ∫ t in 2 * Real.log L..Real.exp L, g t := hmono
    _ = (Real.exp L - 2 * Real.log L) * (500 / L) +
        (2 / L) * (∫ t in 2 * Real.log L..Real.exp L, q t) := by
      rw [intervalIntegral.integral_add intervalIntegrable_const
        (hqintHigh.const_mul (2 / L)), intervalIntegral.integral_const,
        intervalIntegral.integral_const_mul]
      simp only [smul_eq_mul]
    _ ≤ 500 * Real.exp L / L + 6 * Real.exp L / L :=
      add_le_add hconst hqscaled
    _ = 506 * Real.exp L / L := by ring

end HardyTheorem
