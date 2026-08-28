import HardyTheorem.ConreyMollifierRightEdge
import HardyTheorem.ConreyV1RightEdge

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

end HardyTheorem
