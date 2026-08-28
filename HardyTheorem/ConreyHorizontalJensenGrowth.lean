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

end HardyTheorem
