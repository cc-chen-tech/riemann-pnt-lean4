import HardyTheorem.ConreyDigammaHeight
import HardyTheorem.ConreyZetaRightEdge

/-!
# Conrey's degree-one V1 on the moving right edge

This file retains the height-dependent archimedean main term and proves the
exact decomposition and a quantitative pointwise error bound.  A local
constant normalization on a proportional height block is not substituted
for the global-height main term.
-/

open Complex

namespace HardyTheorem

/-- The height-dependent main term of the degree-one `V1` factor. -/
noncomputable def conreyDegreeOneHeightMain
    (g g0 g1 L t : ℝ) : ℂ :=
  ((g : ℂ) + I * (g0 : ℂ)) +
    ((g1 / L : ℝ) : ℂ) *
      ((Real.log (t / (2 * Real.pi)) / 2 : ℝ) : ℂ)

/-- Exact subtraction identity separating the zeta tail, zeta derivative,
and archimedean height error. -/
theorem conreyDegreeOneV1_sub_heightMain_eq
    (g g0 g1 L t : ℝ) (s : ℂ) :
    conreyDegreeOneV1 g g0 g1 L s -
        conreyDegreeOneHeightMain g g0 g1 L t =
      conreyDegreeOneHeightMain g g0 g1 L t * (riemannZeta s - 1) +
        ((g1 / L : ℝ) : ℂ) * deriv riemannZeta s +
        ((g1 / L : ℝ) : ℂ) *
          (deriv conreyH s / conreyH s -
            ((Real.log (t / (2 * Real.pi)) / 2 : ℝ) : ℂ)) * riemannZeta s := by
  unfold conreyDegreeOneV1 conreyDegreeOneHeightMain
  ring

/-- Quantitative degree-one `V1` approximation on `Re s = 2 log L`.
The stronger scale `L >= exp 2` keeps the radius-one Cauchy disk for zeta'
inside `Re z >= 2`. -/
theorem norm_conreyDegreeOneV1_sub_heightMain_movingRight_le
    {g g0 g1 L t : ℝ} {s : ℂ}
    (hL : Real.exp 2 ≤ L)
    (hre : s.re = 2 * Real.log L) (him : s.im = t)
    (ht : 2 ≤ t) (hst : s.re ≤ t) :
    ‖conreyDegreeOneV1 g g0 g1 L s -
        conreyDegreeOneHeightMain g g0 g1 L t‖ ≤
      (3 * ‖conreyDegreeOneHeightMain g g0 g1 L t‖ + 34 * |g1|) / L := by
  have hLpos : 0 < L := (Real.exp_pos 2).trans_le hL
  have hlogL : 2 ≤ Real.log L := by
    have hmono := Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (Real.exp_pos 2)) (Set.mem_Ioi.mpr hLpos) hL
    simpa only [Real.log_exp] using hmono
  have hs4 : 4 ≤ s.re := by rw [hre]; linarith
  have hsEq : s = ((2 * Real.log L : ℝ) : ℂ) + I * t := by
    apply Complex.ext
    · simp [hre]
    · simp [him]
  have hExpOne : Real.exp 1 ≤ L :=
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)).trans hL
  have hzetaTail : ‖riemannZeta s - 1‖ ≤ 3 / L :=
    norm_riemannZeta_movingRight_sub_one_le hExpOne hre
  have hzetaNorm : ‖riemannZeta s‖ ≤ (5 / 3 : ℝ) :=
    (ZeroFreeRegion.norm_riemannZeta_le_re_zeta_two_of_two_le_re s
      (by linarith)).trans ZeroFreeRegion.riemannZeta_two_re_le_five_thirds
  have hzetaDeriv : ‖deriv riemannZeta s‖ ≤ (5 / 3 : ℝ) := by
    have hraw :=
      ZeroFreeRegion.norm_deriv_riemannZeta_sigma_it_le_re_zeta_two_div_radius_of_two_add_radius_le
        (σ := 2 * Real.log L) (t := t) (R := 1) (by norm_num) (by linarith)
    rw [hsEq]
    exact hraw.trans (by
      simpa using ZeroFreeRegion.riemannZeta_two_re_le_five_thirds)
  have hst' : 2 * Real.log L ≤ t := by simpa [hre] using hst
  have harch :
      ‖deriv conreyH s / conreyH s -
        ((Real.log (t / (2 * Real.pi)) / 2 : ℝ) : ℂ)‖ ≤ 8 := by
    rw [hsEq]
    exact norm_logDeriv_conreyH_sub_half_log_t_div_two_pi_le
      ht (by linarith) hst'
  have hcoeff : ‖((g1 / L : ℝ) : ℂ)‖ = |g1| / L := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hLpos]
  have hA0 : 0 ≤ ‖conreyDegreeOneHeightMain g g0 g1 L t‖ := norm_nonneg _
  have hg10 : 0 ≤ |g1| := abs_nonneg _
  rw [conreyDegreeOneV1_sub_heightMain_eq]
  calc
    ‖conreyDegreeOneHeightMain g g0 g1 L t * (riemannZeta s - 1) +
        ((g1 / L : ℝ) : ℂ) * deriv riemannZeta s +
        ((g1 / L : ℝ) : ℂ) *
          (deriv conreyH s / conreyH s -
            ((Real.log (t / (2 * Real.pi)) / 2 : ℝ) : ℂ)) * riemannZeta s‖ ≤
      ‖conreyDegreeOneHeightMain g g0 g1 L t * (riemannZeta s - 1)‖ +
        ‖((g1 / L : ℝ) : ℂ) * deriv riemannZeta s‖ +
        ‖((g1 / L : ℝ) : ℂ) *
          (deriv conreyH s / conreyH s -
            ((Real.log (t / (2 * Real.pi)) / 2 : ℝ) : ℂ)) * riemannZeta s‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖conreyDegreeOneHeightMain g g0 g1 L t‖ * (3 / L) +
        (|g1| / L) * (5 / 3) +
        (|g1| / L) * 8 * (5 / 3) := by
      simp only [norm_mul, hcoeff]
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left hzetaTail hA0)
          (mul_le_mul_of_nonneg_left hzetaDeriv (by positivity)))
        (mul_le_mul
          (mul_le_mul_of_nonneg_left harch (by positivity)) hzetaNorm
          (norm_nonneg _) (by positivity))
    _ ≤ (3 * ‖conreyDegreeOneHeightMain g g0 g1 L t‖ + 34 * |g1|) / L := by
      field_simp [hLpos.ne']
      nlinarith

end HardyTheorem
