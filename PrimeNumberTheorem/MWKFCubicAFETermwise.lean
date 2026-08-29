import Mathlib.MeasureTheory.Integral.DominatedConvergence
import PrimeNumberTheorem.MWKFCubicAFEDirichlet

open Complex Filter MeasureTheory
open scoped Interval

namespace PrimeNumberTheorem
namespace MWKFCubic

/-!
# Termwise integration on the physical cubic AFE line

This file keeps the vertical height finite while interchanging the absolutely
convergent double Dirichlet family with the interval integral.  The final
theorem then lets the height tend to infinity only after the exact finite
identity has been established.
-/

noncomputable def cubicAFEVerticalPoint (X y : ℝ) : ℂ :=
  (X : ℂ) + (y : ℂ) * I

noncomputable def cubicAFEScalar (t : ℝ) (z : ℂ) : ℂ :=
  cubicAFEKernelG t z * cubicAFEGammaProduct t z /
    cubicAFEGammaProduct t 0 / z

theorem cubicAFENormalizedDirichletTerm_eq (t : ℝ) (z : ℂ) (p : ℕ × ℕ) :
    cubicAFENormalizedDirichletTerm t z p =
      cubicAFEScalar t z * cubicAFEDirichletTerm t z p := rfl

private theorem continuous_Gammaℝ_vertical
    (w : ℂ) (X : ℝ) (h : 0 < w.re + X) :
    Continuous (fun y : ℝ ↦ Gammaℝ (w + cubicAFEVerticalPoint X y)) := by
  have hpoint : Continuous (fun y : ℝ ↦ cubicAFEVerticalPoint X y) := by
    unfold cubicAFEVerticalPoint
    fun_prop
  have harg : Continuous
      (fun y : ℝ ↦ w + cubicAFEVerticalPoint X y) :=
    continuous_const.add hpoint
  have hinv : Continuous
      (fun y : ℝ ↦ (Gammaℝ (w + cubicAFEVerticalPoint X y))⁻¹) :=
    differentiable_Gammaℝ_inv.continuous.comp harg
  have hne : ∀ y : ℝ,
      (Gammaℝ (w + cubicAFEVerticalPoint X y))⁻¹ ≠ 0 := by
    intro y
    apply inv_ne_zero
    apply Gammaℝ_ne_zero_of_re_pos
    simp [cubicAFEVerticalPoint]
    exact h
  have hinvinv : Continuous
      (fun y : ℝ ↦ ((Gammaℝ (w + cubicAFEVerticalPoint X y))⁻¹)⁻¹) := by
    exact hinv.inv₀ hne
  simpa only [inv_inv] using hinvinv

theorem continuous_cubicAFEScalar_vertical
    (t X : ℝ) (hX : 1 / 2 < X) :
    Continuous (fun y : ℝ ↦ cubicAFEScalar t (cubicAFEVerticalPoint X y)) := by
  have hs : Continuous (fun y : ℝ ↦
      Gammaℝ (cubicCriticalPoint t + cubicAFEVerticalPoint X y)) := by
    exact continuous_Gammaℝ_vertical (cubicCriticalPoint t) X
      (by norm_num [cubicCriticalPoint]; linarith)
  have hu : Continuous (fun y : ℝ ↦
      Gammaℝ (1 - cubicCriticalPoint t + cubicAFEVerticalPoint X y)) := by
    exact continuous_Gammaℝ_vertical (1 - cubicCriticalPoint t) X
      (by norm_num [cubicCriticalPoint]; linarith)
  have hpoint : Continuous (fun y : ℝ ↦ cubicAFEVerticalPoint X y) := by
    unfold cubicAFEVerticalPoint
    fun_prop
  have hkernel : Continuous (fun y : ℝ ↦
      cubicAFEKernelG t (cubicAFEVerticalPoint X y)) := by
    unfold cubicAFEKernelG cubicAFEPoleCanceller
    fun_prop
  have hz : ∀ y : ℝ, cubicAFEVerticalPoint X y ≠ 0 := by
    intro y hzero
    have hre := congrArg Complex.re hzero
    simp [cubicAFEVerticalPoint] at hre
    linarith
  unfold cubicAFEScalar cubicAFEGammaProduct
  exact ((hkernel.mul (hs.mul hu)).div_const _).div₀ hpoint hz

theorem continuous_cubicAFENormalizedDirichletTerm_vertical
    (t X : ℝ) (hX : 1 / 2 < X) (p : ℕ × ℕ) :
    Continuous (fun y : ℝ ↦
      cubicAFENormalizedDirichletTerm t (cubicAFEVerticalPoint X y) p) := by
  rw [show (fun y : ℝ ↦
      cubicAFENormalizedDirichletTerm t (cubicAFEVerticalPoint X y) p) =
      fun y : ℝ ↦ cubicAFEScalar t (cubicAFEVerticalPoint X y) *
        cubicAFEDirichletTerm t (cubicAFEVerticalPoint X y) p by
      funext y
      exact cubicAFENormalizedDirichletTerm_eq _ _ _]
  apply (continuous_cubicAFEScalar_vertical t X hX).mul
  unfold cubicAFEDirichletTerm
  have hb1 : (p.1 + 1 : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    have hp : (0 : ℝ) ≤ (p.1 : ℝ) := by positivity
    linarith
  have hb2 : (p.2 + 1 : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    have hp : (0 : ℝ) ≤ (p.2 : ℝ) := by positivity
    linarith
  letI : NeZero (p.1 + 1 : ℂ) := ⟨hb1⟩
  letI : NeZero (p.2 + 1 : ℂ) := ⟨hb2⟩
  have hpoint : Continuous (fun y : ℝ ↦ cubicAFEVerticalPoint X y) := by
    unfold cubicAFEVerticalPoint
    fun_prop
  have hc1 : Continuous (fun y : ℝ ↦
      (p.1 + 1 : ℂ) ^ (cubicCriticalPoint t + cubicAFEVerticalPoint X y)) := by
    apply (continuous_const_cpow (p.1 + 1 : ℂ)).comp
    exact continuous_const.add hpoint
  have hc2 : Continuous (fun y : ℝ ↦
      (p.2 + 1 : ℂ) ^ (1 - cubicCriticalPoint t + cubicAFEVerticalPoint X y)) := by
    apply (continuous_const_cpow (p.2 + 1 : ℂ)).comp
    exact (continuous_const.sub continuous_const).add hpoint
  exact (continuous_const.div₀ hc1 (fun _ ↦
      Complex.cpow_ne_zero_iff.mpr (Or.inl hb1))).mul
    (continuous_const.div₀ hc2 (fun _ ↦
      Complex.cpow_ne_zero_iff.mpr (Or.inl hb2)))

theorem norm_cubicAFEDirichletTerm_vertical_eq
    (t X y : ℝ) (p : ℕ × ℕ) :
    ‖cubicAFEDirichletTerm t (cubicAFEVerticalPoint X y) p‖ =
      ‖cubicAFEDirichletTerm t (X : ℂ) p‖ := by
  simp only [cubicAFEDirichletTerm, norm_mul, norm_div, norm_one]
  have hb1 : (p.1 + 1 : ℂ) = ((p.1 + 1 : ℕ) : ℂ) := by push_cast; ring
  have hb2 : (p.2 + 1 : ℂ) = ((p.2 + 1 : ℕ) : ℂ) := by push_cast; ring
  have hb1' : ((p.1 + 1 : ℕ) : ℂ) = (((p.1 + 1 : ℕ) : ℝ) : ℂ) := by norm_cast
  have hb2' : ((p.2 + 1 : ℕ) : ℂ) = (((p.2 + 1 : ℕ) : ℝ) : ℂ) := by norm_cast
  rw [hb1, hb2, hb1', hb2',
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp [cubicCriticalPoint, cubicAFEVerticalPoint]

/-- At every finite height, the physical AFE line may be integrated term by
term with no truncation and no unproved analytic input. -/
theorem hasSum_intervalIntegral_cubicAFENormalizedDirichletTerm
    (t : ℝ) {X : ℝ} (hX : 1 / 2 < X) (V : ℝ) :
    HasSum
      (fun p : ℕ × ℕ ↦ ∫ y : ℝ in -V..V,
        cubicAFENormalizedDirichletTerm t (cubicAFEVerticalPoint X y) p)
      (∫ y : ℝ in -V..V,
        cubicAFECompletedIntegrand t (cubicAFEVerticalPoint X y) /
          cubicAFEGammaProduct t 0) := by
  let a : ℕ × ℕ → ℝ := fun p ↦
    ‖cubicAFEDirichletTerm t (X : ℂ) p‖
  let S : ℝ → ℂ := fun y ↦ cubicAFEScalar t (cubicAFEVerticalPoint X y)
  have ha : Summable a := by
    exact summable_norm_cubicAFEDirichletTerm t hX
  have hS : Continuous S := continuous_cubicAFEScalar_vertical t X hX
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (bound := fun p y ↦ ‖S y‖ * a p)
  · intro p
    exact (continuous_cubicAFENormalizedDirichletTerm_vertical t X hX p).aestronglyMeasurable
  · intro p
    filter_upwards with y
    intro _hy
    change ‖cubicAFEScalar t (cubicAFEVerticalPoint X y) *
        cubicAFEDirichletTerm t (cubicAFEVerticalPoint X y) p‖ ≤
      ‖cubicAFEScalar t (cubicAFEVerticalPoint X y)‖ *
        ‖cubicAFEDirichletTerm t (X : ℂ) p‖
    rw [norm_mul, norm_cubicAFEDirichletTerm_vertical_eq]
  · filter_upwards with y
    intro _hy
    exact ha.mul_left ‖S y‖
  · have hc : Continuous (fun y : ℝ ↦ ‖S y‖ * ∑' p, a p) :=
      hS.norm.mul continuous_const
    simpa only [tsum_mul_left] using hc.intervalIntegrable (-V) V
  · filter_upwards with y
    intro _hy
    have hz : 1 / 2 < (cubicAFEVerticalPoint X y).re := by
      simpa [cubicAFEVerticalPoint] using hX
    rw [cubicAFECompletedIntegrand_div_gamma_eq_tsum t hz]
    exact ((summable_norm_cubicAFEDirichletTerm t hz).of_norm.mul_left
      (cubicAFEScalar t (cubicAFEVerticalPoint X y))).hasSum

/-- Finite-height AFE weight for one positive integer pair. -/
noncomputable def cubicAFEWeightFinite
    (t X V : ℝ) (p : ℕ × ℕ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) *
    ∫ y : ℝ in -V..V,
      cubicAFENormalizedDirichletTerm t (cubicAFEVerticalPoint X y) p

noncomputable def cubicAFEDoubleSumFinite (t X V : ℝ) : ℂ :=
  ∑' p : ℕ × ℕ, cubicAFEWeightFinite t X V p

theorem cubicAFEDoubleSumFinite_eq
    (t : ℝ) {X : ℝ} (hX : 1 / 2 < X) (V : ℝ) :
    cubicAFEDoubleSumFinite t X V =
      (1 / (2 * Real.pi) : ℂ) *
        (∫ y : ℝ in -V..V,
          cubicAFECompletedIntegrand t (cubicAFEVerticalPoint X y) /
            cubicAFEGammaProduct t 0) := by
  unfold cubicAFEDoubleSumFinite cubicAFEWeightFinite
  rw [tsum_mul_left]
  rw [(hasSum_intervalIntegral_cubicAFENormalizedDirichletTerm t hX V).tsum_eq]

theorem tendsto_two_mul_cubicAFEDoubleSumFinite
    (t : ℝ) {X : ℝ} (hX : 1 / 2 < X) :
    Tendsto (fun V : ℝ ↦ 2 * cubicAFEDoubleSumFinite t X V)
      atTop
      (nhds (Complex.normSq (riemannZeta (cubicCriticalPoint t)) : ℂ)) := by
  have hvertical :=
    tendsto_cubicAFECompletedIntegrand_verticalIntegral t
      (show 0 < X by linarith)
  have hdiv : Tendsto
      (fun V : ℝ ↦
        (∫ y : ℝ in -V..V,
          cubicAFECompletedIntegrand t (cubicAFEVerticalPoint X y)) /
            cubicAFEGammaProduct t 0)
      atTop
      (nhds ((Real.pi *
        (completedRiemannZeta (cubicCriticalPoint t) *
          completedRiemannZeta (1 - cubicCriticalPoint t))) /
            cubicAFEGammaProduct t 0)) := by
    simpa only [cubicAFEVerticalPoint] using
      hvertical.div_const (cubicAFEGammaProduct t 0)
  have hnorm : Tendsto
      (fun V : ℝ ↦ ∫ y : ℝ in -V..V,
        cubicAFECompletedIntegrand t (cubicAFEVerticalPoint X y) /
          cubicAFEGammaProduct t 0)
      atTop
      (nhds (Real.pi *
        (Complex.normSq (riemannZeta (cubicCriticalPoint t)) : ℂ))) := by
    rw [completedRiemannZeta_product_eq_gamma_mul_normSq] at hdiv
    have hcancel :
        (Real.pi : ℂ) *
            (cubicAFEGammaProduct t 0 *
              (Complex.normSq (riemannZeta (cubicCriticalPoint t)) : ℂ)) /
              cubicAFEGammaProduct t 0 =
          Real.pi *
            (Complex.normSq (riemannZeta (cubicCriticalPoint t)) : ℂ) := by
      field_simp [cubicAFEGammaProduct_zero_ne t]
    rw [hcancel] at hdiv
    simpa only [intervalIntegral.integral_div] using hdiv
  have hscaled := hnorm.const_mul (1 / (Real.pi : ℂ))
  have hscaled' : Tendsto
      (fun V : ℝ ↦ (1 / (Real.pi : ℂ)) *
        (∫ y : ℝ in -V..V,
          cubicAFECompletedIntegrand t (cubicAFEVerticalPoint X y) /
            cubicAFEGammaProduct t 0))
      atTop
      (nhds (Complex.normSq (riemannZeta (cubicCriticalPoint t)) : ℂ)) := by
    convert hscaled using 1
    field_simp [Real.pi_ne_zero]
  apply hscaled'.congr'
  filter_upwards with V
  rw [cubicAFEDoubleSumFinite_eq t hX V]
  field_simp [Real.pi_ne_zero]

end MWKFCubic
end PrimeNumberTheorem
