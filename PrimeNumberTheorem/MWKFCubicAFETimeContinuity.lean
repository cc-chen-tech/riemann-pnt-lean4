import PrimeNumberTheorem.MWKFCubicAFEMollifierReassembly

open Complex MeasureTheory
open scoped Interval

namespace PrimeNumberTheorem
namespace MWKFCubic

/-!
# Time continuity and integrability of the finite-height cubic AFE
-/

/-- The normalized completed AFE integrand with time and vertical variables
packaged as one real pair. -/
noncomputable def cubicAFENormalizedVerticalIntegrand
    (X : ℝ) (p : ℝ × ℝ) : ℂ :=
  cubicAFECompletedIntegrand p.1 (cubicAFEVerticalPoint X p.2) /
    cubicAFEGammaProduct p.1 0

theorem continuous_cubicAFENormalizedVerticalIntegrand
    {X : ℝ} (hX : 0 < X) :
    Continuous (cubicAFENormalizedVerticalIntegrand X) := by
  let s : ℝ × ℝ → ℂ := fun p ↦ cubicCriticalPoint p.1
  let u : ℝ × ℝ → ℂ := fun p ↦ 1 - s p
  let z : ℝ × ℝ → ℂ := fun p ↦ cubicAFEVerticalPoint X p.2
  have hsC : Continuous s := by
    unfold s cubicCriticalPoint
    fun_prop
  have huC : Continuous u := continuous_const.sub hsC
  have hzC : Continuous z := by
    unfold z cubicAFEVerticalPoint
    fun_prop
  have hz : ∀ p : ℝ × ℝ, z p ≠ 0 := by
    intro p hzero
    have hre := congrArg Complex.re hzero
    simp [z, cubicAFEVerticalPoint] at hre
    linarith
  have hs : ∀ p : ℝ × ℝ, s p ≠ 0 := by
    intro p
    exact cubicCriticalPoint_ne_zero p.1
  have hu : ∀ p : ℝ × ℝ, u p ≠ 0 := by
    intro p
    exact one_sub_cubicCriticalPoint_ne_zero p.1
  have hdenC : Continuous (fun p ↦ s p ^ 2 * u p ^ 2) :=
    (hsC.pow 2).mul (huC.pow 2)
  have hden : ∀ p : ℝ × ℝ, s p ^ 2 * u p ^ 2 ≠ 0 := by
    intro p
    exact mul_ne_zero (pow_ne_zero 2 (hs p)) (pow_ne_zero 2 (hu p))
  have hzetaC : Continuous completedRiemannZeta₀ :=
    differentiable_completedZeta₀.continuous
  have hb₁C : Continuous (fun p ↦
      completedRiemannZeta₀ (s p + z p) * (s p + z p) * (u p - z p) -
        (u p - z p) - (s p + z p)) := by
    exact ((((hzetaC.comp (hsC.add hzC)).mul (hsC.add hzC)).mul
      (huC.sub hzC)).sub (huC.sub hzC)).sub (hsC.add hzC)
  have hb₂C : Continuous (fun p ↦
      completedRiemannZeta₀ (u p + z p) * (u p + z p) * (s p - z p) -
        (s p - z p) - (u p + z p)) := by
    exact ((((hzetaC.comp (huC.add hzC)).mul (huC.add hzC)).mul
      (hsC.sub hzC)).sub (hsC.sub hzC)).sub (huC.add hzC)
  have hextC : Continuous (fun p ↦
      Complex.exp (z p ^ 2) * (1 - 4 * z p ^ 2) /
          (s p ^ 2 * u p ^ 2) *
        (completedRiemannZeta₀ (s p + z p) * (s p + z p) * (u p - z p) -
          (u p - z p) - (s p + z p)) *
        (completedRiemannZeta₀ (u p + z p) * (u p + z p) * (s p - z p) -
          (s p - z p) - (u p + z p))) := by
    have hbase : Continuous (fun p ↦
        Complex.exp (z p ^ 2) * (1 - 4 * z p ^ 2)) :=
      (Complex.continuous_exp.comp (hzC.pow 2)).mul
        (continuous_const.sub (continuous_const.mul (hzC.pow 2)))
    exact ((hbase.div₀ hdenC hden).mul hb₁C).mul hb₂C
  have hGammaSInv : Continuous (fun p ↦ (Gammaℝ (s p))⁻¹) :=
    differentiable_Gammaℝ_inv.continuous.comp hsC
  have hGammaUInv : Continuous (fun p ↦ (Gammaℝ (u p))⁻¹) :=
    differentiable_Gammaℝ_inv.continuous.comp huC
  have hGammaS : Continuous (fun p ↦ Gammaℝ (s p)) := by
    rw [show (fun p ↦ Gammaℝ (s p)) =
        fun p ↦ ((Gammaℝ (s p))⁻¹)⁻¹ by
      funext p
      simp]
    exact hGammaSInv.inv₀ (fun p ↦ by
      apply inv_ne_zero
      apply Gammaℝ_ne_zero_of_re_pos
      simp [s, cubicCriticalPoint])
  have hGammaU : Continuous (fun p ↦ Gammaℝ (u p)) := by
    rw [show (fun p ↦ Gammaℝ (u p)) =
        fun p ↦ ((Gammaℝ (u p))⁻¹)⁻¹ by
      funext p
      simp]
    exact hGammaUInv.inv₀ (fun p ↦ by
      apply inv_ne_zero
      apply Gammaℝ_ne_zero_of_re_pos
      simp [u, s, cubicCriticalPoint]
      norm_num)
  have hgammaC : Continuous (fun p ↦ Gammaℝ (s p) * Gammaℝ (u p)) :=
    hGammaS.mul hGammaU
  have hgamma : ∀ p : ℝ × ℝ, Gammaℝ (s p) * Gammaℝ (u p) ≠ 0 := by
    intro p
    simpa [s, u, cubicAFEGammaProduct] using cubicAFEGammaProduct_zero_ne p.1
  have hform : cubicAFENormalizedVerticalIntegrand X = fun p ↦
      (Complex.exp (z p ^ 2) * (1 - 4 * z p ^ 2) /
          (s p ^ 2 * u p ^ 2) *
        (completedRiemannZeta₀ (s p + z p) * (s p + z p) * (u p - z p) -
          (u p - z p) - (s p + z p)) *
        (completedRiemannZeta₀ (u p + z p) * (u p + z p) * (s p - z p) -
          (s p - z p) - (u p + z p))) / z p /
        (Gammaℝ (s p) * Gammaℝ (u p)) := by
    funext p
    simp [cubicAFENormalizedVerticalIntegrand, cubicAFECompletedIntegrand,
      cubicAFECompletedExtension, cubicAFEGammaProduct, s, u, z]
  rw [hform]
  exact (hextC.div₀ hzC hz).div₀ hgammaC hgamma

theorem continuous_cubicAFEDoubleSumFinite_time
    {X : ℝ} (hX : 1 / 2 < X) (V : ℝ) :
    Continuous (fun t : ℝ ↦ cubicAFEDoubleSumFinite t X V) := by
  rw [show (fun t : ℝ ↦ cubicAFEDoubleSumFinite t X V) =
      fun t : ℝ ↦ (1 / (2 * Real.pi) : ℂ) *
        ∫ y : ℝ in -V..V, cubicAFENormalizedVerticalIntegrand X (t, y) by
    funext t
    rw [cubicAFEDoubleSumFinite_eq t hX V]
    rfl]
  have hjoint : Continuous (Function.uncurry (fun t y ↦
      cubicAFENormalizedVerticalIntegrand X (t, y))) := by
    rw [show Function.uncurry (fun t y ↦
        cubicAFENormalizedVerticalIntegrand X (t, y)) =
      cubicAFENormalizedVerticalIntegrand X by
      funext p
      rfl]
    exact continuous_cubicAFENormalizedVerticalIntegrand (by linarith : 0 < X)
  exact continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hjoint (-V) V)

theorem continuous_cubicAFEMollifiedApproximation
    (W : CubicTestWeight) (T : ℝ) {X : ℝ} (hX : 1 / 2 < X) (V : ℝ) :
    Continuous (cubicAFEMollifiedApproximation W T X V) := by
  unfold cubicAFEMollifiedApproximation
  have hdouble : Continuous (fun t : ℝ ↦
      2 * cubicAFEDoubleSumFinite t X V) :=
    continuous_const.mul (continuous_cubicAFEDoubleSumFinite_time hX V)
  have hmoll : Continuous (fun t : ℝ ↦
      (Complex.normSq (HardyTheorem.selbergMoebiusMollifier
        (cubicMollifierLength T) (cubicCriticalPoint t)) : ℂ)) := by
    exact Complex.continuous_ofReal.comp
      (Complex.continuous_normSq.comp
        (HardyTheorem.continuous_selbergMollifier_criticalLine
          (cubicMollifierLength T)
          (fun n ↦ (HardyTheorem.selbergMoebiusCoeff
            (cubicMollifierLength T) n : ℂ))))
  exact (hdouble.mul hmoll).mul
    (Complex.continuous_ofReal.comp
      (W.continuous.comp (continuous_id.div_const T)))

theorem integrable_cubicAFEMollifiedApproximation
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0)
    {X : ℝ} (hX : 1 / 2 < X) (V : ℝ) :
    Integrable (cubicAFEMollifiedApproximation W T X V) := by
  exact (continuous_cubicAFEMollifiedApproximation W T hX V).integrable_of_hasCompactSupport
      (hasCompactSupport_cubicAFEMollifiedApproximation W hT X V)

end MWKFCubic
end PrimeNumberTheorem
