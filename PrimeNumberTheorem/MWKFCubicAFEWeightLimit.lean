import PrimeNumberTheorem.MWKFCubicAFEScalarDecay
import PrimeNumberTheorem.MWKFCubicAFEPhysicalDecay

open Complex Filter MeasureTheory Set
open scoped Interval Topology

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Infinite-height real-product Mellin weights

The line X remains an explicit parameter: a positive and a negative line
must not be identified without the residue at zero. Absolute convergence
and finite-height domination are proved from the actual scalar. The norm
mass below is independent of V and P, but still depends on fixed t and X.
-/

noncomputable def cubicAFERealProductMellinIntegrand (t X P y : ℝ) : ℂ :=
  cubicAFEScalar t (cubicAFEVerticalPoint X y) *
    Complex.exp (-cubicAFEVerticalPoint X y * (Real.log P : ℂ))

theorem norm_cubicAFERealProductMellinIntegrand (t X y : ℝ) {P : ℝ} (hP : 0 < P) :
    ‖cubicAFERealProductMellinIntegrand t X P y‖ =
      ‖cubicAFEScalar t (cubicAFEVerticalPoint X y)‖ * P ^ (-X) := by
  have he : ‖Complex.exp (-cubicAFEVerticalPoint X y * (Real.log P : ℂ))‖ = P ^ (-X) := by
    rw [Complex.norm_exp, Real.rpow_def_of_pos hP]
    congr 1
    simp [cubicAFEVerticalPoint, Complex.mul_re, mul_comm]
  exact (norm_mul _ _).trans (congrArg (‖cubicAFEScalar t (cubicAFEVerticalPoint X y)‖ * ·) he)

theorem integrable_cubicAFERealProductMellinIntegrand (t : ℝ) {X P : ℝ}
    (hX : -1 / 2 < X) (hne : X ≠ 0) (hP : 0 < P) :
    Integrable (cubicAFERealProductMellinIntegrand t X P) := by
  have hc : Continuous (cubicAFERealProductMellinIntegrand t X P) := by
    apply (continuous_cubicAFEScalar_vertical_of_halfPlane t hX hne).mul
    unfold cubicAFEVerticalPoint
    fun_prop
  exact ((integrable_cubicAFEScalar_vertical t hX hne).norm.mul_const (P ^ (-X))).mono'
    hc.aestronglyMeasurable (Eventually.of_forall (fun y ↦
      (norm_cubicAFERealProductMellinIntegrand t X y hP).le))

noncomputable def cubicAFERealProductWeightVertical (t X P : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ y : ℝ, cubicAFERealProductMellinIntegrand t X P y

noncomputable def cubicAFEWeightNormMass (t X : ℝ) : ℝ :=
  ‖(1 / (2 * Real.pi) : ℂ)‖ * ∫ y : ℝ, ‖cubicAFEScalar t (cubicAFEVerticalPoint X y)‖

theorem cubicAFEWeightNormMass_nonneg (t X : ℝ) : 0 ≤ cubicAFEWeightNormMass t X := by
  exact mul_nonneg (norm_nonneg _) (integral_nonneg (fun _ ↦ norm_nonneg _))

/-- The original finite-height weight tends to its absolutely convergent
full vertical integral, on either side of the pole but not on X=0. -/
theorem tendsto_cubicAFERealProductWeightFinite (t : ℝ) {X P : ℝ}
    (hX : -1 / 2 < X) (hne : X ≠ 0) (hP : 0 < P) :
    Tendsto (fun V : ℝ ↦ cubicAFERealProductWeightFinite t X V P)
      atTop (nhds (cubicAFERealProductWeightVertical t X P)) := by
  exact (intervalIntegral_tendsto_integral
    (integrable_cubicAFERealProductMellinIntegrand t hX hne hP)
    tendsto_neg_atTop_atBot tendsto_id).const_mul (1 / (2 * Real.pi) : ℂ)

theorem norm_cubicAFERealProductWeightVertical_le (t X : ℝ) {P : ℝ} (hP : 0 < P) :
    ‖cubicAFERealProductWeightVertical t X P‖ ≤ cubicAFEWeightNormMass t X * P ^ (-X) := by
  unfold cubicAFERealProductWeightVertical
  rw [norm_mul]
  have hi := norm_integral_le_integral_norm (μ := volume) (cubicAFERealProductMellinIntegrand t X P)
  simp_rw [norm_cubicAFERealProductMellinIntegrand t X _ hP] at hi
  rw [integral_mul_const] at hi
  exact (mul_le_mul_of_nonneg_left hi (norm_nonneg _)).trans_eq (by
    unfold cubicAFEWeightNormMass
    ring)

theorem cubicAFEWeightEnvelope_le_normMass (t : ℝ) {X : ℝ}
    (hX : -1 / 2 < X) (hne : X ≠ 0) (V : ℝ) :
    cubicAFEWeightEnvelope X V t ≤ cubicAFEWeightNormMass t X := by
  have hs := (integrable_cubicAFEScalar_vertical t hX hne).norm
  have hi := intervalIntegral.norm_integral_le_integral_norm_uIoc
    (f := fun y : ℝ ↦ ‖cubicAFEScalar t (cubicAFEVerticalPoint X y)‖) (a := -V) (b := V) (μ := volume)
  simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at hi
  have hb : (∫ y in Set.uIoc (-V) V, ‖cubicAFEScalar t (cubicAFEVerticalPoint X y)‖) ≤
      ∫ y : ℝ, ‖cubicAFEScalar t (cubicAFEVerticalPoint X y)‖ :=
    setIntegral_le_integral hs (Eventually.of_forall (fun _ ↦ norm_nonneg _))
  exact mul_le_mul_of_nonneg_left (hi.trans hb) (norm_nonneg _)

/-- Actual finite-height domination, uniform over every real V (including
reversed interval orientation), with no finite-height envelope left over. -/
theorem norm_cubicAFERealProductWeightFinite_le_normMass (t : ℝ) {X : ℝ}
    (hX : -1 / 2 < X) (hne : X ≠ 0) (V : ℝ) {P : ℝ} (hP : 0 < P) :
    ‖cubicAFERealProductWeightFinite t X V P‖ ≤ cubicAFEWeightNormMass t X * P ^ (-X) :=
  (norm_cubicAFERealProductWeightFinite_le_envelope t X V hP).trans
    (mul_le_mul_of_nonneg_right (cubicAFEWeightEnvelope_le_normMass t hX hne V)
      (Real.rpow_nonneg hP.le _))

end PrimeNumberTheorem.MWKFCubic
