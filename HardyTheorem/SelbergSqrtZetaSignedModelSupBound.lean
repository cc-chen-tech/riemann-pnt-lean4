import HardyTheorem.SelbergSqrtZetaSignedModelCorrelation

open Complex
open scoped BigOperators

namespace HardyTheorem

/-!
# Uniform L1 bound for the signed square-root-zeta model

The complex model is a finite phase polynomial.  Its real signed theta model
is therefore bounded uniformly in the height and rotation by the L1 norm of
its finite coefficient family.
-/

/-- The finite coefficient L1 quantity controlling the signed theta model. -/
noncomputable def selbergSqrtZetaSignedModelSupBoundL1
    (T : ℝ) (X : ℕ) : ℝ :=
  ∑ p ∈ selbergSqrtZetaSignedPhaseSupport (firstZetaApproximationCutoff T) X,
    ‖selbergSqrtZetaSignedPhaseCoeff X p‖

/-- Every signed theta model value is bounded by the L1 norm of its finite
phase-polynomial coefficients. -/
theorem abs_selbergSqrtZetaSignedThetaModel_le_modelSupBoundL1
    (kappa T : ℝ) (X : ℕ) (t : ℝ) :
    |selbergSqrtZetaSignedThetaModel kappa T X t| ≤
      selbergSqrtZetaSignedModelSupBoundL1 T X := by
  change |selbergSqrtZetaSignedThetaModel kappa T X t| ≤
    ∑ p ∈ selbergSqrtZetaSignedPhaseSupport (firstZetaApproximationCutoff T) X,
      ‖selbergSqrtZetaSignedPhaseCoeff X p‖
  rw [selbergSqrtZetaSignedThetaModel_eq_complexModel_re]
  calc
    |(selbergSqrtZetaSignedComplexModel kappa T X t).re| ≤
        ‖selbergSqrtZetaSignedComplexModel kappa T X t‖ :=
      Complex.abs_re_le_norm _
    _ = ‖selbergSqrtZetaSignedPhasePolynomial
          (firstZetaApproximationCutoff T) X t‖ := by
      simp only [selbergSqrtZetaSignedComplexModel, norm_mul,
        Complex.norm_exp]
      simp
    _ ≤ ∑ p ∈ selbergSqrtZetaSignedPhaseSupport (firstZetaApproximationCutoff T) X,
        ‖selbergSqrtZetaSignedPhaseCoeff X p *
          Complex.exp (I * ((thetaModel t +
            selbergSqrtZetaSignedPhaseFrequency p * t : ℝ) : ℂ))‖ := by
      rw [selbergSqrtZetaSignedPhasePolynomial]
      exact norm_sum_le _ _
    _ = ∑ p ∈ selbergSqrtZetaSignedPhaseSupport (firstZetaApproximationCutoff T) X,
        ‖selbergSqrtZetaSignedPhaseCoeff X p‖ := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [norm_mul, Complex.norm_exp]
      simp

end HardyTheorem
