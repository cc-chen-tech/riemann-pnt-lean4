import PrimeNumberTheorem.ExplicitFormulaTruncated
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualClusterSignedComplement

/-!
# Actual explicit-formula decomposition around a visible zero cluster

This module identifies the signed terms used by the cluster-complement
transfer with the project's multiplicity-aware truncated explicit formula.
The identity is exact at every nonzero evaluation point. No estimate for the
explicit-formula approximation error is asserted here.
-/

namespace PrimeNumberTheorem

/-- The closed real-axis terms in the multiplicity-aware explicit formula,
normalized by the evaluation scale and projected to the real axis. -/
noncomputable def actualPNTClosedRealAxisRelativeTerm (x : ℝ) : ℝ :=
  ((-(Real.log (2 * Real.pi) : ℂ) -
      (1 / 2 : ℂ) * (Real.log (1 - x ^ (-2 : ℝ)) : ℂ)) / (x : ℂ)).re

/-- The signed normalized error between `chebyshevPsi0` and the
multiplicity-aware finite-height explicit-formula approximation. -/
noncomputable def actualPNTExplicitFormulaRelativeRemainder
    (T : ℝ → ℝ) (x : ℝ) : ℝ :=
  (((chebyshevPsi0 x : ℂ) -
      explicitFormulaApproxWithMultiplicity x (T x)) / (x : ℂ)).re

/-- The actual relative PNT error is exactly the real part of the complete
finite zero sum plus the closed real-axis and explicit-formula remainder
terms. -/
theorem relativeChebyshevPsi0Error_eq_dynamicFinite_add_closed_add_remainder
    (T : ℝ → ℝ) (x : ℝ) :
    relativeChebyshevPsi0Error x =
      (dynamicFinitePNTZeroSum T x).re +
        (actualPNTClosedRealAxisRelativeTerm x +
          actualPNTExplicitFormulaRelativeRemainder T x) := by
  have hsum :=
    sum_pntRelativeZeroContribution_eq_inv_mul_neg_finiteNontrivialZeroSumWithMultiplicity
      x (T x)
  have happrox :=
    ExplicitFormulaTruncated.explicitFormulaApproxWithMultiplicity_eq_log_two_pi
      x (T x)
  have hcomplex :
      ((((chebyshevPsi0 x - x) / x : ℝ) : ℂ)) =
        ((x : ℂ)⁻¹ *
          (-finiteNontrivialZeroSumWithMultiplicity x (T x))) +
        (-(Real.log (2 * Real.pi) : ℂ) -
            (1 / 2 : ℂ) *
              (Real.log (1 - x ^ (-2 : ℝ)) : ℂ)) / (x : ℂ) +
        ((chebyshevPsi0 x : ℂ) -
            explicitFormulaApproxWithMultiplicity x (T x)) / (x : ℂ) := by
    rw [happrox]
    push_cast
    field_simp
    ring
  unfold relativeChebyshevPsi0Error dynamicFinitePNTZeroSum
    actualPNTClosedRealAxisRelativeTerm
    actualPNTExplicitFormulaRelativeRemainder
  rw [hsum]
  have hre := congrArg Complex.re hcomplex
  simpa only [Complex.add_re, Complex.ofReal_re, add_assoc] using hre

/-- Exact actual explicit-formula decomposition into the visible cluster,
closed real-axis term, contour/approximation remainder, and the signed
outside-cluster complement. -/
theorem relativeChebyshevPsi0Error_eq_visibleCluster_add_actualResiduals
    (T : ℝ → ℝ) (S : Finset ℂ) (x : ℝ) :
    relativeChebyshevPsi0Error x =
      dynamicVisibleClusterPNTMain T S x +
        (actualPNTClosedRealAxisRelativeTerm x +
          actualPNTExplicitFormulaRelativeRemainder T x +
          dynamicOutsideClusterPNTComplement T S x) := by
  rw [
    relativeChebyshevPsi0Error_eq_dynamicFinite_add_closed_add_remainder T x,
    dynamicFinitePNTZeroSum_re_eq_main_add_complement T S x]
  ring

end PrimeNumberTheorem
