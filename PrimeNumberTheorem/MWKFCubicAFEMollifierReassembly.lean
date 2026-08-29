import PrimeNumberTheorem.MWKFCubicAFECombinedPhase

open Complex Filter
open scoped BigOperators

namespace PrimeNumberTheorem
namespace MWKFCubic

/-!
# Finite-height reassembly of the cubic AFE with the finite mollifier

This file keeps the AFE height `V` finite.  In particular, the pointwise
limit below is not interchanged with the outer `t`-integral.
-/

/-- The finite-height AFE approximation to the complete mollified integrand. -/
noncomputable def cubicAFEMollifiedApproximation
    (W : CubicTestWeight) (T X V t : ℝ) : ℂ :=
  (2 * cubicAFEDoubleSumFinite t X V) *
    (Complex.normSq (HardyTheorem.selbergMoebiusMollifier
      (cubicMollifierLength T) (cubicCriticalPoint t)) : ℂ) *
    (W (t / T) : ℂ)

/-- The contribution of one ordered mollifier pair before expanding the AFE
double Dirichlet series. -/
noncomputable def cubicAFEMollifierPairApproximation
    (W : CubicTestWeight) (T X V : ℝ) (d e : ℕ) (t : ℝ) : ℂ :=
  (cubicMollifierCoefficient T d : ℂ) *
    (cubicMollifierCoefficient T e : ℂ) *
    ((2 * cubicAFEDoubleSumFinite t X V) *
      ((1 / (d : ℂ) ^ cubicCriticalPoint t) *
        (starRingEnd ℂ) (1 / (e : ℂ) ^ cubicCriticalPoint t)) *
      (W (t / T) : ℂ))

/-- At each physical height `t`, the finite-height mollified AFE converges to
the literal integrand.  No limit--integral interchange is asserted here. -/
theorem tendsto_cubicAFEMollifiedApproximation
    (W : CubicTestWeight) (T t : ℝ) {X : ℝ} (hX : 1 / 2 < X) :
    Tendsto (fun V : ℝ ↦ cubicAFEMollifiedApproximation W T X V t)
      atTop (nhds (cubicMomentIntegrand W T t : ℂ)) := by
  have h := (tendsto_two_mul_cubicAFEDoubleSumFinite t hX).mul_const
    (Complex.normSq (HardyTheorem.selbergMoebiusMollifier
      (cubicMollifierLength T) (cubicCriticalPoint t)) : ℂ)
  have h' := h.mul_const (W (t / T) : ℂ)
  simpa [cubicAFEMollifiedApproximation, cubicMomentIntegrand,
    cubicCriticalPoint] using h'

/-- Exact finite `(d,e)` reassembly of the finite-height mollified AFE. -/
theorem cubicAFEMollifiedApproximation_eq_pairSum
    (W : CubicTestWeight) (T X V t : ℝ) :
    cubicAFEMollifiedApproximation W T X V t =
      ∑ d ∈ cubicMollifierSupport T, ∑ e ∈ cubicMollifierSupport T,
        cubicAFEMollifierPairApproximation W T X V d e t := by
  unfold cubicAFEMollifiedApproximation cubicAFEMollifierPairApproximation
  rw [show cubicCriticalPoint t = (1 / 2 : ℂ) + I * t by rfl,
    cubicMollifierNormSq_eq_doubleSum]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  ring

end MWKFCubic
end PrimeNumberTheorem
