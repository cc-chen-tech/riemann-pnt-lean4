import MathlibAux.DriftingExponentialPolynomial
import PrimeNumberTheorem.ZeroForcedOscillation

open Complex MeasureTheory Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# Local coercivity for a finite zero cluster

This module identifies a normalized finite zero package with a drifting
exponential polynomial.  It then transfers the collision-safe local `L²`
bound from `MathlibAux.DriftingExponentialPolynomial`.
-/

/-- A multiplicity-weighted finite zero package normalized by the reference
growth exponent `beta`. -/
def normalizedFiniteZeroClusterContribution
    (S : Finset ℂ) (multiplicity : ℂ → ℕ)
    (beta y : ℝ) : ℂ :=
  (Real.exp (-beta * y) : ℂ) *
    ∑ rho ∈ S,
      (multiplicity rho : ℂ) *
        ((Real.exp y : ℝ) : ℂ) ^ rho / rho

/-- The coefficient of a zero after freezing its real growth at the left
endpoint `a`. -/
def finiteZeroClusterCoefficientAt
    (multiplicity : ℂ → ℕ) (beta a : ℝ) (rho : ℂ) : ℂ :=
  (multiplicity rho : ℂ) * rho⁻¹ *
    (Real.exp ((rho.re - beta) * a) : ℂ)

/-- Exact logarithmic-coordinate identification of the normalized finite
zero package with a drifting exponential polynomial. -/
theorem normalizedFiniteZeroClusterContribution_eq_drifting
    (S : Finset ℂ) (multiplicity : ℂ → ℕ) (beta a y : ℝ) :
    normalizedFiniteZeroClusterContribution S multiplicity beta y =
      MathlibAux.driftingExponentialPolynomial S
        (finiteZeroClusterCoefficientAt multiplicity beta a)
        Complex.im (fun rho => rho.re - beta) a y := by
  classical
  unfold normalizedFiniteZeroClusterContribution
  unfold MathlibAux.driftingExponentialPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [ZeroForcedOscillation.realExp_cpow_eq_growth_mul_oscillation
    rho rho.re y rfl]
  simp only [div_eq_mul_inv, finiteZeroClusterCoefficientAt]
  have hgrowth :
      (Real.exp (-beta * y) : ℂ) *
          (Real.exp (rho.re * y) : ℂ) =
        (Real.exp ((rho.re - beta) * y) : ℂ) := by
    rw [← ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  have hsplit :
      (Real.exp ((rho.re - beta) * y) : ℂ) =
        (Real.exp ((rho.re - beta) * a) : ℂ) *
          (Real.exp ((rho.re - beta) * (y - a)) : ℂ) := by
    rw [← ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  calc
    (Real.exp (-beta * y) : ℂ) *
        ((multiplicity rho : ℂ) *
          (((Real.exp (rho.re * y) : ℝ) : ℂ) *
            Complex.exp (I * (rho.im * y))) *
          rho⁻¹) =
        (multiplicity rho : ℂ) * rho⁻¹ *
          ((Real.exp (-beta * y) : ℂ) *
            (Real.exp (rho.re * y) : ℂ)) *
          Complex.exp (I * (rho.im * y)) := by ring
    _ = (multiplicity rho : ℂ) * rho⁻¹ *
          (Real.exp ((rho.re - beta) * a) : ℂ) *
          (Real.exp ((rho.re - beta) * (y - a)) : ℂ) *
          Complex.exp (I * (rho.im * y)) := by
      rw [hgrowth, hsplit]
      ring

/-- A real-part band around `beta` gives the drift interval required by the
abstract coercivity theorem. -/
private theorem finiteZeroCluster_drift_mem
    {S : Finset ℂ} {beta delta : ℝ}
    (hband : ∀ rho ∈ S, beta - delta ≤ rho.re ∧ rho.re ≤ beta) :
    ∀ rho ∈ S,
      -delta ≤ rho.re - beta ∧ rho.re - beta ≤ 0 := by
  intro rho hrho
  have h := hband rho hrho
  constructor <;> linarith

/-- Collision-safe local `L²` lower bound for an actual finite normalized
zero package. Equal ordinates are merged before the diagonal energy and
off-diagonal budget are formed. -/
theorem
    integral_normSq_normalizedFiniteZeroClusterContribution_ge_merged
    {S : Finset ℂ} {multiplicity : ℂ → ℕ}
    {beta a L delta : ℝ}
    (hL : 0 ≤ L)
    (hdelta : 0 ≤ delta)
    (hband : ∀ rho ∈ S, beta - delta ≤ rho.re ∧ rho.re ≤ beta) :
    (1 / 2 : ℝ) *
          (L *
              ∑ u ∈ MathlibAux.mergedFrequencySupport S Complex.im,
                ‖MathlibAux.mergedFrequencyCoefficient S
                    (finiteZeroClusterCoefficientAt multiplicity beta a)
                    Complex.im u‖ ^ 2 -
            ZeroForcedOscillation.offDiagonalBound
              (MathlibAux.mergedFrequencySupport S Complex.im)
              (MathlibAux.mergedFrequencyCoefficient S
                (finiteZeroClusterCoefficientAt multiplicity beta a)
                Complex.im)
              id) -
        L * (1 - Real.exp (-delta * L)) ^ 2 *
          (∑ rho ∈ S,
            ‖finiteZeroClusterCoefficientAt
              multiplicity beta a rho‖) ^ 2 ≤
      ∫ y in a..(a + L),
        ‖normalizedFiniteZeroClusterContribution
          S multiplicity beta y‖ ^ 2 := by
  have hbase :=
    MathlibAux.integral_normSq_driftingExponentialPolynomial_ge_merged
      (S := S)
      (coeff := finiteZeroClusterCoefficientAt multiplicity beta a)
      (freq := Complex.im)
      (drift := fun rho => rho.re - beta)
      (a := a) (L := L) (delta := delta)
      hL hdelta (finiteZeroCluster_drift_mem hband)
  apply hbase.trans_eq
  apply intervalIntegral.integral_congr
  intro y hy
  exact congrArg (fun z : ℂ => ‖z‖ ^ 2)
    (normalizedFiniteZeroClusterContribution_eq_drifting
      S multiplicity beta a y).symm

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
