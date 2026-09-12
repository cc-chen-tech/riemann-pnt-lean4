import MathlibAux.GcdLcmLogQuadratic
import PrimeNumberTheorem.MWKFCubicFiniteExpansion

open scoped BigOperators

namespace PrimeNumberTheorem.MWKFCubic

/-!
# The actual cubic mollifier in the logarithmic reciprocal-LCM kernel

This module specializes the finite reciprocal-LCM identities to the literal
coefficient and cutoff used by `cubicMollifiedSecondMoment`.  Everything here
is a finite equality.  In particular, no contour shift, Selberg--Perron
asymptotic, or off-diagonal estimate is asserted.
-/

/-- The divisor mass attached to the actual cubic mollifier coefficient. -/
noncomputable def cubicMollifierDivisorMass (T : ℝ) (d : ℕ) : ℝ :=
  ∑ n ∈ (cubicMollifierSupport T).filter (fun n => d ∣ n),
    cubicMollifierCoefficient T n * (n : ℝ)⁻¹

/-- The logarithmically weighted divisor mass attached to the actual cubic
mollifier coefficient. -/
noncomputable def cubicMollifierLogDivisorMass (T : ℝ) (d : ℕ) : ℝ :=
  ∑ n ∈ (cubicMollifierSupport T).filter (fun n => d ∣ n),
    cubicMollifierCoefficient T n * Real.log n * (n : ℝ)⁻¹

/-- The reciprocal-LCM quadratic form for the literal cubic mollifier. -/
noncomputable def cubicReciprocalLcmQuadratic (T : ℝ) : ℝ :=
  ∑ d ∈ cubicMollifierSupport T, ∑ e ∈ cubicMollifierSupport T,
    cubicMollifierCoefficient T d * cubicMollifierCoefficient T e *
      (Nat.lcm d e : ℝ)⁻¹

/-- The logarithmic reciprocal-LCM kernel that results after differentiating
the diagonal Mellin factors at the zeta pole.  The scalar `c` records the
archimedean constant and is deliberately left exact. -/
noncomputable def cubicReciprocalLcmLogKernel (T c : ℝ) : ℝ :=
  ∑ d ∈ cubicMollifierSupport T, ∑ e ∈ cubicMollifierSupport T,
    cubicMollifierCoefficient T d * cubicMollifierCoefficient T e *
      (Nat.lcm d e : ℝ)⁻¹ *
        (c + 2 * Real.log (Nat.gcd d e) - Real.log d - Real.log e)

/-- Exact totient-square diagonalization for the actual cubic mollifier. -/
theorem cubicReciprocalLcmQuadratic_eq_totient (T : ℝ) :
    cubicReciprocalLcmQuadratic T =
      ∑ d ∈ cubicMollifierSupport T,
        (Nat.totient d : ℝ) * cubicMollifierDivisorMass T d ^ 2 := by
  unfold cubicReciprocalLcmQuadratic cubicMollifierDivisorMass
  exact MathlibAux.sum_reciprocal_lcm_quadratic_eq_totient_squares
    (cubicMollifierCoefficient T) (cubicMollifierLength T)

/-- Exact logarithmic diagonalization for the actual cubic mollifier. -/
theorem cubicReciprocalLcmLogKernel_eq (T c : ℝ) :
    cubicReciprocalLcmLogKernel T c =
      ∑ d ∈ cubicMollifierSupport T,
        ((c * (Nat.totient d : ℝ) + 2 * MathlibAux.gcdLogWeight d) *
            cubicMollifierDivisorMass T d ^ 2 -
          2 * (Nat.totient d : ℝ) * cubicMollifierDivisorMass T d *
            cubicMollifierLogDivisorMass T d) := by
  unfold cubicReciprocalLcmLogKernel cubicMollifierDivisorMass
    cubicMollifierLogDivisorMass
  exact MathlibAux.sum_reciprocal_lcm_log_kernel_eq
    (cubicMollifierCoefficient T) (cubicMollifierLength T) c

end PrimeNumberTheorem.MWKFCubic
