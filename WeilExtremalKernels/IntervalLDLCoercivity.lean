import WeilExtremalKernels.ArchimedeanTailTransfer

/-!
# Quantitative coercivity from an exact LDL center

Positive pivots of an exact `LDL^T` center give positive definiteness, but an
interval transfer needs a quantitative lower margin.  This module records the
two additional rational bounds needed for that transfer:

* `delta` is a common lower bound for the diagonal of `D`;
* `kappa` controls the inverse of the coordinate map `x -> L^T x`.

They imply

`(delta / kappa) * ||x||^2 <= x^T (L D L^T) x`.

An entrywise interval enclosure with symmetric row budget `rho` is therefore
strictly positive whenever `rho < delta / kappa`.

The theorem is generic.  It does not claim that the current streaming Arb
workspace has already emitted exact values of `delta`, `kappa`, or `rho`.
-/

namespace WeilExtremalKernels

open scoped BigOperators

/-- Squared norm after applying the transpose-coordinate map associated with
the columns of `L`. -/
def transformedSquaredNorm {n : Nat}
    (L : FiniteMatrix n) (x : FiniteVector n) : Real :=
  ∑ k, (columnLinearForm L x k) ^ 2

theorem transformedSquaredNorm_nonneg {n : Nat}
    (L : FiniteMatrix n) (x : FiniteVector n) :
    0 <= transformedSquaredNorm L x := by
  exact Finset.sum_nonneg fun k _ => sq_nonneg (columnLinearForm L x k)

/-- A lower diagonal bound controls the LDL form in transformed coordinates. -/
theorem quadraticForm_ldlMatrix_lower_transformed {n : Nat}
    (L : FiniteMatrix n) (d x : FiniteVector n) (delta : Real)
    (hdiagonal : forall k, delta <= d k) :
    delta * transformedSquaredNorm L x <=
      quadraticForm (ldlMatrix L d) x := by
  rw [quadraticForm_ldlMatrix]
  unfold transformedSquaredNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul_of_nonneg_right
    (hdiagonal k) (sq_nonneg (columnLinearForm L x k))

/-- Quantitative data attached to an exact LDL center.

`inverse_bound` is the finite-dimensional estimate

`||x||^2 <= kappa * ||L^T x||^2`.

It can be certified from an exact inverse of `L^T` or from any rigorous
operator-norm upper bound for that inverse. -/
structure CoerciveLDLCertificate (n : Nat) extends LDLCertificate n where
  delta : Real
  kappa : Real
  delta_nonneg : 0 <= delta
  kappa_pos : 0 < kappa
  diagonal_lower : forall k, delta <= diagonal k
  inverse_bound :
    forall x,
      squaredNorm x <= kappa * transformedSquaredNorm lower x

/-- Matrix reconstructed by a quantitative LDL certificate. -/
def CoerciveLDLCertificate.reconstruct {n : Nat}
    (certificate : CoerciveLDLCertificate n) : FiniteMatrix n :=
  ldlMatrix certificate.lower certificate.diagonal

/-- The exact center has coercivity margin `delta / kappa`. -/
theorem quadraticForm_coerciveLDL_reconstruct_lower {n : Nat}
    (certificate : CoerciveLDLCertificate n)
    (x : FiniteVector n) :
    (certificate.delta / certificate.kappa) * squaredNorm x <=
      quadraticForm certificate.reconstruct x := by
  have hscale :
      0 <= certificate.delta / certificate.kappa :=
    div_nonneg certificate.delta_nonneg certificate.kappa_pos.le
  have hinverse :=
    mul_le_mul_of_nonneg_left (certificate.inverse_bound x) hscale
  have htransformed :=
    quadraticForm_ldlMatrix_lower_transformed
      certificate.lower certificate.diagonal x certificate.delta
      certificate.diagonal_lower
  calc
    (certificate.delta / certificate.kappa) * squaredNorm x <=
        (certificate.delta / certificate.kappa) *
          (certificate.kappa *
            transformedSquaredNorm certificate.lower x) :=
      hinverse
    _ = certificate.delta *
        transformedSquaredNorm certificate.lower x := by
      field_simp [certificate.kappa_pos.ne']
    _ <= quadraticForm certificate.reconstruct x :=
      htransformed

/-- A symmetric interval enclosure of a coercive LDL center is strictly
positive when its row budget is smaller than the certified coercivity margin. -/
theorem quadraticForm_pos_of_coerciveLDL_interval {n : Nat}
    (A C R : FiniteMatrix n)
    (certificate : CoerciveLDLCertificate n)
    (rho : Real)
    (hreconstruct : C = certificate.reconstruct)
    (hR : forall i j, R i j = R j i)
    (hentry : forall i j, |A i j - C i j| <= R i j)
    (hrow : forall i, (∑ j, R i j) <= rho)
    (hbudget : rho < certificate.delta / certificate.kappa) :
    forall x, x != 0 -> 0 < quadraticForm A x := by
  apply quadraticForm_pos_of_interval
    A C R (certificate.delta / certificate.kappa) rho
  · intro x
    rw [hreconstruct]
    exact quadraticForm_coerciveLDL_reconstruct_lower certificate x
  · exact hR
  · exact hentry
  · exact hrow
  · exact hbudget

/-- Strict interval-LDL positivity survives addition of any nonnegative
cutoff-free tail. -/
theorem quadraticForm_pos_of_coerciveLDL_interval_and_tail {n : Nat}
    (A C R H : FiniteMatrix n)
    (certificate : CoerciveLDLCertificate n)
    (rho : Real)
    (hreconstruct : C = certificate.reconstruct)
    (hR : forall i j, R i j = R j i)
    (hentry : forall i j, |A i j - C i j| <= R i j)
    (hrow : forall i, (∑ j, R i j) <= rho)
    (hbudget : rho < certificate.delta / certificate.kappa)
    (htail : forall x, 0 <= quadraticForm H x) :
    forall x, x != 0 -> 0 < quadraticForm (A + H) x :=
  quadraticForm_pos_add_of_tail_nonneg A H
    (quadraticForm_pos_of_coerciveLDL_interval
      A C R certificate rho hreconstruct hR hentry hrow hbudget)
    htail

end WeilExtremalKernels
