import HardyTheorem.SelbergSmoothCoprimeEquiv

open Nat
open scoped BigOperators

namespace HardyTheorem

/-!
# Exact pair reindexing for Selberg's arithmetic sum

The divisibility condition in Selberg's grouped quadratic sum becomes a
condition on the two smooth parts alone.  This file keeps that cancellation
separate from the later analytic estimates.
-/

theorem selbergSmoothCoprime_rho_dvd_products_iff
    {rho X : ℕ} (p q : selbergSmoothCoprimeIndex rho X) :
    rho ∣ (p.1.1.1 * p.1.2.1) * (q.1.1.1 * q.1.2.1) ↔
      rho ∣ p.1.1.1 * q.1.1.1 := by
  have hcop : rho.Coprime (p.1.2.1 * q.1.2.1) :=
    p.2.2.1.symm.mul_right q.2.2.1.symm
  rw [show (p.1.1.1 * p.1.2.1) * (q.1.1.1 * q.1.2.1) =
      (p.1.1.1 * q.1.1.1) * (p.1.2.1 * q.1.2.1) by ac_rfl]
  exact hcop.dvd_mul_right

/-- Reindex both finite taper variables by their unique smooth/coprime
decompositions and remove the coprime residual factors from `rho ∣ κν`. -/
theorem selbergArithmeticPairSum_reindex
    {M : Type*} [AddCommMonoid M] {rho X : ℕ} [NeZero rho]
    (f : ℕ → ℕ → M) :
    (∑ kappa : selbergTaperIndex X,
        ∑ nu : selbergTaperIndex X,
          if rho ∣ kappa.1 * nu.1 then f kappa.1 nu.1 else 0) =
      ∑ p : selbergSmoothCoprimeIndex rho X,
        ∑ q : selbergSmoothCoprimeIndex rho X,
          if rho ∣ p.1.1.1 * q.1.1.1 then
            f (p.1.1.1 * p.1.2.1) (q.1.1.1 * q.1.2.1)
          else 0 := by
  let e := selbergSmoothCoprimeEquiv (X := X) (NeZero.ne rho)
  refine Fintype.sum_equiv e _ _ ?_
  intro kappa
  refine Fintype.sum_equiv e _ _ ?_
  intro nu
  have hkappa := selbergSmoothCoprimeEquiv_apply_product (NeZero.ne rho) kappa
  have hnu := selbergSmoothCoprimeEquiv_apply_product (NeZero.ne rho) nu
  dsimp [e]
  have hcond :
      (rho ∣ kappa.1 * nu.1) ↔
        rho ∣
          (selbergSmoothCoprimeEquiv (NeZero.ne rho) kappa).1.1.1 *
            (selbergSmoothCoprimeEquiv (NeZero.ne rho) nu).1.1.1 := by
    rw [← hkappa, ← hnu]
    exact selbergSmoothCoprime_rho_dvd_products_iff _ _
  by_cases h : rho ∣ kappa.1 * nu.1
  · rw [if_pos h, if_pos (hcond.mp h), hkappa, hnu]
  · rw [if_neg h, if_neg (fun hsmooth => h (hcond.mpr hsmooth))]

end HardyTheorem
