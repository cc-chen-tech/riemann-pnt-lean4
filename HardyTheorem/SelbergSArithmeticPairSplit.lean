import HardyTheorem.SelbergSArithmeticPairReindex

open Complex Nat
open scoped BigOperators

namespace HardyTheorem

/-!
# Exact smooth/coprime split of Selberg's arithmetic pair sum

This is the finite identity before any absolute values or estimates are
taken.  The first mollifier variable carries the shift `theta`; the second
one carries shift zero.
-/

noncomputable def selbergArithmeticPairTerm
    (X : ℕ) (theta : ℝ) (kappa nu : ℕ) : ℂ :=
  ((selbergSqrtZetaTaperedCoeff X kappa : ℂ) *
      (kappa : ℂ) ^ (-((1 - theta : ℝ) : ℂ))) *
    ((selbergSqrtZetaTaperedCoeff X nu : ℂ) *
      (nu : ℂ) ^ (-((1 - (0 : ℝ) : ℝ) : ℂ)))

noncomputable def selbergArithmeticPairSum
    (rho X : ℕ) (theta : ℝ) : ℂ :=
  ∑ kappa : selbergTaperIndex X,
    ∑ nu : selbergTaperIndex X,
      if rho ∣ kappa.1 * nu.1 then
        selbergArithmeticPairTerm X theta kappa.1 nu.1
      else 0

noncomputable def selbergSmoothOuterFactor
    (X : ℕ) (theta : ℝ) (d : ℕ) : ℂ :=
  (selbergSqrtZetaCoeff d : ℂ) *
      (d : ℂ) ^ (-((1 - theta : ℝ) : ℂ)) /
    (Real.log (X : ℝ) : ℂ)

noncomputable def selbergCoprimeLocalFactor
    (rho X : ℕ) (theta : ℝ) (d k : ℕ) : ℂ :=
  selbergS12ShiftedCoprimeCoeff rho theta k *
    perronLogCutoff ((k : ℝ) / ((X : ℝ) / (d : ℝ)))

/-- Exact finite form of Selberg's equation (S17), before grouping the
coprime residual sums. -/
theorem selbergArithmeticPairSum_eq_split
    {rho X : ℕ} [NeZero rho] (theta : ℝ) (hX : 2 ≤ X) :
    selbergArithmeticPairSum rho X theta =
      ∑ p : selbergSmoothCoprimeIndex rho X,
        ∑ q : selbergSmoothCoprimeIndex rho X,
          if rho ∣ p.1.1.1 * q.1.1.1 then
            (selbergSmoothOuterFactor X theta p.1.1.1 *
              selbergCoprimeLocalFactor rho X theta p.1.1.1 p.1.2.1) *
            (selbergSmoothOuterFactor X 0 q.1.1.1 *
              selbergCoprimeLocalFactor rho X 0 q.1.1.1 q.1.2.1)
          else 0 := by
  unfold selbergArithmeticPairSum
  rw [selbergArithmeticPairSum_reindex
    (f := selbergArithmeticPairTerm X theta)]
  apply Fintype.sum_congr
  intro p
  apply Fintype.sum_congr
  intro q
  by_cases hdiv : rho ∣ p.1.1.1 * q.1.1.1
  · rw [if_pos hdiv, if_pos hdiv]
    have hp := selbergTaperedShiftedTerm_split theta hX
      (Finset.mem_Icc.mp p.1.1.2).1
      (Finset.mem_Icc.mp p.1.2.2).1 p.2.2.2 p.2.1 p.2.2.1
    have hq := selbergTaperedShiftedTerm_split 0 hX
      (Finset.mem_Icc.mp q.1.1.2).1
      (Finset.mem_Icc.mp q.1.2.2).1 q.2.2.2 q.2.1 q.2.2.1
    unfold selbergArithmeticPairTerm selbergSmoothOuterFactor
      selbergCoprimeLocalFactor
    rw [hp, hq]
  · rw [if_neg hdiv, if_neg hdiv]

end HardyTheorem
