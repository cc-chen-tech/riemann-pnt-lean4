import HardyTheorem.SelbergSArithmeticLocalSum

open Complex Nat
open scoped BigOperators

namespace HardyTheorem

/-!
# Grouped form of Selberg's arithmetic pair sum

Finite Fubini and distributivity collect both coprime fibers before any
absolute values are taken.  The resulting identity is the exact form to
which the two asymmetric S12 estimates apply.
-/

theorem selberg_sum_sigma_pair_factor
    {D : Type*} [Fintype D]
    {K : D → Type*} [(d : D) → Fintype (K d)]
    (cond : D → D → Prop) [DecidableRel cond]
    (A B : (d : D) → K d → ℂ) :
    (∑ p : (d : D) × K d, ∑ q : (d : D) × K d,
        if cond p.1 q.1 then A p.1 p.2 * B q.1 q.2 else 0) =
      ∑ d : D, ∑ e : D, if cond d e then
        (∑ k : K d, A d k) * (∑ l : K e, B e l) else 0 := by
  classical
  simp_rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases h : cond d e
  · simp only [if_pos h]
    calc
      (∑ k : K d, ∑ l : K e, A d k * B e l) =
          ∑ k : K d, A d k * (∑ l : K e, B e l) := by
        apply Finset.sum_congr rfl
        intro k _hk
        rw [Finset.mul_sum]
      _ = (∑ k : K d, A d k) * (∑ l : K e, B e l) := by
        rw [Finset.sum_mul]
  · simp only [if_neg h, Finset.sum_const_zero]

noncomputable def selbergArithmeticGroupedSum
    (rho X : ℕ) (theta : ℝ) : ℂ :=
  ∑ d : selbergSmoothOuterIndex rho X,
    ∑ e : selbergSmoothOuterIndex rho X,
      if rho ∣ d.1 * e.1 then
        (selbergSmoothOuterFactor X theta d.1 *
          selbergS12WeightedCoprimeSumReal rho theta
            ((X : ℝ) / (d.1 : ℝ))) *
        (selbergSmoothOuterFactor X 0 e.1 *
          selbergS12WeightedCoprimeSumReal rho 0
            ((X : ℝ) / (e.1 : ℝ)))
      else 0

/-- Exact grouped S17 identity, with the local real cutoffs `X / d` and
the shift-zero second factor retained. -/
theorem selbergArithmeticPairSum_eq_grouped
    {rho X : ℕ} [NeZero rho] (theta : ℝ) (hX : 2 ≤ X) :
    selbergArithmeticPairSum rho X theta =
      selbergArithmeticGroupedSum rho X theta := by
  classical
  rw [selbergArithmeticPairSum_eq_split theta hX]
  let E := selbergSplitIndexSigmaEquiv rho X
  let A : (d : selbergSmoothOuterIndex rho X) →
      selbergCoprimeFiberIndex rho X d → ℂ :=
    fun d k =>
      selbergSmoothOuterFactor X theta d.1 *
        selbergCoprimeLocalFactor rho X theta d.1 k.1
  let B : (d : selbergSmoothOuterIndex rho X) →
      selbergCoprimeFiberIndex rho X d → ℂ :=
    fun d k =>
      selbergSmoothOuterFactor X 0 d.1 *
        selbergCoprimeLocalFactor rho X 0 d.1 k.1
  calc
    (∑ p : selbergSmoothCoprimeIndex rho X,
        ∑ q : selbergSmoothCoprimeIndex rho X,
          if rho ∣ p.1.1.1 * q.1.1.1 then
            (selbergSmoothOuterFactor X theta p.1.1.1 *
              selbergCoprimeLocalFactor rho X theta p.1.1.1 p.1.2.1) *
            (selbergSmoothOuterFactor X 0 q.1.1.1 *
              selbergCoprimeLocalFactor rho X 0 q.1.1.1 q.1.2.1)
          else 0) =
        ∑ p : (d : selbergSmoothOuterIndex rho X) ×
              selbergCoprimeFiberIndex rho X d,
          ∑ q : (d : selbergSmoothOuterIndex rho X) ×
              selbergCoprimeFiberIndex rho X d,
            if rho ∣ p.1.1 * q.1.1 then
              A p.1 p.2 * B q.1 q.2 else 0 := by
      refine Fintype.sum_equiv E _ _ ?_
      intro p
      refine Fintype.sum_equiv E _ _ ?_
      intro q
      rfl
    _ = ∑ d : selbergSmoothOuterIndex rho X,
          ∑ e : selbergSmoothOuterIndex rho X,
            if rho ∣ d.1 * e.1 then
              (∑ k : selbergCoprimeFiberIndex rho X d, A d k) *
                (∑ l : selbergCoprimeFiberIndex rho X e, B e l)
            else 0 :=
      selberg_sum_sigma_pair_factor
        (fun d e : selbergSmoothOuterIndex rho X => rho ∣ d.1 * e.1) A B
    _ = selbergArithmeticGroupedSum rho X theta := by
      unfold selbergArithmeticGroupedSum
      apply Finset.sum_congr rfl
      intro d _hd
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hdiv : rho ∣ d.1 * e.1
      · rw [if_pos hdiv, if_pos hdiv]
        dsimp [A, B]
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        rw [selbergCoprimeFiberSum_eq_weightedCoprimeSumReal d theta
          (show 0 < X by omega)]
        rw [selbergCoprimeFiberSum_eq_weightedCoprimeSumReal e 0
          (show 0 < X by omega)]
      · rw [if_neg hdiv, if_neg hdiv]

end HardyTheorem
