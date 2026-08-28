import HardyTheorem.AFECriticalDyadicBlockIdentity
import MathlibAux.DyadicPrefixDecomposition

/-!
# Pointwise maximal inequality for a moving mollified prefix

The critical-line Dirichlet atom is extended by zero outside the ambient
positive prefix `[1,2^K)`.  Its sum over any aligned dyadic block is therefore
exactly the owner polynomial from the collected coefficient construction.
-/

open Complex
open scoped BigOperators

namespace HardyTheorem
namespace AFE

private noncomputable def dyadicCriticalAmbientAtom
    (K : ℕ) (t : ℝ) (n : ℕ) : ℂ :=
  if n ∈ Finset.Ico 1 (2 ^ K) then
    1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)
  else 0

/-- A moving critical-line prefix, multiplied by the concrete Selberg
mollifier.  The prefix is written on `[0,m)` with a zero atom at `0`. -/
noncomputable def dyadicMovingPrefixMollifiedPolynomial
    (K m X : ℕ) (t : ℝ) : ℂ :=
  (∑ n ∈ Finset.Ico 0 m, dyadicCriticalAmbientAtom K t n) *
    selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)

/-- A fixed dyadic prefix times the concrete mollifier varies continuously
with the height. -/
theorem continuous_dyadicMovingPrefixMollifiedPolynomial
    (K m X : ℕ) :
    Continuous fun t : ℝ =>
      dyadicMovingPrefixMollifiedPolynomial K m X t := by
  unfold dyadicMovingPrefixMollifiedPolynomial
  apply Continuous.mul
  · apply continuous_finset_sum
    intro n hn
    unfold dyadicCriticalAmbientAtom
    split_ifs with hambient
    · have hn0 : n ≠ 0 := by
        exact Nat.ne_of_gt (Finset.mem_Ico.mp hambient).1
      rw [show (fun t : ℝ =>
          1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)) =
          fun t : ℝ =>
            (((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
              Complex.exp ((-I * (Real.log n : ℂ)) * t)) by
        funext t
        rw [inv_nat_cpow_criticalLine_eq_exp hn0 t]]
      fun_prop
    · exact continuous_const
  · simpa only [selbergMoebiusMollifier] using
      continuous_selbergMollifier_criticalLine X
        (fun n => (selbergMoebiusCoeff X n : ℂ))

private theorem mem_dyadicPrefixBlock_iff_div_eq
    {j q n : ℕ} :
    n ∈ MathlibAux.dyadicPrefixBlock j q ↔ n / 2 ^ j = q := by
  rw [MathlibAux.dyadicPrefixBlock, Finset.mem_Ico]
  have hpow : 0 < 2 ^ j := pow_pos (by omega) j
  constructor
  · intro hn
    exact Nat.div_eq_of_lt_le hn.1 hn.2
  · intro hdiv
    constructor
    · exact (Nat.le_div_iff_mul_le hpow).mp (by simpa [hdiv])
    · exact (Nat.div_lt_iff_lt_mul hpow).mp (by omega)

private theorem sum_dyadicCriticalAmbientAtom_block_eq_owner
    (K j q : ℕ) (t : ℝ) :
    (∑ n ∈ MathlibAux.dyadicPrefixBlock j q,
        dyadicCriticalAmbientAtom K t n) =
      dyadicOwnerDirichletPolynomial K j q t := by
  unfold dyadicCriticalAmbientAtom dyadicOwnerDirichletPolynomial
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr
  · ext n
    simp only [Finset.mem_filter, dyadicOwnerSupport, Finset.mem_filter]
    rw [mem_dyadicPrefixBlock_iff_div_eq]
    tauto
  · intro n hn
    rfl

private theorem sum_dyadicCriticalAmbientAtom_mul_mollifier_block_eq
    (K j q X : ℕ) (t : ℝ) :
    (∑ n ∈ MathlibAux.dyadicPrefixBlock j q,
        dyadicCriticalAmbientAtom K t n *
          selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) =
      dyadicMollifiedCriticalBlockPolynomial K j X q t := by
  rw [← Finset.sum_mul,
    sum_dyadicCriticalAmbientAtom_block_eq_owner,
    dyadicOwnerDirichletPolynomial_mul_mollifier_eq_blockPolynomial]

/-- Finite Rademacher--Menshov pointwise inequality for the actual moving
prefix times the Selberg mollifier. -/
theorem normSq_dyadicMovingPrefixMollifiedPolynomial_le_tree
    (K m X : ℕ) (hm : m ≤ 2 ^ K) (t : ℝ) :
    Complex.normSq (dyadicMovingPrefixMollifiedPolynomial K m X t) ≤
      (K + 1 : ℝ) *
        ∑ p ∈ MathlibAux.dyadicPrefixTree K 0,
          Complex.normSq
            (dyadicMollifiedCriticalBlockPolynomial K p.1 X p.2 t) := by
  let M := selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)
  let f : ℕ → ℂ := fun n => dyadicCriticalAmbientAtom K t n * M
  have hbase := MathlibAux.normSq_sum_Ico_le_dyadicPrefixTree
    K m 0 hm f
  have hbase' :
      Complex.normSq (∑ n ∈ Finset.Ico 0 m, f n) ≤
        (K + 1 : ℝ) *
          ∑ p ∈ MathlibAux.dyadicPrefixTree K 0,
            Complex.normSq
              (∑ n ∈ MathlibAux.dyadicPrefixBlock p.1 p.2, f n) := by
    simpa only [zero_mul, zero_add] using hbase
  have hprefix :
      (∑ n ∈ Finset.Ico 0 m, f n) =
        dyadicMovingPrefixMollifiedPolynomial K m X t := by
    dsimp only [f, M, dyadicMovingPrefixMollifiedPolynomial]
    rw [Finset.sum_mul]
  rw [hprefix] at hbase'
  refine hbase'.trans_eq ?_
  apply congrArg (fun z : ℝ => (K + 1 : ℝ) * z)
  apply Finset.sum_congr rfl
  intro p hp
  apply congrArg Complex.normSq
  dsimp only [f, M]
  exact sum_dyadicCriticalAmbientAtom_mul_mollifier_block_eq
    K p.1 p.2 X t

end AFE
end HardyTheorem
