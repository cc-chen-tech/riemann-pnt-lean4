import HardyTheorem.SelbergShortCollectedArithmetic

namespace HardyTheorem

/-!
# Vanishing at the top of the Selberg short support

The linear logarithmic cutoff is zero at its right endpoint.  Consequently
the final mollifier factor removes every collected product above
`N * X * (X - 1)`; the formal product support `N * X * X` is not effective.
-/

/-- The linearly tapered Selberg Moebius coefficient vanishes at its right
endpoint. -/
@[simp] theorem selbergMoebiusCoeff_self_eq_zero
    {X : ℕ} (hX : 2 ≤ X) :
    selbergMoebiusCoeff X X = 0 := by
  have hXReal : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  have hlogX : Real.log (X : ℝ) ≠ 0 := (Real.log_pos hXReal).ne'
  rw [selbergMoebiusCoeff, selbergMoebiusWeight, div_self hlogX]
  ring

/-- Every collected coefficient strictly above `N * X * (X - 1)` vanishes.
The proof uses the exact endpoint zero of the final mollifier factor. -/
theorem selbergShortDirichletCollectedCoeff_eq_zero_of_topRange
    {N X k : ℕ} (hX : 2 ≤ X)
    (hk : N * X * (X - 1) < k) :
    selbergShortDirichletCollectedCoeff N X k = 0 := by
  classical
  rw [selbergShortDirichletCollectedCoeff_eq_convolution]
  have hconv : selbergShortCollectedDirichletConvolution N X k = 0 := by
    unfold selbergShortCollectedDirichletConvolution
    apply Finset.sum_eq_zero
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpSupport, hpMul⟩
    rcases Finset.mem_product.mp hpSupport with ⟨hpFirst, hpSecond⟩
    have hpFirstLe : p.1 ≤ N * X := (Finset.mem_Icc.mp hpFirst).2
    have hpSecondLe : p.2 ≤ X := (Finset.mem_Icc.mp hpSecond).2
    have hpSecondEq : p.2 = X := by
      by_contra hpNe
      have hpSecondLt : p.2 < X := lt_of_le_of_ne hpSecondLe hpNe
      have hpSecondPred : p.2 ≤ X - 1 := by omega
      have hprodLe : p.1 * p.2 ≤ N * X * (X - 1) :=
        Nat.mul_le_mul hpFirstLe hpSecondPred
      omega
    rw [hpSecondEq, selbergMoebiusCoeff_self_eq_zero hX, mul_zero]
  rw [hconv]
  simp

end HardyTheorem
