import HardyTheorem.SelbergShortCollectedArithmetic
import MathlibAux.SlidingExponentialCoefficientBound

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

/-- The sliding interval transform also vanishes throughout the ineffective
top range. -/
theorem sliding_selbergShortDirichletCollectedCoeff_eq_zero_of_topRange
    {N X k : ℕ} (hX : 2 ≤ X)
    (hk : N * X * (X - 1) < k) (H : ℝ) :
    MathlibAux.slidingExponentialCoefficient H
        (selbergShortDirichletCollectedCoeff N X)
        selbergShortDirichletCollectedFrequency k = 0 := by
  rw [MathlibAux.slidingExponentialCoefficient,
    selbergShortDirichletCollectedCoeff_eq_zero_of_topRange hX hk,
    zero_mul]

/-- The complete transformed square energy is unchanged when the formal
product support is shortened to the effective endpoint `N * X * (X - 1)`. -/
theorem sum_normSq_sliding_selbergShortDirichletCollectedCoeff_eq_effectiveSupport
    {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X) (H : ℝ) :
    (∑ k ∈ Finset.Ioc 1 (N * X * X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) =
      ∑ k ∈ Finset.Ioc 1 (N * X * (X - 1)),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k) := by
  have honeX : 1 ≤ X := by omega
  have honePred : 1 ≤ X - 1 := by omega
  have honeEffective : 1 ≤ N * X * (X - 1) :=
    Nat.mul_pos (Nat.mul_pos hN honeX) honePred
  have heffectiveFormal : N * X * (X - 1) ≤ N * X * X :=
    Nat.mul_le_mul_left (N * X) (Nat.sub_le X 1)
  have hsplit :
      Finset.Ioc 1 (N * X * (X - 1)) ∪
          Finset.Ioc (N * X * (X - 1)) (N * X * X) =
        Finset.Ioc 1 (N * X * X) :=
    Finset.Ioc_union_Ioc_eq_Ioc honeEffective heffectiveFormal
  have hdisjoint :
      Disjoint (Finset.Ioc 1 (N * X * (X - 1)))
        (Finset.Ioc (N * X * (X - 1)) (N * X * X)) :=
    Finset.Ioc_disjoint_Ioc_of_le le_rfl
  rw [← hsplit, Finset.sum_union hdisjoint]
  have htop :
      (∑ k ∈ Finset.Ioc (N * X * (X - 1)) (N * X * X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [sliding_selbergShortDirichletCollectedCoeff_eq_zero_of_topRange
      hX (Finset.mem_Ioc.mp hk).1 H]
    simp
  rw [htop, add_zero]

end HardyTheorem
