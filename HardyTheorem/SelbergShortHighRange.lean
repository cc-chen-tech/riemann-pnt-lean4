import HardyTheorem.SelbergShortTopRangeVanishing

open scoped BigOperators

namespace HardyTheorem

/-!
# Sharp support for the high Selberg range

Both tapered Moebius factors vanish at their common right endpoint `X`.
Consequently a nonzero triple has both mollifier indices at most `X - 1`,
which shortens the effective high range from `N * X * (X - 1)` to
`N * (X - 1) * (X - 1)`.
-/

/-- The square energy in the unresolved high coefficient range is unchanged
when its endpoint is shortened from `N * X * (X - 1)` to the sharp product
support `N * (X - 1)^2`. -/
theorem sum_normSq_selbergShortDirichletCollectedCoeff_highRange_eq_sharpSupport
    {N X : ℕ} (hX : 2 ≤ X) :
    (∑ k ∈ Finset.Ioc N (N * X * (X - 1)),
        Complex.normSq (selbergShortDirichletCollectedCoeff N X k)) =
      ∑ k ∈ Finset.Ioc N (N * (X - 1) * (X - 1)),
        Complex.normSq (selbergShortDirichletCollectedCoeff N X k) := by
  classical
  have hpred : 1 ≤ X - 1 := by omega
  have hN_le_first : N ≤ N * (X - 1) := by
    simpa using Nat.mul_le_mul_left N hpred
  have hN_le_sharp : N ≤ N * (X - 1) * (X - 1) :=
    hN_le_first.trans (by
      simpa using Nat.mul_le_mul_left (N * (X - 1)) hpred)
  have hsharp_le_old :
      N * (X - 1) * (X - 1) ≤ N * X * (X - 1) := by
    exact Nat.mul_le_mul_right (X - 1)
      (Nat.mul_le_mul_left N (Nat.sub_le X 1))
  have hsplit :
      Finset.Ioc N (N * (X - 1) * (X - 1)) ∪
          Finset.Ioc (N * (X - 1) * (X - 1)) (N * X * (X - 1)) =
        Finset.Ioc N (N * X * (X - 1)) :=
    Finset.Ioc_union_Ioc_eq_Ioc hN_le_sharp hsharp_le_old
  have hdisjoint :
      Disjoint (Finset.Ioc N (N * (X - 1) * (X - 1)))
        (Finset.Ioc (N * (X - 1) * (X - 1)) (N * X * (X - 1))) :=
    Finset.Ioc_disjoint_Ioc_of_le le_rfl
  rw [← hsplit, Finset.sum_union hdisjoint]
  have htail :
      (∑ k ∈ Finset.Ioc (N * (X - 1) * (X - 1))
          (N * X * (X - 1)),
        Complex.normSq (selbergShortDirichletCollectedCoeff N X k)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkSharp : N * (X - 1) * (X - 1) < k :=
      (Finset.mem_Ioc.mp hk).1
    have hcoeff : selbergShortDirichletCollectedCoeff N X k = 0 := by
      unfold selbergShortDirichletCollectedCoeff
      apply Finset.sum_eq_zero
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpSupport, hpProduct⟩
      rcases Finset.mem_product.mp hpSupport with ⟨hmN, hdlX⟩
      rcases Finset.mem_product.mp hdlX with ⟨hdX, hlX⟩
      by_cases hd : p.2.1 = X
      · unfold selbergShortDirichletTripleCoeff
        rw [hd, selbergMoebiusCoeff_self_eq_zero hX]
        simp
      · by_cases hl : p.2.2 = X
        · unfold selbergShortDirichletTripleCoeff
          rw [hl, selbergMoebiusCoeff_self_eq_zero hX]
          simp
        · have hdPred : p.2.1 ≤ X - 1 := by
            have hdLe : p.2.1 ≤ X := (Finset.mem_Icc.mp hdX).2
            omega
          have hlPred : p.2.2 ≤ X - 1 := by
            have hlLe : p.2.2 ≤ X := (Finset.mem_Icc.mp hlX).2
            omega
          have hproductLe :
              p.1 * p.2.1 * p.2.2 ≤ N * (X - 1) * (X - 1) :=
            Nat.mul_le_mul (Nat.mul_le_mul
              (Finset.mem_Icc.mp hmN).2 hdPred) hlPred
          omega
    rw [hcoeff]
    simp
  rw [htail, add_zero]

end HardyTheorem
