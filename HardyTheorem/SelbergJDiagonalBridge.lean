import HardyTheorem.SelbergJDiagonalFixedBridge

open Complex MeasureTheory Set

namespace HardyTheorem

/-! # Assembly of the complete diagonal part of Selberg's `J` -/

noncomputable def selbergJDiagonalNestedOriginalSum
    (delta x theta : ℝ) (X : ℕ) : ℂ :=
  ∑ kappa ∈ Finset.Icc 1 X,
    ∑ lambda ∈ Finset.Icc 1 X,
      ∑ mu ∈ Finset.Icc 1 X,
        ∑ nu ∈ Finset.Icc 1 X,
          selbergDiagonalMollifierBase X kappa nu mu lambda *
            ((∑' j : ℕ, ∫ u in Ioi x,
              selbergDiagonalOriginalIntegrand
                (selbergDiagonalGaussianParameter delta kappa mu
                  (Nat.gcd (kappa * nu) (lambda * mu))) theta j u : ℝ) : ℂ)

theorem selbergJDiagonalPart_eq_nestedOriginalSum
    {delta theta x : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hx : 1 ≤ x) (htheta : 0 < theta) (hthetaHalf : theta ≤ 1 / 2)
    {X : ℕ} (hX : 2 ≤ X) :
    selbergJDiagonalPart delta x theta X =
      selbergJDiagonalNestedOriginalSum delta x theta X := by
  classical
  let f := selbergJIntegratedExpandedPair delta x theta X
  let D := selbergJDiagonalIndexSet X
  have hf : Summable f := summable_selbergJIntegratedExpandedPair
    hdelta hdelta1 htheta.le hx hX
  have hD : Summable (D.indicator f) := hf.indicator D
  unfold selbergJDiagonalPart
  change (∑' q, D.indicator f q) = _
  rw [hD.tsum_prod, tsum_fintype]
  have hsubtype :
      (∑ o : SelbergJOuterIndex X,
          ∑' p : ℕ × ℕ, D.indicator f (o, p)) =
        ∑ o ∈ selbergJOuterFinset X,
          selbergJDiagonalDoubleSeries delta x theta X
            o.1.1 o.1.2 o.2.1 o.2.2 := by
    let G : ((ℕ × ℕ) × (ℕ × ℕ)) → ℂ := fun o =>
      selbergJDiagonalDoubleSeries delta x theta X
        o.1.1 o.1.2 o.2.1 o.2.2
    calc
      (∑ o : SelbergJOuterIndex X,
          ∑' p : ℕ × ℕ, D.indicator f (o, p)) =
          ∑ o : SelbergJOuterIndex X, G o.val := by
        apply Finset.sum_congr rfl
        intro o ho
        dsimp [G]
        unfold selbergJDiagonalDoubleSeries
        apply tsum_congr
        intro p
        simp only [D, selbergJDiagonalIndexSet, Set.indicator, Set.mem_ofPred_eq]
        dsimp [f]
        rw [selbergJIntegratedExpandedPair_eq_offDiagonalPairContribution]
        rfl
      _ = ∑ o ∈ selbergJOuterFinset X, G o :=
        (Finset.sum_subtype (selbergJOuterFinset X)
          (fun _ => Iff.rfl) G).symm
      _ = _ := rfl
  rw [hsubtype]
  unfold selbergJDiagonalNestedOriginalSum selbergJOuterFinset
  let S := Finset.Icc 1 X
  let F : ((ℕ × ℕ) × (ℕ × ℕ)) → ℂ := fun o =>
    selbergJDiagonalDoubleSeries delta x theta X
      o.1.1 o.1.2 o.2.1 o.2.2
  change (∑ o ∈ (S.product S).product (S.product S), F o) = _
  calc
    (∑ o ∈ (S.product S).product (S.product S), F o) =
        ∑ kl ∈ S.product S, ∑ mn ∈ S.product S, F (kl, mn) :=
      Finset.sum_product (S.product S) (S.product S) F
    _ = ∑ kappa ∈ S, ∑ lambda ∈ S,
          ∑ mn ∈ S.product S, F ((kappa, lambda), mn) :=
      Finset.sum_product S S
        (fun kl => ∑ mn ∈ S.product S, F (kl, mn))
    _ = ∑ kappa ∈ S, ∑ lambda ∈ S,
          ∑ mu ∈ S, ∑ nu ∈ S, F ((kappa, lambda), (mu, nu)) := by
      apply Finset.sum_congr rfl
      intro kappa hkappa
      apply Finset.sum_congr rfl
      intro lambda hlambda
      exact Finset.sum_product S S
        (fun mn => F ((kappa, lambda), mn))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro kappa hkappa
      apply Finset.sum_congr rfl
      intro lambda hlambda
      apply Finset.sum_congr rfl
      intro mu hmu
      apply Finset.sum_congr rfl
      intro nu hnu
      dsimp [F]
      exact selbergJDiagonalDoubleSeries_eq_originalRay
        hdelta hdelta1 hx htheta hthetaHalf hX
        (Finset.mem_Icc.mp hkappa).1 (Finset.mem_Icc.mp hkappa).2
        (Finset.mem_Icc.mp hlambda).1 (Finset.mem_Icc.mp hlambda).2
        (Finset.mem_Icc.mp hmu).1 (Finset.mem_Icc.mp hmu).2
        (Finset.mem_Icc.mp hnu).1 (Finset.mem_Icc.mp hnu).2

theorem selbergJDiagonalNestedOriginalSum_eq_physicalOriginalSum
    (delta x theta : ℝ) (X : ℕ) :
    selbergJDiagonalNestedOriginalSum delta x theta X =
      selbergDiagonalPhysicalOriginalSum delta x theta X := by
  classical
  let S := Finset.Icc 1 X
  let T : ℕ → ℕ → ℕ → ℕ → ℂ := fun kappa lambda mu nu =>
    selbergDiagonalMollifierBase X kappa nu mu lambda *
      ((∑' j : ℕ, ∫ u in Ioi x,
        selbergDiagonalOriginalIntegrand
          (selbergDiagonalGaussianParameter delta kappa mu
            (Nat.gcd (kappa * nu) (lambda * mu))) theta j u : ℝ) : ℂ)
  unfold selbergJDiagonalNestedOriginalSum selbergDiagonalPhysicalOriginalSum
  change (∑ kappa ∈ S, ∑ lambda ∈ S, ∑ mu ∈ S, ∑ nu ∈ S,
      T kappa lambda mu nu) = _
  have hrawToSubtype : ∀ F : ℕ → ℂ,
      (∑ n ∈ S, F n) = ∑ n : selbergTaperIndex X, F n.1 := by
    intro F
    exact Finset.sum_subtype S (fun _ => Iff.rfl) F
  calc
    (∑ kappa ∈ S, ∑ lambda ∈ S, ∑ mu ∈ S, ∑ nu ∈ S,
        T kappa lambda mu nu) =
      ∑ kappa : selbergTaperIndex X,
        ∑ lambda : selbergTaperIndex X,
          ∑ mu : selbergTaperIndex X,
            ∑ nu : selbergTaperIndex X,
              T kappa.1 lambda.1 mu.1 nu.1 := by
        rw [hrawToSubtype]
        apply Finset.sum_congr rfl
        intro kappa hkappa
        rw [hrawToSubtype]
        apply Finset.sum_congr rfl
        intro lambda hlambda
        rw [hrawToSubtype]
        apply Finset.sum_congr rfl
        intro mu hmu
        rw [hrawToSubtype]
    _ = ∑ kappa : selbergTaperIndex X,
        ∑ nu : selbergTaperIndex X,
          ∑ mu : selbergTaperIndex X,
            ∑ lambda : selbergTaperIndex X,
              T kappa.1 lambda.1 mu.1 nu.1 := by
      apply Finset.sum_congr rfl
      intro kappa hkappa
      calc
        (∑ lambda : selbergTaperIndex X,
            ∑ mu : selbergTaperIndex X,
              ∑ nu : selbergTaperIndex X,
                T kappa.1 lambda.1 mu.1 nu.1) =
            ∑ mu : selbergTaperIndex X,
              ∑ lambda : selbergTaperIndex X,
                ∑ nu : selbergTaperIndex X,
                  T kappa.1 lambda.1 mu.1 nu.1 := Finset.sum_comm
        _ = ∑ mu : selbergTaperIndex X,
              ∑ nu : selbergTaperIndex X,
                ∑ lambda : selbergTaperIndex X,
                  T kappa.1 lambda.1 mu.1 nu.1 := by
            apply Finset.sum_congr rfl
            intro mu hmu
            exact Finset.sum_comm
        _ = ∑ nu : selbergTaperIndex X,
              ∑ mu : selbergTaperIndex X,
                ∑ lambda : selbergTaperIndex X,
                  T kappa.1 lambda.1 mu.1 nu.1 := Finset.sum_comm
    _ = _ := by
      simp only [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro kappa hkappa
      apply Finset.sum_congr rfl
      intro nu hnu
      apply Finset.sum_congr rfl
      intro mu hmu
      apply Finset.sum_congr rfl
      intro lambda hlambda
      simp only [T, selbergArithmeticDiagonalGcd]
      rw [Nat.mul_comm mu.1 lambda.1]

theorem selbergJDiagonalPart_eq_physicalOriginalSum
    {delta theta x : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hx : 1 ≤ x) (htheta : 0 < theta) (hthetaHalf : theta ≤ 1 / 2)
    {X : ℕ} (hX : 2 ≤ X) :
    selbergJDiagonalPart delta x theta X =
      selbergDiagonalPhysicalOriginalSum delta x theta X := by
  rw [selbergJDiagonalPart_eq_nestedOriginalSum
    hdelta hdelta1 hx htheta hthetaHalf hX,
    selbergJDiagonalNestedOriginalSum_eq_physicalOriginalSum]

end HardyTheorem
