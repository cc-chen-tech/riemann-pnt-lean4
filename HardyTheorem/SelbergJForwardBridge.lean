import HardyTheorem.SelbergJPartition

open Complex MeasureTheory Set

namespace HardyTheorem

/-! # Reindexing the abstract positive-frequency part as the physical forward ray -/

theorem selbergJIntegratedExpandedPair_eq_offDiagonalPairContribution
    (delta x theta : ℝ) (X : ℕ)
    (q : SelbergJOuterIndex X × (ℕ × ℕ)) :
    selbergJIntegratedExpandedPair delta x theta X q =
      selbergPhysicalOffDiagonalPairContribution delta x theta X
        (q.2.1 + 1) q.1.val.1.1 q.1.val.1.2
        (q.2.2 + 1) q.1.val.2.1 q.1.val.2.2 := by
  unfold selbergJIntegratedExpandedPair selbergJGlobalExpandedPairIntegrand
    selbergPhysicalExpandedPairIntegrand
    selbergPhysicalOffDiagonalPairContribution
  rw [integral_const_mul]

noncomputable def selbergJForwardFixedPairSeries
    (delta x theta : ℝ) (X m kappa lambda mu nu : ℕ) : ℂ :=
  ∑' j : ℕ,
    if (j + 1) * lambda * mu < m * kappa * nu then
      selbergPhysicalOffDiagonalPairContribution
        delta x theta X m kappa lambda (j + 1) mu nu
    else 0

theorem selbergJForwardFixedPairSeries_eq_physicalForwardFixedSum
    (delta x theta : ℝ) (X : ℕ)
    {m kappa lambda mu nu : ℕ}
    (hlambda : 1 ≤ lambda) (hmu : 1 ≤ mu) :
    selbergJForwardFixedPairSeries delta x theta X m kappa lambda mu nu =
      selbergPhysicalForwardFixedSum delta x theta X m kappa lambda mu nu := by
  classical
  let K := m * (kappa * nu)
  let d := lambda * mu
  let N := selbergPositiveGapCount K d
  let F : ℕ → ℂ := fun n => selbergPhysicalOffDiagonalPairContribution
    delta x theta X m kappa lambda n mu nu
  have hd : 1 ≤ d := Nat.mul_pos hlambda hmu
  unfold selbergJForwardFixedPairSeries selbergPhysicalForwardFixedSum
  simp only [Nat.mul_assoc]
  change (∑' j : ℕ, if (j + 1) * d < K then F (j + 1) else 0) =
    ∑ n ∈ Finset.Icc 1 N, F n
  rw [tsum_eq_sum (s := Finset.range N)]
  · have hleft :
        (∑ j ∈ Finset.range N,
          if (j + 1) * d < K then F (j + 1) else 0) =
          ∑ j ∈ Finset.range N, F (j + 1) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjN : j + 1 ≤ N := by simpa using Finset.mem_range.mp hj
        have hjmem : j + 1 ∈ Finset.Icc 1 N :=
          Finset.mem_Icc.mpr ⟨Nat.le_add_left 1 j, hjN⟩
        have hgap := ((selberg_positive_gap_admissible_iff hd).mpr hjmem).2
        rw [if_pos hgap]
    rw [hleft]
    symm
    refine Finset.sum_bij (fun n _hn => n - 1) ?_ ?_ ?_ ?_
    · intro n hn
      have hn' := Finset.mem_Icc.mp hn
      exact Finset.mem_range.mpr (by omega)
    · intro a ha b hb hab
      have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
      have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
      omega
    · intro j hj
      refine ⟨j + 1, Finset.mem_Icc.mpr ⟨Nat.le_add_left 1 j, ?_⟩, ?_⟩
      · simpa using Finset.mem_range.mp hj
      · omega
    · intro n hn
      have hn1 := (Finset.mem_Icc.mp hn).1
      congr 1
      omega
  · intro j hj
    simp only [not_lt, Finset.mem_range] at hj
    have hnot : ¬(j + 1) * d < K := by
      intro hgap
      have hjmem := (selberg_positive_gap_admissible_iff hd).mp
        ⟨Nat.le_add_left 1 j, hgap⟩
      have hjle := (Finset.mem_Icc.mp hjmem).2
      omega
    rw [if_neg hnot]

noncomputable def selbergJForwardDoubleSeries
    (delta x theta : ℝ) (X kappa lambda mu nu : ℕ) : ℂ :=
  ∑' p : ℕ × ℕ,
    if (p.2 + 1) * lambda * mu < (p.1 + 1) * kappa * nu then
      selbergPhysicalOffDiagonalPairContribution delta x theta X
        (p.1 + 1) kappa lambda (p.2 + 1) mu nu
    else 0

theorem selbergJForwardDoubleSeries_eq_physicalForwardRaySum
    {delta theta x : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (htheta : 0 ≤ theta) (hx : 1 ≤ x)
    {X kappa lambda mu nu : ℕ} (hX : 2 ≤ X)
    (hkappa : 1 ≤ kappa) (hkappaX : kappa ≤ X)
    (hlambda : 1 ≤ lambda) (hlambdaX : lambda ≤ X)
    (hmu : 1 ≤ mu) (hmuX : mu ≤ X)
    (hnu : 1 ≤ nu) (hnuX : nu ≤ X) :
    selbergJForwardDoubleSeries delta x theta X kappa lambda mu nu =
      selbergPhysicalForwardRaySum delta x theta X kappa lambda mu nu := by
  let f : (ℕ × ℕ) → ℂ := fun p =>
    selbergPhysicalOffDiagonalPairContribution delta x theta X
      (p.1 + 1) kappa lambda (p.2 + 1) mu nu
  have hnorm := summable_integral_norm_selbergPhysicalExpandedPairIntegrand
    hdelta hdelta1 htheta hx hX hkappa hkappaX hlambda hlambdaX
      hmu hmuX hnu hnuX
  have hf : Summable f := by
    apply Summable.of_norm_bounded hnorm
    intro p
    rw [show f p = ∫ u in Ioi x,
        selbergPhysicalExpandedPairIntegrand delta theta X
          kappa lambda mu nu p u by
      dsimp [f]
      unfold selbergPhysicalOffDiagonalPairContribution
        selbergPhysicalExpandedPairIntegrand
      rw [integral_const_mul]]
    exact norm_integral_le_integral_norm _
  let P : Set (ℕ × ℕ) := {p |
    (p.2 + 1) * lambda * mu < (p.1 + 1) * kappa * nu}
  have hP : Summable (P.indicator f) := hf.indicator P
  unfold selbergJForwardDoubleSeries selbergPhysicalForwardRaySum
  have hind :
      (∑' p : ℕ × ℕ,
        if (p.2 + 1) * lambda * mu < (p.1 + 1) * kappa * nu then
          selbergPhysicalOffDiagonalPairContribution delta x theta X
            (p.1 + 1) kappa lambda (p.2 + 1) mu nu
        else 0) = ∑' p : ℕ × ℕ, P.indicator f p := by
    apply tsum_congr
    intro p
    simp [P, f, Set.indicator]
  rw [hind]
  rw [hP.tsum_prod]
  apply tsum_congr
  intro j
  rw [← selbergJForwardFixedPairSeries_eq_physicalForwardFixedSum
    delta x theta X hlambda hmu]
  unfold selbergJForwardFixedPairSeries
  apply tsum_congr
  intro c
  simp [P, f, Set.indicator]

theorem selbergJForwardPart_eq_physicalPositiveOffDiagonalSum
    {delta theta x : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (htheta : 0 ≤ theta) (hx : 1 ≤ x)
    {X : ℕ} (hX : 2 ≤ X) :
    selbergJForwardPart delta x theta X =
      selbergPhysicalPositiveOffDiagonalSum delta x theta X := by
  classical
  let f := selbergJIntegratedExpandedPair delta x theta X
  let P := selbergJForwardIndexSet X
  have hf : Summable f := summable_selbergJIntegratedExpandedPair
    hdelta hdelta1 htheta hx hX
  have hP : Summable (P.indicator f) := hf.indicator P
  unfold selbergJForwardPart
  change (∑' q, P.indicator f q) = _
  rw [hP.tsum_prod, tsum_fintype]
  have hsubtype :
      (∑ o : SelbergJOuterIndex X,
          ∑' p : ℕ × ℕ, P.indicator f (o, p)) =
        ∑ o ∈ selbergJOuterFinset X,
          selbergJForwardDoubleSeries delta x theta X
            o.1.1 o.1.2 o.2.1 o.2.2 := by
    let G : ((ℕ × ℕ) × (ℕ × ℕ)) → ℂ := fun o =>
      selbergJForwardDoubleSeries delta x theta X
        o.1.1 o.1.2 o.2.1 o.2.2
    calc
      (∑ o : SelbergJOuterIndex X,
          ∑' p : ℕ × ℕ, P.indicator f (o, p)) =
          ∑ o : SelbergJOuterIndex X, G o.val := by
        apply Finset.sum_congr rfl
        intro o ho
        dsimp [G]
        unfold selbergJForwardDoubleSeries
        apply tsum_congr
        intro p
        simp only [P, selbergJForwardIndexSet, Set.indicator, Set.mem_ofPred_eq]
        dsimp [f]
        rw [selbergJIntegratedExpandedPair_eq_offDiagonalPairContribution]
        rfl
      _ = ∑ o ∈ selbergJOuterFinset X, G o :=
        (Finset.sum_subtype (selbergJOuterFinset X)
          (fun _ => Iff.rfl) G).symm
      _ = _ := rfl
  rw [hsubtype]
  unfold selbergPhysicalPositiveOffDiagonalSum selbergJOuterFinset
  let S := Finset.Icc 1 X
  let F : ((ℕ × ℕ) × (ℕ × ℕ)) → ℂ := fun o =>
    selbergJForwardDoubleSeries delta x theta X
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
      exact selbergJForwardDoubleSeries_eq_physicalForwardRaySum
        hdelta hdelta1 htheta hx hX
        (Finset.mem_Icc.mp hkappa).1 (Finset.mem_Icc.mp hkappa).2
        (Finset.mem_Icc.mp hlambda).1 (Finset.mem_Icc.mp hlambda).2
        (Finset.mem_Icc.mp hmu).1 (Finset.mem_Icc.mp hmu).2
        (Finset.mem_Icc.mp hnu).1 (Finset.mem_Icc.mp hnu).2

end HardyTheorem
