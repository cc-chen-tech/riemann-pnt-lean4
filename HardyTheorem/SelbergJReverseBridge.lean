import HardyTheorem.SelbergJForwardBridge

open Complex MeasureTheory Set

namespace HardyTheorem

/-! # Exact simultaneous-swap bridge for the negative-frequency side -/

theorem selbergPhysicalPairIntegrand_eq_conj_swap
    (delta theta u : ℝ) (m kappa lambda n mu nu : ℕ) :
    selbergPhysicalPairIntegrand delta theta u m kappa lambda n mu nu =
      (starRingEnd ℂ)
        (selbergPhysicalPairIntegrand delta theta u n mu nu m kappa lambda) := by
  unfold selbergPhysicalPairIntegrand selbergOscillatoryGaussian
    selbergPhysicalPairDamping selbergPhysicalPairSignedFrequency
    selbergPhysicalSquareRatio
  change (u ^ (-theta) : ℝ) • Complex.exp _ =
    (Complex.conjCLE : ℂ →L[ℝ] ℂ)
      ((u ^ (-theta) : ℝ) • Complex.exp _)
  rw [map_smul]
  change (u ^ (-theta) : ℝ) • Complex.exp _ =
    (u ^ (-theta) : ℝ) • (starRingEnd ℂ) (Complex.exp _)
  rw [← Complex.exp_conj]
  apply congrArg (fun z : ℂ => (u ^ (-theta) : ℝ) • Complex.exp z)
  apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im] <;> ring

theorem selbergPhysicalPairMollifierCoefficient_eq_conj_swap
    (X kappa lambda mu nu : ℕ) :
    selbergPhysicalPairMollifierCoefficient X kappa lambda mu nu =
      (starRingEnd ℂ)
        (selbergPhysicalPairMollifierCoefficient X mu nu kappa lambda) := by
  simp [selbergPhysicalPairMollifierCoefficient]
  ring

theorem selbergPhysicalOffDiagonalPairContribution_eq_conj_swap
    (delta x theta : ℝ) (X m kappa lambda n mu nu : ℕ) :
    selbergPhysicalOffDiagonalPairContribution
        delta x theta X m kappa lambda n mu nu =
      (starRingEnd ℂ) (selbergPhysicalOffDiagonalPairContribution
        delta x theta X n mu nu m kappa lambda) := by
  unfold selbergPhysicalOffDiagonalPairContribution
  rw [selbergPhysicalPairMollifierCoefficient_eq_conj_swap, map_mul]
  congr 1
  calc
    (∫ u in Ioi x, selbergPhysicalPairIntegrand delta theta u
        m kappa lambda n mu nu) =
        ∫ u in Ioi x, (starRingEnd ℂ)
          (selbergPhysicalPairIntegrand delta theta u
            n mu nu m kappa lambda) := by
      apply integral_congr_ae
      filter_upwards with u
      exact selbergPhysicalPairIntegrand_eq_conj_swap
        delta theta u m kappa lambda n mu nu
    _ = (starRingEnd ℂ) (∫ u in Ioi x,
        selbergPhysicalPairIntegrand delta theta u
          n mu nu m kappa lambda) := integral_conj

noncomputable def selbergJReverseDoubleSeries
    (delta x theta : ℝ) (X kappa lambda mu nu : ℕ) : ℂ :=
  ∑' p : ℕ × ℕ,
    if (p.1 + 1) * kappa * nu < (p.2 + 1) * lambda * mu then
      selbergPhysicalOffDiagonalPairContribution delta x theta X
        (p.1 + 1) kappa lambda (p.2 + 1) mu nu
    else 0

theorem selbergJReverseDoubleSeries_eq_conj_forwardDoubleSeries_swap
    {delta theta x : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (htheta : 0 ≤ theta) (hx : 1 ≤ x)
    {X kappa lambda mu nu : ℕ} (hX : 2 ≤ X)
    (hkappa : 1 ≤ kappa) (hkappaX : kappa ≤ X)
    (hlambda : 1 ≤ lambda) (hlambdaX : lambda ≤ X)
    (hmu : 1 ≤ mu) (hmuX : mu ≤ X)
    (hnu : 1 ≤ nu) (hnuX : nu ≤ X) :
    selbergJReverseDoubleSeries delta x theta X kappa lambda mu nu =
      (starRingEnd ℂ)
        (selbergJForwardDoubleSeries delta x theta X mu nu kappa lambda) := by
  let g : (ℕ × ℕ) → ℂ := fun p =>
    if (p.2 + 1) * nu * kappa < (p.1 + 1) * mu * lambda then
      selbergPhysicalOffDiagonalPairContribution delta x theta X
        (p.1 + 1) mu nu (p.2 + 1) kappa lambda
    else 0
  let f : (ℕ × ℕ) → ℂ := fun p =>
    selbergPhysicalOffDiagonalPairContribution delta x theta X
      (p.1 + 1) mu nu (p.2 + 1) kappa lambda
  have hnorm := summable_integral_norm_selbergPhysicalExpandedPairIntegrand
    hdelta hdelta1 htheta hx hX hmu hmuX hnu hnuX
      hkappa hkappaX hlambda hlambdaX
  have hf : Summable f := by
    apply Summable.of_norm_bounded hnorm
    intro p
    rw [show f p = ∫ u in Ioi x,
        selbergPhysicalExpandedPairIntegrand delta theta X
          mu nu kappa lambda p u by
      dsimp [f]
      unfold selbergPhysicalOffDiagonalPairContribution
        selbergPhysicalExpandedPairIntegrand
      rw [integral_const_mul]]
    exact norm_integral_le_integral_norm _
  let P : Set (ℕ × ℕ) := {p |
    (p.2 + 1) * nu * kappa < (p.1 + 1) * mu * lambda}
  have hg : Summable g := by
    have hP : Summable (P.indicator f) := hf.indicator P
    exact hP.congr (fun p => by simp [g, P, f, Set.indicator])
  unfold selbergJReverseDoubleSeries selbergJForwardDoubleSeries
  calc
    (∑' p : ℕ × ℕ,
      if (p.1 + 1) * kappa * nu < (p.2 + 1) * lambda * mu then
        selbergPhysicalOffDiagonalPairContribution delta x theta X
          (p.1 + 1) kappa lambda (p.2 + 1) mu nu
      else 0) = ∑' p : ℕ × ℕ, (starRingEnd ℂ) (g (p.2, p.1)) := by
        apply tsum_congr
        intro p
        simp only [g]
        by_cases hp : (p.1 + 1) * kappa * nu <
            (p.2 + 1) * lambda * mu
        · rw [if_pos hp]
          have hp' : (p.1 + 1) * nu * kappa <
              (p.2 + 1) * mu * lambda := by
            simpa only [mul_assoc, mul_comm, mul_left_comm] using hp
          rw [if_pos hp']
          exact selbergPhysicalOffDiagonalPairContribution_eq_conj_swap
            delta x theta X _ _ _ _ _ _
        · rw [if_neg hp]
          have hp' : ¬(p.1 + 1) * nu * kappa <
              (p.2 + 1) * mu * lambda := by
            simpa only [mul_assoc, mul_comm, mul_left_comm] using hp
          rw [if_neg hp', map_zero]
    _ = ∑' p : ℕ × ℕ, (starRingEnd ℂ) (g p) := by
      exact (Equiv.prodComm ℕ ℕ).tsum_eq (fun p => (starRingEnd ℂ) (g p))
    _ = (starRingEnd ℂ) (∑' p : ℕ × ℕ, g p) :=
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).map_tsum hg).symm
    _ = _ := rfl

theorem selbergJReversePart_eq_physicalReverseOffDiagonalSum
    {delta theta x : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (htheta : 0 ≤ theta) (hx : 1 ≤ x)
    {X : ℕ} (hX : 2 ≤ X) :
    selbergJReversePart delta x theta X =
      selbergPhysicalReverseOffDiagonalSum delta x theta X := by
  classical
  let f := selbergJIntegratedExpandedPair delta x theta X
  let R := selbergJReverseIndexSet X
  have hf : Summable f := summable_selbergJIntegratedExpandedPair
    hdelta hdelta1 htheta hx hX
  have hR : Summable (R.indicator f) := hf.indicator R
  unfold selbergJReversePart
  change (∑' q, R.indicator f q) = _
  rw [hR.tsum_prod, tsum_fintype]
  have hsubtype :
      (∑ o : SelbergJOuterIndex X,
          ∑' p : ℕ × ℕ, R.indicator f (o, p)) =
        ∑ o ∈ selbergJOuterFinset X,
          selbergJReverseDoubleSeries delta x theta X
            o.1.1 o.1.2 o.2.1 o.2.2 := by
    let G : ((ℕ × ℕ) × (ℕ × ℕ)) → ℂ := fun o =>
      selbergJReverseDoubleSeries delta x theta X
        o.1.1 o.1.2 o.2.1 o.2.2
    calc
      (∑ o : SelbergJOuterIndex X,
          ∑' p : ℕ × ℕ, R.indicator f (o, p)) =
          ∑ o : SelbergJOuterIndex X, G o.val := by
        apply Finset.sum_congr rfl
        intro o ho
        dsimp [G]
        unfold selbergJReverseDoubleSeries
        apply tsum_congr
        intro p
        simp only [R, selbergJReverseIndexSet, Set.indicator, Set.mem_ofPred_eq]
        dsimp [f]
        rw [selbergJIntegratedExpandedPair_eq_offDiagonalPairContribution]
        rfl
      _ = ∑ o ∈ selbergJOuterFinset X, G o :=
        (Finset.sum_subtype (selbergJOuterFinset X)
          (fun _ => Iff.rfl) G).symm
      _ = _ := rfl
  rw [hsubtype]
  unfold selbergPhysicalReverseOffDiagonalSum selbergJOuterFinset
  let S := Finset.Icc 1 X
  let F : ((ℕ × ℕ) × (ℕ × ℕ)) → ℂ := fun o =>
    selbergJReverseDoubleSeries delta x theta X
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
      rw [selbergJReverseDoubleSeries_eq_conj_forwardDoubleSeries_swap
        hdelta hdelta1 htheta hx hX
        (Finset.mem_Icc.mp hkappa).1 (Finset.mem_Icc.mp hkappa).2
        (Finset.mem_Icc.mp hlambda).1 (Finset.mem_Icc.mp hlambda).2
        (Finset.mem_Icc.mp hmu).1 (Finset.mem_Icc.mp hmu).2
        (Finset.mem_Icc.mp hnu).1 (Finset.mem_Icc.mp hnu).2]
      rw [selbergJForwardDoubleSeries_eq_physicalForwardRaySum
        hdelta hdelta1 htheta hx hX
        (Finset.mem_Icc.mp hmu).1 (Finset.mem_Icc.mp hmu).2
        (Finset.mem_Icc.mp hnu).1 (Finset.mem_Icc.mp hnu).2
        (Finset.mem_Icc.mp hkappa).1 (Finset.mem_Icc.mp hkappa).2
        (Finset.mem_Icc.mp hlambda).1 (Finset.mem_Icc.mp hlambda).2]

end HardyTheorem
