import HardyTheorem.SelbergJDiagonalRayEquiv

open Complex MeasureTheory Set

namespace HardyTheorem

/-! # Reindexing one fixed outer diagonal pair as the original gcd ray -/

noncomputable def selbergJDiagonalDoubleSeries
    (delta x theta : ℝ) (X kappa lambda mu nu : ℕ) : ℂ :=
  ∑' p : ℕ × ℕ,
    if (p.1 + 1) * kappa * nu = (p.2 + 1) * lambda * mu then
      selbergPhysicalOffDiagonalPairContribution delta x theta X
        (p.1 + 1) kappa lambda (p.2 + 1) mu nu
    else 0

theorem selbergJDiagonalDoubleSeries_eq_originalRay
    {delta theta x : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hx : 1 ≤ x) (htheta : 0 < theta) (hthetaHalf : theta ≤ 1 / 2)
    {X kappa lambda mu nu : ℕ} (hX : 2 ≤ X)
    (hkappa : 1 ≤ kappa) (hkappaX : kappa ≤ X)
    (hlambda : 1 ≤ lambda) (hlambdaX : lambda ≤ X)
    (hmu : 1 ≤ mu) (hmuX : mu ≤ X)
    (hnu : 1 ≤ nu) (hnuX : nu ≤ X) :
    selbergJDiagonalDoubleSeries delta x theta X kappa lambda mu nu =
      selbergDiagonalMollifierBase X kappa nu mu lambda *
        ((∑' j : ℕ, ∫ u in Ioi x,
          selbergDiagonalOriginalIntegrand
            (selbergDiagonalGaussianParameter delta kappa mu
              (Nat.gcd (kappa * nu) (lambda * mu))) theta j u : ℝ) : ℂ) := by
  let A := kappa * nu
  let B := lambda * mu
  let eta := selbergDiagonalGaussianParameter delta kappa mu (Nat.gcd A B)
  let f : (ℕ × ℕ) → ℂ := fun p =>
    selbergPhysicalOffDiagonalPairContribution delta x theta X
      (p.1 + 1) kappa lambda (p.2 + 1) mu nu
  let D : Set (ℕ × ℕ) := {p | (p.1 + 1) * A = (p.2 + 1) * B}
  have hA : 1 ≤ A := Nat.mul_pos hkappa hnu
  have hB : 1 ≤ B := Nat.mul_pos hlambda hmu
  have hg : 0 < Nat.gcd A B :=
    Nat.gcd_pos_of_pos_left B (zero_lt_one.trans_le hA)
  have heta : 0 < eta := selbergDiagonalGaussianParameter_pos
    hdelta (hdelta1.trans_lt (by linarith [Real.pi_gt_three]))
      hkappa hmu hg
  have hnorm := summable_integral_norm_selbergPhysicalExpandedPairIntegrand
    hdelta hdelta1 htheta.le hx hX hkappa hkappaX hlambda hlambdaX
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
  have hD : Summable (D.indicator f) := hf.indicator D
  let e := selbergDiagonalRayEquiv hA hB
  have hray :
      (∑' p : ℕ × ℕ, D.indicator f p) =
        ∑' j : ℕ, f ((e.symm j).val) := by
    rw [← tsum_subtype D f]
    exact (e.symm.tsum_eq (fun p : selbergDiagonalRayIndex A B => f p.val)).symm
  have hIreal := (hasSum_integral_selbergDiagonalOriginalIntegrand
    heta (zero_lt_one.trans_le hx) htheta hthetaHalf).summable
  have hI : Summable (fun j : ℕ =>
      ((∫ u in Ioi x, selbergDiagonalOriginalIntegrand eta theta j u : ℝ) : ℂ)) :=
    Complex.ofRealLI.toContinuousLinearMap.summable hIreal
  have hofRealTsum :
      (∑' j : ℕ, ((∫ u in Ioi x,
        selbergDiagonalOriginalIntegrand eta theta j u : ℝ) : ℂ)) =
        ((∑' j : ℕ, ∫ u in Ioi x,
          selbergDiagonalOriginalIntegrand eta theta j u : ℝ) : ℂ) :=
    (Complex.ofRealLI.toContinuousLinearMap.map_tsum hIreal).symm
  unfold selbergJDiagonalDoubleSeries
  have hindicator :
      (∑' p : ℕ × ℕ,
        if (p.1 + 1) * kappa * nu = (p.2 + 1) * lambda * mu then
          selbergPhysicalOffDiagonalPairContribution delta x theta X
            (p.1 + 1) kappa lambda (p.2 + 1) mu nu
        else 0) = ∑' p : ℕ × ℕ, D.indicator f p := by
    apply tsum_congr
    intro p
    simp [D, A, B, f, Set.indicator, Nat.mul_assoc]
  rw [hindicator, hray]
  have hterm : ∀ j : ℕ, f ((e.symm j).val) =
      selbergDiagonalMollifierBase X kappa nu mu lambda *
        ((∫ u in Ioi x, selbergDiagonalOriginalIntegrand eta theta j u : ℝ) : ℂ) := by
    intro j
    let q : selbergDiagonalRayIndex A B := e.symm j
    have hs := selbergDiagonalRayScale_spec hA hB q
    have hrs := hs.1
    have heq := e.apply_symm_apply j
    have hscale : selbergDiagonalRayScale hA hB q = j + 1 := by
      change selbergDiagonalRayScale hA hB (e.symm j) - 1 = j at heq
      have heq' : selbergDiagonalRayScale hA hB q - 1 = j := by
        simpa only [q] using heq
      omega
    have hqm : q.1.1 + 1 = (j + 1) * (B / Nat.gcd A B) := by
      rw [hs.2.1, hscale]
    have hqn : q.1.2 + 1 = (j + 1) * (A / Nat.gcd A B) := by
      rw [hs.2.2, hscale]
    dsimp [f]
    change selbergPhysicalOffDiagonalPairContribution delta x theta X
        (q.1.1 + 1) kappa lambda (q.1.2 + 1) mu nu = _
    rw [hqm, hqn]
    unfold selbergPhysicalOffDiagonalPairContribution
    rw [selbergPhysicalPairMollifierCoefficient_eq_diagonalBase]
    congr 1
    calc
      (∫ u in Ioi x, selbergPhysicalPairIntegrand delta theta u
          ((j + 1) * (B / Nat.gcd A B)) kappa lambda
          ((j + 1) * (A / Nat.gcd A B)) mu nu) =
          ∫ u in Ioi x, (selbergDiagonalOriginalIntegrand eta theta j u : ℂ) := by
        apply integral_congr_ae
        filter_upwards with u
        simpa only [A, B, eta, show j + 1 - 1 = j by omega] using
          selbergPhysicalPairIntegrand_on_gcdRay
            hkappa hlambda hmu hnu (Nat.le_add_left 1 j)
      _ = ((∫ u in Ioi x,
          selbergDiagonalOriginalIntegrand eta theta j u : ℝ) : ℂ) :=
        integral_complex_ofReal
  calc
    (∑' j : ℕ, f ((e.symm j).val)) =
        ∑' j : ℕ, selbergDiagonalMollifierBase X kappa nu mu lambda *
          ((∫ u in Ioi x,
            selbergDiagonalOriginalIntegrand eta theta j u : ℝ) : ℂ) :=
      tsum_congr hterm
    _ = selbergDiagonalMollifierBase X kappa nu mu lambda *
        (∑' j : ℕ, ((∫ u in Ioi x,
          selbergDiagonalOriginalIntegrand eta theta j u : ℝ) : ℂ)) :=
      Summable.tsum_mul_left _ hI
    _ = _ := by rw [hofRealTsum]

end HardyTheorem
