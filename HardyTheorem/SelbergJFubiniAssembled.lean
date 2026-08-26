import HardyTheorem.SelbergJPointwiseExpansion

set_option maxHeartbeats 800000

open Complex MeasureTheory Set

namespace HardyTheorem

/-! # The full absolutely convergent pair expansion of Selberg's `J` -/

noncomputable def selbergJOuterFinset (X : ℕ) :
    Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((Finset.Icc 1 X).product (Finset.Icc 1 X)).product
    ((Finset.Icc 1 X).product (Finset.Icc 1 X))

abbrev SelbergJFiniteIndex (X : ℕ) := {n : ℕ // n ∈ Finset.Icc 1 X}

abbrev SelbergJOuterIndex (X : ℕ) :=
  {o : (ℕ × ℕ) × (ℕ × ℕ) // o ∈ selbergJOuterFinset X}

noncomputable def selbergJGlobalExpandedPairIntegrand
    (delta theta : ℝ) (X : ℕ)
    (q : SelbergJOuterIndex X × (ℕ × ℕ)) (u : ℝ) : ℂ :=
  selbergPhysicalExpandedPairIntegrand delta theta X
    q.1.val.1.1 q.1.val.1.2 q.1.val.2.1 q.1.val.2.2 q.2 u

theorem summable_selbergJGlobalExpandedPairIntegrand
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    {theta u : ℝ} (hu : 0 < u) (X : ℕ) :
    Summable (fun q : SelbergJOuterIndex X × (ℕ × ℕ) =>
      selbergJGlobalExpandedPairIntegrand delta theta X q u) := by
  apply Summable.of_norm
  rw [summable_prod_of_nonneg (fun _ => norm_nonneg _)]
  constructor
  · intro o
    have ho := Finset.mem_product.mp o.property
    have hkl := Finset.mem_product.mp ho.1
    have hmn := Finset.mem_product.mp ho.2
    simpa [selbergJGlobalExpandedPairIntegrand] using
      (summable_selbergPhysicalExpandedPairIntegrand
      hdelta hdelta1 hu
      (Finset.mem_Icc.mp hkl.1).1 (Finset.mem_Icc.mp hkl.2).1
      (Finset.mem_Icc.mp hmn.1).1 (Finset.mem_Icc.mp hmn.2).1).norm
  · exact Summable.of_finite

noncomputable def selbergJGlobalPairSeries
    (delta theta u : ℝ) (X : ℕ) : ℂ :=
  ∑' q : SelbergJOuterIndex X × (ℕ × ℕ),
    selbergJGlobalExpandedPairIntegrand delta theta X q u

theorem selbergJGlobalPairSeries_eq_physicalPairSeries
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    {theta u : ℝ} (hu : 0 < u) (X : ℕ) :
    selbergJGlobalPairSeries delta theta u X =
      selbergPhysicalPairSeries delta theta u X := by
  classical
  have hsum := summable_selbergJGlobalExpandedPairIntegrand
    (theta := theta) hdelta hdelta1 hu X
  rw [selbergJGlobalPairSeries, hsum.tsum_prod, tsum_fintype]
  have hsubtype :
      (∑ o : SelbergJOuterIndex X,
          ∑' p : ℕ × ℕ,
            selbergJGlobalExpandedPairIntegrand delta theta X (o, p) u) =
        ∑ o ∈ selbergJOuterFinset X,
          ∑' p : ℕ × ℕ,
            selbergPhysicalExpandedPairIntegrand delta theta X
              o.1.1 o.1.2 o.2.1 o.2.2 p u := by
    symm
    apply Finset.sum_subtype (selbergJOuterFinset X)
    intro o
    rfl
  rw [hsubtype]
  unfold selbergPhysicalPairSeries selbergJOuterFinset
  let S := Finset.Icc 1 X
  let F : ((ℕ × ℕ) × (ℕ × ℕ)) → ℂ := fun o =>
    ∑' p : ℕ × ℕ, selbergPhysicalExpandedPairIntegrand delta theta X
      o.1.1 o.1.2 o.2.1 o.2.2 p u
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
    _ = _ := rfl

noncomputable def selbergJ (delta x theta : ℝ) (X : ℕ) : ℝ :=
  ∫ u in Ioi x, u ^ (-theta) * Complex.normSq
    (selbergNonconstantThetaKernel delta X (Real.log u))

theorem selbergJ_eq_integral_physicalPairSeries
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    {x theta : ℝ} (hx : 1 ≤ x) (X : ℕ) :
    (selbergJ delta x theta X : ℂ) =
      ∫ u in Ioi x, selbergPhysicalPairSeries delta theta u X := by
  rw [selbergJ, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [selbergPhysicalPairSeries_eq_weighted_normSq_kernel
    hdelta hdelta1 (zero_lt_one.trans_le (hx.trans hu.le))]
  rw [selbergPhysicalThetaKernel_eq_nonconstantThetaKernel_log
    hdelta hdelta1 (zero_lt_one.trans_le (hx.trans hu.le))]

theorem summable_integral_norm_selbergJGlobalExpandedPairIntegrand
    {delta theta x : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (htheta : 0 ≤ theta) (hx : 1 ≤ x)
    {X : ℕ} (hX : 2 ≤ X) :
    Summable (fun q : SelbergJOuterIndex X × (ℕ × ℕ) =>
      ∫ u in Ioi x,
        ‖selbergJGlobalExpandedPairIntegrand delta theta X q u‖) := by
  rw [summable_prod_of_nonneg (fun _ => integral_nonneg fun _ => norm_nonneg _)]
  constructor
  · intro o
    have ho := Finset.mem_product.mp o.property
    have hkl := Finset.mem_product.mp ho.1
    have hmn := Finset.mem_product.mp ho.2
    change Summable (fun p : ℕ × ℕ =>
      ∫ u in Ioi x,
        ‖selbergPhysicalExpandedPairIntegrand delta theta X
          o.val.1.1 o.val.1.2 o.val.2.1 o.val.2.2 p u‖)
    exact summable_integral_norm_selbergPhysicalExpandedPairIntegrand
      hdelta hdelta1 htheta hx hX
      (Finset.mem_Icc.mp hkl.1).1 (Finset.mem_Icc.mp hkl.1).2
      (Finset.mem_Icc.mp hkl.2).1 (Finset.mem_Icc.mp hkl.2).2
      (Finset.mem_Icc.mp hmn.1).1 (Finset.mem_Icc.mp hmn.1).2
      (Finset.mem_Icc.mp hmn.2).1 (Finset.mem_Icc.mp hmn.2).2
  · exact Summable.of_finite

theorem selbergJ_eq_tsum_integral_globalExpandedPair
    {delta theta x : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (htheta : 0 ≤ theta) (hx : 1 ≤ x)
    {X : ℕ} (hX : 2 ≤ X) :
    (selbergJ delta x theta X : ℂ) =
      ∑' q : SelbergJOuterIndex X × (ℕ × ℕ),
        ∫ u in Ioi x,
          selbergJGlobalExpandedPairIntegrand delta theta X q u := by
  rw [selbergJ_eq_integral_physicalPairSeries hdelta hdelta1 hx]
  have hint : ∀ q : SelbergJOuterIndex X × (ℕ × ℕ),
      IntegrableOn (selbergJGlobalExpandedPairIntegrand
        delta theta X q) (Ioi x) := by
    intro q
    have ho := Finset.mem_product.mp q.1.property
    have hkl := Finset.mem_product.mp ho.1
    have hmn := Finset.mem_product.mp ho.2
    change IntegrableOn (selbergPhysicalExpandedPairIntegrand delta theta X
      q.1.val.1.1 q.1.val.1.2 q.1.val.2.1 q.1.val.2.2 q.2) (Ioi x)
    exact integrableOn_selbergPhysicalExpandedPairIntegrand
      hdelta hdelta1 htheta hx hX
      (Finset.mem_Icc.mp hkl.1).1 (Finset.mem_Icc.mp hkl.1).2
      (Finset.mem_Icc.mp hkl.2).1 (Finset.mem_Icc.mp hkl.2).2
      (Finset.mem_Icc.mp hmn.1).1 (Finset.mem_Icc.mp hmn.1).2
      (Finset.mem_Icc.mp hmn.2).1 (Finset.mem_Icc.mp hmn.2).2 q.2
  have hsum := summable_integral_norm_selbergJGlobalExpandedPairIntegrand
    hdelta hdelta1 htheta hx hX
  have hfubini := hasSum_integral_of_summable_integral_norm hint hsum
  rw [hfubini.tsum_eq]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [← selbergJGlobalPairSeries_eq_physicalPairSeries
    hdelta hdelta1 (zero_lt_one.trans_le (hx.trans hu.le))]
  rfl

end HardyTheorem
