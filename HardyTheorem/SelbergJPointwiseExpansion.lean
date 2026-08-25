import HardyTheorem.SelbergJAbsoluteFubini

open Complex
open scoped BigOperators

namespace HardyTheorem

/-! # Pointwise square expansion of Selberg's physical theta kernel -/

noncomputable def selbergPhysicalThetaRay
    (delta u : ℝ) (kappa lambda : ℕ) : ℂ :=
  ∑' j : ℕ, selbergPhysicalGaussianTerm delta u (j + 1) kappa lambda

theorem summable_selbergPhysicalGaussianTerm_add_one
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    {u : ℝ} (hu : 0 < u)
    {kappa lambda : ℕ} (hkappa : 1 ≤ kappa) (hlambda : 1 ≤ lambda) :
    Summable (fun j : ℕ =>
      selbergPhysicalGaussianTerm delta u (j + 1) kappa lambda) := by
  have hdeltaPi : delta < Real.pi / 2 := by
    linarith [Real.pi_gt_three]
  exact (summable_selbergGaussianThetaTerm_add_one
    hdelta hdeltaPi hkappa hlambda (Real.log u)).congr fun j =>
      selbergGaussianThetaTerm_log_eq_physical hu delta kappa lambda (j + 1)

theorem selbergGaussianThetaSum_log_eq_physicalThetaRay
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    {u : ℝ} (hu : 0 < u)
    {kappa lambda : ℕ} (hkappa : 1 ≤ kappa) (hlambda : 1 ≤ lambda) :
    selbergGaussianThetaSum delta (Real.log u) kappa lambda =
      selbergPhysicalThetaRay delta u kappa lambda := by
  unfold selbergGaussianThetaSum selbergPhysicalThetaRay
  apply tsum_congr
  intro j
  exact selbergGaussianThetaTerm_log_eq_physical
    hu delta kappa lambda (j + 1)

noncomputable def selbergPhysicalThetaKernel
    (delta u : ℝ) (X : ℕ) : ℂ :=
  ∑ kappa ∈ Finset.Icc 1 X,
    ∑ lambda ∈ Finset.Icc 1 X,
      ((selbergSqrtZetaTaperedCoeff X kappa : ℂ) *
        (selbergSqrtZetaTaperedCoeff X lambda : ℂ) / (lambda : ℂ)) *
        selbergPhysicalThetaRay delta u kappa lambda

theorem selbergPhysicalThetaKernel_eq_nonconstantThetaKernel_log
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    {u : ℝ} (hu : 0 < u) (X : ℕ) :
    selbergPhysicalThetaKernel delta u X =
      selbergNonconstantThetaKernel delta X (Real.log u) := by
  unfold selbergPhysicalThetaKernel selbergNonconstantThetaKernel
  apply Finset.sum_congr rfl
  intro kappa hkappa
  apply Finset.sum_congr rfl
  intro lambda hlambda
  rw [selbergGaussianThetaSum_log_eq_physicalThetaRay
    hdelta hdelta1 hu (Finset.mem_Icc.mp hkappa).1
      (Finset.mem_Icc.mp hlambda).1]

private noncomputable def selbergPhysicalThetaOuterCoefficient
    (X kappa lambda : ℕ) : ℂ :=
  (selbergSqrtZetaTaperedCoeff X kappa : ℂ) *
    (selbergSqrtZetaTaperedCoeff X lambda : ℂ) / (lambda : ℂ)

private theorem selbergPhysicalPairMollifierCoefficient_eq_outer_mul
    (X kappa lambda mu nu : ℕ) :
    selbergPhysicalPairMollifierCoefficient X kappa lambda mu nu =
      selbergPhysicalThetaOuterCoefficient X kappa lambda *
        selbergPhysicalThetaOuterCoefficient X mu nu := by
  unfold selbergPhysicalPairMollifierCoefficient
    selbergPhysicalThetaOuterCoefficient
  rfl

theorem selbergPhysicalExpandedPairIntegrand_eq_product
    (delta theta u : ℝ) (X kappa lambda mu nu : ℕ) (p : ℕ × ℕ) :
    selbergPhysicalExpandedPairIntegrand
        delta theta X kappa lambda mu nu p u =
      (u ^ (-theta) : ℝ) •
        ((selbergPhysicalThetaOuterCoefficient X kappa lambda *
            selbergPhysicalGaussianTerm delta u (p.1 + 1) kappa lambda) *
          (starRingEnd ℂ)
            (selbergPhysicalThetaOuterCoefficient X mu nu *
              selbergPhysicalGaussianTerm delta u (p.2 + 1) mu nu)) := by
  rw [selbergPhysicalExpandedPairIntegrand,
    selbergPhysicalPairMollifierCoefficient_eq_outer_mul,
    ← selbergPhysicalGaussian_mul_conj_eq_pairIntegrand]
  unfold selbergPhysicalThetaOuterCoefficient
  simp only [map_mul, map_div₀, Complex.conj_ofReal,
    map_natCast]
  push_cast
  simp only [Complex.real_smul]
  ring

theorem tsum_selbergPhysicalExpandedPairIntegrand_eq_product
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    {theta u : ℝ} (hu : 0 < u)
    {X kappa lambda mu nu : ℕ}
    (hkappa : 1 ≤ kappa) (hlambda : 1 ≤ lambda)
    (hmu : 1 ≤ mu) (hnu : 1 ≤ nu) :
    (∑' p : ℕ × ℕ, selbergPhysicalExpandedPairIntegrand
        delta theta X kappa lambda mu nu p u) =
      (u ^ (-theta) : ℝ) •
        ((selbergPhysicalThetaOuterCoefficient X kappa lambda *
            selbergPhysicalThetaRay delta u kappa lambda) *
          (starRingEnd ℂ)
            (selbergPhysicalThetaOuterCoefficient X mu nu *
              selbergPhysicalThetaRay delta u mu nu)) := by
  let f : ℕ → ℂ := fun j =>
    selbergPhysicalThetaOuterCoefficient X kappa lambda *
      selbergPhysicalGaussianTerm delta u (j + 1) kappa lambda
  let g : ℕ → ℂ := fun j =>
    (starRingEnd ℂ) (selbergPhysicalThetaOuterCoefficient X mu nu *
      selbergPhysicalGaussianTerm delta u (j + 1) mu nu)
  have hf0 := summable_selbergPhysicalGaussianTerm_add_one
    hdelta hdelta1 hu hkappa hlambda
  have hg0 := summable_selbergPhysicalGaussianTerm_add_one
    hdelta hdelta1 hu hmu hnu
  have hf : Summable f := hf0.mul_left _
  have hbase : Summable (fun j =>
      selbergPhysicalThetaOuterCoefficient X mu nu *
        selbergPhysicalGaussianTerm delta u (j + 1) mu nu) := hg0.mul_left _
  have hg : Summable g := by
    exact (Complex.conjCLE : ℂ →L[ℝ] ℂ).summable hbase
  have hnormprod := hf.norm.mul_of_nonneg hg.norm
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hfg : Summable (fun p : ℕ × ℕ => f p.1 * g p.2) := by
    apply Summable.of_norm_bounded hnormprod
    intro p
    rw [norm_mul]
  have hprod := hf.tsum_mul_tsum hg hfg
  have htsumf : (∑' j : ℕ, f j) =
      selbergPhysicalThetaOuterCoefficient X kappa lambda *
        selbergPhysicalThetaRay delta u kappa lambda := by
    exact Summable.tsum_mul_left _ hf0
  have htsumg : (∑' j : ℕ, g j) =
      (starRingEnd ℂ) (selbergPhysicalThetaOuterCoefficient X mu nu *
        selbergPhysicalThetaRay delta u mu nu) := by
    calc
      (∑' j : ℕ, g j) =
          (starRingEnd ℂ) (∑' j : ℕ,
            selbergPhysicalThetaOuterCoefficient X mu nu *
              selbergPhysicalGaussianTerm delta u (j + 1) mu nu) :=
        ((Complex.conjCLE : ℂ →L[ℝ] ℂ).map_tsum hbase).symm
      _ = (starRingEnd ℂ) (selbergPhysicalThetaOuterCoefficient X mu nu *
          selbergPhysicalThetaRay delta u mu nu) := by
        rw [Summable.tsum_mul_left _ hg0]
        rfl
  calc
    (∑' p : ℕ × ℕ, selbergPhysicalExpandedPairIntegrand
        delta theta X kappa lambda mu nu p u) =
      ∑' p : ℕ × ℕ, (((u ^ (-theta) : ℝ) : ℂ) * (f p.1 * g p.2)) := by
        apply tsum_congr
        intro p
        rw [selbergPhysicalExpandedPairIntegrand_eq_product]
        simp only [Complex.real_smul]
        dsimp [f, g]
    _ = ((u ^ (-theta) : ℝ) : ℂ) * (∑' p : ℕ × ℕ, f p.1 * g p.2) :=
      Summable.tsum_mul_left _ hfg
    _ = ((u ^ (-theta) : ℝ) : ℂ) * ((∑' j : ℕ, f j) * (∑' j : ℕ, g j)) := by
      rw [hprod]
    _ = (u ^ (-theta) : ℝ) •
        ((selbergPhysicalThetaOuterCoefficient X kappa lambda *
            selbergPhysicalThetaRay delta u kappa lambda) *
          (starRingEnd ℂ)
            (selbergPhysicalThetaOuterCoefficient X mu nu *
              selbergPhysicalThetaRay delta u mu nu)) := by
      rw [htsumf, htsumg]
      rfl

theorem summable_selbergPhysicalExpandedPairIntegrand
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    {theta u : ℝ} (hu : 0 < u)
    {X kappa lambda mu nu : ℕ}
    (hkappa : 1 ≤ kappa) (hlambda : 1 ≤ lambda)
    (hmu : 1 ≤ mu) (hnu : 1 ≤ nu) :
    Summable (fun p : ℕ × ℕ => selbergPhysicalExpandedPairIntegrand
      delta theta X kappa lambda mu nu p u) := by
  let f : ℕ → ℂ := fun j =>
    selbergPhysicalThetaOuterCoefficient X kappa lambda *
      selbergPhysicalGaussianTerm delta u (j + 1) kappa lambda
  let g : ℕ → ℂ := fun j =>
    (starRingEnd ℂ) (selbergPhysicalThetaOuterCoefficient X mu nu *
      selbergPhysicalGaussianTerm delta u (j + 1) mu nu)
  have hf0 := summable_selbergPhysicalGaussianTerm_add_one
    hdelta hdelta1 hu hkappa hlambda
  have hg0 := summable_selbergPhysicalGaussianTerm_add_one
    hdelta hdelta1 hu hmu hnu
  have hf : Summable f := hf0.mul_left _
  have hbase : Summable (fun j =>
      selbergPhysicalThetaOuterCoefficient X mu nu *
        selbergPhysicalGaussianTerm delta u (j + 1) mu nu) := hg0.mul_left _
  have hg : Summable g :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).summable hbase
  have hnormprod := hf.norm.mul_of_nonneg hg.norm
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hfg : Summable (fun p : ℕ × ℕ => f p.1 * g p.2) := by
    apply Summable.of_norm_bounded hnormprod
    intro p
    rw [norm_mul]
  apply (hfg.mul_left (((u ^ (-theta) : ℝ) : ℂ))).congr
  intro p
  rw [selbergPhysicalExpandedPairIntegrand_eq_product]
  simp only [Complex.real_smul]
  dsimp [f, g]

noncomputable def selbergPhysicalPairSeries
    (delta theta u : ℝ) (X : ℕ) : ℂ :=
  ∑ kappa ∈ Finset.Icc 1 X,
    ∑ lambda ∈ Finset.Icc 1 X,
      ∑ mu ∈ Finset.Icc 1 X,
        ∑ nu ∈ Finset.Icc 1 X,
          ∑' p : ℕ × ℕ, selbergPhysicalExpandedPairIntegrand
            delta theta X kappa lambda mu nu p u

theorem selbergPhysicalPairSeries_eq_weighted_normSq_kernel
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    {theta u : ℝ} (hu : 0 < u) (X : ℕ) :
    selbergPhysicalPairSeries delta theta u X =
      ((u ^ (-theta) * Complex.normSq
        (selbergPhysicalThetaKernel delta u X) : ℝ) : ℂ) := by
  classical
  let F : ℕ → ℕ → ℂ := fun kappa lambda =>
    selbergPhysicalThetaOuterCoefficient X kappa lambda *
      selbergPhysicalThetaRay delta u kappa lambda
  have hexpand : selbergPhysicalPairSeries delta theta u X =
      ∑ kappa ∈ Finset.Icc 1 X,
        ∑ lambda ∈ Finset.Icc 1 X,
          ∑ mu ∈ Finset.Icc 1 X,
            ∑ nu ∈ Finset.Icc 1 X,
              (u ^ (-theta) : ℝ) •
                (F kappa lambda * (starRingEnd ℂ) (F mu nu)) := by
    unfold selbergPhysicalPairSeries
    apply Finset.sum_congr rfl
    intro kappa hkappa
    apply Finset.sum_congr rfl
    intro lambda hlambda
    apply Finset.sum_congr rfl
    intro mu hmu
    apply Finset.sum_congr rfl
    intro nu hnu
    exact tsum_selbergPhysicalExpandedPairIntegrand_eq_product
      hdelta hdelta1 hu
      (Finset.mem_Icc.mp hkappa).1 (Finset.mem_Icc.mp hlambda).1
      (Finset.mem_Icc.mp hmu).1 (Finset.mem_Icc.mp hnu).1
  rw [hexpand]
  have hfactor :
      (∑ kappa ∈ Finset.Icc 1 X,
        ∑ lambda ∈ Finset.Icc 1 X,
          ∑ mu ∈ Finset.Icc 1 X,
            ∑ nu ∈ Finset.Icc 1 X,
              (u ^ (-theta) : ℝ) •
                (F kappa lambda * (starRingEnd ℂ) (F mu nu))) =
      (u ^ (-theta) : ℝ) •
        ((∑ kappa ∈ Finset.Icc 1 X,
            ∑ lambda ∈ Finset.Icc 1 X, F kappa lambda) *
          (starRingEnd ℂ) (∑ mu ∈ Finset.Icc 1 X,
            ∑ nu ∈ Finset.Icc 1 X, F mu nu)) := by
    let S : ℂ := ∑ kappa ∈ Finset.Icc 1 X,
      ∑ lambda ∈ Finset.Icc 1 X, F kappa lambda
    let T : ℂ := ∑ mu ∈ Finset.Icc 1 X,
      ∑ nu ∈ Finset.Icc 1 X, (starRingEnd ℂ) (F mu nu)
    have hpair :
        (∑ kappa ∈ Finset.Icc 1 X,
          ∑ lambda ∈ Finset.Icc 1 X,
            ∑ mu ∈ Finset.Icc 1 X,
              ∑ nu ∈ Finset.Icc 1 X,
                F kappa lambda * (starRingEnd ℂ) (F mu nu)) = S * T := by
      calc
        (∑ kappa ∈ Finset.Icc 1 X,
            ∑ lambda ∈ Finset.Icc 1 X,
              ∑ mu ∈ Finset.Icc 1 X,
                ∑ nu ∈ Finset.Icc 1 X,
                  F kappa lambda * (starRingEnd ℂ) (F mu nu)) =
            ∑ kappa ∈ Finset.Icc 1 X,
              ∑ lambda ∈ Finset.Icc 1 X, F kappa lambda * T := by
          apply Finset.sum_congr rfl
          intro kappa hkappa
          apply Finset.sum_congr rfl
          intro lambda hlambda
          dsimp [T]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro mu hmu
          rw [Finset.mul_sum]
        _ = S * T := by
          dsimp [S]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro kappa hkappa
          rw [Finset.sum_mul]
    calc
      (∑ kappa ∈ Finset.Icc 1 X,
          ∑ lambda ∈ Finset.Icc 1 X,
            ∑ mu ∈ Finset.Icc 1 X,
              ∑ nu ∈ Finset.Icc 1 X,
                (u ^ (-theta) : ℝ) •
                  (F kappa lambda * (starRingEnd ℂ) (F mu nu))) =
        (u ^ (-theta) : ℝ) •
          (∑ kappa ∈ Finset.Icc 1 X,
            ∑ lambda ∈ Finset.Icc 1 X,
              ∑ mu ∈ Finset.Icc 1 X,
                ∑ nu ∈ Finset.Icc 1 X,
                  F kappa lambda * (starRingEnd ℂ) (F mu nu)) := by
        simp only [Finset.smul_sum]
      _ = (u ^ (-theta) : ℝ) • (S * T) := by rw [hpair]
      _ = _ := by
        dsimp [S, T]
        simp only [map_sum]
  rw [hfactor]
  change (u ^ (-theta) : ℝ) •
      (selbergPhysicalThetaKernel delta u X *
        (starRingEnd ℂ) (selbergPhysicalThetaKernel delta u X)) = _
  rw [Complex.mul_conj]
  push_cast
  rfl

end HardyTheorem
