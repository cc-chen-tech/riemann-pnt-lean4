import HardyTheorem.SelbergSqrtZetaSignedAutocorrelationTransfer
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Shift-square budget for signed autocorrelation transfer

The integrated autocorrelation approximation is uniform on every lag section.
Writing a lag as `w - v` identifies the triangular lag region with the square
`(v, w) ∈ [0, H]²`. Integrating the section bound over that square costs
exactly the area `H²`.
-/

open MeasureTheory Set

namespace HardyTheorem

/-- The actual mollified autocorrelation kernel in fixed square coordinates. -/
noncomputable def selbergSqrtZetaMollifiedAutocorrelationShiftKernel
    (X : ℕ) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  selbergSqrtZetaMollifiedHardyZ X (p.2 + p.1.1) *
    selbergSqrtZetaMollifiedHardyZ X (p.2 + p.1.2)

/-- The signed finite-model autocorrelation kernel in fixed square
coordinates. -/
noncomputable def selbergSqrtZetaSignedThetaModelAutocorrelationShiftKernel
    (kappa T : ℝ) (X : ℕ) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  selbergSqrtZetaSignedThetaModel kappa T X (p.2 + p.1.1) *
    selbergSqrtZetaSignedThetaModel kappa T X (p.2 + p.1.2)

/-- Both autocorrelation kernels are Bochner integrable on the compact
shift-height box. -/
theorem integrable_selbergSqrtZetaSignedAutocorrelationShiftKernels
    (kappa T : ℝ) (X : ℕ) {H : ℝ}
    (hT : 0 < T) (_hH : 0 ≤ H) (_hHT : H ≤ T) :
    Integrable
        (selbergSqrtZetaMollifiedAutocorrelationShiftKernel X)
        (((volume.restrict (Ioc 0 H)).prod
            (volume.restrict (Ioc 0 H))).prod
          (volume.restrict (Ioc T (2 * T - H)))) ∧
      Integrable
        (selbergSqrtZetaSignedThetaModelAutocorrelationShiftKernel
          kappa T X)
        (((volume.restrict (Ioc 0 H)).prod
            (volume.restrict (Ioc 0 H))).prod
          (volume.restrict (Ioc T (2 * T - H)))) := by
  let box : Set ((ℝ × ℝ) × ℝ) :=
    (Icc 0 H ×ˢ Icc 0 H) ×ˢ Icc T (2 * T - H)
  have hcompact : IsCompact box :=
    (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  have hactualContinuous : Continuous
      (selbergSqrtZetaMollifiedAutocorrelationShiftKernel X) := by
    unfold selbergSqrtZetaMollifiedAutocorrelationShiftKernel
    exact
      (continuous_selbergSqrtZetaMollifiedHardyZ X).comp
          (continuous_snd.add continuous_fst.fst) |>.mul <|
        (continuous_selbergSqrtZetaMollifiedHardyZ X).comp
          (continuous_snd.add continuous_fst.snd)
  have hmodelDyadic : ContinuousOn
      (selbergSqrtZetaSignedThetaModel kappa T X) (Icc T (2 * T)) :=
    continuousOn_selbergSqrtZetaSignedThetaModel_Icc_T_two_mul_T
      kappa T X hT
  have hargV : ContinuousOn
      (fun p : (ℝ × ℝ) × ℝ => p.2 + p.1.1) box :=
    (continuous_snd.add continuous_fst.fst).continuousOn
  have hargW : ContinuousOn
      (fun p : (ℝ × ℝ) × ℝ => p.2 + p.1.2) box :=
    (continuous_snd.add continuous_fst.snd).continuousOn
  have hmapV : MapsTo
      (fun p : (ℝ × ℝ) × ℝ => p.2 + p.1.1) box (Icc T (2 * T)) := by
    intro p hp
    exact ⟨by linarith [hp.2.1, hp.1.1.1],
      by linarith [hp.2.2, hp.1.1.2]⟩
  have hmapW : MapsTo
      (fun p : (ℝ × ℝ) × ℝ => p.2 + p.1.2) box (Icc T (2 * T)) := by
    intro p hp
    exact ⟨by linarith [hp.2.1, hp.1.2.1],
      by linarith [hp.2.2, hp.1.2.2]⟩
  have hmodelV : ContinuousOn
      (fun p : (ℝ × ℝ) × ℝ =>
        selbergSqrtZetaSignedThetaModel kappa T X (p.2 + p.1.1)) box := by
    simpa only [Function.comp_def] using hmodelDyadic.comp hargV hmapV
  have hmodelW : ContinuousOn
      (fun p : (ℝ × ℝ) × ℝ =>
        selbergSqrtZetaSignedThetaModel kappa T X (p.2 + p.1.2)) box := by
    simpa only [Function.comp_def] using hmodelDyadic.comp hargW hmapW
  have hactualBox : IntegrableOn
      (selbergSqrtZetaMollifiedAutocorrelationShiftKernel X) box
      ((volume.prod volume).prod volume) :=
    hactualContinuous.continuousOn.integrableOn_compact hcompact
  have hmodelBox : IntegrableOn
      (selbergSqrtZetaSignedThetaModelAutocorrelationShiftKernel
        kappa T X) box ((volume.prod volume).prod volume) := by
    have hmodelContinuous : ContinuousOn
        (selbergSqrtZetaSignedThetaModelAutocorrelationShiftKernel
          kappa T X) box := by
      change ContinuousOn
        ((fun p : (ℝ × ℝ) × ℝ =>
          selbergSqrtZetaSignedThetaModel kappa T X (p.2 + p.1.1)) *
          fun p : (ℝ × ℝ) × ℝ =>
            selbergSqrtZetaSignedThetaModel kappa T X (p.2 + p.1.2)) box
      simpa [selbergSqrtZetaSignedThetaModelAutocorrelationShiftKernel] using
        hmodelV.mul hmodelW
    exact hmodelContinuous.integrableOn_compact hcompact
  have hsmall :
      ((Ioc 0 H ×ˢ Ioc 0 H) ×ˢ Ioc T (2 * T - H)) ⊆ box :=
    Set.prod_mono
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
      Ioc_subset_Icc_self
  constructor
  · have := hactualBox.mono_set hsmall
    simpa only [Measure.prod_restrict, IntegrableOn] using this
  · have := hmodelBox.mono_set hsmall
    simpa only [Measure.prod_restrict, IntegrableOn] using this

/-- The uniform lag-section autocorrelation error integrates over the full
shift square with the exact area factor `H²`. -/
theorem
    exists_abs_integral_integral_integral_selbergSqrtZetaMollifiedAutocorrelation_sub_signedThetaModel_le :
    ∃ kappa C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T H M : ℝ,
        T0 ≤ T → 0 ≤ H → H ≤ T → 0 ≤ M →
        (∀ x ∈ Icc T (2 * T),
          |selbergSqrtZetaSignedThetaModel kappa T X x| ≤ M) →
        |(∫ v in 0..H, ∫ w in 0..H, ∫ x in T..2 * T - H,
              selbergSqrtZetaMollifiedHardyZ X (x + v) *
                selbergSqrtZetaMollifiedHardyZ X (x + w)) -
            ∫ v in 0..H, ∫ w in 0..H, ∫ x in T..2 * T - H,
              selbergSqrtZetaSignedThetaModel kappa T X (x + v) *
                selbergSqrtZetaSignedThetaModel kappa T X (x + w)| ≤
          H ^ 2 * (T - H) *
            (2 * (M + 4 * C * X / Real.sqrt T) *
              (4 * C * X / Real.sqrt T)) := by
  obtain ⟨kappa, C, T0, hC, hT0, hsection⟩ :=
    exists_abs_integral_selbergSqrtZetaMollifiedAutocorrelation_sub_signedThetaModel_le
  refine ⟨kappa, C, T0, hC, hT0, ?_⟩
  intro X hX T H M hT hH hHT hM hmodel
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) (hT0.trans hT)
  have hlong : T ≤ 2 * T - H := by linarith
  let nuShift : Measure ℝ := volume.restrict (Ioc 0 H)
  let muHeight : Measure ℝ := volume.restrict (Ioc T (2 * T - H))
  let actualKernel : (ℝ × ℝ) × ℝ → ℝ :=
    selbergSqrtZetaMollifiedAutocorrelationShiftKernel X
  let modelKernel : (ℝ × ℝ) × ℝ → ℝ :=
    selbergSqrtZetaSignedThetaModelAutocorrelationShiftKernel kappa T X
  let E : ℝ :=
    (T - H) *
      (2 * (M + 4 * C * X / Real.sqrt T) *
        (4 * C * X / Real.sqrt T))
  obtain ⟨hactual, hmodelInt⟩ :=
    integrable_selbergSqrtZetaSignedAutocorrelationShiftKernels
      kappa T X hTpos hH hHT
  have hactual' : Integrable actualKernel
      ((nuShift.prod nuShift).prod muHeight) := by
    simpa only [actualKernel, nuShift, muHeight] using hactual
  have hmodel' : Integrable modelKernel
      ((nuShift.prod nuShift).prod muHeight) := by
    simpa only [modelKernel, nuShift, muHeight] using hmodelInt
  have hactualOuter : Integrable
      (fun p : ℝ × ℝ => ∫ x, actualKernel (p, x) ∂muHeight)
      (nuShift.prod nuShift) :=
    hactual'.integral_prod_left
  have hmodelOuter : Integrable
      (fun p : ℝ × ℝ => ∫ x, modelKernel (p, x) ∂muHeight)
      (nuShift.prod nuShift) :=
    hmodel'.integral_prod_left
  have hfixed : ∀ v ∈ Icc 0 H, ∀ w ∈ Icc 0 H,
      |(∫ x in T..2 * T - H,
            selbergSqrtZetaMollifiedHardyZ X (x + v) *
              selbergSqrtZetaMollifiedHardyZ X (x + w)) -
          ∫ x in T..2 * T - H,
            selbergSqrtZetaSignedThetaModel kappa T X (x + v) *
              selbergSqrtZetaSignedThetaModel kappa T X (x + w)| ≤ E := by
    intro v hv w hw
    have htau : w - v ∈ Icc (-H) H := by
      constructor <;> linarith [hv.1, hv.2, hw.1, hw.2]
    have hvsection :
        v ∈ Icc (max 0 (-(w - v))) (min H (H - (w - v))) := by
      constructor
      · rw [max_le_iff]
        constructor <;> linarith [hv.1, hw.1]
      · rw [le_min_iff]
        constructor <;> linarith [hv.2, hw.2]
    have hbase :=
      hsection X hX T H (w - v) v M hT hH hHT htau hvsection hM hmodel
    have hadd (x : ℝ) : x + v + (w - v) = x + w := by ring
    have hactualShift :
        (∫ x in T..2 * T - H,
            selbergSqrtZetaMollifiedHardyZ X (x + v) *
              selbergSqrtZetaMollifiedHardyZ X (x + w)) =
          ∫ x in T + v..(2 * T - H) + v,
            selbergSqrtZetaMollifiedHardyZ X x *
              selbergSqrtZetaMollifiedHardyZ X (x + (w - v)) := by
      simpa only [hadd] using
        intervalIntegral.integral_comp_add_right
          (fun x =>
            selbergSqrtZetaMollifiedHardyZ X x *
              selbergSqrtZetaMollifiedHardyZ X (x + (w - v))) v
    have hmodelShift :
        (∫ x in T..2 * T - H,
            selbergSqrtZetaSignedThetaModel kappa T X (x + v) *
              selbergSqrtZetaSignedThetaModel kappa T X (x + w)) =
          ∫ x in T + v..(2 * T - H) + v,
            selbergSqrtZetaSignedThetaModel kappa T X x *
              selbergSqrtZetaSignedThetaModel kappa T X (x + (w - v)) := by
      simpa only [hadd] using
        intervalIntegral.integral_comp_add_right
          (fun x =>
            selbergSqrtZetaSignedThetaModel kappa T X x *
              selbergSqrtZetaSignedThetaModel kappa T X (x + (w - v))) v
    simpa only [E, hactualShift, hmodelShift] using hbase
  have hpoint : ∀ᵐ p ∂nuShift.prod nuShift,
      ‖(∫ x, actualKernel (p, x) ∂muHeight) -
          ∫ x, modelKernel (p, x) ∂muHeight‖ ≤ E := by
    dsimp only [nuShift]
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem
      (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
    have hv : p.1 ∈ Icc 0 H := ⟨le_of_lt hp.1.1, hp.1.2⟩
    have hw : p.2 ∈ Icc 0 H := ⟨le_of_lt hp.2.1, hp.2.2⟩
    simpa only [muHeight, actualKernel, modelKernel,
      intervalIntegral.integral_of_le hlong, Real.norm_eq_abs,
      selbergSqrtZetaMollifiedAutocorrelationShiftKernel,
      selbergSqrtZetaSignedThetaModelAutocorrelationShiftKernel] using
      hfixed p.1 hv p.2 hw
  have hshiftMeasure :
      (nuShift.prod nuShift).real Set.univ = H ^ 2 := by
    dsimp only [nuShift]
    rw [Measure.prod_restrict, measureReal_def,
      Measure.restrict_apply_univ, Measure.prod_prod,
      Real.volume_Ioc, sub_zero, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hH]
    ring
  have hactualTriple :
      (∫ v in 0..H, ∫ w in 0..H, ∫ x in T..2 * T - H,
          selbergSqrtZetaMollifiedHardyZ X (x + v) *
            selbergSqrtZetaMollifiedHardyZ X (x + w)) =
        ∫ p, ∫ x, actualKernel (p, x) ∂muHeight
          ∂nuShift.prod nuShift := by
    rw [integral_prod _ hactualOuter]
    simp only [nuShift, muHeight, actualKernel,
      intervalIntegral.integral_of_le hH,
      intervalIntegral.integral_of_le hlong,
      selbergSqrtZetaMollifiedAutocorrelationShiftKernel]
  have hmodelTriple :
      (∫ v in 0..H, ∫ w in 0..H, ∫ x in T..2 * T - H,
          selbergSqrtZetaSignedThetaModel kappa T X (x + v) *
            selbergSqrtZetaSignedThetaModel kappa T X (x + w)) =
        ∫ p, ∫ x, modelKernel (p, x) ∂muHeight
          ∂nuShift.prod nuShift := by
    rw [integral_prod _ hmodelOuter]
    simp only [nuShift, muHeight, modelKernel,
      intervalIntegral.integral_of_le hH,
      intervalIntegral.integral_of_le hlong,
      selbergSqrtZetaSignedThetaModelAutocorrelationShiftKernel]
  rw [hactualTriple, hmodelTriple]
  rw [← integral_sub hactualOuter hmodelOuter]
  change ‖∫ p, (∫ x, actualKernel (p, x) ∂muHeight) -
      ∫ x, modelKernel (p, x) ∂muHeight ∂nuShift.prod nuShift‖ ≤ _
  calc
    ‖∫ p, (∫ x, actualKernel (p, x) ∂muHeight) -
        ∫ x, modelKernel (p, x) ∂muHeight ∂nuShift.prod nuShift‖ ≤
        E * (nuShift.prod nuShift).real Set.univ :=
      norm_integral_le_of_norm_le_const hpoint
    _ = H ^ 2 * (T - H) *
        (2 * (M + 4 * C * X / Real.sqrt T) *
          (4 * C * X / Real.sqrt T)) := by
      rw [hshiftMeasure]
      dsimp only [E]
      ring

end HardyTheorem
