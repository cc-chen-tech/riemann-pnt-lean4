import HardyTheorem.SelbergSqrtZetaSignedAutocorrelationShiftBudget
import MathlibAux.AutocorrelationApproximationL2

/-!
# L2 shift-square budget for the signed Selberg model

This replaces the pointwise finite-model bound in the autocorrelation
transfer by the square masses of the actual function and its finite model on
the dyadic control interval.
-/

open MeasureTheory Set

namespace HardyTheorem

/-- On every admissible lag section, dyadic square masses control the error
between the actual mollified autocorrelation and its finite theta model. -/
theorem
    exists_abs_integral_selbergSqrtZetaMollifiedAutocorrelation_sub_signedThetaModel_le_L2 :
    ∃ kappa C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T H tau v MF MP : ℝ,
        T0 ≤ T → 0 ≤ H → H ≤ T →
        tau ∈ Icc (-H) H →
        v ∈ Icc (max 0 (-tau)) (min H (H - tau)) →
        (∫ x in T..2 * T,
          selbergSqrtZetaMollifiedHardyZ X x ^ 2) ≤ MF →
        (∫ x in T..2 * T,
          selbergSqrtZetaSignedThetaModel kappa T X x ^ 2) ≤ MP →
        |(∫ x in T + v..(2 * T - H) + v,
              selbergSqrtZetaMollifiedHardyZ X x *
                selbergSqrtZetaMollifiedHardyZ X (x + tau)) -
            ∫ x in T + v..(2 * T - H) + v,
              selbergSqrtZetaSignedThetaModel kappa T X x *
                selbergSqrtZetaSignedThetaModel kappa T X (x + tau)| ≤
          (4 * C * X / Real.sqrt T) * Real.sqrt (T - H) *
            (Real.sqrt MF + Real.sqrt MP) := by
  obtain ⟨kappa, C, T0, hC, hT0, happ⟩ :=
    exists_abs_selbergSqrtZetaMollifiedHardyZ_sub_signedThetaModel_le_four_mul
  refine ⟨kappa, C, T0, hC, hT0, ?_⟩
  intro X hX T H tau v MF MP hT hH hHT htau hv hFmass hPmass
  let F : ℝ → ℝ := selbergSqrtZetaMollifiedHardyZ X
  let P : ℝ → ℝ := selbergSqrtZetaSignedThetaModel kappa T X
  let eps : ℝ := 4 * C * X / Real.sqrt T
  let A : ℝ := T + v
  let B : ℝ := (2 * T - H) + v
  let lo : ℝ := min A (A + tau)
  let hi : ℝ := max B (B + tau)
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) (hT0.trans hT)
  have hTtwo : T ≤ 2 * T := by linarith
  have heps : 0 ≤ eps := by
    dsimp only [eps]
    positivity
  have hAB : A ≤ B := by
    dsimp only [A, B]
    linarith
  have hcontrol :
      Icc lo hi ⊆ Icc T (2 * T) := by
    dsimp only [lo, hi, A, B]
    exact selberg_lag_controlInterval_subset_dyadic htau hv
  have hlohi : lo ≤ hi := by
    exact (min_le_left A (A + tau)).trans
      (hAB.trans (le_max_left B (B + tau)))
  have hloMem : lo ∈ Icc lo hi := ⟨le_rfl, hlohi⟩
  have hiMem : hi ∈ Icc lo hi := ⟨hlohi, le_rfl⟩
  have hTlo : T ≤ lo := (hcontrol hloMem).1
  have hhiTwoT : hi ≤ 2 * T := (hcontrol hiMem).2
  have hPdyadic : ContinuousOn P (Icc T (2 * T)) := by
    dsimp only [P]
    exact
      continuousOn_selbergSqrtZetaSignedThetaModel_Icc_T_two_mul_T
        kappa T X hTpos
  have hFcontrol : ContinuousOn F (Icc lo hi) := by
    exact (continuous_selbergSqrtZetaMollifiedHardyZ X).continuousOn
  have hPcontrol : ContinuousOn P (Icc lo hi) :=
    hPdyadic.mono hcontrol
  have happrox : ∀ x ∈ Icc lo hi, |F x - P x| ≤ eps := by
    intro x hx
    exact happ X hX T x hT (hcontrol hx)
  have hFglobalInt : IntervalIntegrable (fun x => F x ^ 2)
      volume T (2 * T) := by
    exact
      ((continuous_selbergSqrtZetaMollifiedHardyZ X).pow 2).intervalIntegrable
        T (2 * T)
  have hPglobalInt : IntervalIntegrable (fun x => P x ^ 2)
      volume T (2 * T) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hTtwo]
    exact hPdyadic.pow 2
  have hFcontrolMass :
      (∫ x in lo..hi, F x ^ 2) ≤ MF := by
    calc
      (∫ x in lo..hi, F x ^ 2) ≤ ∫ x in T..2 * T, F x ^ 2 :=
        intervalIntegral.integral_mono_interval hTlo hlohi hhiTwoT
          (Filter.Eventually.of_forall fun x => sq_nonneg (F x))
          hFglobalInt
      _ ≤ MF := by simpa only [F] using hFmass
  have hPcontrolMass :
      (∫ x in lo..hi, P x ^ 2) ≤ MP := by
    calc
      (∫ x in lo..hi, P x ^ 2) ≤ ∫ x in T..2 * T, P x ^ 2 :=
        intervalIntegral.integral_mono_interval hTlo hlohi hhiTwoT
          (Filter.Eventually.of_forall fun x => sq_nonneg (P x))
          hPglobalInt
      _ ≤ MP := by simpa only [P] using hPmass
  have htransfer :=
    MathlibAux.abs_integral_mul_shift_sub_mul_shift_le_of_continuousOn_L2
      hFcontrol hPcontrol hAB heps happrox hFcontrolMass hPcontrolMass
  simpa only [F, P, A, B, eps, lo, hi, show
      ((2 * T - H) + v) - (T + v) = T - H by ring] using htransfer

/-- Integrating the L2 lag-section estimate over the shift square costs
exactly its area `H²`. -/
theorem
    exists_abs_integral_integral_integral_selbergSqrtZetaMollifiedAutocorrelation_sub_signedThetaModel_le_L2 :
    ∃ kappa C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T H MF MP : ℝ,
        T0 ≤ T → 0 ≤ H → H ≤ T →
        (∫ x in T..2 * T,
          selbergSqrtZetaMollifiedHardyZ X x ^ 2) ≤ MF →
        (∫ x in T..2 * T,
          selbergSqrtZetaSignedThetaModel kappa T X x ^ 2) ≤ MP →
        |(∫ v in 0..H, ∫ w in 0..H, ∫ x in T..2 * T - H,
              selbergSqrtZetaMollifiedHardyZ X (x + v) *
                selbergSqrtZetaMollifiedHardyZ X (x + w)) -
            ∫ v in 0..H, ∫ w in 0..H, ∫ x in T..2 * T - H,
              selbergSqrtZetaSignedThetaModel kappa T X (x + v) *
                selbergSqrtZetaSignedThetaModel kappa T X (x + w)| ≤
          H ^ 2 * (4 * C * X / Real.sqrt T) * Real.sqrt (T - H) *
            (Real.sqrt MF + Real.sqrt MP) := by
  obtain ⟨kappa, C, T0, hC, hT0, hsection⟩ :=
    exists_abs_integral_selbergSqrtZetaMollifiedAutocorrelation_sub_signedThetaModel_le_L2
  refine ⟨kappa, C, T0, hC, hT0, ?_⟩
  intro X hX T H MF MP hT hH hHT hFmass hPmass
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) (hT0.trans hT)
  have hlong : T ≤ 2 * T - H := by linarith
  let nuShift : Measure ℝ := volume.restrict (Ioc 0 H)
  let muHeight : Measure ℝ := volume.restrict (Ioc T (2 * T - H))
  let actualKernel : (ℝ × ℝ) × ℝ → ℝ :=
    selbergSqrtZetaMollifiedAutocorrelationShiftKernel X
  let modelKernel : (ℝ × ℝ) × ℝ → ℝ :=
    selbergSqrtZetaSignedThetaModelAutocorrelationShiftKernel kappa T X
  let E : ℝ :=
    (4 * C * X / Real.sqrt T) * Real.sqrt (T - H) *
      (Real.sqrt MF + Real.sqrt MP)
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
      hsection X hX T H (w - v) v MF MP hT hH hHT
        htau hvsection hFmass hPmass
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
              selbergSqrtZetaSignedThetaModel kappa T X
                (x + (w - v)) := by
      simpa only [hadd] using
        intervalIntegral.integral_comp_add_right
          (fun x =>
            selbergSqrtZetaSignedThetaModel kappa T X x *
              selbergSqrtZetaSignedThetaModel kappa T X
                (x + (w - v))) v
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
    _ = H ^ 2 * (4 * C * X / Real.sqrt T) * Real.sqrt (T - H) *
        (Real.sqrt MF + Real.sqrt MP) := by
      rw [hshiftMeasure]
      dsimp only [E]
      ring

end HardyTheorem
