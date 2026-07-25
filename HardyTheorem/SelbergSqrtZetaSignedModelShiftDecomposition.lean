import HardyTheorem.SelbergSqrtZetaSignedCollectedShiftBudget
import HardyTheorem.SelbergSqrtZetaSignedDiagonalShiftBudget
import HardyTheorem.SelbergSqrtZetaSignedPseudoShiftBudget

/-!
# Shift-averaged real-model correlation decomposition

The product of two real parts is half the sum of an ordinary complex
correlation and a pseudo-correlation. This module lifts that pointwise
identity through the complete shift-height box. The resulting norm bound
retains the oscillatory cancellation already proved separately for the two
complex correlations.
-/

open Complex MeasureTheory Set

namespace HardyTheorem

/-- The full ordinary complex correlation on the shift-height box. -/
noncomputable def selbergSqrtZetaSignedOrdinaryShiftKernel
    (kappa T : ℝ) (X : ℕ) (p : (ℝ × ℝ) × ℝ) : ℂ :=
  selbergSqrtZetaSignedComplexModel kappa T X (p.2 + p.1.1) *
    (starRingEnd ℂ)
      (selbergSqrtZetaSignedComplexModel kappa T X (p.2 + p.1.2))

/-- The real signed-theta-model correlation on the shift-height box. -/
noncomputable def selbergSqrtZetaSignedThetaShiftKernel
    (kappa T : ℝ) (X : ℕ) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  selbergSqrtZetaSignedThetaModel kappa T X (p.2 + p.1.1) *
    selbergSqrtZetaSignedThetaModel kappa T X (p.2 + p.1.2)

/-- The full ordinary correlation is integrable because it is the sum of
the already-integrable unequal-frequency remainder and same-frequency
diagonal block. -/
theorem integrable_selbergSqrtZetaSignedOrdinaryShiftKernel
    (kappa T : ℝ) (X : ℕ) {delta : ℝ}
    (hT : 0 < T) (hroom : delta ≤ T) :
    Integrable
      (selbergSqrtZetaSignedOrdinaryShiftKernel kappa T X)
      (((volume.restrict (Ioc 0 delta)).prod
          (volume.restrict (Ioc 0 delta))).prod
        (volume.restrict (Ioc T (2 * T - delta)))) := by
  let mu :=
    ((volume.restrict (Ioc 0 delta)).prod
      (volume.restrict (Ioc 0 delta))).prod
      (volume.restrict (Ioc T (2 * T - delta)))
  have hrem :
      Integrable
        (selbergSqrtZetaSignedCollectedCorrelationShiftKernel kappa T X) mu := by
    simpa only [mu] using
      integrable_selbergSqrtZetaSignedCollectedCorrelationShiftKernel
        kappa T X hT hroom
  have hdiag :
      Integrable
        (selbergSqrtZetaSignedDiagonalShiftKernel T X) mu := by
    simpa only [mu] using
      integrable_selbergSqrtZetaSignedDiagonalShiftKernel T X hT hroom
  apply (hrem.add hdiag).congr
  filter_upwards with p
  simp only [Pi.add_apply]
  unfold selbergSqrtZetaSignedOrdinaryShiftKernel
    selbergSqrtZetaSignedCollectedCorrelationShiftKernel
    selbergSqrtZetaSignedDiagonalShiftKernel
  ring

/-- The real signed-theta correlation is integrable on the same box. -/
theorem integrable_selbergSqrtZetaSignedThetaShiftKernel
    (kappa T : ℝ) (X : ℕ) {delta : ℝ}
    (hT : 0 < T) (hroom : delta ≤ T) :
    Integrable
      (selbergSqrtZetaSignedThetaShiftKernel kappa T X)
      (((volume.restrict (Ioc 0 delta)).prod
          (volume.restrict (Ioc 0 delta))).prod
        (volume.restrict (Ioc T (2 * T - delta)))) := by
  let mu :=
    ((volume.restrict (Ioc 0 delta)).prod
      (volume.restrict (Ioc 0 delta))).prod
      (volume.restrict (Ioc T (2 * T - delta)))
  have hord :
      Integrable
        (selbergSqrtZetaSignedOrdinaryShiftKernel kappa T X) mu := by
    simpa only [mu] using
      integrable_selbergSqrtZetaSignedOrdinaryShiftKernel
        kappa T X hT hroom
  have hpseudo :
      Integrable
        (selbergSqrtZetaSignedPseudoShiftKernel kappa T X) mu := by
    simpa only [mu] using
      integrable_selbergSqrtZetaSignedPseudoShiftKernel
        kappa T X hT hroom
  have hsum : Integrable
      (fun p =>
        (selbergSqrtZetaSignedOrdinaryShiftKernel kappa T X p).re +
          (selbergSqrtZetaSignedPseudoShiftKernel kappa T X p).re) mu :=
    hord.re.add hpseudo.re
  apply (hsum.const_mul (1 / 2 : ℝ)).congr
  filter_upwards with p
  unfold selbergSqrtZetaSignedThetaShiftKernel
    selbergSqrtZetaSignedOrdinaryShiftKernel
    selbergSqrtZetaSignedPseudoShiftKernel
  rw [
    selbergSqrtZetaSignedThetaModel_mul_eq_correlation_add_pseudocorrelation]
  ring

/-- On the product box, the real-model correlation integral is exactly half
the sum of the real parts of the ordinary and pseudo complex integrals. -/
theorem integral_selbergSqrtZetaSignedThetaShiftKernel_eq
    (kappa T : ℝ) (X : ℕ) {delta : ℝ}
    (hT : 0 < T) (hroom : delta ≤ T) :
    (∫ p,
        selbergSqrtZetaSignedThetaShiftKernel kappa T X p
        ∂(((volume.restrict (Ioc 0 delta)).prod
            (volume.restrict (Ioc 0 delta))).prod
          (volume.restrict (Ioc T (2 * T - delta))))) =
      ((∫ p,
          selbergSqrtZetaSignedOrdinaryShiftKernel kappa T X p
          ∂(((volume.restrict (Ioc 0 delta)).prod
              (volume.restrict (Ioc 0 delta))).prod
            (volume.restrict (Ioc T (2 * T - delta))))).re +
        (∫ p,
          selbergSqrtZetaSignedPseudoShiftKernel kappa T X p
          ∂(((volume.restrict (Ioc 0 delta)).prod
              (volume.restrict (Ioc 0 delta))).prod
            (volume.restrict (Ioc T (2 * T - delta))))).re) / 2 := by
  let mu :=
    ((volume.restrict (Ioc 0 delta)).prod
      (volume.restrict (Ioc 0 delta))).prod
      (volume.restrict (Ioc T (2 * T - delta)))
  have hord :
      Integrable
        (selbergSqrtZetaSignedOrdinaryShiftKernel kappa T X) mu := by
    simpa only [mu] using
      integrable_selbergSqrtZetaSignedOrdinaryShiftKernel
        kappa T X hT hroom
  have hpseudo :
      Integrable
        (selbergSqrtZetaSignedPseudoShiftKernel kappa T X) mu := by
    simpa only [mu] using
      integrable_selbergSqrtZetaSignedPseudoShiftKernel
        kappa T X hT hroom
  have hpoint : ∀ p,
      selbergSqrtZetaSignedThetaShiftKernel kappa T X p =
        ((selbergSqrtZetaSignedOrdinaryShiftKernel kappa T X p).re +
          (selbergSqrtZetaSignedPseudoShiftKernel kappa T X p).re) / 2 := by
    intro p
    unfold selbergSqrtZetaSignedThetaShiftKernel
      selbergSqrtZetaSignedOrdinaryShiftKernel
      selbergSqrtZetaSignedPseudoShiftKernel
    exact
      selbergSqrtZetaSignedThetaModel_mul_eq_correlation_add_pseudocorrelation
        kappa T X _ _
  have hadd :
      (∫ p,
          ((selbergSqrtZetaSignedOrdinaryShiftKernel kappa T X p).re +
            (selbergSqrtZetaSignedPseudoShiftKernel kappa T X p).re) ∂mu) =
        (∫ p,
            (selbergSqrtZetaSignedOrdinaryShiftKernel kappa T X p).re ∂mu) +
          ∫ p,
            (selbergSqrtZetaSignedPseudoShiftKernel kappa T X p).re ∂mu := by
    exact integral_add hord.re hpseudo.re
  have hordRe :
      (∫ p,
          (selbergSqrtZetaSignedOrdinaryShiftKernel kappa T X p).re ∂mu) =
        (∫ p,
          selbergSqrtZetaSignedOrdinaryShiftKernel kappa T X p ∂mu).re := by
    simpa using integral_re hord
  have hpseudoRe :
      (∫ p,
          (selbergSqrtZetaSignedPseudoShiftKernel kappa T X p).re ∂mu) =
        (∫ p,
          selbergSqrtZetaSignedPseudoShiftKernel kappa T X p ∂mu).re := by
    simpa using integral_re hpseudo
  change (∫ p, selbergSqrtZetaSignedThetaShiftKernel kappa T X p ∂mu) = _
  calc
    (∫ p, selbergSqrtZetaSignedThetaShiftKernel kappa T X p ∂mu) =
        ∫ p,
          (1 / 2 : ℝ) *
            ((selbergSqrtZetaSignedOrdinaryShiftKernel kappa T X p).re +
              (selbergSqrtZetaSignedPseudoShiftKernel kappa T X p).re) ∂mu := by
      apply integral_congr_ae
      filter_upwards with p
      rw [hpoint p]
      ring
    _ = (1 / 2 : ℝ) *
        (∫ p,
          ((selbergSqrtZetaSignedOrdinaryShiftKernel kappa T X p).re +
            (selbergSqrtZetaSignedPseudoShiftKernel kappa T X p).re) ∂mu) := by
      rw [integral_const_mul]
    _ = (1 / 2 : ℝ) *
        ((∫ p,
            (selbergSqrtZetaSignedOrdinaryShiftKernel kappa T X p).re ∂mu) +
          ∫ p,
            (selbergSqrtZetaSignedPseudoShiftKernel kappa T X p).re ∂mu) := by
      rw [hadd]
    _ = (1 / 2 : ℝ) *
        ((∫ p,
            selbergSqrtZetaSignedOrdinaryShiftKernel kappa T X p ∂mu).re +
          (∫ p,
            selbergSqrtZetaSignedPseudoShiftKernel kappa T X p ∂mu).re) := by
      rw [hordRe, hpseudoRe]
    _ = ((∫ p,
            selbergSqrtZetaSignedOrdinaryShiftKernel kappa T X p ∂mu).re +
          (∫ p,
            selbergSqrtZetaSignedPseudoShiftKernel kappa T X p ∂mu).re) / 2 := by
      ring

/-- The shift-averaged real-model correlation is bounded by half the sum of
the ordinary and pseudo complex correlation norms. -/
theorem
    abs_integral_integral_integral_selbergSqrtZetaSignedThetaModel_mul_shift_le
    (kappa T : ℝ) (X : ℕ) {delta : ℝ}
    (hT : 0 < T) (hdelta : 0 ≤ delta) (hroom : delta ≤ T) :
    |∫ v in 0..delta, ∫ w in 0..delta, ∫ t in T..2 * T - delta,
        selbergSqrtZetaSignedThetaModel kappa T X (t + v) *
          selbergSqrtZetaSignedThetaModel kappa T X (t + w)| ≤
      (‖∫ v in 0..delta, ∫ w in 0..delta, ∫ t in T..2 * T - delta,
          selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
            (starRingEnd ℂ)
              (selbergSqrtZetaSignedComplexModel kappa T X (t + w))‖ +
        ‖∫ v in 0..delta, ∫ w in 0..delta, ∫ t in T..2 * T - delta,
          selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
            selbergSqrtZetaSignedComplexModel kappa T X (t + w)‖) / 2 := by
  have hlong : T ≤ 2 * T - delta := by linarith
  let nuShift : Measure ℝ := volume.restrict (Ioc 0 delta)
  let muHeight : Measure ℝ := volume.restrict (Ioc T (2 * T - delta))
  let muBox : Measure ((ℝ × ℝ) × ℝ) :=
    (nuShift.prod nuShift).prod muHeight
  let Ftheta : (ℝ × ℝ) × ℝ → ℝ :=
    selbergSqrtZetaSignedThetaShiftKernel kappa T X
  let Ford : (ℝ × ℝ) × ℝ → ℂ :=
    selbergSqrtZetaSignedOrdinaryShiftKernel kappa T X
  let Fpseudo : (ℝ × ℝ) × ℝ → ℂ :=
    selbergSqrtZetaSignedPseudoShiftKernel kappa T X
  have htheta : Integrable Ftheta muBox := by
    simpa only [Ftheta, muBox, nuShift, muHeight] using
      integrable_selbergSqrtZetaSignedThetaShiftKernel
        kappa T X hT hroom
  have hord : Integrable Ford muBox := by
    simpa only [Ford, muBox, nuShift, muHeight] using
      integrable_selbergSqrtZetaSignedOrdinaryShiftKernel
        kappa T X hT hroom
  have hpseudo : Integrable Fpseudo muBox := by
    simpa only [Fpseudo, muBox, nuShift, muHeight] using
      integrable_selbergSqrtZetaSignedPseudoShiftKernel
        kappa T X hT hroom
  have houterTheta : Integrable
      (fun p : ℝ × ℝ => ∫ t, Ftheta (p, t) ∂muHeight)
      (nuShift.prod nuShift) :=
    htheta.integral_prod_left
  have houterOrd : Integrable
      (fun p : ℝ × ℝ => ∫ t, Ford (p, t) ∂muHeight)
      (nuShift.prod nuShift) :=
    hord.integral_prod_left
  have houterPseudo : Integrable
      (fun p : ℝ × ℝ => ∫ t, Fpseudo (p, t) ∂muHeight)
      (nuShift.prod nuShift) :=
    hpseudo.integral_prod_left
  have htripleTheta :
      (∫ v in 0..delta, ∫ w in 0..delta, ∫ t in T..2 * T - delta,
        selbergSqrtZetaSignedThetaModel kappa T X (t + v) *
          selbergSqrtZetaSignedThetaModel kappa T X (t + w)) =
        ∫ p, Ftheta p ∂muBox := by
    calc
      _ = ∫ p, ∫ t, Ftheta (p, t) ∂muHeight
          ∂nuShift.prod nuShift := by
        rw [integral_prod _ houterTheta]
        simp only [nuShift, muHeight, Ftheta,
          intervalIntegral.integral_of_le hdelta,
          intervalIntegral.integral_of_le hlong,
          selbergSqrtZetaSignedThetaShiftKernel]
      _ = ∫ p, Ftheta p ∂muBox := by
        simpa only [muBox] using (integral_prod Ftheta htheta).symm
  have htripleOrd :
      (∫ v in 0..delta, ∫ w in 0..delta, ∫ t in T..2 * T - delta,
        selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
          (starRingEnd ℂ)
            (selbergSqrtZetaSignedComplexModel kappa T X (t + w))) =
        ∫ p, Ford p ∂muBox := by
    calc
      _ = ∫ p, ∫ t, Ford (p, t) ∂muHeight
          ∂nuShift.prod nuShift := by
        rw [integral_prod _ houterOrd]
        simp only [nuShift, muHeight, Ford,
          intervalIntegral.integral_of_le hdelta,
          intervalIntegral.integral_of_le hlong,
          selbergSqrtZetaSignedOrdinaryShiftKernel]
      _ = ∫ p, Ford p ∂muBox := by
        simpa only [muBox] using (integral_prod Ford hord).symm
  have htriplePseudo :
      (∫ v in 0..delta, ∫ w in 0..delta, ∫ t in T..2 * T - delta,
        selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
          selbergSqrtZetaSignedComplexModel kappa T X (t + w)) =
        ∫ p, Fpseudo p ∂muBox := by
    calc
      _ = ∫ p, ∫ t, Fpseudo (p, t) ∂muHeight
          ∂nuShift.prod nuShift := by
        rw [integral_prod _ houterPseudo]
        simp only [nuShift, muHeight, Fpseudo,
          intervalIntegral.integral_of_le hdelta,
          intervalIntegral.integral_of_le hlong,
          selbergSqrtZetaSignedPseudoShiftKernel]
      _ = ∫ p, Fpseudo p ∂muBox := by
        simpa only [muBox] using (integral_prod Fpseudo hpseudo).symm
  have hidentity :
      (∫ p, Ftheta p ∂muBox) =
        ((∫ p, Ford p ∂muBox).re +
          (∫ p, Fpseudo p ∂muBox).re) / 2 := by
    simpa only [Ftheta, Ford, Fpseudo, muBox, nuShift, muHeight] using
      integral_selbergSqrtZetaSignedThetaShiftKernel_eq
        kappa T X hT hroom
  rw [htripleTheta, htripleOrd, htriplePseudo, hidentity]
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact
    (div_le_div_of_nonneg_right
      (abs_add_le _ _)
      (by norm_num)).trans
      (div_le_div_of_nonneg_right
        (add_le_add
          (Complex.abs_re_le_norm _)
          (Complex.abs_re_le_norm _))
        (by norm_num))

end HardyTheorem
