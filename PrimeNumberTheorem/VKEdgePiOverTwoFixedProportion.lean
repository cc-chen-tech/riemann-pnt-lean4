import MathlibAux.ScaledPaleyZygmund
import PrimeNumberTheorem.VKEdgePiOverTwoSweptL2

open Complex Filter MeasureTheory Set

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

theorem measurable_normalizedPsiError_fixedProportion (rho : ℂ) :
    Measurable (normalizedPsiError rho) := by
  have hpsi : Measurable chebyshevPsi := by
    simpa only [chebyshevPsi_eq_mathlib] using
      Chebyshev.psi_mono.measurable
  unfold normalizedPsiError
  fun_prop

/--
Conditional on an external matching fourth-moment upper bound for the true
normalized PNT error, an off-line zeta zero forces a fixed-proportion
large-value set in every sufficiently late epsilon logarithmic window.

The project does not prove `hExternalFourthMoment`; it is an explicit analytic
hypothesis of this theorem.
-/
theorem
    exists_eventually_fixedProportion_largeNormalizedPsiError_of_fourthMoment
    {ε C4 : ℝ} {rho : ℂ} {sigma : ℝ}
    (hε : 0 < ε)
    (hgamma : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (hσ : 1 / 2 < sigma)
    (hσrho : sigma < rho.re)
    (hrhoRe1 : rho.re < 1)
    (hC4 : 0 < C4)
    (hExternalFourthMoment :
      ∀ᶠ Y : ℝ in atTop,
        IntegrableOn
            (fun y => normalizedPsiError rho y ^ 4)
            (Icc (Real.log Y) ((1 + ε) * Real.log Y)) ∧
          (∫ y in Icc (Real.log Y) ((1 + ε) * Real.log Y),
              normalizedPsiError rho y ^ 4) ≤
            C4 * Real.log Y) :
    ∃ k : ℕ,
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0 ∧
      0 < centeredSharpenedSweptOrdinaryL2Constant ε rho k ∧
      ∀ᶠ Y : ℝ in atTop,
        (centeredSharpenedSweptOrdinaryL2Constant ε rho k ^ 2 /
              (4 * C4)) *
            Real.log Y <
          volume.real
            {y ∈ Icc (Real.log Y) ((1 + ε) * Real.log Y) |
              centeredSharpenedSweptOrdinaryL2Constant ε rho k /
                    (2 * ε) <
                normalizedPsiError rho y ^ 2} := by
  rcases
      exists_eventually_ordinarySecondMoment_in_epsilonLogWindow_gt_linear
        hε hgamma hzero hσ hσrho hrhoRe1 with
    ⟨k, hmissing, hc2, hsecond⟩
  refine ⟨k, hmissing, hc2, ?_⟩
  filter_upwards [hsecond, hExternalFourthMoment,
    eventually_gt_atTop (1 : ℝ)] with Y hsecondY hfourthY hY
  let window : Set ℝ :=
    Icc (Real.log Y) ((1 + ε) * Real.log Y)
  let c2 : ℝ :=
    centeredSharpenedSweptOrdinaryL2Constant ε rho k
  have hlog : 0 < Real.log Y := Real.log_pos hY
  have hleftRight :
      Real.log Y ≤ (1 + ε) * Real.log Y := by
    nlinarith [mul_pos hε hlog]
  have hmeasure :
      volume.real window = ε * Real.log Y := by
    dsimp only [window]
    rw [Measure.real, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hleftRight)]
    ring
  have hlarge :=
    MathlibAux.measure_sq_largeSet_gt_of_scaled_moments
      (μ := volume) (s := window)
      (g := normalizedPsiError rho)
      (ε := ε) (L := Real.log Y) (c2 := c2) (C4 := C4)
      (θ := (1 / 2 : ℝ))
      measurableSet_Icc measure_Icc_lt_top.ne hmeasure hε hlog hc2 hC4
      (measurable_normalizedPsiError_fixedProportion rho)
      hfourthY.1 hsecondY hfourthY.2 (by norm_num) (by norm_num)
  dsimp only [window, c2] at hlarge ⊢
  convert hlarge using 1 <;>
    (field_simp [hε.ne', hC4.ne'] ; try ring)

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
