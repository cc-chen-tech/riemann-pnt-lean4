import PrimeNumberTheorem.ExplicitFormulaNormalizedWindowRemainder

open Complex Filter Set Topology

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

open ExplicitFormulaAux

/-!
# Independently parameterized power-height remainders

This module selects a genuine good explicit-formula height of size
`exp (gammaLow * a)`.  It keeps the detector exponent `gammaLow` independent
of any outer contour exponent used by downstream arguments.
-/

/-- Deterministic normalized remainder envelope at detector height
`exp (gammaLow * a)` on `[a, a + L]`. -/
noncomputable def normalizedPowerHeightWindowRemainderEnvelope
    (C D beta gammaLow L a : ℝ) : ℝ :=
  C * Real.exp ((1 - beta) * L) *
      (Real.exp ((1 - beta - gammaLow) * a) *
        ((1 + a + L) ^ 2 + (2 + gammaLow * a) ^ 2)) +
    2 * D * Real.exp ((gammaLow - beta) * a) *
      (2 + gammaLow * a) +
    Real.exp (-beta * a) *
      (1 + 2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound + a + L)

private theorem tendsto_exp_mul_quadratic_powerHeight
    {c u v w : ℝ} (hc : c < 0) :
    Tendsto
      (fun a : ℝ => Real.exp (c * a) * (u * a ^ 2 + v * a + w))
      atTop (nhds 0) := by
  have hpow (k : ℕ) :
      Tendsto (fun a : ℝ => Real.exp (c * a) * a ^ k)
        atTop (nhds 0) := by
    have hsmall :=
      isLittleO_exp_mul_rpow_of_lt (k : ℝ) (a := c) (b := 0) hc
    have hratio := hsmall.tendsto_div_nhds_zero
    simpa [Real.rpow_natCast] using hratio
  have h2 :
      Tendsto (fun a : ℝ => u * (Real.exp (c * a) * a ^ 2))
        atTop (nhds 0) := by
    simpa using (hpow 2).const_mul u
  have h1 :
      Tendsto (fun a : ℝ => v * (Real.exp (c * a) * a))
        atTop (nhds 0) := by
    simpa using (hpow 1).const_mul v
  have h0 :
      Tendsto (fun a : ℝ => w * Real.exp (c * a))
        atTop (nhds 0) := by
    simpa using (hpow 0).const_mul w
  have hsum :
      Tendsto
        (fun a : ℝ =>
          u * (Real.exp (c * a) * a ^ 2) +
            v * (Real.exp (c * a) * a) +
            w * Real.exp (c * a))
        atTop (nhds 0) := by
    simpa using (h2.add h1).add h0
  convert hsum using 1
  funext a
  ring

/-- The generalized envelope tends to zero on proportional windows when the
low detector height beats both the `x / T` error and the interpolation cost. -/
theorem
    tendsto_normalizedPowerHeightWindowRemainderEnvelope_proportional_atTop_nhds_zero
    {C D beta gammaLow ε : ℝ}
    (hbeta : 1 / 2 < beta)
    (hgammaBeta : gammaLow < beta)
    (hdecay : (1 - beta) * (1 + ε) < gammaLow) :
    Tendsto
      (fun a =>
        normalizedPowerHeightWindowRemainderEnvelope
          C D beta gammaLow (ε * a) a)
      atTop (nhds 0) := by
  let c₁ : ℝ :=
    (1 - beta - gammaLow) + (1 - beta) * ε
  have hc₁ : c₁ < 0 := by
    dsimp [c₁]
    linarith
  have hfirst0 :
      Tendsto
        (fun a : ℝ =>
          Real.exp (c₁ * a) *
            ((1 + a + ε * a) ^ 2 +
              (2 + gammaLow * a) ^ 2))
        atTop (nhds 0) := by
    convert
      tendsto_exp_mul_quadratic_powerHeight
        (c := c₁)
        (u := (1 + ε) ^ 2 + gammaLow ^ 2)
        (v := 2 + 2 * ε + 4 * gammaLow)
        (w := 5) hc₁ using 1
    funext a
    ring
  have hfirst :
      Tendsto
        (fun a : ℝ =>
          C * Real.exp ((1 - beta) * (ε * a)) *
            (Real.exp ((1 - beta - gammaLow) * a) *
              ((1 + a + ε * a) ^ 2 +
                (2 + gammaLow * a) ^ 2)))
        atTop (nhds 0) := by
    have hmul :
        Tendsto
          (fun a : ℝ =>
            C *
              (Real.exp (c₁ * a) *
                ((1 + a + ε * a) ^ 2 +
                  (2 + gammaLow * a) ^ 2)))
          atTop (nhds 0) := by
      simpa using hfirst0.const_mul C
    convert hmul using 1
    funext a
    have hexp :
        Real.exp ((1 - beta) * (ε * a)) *
            Real.exp ((1 - beta - gammaLow) * a) =
          Real.exp (c₁ * a) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [c₁]
      ring
    rw [show
      C * Real.exp ((1 - beta) * (ε * a)) *
            (Real.exp ((1 - beta - gammaLow) * a) *
              ((1 + a + ε * a) ^ 2 +
                (2 + gammaLow * a) ^ 2)) =
          C *
            (Real.exp ((1 - beta) * (ε * a)) *
              Real.exp ((1 - beta - gammaLow) * a)) *
            ((1 + a + ε * a) ^ 2 +
              (2 + gammaLow * a) ^ 2) by ring]
    rw [hexp]
    ring
  have hc₂ : gammaLow - beta < 0 := by linarith
  have hsecond0 :
      Tendsto
        (fun a : ℝ =>
          Real.exp ((gammaLow - beta) * a) *
            (2 + gammaLow * a))
        atTop (nhds 0) := by
    convert
      tendsto_exp_mul_quadratic_powerHeight
        (c := gammaLow - beta) (u := 0) (v := gammaLow) (w := 2)
        hc₂ using 1
    funext a
    ring
  have hsecond :
      Tendsto
        (fun a : ℝ =>
          2 * D * Real.exp ((gammaLow - beta) * a) *
            (2 + gammaLow * a))
        atTop (nhds 0) := by
    have hmul :
        Tendsto
          (fun a : ℝ =>
            (2 * D) *
              (Real.exp ((gammaLow - beta) * a) *
                (2 + gammaLow * a)))
          atTop (nhds 0) := by
      simpa using hsecond0.const_mul (2 * D)
    convert hmul using 1
    funext a
    ring
  have hbetaNeg : -beta < 0 := by linarith
  have hthird :
      Tendsto
        (fun a : ℝ =>
          Real.exp (-beta * a) *
            (1 + 2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound +
              a + ε * a))
        atTop (nhds 0) := by
    convert
      tendsto_exp_mul_quadratic_powerHeight
        (c := -beta) (u := 0) (v := 1 + ε)
        (w :=
          1 + 2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound)
        hbetaNeg using 1
    funext a
    ring
  simpa only [normalizedPowerHeightWindowRemainderEnvelope, zero_add] using
    (hfirst.add hsecond).add hthird

private theorem normalized_real_powerHeight_remainder_le_envelope
    {C D beta gammaLow L a T y : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbeta : 1 / 2 < beta) (hbeta1 : beta < 1)
    (hgamma : 0 < gammaLow)
    (hL : 0 ≤ L) (ha0 : 0 ≤ a)
    (hA : 8 ≤ Real.exp (gammaLow * a))
    (hT : T ∈
      Set.Icc
        (Real.exp (gammaLow * a))
        (Real.exp (gammaLow * a) + 1))
    (hy : y ∈ Set.Icc a (a + L))
    (hraw :
      ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
          (chebyshevPsi0 (Real.exp y) : ℂ)‖ ≤
        C * Real.exp y *
            ((1 + y) ^ 2 +
              (1 + Real.log (Real.exp (gammaLow * a) + 6)) ^ 2) / T +
          (1 + D * T * (1 + Real.log (T + 6))) +
          2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound + y) :
    Real.exp (-beta * y) *
        ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
            (chebyshevPsi0 (Real.exp y) : ℂ)‖ ≤
      normalizedPowerHeightWindowRemainderEnvelope
        C D beta gammaLow L a := by
  have hbeta0 : 0 < beta := by linarith
  have hOneBeta : 0 < 1 - beta := by linarith
  have hApos : 0 < Real.exp (gammaLow * a) := Real.exp_pos _
  have hTpos : 0 < T := hApos.trans_le hT.1
  have hAplus :
      Real.exp (gammaLow * a) + 6 ≤
        2 * Real.exp (gammaLow * a) := by
    nlinarith
  have hTplus :
      T + 6 ≤ 2 * Real.exp (gammaLow * a) := by
    nlinarith [hT.2, hA]
  have hlogTwo : Real.log 2 ≤ 1 :=
    Real.log_two_lt_d9.le.trans (by norm_num)
  have hlogAplus :
      Real.log (Real.exp (gammaLow * a) + 6) ≤
        1 + gammaLow * a := by
    calc
      Real.log (Real.exp (gammaLow * a) + 6) ≤
          Real.log (2 * Real.exp (gammaLow * a)) := by
        exact Real.log_le_log (by positivity) hAplus
      _ = Real.log 2 + gammaLow * a := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
          (ne_of_gt (Real.exp_pos (gammaLow * a))), Real.log_exp]
      _ ≤ 1 + gammaLow * a := by linarith
  have hlogTplus :
      Real.log (T + 6) ≤ 1 + gammaLow * a := by
    calc
      Real.log (T + 6) ≤
          Real.log (2 * Real.exp (gammaLow * a)) := by
        exact Real.log_le_log (by positivity) hTplus
      _ = Real.log 2 + gammaLow * a := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
          (ne_of_gt (Real.exp_pos (gammaLow * a))), Real.log_exp]
      _ ≤ 1 + gammaLow * a := by linarith
  have hlogAplus0 :
      0 ≤ 1 + Real.log (Real.exp (gammaLow * a) + 6) := by
    have hge : 1 ≤ Real.exp (gammaLow * a) + 6 := by
      nlinarith [Real.exp_pos (gammaLow * a)]
    linarith [Real.log_nonneg hge]
  have hlogTplus0 : 0 ≤ 1 + Real.log (T + 6) := by
    have hge : 1 ≤ T + 6 := by linarith
    linarith [Real.log_nonneg hge]
  have hgammaA0 : 0 ≤ gammaLow * a := mul_nonneg hgamma.le ha0
  have hAquad :
      (1 + Real.log (Real.exp (gammaLow * a) + 6)) ^ 2 ≤
        (2 + gammaLow * a) ^ 2 := by
    have huv :
        1 + Real.log (Real.exp (gammaLow * a) + 6) ≤
          2 + gammaLow * a := by linarith
    nlinarith
  have hyone0 : 0 ≤ 1 + y := by linarith [hy.1]
  have hayL0 : 0 ≤ 1 + a + L := by linarith
  have hyquad : (1 + y) ^ 2 ≤ (1 + a + L) ^ 2 := by
    have huv : 1 + y ≤ 1 + a + L := by linarith [hy.2]
    nlinarith
  have hpoly :
      (1 + y) ^ 2 +
          (1 + Real.log (Real.exp (gammaLow * a) + 6)) ^ 2 ≤
        (1 + a + L) ^ 2 + (2 + gammaLow * a) ^ 2 := by
    linarith
  have hTinv : 1 / T ≤ Real.exp (-gammaLow * a) := by
    calc
      1 / T ≤ 1 / Real.exp (gammaLow * a) :=
        one_div_le_one_div_of_le hApos hT.1
      _ = Real.exp (-gammaLow * a) := by
        rw [one_div, ← Real.exp_neg]
        congr 1
        ring
  have hTupper : T ≤ 2 * Real.exp (gammaLow * a) := by
    nlinarith [hT.2, hA]
  have hlogFactor :
      1 + Real.log (T + 6) ≤ 2 + gammaLow * a := by
    linarith
  have hnormMon :
      Real.exp (-beta * y) *
          ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
              (chebyshevPsi0 (Real.exp y) : ℂ)‖ ≤
        Real.exp (-beta * y) *
          (C * Real.exp y *
              ((1 + y) ^ 2 +
                (1 + Real.log (Real.exp (gammaLow * a) + 6)) ^ 2) / T +
            (1 + D * T * (1 + Real.log (T + 6))) +
            2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound + y) :=
    mul_le_mul_of_nonneg_left hraw (Real.exp_pos _).le
  have hfirst :
      Real.exp (-beta * y) *
          (C * Real.exp y *
            ((1 + y) ^ 2 +
              (1 + Real.log (Real.exp (gammaLow * a) + 6)) ^ 2) / T) ≤
        C * Real.exp ((1 - beta) * L) *
          (Real.exp ((1 - beta - gammaLow) * a) *
            ((1 + a + L) ^ 2 + (2 + gammaLow * a) ^ 2)) := by
    have hexpy :
        Real.exp ((1 - beta) * y) ≤
          Real.exp ((1 - beta) * (a + L)) :=
      Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hy.2 hOneBeta.le)
    have hpoly0 :
        0 ≤ (1 + y) ^ 2 +
          (1 + Real.log (Real.exp (gammaLow * a) + 6)) ^ 2 := by
      positivity
    have hexpCombine :
        Real.exp (-beta * y) * Real.exp y =
          Real.exp ((1 - beta) * y) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hexpWindowCombine :
        Real.exp ((1 - beta) * (a + L)) *
            Real.exp (-gammaLow * a) =
          Real.exp ((1 - beta) * L) *
            Real.exp ((1 - beta - gammaLow) * a) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [div_eq_mul_inv]
    calc
      Real.exp (-beta * y) *
          (C * Real.exp y *
            ((1 + y) ^ 2 +
              (1 + Real.log (Real.exp (gammaLow * a) + 6)) ^ 2) * T⁻¹) =
          C * (Real.exp (-beta * y) * Real.exp y) *
            ((1 + y) ^ 2 +
              (1 + Real.log (Real.exp (gammaLow * a) + 6)) ^ 2) *
            (1 / T) := by ring
      _ = C * Real.exp ((1 - beta) * y) *
            ((1 + y) ^ 2 +
              (1 + Real.log (Real.exp (gammaLow * a) + 6)) ^ 2) *
            (1 / T) := by rw [hexpCombine]
      _ ≤ C * Real.exp ((1 - beta) * (a + L)) *
            ((1 + a + L) ^ 2 + (2 + gammaLow * a) ^ 2) *
            Real.exp (-gammaLow * a) := by
        gcongr
      _ = C *
            (Real.exp ((1 - beta) * (a + L)) *
              Real.exp (-gammaLow * a)) *
            ((1 + a + L) ^ 2 + (2 + gammaLow * a) ^ 2) := by
        ring
      _ = C * Real.exp ((1 - beta) * L) *
            (Real.exp ((1 - beta - gammaLow) * a) *
              ((1 + a + L) ^ 2 + (2 + gammaLow * a) ^ 2)) := by
        rw [hexpWindowCombine]
        ring
  have hsecond :
      Real.exp (-beta * y) *
          (1 + D * T * (1 + Real.log (T + 6))) ≤
        Real.exp (-beta * a) +
          2 * D * Real.exp ((gammaLow - beta) * a) *
            (2 + gammaLow * a) := by
    have hnormexp :
        Real.exp (-beta * y) ≤ Real.exp (-beta * a) :=
      Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left hy.1 (by linarith))
    have hprod :
        D * T * (1 + Real.log (T + 6)) ≤
          2 * D * Real.exp (gammaLow * a) *
            (2 + gammaLow * a) := by
      calc
        D * T * (1 + Real.log (T + 6)) ≤
            D * (2 * Real.exp (gammaLow * a)) *
              (2 + gammaLow * a) := by
          gcongr
        _ = _ := by ring
    have hexpCombine :
        Real.exp (-beta * a) * Real.exp (gammaLow * a) =
          Real.exp ((gammaLow - beta) * a) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      Real.exp (-beta * y) *
          (1 + D * T * (1 + Real.log (T + 6))) =
          Real.exp (-beta * y) +
            Real.exp (-beta * y) *
              (D * T * (1 + Real.log (T + 6))) := by ring
      _ ≤ Real.exp (-beta * a) +
            Real.exp (-beta * a) *
              (2 * D * Real.exp (gammaLow * a) *
                (2 + gammaLow * a)) := by
        gcongr
      _ = Real.exp (-beta * a) +
            2 * D * Real.exp ((gammaLow - beta) * a) *
              (2 + gammaLow * a) := by
        rw [show
          Real.exp (-beta * a) *
              (2 * D * Real.exp (gammaLow * a) *
                (2 + gammaLow * a)) =
            2 * D *
              (Real.exp (-beta * a) * Real.exp (gammaLow * a)) *
              (2 + gammaLow * a) by ring]
        rw [hexpCombine]
  have hclosed :
      Real.exp (-beta * y) *
          (2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound + y) ≤
        Real.exp (-beta * a) *
          (2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound + a + L) := by
    have hnormexp :
        Real.exp (-beta * y) ≤ Real.exp (-beta * a) :=
      Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left hy.1 (by linarith))
    have hclosed0 :
        0 ≤ 2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound + y := by
      have hz := VKEdgePiOverTwo.zero_lt_zeroPackageClosedTermsUniformBound
      linarith [hy.1]
    have hclosedLe :
        2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound + y ≤
          2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound + a + L := by
      linarith [hy.2]
    gcongr
  rw [normalizedPowerHeightWindowRemainderEnvelope]
  calc
    Real.exp (-beta * y) *
        ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
            (chebyshevPsi0 (Real.exp y) : ℂ)‖ ≤ _ := hnormMon
    _ = Real.exp (-beta * y) *
          (C * Real.exp y *
            ((1 + y) ^ 2 +
              (1 + Real.log (Real.exp (gammaLow * a) + 6)) ^ 2) / T) +
        Real.exp (-beta * y) *
          (1 + D * T * (1 + Real.log (T + 6))) +
        Real.exp (-beta * y) *
          (2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound + y) := by
      ring
    _ ≤
        C * Real.exp ((1 - beta) * L) *
            (Real.exp ((1 - beta - gammaLow) * a) *
              ((1 + a + L) ^ 2 + (2 + gammaLow * a) ^ 2)) +
          (Real.exp (-beta * a) +
            2 * D * Real.exp ((gammaLow - beta) * a) *
              (2 + gammaLow * a)) +
          Real.exp (-beta * a) *
            (2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound + a + L) := by
      gcongr
    _ = _ := by ring

/-- On every sufficiently late proportional logarithmic window, one genuine
good height of size `exp (gammaLow * a)` makes the normalized finite-height
explicit-formula remainder uniformly small. -/
theorem
    eventually_exists_uniform_goodHeight_normalized_powerHeight_proportional_window_remainder_lt
    {beta gammaLow ε eta : ℝ}
    (hbeta : 1 / 2 < beta)
    (hbeta1 : beta < 1)
    (hgamma : 0 < gammaLow)
    (hgammaBeta : gammaLow < beta)
    (hdecay : (1 - beta) * (1 + ε) < gammaLow)
    (hε : 0 < ε)
    (heta : 0 < eta) :
    ∀ᶠ a : ℝ in atTop,
      ∃ Tlow ∈
          Set.Icc
            (Real.exp (gammaLow * a))
            (Real.exp (gammaLow * a) + 1),
        ExplicitFormulaAux.goodHeight Tlow ∧
          ∀ y ∈ Set.Icc a ((1 + ε) * a),
            Real.exp (-beta * y) *
                ‖explicitFormulaApproxWithMultiplicity (Real.exp y) Tlow -
                  (chebyshevPsi0 (Real.exp y) : ℂ)‖ < eta := by
  rcases
      exists_uniform_goodHeight_Icc_norm_real_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le
      with ⟨C, D, hC, hD, hselect⟩
  have henv :
      Tendsto
        (fun a =>
          normalizedPowerHeightWindowRemainderEnvelope
            C D beta gammaLow (ε * a) a)
        atTop (nhds 0) :=
    tendsto_normalizedPowerHeightWindowRemainderEnvelope_proportional_atTop_nhds_zero
      hbeta hgammaBeta hdecay
  have henvlt :
      ∀ᶠ a in atTop,
        normalizedPowerHeightWindowRemainderEnvelope
          C D beta gammaLow (ε * a) a < eta :=
    (tendsto_order.1 henv).2 eta heta
  have ha0 : ∀ᶠ a : ℝ in atTop, 0 ≤ a := eventually_ge_atTop 0
  have halog3 :
      ∀ᶠ a : ℝ in atTop, Real.log 3 ≤ a :=
    eventually_ge_atTop (Real.log 3)
  have haEight :
      ∀ᶠ a : ℝ in atTop, Real.log 8 / gammaLow ≤ a :=
    eventually_ge_atTop (Real.log 8 / gammaLow)
  filter_upwards [henvlt, ha0, halog3, haEight] with
      a henvA ha0A halog3A haEightA
  have hlogEight : Real.log 8 ≤ gammaLow * a := by
    simpa [mul_comm] using (div_le_iff₀ hgamma).mp haEightA
  have hA : 8 ≤ Real.exp (gammaLow * a) := by
    calc
      8 = Real.exp (Real.log 8) :=
        (Real.exp_log (by norm_num : (0 : ℝ) < 8)).symm
      _ ≤ Real.exp (gammaLow * a) := Real.exp_le_exp.mpr hlogEight
  rcases hselect (Real.exp (gammaLow * a)) hA with
    ⟨Tlow, hT, hgood, hraw⟩
  refine ⟨Tlow, hT, hgood, ?_⟩
  intro y hy
  have hylog3 : Real.log 3 ≤ y := halog3A.trans hy.1
  have hy' : y ∈ Set.Icc a (a + ε * a) := by
    constructor
    · exact hy.1
    · calc
        y ≤ (1 + ε) * a := hy.2
        _ = a + ε * a := by ring
  have hx : 3 ≤ Real.exp y := by
    calc
      3 = Real.exp (Real.log 3) :=
        (Real.exp_log (by norm_num : (0 : ℝ) < 3)).symm
      _ ≤ Real.exp y := Real.exp_le_exp.mpr hylog3
  have hrawY := hraw (Real.exp y) hx
  simp only [Real.log_exp] at hrawY
  have hle :=
    normalized_real_powerHeight_remainder_le_envelope
      hC hD hbeta hbeta1 hgamma
      (mul_nonneg hε.le ha0A) ha0A hA hT hy' hrawY
  exact hle.trans_lt henvA

end ExplicitFormulaResidues
end PrimeNumberTheorem
