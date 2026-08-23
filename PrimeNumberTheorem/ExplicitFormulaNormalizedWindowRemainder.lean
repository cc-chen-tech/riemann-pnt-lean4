import PrimeNumberTheorem.ExplicitFormulaUniformRealHeight

open Complex Filter Set Topology

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

open ExplicitFormulaAux

/-!
# Power-scale heights and normalized real-window remainders
-/

/-- A fixed quadratic factor is absorbed by every genuinely decaying
exponential on the logarithmic scale. -/
theorem tendsto_exp_mul_one_add_sq_atTop_nhds_zero_of_neg
    {c : ℝ} (hc : c < 0) :
    Tendsto (fun a : ℝ => Real.exp (c * a) * (1 + a) ^ 2)
      atTop (nhds 0) := by
  have hpow (k : ℕ) :
      Tendsto (fun a : ℝ => Real.exp (c * a) * a ^ k)
        atTop (nhds 0) := by
    have hsmall :=
      isLittleO_exp_mul_rpow_of_lt (k : ℝ)
        (a := c) (b := 0) hc
    have hratio := hsmall.tendsto_div_nhds_zero
    simpa [Real.rpow_natCast] using hratio
  have h2 := hpow 2
  have h1 := hpow 1
  have h0 := hpow 0
  have h1' :
      Tendsto
        (fun a : ℝ => 2 * (Real.exp (c * a) * a))
        atTop (nhds 0) := by
    simpa using h1.const_mul 2
  have hsum :
      Tendsto
        (fun a : ℝ =>
          Real.exp (c * a) * a ^ 2 +
            2 * (Real.exp (c * a) * a) +
            Real.exp (c * a))
        atTop (nhds 0) := by
    simpa only [pow_one, pow_zero, mul_one, zero_add, add_zero] using
      (h2.add h1').add h0
  convert hsum using 1
  funext a
  ring

/-- The common real-sample height may be selected on the power scale
`A = exp(a / 2)`.  The same selected height controls every logarithmic sample
`y` above `log 3`. -/
theorem
    exists_uniform_goodHeight_exp_half_norm_real_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ a : ℝ, 8 ≤ Real.exp (a / 2) →
        ∃ T ∈ Set.Icc (Real.exp (a / 2)) (Real.exp (a / 2) + 1),
          ExplicitFormulaAux.goodHeight T ∧
            ∀ y : ℝ, Real.log 3 ≤ y →
              ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
                  (chebyshevPsi0 (Real.exp y) : ℂ)‖ ≤
                C * Real.exp y *
                    ((1 + y) ^ 2 +
                      (1 + Real.log (Real.exp (a / 2) + 6)) ^ 2) / T +
                  (1 + D * T * (1 + Real.log (T + 6))) +
                  2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound +
                  y := by
  rcases
      exists_uniform_goodHeight_Icc_norm_real_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le
      with ⟨C, D, hC, hD, hselect⟩
  refine ⟨C, D, hC, hD, ?_⟩
  intro a ha
  rcases hselect (Real.exp (a / 2)) ha with
    ⟨T, hTmem, hgood, hreal⟩
  refine ⟨T, hTmem, hgood, ?_⟩
  intro y hy
  have hx : 3 ≤ Real.exp y := by
    calc
      3 = Real.exp (Real.log 3) :=
        (Real.exp_log (by norm_num : (0 : ℝ) < 3)).symm
      _ ≤ Real.exp y := Real.exp_le_exp.mpr hy
  simpa only [Real.log_exp] using hreal (Real.exp y) hx

/-- A deterministic upper envelope for the normalized approximation remainder
on the logarithmic window `[a, a + L]`, after selecting a height of size
`exp (a / 2)`. -/
noncomputable def normalizedWindowRemainderEnvelope
    (C D beta L a : ℝ) : ℝ :=
  C * Real.exp ((1 - beta) * L) *
      (Real.exp ((1 / 2 - beta) * a) *
        ((1 + a + L) ^ 2 + (2 + a) ^ 2)) +
    2 * D * Real.exp ((1 / 2 - beta) * a) * (2 + a) +
    Real.exp (-beta * a) *
      (1 + 2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound + a + L)

private theorem tendsto_exp_mul_quadratic_atTop_nhds_zero_of_neg
    {c u v w : ℝ} (hc : c < 0) :
    Tendsto
      (fun a : ℝ => Real.exp (c * a) * (u * a ^ 2 + v * a + w))
      atTop (nhds 0) := by
  have hpow (k : ℕ) :
      Tendsto (fun a : ℝ => Real.exp (c * a) * a ^ k)
        atTop (nhds 0) := by
    have hsmall :=
      isLittleO_exp_mul_rpow_of_lt (k : ℝ)
        (a := c) (b := 0) hc
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

/-- For every fixed window length, the deterministic remainder envelope tends
to zero once the normalization exponent is strictly between `1 / 2` and `1`.
-/
theorem tendsto_normalizedWindowRemainderEnvelope_atTop_nhds_zero
    {C D beta L : ℝ} (hbeta : 1 / 2 < beta) (hbeta1 : beta < 1) :
    Tendsto (normalizedWindowRemainderEnvelope C D beta L)
      atTop (nhds 0) := by
  have hc : 1 / 2 - beta < 0 := by linarith
  have hnbeta : -beta < 0 := by linarith
  have hfirst0 :
      Tendsto
        (fun a : ℝ =>
          Real.exp ((1 / 2 - beta) * a) *
            ((1 + a + L) ^ 2 + (2 + a) ^ 2))
        atTop (nhds 0) := by
    convert
      tendsto_exp_mul_quadratic_atTop_nhds_zero_of_neg
        (c := 1 / 2 - beta) (u := 2)
        (v := 2 * L + 6) (w := (1 + L) ^ 2 + 4) hc using 1
    funext a
    ring
  have hfirst :
      Tendsto
        (fun a : ℝ =>
          C * Real.exp ((1 - beta) * L) *
            (Real.exp ((1 / 2 - beta) * a) *
              ((1 + a + L) ^ 2 + (2 + a) ^ 2)))
        atTop (nhds 0) := by
    simpa using hfirst0.const_mul (C * Real.exp ((1 - beta) * L))
  have hsecond0 :
      Tendsto
        (fun a : ℝ =>
          Real.exp ((1 / 2 - beta) * a) * (2 + a))
        atTop (nhds 0) := by
    convert
      tendsto_exp_mul_quadratic_atTop_nhds_zero_of_neg
        (c := 1 / 2 - beta) (u := 0) (v := 1) (w := 2) hc using 1
    funext a
    ring
  have hsecond :
      Tendsto
        (fun a : ℝ =>
          2 * D * Real.exp ((1 / 2 - beta) * a) * (2 + a))
        atTop (nhds 0) := by
    have hmul :
        Tendsto
          (fun a : ℝ =>
            (2 * D) *
              (Real.exp ((1 / 2 - beta) * a) * (2 + a)))
          atTop (nhds 0) := by
      simpa using hsecond0.const_mul (2 * D)
    convert hmul using 1
    funext a
    ring
  have hthird :
      Tendsto
        (fun a : ℝ =>
          Real.exp (-beta * a) *
            (1 + 2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound + a + L))
        atTop (nhds 0) := by
    convert
      tendsto_exp_mul_quadratic_atTop_nhds_zero_of_neg
        (c := -beta) (u := 0) (v := 1)
        (w := 1 + 2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound + L)
        hnbeta using 1
    funext a
    ring
  change Tendsto (fun a : ℝ => normalizedWindowRemainderEnvelope C D beta L a)
    atTop (𝓝 0)
  simpa only [normalizedWindowRemainderEnvelope, zero_add] using
    (hfirst.add hsecond).add hthird

private theorem normalized_real_remainder_le_envelope
    {C D beta L a T y : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbeta : 1 / 2 < beta) (hbeta1 : beta < 1)
    (hL : 0 ≤ L) (ha0 : 0 ≤ a)
    (hA : 8 ≤ Real.exp (a / 2))
    (hT : T ∈ Set.Icc (Real.exp (a / 2)) (Real.exp (a / 2) + 1))
    (hy : y ∈ Set.Icc a (a + L))
    (hraw :
      ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
          (chebyshevPsi0 (Real.exp y) : ℂ)‖ ≤
        C * Real.exp y *
            ((1 + y) ^ 2 +
              (1 + Real.log (Real.exp (a / 2) + 6)) ^ 2) / T +
          (1 + D * T * (1 + Real.log (T + 6))) +
          2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound +
          y) :
    Real.exp (-beta * y) *
        ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
            (chebyshevPsi0 (Real.exp y) : ℂ)‖ ≤
      normalizedWindowRemainderEnvelope C D beta L a := by
  have hbeta0 : 0 < beta := by linarith
  have hOneBeta : 0 < 1 - beta := by linarith
  have hApos : 0 < Real.exp (a / 2) := Real.exp_pos _
  have hTpos : 0 < T := hApos.trans_le hT.1
  have hAplus : Real.exp (a / 2) + 6 ≤ 2 * Real.exp (a / 2) := by
    nlinarith
  have hTplus : T + 6 ≤ 2 * Real.exp (a / 2) := by
    nlinarith [hT.2, hA]
  have hlogTwo : Real.log 2 ≤ 1 := Real.log_two_lt_d9.le.trans (by norm_num)
  have hlogAplus :
      Real.log (Real.exp (a / 2) + 6) ≤ 1 + a / 2 := by
    calc
      Real.log (Real.exp (a / 2) + 6) ≤
          Real.log (2 * Real.exp (a / 2)) := by
        exact Real.log_le_log (by positivity) hAplus
      _ = Real.log 2 + a / 2 := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
          (ne_of_gt (Real.exp_pos (a / 2))), Real.log_exp]
      _ ≤ 1 + a / 2 := by linarith
  have hlogTplus :
      Real.log (T + 6) ≤ 1 + a / 2 := by
    calc
      Real.log (T + 6) ≤ Real.log (2 * Real.exp (a / 2)) := by
        exact Real.log_le_log (by positivity) hTplus
      _ = Real.log 2 + a / 2 := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
          (ne_of_gt (Real.exp_pos (a / 2))), Real.log_exp]
      _ ≤ 1 + a / 2 := by linarith
  have hlogAplus0 : 0 ≤ 1 + Real.log (Real.exp (a / 2) + 6) := by
    have : 1 ≤ Real.exp (a / 2) + 6 := by nlinarith
    have := Real.log_nonneg this
    linarith
  have hlogTplus0 : 0 ≤ 1 + Real.log (T + 6) := by
    have : 1 ≤ T + 6 := by linarith
    have := Real.log_nonneg this
    linarith
  have hAquad :
      (1 + Real.log (Real.exp (a / 2) + 6)) ^ 2 ≤ (2 + a) ^ 2 := by
    have huv :
        1 + Real.log (Real.exp (a / 2) + 6) ≤ 2 + a := by
      linarith
    nlinarith
  have hyone0 : 0 ≤ 1 + y := by linarith [hy.1]
  have hayL0 : 0 ≤ 1 + a + L := by linarith
  have hyquad : (1 + y) ^ 2 ≤ (1 + a + L) ^ 2 := by
    have huv : 1 + y ≤ 1 + a + L := by linarith [hy.2]
    nlinarith
  have hpoly :
      (1 + y) ^ 2 +
          (1 + Real.log (Real.exp (a / 2) + 6)) ^ 2 ≤
        (1 + a + L) ^ 2 + (2 + a) ^ 2 := by
    linarith
  have hTinv : 1 / T ≤ Real.exp (-a / 2) := by
    calc
      1 / T ≤ 1 / Real.exp (a / 2) :=
        one_div_le_one_div_of_le hApos hT.1
      _ = Real.exp (-a / 2) := by
        rw [one_div, ← Real.exp_neg]
        congr 2
        ring
  have hTupper : T ≤ 2 * Real.exp (a / 2) := by
    nlinarith [hT.2, hA]
  have hlogFactor :
      1 + Real.log (T + 6) ≤ 2 + a := by
    linarith
  have hnormMon :
      Real.exp (-beta * y) *
          ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
              (chebyshevPsi0 (Real.exp y) : ℂ)‖ ≤
        Real.exp (-beta * y) *
          (C * Real.exp y *
              ((1 + y) ^ 2 +
                (1 + Real.log (Real.exp (a / 2) + 6)) ^ 2) / T +
            (1 + D * T * (1 + Real.log (T + 6))) +
            2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound +
            y) :=
    mul_le_mul_of_nonneg_left hraw (Real.exp_pos _).le
  have hfirst :
      Real.exp (-beta * y) *
          (C * Real.exp y *
            ((1 + y) ^ 2 +
              (1 + Real.log (Real.exp (a / 2) + 6)) ^ 2) / T) ≤
        C * Real.exp ((1 - beta) * L) *
          (Real.exp ((1 / 2 - beta) * a) *
            ((1 + a + L) ^ 2 + (2 + a) ^ 2)) := by
    have hexpy :
        Real.exp ((1 - beta) * y) ≤
          Real.exp ((1 - beta) * (a + L)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hy.2 hOneBeta.le)
    have hpoly0 :
        0 ≤ (1 + y) ^ 2 +
          (1 + Real.log (Real.exp (a / 2) + 6)) ^ 2 := by positivity
    have hexpCombine :
        Real.exp (-beta * y) * Real.exp y =
          Real.exp ((1 - beta) * y) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hexpWindowCombine :
        Real.exp ((1 - beta) * (a + L)) * Real.exp (-a / 2) =
          Real.exp ((1 - beta) * L) *
            Real.exp ((1 / 2 - beta) * a) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [div_eq_mul_inv]
    calc
      Real.exp (-beta * y) *
          (C * Real.exp y *
            ((1 + y) ^ 2 +
              (1 + Real.log (Real.exp (a / 2) + 6)) ^ 2) * T⁻¹) =
          C * (Real.exp (-beta * y) * Real.exp y) *
            ((1 + y) ^ 2 +
              (1 + Real.log (Real.exp (a / 2) + 6)) ^ 2) * (1 / T) := by
        ring
      _ = C * Real.exp ((1 - beta) * y) *
            ((1 + y) ^ 2 +
              (1 + Real.log (Real.exp (a / 2) + 6)) ^ 2) * (1 / T) := by
        rw [hexpCombine]
      _ ≤ C * Real.exp ((1 - beta) * (a + L)) *
            ((1 + a + L) ^ 2 + (2 + a) ^ 2) *
            Real.exp (-a / 2) := by
        gcongr
      _ = C *
            (Real.exp ((1 - beta) * (a + L)) * Real.exp (-a / 2)) *
              ((1 + a + L) ^ 2 + (2 + a) ^ 2) := by ring
      _ = C * Real.exp ((1 - beta) * L) *
            (Real.exp ((1 / 2 - beta) * a) *
              ((1 + a + L) ^ 2 + (2 + a) ^ 2)) := by
        rw [hexpWindowCombine]
        ring
  have hsecond :
      Real.exp (-beta * y) *
          (1 + D * T * (1 + Real.log (T + 6))) ≤
        Real.exp (-beta * a) +
          2 * D * Real.exp ((1 / 2 - beta) * a) * (2 + a) := by
    have hnormexp :
        Real.exp (-beta * y) ≤ Real.exp (-beta * a) := by
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hy.1 (by linarith))
    have hprod :
        D * T * (1 + Real.log (T + 6)) ≤
          2 * D * Real.exp (a / 2) * (2 + a) := by
      calc
        D * T * (1 + Real.log (T + 6)) ≤
            D * (2 * Real.exp (a / 2)) * (2 + a) := by
          gcongr
        _ = 2 * D * Real.exp (a / 2) * (2 + a) := by ring
    have hexpCombine :
        Real.exp (-beta * a) * Real.exp (a / 2) =
          Real.exp ((1 / 2 - beta) * a) := by
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
              (2 * D * Real.exp (a / 2) * (2 + a)) := by
        gcongr
      _ = Real.exp (-beta * a) +
            2 * D * Real.exp ((1 / 2 - beta) * a) * (2 + a) := by
        rw [show
          Real.exp (-beta * a) *
              (2 * D * Real.exp (a / 2) * (2 + a)) =
            2 * D *
              (Real.exp (-beta * a) * Real.exp (a / 2)) *
                (2 + a) by ring]
        rw [hexpCombine]
  have hclosed :
      Real.exp (-beta * y) *
          (2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound + y) ≤
        Real.exp (-beta * a) *
          (2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound + a + L) := by
    have hnormexp :
        Real.exp (-beta * y) ≤ Real.exp (-beta * a) := by
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hy.1 (by linarith))
    have hclosed0 :
        0 ≤ 2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound + y := by
      have hz :=
        VKEdgePiOverTwo.zero_lt_zeroPackageClosedTermsUniformBound
      linarith [hy.1]
    have hclosedLe :
        2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound + y ≤
          2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound + a + L := by
      linarith [hy.2]
    gcongr
  rw [normalizedWindowRemainderEnvelope]
  calc
    Real.exp (-beta * y) *
        ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
            (chebyshevPsi0 (Real.exp y) : ℂ)‖ ≤ _ := hnormMon
    _ = Real.exp (-beta * y) *
          (C * Real.exp y *
            ((1 + y) ^ 2 +
              (1 + Real.log (Real.exp (a / 2) + 6)) ^ 2) / T) +
        Real.exp (-beta * y) *
          (1 + D * T * (1 + Real.log (T + 6))) +
        Real.exp (-beta * y) *
          (2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound + y) := by
      ring
    _ ≤
        C * Real.exp ((1 - beta) * L) *
            (Real.exp ((1 / 2 - beta) * a) *
              ((1 + a + L) ^ 2 + (2 + a) ^ 2)) +
          (Real.exp (-beta * a) +
            2 * D * Real.exp ((1 / 2 - beta) * a) * (2 + a)) +
          Real.exp (-beta * a) *
            (2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound + a + L) := by
      gcongr
    _ = _ := by ring

/-- On every fixed logarithmic window `[a, a + L]`, a single good height of
size `exp (a / 2)` makes the finite-height explicit-formula approximation
uniformly `o(exp (beta * y))` for each `1 / 2 < beta < 1`.

This theorem controls the finite-height approximation remainder.  It does not
bound the complementary zero package in a zero-cluster argument. -/
theorem eventually_exists_uniform_goodHeight_normalized_window_remainder_lt
    {beta L eta : ℝ}
    (hbeta : 1 / 2 < beta) (hbeta1 : beta < 1)
    (hL : 0 ≤ L) (heta : 0 < eta) :
    ∀ᶠ a in atTop,
      ∃ T ∈ Set.Icc (Real.exp (a / 2)) (Real.exp (a / 2) + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ y ∈ Set.Icc a (a + L),
            Real.exp (-beta * y) *
                ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
                    (chebyshevPsi0 (Real.exp y) : ℂ)‖ < eta := by
  rcases
      exists_uniform_goodHeight_exp_half_norm_real_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le
      with ⟨C, D, hC, hD, hselect⟩
  have henv :
      Tendsto (normalizedWindowRemainderEnvelope C D beta L)
        atTop (nhds 0) :=
    tendsto_normalizedWindowRemainderEnvelope_atTop_nhds_zero hbeta hbeta1
  have henvlt :
      ∀ᶠ a in atTop, normalizedWindowRemainderEnvelope C D beta L a < eta :=
    (tendsto_order.1 henv).2 eta heta
  have ha0 : ∀ᶠ a : ℝ in atTop, 0 ≤ a := eventually_ge_atTop 0
  have halog3 :
      ∀ᶠ a : ℝ in atTop, Real.log 3 ≤ a :=
    eventually_ge_atTop (Real.log 3)
  have haEight :
      ∀ᶠ a : ℝ in atTop, 2 * Real.log 8 ≤ a :=
    eventually_ge_atTop (2 * Real.log 8)
  filter_upwards [henvlt, ha0, halog3, haEight] with a henvA ha0A halog3A haEightA
  have hA : 8 ≤ Real.exp (a / 2) := by
    calc
      8 = Real.exp (Real.log 8) :=
        (Real.exp_log (by norm_num : (0 : ℝ) < 8)).symm
      _ ≤ Real.exp (a / 2) := by
        apply Real.exp_le_exp.mpr
        linarith
  rcases hselect a hA with ⟨T, hT, hgood, hraw⟩
  refine ⟨T, hT, hgood, ?_⟩
  intro y hy
  have hylog3 : Real.log 3 ≤ y := halog3A.trans hy.1
  have hle :=
    normalized_real_remainder_le_envelope
      hC hD hbeta hbeta1 hL ha0A hA hT hy (hraw y hylog3)
  exact hle.trans_lt henvA

/-- The normalized explicit-formula remainder envelope still tends to zero
when the logarithmic window length grows proportionally to its left endpoint,
provided the normalization gain `beta - 1 / 2` dominates the window-growth
loss `(1 - beta) * ε`. -/
theorem
    tendsto_normalizedWindowRemainderEnvelope_proportional_atTop_nhds_zero
    {C D beta ε : ℝ}
    (hbeta : 1 / 2 < beta)
    (hbeta1 : beta < 1)
    (hdecay : (1 - beta) * ε < beta - 1 / 2) :
    Tendsto
      (fun a =>
        normalizedWindowRemainderEnvelope C D beta (ε * a) a)
      atTop (nhds 0) := by
  let c : ℝ := (1 / 2 - beta) + (1 - beta) * ε
  have hc : c < 0 := by
    dsimp [c]
    linarith
  have hfirst0 :
      Tendsto
        (fun a : ℝ =>
          Real.exp (c * a) *
            ((1 + a + ε * a) ^ 2 + (2 + a) ^ 2))
        atTop (nhds 0) := by
    convert
      tendsto_exp_mul_quadratic_atTop_nhds_zero_of_neg
        (c := c) (u := (1 + ε) ^ 2 + 1)
        (v := 2 * ε + 6) (w := 5) hc using 1
    funext a
    ring
  have hfirst :
      Tendsto
        (fun a : ℝ =>
          C * Real.exp ((1 - beta) * (ε * a)) *
            (Real.exp ((1 / 2 - beta) * a) *
              ((1 + a + ε * a) ^ 2 + (2 + a) ^ 2)))
        atTop (nhds 0) := by
    have hmul :
        Tendsto
          (fun a : ℝ =>
            C *
              (Real.exp (c * a) *
                ((1 + a + ε * a) ^ 2 + (2 + a) ^ 2)))
          atTop (nhds 0) := by
      simpa using hfirst0.const_mul C
    convert hmul using 1
    funext a
    have hexp :
        Real.exp ((1 - beta) * (ε * a)) *
            Real.exp ((1 / 2 - beta) * a) =
          Real.exp (c * a) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [c]
      ring
    rw [show
        C * Real.exp ((1 - beta) * (ε * a)) *
              (Real.exp ((1 / 2 - beta) * a) *
                ((1 + a + ε * a) ^ 2 + (2 + a) ^ 2)) =
            C *
              (Real.exp ((1 - beta) * (ε * a)) *
                Real.exp ((1 / 2 - beta) * a)) *
              ((1 + a + ε * a) ^ 2 + (2 + a) ^ 2) by
          ring,
      hexp]
    ring
  have hhalf : 1 / 2 - beta < 0 := by linarith
  have hsecond0 :
      Tendsto
        (fun a : ℝ =>
          Real.exp ((1 / 2 - beta) * a) * (2 + a))
        atTop (nhds 0) := by
    convert
      tendsto_exp_mul_quadratic_atTop_nhds_zero_of_neg
        (c := 1 / 2 - beta) (u := 0) (v := 1) (w := 2)
        hhalf using 1
    funext a
    ring
  have hsecond :
      Tendsto
        (fun a : ℝ =>
          2 * D * Real.exp ((1 / 2 - beta) * a) * (2 + a))
        atTop (nhds 0) := by
    have hmul :
        Tendsto
          (fun a : ℝ =>
            (2 * D) *
              (Real.exp ((1 / 2 - beta) * a) * (2 + a)))
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
      tendsto_exp_mul_quadratic_atTop_nhds_zero_of_neg
        (c := -beta) (u := 0) (v := 1 + ε)
        (w :=
          1 + 2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound)
        hbetaNeg using 1
    funext a
    ring
  simpa only [normalizedWindowRemainderEnvelope, zero_add] using
    (hfirst.add hsecond).add hthird

/-- On every sufficiently late proportional logarithmic window
`[a, (1 + ε) * a]`, one good height of size `exp (a / 2)` makes the
finite-height explicit-formula approximation uniformly small, whenever the
normalization gain dominates the proportional-window growth loss. -/
theorem
    eventually_exists_uniform_goodHeight_normalized_proportional_window_remainder_lt
    {beta ε eta : ℝ}
    (hbeta : 1 / 2 < beta)
    (hbeta1 : beta < 1)
    (hε : 0 < ε)
    (hdecay : (1 - beta) * ε < beta - 1 / 2)
    (heta : 0 < eta) :
    ∀ᶠ a : ℝ in atTop,
      ∃ T ∈ Set.Icc (Real.exp (a / 2)) (Real.exp (a / 2) + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ y ∈ Set.Icc a ((1 + ε) * a),
            Real.exp (-beta * y) *
                ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
                  (chebyshevPsi0 (Real.exp y) : ℂ)‖ < eta := by
  rcases
      exists_uniform_goodHeight_exp_half_norm_real_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le
      with ⟨C, D, hC, hD, hselect⟩
  have henv :
      Tendsto
        (fun a =>
          normalizedWindowRemainderEnvelope C D beta (ε * a) a)
        atTop (nhds 0) :=
    tendsto_normalizedWindowRemainderEnvelope_proportional_atTop_nhds_zero
      hbeta hbeta1 hdecay
  have henvlt :
      ∀ᶠ a in atTop,
        normalizedWindowRemainderEnvelope C D beta (ε * a) a < eta :=
    (tendsto_order.1 henv).2 eta heta
  have ha0 : ∀ᶠ a : ℝ in atTop, 0 ≤ a := eventually_ge_atTop 0
  have halog3 :
      ∀ᶠ a : ℝ in atTop, Real.log 3 ≤ a :=
    eventually_ge_atTop (Real.log 3)
  have haEight :
      ∀ᶠ a : ℝ in atTop, 2 * Real.log 8 ≤ a :=
    eventually_ge_atTop (2 * Real.log 8)
  filter_upwards [henvlt, ha0, halog3, haEight] with
      a henvA ha0A halog3A haEightA
  have hA : 8 ≤ Real.exp (a / 2) := by
    calc
      8 = Real.exp (Real.log 8) :=
        (Real.exp_log (by norm_num : (0 : ℝ) < 8)).symm
      _ ≤ Real.exp (a / 2) := by
        apply Real.exp_le_exp.mpr
        linarith
  rcases hselect a hA with ⟨T, hT, hgood, hraw⟩
  refine ⟨T, hT, hgood, ?_⟩
  intro y hy
  have hylog3 : Real.log 3 ≤ y := halog3A.trans hy.1
  have hy' : y ∈ Set.Icc a (a + ε * a) := by
    constructor
    · exact hy.1
    · convert hy.2 using 1 <;> ring
  have hle :=
    normalized_real_remainder_le_envelope
      hC hD hbeta hbeta1 (mul_nonneg hε.le ha0A) ha0A hA hT
      hy' (hraw y hylog3)
  exact hle.trans_lt henvA

end ExplicitFormulaResidues
end PrimeNumberTheorem
