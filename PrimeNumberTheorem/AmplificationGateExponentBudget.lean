import Mathlib

/-!
# Gate input 6 (`hgap`): the exponent budget

Self-contained proof that the power growth `T^qexp` eventually beats the
Carlson-shaped majorant

    C (T+H)^(4σ(1-σ)) (log(T+H))^4

whenever `4σ(1-σ) < qexp` (with `qexp` standing for the total growth
exponent of `q(T)^depth`, e.g. `h'·depth` with `q(T) = T^(h')`).

This is the analytic content of the gate's `hgap` input in
`ExceptionalZeroAmplificationGateContract.amplificationGate`; the
instantiation `q T = ⌊T^h'⌋`, `localContribution = 1`, `depth` with
`h'·depth > 4σ(1-σ)` supplies the hypotheses.  The log power is absorbed
by the subpolynomial estimate `(log x)^4 = o(x^(4ε))`
(`isLittleO_log_rpow_rpow_atTop`).
-/

namespace PrimeNumberTheorem
namespace ExceptionalZeroAmplificationGate

open Filter

/-- The exponent budget: `T^qexp − C (T+H)^(4σ(1-σ)) (log(T+H))^4 → ∞`
whenever `4σ(1-σ) < qexp`. -/
theorem tendsto_powerGrowth_sub_carlsonMajorant_atTop
    {σ C H qexp : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hqexp : 4 * σ * (1 - σ) < qexp) :
    Filter.Tendsto
      (fun T : ℝ => T ^ qexp - C * ‖(T + H) ^ (4 * σ * (1 - σ)) * (Real.log (T + H)) ^ 4‖)
      atTop atTop := by
  let b : ℝ := 4 * σ * (1 - σ)
  let ε : ℝ := (qexp - b) / 8
  have hb_nonneg : 0 ≤ b := by
    dsimp [b]
    exact mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (4 : ℝ)) hσ.le)
      (sub_nonneg.mpr hσ1.le)
  have hqpos : 0 < qexp := lt_of_le_of_lt hb_nonneg hqexp
  have hε : 0 < ε := by
    dsimp [ε, b]
    exact div_pos (sub_pos.mpr hqexp) (by norm_num : 0 < (8 : ℝ))
  have h4ε : 0 < 4 * ε := mul_pos (by norm_num) hε
  -- subpolynomial: (log x)^4 ≤ x^(4ε) eventually (uniform constant 1)
  have hlog : ∀ᶠ x in atTop, ‖(Real.log x) ^ 4‖ ≤ ‖x ^ (4 * ε)‖ := by
    have hb := (isLittleO_log_rpow_rpow_atTop (r := 4) (s := 4 * ε) h4ε).bound
      (by norm_num : 0 < (1 : ℝ))
    exact hb.mono (fun x hx => by simp [one_mul] at hx ⊢; exact hx)
  have hlog' : ∀ᶠ T in atTop, ‖(Real.log (T + H)) ^ 4‖ ≤ ‖(T + H) ^ (4 * ε)‖ := by
    have hf : Filter.Tendsto (fun T : ℝ => T) atTop atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro a
      exact ⟨a, fun x hx => hx⟩
    exact (tendsto_atTop_add_const_right atTop H hf).eventually hlog
  have hbig : ∀ᶠ T in atTop,
      C * ‖(T + H) ^ b * (Real.log (T + H)) ^ 4‖ ≤ C * (T + H) ^ (b + 4 * ε) := by
    filter_upwards [hlog', Filter.eventually_ge_atTop (1 : ℝ),
        Filter.eventually_ge_atTop H] with T hlogT hT1 hTH
    have hpos : 0 < T + H := by linarith
    have hlog4 : ‖(Real.log (T + H)) ^ 4‖ = (Real.log (T + H)) ^ 4 := by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (pow_nonneg (Real.log_nonneg (by linarith : 1 ≤ T + H)) 4)]
    have hrpow : ‖(T + H) ^ (4 * ε)‖ = (T + H) ^ (4 * ε) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hpos.le (4 * ε))]
    have hb' : ‖(T + H) ^ b‖ = (T + H) ^ b := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hpos.le b)]
    have hA : ‖(T + H) ^ b * (Real.log (T + H)) ^ 4‖ ≤
        (T + H) ^ b * (Real.log (T + H)) ^ 4 := by
      have hnm : ‖(T + H) ^ b * (Real.log (T + H)) ^ 4‖ ≤
          ‖(T + H) ^ b‖ * ‖(Real.log (T + H)) ^ 4‖ := norm_mul_le _ _
      simp [hb', hlog4] at hnm ⊢
    have hB : (T + H) ^ b * (Real.log (T + H)) ^ 4 ≤
        (T + H) ^ b * (T + H) ^ (4 * ε) := by
      exact mul_le_mul_of_nonneg_left (by simpa [hlog4, hrpow] using hlogT)
        (Real.rpow_nonneg hpos.le b)
    have hC' : (T + H) ^ b * (T + H) ^ (4 * ε) = (T + H) ^ (b + 4 * ε) := by
      exact (Real.rpow_add hpos b (4 * ε)).symm
    calc
      C * ‖(T + H) ^ b * (Real.log (T + H)) ^ 4‖ ≤
          C * ((T + H) ^ b * (Real.log (T + H)) ^ 4) := by
        exact mul_le_mul_of_nonneg_left hA hC
      _ ≤ C * ((T + H) ^ b * (T + H) ^ (4 * ε)) := by
        exact mul_le_mul_of_nonneg_left hB hC
      _ = C * (T + H) ^ (b + 4 * ε) := by rw [hC']
  have hscale : ∀ᶠ T in atTop, (T + H) ^ (b + 4 * ε) ≤ (2 * T) ^ (b + 4 * ε) := by
    filter_upwards [Filter.eventually_ge_atTop H,
        Filter.eventually_ge_atTop (1 : ℝ)] with T hTH hT1
    have hpos : 0 < T + H := by linarith
    have hle : T + H ≤ 2 * T := by nlinarith
    exact Real.rpow_le_rpow hpos.le hle (add_nonneg hb_nonneg h4ε.le)
  have hsmall : ∀ᶠ T in atTop, C * (2 * T) ^ (b + 4 * ε) ≤ T ^ qexp / 2 := by
    have htend : Filter.Tendsto (fun T : ℝ => T ^ (4 * ε)) atTop atTop :=
      tendsto_rpow_atTop h4ε
    have hev : ∀ᶠ T in atTop, 2 * C * (2 : ℝ) ^ (b + 4 * ε) ≤ T ^ (4 * ε) :=
      htend.eventually (Filter.eventually_ge_atTop (2 * C * (2 : ℝ) ^ (b + 4 * ε)))
    filter_upwards [hev, Filter.eventually_ge_atTop (1 : ℝ)] with T hge hT1
    have hpos : 0 < T := lt_of_lt_of_le zero_lt_one hT1
    have hmul : (2 * T) ^ (b + 4 * ε) = (2 : ℝ) ^ (b + 4 * ε) * T ^ (b + 4 * ε) := by
      exact Real.mul_rpow (by norm_num : 0 ≤ (2 : ℝ)) hpos.le
    have hge' : C * (2 : ℝ) ^ (b + 4 * ε) ≤ T ^ (4 * ε) / 2 := by
      nlinarith [hge, hC]
    calc
      C * (2 * T) ^ (b + 4 * ε) = C * (2 : ℝ) ^ (b + 4 * ε) * T ^ (b + 4 * ε) := by
        rw [hmul]
        ring
      _ ≤ (T ^ (4 * ε) / 2) * T ^ (b + 4 * ε) := by
        exact mul_le_mul_of_nonneg_right hge' (Real.rpow_nonneg hpos.le (b + 4 * ε))
      _ = T ^ qexp / 2 := by
        have hp : T ^ (4 * ε) * T ^ (b + 4 * ε) = T ^ qexp := by
          rw [← Real.rpow_add hpos (4 * ε) (b + 4 * ε)]
          congr 1
          dsimp [ε, b]
          ring
        rw [show T ^ (4 * ε) / 2 * T ^ (b + 4 * ε) =
          (T ^ (4 * ε) * T ^ (b + 4 * ε)) / 2 by ring]
        rw [hp]
  have hdom : ∀ᶠ T in atTop,
      T ^ qexp / 2 ≤ T ^ qexp - C * ‖(T + H) ^ b * (Real.log (T + H)) ^ 4‖ := by
    filter_upwards [hbig, hscale, hsmall] with T hb1 hs1 hs2
    have h1 : C * ‖(T + H) ^ b * (Real.log (T + H)) ^ 4‖ ≤ C * (2 * T) ^ (b + 4 * ε) := by
      have hA : C * (T + H) ^ (b + 4 * ε) ≤ C * (2 * T) ^ (b + 4 * ε) := by
        exact mul_le_mul_of_nonneg_left hs1 hC
      linarith [hb1, hA]
    nlinarith [h1, hs2]
  refine Filter.tendsto_atTop_mono' atTop hdom ?_
  have h1 : Filter.Tendsto (fun T : ℝ => T ^ qexp) atTop atTop :=
    tendsto_rpow_atTop hqpos
  have h2 : Filter.Tendsto (fun T : ℝ => (1 / 2 : ℝ) * T ^ qexp) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num : 0 < (1 / 2 : ℝ)) h1
  simpa [div_eq_mul_inv, mul_comm] using h2

/-- Gate-shaped version: if the layer degree satisfies `T^h' ≤ q T`
eventually (e.g. `q T = ⌊T^h'⌋`) and `4σ(1-σ) < h'·depth`, then the gate's
`hgap` growth condition holds for any positive local contribution. -/
theorem tendsto_qPower_sub_carlsonMajorant_atTop
    {σ C H h' cl : ℝ} {q : ℝ → ℕ} {depth : ℕ}
    (hσ : 0 < σ) (hσ1 : σ < 1) (hC : 0 ≤ C) (hH : 0 ≤ H) (hcl : 0 < cl)
    (hq : ∀ᶠ T in atTop, T ^ h' ≤ (q T : ℝ))
    (hqexp : 4 * σ * (1 - σ) < h' * depth) :
    Filter.Tendsto
      (fun T : ℝ => cl * (q T ^ depth) -
        C * ‖(T + H) ^ (4 * σ * (1 - σ)) * (Real.log (T + H)) ^ 4‖)
      atTop atTop := by
  have hbmul : 0 ≤ 4 * σ * (1 - σ) := by
    exact mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (4 : ℝ)) hσ.le)
      (sub_nonneg.mpr hσ1.le)
  have hmulpos : 0 < h' * (depth : ℝ) := lt_of_le_of_lt hbmul hqexp
  have hhpos : 0 < h' := by
    by_contra h
    nlinarith [hmulpos, h, (by positivity : 0 ≤ (depth : ℝ))]
  have hdom : ∀ᶠ T in atTop,
      cl * T ^ (h' * depth) - C * ‖(T + H) ^ (4 * σ * (1 - σ)) * (Real.log (T + H)) ^ 4‖ ≤
        cl * (q T ^ depth) - C * ‖(T + H) ^ (4 * σ * (1 - σ)) * (Real.log (T + H)) ^ 4‖ := by
    filter_upwards [hq, Filter.eventually_ge_atTop (1 : ℝ)] with T hqT hT1
    have hpos : 0 < T := lt_of_lt_of_le zero_lt_one hT1
    have hpow : (T ^ h') ^ depth = T ^ (h' * depth) := by
      have h1 : (T ^ h') ^ (depth : ℕ) = (T ^ h') ^ ((depth : ℕ) : ℝ) := by
        exact (Real.rpow_natCast (T ^ h') depth).symm
      have h2 : (T ^ h') ^ ((depth : ℕ) : ℝ) = T ^ (h' * ((depth : ℕ) : ℝ)) := by
        rw [Real.rpow_mul hpos.le h' ((depth : ℕ) : ℝ)]
      have h3 : T ^ (h' * ((depth : ℕ) : ℝ)) = T ^ (h' * depth) := by
        norm_num
      exact h1.trans (h2.trans h3)
    have hqpow : T ^ (h' * depth) ≤ (q T : ℝ) ^ depth := by
      rw [← hpow]
      exact pow_le_pow_left₀ (Real.rpow_nonneg hpos.le h') hqT depth
    exact sub_le_sub_right (mul_le_mul_of_nonneg_left hqpow hcl.le) _
  have hbase : Filter.Tendsto
      (fun T : ℝ => cl * T ^ (h' * depth) -
        C * ‖(T + H) ^ (4 * σ * (1 - σ)) * (Real.log (T + H)) ^ 4‖)
      atTop atTop := by
    have hC' : 0 ≤ C / cl := div_nonneg hC hcl.le
    have hmain := tendsto_powerGrowth_sub_carlsonMajorant_atTop
      (σ := σ) (C := C / cl) (H := H) (qexp := h' * depth) hσ hσ1 hC' hH hqexp
    have hscaled : Filter.Tendsto (fun T : ℝ => cl * (T ^ (h' * depth) -
        (C / cl) * ‖(T + H) ^ (4 * σ * (1 - σ)) * (Real.log (T + H)) ^ 4‖))
        atTop atTop :=
      Filter.Tendsto.const_mul_atTop hcl hmain
    have hconv' : (fun T : ℝ => cl * (T ^ (h' * depth) -
        (C / cl) * ‖(T + H) ^ (4 * σ * (1 - σ)) * Real.log (T + H) ^ 4‖)) =ᶠ[atTop]
        (fun T : ℝ => cl * T ^ (h' * depth) -
          C * ‖(T + H) ^ (4 * σ * (1 - σ)) * Real.log (T + H) ^ 4‖) := by
      filter_upwards with T
      field_simp [hcl.ne']
    exact hscaled.congr' hconv'
  exact Filter.tendsto_atTop_mono' atTop hdom hbase

end ExceptionalZeroAmplificationGate
end PrimeNumberTheorem
