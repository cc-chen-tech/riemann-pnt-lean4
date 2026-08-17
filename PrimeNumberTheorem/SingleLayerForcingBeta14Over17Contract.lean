import PrimeNumberTheorem.SingleLayerForcingBeta14Over17
import PrimeNumberTheorem.ZeroDensityAmplificationAudit

/-!
# Single-layer forcing: contract interfaces for the cubic tail line

Two ready-made discharge targets for
`actual-cubic-two-height-l2-tail`:

1. **Count form** — `SingleLayerForcingCertificate β lam`: the coherent
   F_R/F_L budget in counting form,

       N(2/3, X^(λ(1-β))) ≥ c · X^(2λ(β-2/3) − λ(1-β)·(8/9)) · (log X)^(-k)

   closing `no_nontrivial_zero_re_gt_14_over_17_of_certificates`.

2. **Window-family form** — matching the existing gap-family machinery
   (`actualDynamicCarlsonGapFamily`, the two-height window mass): a lower
   bound

       c · (T+H)^e · (log(T+H))^(-k) ≤ disjointWindowFamilyLowerCount … σ H T

   with the exponent gap `4σ(1-σ) < e` is converted here into the gap
   `Tendsto` required by the already-proved
   `disjointWindowFamily_carlson_contradiction`, absorbing the
   `(log(T+H))^(-k)` deficit into the power gap (via
   `isLittleO_log_rpow_rpow_atTop`).

Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PrimeNumberTheorem

open Filter
open scoped BigOperators

/-- The coherent-forcing certificate for one seed real part `β` and window
exponent `lam`: an eventual lower bound for the right-half-plane zero count
at `σ = 2/3` up to height `X^(lam(1-β))` in the forced exponent. -/
structure SingleLayerForcingCertificate (β lam : ℝ) where
  c : ℝ
  k : ℝ
  c_pos : 0 < c
  k_pos : 0 < k
  lower : ∀ᶠ X in atTop,
    c * X ^ (2 * lam * (β - 2 / 3) - lam * (1 - β) * (4 * (2 / 3 : ℝ) * (1 - (2 / 3 : ℝ)))) *
        (Real.log X) ^ (-k) ≤
      (ZeroDensity.zeroDensityCount (2 / 3 : ℝ) (X ^ (lam * (1 - β))) : ℝ)

/-- Terminal closure through the certificate interface. -/
theorem no_nontrivial_zero_re_gt_14_over_17_of_certificates
    (hcert : ∀ β lam : ℝ, (14 / 17 : ℝ) < β → β < 1 → 0 < lam →
      SingleLayerForcingCertificate β lam) :
    ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → ρ.re ≤ (14 / 17 : ℝ) := by
  refine no_nontrivial_zero_re_gt_14_over_17_of_forcing ?_
  intro β lam hβ hβ1 hlam
  rcases hcert β lam hβ hβ1 hlam with ⟨c, k, hc, hk, hlow⟩
  exact ⟨c, k, hc, hk, hlow⟩

/-- A logarithmic deficit `(log x)^(-k)` dominates `x^(-ε)` eventually
(`k ≥ 0`, `ε > 0`): the deficit is absorbed into any positive power gap. -/
theorem eventually_log_rpow_neg_ge_rpow_neg
    {k ε : ℝ} (hk : 0 ≤ k) (hε : 0 < ε) :
    ∀ᶠ x in atTop, (Real.log x) ^ (-k) ≥ x ^ (-ε) := by
  have hlogk : ∀ᶠ x in atTop, (Real.log x) ^ k ≤ x ^ ε := by
    have hb := (isLittleO_log_rpow_rpow_atTop (r := k) (s := ε) hε).bound
      (by norm_num : 0 < (1 : ℝ))
    filter_upwards [hb, Filter.eventually_ge_atTop (1 : ℝ)] with x hbx hx1
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    have hxε : 0 ≤ x ^ ε := Real.rpow_nonneg hxpos.le ε
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog0 k),
      abs_of_nonneg hxε, one_mul] using hbx
  filter_upwards [hlogk, Filter.eventually_ge_atTop (Real.exp 1)] with x hlogkx hxe
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
  have hlogpos : 0 < Real.log x := by
    have hle : Real.log (Real.exp 1) ≤ Real.log x :=
      Real.log_le_log (Real.exp_pos 1) hxe
    exact lt_of_lt_of_le zero_lt_one (by simpa [Real.log_exp] using hle)
  have hxεpos : 0 < x ^ ε := Real.rpow_pos_of_pos hxpos ε
  have hlogkpos : 0 < (Real.log x) ^ k := Real.rpow_pos_of_pos hlogpos k
  have hinv : (x ^ ε)⁻¹ ≤ ((Real.log x) ^ k)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hlogkpos hlogkx
  have hneg : (Real.log x) ^ (-k) = ((Real.log x) ^ k)⁻¹ := Real.rpow_neg hlogpos.le k
  have hnegx : x ^ (-ε) = (x ^ ε)⁻¹ := Real.rpow_neg hxpos.le ε
  rw [hneg, hnegx]
  exact hinv

/-- The window-family gap: a lower bound `c·(T+H)^e·(log(T+H))^(-k)` for the
certified window count with the exponent gap `4σ(1-σ) < e` produces the
divergent gap against the Carlson majorant. -/
theorem singleLayerWindowForcing_tendsto_gap
    {ι ρ : Type*} [DecidableEq ι] [DecidableEq ρ]
    (windows : ℝ → Finset ι) (cluster : ι → Finset ρ)
    (windowStart : ι → ℝ) (realPart ordinate : ρ → ℝ)
    (σ H c k e : ℝ) (hCarlson : CarlsonEventualMajorant σ)
    (hσ : 0 < σ) (hσ1 : σ < 1) (hH : 0 ≤ H) (hc : 0 < c) (hk : 0 ≤ k)
    (hforcingWindow : ∀ᶠ T in atTop,
      c * (T + H) ^ e * (Real.log (T + H)) ^ (-k) ≤
        disjointWindowFamilyLowerCount windows cluster windowStart realPart ordinate σ H T)
    (hgapExp : 4 * σ * (1 - σ) < e) :
    Filter.Tendsto
      (fun T =>
        disjointWindowFamilyLowerCount windows cluster windowStart realPart ordinate σ H T -
          (hCarlson.C * ‖(T + H) ^ (4 * σ * (1 - σ)) * (Real.log (T + H)) ^ 4‖))
      Filter.atTop Filter.atTop := by
  let q : ℝ := 4 * σ * (1 - σ)
  let ε : ℝ := (e - q) / 2
  have hε : 0 < ε := by
    dsimp [ε, q]
    exact div_pos (sub_pos.mpr hgapExp) (by norm_num : 0 < (2 : ℝ))
  have hqexp : q < e - ε := by
    dsimp [ε, q]
    linarith [hgapExp]
  have hlog_abs : ∀ᶠ T in atTop, (Real.log (T + H)) ^ (-k) ≥ (T + H) ^ (-ε) := by
    have htend : Filter.Tendsto (fun T : ℝ => T + H) atTop atTop :=
      tendsto_atTop_add_const_right atTop H tendsto_id
    exact htend.eventually (eventually_log_rpow_neg_ge_rpow_neg hk hε)
  have hdom : ∀ᶠ T in atTop,
      c * T ^ (e - ε) - hCarlson.C * ‖(T + H) ^ q * (Real.log (T + H)) ^ 4‖ ≤
        disjointWindowFamilyLowerCount windows cluster windowStart realPart ordinate σ H T -
          (hCarlson.C * ‖(T + H) ^ q * (Real.log (T + H)) ^ 4‖) := by
    filter_upwards [hforcingWindow, hlog_abs, Filter.eventually_ge_atTop (1 : ℝ)] with
      T hlow hlogabs hT1
    have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT1
    have hTH : T ≤ T + H := le_add_of_nonneg_right hH
    have hTHpos : 0 < T + H := lt_of_lt_of_le hTpos hTH
    have hmid : c * (T + H) ^ e * (Real.log (T + H)) ^ (-k) ≥ c * (T + H) ^ (e - ε) := by
      have hmul : (T + H) ^ e * (Real.log (T + H)) ^ (-k) ≥
          (T + H) ^ e * (T + H) ^ (-ε) :=
        mul_le_mul_of_nonneg_left hlogabs (Real.rpow_nonneg hTHpos.le e)
      have hpow : (T + H) ^ e * (T + H) ^ (-ε) = (T + H) ^ (e - ε) := by
        have hsum : e + -ε = e - ε := by ring
        rw [← Real.rpow_add hTHpos, hsum]
      have h1 : (T + H) ^ e * (Real.log (T + H)) ^ (-k) ≥ (T + H) ^ (e - ε) := by
        rwa [hpow] at hmul
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left h1 hc.le
    have hq0 : 0 ≤ q := by
      dsimp [q]
      exact mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (4 : ℝ)) hσ.le) (sub_nonneg.mpr hσ1.le)
    have hT_pow : (T + H) ^ (e - ε) ≥ T ^ (e - ε) := by
      exact Real.rpow_le_rpow (le_of_lt hTpos) hTH
        (by dsimp [ε]; linarith [hq0, hgapExp] : 0 ≤ e - ε)
    have hmid2 : c * T ^ (e - ε) ≤ c * (T + H) ^ (e - ε) :=
      mul_le_mul_of_nonneg_left hT_pow hc.le
    have hchain : c * T ^ (e - ε) ≤
        disjointWindowFamilyLowerCount windows cluster windowStart realPart ordinate σ H T :=
      le_trans hmid2 (le_trans hmid hlow)
    exact sub_le_sub_right hchain _
  have hbase : Filter.Tendsto
      (fun T : ℝ => c * T ^ (e - ε) -
        hCarlson.C * ‖(T + H) ^ q * (Real.log (T + H)) ^ 4‖)
      atTop atTop := by
    have hC' : 0 ≤ hCarlson.C / c := div_nonneg (by exact_mod_cast hCarlson.C_nonneg) hc.le
    have hmain := ExceptionalZeroAmplificationGate.tendsto_powerGrowth_sub_carlsonMajorant_atTop
      (σ := σ) (C := hCarlson.C / c) (H := H) (qexp := e - ε) hσ hσ1 hC' hH
      (by dsimp [q] at hqexp ⊢; exact hqexp)
    have hscaled : Filter.Tendsto (fun T : ℝ => c * (T ^ (e - ε) -
        (hCarlson.C / c) * ‖(T + H) ^ q * (Real.log (T + H)) ^ 4‖)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hc hmain
    have hconv' : (fun T : ℝ => c * (T ^ (e - ε) -
        (hCarlson.C / c) * ‖(T + H) ^ q * (Real.log (T + H)) ^ 4‖)) =ᶠ[atTop]
        (fun T : ℝ => c * T ^ (e - ε) -
          hCarlson.C * ‖(T + H) ^ q * (Real.log (T + H)) ^ 4‖) := by
      filter_upwards with T
      field_simp [hc.ne']
    exact hscaled.congr' hconv'
  refine Filter.tendsto_atTop_mono' atTop hdom ?_
  simpa [q] using hbase

/-- The window-family single-layer contradiction: the certified window
count, forced below by `c·(T+H)^e·(log(T+H))^(-k)` with `4σ(1-σ) < e`,
contradicts the Carlson upper bound through the already-proved
`disjointWindowFamily_carlson_contradiction`. -/
theorem singleLayerWindowForcing_carlson_contradiction
    {ι ρ : Type*} [DecidableEq ι] [DecidableEq ρ]
    (windows : ℝ → Finset ι) (cluster : ι → Finset ρ)
    (windowStart : ι → ℝ) (realPart ordinate : ρ → ℝ)
    (σ H c k e : ℝ)
    (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (hH : 0 ≤ H) (hc : 0 < c) (hk : 0 ≤ k)
    (hlowerBridge : ∀ᶠ T in atTop,
      disjointWindowFamilyLowerCount windows cluster windowStart realPart ordinate σ H T ≤
        (ZeroDensity.zeroDensityCount σ (T + H) : ℝ))
    (hforcingWindow : ∀ᶠ T in atTop,
      c * (T + H) ^ e * (Real.log (T + H)) ^ (-k) ≤
        disjointWindowFamilyLowerCount windows cluster windowStart realPart ordinate σ H T)
    (hgapExp : 4 * σ * (1 - σ) < e) :
    False := by
  let hCarlson : CarlsonEventualMajorant σ :=
    Classical.choice (exists_carlsonEventualMajorant hσ hσ1)
  have hgap := singleLayerWindowForcing_tendsto_gap
    (windows := windows) (cluster := cluster) (windowStart := windowStart)
    (realPart := realPart) (ordinate := ordinate)
    (σ := σ) (H := H) (c := c) (k := k) (e := e) (hCarlson := hCarlson)
    (hσ := lt_trans (by norm_num : 0 < (1 / 2 : ℝ)) hσ) (hσ1 := hσ1) (hH := hH)
    (hc := hc) (hk := hk) (hforcingWindow := hforcingWindow) (hgapExp := hgapExp)
  exact disjointWindowFamily_carlson_contradiction
    (windows := windows) (cluster := cluster) (windowStart := windowStart)
    (realPart := realPart) (ordinate := ordinate) (sigma := σ) (H := H)
    (hCarlson := hCarlson) (hlower := hlowerBridge) (hgap := hgap)

end PrimeNumberTheorem
