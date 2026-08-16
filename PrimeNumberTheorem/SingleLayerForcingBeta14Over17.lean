import PrimeNumberTheorem.ZeroDensityAmplificationAudit
import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlson
import PrimeNumberTheorem.AmplificationGateExponentBudget

/-!
# Single-layer forcing: the `β > 14/17` exclusion

The replacement route of `docs/research/single-layer-forcing-beta-14-17.md`
(the directed windowed detector is withdrawn, see
`docs/research/L3-defect-record.md`).  One layer of the coherent
window-energy forcing contradicts the Carlson density for seeds with
`Re ρ > 14/17`, with no directed iteration and no windowed detector.

The only analytic input is the *forcing lower count*: for every seed real
part `β > 14/17` and window exponent `lam > 0`, the coherent F_R/F_L budget
of the cubic design forces

    N(2/3, X^(lam(1-β))) ≥ c · X^(2lam(β-2/3) − lam(1-β)·(8/9)) · (log X)^(-k)

(eventually, with `c, k > 0`).  This is the deliverable of the cubic tail
line (`actual-cubic-two-height-l2-tail`).  Everything else — the exponent
gap `β > 14/17` arithmetic, the Carlson upper bound conversion to the
`X`-variable, the power-vs-polylog contradiction, and the terminal
exclusion — is proved in this module.

Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PrimeNumberTheorem

open Filter
open scoped BigOperators

/-- A power-gap inequality of the shape `A·X^d·(log X)^(-k) ≤ B·(log X)^4`
eventually (with `d > 0`) is impossible: the left side grows like `X^d`
modulo a logarithmic deficit while the right side is polylogarithmic. -/
theorem powerGrowth_logGap_contradiction
    {A B k d : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hk : 0 ≤ k) (hd : 0 < d)
    (hineq : ∀ᶠ X in atTop, A * X ^ d * (Real.log X) ^ (-k) ≤ B * (Real.log X) ^ 4) :
    False := by
  have hlog : ∀ᶠ X in atTop, (Real.log X) ^ (4 + k) ≤ X ^ (d / 2) := by
    have hb := (isLittleO_log_rpow_rpow_atTop (r := 4 + k) (s := d / 2)
        (by linarith : 0 < d / 2)).bound (by norm_num : 0 < (1 : ℝ))
    filter_upwards [hb, Filter.eventually_ge_atTop (1 : ℝ)] with X hbX hX1
    have hlog0 : 0 ≤ Real.log X := Real.log_nonneg hX1
    have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX1
    have hXd : 0 ≤ X ^ (d / 2) := Real.rpow_nonneg hXpos.le (d / 2)
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog0 (4 + k)),
      abs_of_nonneg hXd, one_mul] using hbX
  have hbound : ∀ᶠ X in atTop, X ≤ (B / A) ^ (2 / d) := by
    filter_upwards [hineq, hlog, Filter.eventually_ge_atTop (Real.exp 1)] with X hineqX hlogX hXe
    have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
    have hlogpos : 0 < Real.log X := by
      have hle : Real.log (Real.exp 1) ≤ Real.log X := by
        exact Real.log_le_log (Real.exp_pos 1) hXe
      exact lt_of_lt_of_le zero_lt_one (by simpa [Real.log_exp] using hle)
    have hlog0 : 0 ≤ Real.log X := le_of_lt hlogpos
    have hkpow : 0 ≤ (Real.log X) ^ k := Real.rpow_nonneg hlog0 k
    have hmul : A * X ^ d ≤ B * (Real.log X) ^ (4 + k) := by
      have h1 : A * X ^ d * (Real.log X) ^ (-k) * (Real.log X) ^ k ≤
          B * (Real.log X) ^ 4 * (Real.log X) ^ k :=
        mul_le_mul_of_nonneg_right hineqX hkpow
      have h2 : A * X ^ d * (Real.log X) ^ (-k) * (Real.log X) ^ k = A * X ^ d := by
        have hmid : (Real.log X) ^ (-k) * (Real.log X) ^ k = 1 := by
          rw [(Real.rpow_add hlogpos (-k) k).symm]
          have hzero : -k + k = 0 := by ring
          rw [hzero, Real.rpow_zero]
        rw [mul_assoc (A * X ^ d) (Real.log X ^ (-k)) (Real.log X ^ k)]
        simpa [hmid]
      have h3 : B * (Real.log X) ^ 4 * (Real.log X) ^ k = B * (Real.log X) ^ (4 + k) := by
        have hpowadd : (Real.log X) ^ 4 * (Real.log X) ^ k = (Real.log X) ^ (4 + k) :=
          Real.rpow_add hlogpos 4 k
        rw [mul_assoc B (Real.log X ^ 4) (Real.log X ^ k)]
        simpa [hpowadd]
      simpa [h2, h3] using h1
    have hupper : A * X ^ d ≤ B * X ^ (d / 2) :=
      le_trans hmul (mul_le_mul_of_nonneg_left hlogX hB)
    have hX : X ^ (d / 2) ≤ B / A := by
      have hXpos2 : 0 < X ^ (d / 2) := Real.rpow_pos_of_pos hXpos (d / 2)
      have hA' : A * X ^ (d / 2) ≤ B := by
        have hmain : (A * X ^ (d / 2)) * (X ^ (d / 2)) ≤ B * X ^ (d / 2) := by
          rw [mul_assoc]
          have hXd : X ^ d = X ^ (d / 2) * X ^ (d / 2) := by
            have hsum : d = d / 2 + d / 2 := by ring
            rw [hsum, Real.rpow_add hXpos]
          rw [← hXd]
          exact hupper
        exact (mul_le_mul_right hXpos2).mp hmain
      exact (le_div_iff₀' hA).mpr (by simpa [mul_comm] using hA')
    have hXfinal : X ≤ (B / A) ^ (2 / d) := by
      have hpos : 0 ≤ B / A := div_nonneg hB hA.le
      have hexp : 0 < 2 / d := div_pos (by norm_num : 0 < (2 : ℝ)) hd
      have hbase : X = (X ^ (d / 2)) ^ (2 / d) := by
        rw [← Real.rpow_mul hXpos.le (d / 2) (2 / d)]
        have hmul' : (d / 2) * (2 / d) = 1 := by
          field_simp [hd.ne']
          ring
        rw [hmul', Real.rpow_one]
      calc
        X = (X ^ (d / 2)) ^ (2 / d) := hbase
        _ ≤ (B / A) ^ (2 / d) :=
          Real.rpow_le_rpow (Real.rpow_nonneg hXpos.le (d / 2)) hX hexp.le
    exact hXfinal
  have hcontr : ∀ᶠ X in atTop, (B / A) ^ (2 / d) < X :=
    Filter.eventually_gt_atTop ((B / A) ^ (2 / d))
  filter_upwards [hbound, hcontr] with X hb hc
  linarith

/-- The single-layer contradiction: the forcing lower count at
`σ = 2/3`, `T = X^(lam(1-β))` with the exponent gap beats the Carlson upper
bound once the exponent comparison `lam(1-β)q(σ) < 2lam(β-σ) − lam(1-β)q(σ)`
holds (for `σ = 2/3`, `lam = 1` this is exactly `β > 14/17`). -/
theorem singleLayerForcing_carlson_contradiction
    {σ β lam c k : ℝ}
    (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (hσβ : σ ≤ β) (hβ1 : β < 1)
    (hlam : 0 < lam) (hc : 0 < c) (hk : 0 ≤ k)
    (hlow : ∀ᶠ X in atTop,
      c * X ^ (2 * lam * (β - σ) - lam * (1 - β) * (4 * σ * (1 - σ))) * (Real.log X) ^ (-k) ≤
        (ZeroDensity.zeroDensityCount σ (X ^ (lam * (1 - β))) : ℝ))
    (hgap : lam * (1 - β) * (4 * σ * (1 - σ)) <
      2 * lam * (β - σ) - lam * (1 - β) * (4 * σ * (1 - σ))) :
    False := by
  let hCarlson : CarlsonEventualMajorant σ :=
    Classical.choice (exists_carlsonEventualMajorant hσ hσ1)
  have hγpos : 0 < lam * (1 - β) := mul_pos hlam (sub_pos.mpr hβ1)
  have hγ0 : 0 ≤ lam * (1 - β) := le_of_lt hγpos
  have hq0 : 0 ≤ 4 * σ * (1 - σ) :=
    mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (4 : ℝ)) hσ.le) (sub_nonneg.mpr hσ1.le)
  have hCarlsonX : ∀ᶠ X in atTop,
      (ZeroDensity.zeroDensityCount σ (X ^ (lam * (1 - β))) : ℝ) ≤
        (hCarlson.C : ℝ) * ‖(X ^ (lam * (1 - β))) ^ (4 * σ * (1 - σ)) *
          (Real.log (X ^ (lam * (1 - β)))) ^ 4‖ := by
    have htend : Filter.Tendsto (fun X : ℝ => X ^ (lam * (1 - β))) atTop atTop :=
      tendsto_rpow_atTop hγpos
    exact htend.eventually hCarlson.bound
  have hnorm : ∀ᶠ X in atTop,
      c * X ^ (2 * lam * (β - σ) - lam * (1 - β) * (4 * σ * (1 - σ))) * (Real.log X) ^ (-k) ≤
        (hCarlson.C : ℝ) * (lam * (1 - β)) ^ 4 *
          X ^ (lam * (1 - β) * (4 * σ * (1 - σ))) * (Real.log X) ^ 4 := by
    filter_upwards [hlow, hCarlsonX, Filter.eventually_ge_atTop (1 : ℝ)] with X hlowX hupX hX1
    have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX1
    have hpow1 : (X ^ (lam * (1 - β))) ^ (4 * σ * (1 - σ)) =
        X ^ (lam * (1 - β) * (4 * σ * (1 - σ))) := by
      rw [Real.rpow_mul hXpos.le (lam * (1 - β)) (4 * σ * (1 - σ))]
    have hlog1 : Real.log (X ^ (lam * (1 - β))) = (lam * (1 - β)) * Real.log X :=
      Real.log_rpow hXpos (lam * (1 - β))
    have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg hX1
    have hγlog0 : 0 ≤ (lam * (1 - β)) * Real.log X := mul_nonneg hγ0 hlogX0
    have hnorm4 : ‖(X ^ (lam * (1 - β))) ^ (4 * σ * (1 - σ)) *
          (Real.log (X ^ (lam * (1 - β)))) ^ 4‖ =
        X ^ (lam * (1 - β) * (4 * σ * (1 - σ))) * (lam * (1 - β)) ^ 4 * (Real.log X) ^ 4 := by
      rw [hpow1, hlog1, Real.norm_eq_abs]
      have hnonneg : 0 ≤ X ^ (lam * (1 - β) * (4 * σ * (1 - σ))) *
          ((lam * (1 - β)) * Real.log X) ^ 4 := by
        positivity
      rw [abs_of_nonneg hnonneg]
      have hγ4 : ((lam * (1 - β)) * Real.log X) ^ 4 = (lam * (1 - β)) ^ 4 * (Real.log X) ^ 4 := by
        rw [Real.mul_rpow hγ0 hlogX0]
      rw [hγ4]
      ring
    exact hlowX.trans (by simpa [hnorm4] using hupX)
  have hd : 0 < 2 * lam * (β - σ) - 2 * lam * (1 - β) * (4 * σ * (1 - σ)) := by
    linarith [hgap]
  have hfin : ∀ᶠ X in atTop,
      c * X ^ (2 * lam * (β - σ) - 2 * lam * (1 - β) * (4 * σ * (1 - σ))) * (Real.log X) ^ (-k) ≤
        ((hCarlson.C : ℝ) * (lam * (1 - β)) ^ 4) * (Real.log X) ^ 4 := by
    filter_upwards [hnorm, Filter.eventually_ge_atTop (1 : ℝ)] with X hnormX hX1
    have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX1
    have hden : 0 < X ^ (lam * (1 - β) * (4 * σ * (1 - σ))) :=
      Real.rpow_pos_of_pos hXpos (lam * (1 - β) * (4 * σ * (1 - σ)))
    have hdiv : c * X ^ (2 * lam * (β - σ) - lam * (1 - β) * (4 * σ * (1 - σ))) *
          (Real.log X) ^ (-k) / X ^ (lam * (1 - β) * (4 * σ * (1 - σ))) ≤
        ((hCarlson.C : ℝ) * (lam * (1 - β)) ^ 4) *
          X ^ (lam * (1 - β) * (4 * σ * (1 - σ))) * (Real.log X) ^ 4 /
            X ^ (lam * (1 - β) * (4 * σ * (1 - σ))) := by
      exact div_le_div_of_nonneg_right hnormX hden.le
    have hdiv' : c * X ^ (2 * lam * (β - σ) - lam * (1 - β) * (4 * σ * (1 - σ))) *
          (Real.log X) ^ (-k) / X ^ (lam * (1 - β) * (4 * σ * (1 - σ))) =
        c * X ^ (2 * lam * (β - σ) - 2 * lam * (1 - β) * (4 * σ * (1 - σ))) * (Real.log X) ^ (-k) := by
      have hpow : X ^ (2 * lam * (β - σ) - lam * (1 - β) * (4 * σ * (1 - σ))) /
            X ^ (lam * (1 - β) * (4 * σ * (1 - σ))) =
          X ^ (2 * lam * (β - σ) - 2 * lam * (1 - β) * (4 * σ * (1 - σ))) := by
        calc
          X ^ (2 * lam * (β - σ) - lam * (1 - β) * (4 * σ * (1 - σ))) /
                X ^ (lam * (1 - β) * (4 * σ * (1 - σ)))
              = X ^ (2 * lam * (β - σ) - lam * (1 - β) * (4 * σ * (1 - σ))) *
                  X ^ (-(lam * (1 - β) * (4 * σ * (1 - σ)))) := by
            rw [div_eq_mul_inv, ← Real.rpow_neg hXpos.le]
          _ = X ^ (2 * lam * (β - σ) - lam * (1 - β) * (4 * σ * (1 - σ)) +
              -(lam * (1 - β) * (4 * σ * (1 - σ)))) := by
            rw [Real.rpow_add hXpos]
          _ = X ^ (2 * lam * (β - σ) - 2 * lam * (1 - β) * (4 * σ * (1 - σ))) := by
            congr 1
            ring
      calc
        c * X ^ (2 * lam * (β - σ) - lam * (1 - β) * (4 * σ * (1 - σ))) *
              (Real.log X) ^ (-k) / X ^ (lam * (1 - β) * (4 * σ * (1 - σ)))
            = c * (Real.log X) ^ (-k) *
              (X ^ (2 * lam * (β - σ) - lam * (1 - β) * (4 * σ * (1 - σ))) /
                X ^ (lam * (1 - β) * (4 * σ * (1 - σ)))) := by ring
        _ = c * (Real.log X) ^ (-k) *
              X ^ (2 * lam * (β - σ) - 2 * lam * (1 - β) * (4 * σ * (1 - σ))) := by
          rw [hpow]
        _ = c * X ^ (2 * lam * (β - σ) - 2 * lam * (1 - β) * (4 * σ * (1 - σ))) * (Real.log X) ^ (-k) := by
          ring
    have hdiv'' : ((hCarlson.C : ℝ) * (lam * (1 - β)) ^ 4) *
          X ^ (lam * (1 - β) * (4 * σ * (1 - σ))) * (Real.log X) ^ 4 /
            X ^ (lam * (1 - β) * (4 * σ * (1 - σ))) =
        ((hCarlson.C : ℝ) * (lam * (1 - β)) ^ 4) * (Real.log X) ^ 4 := by
      calc
        ((hCarlson.C : ℝ) * (lam * (1 - β)) ^ 4) *
              X ^ (lam * (1 - β) * (4 * σ * (1 - σ))) * (Real.log X) ^ 4 /
                X ^ (lam * (1 - β) * (4 * σ * (1 - σ)))
            = ((hCarlson.C : ℝ) * (lam * (1 - β)) ^ 4) * (Real.log X) ^ 4 *
              (X ^ (lam * (1 - β) * (4 * σ * (1 - σ))) /
                X ^ (lam * (1 - β) * (4 * σ * (1 - σ)))) := by ring
        _ = ((hCarlson.C : ℝ) * (lam * (1 - β)) ^ 4) * (Real.log X) ^ 4 * 1 := by
          rw [div_self hden.ne']
        _ = ((hCarlson.C : ℝ) * (lam * (1 - β)) ^ 4) * (Real.log X) ^ 4 := by ring
    rwa [hdiv', hdiv''] at hdiv
  have hB : 0 ≤ (hCarlson.C : ℝ) * (lam * (1 - β)) ^ 4 :=
    mul_nonneg (by exact_mod_cast hCarlson.C_nonneg)
      (Real.rpow_nonneg hγ0 4)
  exact powerGrowth_logGap_contradiction
    (A := c) (B := (hCarlson.C : ℝ) * (lam * (1 - β)) ^ 4) (k := k)
    (d := 2 * lam * (β - σ) - 2 * lam * (1 - β) * (4 * σ * (1 - σ)))
    hc hB hk hd hfin

/--
Terminal partial exclusion: if the coherent forcing supplies the lower
count for every seed real part `β > 14/17` and window exponent `lam > 0`,
then no non-trivial zero has real part `> 14/17`.

The exponent-gap arithmetic is unconditional: with `σ = 2/3` and
`lam = 1` the comparison `(1-β)·8/9 < 2(β-2/3) − (1-β)·8/9` is exactly
`β > 14/17`.
-/
theorem no_nontrivial_zero_re_gt_14_over_17_of_forcing
    (hforcing : ∀ β lam : ℝ, (14 / 17 : ℝ) < β → β < 1 → 0 < lam →
      ∃ c k : ℝ, 0 < c ∧ 0 < k ∧
        ∀ᶠ X in atTop,
          c * X ^ (2 * lam * (β - 2 / 3) - lam * (1 - β) * (8 / 9 : ℝ)) * (Real.log X) ^ (-k) ≤
            (ZeroDensity.zeroDensityCount (2 / 3 : ℝ) (X ^ (lam * (1 - β))) : ℝ)) :
    ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → ρ.re ≤ (14 / 17 : ℝ) := by
  intro ρ hρ
  by_contra hgt
  have hβ : (14 / 17 : ℝ) < ρ.re := lt_of_not_ge hgt
  have hβ1 : ρ.re < 1 := hρ.2.2
  rcases hforcing ρ.re 1 hβ hβ1 (by norm_num : 0 < (1 : ℝ)) with ⟨c, k, hc, hk, hlow⟩
  have hgap : (1 - ρ.re) * (8 / 9 : ℝ) <
      2 * (ρ.re - 2 / 3) - (1 - ρ.re) * (8 / 9) := by
    nlinarith [hβ]
  have hFalse := singleLayerForcing_carlson_contradiction
    (σ := 2 / 3) (β := ρ.re) (lam := 1) (c := c) (k := k)
    (hσ := by norm_num) (hσ1 := by norm_num)
    (hσβ := by linarith) (hβ1 := hβ1)
    (hlam := by norm_num) (hc := hc) (hk := le_of_lt hk) hlow hgap
  exact False.elim hFalse

end PrimeNumberTheorem
