import PrimeNumberTheorem.CarlsonHalfRangeDensity
import PrimeNumberTheorem.SingleLayerForcingSeparatedDensity

/-! The unconditional half-range density theorem plugged into the existing
single-layer forcing chain. The forcing lower bound remains an explicit
assumption; no unconditional zero-free region is asserted here. -/

open Filter

namespace PrimeNumberTheorem

/-- Exact margin at the old endpoint, including a loss in the forcing exponent. -/
theorem halfRange_forcing_loss_margin (lam eta : ℝ) :
    2 * lam * (14 / 17 - 2 / 3) -
        lam * (1 - 14 / 17) * (8 / 9 + eta + halfRangeTargetExponent) =
      (3 * lam / 17) * (1 / 400 - eta) := by
  dsimp [halfRangeTargetExponent]
  ring

/-- The new density input is supplied by a proved theorem, not a premise.
At every `beta>=14/17`, an extra forcing loss `eta<1/400` is admissible. -/
theorem singleLayerForcing_halfRange_contradiction
    {β lam c k eta : ℝ}
    (hβ : (14 / 17 : ℝ) ≤ β) (hβ1 : β < 1)
    (hlam : 0 < lam) (hc : 0 < c) (hk : 0 ≤ k) (heta : eta < 1 / 400)
    (hlow : ∀ᶠ X in atTop,
      c * X ^ (2 * lam * (β - 2 / 3) - lam * (1 - β) * (8 / 9 + eta)) *
          (Real.log X) ^ (-k) ≤
        (ZeroDensity.zeroDensityCount (2 / 3) (X ^ (lam * (1 - β))) : ℝ)) : False := by
  have hclassic : 0 ≤ 2 * (β - 2 / 3) - (1 - β) * (16 / 9) := by
    linarith only [hβ]
  have hsmall : (1 - β) * eta < (1 - β) * (1 / 400) :=
    mul_lt_mul_of_pos_left heta (sub_pos.mpr hβ1)
  have hmargin : 0 < 2 * (β - 2 / 3) -
      (1 - β) * ((8 / 9 + eta) + (8 / 9 - 1 / 400)) := by
    nlinarith only [hclassic, hsmall]
  have hgap : lam * (1 - β) * (8 / 9 - 1 / 400) <
      2 * lam * (β - 2 / 3) - lam * (1 - β) * (8 / 9 + eta) := by
    nlinarith only [mul_pos hlam hmargin]
  exact singleLayerForcing_density_contradiction hβ1 hlam hc hk
    (by norm_num : (0 : ℝ) ≤ 8 / 9 - 1 / 400)
    (Classical.choice exists_carlson_halfRange_densityCertificate) hlow hgap

/-- The original `SingleLayerForcingBeta14Over17` lower-count interface,
now using the unconditional improved density certificate. -/
theorem no_nontrivial_zero_re_gt_14_over_17_of_forcing_halfRange
    (hforcing : ∀ β lam : ℝ, (14 / 17 : ℝ) < β → β < 1 → 0 < lam →
      ∃ c k : ℝ, 0 < c ∧ 0 < k ∧ ∀ᶠ X in atTop,
        c * X ^ (2 * lam * (β - 2 / 3) - lam * (1 - β) * (8 / 9)) *
            (Real.log X) ^ (-k) ≤
          (ZeroDensity.zeroDensityCount (2 / 3) (X ^ (lam * (1 - β))) : ℝ)) :
    ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → ρ.re ≤ (14 / 17 : ℝ) := by
  intro ρ hρ
  by_contra hnot
  have hβ : (14 / 17 : ℝ) < ρ.re := lt_of_not_ge hnot
  obtain ⟨c, k, hc, hk, hlow⟩ := hforcing ρ.re 1 hβ hρ.2.2 (by norm_num)
  apply singleLayerForcing_halfRange_contradiction (lam := 1) (eta := 0) hβ.le hρ.2.2
    (by norm_num) hc hk.le (by norm_num)
  simpa only [add_zero] using hlow

/-- If the forcing supplier works for actual seeds at the old endpoint,
the positive density margin also excludes equality there. The seed-forcing
supplier is not constructed by this theorem. -/
theorem no_nontrivial_zero_re_ge_14_over_17_of_seed_forcing_halfRange
    (hforcing : ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → (14 / 17 : ℝ) ≤ ρ.re →
      ∃ c k : ℝ, 0 < c ∧ 0 ≤ k ∧ ∀ᶠ X in atTop,
        c * X ^ (2 * (ρ.re - 2 / 3) - (1 - ρ.re) * (8 / 9)) *
            (Real.log X) ^ (-k) ≤
          (ZeroDensity.zeroDensityCount (2 / 3) (X ^ (1 - ρ.re)) : ℝ)) :
    ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → ρ.re < (14 / 17 : ℝ) := by
  intro ρ hρ
  by_contra hnot
  have hβ : (14 / 17 : ℝ) ≤ ρ.re := le_of_not_gt hnot
  obtain ⟨c, k, hc, hk, hlow⟩ := hforcing ρ hρ hβ
  apply singleLayerForcing_halfRange_contradiction (lam := 1) (eta := 0) hβ hρ.2.2
    (by norm_num) hc hk (by norm_num)
  simpa only [add_zero, mul_one, one_mul] using hlow

end PrimeNumberTheorem
