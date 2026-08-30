import PrimeNumberTheorem.SingleLayerForcingHalfRangeDensity

set_option autoImplicit false
open Filter
open PrimeNumberTheorem

example (lam eta : ℝ) :
    2 * lam * (14 / 17 - 2 / 3) -
        lam * (1 - 14 / 17) * (8 / 9 + eta + halfRangeTargetExponent) =
      (3 * lam / 17) * (1 / 400 - eta) :=
  halfRange_forcing_loss_margin lam eta

example {β lam c k eta : ℝ}
    (hβ : (14 / 17 : ℝ) ≤ β) (hβ1 : β < 1)
    (hlam : 0 < lam) (hc : 0 < c) (hk : 0 ≤ k) (heta : eta < 1 / 400)
    (hlow : ∀ᶠ X in atTop,
      c * X ^ (2 * lam * (β - 2 / 3) - lam * (1 - β) * (8 / 9 + eta)) *
          (Real.log X) ^ (-k) ≤
        (ZeroDensity.zeroDensityCount (2 / 3) (X ^ (lam * (1 - β))) : ℝ)) : False :=
  singleLayerForcing_halfRange_contradiction hβ hβ1 hlam hc hk heta hlow

example (hforcing : ∀ β lam : ℝ, (14 / 17 : ℝ) < β → β < 1 → 0 < lam →
    ∃ c k : ℝ, 0 < c ∧ 0 < k ∧ ∀ᶠ X in atTop,
      c * X ^ (2 * lam * (β - 2 / 3) - lam * (1 - β) * (8 / 9)) *
          (Real.log X) ^ (-k) ≤
        (ZeroDensity.zeroDensityCount (2 / 3) (X ^ (lam * (1 - β))) : ℝ)) :
    ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → ρ.re ≤ (14 / 17 : ℝ) :=
  no_nontrivial_zero_re_gt_14_over_17_of_forcing_halfRange hforcing

example (hforcing : ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → (14 / 17 : ℝ) ≤ ρ.re →
    ∃ c k : ℝ, 0 < c ∧ 0 ≤ k ∧ ∀ᶠ X in atTop,
      c * X ^ (2 * (ρ.re - 2 / 3) - (1 - ρ.re) * (8 / 9)) *
          (Real.log X) ^ (-k) ≤
        (ZeroDensity.zeroDensityCount (2 / 3) (X ^ (1 - ρ.re)) : ℝ)) :
    ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → ρ.re < (14 / 17 : ℝ) :=
  no_nontrivial_zero_re_ge_14_over_17_of_seed_forcing_halfRange hforcing

#print axioms halfRange_forcing_loss_margin
#print axioms singleLayerForcing_halfRange_contradiction
#print axioms no_nontrivial_zero_re_gt_14_over_17_of_forcing_halfRange
#print axioms no_nontrivial_zero_re_ge_14_over_17_of_seed_forcing_halfRange
