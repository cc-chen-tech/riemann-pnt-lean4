import PrimeNumberTheorem.SingleLayerForcingSeparatedDensity

namespace PrimeNumberTheorem

open Filter

example {A C k d : ℝ} {B : ℕ}
    (hA : 0 < A) (hC : 0 ≤ C) (hk : 0 ≤ k) (hd : 0 < d)
    (hineq : ∀ᶠ X in atTop,
      A * X ^ d * (Real.log X) ^ (-k) ≤ C * (Real.log X) ^ B) :
    False :=
  powerGrowth_arbitraryLogGap_contradiction hA hC hk hd hineq

example {σ β lam c k qF qD : ℝ} {B : ℕ}
    (hβ1 : β < 1) (hlam : 0 < lam) (hc : 0 < c) (hk : 0 ≤ k)
    (hqD : 0 ≤ qD) (density : ZeroDensityEventualMajorant σ qD B)
    (hlow : ∀ᶠ X in atTop,
      c * X ^ (2 * lam * (β - σ) - lam * (1 - β) * qF) *
          (Real.log X) ^ (-k) ≤
        (ZeroDensity.zeroDensityCount σ (X ^ (lam * (1 - β))) : ℝ))
    (hgap : lam * (1 - β) * qD <
      2 * lam * (β - σ) - lam * (1 - β) * qF) :
    False :=
  singleLayerForcing_density_contradiction hβ1 hlam hc hk hqD density hlow hgap

example :
    0 < 2 * (14 / 17 - 2 / 3) -
      (1 - 14 / 17) * (8 / 9 + diTargetExponent) :=
  separatedDensity_gap_at_fourteen_seventeenths

example {β lam c k : ℝ}
    (density : CarlsonDIImprovedDensityCertificate)
    (hβ : 14 / 17 < β) (hβ1 : β < 1)
    (hlam : 0 < lam) (hc : 0 < c) (hk : 0 ≤ k)
    (hlow : ∀ᶠ X in atTop,
      c * X ^ (2 * lam * (β - 2 / 3) - lam * (1 - β) * (8 / 9)) *
          (Real.log X) ^ (-k) ≤
        (ZeroDensity.zeroDensityCount (2 / 3)
          (X ^ (lam * (1 - β))) : ℝ)) :
    False :=
  singleLayerForcing_DI_contradiction density hβ hβ1 hlam hc hk hlow

#print axioms powerGrowth_arbitraryLogGap_contradiction
#print axioms singleLayerForcing_density_contradiction
#print axioms separatedDensity_gap_at_fourteen_seventeenths
#print axioms singleLayerForcing_DI_contradiction
#print axioms no_nontrivial_zero_re_gt_14_over_17_of_forcing_and_DI

end PrimeNumberTheorem
