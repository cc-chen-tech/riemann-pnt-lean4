import HardyTheorem.AFEExplicitPoissonFarTail

open HardyTheorem AFE Set
open scoped BigOperators

example {C₁ C₂ sigma x N t : ℝ} {m : ℕ}
    (hs : 0 < sigma) (hx : 2 ≤ x) (hxN : x ≤ N) (ht : 0 ≤ t)
    (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hC₂ : ∀ z : ℝ, |deriv (deriv Real.smoothTransition) z| ≤ C₂)
    (hm : 1 ≤ m) (hfar : t / (x - 1) ≤ Real.pi * m) :
    ‖explicitPoissonMode sigma x N t (m : ℤ)‖ +
      ‖explicitPoissonMode sigma x N t (-(m : ℤ))‖ ≤
        2 * explicitPoissonFarConstant C₁ C₂ sigma * (x - 1) ^ (-sigma) /
          (Real.pi * m) ^ 2 :=
  norm_explicitPoissonMode_pair_le_far hs hx hxN ht hC₁0 hC₂0 hC₁ hC₂ hm hfar

-- Arbitrary finite far-frequency sets; the bound depends on neither N nor S.
example {C₁ C₂ sigma x N t : ℝ} (S : Finset ℕ)
    (hs : 0 < sigma) (hx : 2 ≤ x) (hxN : x ≤ N) (ht : 0 ≤ t)
    (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hC₂ : ∀ z : ℝ, |deriv (deriv Real.smoothTransition) z| ≤ C₂)
    (hfar : ∀ m ∈ S, 1 ≤ m ∧ t / (x - 1) ≤ Real.pi * m) :
    (∑ m ∈ S, (‖explicitPoissonMode sigma x N t (m : ℤ)‖ +
      ‖explicitPoissonMode sigma x N t (-(m : ℤ))‖)) ≤
        4 * explicitPoissonFarConstant C₁ C₂ sigma * (x - 1) ^ (-sigma) / Real.pi ^ 2 :=
  sum_norm_explicitPoissonMode_pair_le_far S hs hx hxN ht hC₁0 hC₂0 hC₁ hC₂ hfar

#print axioms norm_explicitPoissonMode_pair_le_far
#print axioms sum_norm_explicitPoissonMode_pair_le_far

-- An infinite-series inequality alone could be vacuous without summability.
example {C₁ C₂ sigma x N t : ℝ}
    (hs : 0 < sigma) (hx : 2 ≤ x) (hxN : x ≤ N) (ht : 0 ≤ t)
    (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hC₂ : ∀ z : ℝ, |deriv (deriv Real.smoothTransition) z| ≤ C₂) :
    Summable (explicitPoissonFarMass sigma x N t) ∧
      (∑' m : ℕ, explicitPoissonFarMass sigma x N t m) ≤
        4 * explicitPoissonFarConstant C₁ C₂ sigma * (x - 1) ^ (-sigma) / Real.pi ^ 2 :=
  summable_tsum_explicitPoissonFarMass_le hs hx hxN ht hC₁0 hC₂0 hC₁ hC₂

#print axioms summable_tsum_explicitPoissonFarMass_le
