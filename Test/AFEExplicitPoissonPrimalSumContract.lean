import HardyTheorem.AFEExplicitPoissonPrimalSum

open HardyTheorem AFE Complex

-- The natural-number Dirichlet sum is the conclusion, not an input bridge.
example (sigma t : ℝ) {K N : ℕ} (hK : 1 ≤ K) (hN : K + 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-((sigma : ℂ) + I * t))) -
        (∑ n ∈ Finset.Icc 1 K, (n : ℂ) ^ (-((sigma : ℂ) + I * t))) =
      ∑' k : ℤ, explicitPoissonMode sigma ((K : ℝ) + 1) N t k :=
  dirichlet_sum_sub_eq_explicitPoisson_tsum sigma t hK hN

-- This exact identity retains the pole-subtraction sign used in the AFE.
example (sigma t : ℝ) {K N : ℕ} (hK : 1 ≤ K) (hN : K + 1 ≤ N) :
    let s : ℂ := (sigma : ℂ) + I * t
    ((∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) - (N : ℂ) ^ (1 - s) / (1 - s)) -
        (∑ n ∈ Finset.Icc 1 K, (n : ℂ) ^ (-s)) =
      (∑' k : ℤ, explicitPoissonMode sigma ((K : ℝ) + 1) N t k) -
        (N : ℂ) ^ (1 - s) / (1 - s) :=
  dirichlet_sum_sub_pole_eq_explicitPoisson_tsum sigma t hK hN

#print axioms dirichlet_sum_sub_eq_explicitPoisson_tsum
#print axioms dirichlet_sum_sub_pole_eq_explicitPoisson_tsum
