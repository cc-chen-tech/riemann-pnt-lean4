import HardyTheorem.AFEExplicitPoissonFiniteBand

open HardyTheorem AFE
open scoped BigOperators

-- Positive modes, with exact Fourier normalization and no extra power of M.
example {C₁ sigma x N t : ℝ} (M : ℕ)
    (hs : 0 < sigma) (hx : 1 < x) (hxN : x ≤ N) (ht : 0 ≤ t)
    (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁) :
    (∑ m ∈ Finset.Icc 1 M, ‖explicitPoissonMode sigma x N t (m : ℤ)‖) ≤
      (8 * C₁ * (x - 1) ^ (-sigma) / Real.pi) * (1 + Real.log M) :=
  sum_norm_explicitPoissonMode_positive_le_log M hs hx hxN ht hC₁0 hC₁

-- The nearest integer above the endpoint is excluded: indexing starts at j=1.
example {C₁ sigma x N t : ℝ} (M : ℕ)
    (hs : 0 < sigma) (hx : 1 < x) (hxN : x ≤ N) (ht : 0 ≤ t)
    (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁) :
    (∑ j ∈ Finset.Icc 1 M,
      ‖explicitPoissonMode sigma x N t
        (-((Nat.floor (t / (2 * Real.pi * (x - 1))) + 1 + j : ℕ) : ℤ))‖) ≤
      (8 * C₁ * (x - 1) ^ (-sigma) / Real.pi) * (1 + Real.log M) :=
  sum_norm_explicitPoissonMode_above_endpoint_le_log M hs hx hxN ht hC₁0 hC₁

#print axioms sum_norm_explicitPoissonMode_positive_le_log
#print axioms sum_norm_explicitPoissonMode_above_endpoint_le_log
