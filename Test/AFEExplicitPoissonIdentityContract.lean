import HardyTheorem.AFEExplicitPoissonIdentity

open HardyTheorem AFE Complex
open scoped FourierTransform

example (sigma t : ℝ) {x N : ℝ} (hx : 1 < x) (hxN : x ≤ N) (k : ℤ) :
    𝓕 (explicitWeightedPoissonCutoff ((sigma : ℂ) + I * t) x N) k =
      explicitPoissonMode sigma x N t k :=
  fourier_explicitWeightedPoissonCutoff_eq_mode sigma t hx hxN k

-- Same cutoff as the uniform derivative/tail estimates, with no Poisson gate.
example (sigma t : ℝ) {x N : ℝ} (hx : 1 < x) (hxN : x ≤ N) :
    (∑' n : ℤ, explicitWeightedPoissonCutoff ((sigma : ℂ) + I * t) x N n) =
      ∑' k : ℤ, explicitPoissonMode sigma x N t k :=
  explicitWeightedPoissonCutoff_tsum_eq_mode_tsum sigma t hx hxN

-- Unit transitions add no extra integer terms, unlike the old width-two bump.
example (s : ℂ) {m n : ℕ} (hm : 1 < m) (hmn : m ≤ n) :
    (∑' k : ℤ, explicitWeightedPoissonCutoff s m n k) =
      ∑ k ∈ Finset.Icc (m : ℤ) n, (k : ℂ) ^ (-s) :=
  explicitWeightedPoissonCutoff_tsum_eq_core s hm hmn

#print axioms explicitWeightedPoissonCutoff_contDiff
#print axioms fourier_explicitWeightedPoissonCutoff_eq_mode
#print axioms explicitWeightedPoissonCutoff_tsum_eq_mode_tsum
#print axioms explicitWeightedPoissonCutoff_tsum_eq_core
