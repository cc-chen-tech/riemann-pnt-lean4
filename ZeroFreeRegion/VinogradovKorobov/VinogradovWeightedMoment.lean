import ZeroFreeRegion.VinogradovKorobov.VinogradovWeighted

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

local instance weightedPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- A coefficient vector for the weighted system: the coefficient of degree
`j+1` lives in its own ring modulo `p^((j+1)*a)`. -/
abbrev VinogradovWeightedCoefficient (p a k : ℕ) :=
  (j : Fin k) → ZMod (vinogradovWeightedModulus p a j)

instance vinogradovWeightedModulus_neZero
    (p a : ℕ) [Fact p.Prime] {k : ℕ} (j : Fin k) :
    NeZero (vinogradovWeightedModulus p a j) :=
  ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩

/-- Product of degree-wise normalized character averages detecting all
weighted Vinogradov congruences. -/
noncomputable def vinogradovWeightedSolutionSelector
    (p a k s X : ℕ) [Fact p.Prime]
    (x y : Fin s → Fin X) : ℂ :=
  ∏ j : Fin k,
    ((vinogradovWeightedModulus p a j : ℂ)⁻¹ *
      ∑ c : ZMod (vinogradovWeightedModulus p a j),
        ZMod.stdAddChar
          (c * (vinogradovWeightedPowerSumMod p a x j -
            vinogradovWeightedPowerSumMod p a y j)))

/-- The weighted Fourier selector is one precisely on weighted modular
solutions, and zero otherwise. -/
theorem vinogradovWeightedSolutionSelector_eq_indicator
    (p a k s X : ℕ) [Fact p.Prime]
    (x y : Fin s → Fin X) :
    vinogradovWeightedSolutionSelector p a k s X x y =
      if IsVinogradovWeightedSolutionMod p a k s X x y then 1 else 0 := by
  classical
  simp only [vinogradovWeightedSolutionSelector,
    normalized_sum_stdAddChar_mul]
  by_cases h : IsVinogradovWeightedSolutionMod p a k s X x y
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro j hj
    rw [if_pos]
    exact sub_eq_zero.mpr (h j)
  · rw [if_neg h]
    simp only [IsVinogradovWeightedSolutionMod, not_forall] at h
    obtain ⟨j, hj⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [if_neg]
    exact sub_ne_zero.mpr hj

/-- Summing the weighted selector over both tuples counts exactly the weighted
modular solutions. -/
theorem sum_vinogradovWeightedSolutionSelector_eq_count
    (p a k s X : ℕ) [Fact p.Prime] :
    ∑ x : Fin s → Fin X, ∑ y : Fin s → Fin X,
      vinogradovWeightedSolutionSelector p a k s X x y =
        (vinogradovWeightedSolutionCountMod p a k s X : ℂ) := by
  classical
  simp_rw [vinogradovWeightedSolutionSelector_eq_indicator]
  simp [vinogradovWeightedSolutionCountMod, Finset.sum_boole]

/-- The product of complex normalization factors is the inverse critical
weight modulus. -/
theorem prod_vinogradovWeightedModulus_inv_natCast
    (p a k : ℕ) [Fact p.Prime] :
    (∏ j : Fin k,
        (vinogradovWeightedModulus p a j : ℂ)⁻¹) =
      (p ^ (a * (k * (k + 1) / 2)) : ℂ)⁻¹ := by
  rw [Finset.prod_inv_distrib]
  congr 1
  exact_mod_cast prod_vinogradovWeightedModulus p a k

end

end ZeroFreeRegion.VinogradovKorobov
