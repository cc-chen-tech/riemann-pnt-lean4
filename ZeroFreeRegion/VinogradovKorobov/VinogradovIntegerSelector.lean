import ZeroFreeRegion.VinogradovKorobov.VinogradovMeanValue
import ZeroFreeRegion.VinogradovKorobov.VinogradovModularSymmetry

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- The `j+1`-st power sum of an arbitrary integer tuple, reduced modulo
`Q`. -/
def vinogradovIntPowerSumMod
    (Q : ℕ) {k s : ℕ} (x : Fin s → ℤ) (j : Fin k) : ZMod Q :=
  ∑ i, (x i : ZMod Q) ^ (j.val + 1)

/-- The common-modulus integer Vinogradov predicate is equivalent to equality
of all reduced power sums. -/
theorem isVinogradovSolutionIntMod_iff_powerSumMod
    (Q k s : ℕ) (x y : Fin s → ℤ) :
    IsVinogradovSolutionIntMod Q k s x y ↔
      ∀ j : Fin k,
        vinogradovIntPowerSumMod Q x j = vinogradovIntPowerSumMod Q y j := by
  constructor
  · intro h j
    have hj := (ZMod.intCast_eq_intCast_iff
      (vinogradovPowerSumInt x j) (vinogradovPowerSumInt y j) Q).mpr (h j)
    simpa [vinogradovIntPowerSumMod, vinogradovPowerSumInt] using hj
  · intro h j
    apply (ZMod.intCast_eq_intCast_iff
      (vinogradovPowerSumInt x j) (vinogradovPowerSumInt y j) Q).mp
    simpa [vinogradovIntPowerSumMod, vinogradovPowerSumInt] using h j

/-- The integer modular Vinogradov predicate is decidable through its finite
system of reduced power-sum equations. -/
instance instDecidableIsVinogradovSolutionIntMod
    (Q k s : ℕ) (x y : Fin s → ℤ) :
    Decidable (IsVinogradovSolutionIntMod Q k s x y) :=
  decidable_of_iff
    (∀ j : Fin k,
      vinogradovIntPowerSumMod Q x j = vinogradovIntPowerSumMod Q y j)
    (isVinogradovSolutionIntMod_iff_powerSumMod Q k s x y).symm

/-- Product of normalized character averages detecting the common-modulus
Vinogradov equations for an arbitrary integer tuple pair. -/
noncomputable def vinogradovIntSolutionSelector
    (Q k s : ℕ) [NeZero Q] (x y : Fin s → ℤ) : ℂ :=
  ∏ j : Fin k,
    ((Q : ℂ)⁻¹ * ∑ a : ZMod Q,
      ZMod.stdAddChar
        (a * (vinogradovIntPowerSumMod Q x j -
          vinogradovIntPowerSumMod Q y j)))

/-- The arbitrary-integer Fourier selector is exactly the indicator of the
common-modulus Vinogradov system. -/
theorem vinogradovIntSolutionSelector_eq_indicator
    (Q k s : ℕ) [NeZero Q] (x y : Fin s → ℤ) :
    vinogradovIntSolutionSelector Q k s x y =
      if IsVinogradovSolutionIntMod Q k s x y then 1 else 0 := by
  classical
  simp only [vinogradovIntSolutionSelector, normalized_sum_stdAddChar_mul]
  by_cases h : IsVinogradovSolutionIntMod Q k s x y
  · rw [if_pos h]
    have hmod := (isVinogradovSolutionIntMod_iff_powerSumMod Q k s x y).mp h
    apply Finset.prod_eq_one
    intro j hj
    rw [if_pos]
    exact sub_eq_zero.mpr (hmod j)
  · rw [if_neg h]
    have hmod : ¬ ∀ j : Fin k,
        vinogradovIntPowerSumMod Q x j = vinogradovIntPowerSumMod Q y j := by
      intro hall
      exact h ((isVinogradovSolutionIntMod_iff_powerSumMod Q k s x y).mpr hall)
    simp only [not_forall] at hmod
    obtain ⟨j, hj⟩ := hmod
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [if_neg]
    exact sub_ne_zero.mpr hj

end

end ZeroFreeRegion.VinogradovKorobov
