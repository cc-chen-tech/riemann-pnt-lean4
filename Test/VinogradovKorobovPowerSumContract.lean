import ZeroFreeRegion.VinogradovKorobov.PowerSum

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable example (L : ℕ) (α : ℝ) : ℝ :=
  finiteRpowSumEnvelope L α

example (L : ℕ) (α : ℝ)
    (hL : 2 ≤ L) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    (∑ ell ∈ Finset.Icc 1 (L - 1), (ell : ℝ) ^ (-α)) ≤
      finiteRpowSumEnvelope L α :=
  sum_Icc_rpow_neg_le_envelope L α hL hα0 hα1

example (L : ℕ) (α : ℝ)
    (hL : 2 ≤ L) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    (∑ ell ∈ Finset.Icc 1 (L - 1),
        ((L : ℝ) - (ell : ℝ)) * (ell : ℝ) ^ (-α)) ≤
      (L : ℝ) * finiteRpowSumEnvelope L α :=
  weighted_rpow_neg_sum_le_envelope L α hL hα0 hα1

example (L : ℕ) (α : ℝ)
    (hL : 2 ≤ L) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    0 ≤ finiteRpowSumEnvelope L α :=
  finiteRpowSumEnvelope_nonneg L α hL hα0 hα1

end ZeroFreeRegion.VinogradovKorobov
