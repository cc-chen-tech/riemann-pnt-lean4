import ZeroFreeRegion.VinogradovKorobov.FordIncompleteSupportMoment

open scoped BigOperators

open ZeroFreeRegion.VinogradovKorobov

#check sum_norm_incompleteVinogradovSupportWeylSumMod_pow_two_mul_eq

example (Q h d s X : ℕ) [NeZero Q] (B : Finset (Fin X)) :
    ∑ a : Fin d → ZMod Q,
      ‖incompleteVinogradovSupportWeylSumMod Q h d X B a‖ ^ (2 * s) =
        (Q : ℝ) ^ d *
          incompleteVinogradovSupportSolutionCountMod Q h d s X B :=
  sum_norm_incompleteVinogradovSupportWeylSumMod_pow_two_mul_eq
    Q h d s X B
