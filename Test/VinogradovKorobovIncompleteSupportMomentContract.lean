import ZeroFreeRegion.VinogradovKorobov.VinogradovIncompleteSupportMoment

open ZeroFreeRegion.VinogradovKorobov

#check incompletePowerSumOnMod
#check IsIncompleteSolutionOnMod
#check incompleteSolutionCountOnMod
#check incompletePhaseOnMod
#check incompleteWeylSumOnMod
#check norm_incompleteWeylSumOnMod_le_card
#check normalizedIncompleteMomentOnMod
#check normalizedIncompleteMomentOnMod_eq_solutionCount
#check incompleteSolutionCountOnMod_le_total
#check vinogradovIntervalValueMod
#check normalizedIncompleteMomentOnMod_interval_eq
#check vinogradovSupportValueMod
#check IsIncompleteVinogradovSupportSolutionMod
#check incompleteVinogradovSupportSolutionCountMod
#check incompleteVinogradovSupportWeylSumMod
#check norm_incompleteVinogradovSupportWeylSumMod_le_card
#check normalizedIncompleteVinogradovSupportMomentMod
#check normalizedIncompleteVinogradovSupportMomentMod_eq_solutionCount
#check incompleteVinogradovSupportSolutionCountMod_le_total

example (Q h d s X : ℕ) [NeZero Q] :
    normalizedIncompleteMomentOnMod Q h d s
        (vinogradovIntervalValueMod Q X) =
      normalizedIncompleteVinogradovMomentMod Q h d s X :=
  normalizedIncompleteMomentOnMod_interval_eq Q h d s X

example (Q h d s X : ℕ) [NeZero Q] (B : Finset (Fin X)) :
    normalizedIncompleteVinogradovSupportMomentMod Q h d s X B =
      (incompleteVinogradovSupportSolutionCountMod Q h d s X B : ℂ) :=
  normalizedIncompleteVinogradovSupportMomentMod_eq_solutionCount
    Q h d s X B
