import ZeroFreeRegion.VinogradovKorobov.VinogradovIncompleteMoment

open ZeroFreeRegion.VinogradovKorobov

#check incompleteVinogradovPowerSumMod
#check IsIncompleteVinogradovSolutionMod
#check incompleteVinogradovSolutionCountMod
#check incompleteVinogradovPhaseMod
#check incompleteVinogradovWeylSumMod
#check incompleteVinogradovTuplePhaseMod
#check normalizedIncompleteVinogradovMomentMod
#check normalizedIncompleteVinogradovMomentMod_eq_solutionCount
#check isIncompleteVinogradovSolutionMod_one_iff
#check incompleteVinogradovSolutionCountMod_one_eq
#check normalizedIncompleteVinogradovMomentMod_one_eq
#check IsVinogradovSolutionMod.toIncomplete
#check vinogradovSolutionCountMod_le_incomplete

example (Q k s X : ℕ) [NeZero Q] :
    normalizedIncompleteVinogradovMomentMod Q 1 k s X =
      normalizedVinogradovMomentMod Q k s X :=
  normalizedIncompleteVinogradovMomentMod_one_eq Q k s X
