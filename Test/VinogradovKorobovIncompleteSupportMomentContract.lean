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

example (Q h d s : ℕ) {ι : Type*} [Fintype ι] [NeZero Q]
    (value : ι → ZMod Q) :
    normalizedIncompleteMomentOnMod Q h d s value =
      (incompleteSolutionCountOnMod Q h d s value : ℂ) :=
  normalizedIncompleteMomentOnMod_eq_solutionCount Q h d s value

example (Q h d : ℕ) {ι : Type*} [Fintype ι] [NeZero Q]
    (value : ι → ZMod Q) (a : Fin d → ZMod Q) :
    ‖incompleteWeylSumOnMod Q h d value a‖ ≤ Fintype.card ι :=
  norm_incompleteWeylSumOnMod_le_card Q h d value a

example (Q h d s : ℕ) {ι : Type*} [Fintype ι]
    (value : ι → ZMod Q) :
    incompleteSolutionCountOnMod Q h d s value ≤
      Fintype.card ι ^ (2 * s) :=
  incompleteSolutionCountOnMod_le_total Q h d s value

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

example (Q h d X : ℕ) [NeZero Q] (B : Finset (Fin X))
    (a : Fin d → ZMod Q) :
    ‖incompleteVinogradovSupportWeylSumMod Q h d X B a‖ ≤ B.card :=
  norm_incompleteVinogradovSupportWeylSumMod_le_card Q h d X B a

example (Q h d s X : ℕ) (B : Finset (Fin X)) :
    incompleteVinogradovSupportSolutionCountMod Q h d s X B ≤
      B.card ^ (2 * s) :=
  incompleteVinogradovSupportSolutionCountMod_le_total Q h d s X B
