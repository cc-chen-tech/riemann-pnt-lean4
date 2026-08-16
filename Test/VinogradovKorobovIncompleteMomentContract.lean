import ZeroFreeRegion.VinogradovKorobov.VinogradovIncompleteMoment

open ZeroFreeRegion.VinogradovKorobov

attribute [local instance] Classical.propDecidable

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

example (Q h d s X : ℕ) [NeZero Q]
    (x y : Fin s → Fin X) :
    incompleteVinogradovSolutionSelector Q h d s X x y =
      if IsIncompleteVinogradovSolutionMod Q h d s X x y then 1 else 0 :=
  incompleteVinogradovSolutionSelector_eq_indicator Q h d s X x y

example (Q h d s X : ℕ) [NeZero Q] :
    normalizedIncompleteVinogradovMomentMod Q h d s X =
      (incompleteVinogradovSolutionCountMod Q h d s X : ℂ) :=
  normalizedIncompleteVinogradovMomentMod_eq_solutionCount Q h d s X

example (Q k s X : ℕ) (x y : Fin s → Fin X) :
    IsIncompleteVinogradovSolutionMod Q 1 k s X x y ↔
      IsVinogradovSolutionMod Q k s X x y :=
  isIncompleteVinogradovSolutionMod_one_iff Q k s X x y

example (Q k s X : ℕ) :
    incompleteVinogradovSolutionCountMod Q 1 k s X =
      vinogradovSolutionCountMod Q k s X :=
  incompleteVinogradovSolutionCountMod_one_eq Q k s X

example (Q k s X : ℕ) [NeZero Q] :
    normalizedIncompleteVinogradovMomentMod Q 1 k s X =
      normalizedVinogradovMomentMod Q k s X :=
  normalizedIncompleteVinogradovMomentMod_one_eq Q k s X

example {Q k h d s X : ℕ} {x y : Fin s → Fin X}
    (hxy : IsVinogradovSolutionMod Q k s X x y)
    (hh : 1 ≤ h) (hwindow : h + d ≤ k + 1) :
    IsIncompleteVinogradovSolutionMod Q h d s X x y :=
  hxy.toIncomplete hh hwindow

example (Q k h d s X : ℕ)
    (hh : 1 ≤ h) (hwindow : h + d ≤ k + 1) :
    vinogradovSolutionCountMod Q k s X ≤
      incompleteVinogradovSolutionCountMod Q h d s X :=
  vinogradovSolutionCountMod_le_incomplete Q k h d s X hh hwindow
