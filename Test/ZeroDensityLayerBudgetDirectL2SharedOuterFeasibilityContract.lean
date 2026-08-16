import PrimeNumberTheorem.ZeroDensityLayerBudgetDirectL2SharedOuterFeasibility

namespace PrimeNumberTheorem

example (beta : ℝ) : directL2SharedOuterCap beta = 2 * beta - 1 := rfl

example (beta theta : ℝ) :
    directL2SharedOuterEpsilonThreshold beta theta =
      (2 - theta) * (2 * beta - 1) / (2 * (1 - beta)) - 1 := rfl

example (beta : ℝ) :
    directL2PolylogSharedOuterEpsilonThreshold beta =
      (3 * beta - 2) / (1 - beta) := rfl

example (beta lambda theta : ℝ) (hbetaHalf : 1 / 2 < beta)
    (htheta : theta < 2) :
    directL2CriticalRightHeight beta lambda theta < directL2SharedOuterCap beta ↔
      theta < 2 - 2 * lambda * (1 - beta) / directL2SharedOuterCap beta :=
  directL2CriticalRightHeight_lt_sharedOuterCap_iff
    beta lambda theta hbetaHalf htheta

example (beta theta epsilon : ℝ) (hbetaHalf : 1 / 2 < beta)
    (hbetaOne : beta < 1) (htheta : theta < 2) :
    directL2CriticalRightHeight beta (1 + epsilon) theta <
        directL2SharedOuterCap beta ↔
      epsilon < directL2SharedOuterEpsilonThreshold beta theta :=
  directL2CriticalRightHeight_shortInterval_iff
    beta theta epsilon hbetaHalf hbetaOne htheta

example (beta : ℝ) (hbetaOne : beta < 1) :
    directL2SharedOuterEpsilonThreshold beta 0 =
      directL2PolylogSharedOuterEpsilonThreshold beta :=
  directL2SharedOuterEpsilonThreshold_zero beta hbetaOne

example (beta epsilon : ℝ) (hbetaHalf : 1 / 2 < beta)
    (hbetaOne : beta < 1) :
    directL2CriticalRightHeight beta (1 + epsilon) 0 <
        directL2SharedOuterCap beta ↔
      epsilon < directL2PolylogSharedOuterEpsilonThreshold beta :=
  directL2Polylog_shortInterval_sharedOuter_iff
    beta epsilon hbetaHalf hbetaOne

example (beta : ℝ) (hbetaOne : beta < 1) :
    0 < directL2PolylogSharedOuterEpsilonThreshold beta ↔ 2 / 3 < beta :=
  directL2PolylogSharedOuterEpsilonThreshold_pos_iff beta hbetaOne

example (beta epsilon : ℝ) (hbeta : 2 / 3 < beta) (hbetaOne : beta < 1)
    (hepsilon : epsilon < directL2PolylogSharedOuterEpsilonThreshold beta) :
    directL2CriticalRightHeight beta (1 + epsilon) 0 <
      directL2SharedOuterCap beta :=
  directL2Polylog_shortInterval_sharedOuter
    beta epsilon hbeta hbetaOne hepsilon

example (beta : ℝ) (hbeta : 2 / 3 < beta) (hbetaOne : beta < 1) :
    ∃ epsilon : ℝ,
      0 < epsilon ∧
      epsilon < directL2PolylogSharedOuterEpsilonThreshold beta ∧
      directL2CriticalRightHeight beta (1 + epsilon) 0 <
        directL2SharedOuterCap beta :=
  exists_pos_directL2Polylog_sharedOuterEpsilon beta hbeta hbetaOne

example (beta theta : ℝ) (hbetaOne : beta < 1) :
    directL2SharedOuterEpsilonThreshold beta theta =
      (2 * (3 * beta - 2) - theta * (2 * beta - 1)) /
        (2 * (1 - beta)) :=
  directL2SharedOuterEpsilonThreshold_eq_expanded beta theta hbetaOne

example (beta theta : ℝ) (hbetaHalf : 1 / 2 < beta)
    (hbetaOne : beta < 1) :
    0 < directL2SharedOuterEpsilonThreshold beta theta ↔
      theta < 2 * (3 * beta - 2) / (2 * beta - 1) :=
  directL2SharedOuterEpsilonThreshold_pos_iff
    beta theta hbetaHalf hbetaOne

example (beta theta : ℝ) (hbetaHalf : 1 / 2 < beta)
    (hbetaOne : beta < 1) :
    (∃ epsilon : ℝ,
      0 < epsilon ∧ epsilon < directL2SharedOuterEpsilonThreshold beta theta) ↔
      theta < 2 * (3 * beta - 2) / (2 * beta - 1) :=
  exists_pos_directL2_sharedOuterEpsilon_iff
    beta theta hbetaHalf hbetaOne

example :
    4 * (3 / 4 : ℝ) - 2 =
      2 * (3 * (3 / 4 : ℝ) - 2) / (2 * (3 / 4 : ℝ) - 1) :=
  directL2_thresholds_eq_at_threeFourths

example (beta : ℝ) (hbetaHalf : 1 / 2 < beta)
    (hbetaThreeFourths : beta < 3 / 4) :
    2 * (3 * beta - 2) / (2 * beta - 1) < 4 * beta - 2 :=
  directL2_sharedThreshold_lt_intrinsic_of_lt_threeFourths
    beta hbetaHalf hbetaThreeFourths

example (beta : ℝ) (hbetaThreeFourths : 3 / 4 < beta)
    (hbetaOne : beta < 1) :
    4 * beta - 2 < 2 * (3 * beta - 2) / (2 * beta - 1) :=
  directL2_intrinsicThreshold_lt_shared_of_threeFourths_lt
    beta hbetaThreeFourths hbetaOne

end PrimeNumberTheorem
